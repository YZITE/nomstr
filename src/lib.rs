//! [original source](https://github.com/Geal/nom/blob/47fdc2dd94bd113f4a95dd0c29188616ab83e182/examples/string.rs)
//!
//! This example shows an example of how to parse an escaped string. The
//! rules for the string are similar to JSON and rust. A string is:
//!
//! - Enclosed by double quotes
//! - Can contain any raw unescaped code point besides \ and "
//! - Matches the following escape sequences: \b, \f, \n, \r, \t, \", \\, \/
//! - Matches code points like Rust: \u{XXXX}, where XXXX can be up to 6
//!   hex characters
//! - an escape followed by whitespace consumes all whitespace between the
//!   escape and the next non-whitespace character

#![no_std]

extern crate alloc;
extern crate core;

use alloc::borrow::Cow;
use core::ops::RangeFrom;
use nom::bytes::streaming::{tag, take_till1, take_while_m_n};
use nom::character::streaming::{char, multispace1};
use nom::combinator::{flat_map, map, opt, value};
use nom::error::{ErrorKind as nomErrKind, ParseError};
use nom::sequence::{delimited, preceded};
use nom::{
    branch::alt, multi::fold_many0, AsBytes, AsChar, Compare, IResult, InputIter, InputLength,
    InputTake, Slice,
};

mod raw;
pub use raw::parse_raw_string;

// parser combinators are constructed from the bottom up:
// first we write parsers for the smallest elements (escaped characters),
// then combine them into larger parsers.

/// helper trait to avoid repetition of trait bounds
// comments indicate which function requires that bound
pub trait MyInput:
    AsBytes         // parse_unicode
    + Clone         // map*
    + InputIter     // parse_unicode
    + InputTake     // tag, take_while_m_n
    + InputLength   // parse_literal
    + Slice<RangeFrom<usize>>
    + nom::InputTakeAtPosition
    + for<'a> Compare<&'a str> // tag
{
}

impl<T> MyInput for T where
    Self: AsBytes
        + Clone
        + InputIter
        + InputTake
        + InputLength
        + Slice<RangeFrom<usize>>
        + nom::InputTakeAtPosition
        + for<'a> Compare<&'a str>
{
}

#[inline]
fn nome_from_error_kind<I, E>(input: I, kind: nomErrKind) -> nom::Err<E>
where
    E: ParseError<I>,
{
    nom::Err::Error(E::from_error_kind(input, kind))
}

/// Parse a unicode sequence, of the form u{XXXX}, where XXXX is 1 to 6
/// hexadecimal numerals. We will combine this later with parse_escaped_char
/// to parse sequences like \u{00AC}.
fn parse_unicode<I, E>(input: I) -> IResult<I, char, E>
where
    E: ParseError<I>,
    I: MyInput,
    <I as nom::InputIter>::Item: AsChar,
{
    let i = input.clone();

    // parse u{XXXX}.
    // XXXX: match between 1 and 6 hexadecimal numerals
    let (input, hex) = delimited(
        tag("u{"),
        take_while_m_n(1, 6, AsChar::is_hex_digit),
        char('}'),
    )(input)?;

    // convert hex to u32
    let o2 = u32::from_str_radix(core::str::from_utf8(hex.as_bytes()).unwrap(), 16)
        .map_err(|_| nome_from_error_kind(i.clone(), nomErrKind::MapRes))?;

    // In this case, because not all u32 values are valid unicode
    // code points, we have to fallibly convert to char with from_u32.
    let o3 = core::char::from_u32(o2).ok_or_else(|| nome_from_error_kind(i, nomErrKind::MapOpt))?;
    Ok((input, o3))
}

fn parse_escaped_char<I, E>(input: I) -> IResult<I, char, E>
where
    E: ParseError<I>,
    I: InputIter + Slice<RangeFrom<usize>>,
    <I as nom::InputIter>::Item: AsChar + Copy,
{
    let x = input
        .iter_elements()
        .next()
        .ok_or(nom::Err::Incomplete(nom::Needed::Size(1)))?;
    let xr = match x.as_char() {
        'n' => '\n',
        'r' => '\r',
        't' => '\t',
        'b' => '\u{08}',
        'f' => '\u{0C}',
        xc @ '\\' | xc @ '/' => xc,
        _ => return Err(nome_from_error_kind(input, nomErrKind::OneOf)),
    };
    Ok((input.slice(x.len()..), xr))
}

/// Parse a non-empty block of text that doesn't include \ or "
fn parse_literal<I, E>(delim: char) -> impl Fn(I) -> IResult<I, I, E>
where
    E: ParseError<I>,
    I: MyInput,
    <I as nom::InputTakeAtPosition>::Item: AsChar,
{
    take_till1(
        move |i: <I as nom::InputTakeAtPosition>::Item| match i.as_char() {
            '\\' => true,
            j => j == delim,
        },
    )
}

/// A string fragment contains a fragment of a string being parsed: either
/// a non-empty Literal (a series of non-escaped characters), a single
/// parsed escaped character, or a block of escaped whitespace.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum StringFragment<I> {
    Literal(I),
    EscapedChar(char),
    EscapedWS,
}

/// Combine parse_literal and parse_escaped_char into a StringFragment.
fn parse_fragment<I, E>(delim: char) -> impl Fn(I) -> IResult<I, StringFragment<I>, E>
where
    E: ParseError<I>,
    I: MyInput,
    <I as nom::InputIter>::Item: AsChar + Copy,
    <I as nom::InputTakeAtPosition>::Item: AsChar + Copy,
{
    alt((
        // The `map` combinator runs a parser, then applies a function to the output
        // of that parser.
        map(parse_literal(delim), StringFragment::Literal),
        preceded(
            char('\\'),
            alt((
                // parse escape sequences
                map(
                    alt((parse_unicode, parse_escaped_char, char(delim))),
                    StringFragment::EscapedChar,
                ),
                // discard any escaped whitespace
                value(StringFragment::EscapedWS, multispace1),
            )),
        ),
    ))
}

fn fragment_fold<'i, I: AsBytes + ?Sized + 'i>(
    mut string: Cow<'i, [u8]>,
    fragment: StringFragment<&'i I>,
) -> Cow<'i, [u8]> {
    match fragment {
        StringFragment::Literal(s) => string.to_mut().extend_from_slice(s.as_bytes()),
        StringFragment::EscapedChar(c) => {
            let s = string.to_mut();
            let oldlen = s.len();
            s.resize(oldlen + 4, 0u8);
            let dstlen = c.encode_utf8(&mut s[oldlen..]).len();
            s.truncate(oldlen + dstlen);
        }
        StringFragment::EscapedWS => {}
    }
    string
}

/// Parse a string. Use a loop of parse_fragment and push all of the fragments
/// into an output string.
pub fn parse_string<'i, I, E>(delim: char) -> impl Fn(&'i I) -> IResult<&'i I, Cow<'i, [u8]>, E>
where
    E: ParseError<&'i I>,
    I: AsBytes + ?Sized + 'i,
    &'i I: MyInput + PartialEq,
    <&'i I as nom::InputIter>::Item: AsChar + Copy,
    <&'i I as nom::InputTakeAtPosition>::Item: AsChar + Copy,
{
    debug_assert!(delim != '\\');

    // Finally, parse the string. Note that, if `build_string` could accept a raw
    // " character, the closing delimiter " would never match. When using
    // `delimited` with a looping parser (like fold_many0), be sure that the
    // loop won't accidentally match your closing delimiter!
    delimited(
        char(delim),
        flat_map(
            opt(map(parse_literal(delim), I::as_bytes)),
            move |init: Option<&'i [u8]>| {
                fold_many0(
                    parse_fragment(delim),
                    Cow::Borrowed(init.unwrap_or(&[])),
                    fragment_fold,
                )
            },
        ),
        char(delim),
    )
}

#[cfg(test)]
mod tests {
    use super::*;

    fn cwtr<'a>(x: &'a (&'a [u8], Cow<'a, [u8]>)) -> (&'a [u8], &'a [u8]) {
        (x.0, &*x.1)
    }

    #[test]
    fn test0() {
        let sprs = parse_string::<_, ()>('"');
        let res = sprs(b"\"abc\"".as_ref());
        assert_eq!(
            res.as_ref().map(cwtr),
            Ok(("".as_bytes(), "abc".as_bytes()))
        );
        if let Cow::Owned(_) = res.unwrap().1 {
            unreachable!();
        }

        let data: &[u8] = b"\"tab:\\tafter tab, newline:\\nnew line, quote: \\\", emoji: \\u{1F602}, newline:\\nescaped whitespace: \\    abc\"";
        let tmp = sprs(data);
        assert_eq!(
          tmp.as_ref().map(cwtr),
          Ok((
            "".as_bytes(),
            "tab:\tafter tab, newline:\nnew line, quote: \", emoji: 😂, newline:\nescaped whitespace: abc".as_bytes()
          ))
        );
    }
}
