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

use nom::bytes::streaming::{is_not, tag, take_while_m_n};
use nom::character::streaming::{char, multispace1};
use nom::combinator::{flat_map, map, map_opt, map_res, opt, value, verify};
use nom::sequence::{delimited, preceded};
use nom::{
    branch::alt, error::ParseError, multi::fold_many0, AsBytes, AsChar, Compare, IResult,
    InputIter, InputLength, InputTake, Slice,
};
use std::{borrow::Cow, ops::RangeFrom};

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

/// Parse a unicode sequence, of the form u{XXXX}, where XXXX is 1 to 6
/// hexadecimal numerals. We will combine this later with parse_escaped_char
/// to parse sequences like \u{00AC}.
fn parse_unicode<E, Input>(input: Input) -> IResult<Input, char, E>
where
    E: ParseError<Input>,
    Input: MyInput,
    <Input as nom::InputIter>::Item: AsChar,
{
    // parse u{XXXX}.
    // XXXX: match between 1 and 6 hexadecimal numerals
    let parse_delimited_hex = delimited(
        tag("u{"),
        take_while_m_n(1, 6, <Input as nom::InputIter>::Item::is_hex_digit),
        char('}'),
    );

    let parse_u32 = map_res(parse_delimited_hex, move |hex: Input| {
        u32::from_str_radix(std::str::from_utf8(hex.as_bytes()).unwrap(), 16)
    });

    // In this case, because not all u32 values are valid unicode
    // code points, we have to fallibly convert to char with from_u32.
    map_opt(parse_u32, std::char::from_u32)(input)
}

fn eval_escape(x: char) -> Option<char> {
    Some(match x {
        'n' => '\n',
        'r' => '\r',
        't' => '\t',
        'b' => '\u{08}',
        'f' => '\u{0C}',
        '\\' | '/' => x,
        _ => return None,
    })
}

fn parse_escaped_char<E, Input>(input: Input) -> IResult<Input, char, E>
where
    E: ParseError<Input>,
    Input: InputIter + Slice<RangeFrom<usize>>,
    <Input as nom::InputIter>::Item: AsChar,
{
    match input.iter_elements().next() {
        None => Err(nom::Err::Incomplete(nom::Needed::Size(1))),
        Some(x) => {
            if let Some(x2) = eval_escape(x.as_char()) {
                Ok((input.slice(input.slice_index(1).unwrap()..), x2))
            } else {
                Err(nom::Err::Error(E::from_error_kind(
                    input,
                    nom::error::ErrorKind::Alt,
                )))
            }
        }
    }
}

/// Parse a non-empty block of text that doesn't include \ or "
fn parse_literal<E, Input>(input: Input) -> IResult<Input, Input, E>
where
    E: ParseError<Input>,
    Input: MyInput,
    for<'a> &'a str: InputLength + nom::FindToken<<Input as nom::InputTakeAtPosition>::Item>,
{
    // In this case, we want to ensure that the output of is_not is non-empty.
    verify(is_not("\"\\"), |s: &Input| s.input_len() != 0)(input)
}

/// A string fragment contains a fragment of a string being parsed: either
/// a non-empty Literal (a series of non-escaped characters), a single
/// parsed escaped character, or a block of escaped whitespace.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum StringFragment<Input> {
    Literal(Input),
    EscapedChar(char),
    EscapedWS,
}

/// Combine parse_literal and parse_escaped_char into a StringFragment.
fn parse_fragment<E, Input>(
    delim: char,
) -> impl Fn(Input) -> IResult<Input, StringFragment<Input>, E>
where
    E: ParseError<Input>,
    Input: MyInput,
    <Input as nom::InputIter>::Item: AsChar,
    <Input as nom::InputTakeAtPosition>::Item: AsChar + Clone,
    for<'a> &'a str: InputLength + nom::FindToken<<Input as nom::InputTakeAtPosition>::Item>,
{
    alt((
        // The `map` combinator runs a parser, then applies a function to the output
        // of that parser.
        map(parse_literal, StringFragment::Literal),
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

fn fragment_fold<'i, Input: AsBytes + ?Sized + 'i>(
    mut string: Cow<'i, [u8]>,
    fragment: StringFragment<&'i Input>,
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
pub fn parse_string<'i, E, Input>(
    delim: char,
) -> impl Fn(&'i Input) -> IResult<&'i Input, Cow<'i, [u8]>, E>
where
    E: ParseError<&'i Input>,
    Input: AsBytes + ?Sized + 'i,
    &'i Input: MyInput + PartialEq,
    <&'i Input as nom::InputIter>::Item: AsChar,
    <&'i Input as nom::InputTakeAtPosition>::Item: AsChar + Clone,
    for<'a> &'a str: InputLength + nom::FindToken<<&'i Input as nom::InputTakeAtPosition>::Item>,
{
    debug_assert!(delim != '\\');

    // Finally, parse the string. Note that, if `build_string` could accept a raw
    // " character, the closing delimiter " would never match. When using
    // `delimited` with a looping parser (like fold_many0), be sure that the
    // loop won't accidentally match your closing delimiter!
    delimited(
        char(delim),
        flat_map(
            opt(map(parse_literal, Input::as_bytes)),
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
        let sprs = parse_string::<(), _>('"');
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
