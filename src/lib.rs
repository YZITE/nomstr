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

use bstr::ByteSlice;
use nom::branch::alt;
use nom::bytes::streaming::{is_not, take_while_m_n};
use nom::character::streaming::{char, multispace1};
use nom::combinator::{flat_map, map, map_opt, map_res, opt, value, verify};
use nom::sequence::{delimited, preceded};
use nom::{error::ParseError, multi::fold_many0, IResult};
use std::borrow::Cow;

// parser combinators are constructed from the bottom up:
// first we write parsers for the smallest elements (escaped characters),
// then combine them into larger parsers.

/// Parse a unicode sequence, of the form u{XXXX}, where XXXX is 1 to 6
/// hexadecimal numerals. We will combine this later with parse_escaped_char
/// to parse sequences like \u{00AC}.
fn parse_unicode<'a, E: ParseError<&'a [u8]>>(input: &'a [u8]) -> IResult<&'a [u8], char, E> {
    // `take_while_m_n` parses between `m` and `n` bytes (inclusive) that match
    // a predicate. `parse_hex` here parses between 1 and 6 hexadecimal numerals.
    let parse_hex = take_while_m_n(1, 6, |c: u8| c.is_ascii_hexdigit());

    // `preceeded` takes a prefix parser, and if it succeeds, returns the result
    // of the body parser. In this case, it parses u{XXXX}.
    let parse_delimited_hex = preceded(
        char('u'),
        // `delimited` is like `preceded`, but it parses both a prefix and a suffix.
        // It returns the result of the middle parser. In this case, it parses
        // {XXXX}, where XXXX is 1 to 6 hex numerals, and returns XXXX
        delimited(char('{'), parse_hex, char('}')),
    );

    // `map_res` takes the result of a parser and applies a function that returns
    // a Result. In this case we take the hex bytes from parse_hex and attempt to
    // convert them to a u32.
    let parse_u32 = map_res(parse_delimited_hex, move |hex| {
        u32::from_str_radix(std::str::from_utf8(hex).unwrap(), 16)
    });

    // map_opt is like map_res, but it takes an Option instead of a Result. If
    // the function returns None, map_opt returns an error. In this case, because
    // not all u32 values are valid unicode code points, we have to fallibly
    // convert to char with from_u32.
    map_opt(parse_u32, |value| std::char::from_u32(value))(input)
}

fn eval_escape(x: u8) -> Option<char> {
    Some(match x {
        b'n' => '\n',
        b'r' => '\r',
        b't' => '\t',
        b'b' => '\u{08}',
        b'f' => '\u{0C}',
        b'\\' => '\\',
        b'/' => '/',
        b'"' => '"',
        _ => return None,
    })
}

fn parse_escaped_char<'a, E: ParseError<&'a [u8]>>(input: &'a [u8]) -> IResult<&'a [u8], char, E> {
    match input.bytes().next() {
        None => Err(nom::Err::Incomplete(nom::Needed::Size(1))),
        Some(x) => {
            if let Some(x2) = eval_escape(x) {
                Ok((&input[1..], x2))
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
fn parse_literal<'a, E: ParseError<&'a [u8]>>(input: &'a [u8]) -> IResult<&'a [u8], &'a [u8], E> {
    // `is_not` parses a string of 0 or more characters that aren't one of the
    // given characters.
    let not_quote_slash = is_not("\"\\");

    // `verify` runs a parser, then runs a verification function on the output of
    // the parser. The verification function accepts out output only if it
    // returns true. In this case, we want to ensure that the output of is_not
    // is non-empty.
    verify(not_quote_slash, |s: &[u8]| !s.is_empty())(input)
}

/// A string fragment contains a fragment of a string being parsed: either
/// a non-empty Literal (a series of non-escaped characters), a single
/// parsed escaped character, or a block of escaped whitespace.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum StringFragment<'a> {
    Literal(&'a [u8]),
    EscapedChar(char),
    EscapedWS,
}

/// Combine parse_literal, parse_escaped_whitespace, and parse_escaped_char
/// into a StringFragment.
fn parse_fragment<'a, E: ParseError<&'a [u8]>>(
    input: &'a [u8],
) -> IResult<&'a [u8], StringFragment<'a>, E> {
    alt((
        // The `map` combinator runs a parser, then applies a function to the output
        // of that parser.
        map(parse_literal, StringFragment::Literal),
        preceded(
            char('\\'),
            alt((
                // parse escape sequences
                map(
                    alt((parse_unicode, parse_escaped_char)),
                    StringFragment::EscapedChar,
                ),
                // discard any escaped whitespace
                value(StringFragment::EscapedWS, multispace1),
            )),
        ),
    ))(input)
}

/// Parse a string. Use a loop of parse_fragment and push all of the fragments
/// into an output string.
pub fn parse_string<'a, E: ParseError<&'a [u8]>>(
    input: &'a [u8],
) -> IResult<&'a [u8], Cow<'a, [u8]>, E> {
    // fold_many0 is the equivalent of iterator::fold. It runs a parser in a loop,
    // and for each output value, calls a folding function on each output value.
    let build_string = |init: Option<&'a [u8]>| {
        fold_many0(
            // Our parser function– parses a single string fragment
            parse_fragment,
            // Our init value, an empty string
            Cow::Borrowed(init.unwrap_or(&[])),
            // Our folding function. For each fragment, append the fragment to the
            // string.
            |mut string, fragment| {
                match fragment {
                    StringFragment::Literal(s) => string.to_mut().extend_from_slice(s),
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
            },
        )
    };

    let full_string = flat_map(opt(parse_literal), build_string);

    // Finally, parse the string. Note that, if `build_string` could accept a raw
    // " character, the closing delimiter " would never match. When using
    // `delimited` with a looping parser (like fold_many0), be sure that the
    // loop won't accidentally match your closing delimiter!
    delimited(char('"'), full_string, char('"'))(input)
}

/*
fn main() {
  let data = "\"abc\"";
  println!("EXAMPLE 1:\nParsing a simple input string: {}", data);
  let result = parse_string::<()>(data);
  assert_eq!(result, Ok(("", String::from("abc"))));
  println!("Result: {}\n\n", result.unwrap().1);

  let data = "\"tab:\\tafter tab, newline:\\nnew line, quote: \\\", emoji: \\u{1F602}, newline:\\nescaped whitespace: \\    abc\"";
  println!(
    "EXAMPLE 2:\nParsing a string with escape sequences, newline literal, and escaped whitespace:\n\n{}\n",
    data
  );
  let result = parse_string::<()>(data);
  assert_eq!(
    result,
    Ok((
      "",
      String::from("tab:\tafter tab, newline:\nnew line, quote: \", emoji: 😂, newline:\nescaped whitespace: abc")
    ))
  );
  println!("Result:\n\n{}", result.unwrap().1);
}
*/
