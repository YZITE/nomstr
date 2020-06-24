use alloc::string::String;
use nom::bytes::streaming::{tag, take_until, take_while};
use nom::character::streaming::char;
use nom::error::ParseError;
use nom::{AsChar, IResult, InputIter, InputTakeAtPosition};

pub fn parse_raw_string<I, E>() -> impl Fn(I) -> IResult<I, I, E>
where
    E: ParseError<I>,
    I: crate::MyInput + for<'a> nom::FindSubstring<&'a str>,
    <I as InputIter>::Item: AsChar,
    <I as InputTakeAtPosition>::Item: AsChar,
{
    move |input: I| {
        let (input, _) = char('r')(input)?;
        let (input, o1) =
            take_while(|i: <I as InputTakeAtPosition>::Item| i.as_char() == '#')(input)?;
        let (input, _) = char('"')(input)?;
        let cltag: String = core::iter::once('"')
            .chain(core::iter::repeat('#').take(o1.input_len()))
            .collect();
        let (input, x) = take_until(cltag.as_str())(input)?;
        let (input, _) = tag(cltag.as_str())(input)?;
        Ok((input, x))
    }
}

#[cfg(test)]
mod tests {
    use super::parse_raw_string;

    #[test]
    fn test_rawstr() {
        let sprs = parse_raw_string::<_, ()>();
        let tmp = sprs("r\"abc i khlr\"");
        assert_eq!(Ok(("", "abc i khlr")), tmp);
        let tmp = sprs("r##\"jkvlkvf \" knvl \"# fmölk\"##");
        assert_eq!(Ok(("", "jkvlkvf \" knvl \"# fmölk")), tmp);
    }
}
