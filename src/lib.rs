use serde_json::Value;
use std::borrow::Cow;
use std::iter::Skip;
use std::num::ParseIntError;
use std::str::Split;
use thiserror::Error;

#[derive(Clone, Debug, Error, PartialEq)]
pub enum Error {
    #[error("invalid escape sequence in reference token {0}")]
    InvalidEscape(String),
    #[error("no leading slash")]
    NoLeadingSlash,
    #[error("pointer referencing a non-existent value")]
    NonExistentValue,
    #[error("invalid pointer index")]
    InvalidIndex(#[from] ParseIntError),
    #[error("index has leading zero")]
    LeadingZero(String),
    #[error("pointer attempted to reference value which is not in an object or array")]
    NotObjectOrArray,
}

fn get<'v>(pointer: &str, value: &'v Value) -> Result<Option<&'v Value>, Error> {
    if pointer.is_empty() {
        return Ok(Some(value));
    }

    if !pointer.starts_with('/') {
        return Err(Error::NoLeadingSlash);
    }

    let mut current_value = Some(value);
    for reference_token in TokenIterator::new(pointer) {
        let reference_token = reference_token?;

        if current_value.is_none() {
            return Err(Error::NonExistentValue);
        }

        let value = current_value.unwrap();

        current_value = if value.is_array() {
            // reference token must be an index for the array
            match reference_token.inner.as_ref() {
                "0" => value.as_array().unwrap().get(0),
                "-" => None,
                reference_token if !reference_token.starts_with('0') => value
                    .as_array()
                    .unwrap()
                    .get(reference_token.parse::<usize>()?),
                reference_token => return Err(Error::LeadingZero(reference_token.into())),
            }
        } else if value.is_object() {
            value
                .as_object()
                .unwrap()
                .get(reference_token.inner.as_ref())
        } else {
            return Err(Error::NotObjectOrArray);
        }
    }

    Ok(current_value)
}

pub trait Resolve {
    fn resolve(&self, pointer: &str) -> Result<Option<&Value>, Error>;
}

impl Resolve for Value {
    fn resolve(&self, pointer: &str) -> Result<Option<&Value>, Error> {
        get(pointer, self)
    }
}

#[derive(Debug)]
struct ReferenceToken<'p> {
    inner: Cow<'p, str>,
}

#[inline]
fn invalid_escape_sequence(sequence: &[u8]) -> bool {
    if &sequence[0..=0] == b"~" {
        if sequence.len() != 2 {
            return true;
        }

        &sequence[1..=1] != b"0" && &sequence[1..=1] != b"1"
    } else {
        false
    }
}

impl<'p> TryFrom<&'p str> for ReferenceToken<'p> {
    type Error = Error;

    fn try_from(token: &'p str) -> Result<Self, Self::Error> {
        Ok(if token.contains('~') {
            // Verify occurrences of ~ are valid
            let is_invalid =
                token.len() < 2 || token.as_bytes().windows(2).any(invalid_escape_sequence);

            if is_invalid {
                return Err(Error::InvalidEscape(token.to_string()));
            }

            ReferenceToken {
                inner: Cow::from(token.replace("~1", "/").replace("~0", "~")),
            }
        } else {
            ReferenceToken {
                inner: Cow::from(token),
            }
        })
    }
}

struct TokenIterator<'p> {
    iter: Skip<Split<'p, char>>,
}

impl<'p> TokenIterator<'p> {
    fn new(pointer: &'p str) -> TokenIterator<'p> {
        TokenIterator {
            iter: pointer.split('/').skip(1),
        }
    }
}

impl<'p> Iterator for TokenIterator<'p> {
    type Item = Result<ReferenceToken<'p>, Error>;

    fn next(&mut self) -> Option<Self::Item> {
        self.iter.next().map(ReferenceToken::try_from)
    }
}

#[cfg(test)]
mod tests {
    use crate::{Error, Resolve};
    use serde_json::json;

    #[test]
    fn rfc6901_tests() {
        let value = json!({
            "foo": ["bar", "baz"],
            "foo": ["bar", "baz"],
            "": 0,
            "a/b": 1,
            "c%d": 2,
            "e^f": 3,
            "g|h": 4,
            "i\\j": 5,
            "k\"l": 6,
            " ": 7,
            "m~n": 8
        });

        assert_eq!(value.resolve(""), Ok(Some(&value)));
        assert_eq!(value.resolve("/foo"), Ok(Some(&json!(["bar", "baz"]))));
        assert_eq!(value.resolve("/foo/0"), Ok(Some(&json!("bar"))));
        assert_eq!(value.resolve("/"), Ok(Some(&json!(0))));
        assert_eq!(value.resolve("/a~1b"), Ok(Some(&json!(1))));
        assert_eq!(value.resolve("/c%d"), Ok(Some(&json!(2))));
        assert_eq!(value.resolve("/e^f"), Ok(Some(&json!(3))));
        assert_eq!(value.resolve("/g|h"), Ok(Some(&json!(4))));
        assert_eq!(value.resolve("/i\\j"), Ok(Some(&json!(5))));
        assert_eq!(value.resolve("/k\"l"), Ok(Some(&json!(6))));
        assert_eq!(value.resolve("/ "), Ok(Some(&json!(7))));
        assert_eq!(value.resolve("/m~0n"), Ok(Some(&json!(8))));
    }

    #[test]
    fn invalid_escape() {
        let value = json!({});

        assert_eq!(value.resolve("/~"), Err(Error::InvalidEscape("~".into())));
        assert_eq!(value.resolve("/~2"), Err(Error::InvalidEscape("~2".into())));
        assert_eq!(
            value.resolve("/foo~2bar"),
            Err(Error::InvalidEscape("foo~2bar".into()))
        );
    }

    #[test]
    fn no_leading_slash() {
        let value = json!({"foo": "bar"});

        assert_eq!(value.resolve("foo"), Err(Error::NoLeadingSlash));
    }

    #[test]
    fn non_existent_value() {
        let value = json!({"foo": "bar"});

        assert_eq!(
            value.resolve("/bar/not-exist"),
            Err(Error::NonExistentValue)
        );
    }

    #[test]
    fn invalid_index() {
        let value = json!(["foo", "bar", "baz"]);

        assert!(matches!(value.resolve("/foo"), Err(Error::InvalidIndex(_))));
    }

    #[test]
    fn leading_zero() {
        let value = json!(["foo", "bar", "baz"]);

        assert_eq!(value.resolve("/01"), Err(Error::LeadingZero("01".into())));
    }

    #[test]
    fn not_object_or_array() {
        let value = json!({
            "foo": "bar",
        });

        assert_eq!(value.resolve("/foo/bar"), Err(Error::NotObjectOrArray));

        let value = json!({
            "foo": [{
                "bar": "baz",
            }],
        });

        assert_eq!(
            value.resolve("/foo/0/bar/baz"),
            Err(Error::NotObjectOrArray)
        );
    }
}
