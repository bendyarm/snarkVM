// Copyright 2024 Aleo Network Foundation
// This file is part of the snarkVM library.

// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at:

// http://www.apache.org/licenses/LICENSE-2.0

// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

use super::*;

impl<N: Network> Parser for PlaintextType<N> {
    /// Parses a string into a plaintext type.
    #[inline]
    fn parse(string: &str) -> ParserResult<Self> {
        // Parse to determine the plaintext type (order matters).
        alt((
            map(ArrayType::parse, |type_| Self::Array(type_)),
            map(Identifier::parse, |identifier| Self::Struct(identifier)),
            map(LiteralType::parse, |type_| Self::Literal(type_)),
        ))(string)
    }
}

impl<N: Network> FromStr for PlaintextType<N> {
    type Err = Error;

    /// Returns a plaintext type from a string literal.
    fn from_str(string: &str) -> Result<Self> {
        match Self::parse(string) {
            Ok((remainder, object)) => {
                // Ensure the remainder is empty.
                ensure!(remainder.is_empty(), "Failed to parse string. Found invalid character in: \"{remainder}\"");
                // Return the object.
                Ok(object)
            }
            Err(error) => bail!("Failed to parse string. {error}"),
        }
    }
}

impl<N: Network> Debug for PlaintextType<N> {
    /// Prints the plaintext type as a string.
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        Display::fmt(self, f)
    }
}

impl<N: Network> Display for PlaintextType<N> {
    /// Prints the plaintext type as a string.
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        match self {
            // Prints the literal, i.e. field
            Self::Literal(literal) => Display::fmt(literal, f),
            // Prints the struct, i.e. signature
            Self::Struct(struct_) => Display::fmt(struct_, f),
            // Prints the array type, i.e. [field; 2u32]
            Self::Array(array) => Display::fmt(array, f),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use snarkvm_console_network::MainnetV0;
    use crate::U32;

    type CurrentNetwork = MainnetV0;

    #[test]
    fn test_parse() -> Result<()> {
        assert_eq!(
            PlaintextType::parse("field"),
            Ok(("", PlaintextType::<CurrentNetwork>::Literal(LiteralType::Field)))
        );
        assert_eq!(
            PlaintextType::parse("signature"),
            Ok(("", PlaintextType::<CurrentNetwork>::Literal(LiteralType::Signature)))
        );
        assert_eq!(
            PlaintextType::parse("string"),
            Ok(("", PlaintextType::<CurrentNetwork>::Literal(LiteralType::String)))
        );
        assert_eq!(
            PlaintextType::parse("foo"),
            Ok(("", PlaintextType::<CurrentNetwork>::Struct(Identifier::from_str("foo")?)))
        );
        assert_eq!(
            PlaintextType::parse("u8jdsklaj"),
            Ok(("", PlaintextType::<CurrentNetwork>::Struct(Identifier::from_str("u8jdsklaj")?)))
        );
        assert_eq!(
            PlaintextType::parse("[field; 1u32]"),
            Ok(("", PlaintextType::<CurrentNetwork>::Array(ArrayType::from_str("[field; 1u32]")?)))
        );
        // The previous assertion effectively parses the string twice,
        // once via PlaintextType::parse and once via ArrayType::from_str, both of which call ArrayType::parse.
        // Here is a test that parses it once and then checks that the result has the right structure:
        assert_eq!(
            PlaintextType::parse("[field; 1u32]"),
            Ok(("", PlaintextType::<CurrentNetwork>::Array(
                ArrayType::<CurrentNetwork>::new(PlaintextType::Literal(LiteralType::Field),
                                                 vec![U32::new(1)])?))));
        // Make sure parsing a nested array consumes the entire string.
        assert_eq!(
            PlaintextType::<CurrentNetwork>::parse("[[field; 2u32]; 1u32]").unwrap().0,
            "");

        // Uncomment to double-check that we have the expected value for the constant that
        // defines the maximum dimensions of an array.
        // assert_eq!(MainnetV0::MAX_DATA_DEPTH, 32);

        // Make sure parsing the deepest allowed array consumes the entire string.
        let open_brackets = "[".repeat(MainnetV0::MAX_DATA_DEPTH);
        let element_type_string = String::from("field");
        let close_arrays = "; 1u32]".repeat(MainnetV0::MAX_DATA_DEPTH);
        assert_eq!(
            PlaintextType::<CurrentNetwork>::parse(format!("{}{}{}",
                                                           open_brackets,
                                                           element_type_string,
                                                           close_arrays).as_str()).unwrap().0,
            "");

        Ok(())
    }

    #[test]
    fn test_parse_fails() -> Result<()> {
        // Literal type must not contain visibility.
        assert_eq!(
            Ok((".constant", PlaintextType::<CurrentNetwork>::from_str("field")?)),
            PlaintextType::<CurrentNetwork>::parse("field.constant")
        );
        assert_eq!(
            Ok((".public", PlaintextType::<CurrentNetwork>::from_str("field")?)),
            PlaintextType::<CurrentNetwork>::parse("field.public")
        );
        assert_eq!(
            Ok((".private", PlaintextType::<CurrentNetwork>::from_str("field")?)),
            PlaintextType::<CurrentNetwork>::parse("field.private")
        );

        // Struct type must not contain visibility.
        assert_eq!(
            Ok((".constant", Identifier::<CurrentNetwork>::from_str("foo")?)),
            Identifier::<CurrentNetwork>::parse("foo.constant")
        );
        assert_eq!(
            Ok((".public", Identifier::<CurrentNetwork>::from_str("foo")?)),
            Identifier::<CurrentNetwork>::parse("foo.public")
        );
        assert_eq!(
            Ok((".private", Identifier::<CurrentNetwork>::from_str("foo")?)),
            Identifier::<CurrentNetwork>::parse("foo.private")
        );

        // Array type must not contain visibility.
        assert_eq!(
            Ok((".constant", PlaintextType::<CurrentNetwork>::from_str("[field; 1u32]")?)),
            PlaintextType::<CurrentNetwork>::parse("[field; 1u32].constant")
        );
        assert_eq!(
            Ok((".public", PlaintextType::<CurrentNetwork>::from_str("[field; 1u32]")?)),
            PlaintextType::<CurrentNetwork>::parse("[field; 1u32].public")
        );
        assert_eq!(
            Ok((".private", PlaintextType::<CurrentNetwork>::from_str("[field; 1u32]")?)),
            PlaintextType::<CurrentNetwork>::parse("[field; 1u32].private")
        );

        // Must be non-empty.
        assert!(PlaintextType::<CurrentNetwork>::parse("").is_err());
        assert!(PlaintextType::<CurrentNetwork>::parse("{}").is_err());

        // Invalid characters.
        assert!(PlaintextType::<CurrentNetwork>::parse("_").is_err());
        assert!(PlaintextType::<CurrentNetwork>::parse("__").is_err());
        assert!(PlaintextType::<CurrentNetwork>::parse("___").is_err());
        assert!(PlaintextType::<CurrentNetwork>::parse("-").is_err());
        assert!(PlaintextType::<CurrentNetwork>::parse("--").is_err());
        assert!(PlaintextType::<CurrentNetwork>::parse("---").is_err());
        assert!(PlaintextType::<CurrentNetwork>::parse("*").is_err());
        assert!(PlaintextType::<CurrentNetwork>::parse("**").is_err());
        assert!(PlaintextType::<CurrentNetwork>::parse("***").is_err());

        // Must not start with a number.
        assert!(PlaintextType::<CurrentNetwork>::parse("1").is_err());
        assert!(PlaintextType::<CurrentNetwork>::parse("2").is_err());
        assert!(PlaintextType::<CurrentNetwork>::parse("3").is_err());
        assert!(PlaintextType::<CurrentNetwork>::parse("1foo").is_err());
        assert!(PlaintextType::<CurrentNetwork>::parse("12").is_err());
        assert!(PlaintextType::<CurrentNetwork>::parse("111").is_err());

        // Struct types must fit within the data capacity of a base field element.
        let struct_ = PlaintextType::<CurrentNetwork>::parse(
            "foo_bar_baz_qux_quux_quuz_corge_grault_garply_waldo_fred_plugh_xyzzy",
        );
        assert!(struct_.is_err());

        // Too deep an array
        let open_brackets = "[".repeat(MainnetV0::MAX_DATA_DEPTH + 1);
        let element_type_string = String::from("field");
        let close_arrays = "; 1u32]".repeat(MainnetV0::MAX_DATA_DEPTH + 1);
        assert!(PlaintextType::<CurrentNetwork>::parse(format!("{}{}{}", open_brackets, element_type_string, close_arrays).as_str()).is_err());

        Ok(())
    }

    #[test]
    fn test_display() -> Result<()> {
        assert_eq!(PlaintextType::<CurrentNetwork>::Literal(LiteralType::Boolean).to_string(), "boolean");
        assert_eq!(PlaintextType::<CurrentNetwork>::Literal(LiteralType::Field).to_string(), "field");
        assert_eq!(PlaintextType::<CurrentNetwork>::Literal(LiteralType::Signature).to_string(), "signature");
        assert_eq!(PlaintextType::<CurrentNetwork>::Struct(Identifier::from_str("foo")?).to_string(), "foo");
        assert_eq!(PlaintextType::<CurrentNetwork>::Struct(Identifier::from_str("bar")?).to_string(), "bar");
        assert_eq!(
            PlaintextType::<CurrentNetwork>::Array(ArrayType::from_str("[field; 8u32]")?).to_string(),
            "[field; 8u32]"
        );
        Ok(())
    }
}
