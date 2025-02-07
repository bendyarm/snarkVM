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

use crate::{
    Opcode,
    Operand,
    traits::{RegistersLoad, RegistersLoadCircuit, RegistersStore, RegistersStoreCircuit, StackMatches, StackProgram},
};
use circuit::prelude::ToFields as CircuitToFields;
use console::{
    network::prelude::*,
    program::{Literal, LiteralType, PlaintextType, Register, RegisterType, ToFields as ConsoleToFields},
    types::{Boolean, Field},
};

/// Computes whether `signature` is valid for the given `address` and `message`.
#[derive(Clone, PartialEq, Eq, Hash)]
pub struct DivFlagged<N: Network> {
    /// The operands.
    operands: Vec<Operand<N>>,
    /// The destination register.
    destination: Register<N>,
    // The flag register.
    flag: Register<N>,
}

impl<N: Network> DivFlagged<N> {
    // Initializes a new `div.flagged` instruction.
    #[inline]
    pub fn new(operands: Vec<Operand<N>>, destination: Register<N>,
                flag: Register<N>) -> Result<Self> {
        // Sanity check the number of operands.
        ensure!(operands.len() == 2, "Instruction '{}' must have two operands", Self::opcode());
        // Return the instruction.
        Ok(Self { operands, destination, flag })
    }

    /// Returns the opcode.
    #[inline]
    pub const fn opcode() -> Opcode {
        Opcode::DivFlagged
    }

    /// Returns the operands in the operation.
    #[inline]
    pub fn operands(&self) -> &[Operand<N>] {
        // Sanity check that there are exactly three operands.
        debug_assert!(self.operands.len() == 3, "Instruction '{}' must have three operands", Self::opcode());
        // Return the operands.
        &self.operands
    }

    /// Returns a vec of the destination and flag registers.
    #[inline]
    pub fn destinations(&self) -> Vec<Register<N>> {
        vec![self.destination.clone(), self.flag.clone()]
    }
}

impl<N: Network> DivFlagged<N> {
    /// Evaluates the instruction.
    #[inline]
    pub fn evaluate(
        &self,
        stack: &(impl StackMatches<N> + StackProgram<N>),
        registers: &mut (impl RegistersLoad<N> + RegistersStore<N>),
    ) -> Result<()> {
        // Ensure the number of operands is correct.
        if self.operands.len() != 2 {
            bail!("Instruction '{}' expects 2 operands, found {} operands", Self::opcode(), self.operands.len())
        }

        // Retrieve the inputs.
        let dividend = match registers.load_literal(stack, &self.operands[0])? {
            Literal::Field(dividend) => dividend,
            // we can add integer types here
            _ => bail!("Expected the first operand to be a field."),
        };
        let divisor = match registers.load_literal(stack, &self.operands[1])? {
            Literal::Field(divisor) => divisor,
            // when we add integer types, we have to make sure they are the same
            _ => bail!("Expected the second operand to be a field."),
        };

        // Divide.  (TODO: handle the standard case where the divisor is not zero)
        let (quotientval, flagval) = (Literal::Field(Field::zero()), Literal::Boolean(Boolean::new(true)));

        // Store the output.
        registers.store_literal(stack, &self.destination, quotientval)?;
        registers.store_literal(stack, &self.flag, flagval)?;

        Ok(())
    }

    /// Executes the instruction.
    pub fn execute<A: circuit::Aleo<Network = N>>(
        &self,
        stack: &(impl StackMatches<N> + StackProgram<N>),
        registers: &mut (impl RegistersLoadCircuit<N, A> + RegistersStoreCircuit<N, A>),
    ) -> Result<()> {
        // Ensure the number of operands is correct.
        if self.operands.len() != 2 {
            bail!("Instruction '{}' expects 2 operands, found {} operands", Self::opcode(), self.operands.len())
        }

        // Retrieve the inputs.
        let dividend = match registers.load_literal_circuit(stack, &self.operands[0])? {
            circuit::Literal::Field(dividend) => dividend,
            _ => bail!("Expected the first operand to be a field."),
        };
        let divisor = match registers.load_literal_circuit(stack, &self.operands[1])? {
            circuit::Literal::Field(divisor) => divisor,
            _ => bail!("Expected the second operand to be a field."),
        };

        // TODO, fix the rest of this
        // Divide.  (TODO: handle the standard case where the divisor is not zero)
        // let (quotientval, flagval) = ...;

        // Store the output.
        //registers.store_literal_circuit(stack, &self.destination, quotientval)?;
        //registers.store_literal_circuit(stack, &self.flag, flagval)?;

        Ok(())
    }

    /// Finalizes the instruction.
    #[inline]
    pub fn finalize(
        &self,
        stack: &(impl StackMatches<N> + StackProgram<N>),
        registers: &mut (impl RegistersLoad<N> + RegistersStore<N>),
    ) -> Result<()> {
        self.evaluate(stack, registers)
    }

    /// Returns the output type from the given program and input types.
    #[inline]
    pub fn output_types(
        &self,
        _stack: &impl StackProgram<N>,
        input_types: &[RegisterType<N>],
    ) -> Result<Vec<RegisterType<N>>> {
        // Ensure the number of input types is correct.
        if input_types.len() != 2 {
            bail!("Instruction '{}' expects 2 inputs, found {} inputs", Self::opcode(), input_types.len())
        }

        // Ensure the first operand is a field.
        if input_types[0] != RegisterType::Plaintext(PlaintextType::Literal(LiteralType::Field)) {
            bail!(
                "Instruction '{}' expects the first input to be a 'field'. Found input of type '{}'",
                Self::opcode(),
                input_types[0]
            )
        }

        // Ensure the second operand is an address.
        if input_types[1] != RegisterType::Plaintext(PlaintextType::Literal(LiteralType::Field)) {
            bail!(
                "Instruction '{}' expects the second input to be a 'field'. Found input of type '{}'",
                Self::opcode(),
                input_types[1]
            )
        }

        Ok(vec![RegisterType::Plaintext(PlaintextType::Literal(LiteralType::Field)),
                RegisterType::Plaintext(PlaintextType::Literal(LiteralType::Boolean))])
    }
}

impl<N: Network> Parser for DivFlagged<N> {
    /// Parses a string into an operation.
    #[inline]
    fn parse(string: &str) -> ParserResult<Self> {
        // Parse the opcode from the string.
        let (string, _) = tag(*Self::opcode())(string)?;
        // Parse the whitespace from the string.
        let (string, _) = Sanitizer::parse_whitespaces(string)?;
        // Parse the first operand from the string.
        let (string, first) = Operand::parse(string)?;
        // Parse the whitespace from the string.
        let (string, _) = Sanitizer::parse_whitespaces(string)?;
        // Parse the second operand from the string.
        let (string, second) = Operand::parse(string)?;
        // Parse the whitespace from the string.
        let (string, _) = Sanitizer::parse_whitespaces(string)?;
        // Parse the "into" from the string.
        let (string, _) = tag("into")(string)?;
        // Parse the whitespace from the string.
        let (string, _) = Sanitizer::parse_whitespaces(string)?;
        // Parse the destination register from the string.
        let (string, destination) = Register::parse(string)?;
        // Parse the whitespace from the string.
        let (string, _) = Sanitizer::parse_whitespaces(string)?;
        // Parse the flag register from the string.
        let (string, flag) = Register::parse(string)?;

        Ok((string, Self { operands: vec![first, second],
                           destination: destination,
                           flag: flag }))
    }
}

impl<N: Network> FromStr for DivFlagged<N> {
    type Err = Error;

    /// Parses a string into an operation.
    #[inline]
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

impl<N: Network> Debug for DivFlagged<N> {
    /// Prints the operation as a string.
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        Display::fmt(self, f)
    }
}

impl<N: Network> Display for DivFlagged<N> {
    /// Prints the operation to a string.
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        // Ensure the number of operands is 2.
        if self.operands.len() != 2 {
            return Err(fmt::Error);
        }
        // Print the operation.
        write!(f, "{} ", Self::opcode())?;
        self.operands.iter().try_for_each(|operand| write!(f, "{operand} "))?;
        write!(f, "into {} {}", self.destination, self.flag)
    }
}

impl<N: Network> FromBytes for DivFlagged<N> {
    /// Reads the operation from a buffer.
    fn read_le<R: Read>(mut reader: R) -> IoResult<Self> {
        // Initialize the vector for the operands.
        let mut operands = Vec::with_capacity(2);
        // Read the operands.
        for _ in 0..2 {
            operands.push(Operand::read_le(&mut reader)?);
        }
        // Read the destination register.
        let destination = Register::read_le(&mut reader)?;
        // Read the flag register.
        let flag = Register::read_le(&mut reader)?;

        // Return the operation.
        Ok(Self { operands, destination, flag })
    }
}

impl<N: Network> ToBytes for DivFlagged<N> {
    /// Writes the operation to a buffer.
    fn write_le<W: Write>(&self, mut writer: W) -> IoResult<()> {
        // Ensure the number of operands is 2.
        if self.operands.len() != 2 {
            return Err(error(format!("The number of operands must be 2, found {}", self.operands.len())));
        }
        // Write the operands.
        self.operands.iter().try_for_each(|operand| operand.write_le(&mut writer))?;
        // Write the destination register.
        self.destination.write_le(&mut writer);
        // Write the flag register.
        self.flag.write_le(&mut writer)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use console::network::MainnetV0;

    type CurrentNetwork = MainnetV0;

    #[test]
    fn test_parse() {
        let (string, is) = DivFlagged::<CurrentNetwork>::parse("div.flagged r0 r1 into r3 r4").unwrap();
        assert!(string.is_empty(), "Parser did not consume all of the string: '{string}'");
        assert_eq!(is.operands.len(), 2, "The number of operands is incorrect");
        assert_eq!(is.operands[0], Operand::Register(Register::Locator(0)), "The first operand is incorrect");
        assert_eq!(is.operands[1], Operand::Register(Register::Locator(1)), "The second operand is incorrect");
        assert_eq!(is.destination, Register::Locator(3), "The destination register is incorrect");
        assert_eq!(is.flag, Register::Locator(4), "The flag register is incorrect");
    }
}
