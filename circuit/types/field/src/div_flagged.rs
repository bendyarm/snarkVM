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

// Define the DivFlagged trait
pub trait DivFlagged<Rhs = Self> {
    type Output;
    fn div_flagged(self, rhs: Rhs) -> Self::Output;
}

impl<E: Environment> DivFlagged<Field<E>> for Field<E> {
    type Output = (Field<E>, Boolean<E>);

    fn div_flagged(self, other: Field<E>) -> Self::Output {
        // div.flagged r1 r2 into r3 r4
        // becomes
        // (r2) * (w1) = (1 - r4)  // r2=0 => r4=1; r2≠0 ∧ r4=0 => w1 = 1/r2
        // (r2) * (r4) = (0)       // r2≠0 => r4=0
        // (r1) * (w1) = (r3)      // r2≠0 => w1=(1/r2) => r3 = r1/r2
        // (r3) * (r4) = (0)       // r2=0 => r4=1 => r3 = 0, and
        //                     // r2≠0 => r4=0 ∧ r3 is not further constrained
        // The first two constraints compute (1 - r4) = indicator(r2);
        // the third constraint computes r3 as the quotient for the case
        // when r2 is not zero;
        // the fourth constraint forces r3 to zero when r2 is zero (and doesn't
        // further constrain r3 when r2 is not zero, since in that case r4=0).

        // r1->self, r2->other, r3->quotient, r4->flag

        // TODO: refine mode handling
        // Note that witness!() sets mode on the new circuit variable,
        // so we want to make sure we are setting it correctly.

        // The witness can be 0 when r2 is 0 (must be 1/r2 otherwise).
        let w: Field<E> =
            witness!(|other| { if other.is_zero() { console::Field::zero() } else { console::Field::one() / other } });
        // r4 is 1 when the divisor is 0, otherwise 0.
        let flag: Boolean<E> = witness!(|other| { other.is_zero() });
        // (r1) * (w1) = (r3)
        let quotient = self * &w;

        // Enforce the remaining constraints
        // (r1) * (w1) = (1 - r4)
        E::enforce(|| (&other, &w, !&flag));

        // (r2) * (r4) = (0)
        E::enforce(|| (&other, &flag, E::zero()));

        // (r3) * (r4) = (0)
        E::enforce(|| (&quotient, &flag, E::zero()));

        // Returns a boolean flag.
        (quotient, flag)
    }
}

impl<E: Environment> Metrics<dyn DivFlagged<Field<E>, Output = (Field<E>, Boolean<E>)>> for Field<E> {
    type Case = (Mode, Mode);

    fn count(case: &Self::Case) -> Count {
        match case {
            (Mode::Constant, Mode::Constant) | (_, Mode::Constant) => Count::is(1, 0, 0, 0),
            (Mode::Constant, _) => Count::is(0, 0, 1, 1),
            (_, _) => Count::is(0, 0, 2, 2),
        }
    }
}

impl<E: Environment> OutputMode<dyn DivFlagged<Field<E>, Output = (Field<E>, Boolean<E>)>> for Field<E> {
    type Case = (CircuitType<Field<E>>, CircuitType<Field<E>>);

    fn output_mode(case: &Self::Case) -> Mode {
        match (case.0.mode(), case.1.mode()) {
            (Mode::Constant, Mode::Constant) => Mode::Constant,
            (Mode::Public, Mode::Constant) => match &case.1 {
                CircuitType::Constant(constant) => match constant.eject_value().is_one() {
                    true => Mode::Public,
                    false => Mode::Private,
                },
                _ => E::halt("The constant is required to determine the output mode of Public + Constant"),
            },
            (_, _) => Mode::Private,
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use snarkvm_circuit_environment::{Circuit, assert_count_fails};

    const ITERATIONS: u64 = 1000;

    fn check_div_flagged(
        name: &str,
        first: &console::Field<<Circuit as Environment>::Network>,
        second: &console::Field<<Circuit as Environment>::Network>,
        mode_a: Mode,
        mode_b: Mode,
    ) {
        let a = Field::<Circuit>::new(mode_a, *first);
        let b = Field::<Circuit>::new(mode_b, *second);

        if second.is_zero() {
            Circuit::scope(name, || {
                let (result, flag) = a.div_flagged(b);
                let fieldzero: Field<Circuit> = Field::zero();
                assert_eq!(result.eject_value(), fieldzero.eject_value());
                assert_eq!(flag.eject_value(), true);
            });
        } else {
            let expected = *first / *second;
            Circuit::scope(name, || {
                let (candidate, flag) = a.clone().div_flagged(b.clone());
                assert_eq!(expected, candidate.eject_value(), "({} / {})", a.eject_value(), b.eject_value());
                assert_eq!(flag.eject_value(), false);
                // TODO: fix macros to handle tuple of outputs:
                //assert_count!(DivFlagged(Field, Field) => (Field, Boolean), &(a.eject_mode(), b.eject_mode()));
                //assert_output_mode!(DivFlagged(Field, Field) => (Field, Boolean), &(CircuitType::from(a), CircuitType::from(b)), candidate);
            });
        }
    }

    fn run_test(mode_a: Mode, mode_b: Mode) {
        let mut rng = TestRng::default();

        for i in 0..ITERATIONS {
            let first = Uniform::rand(&mut rng);
            let second = Uniform::rand(&mut rng);

            let name = format!("DivFlagged: a / b {i}");
            check_div_flagged(&name, &first, &second, mode_a, mode_b);

            // Check division by one.
            let one = console::Field::<<Circuit as Environment>::Network>::one();
            let name = format!("DivFlagged By One {i}");
            check_div_flagged(&name, &first, &one, mode_a, mode_b);

            // Check division by zero.
            let zero = console::Field::<<Circuit as Environment>::Network>::zero();
            let name = format!("DivFlagged By Zero {i}");
            check_div_flagged(&name, &first, &zero, mode_a, mode_b);
        }
    }

    #[test]
    fn test_constant_div_constant() {
        run_test(Mode::Constant, Mode::Constant);
    }

    #[test]
    fn test_constant_div_public() {
        run_test(Mode::Constant, Mode::Public);
    }

    #[test]
    fn test_constant_div_private() {
        run_test(Mode::Constant, Mode::Private);
    }

    #[test]
    fn test_public_div_constant() {
        run_test(Mode::Public, Mode::Constant);
    }

    #[test]
    fn test_public_div_public() {
        run_test(Mode::Public, Mode::Public);
    }

    #[test]
    fn test_public_div_private() {
        run_test(Mode::Public, Mode::Private);
    }

    #[test]
    fn test_private_div_constant() {
        run_test(Mode::Private, Mode::Constant);
    }

    #[test]
    fn test_private_div_public() {
        run_test(Mode::Private, Mode::Public);
    }

    #[test]
    fn test_private_div_private() {
        run_test(Mode::Private, Mode::Private);
    }
}
