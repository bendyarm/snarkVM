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

// Define the InverseFlagged trait
pub trait InverseFlagged {
    type Output;
    fn inverse_flagged(self) -> Self::Output;
}

impl<E: Environment> InverseFlagged for Field<E> {
    type Output = (Field<E>, Boolean<E>);

    fn inverse_flagged(self) -> Self::Output {
        // inv.flagged r1 into r2 r3
        // becomes
        // (r1) * (w1) = (1 - r3)  // r1=0 => r3=1; r1≠0 ∧ r3=0 => w1 = 1/r1
        // (r1) * (r3) - (0)       // r1≠0 => r3=0
        // (w1) * (1 - r3) = (r2)  // r1=0 => r3=1 => r2=0; r1≠0 => r2=w1=1/r1
        //
        // The first two constraints compute (1 - r3) = indicator(r1);
        // the third constraint multiplies that indicator by w1 to get r2, so
        // if r1 was zero, r2 will be zero, and
        // if r1 was non-zero, r2 will be 1/r1.

        // r1->self, r2->inverse, r3->flag

        // TODO: refine mode handling
        let mode = if self.eject_mode() == Mode::Constant { Mode::Constant } else { Mode::Private };

        // The witness can be 0 when r1 is 0 (must be 1/r1 otherwise).
        // Init console_witness to zero but set it in witness!() below.
        let mut console_witness = console::Field::zero();

        let w: Field<E> = witness!(|self| {
            if self.is_zero() {
                console_witness = console::Field::zero();
                console_witness
            } else {
                console_witness = console::Field::one() / self;
                console_witness
            }
        });
        // r3 is 1 when the divisor is 0, otherwise 0.
        let flag: Boolean<E> = witness!(|self| { self.is_zero() });

        // Enforce the constraints.
        // (r1) * (w1) = (1 - r3)
        E::enforce(|| (&self, &w, !&flag));

        // (r1) * (r3) = (0)
        E::enforce(|| (&self, &flag, E::zero()));

        // (w1) * (1 - r3) = (r2)
        let inverse = Field::new(mode, console_witness);
        E::enforce(|| (&w, !&flag, &inverse));

        (inverse, flag)
    }
}

impl<E: Environment> Metrics<dyn InverseFlagged<Output = (Field<E>, Boolean<E>)>> for Field<E> {
    type Case = Mode;

    fn count(case: &Self::Case) -> Count {
        match case.is_constant() {
            true => Count::is(1, 0, 0, 0),
            false => Count::is(0, 0, 1, 1),
        }
    }
}

impl<E: Environment> OutputMode<dyn InverseFlagged<Output = (Field<E>, Boolean<E>)>> for Field<E> {
    type Case = Mode;

    fn output_mode(case: &Self::Case) -> Mode {
        match case.is_constant() {
            true => Mode::Constant,
            false => Mode::Private,
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use snarkvm_circuit_environment::Circuit;

    const ITERATIONS: u64 = 1_000;

    fn check_inverse_flagged(name: &str, mode: Mode, rng: &mut TestRng) {
        for i in 0..ITERATIONS {
            // We try 0.inverse_flagged() for the first iteration,
            // and sample a random element for the others

            let given: console::Field<<Circuit as Environment>::Network> = match i == 0 {
                true => console::Field::zero(),
                false => Uniform::rand(rng),
            };

            // create a new field element of the circuit
            let a = Field::<Circuit>::new(mode, given);

            if given.is_zero() {
                Circuit::scope(name, || {
                    let (result, flag) = a.inverse_flagged();
                    let fieldzero: Field<Circuit> = Field::zero();
                    assert_eq!(result.eject_value(), fieldzero.eject_value());
                    assert_eq!(flag.eject_value(), true);
                });
            } else {
                let expected = given.inverse().unwrap();
                Circuit::scope(name, || {
                    let (result, flag) = a.inverse_flagged();
                    assert_eq!(expected, result.eject_value());
                    assert_eq!(flag.eject_value(), false);
                    // TODO: fix macros to handle tuple of outputs:
                    // assert_count!(InverseFlagged(Field) => (Field, Boolean), &mode);
                    // assert_output_mode!(InverseFlagged(Field) => (Field, Boolean), &mode, result);
                });
            };
            Circuit::reset();
        }
    }

    #[test]
    fn test_inverse() {
        let mut rng = TestRng::default();

        check_inverse_flagged("Constant", Mode::Constant, &mut rng);
        check_inverse_flagged("Public", Mode::Public, &mut rng);
        check_inverse_flagged("Private", Mode::Private, &mut rng);
    }
}
