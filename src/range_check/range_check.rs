use halo2_proofs::{
    arithmetic::FieldExt, circuit::*, dev::MockProver, pasta::Fp, plonk::*, poly::Rotation,
};
use std::marker::PhantomData;

use halo2_proofs::{
    circuit::floor_planner::V1,
    dev::{FailureLocation, VerifyFailure},
    plonk::Circuit,
};
use std::any::{Any, TypeId};

struct Sizes {
    RANGE: usize,
    NUM_BITS: usize,
    LOOKUP_RANGE: usize,
}
#[derive(Clone, Copy, Debug)]

struct RangeCheckConfig<F: FieldExt, const RANGE: usize> {
    value: Column<Advice>,
    q_range_check: Selector,
    _marker: PhantomData<F>,
}

impl<F: FieldExt, const RANGE: usize> RangeCheckConfig<F, RANGE> {
    fn configure(
        meta: &mut ConstraintSystem<F>,
        q_range_check: Selector,
        value: Column<Advice>,
    ) -> Self {
        let config = Self {
            value,
            q_range_check,
            _marker: PhantomData,
        };

        meta.create_gate("range check", |meta| {
            let q_range_check = meta.query_selector(q_range_check);
            let value = meta.query_advice(value, Rotation::cur());
            let range_check = |range: usize, value: Expression<F>| {
                (0..range).fold(
                    value.clone(),
                    // We do value.clone() above to initialize the types correctly. Since we want it to check 0 equality, it doesn't really matter what it is
                    |acc: halo2_proofs::plonk::Expression<F>, i| {
                        acc * (value.clone()
                            - halo2_proofs::plonk::Expression::Constant(F::from(i as u64)))
                    },
                )
            };
            Constraints::with_selector(q_range_check, [("range check", range_check(RANGE, value))])
        });
        config
    }
}
#[derive(Clone, Copy, Debug)]

struct RangeCheckChip<F: FieldExt, const RANGE: usize> {
    config: RangeCheckConfig<F, RANGE>,
    _marker: PhantomData<F>,
}

impl<F: FieldExt, const RANGE: usize> RangeCheckChip<F, RANGE> {
    fn construct(config: RangeCheckConfig<F, RANGE>) -> Self {
        Self {
            config,
            _marker: PhantomData,
        }
    }

    fn configure(meta: &mut ConstraintSystem<F>) -> RangeCheckConfig<F, RANGE> {
        let value = meta.advice_column();
        let q_range_check = meta.selector();
        let config = RangeCheckConfig::configure(meta, q_range_check, value);
        config
    }

    fn assign(
        &self,
        mut layouter: impl Layouter<F>,
        value: Value<F>,
    ) -> Result<AssignedCell<F, F>, halo2_proofs::plonk::Error> {
        layouter.assign_region(
            || "Range chip brute force",
            |mut region| {
                let offset = 0;
                self.config.q_range_check.enable(&mut region, offset);
                let advice: AssignedCell<F, F> = region
                    .assign_advice(|| "value", self.config.value, offset, || value)
                    .map(|value| value as AssignedCell<F, F>)?;
                Ok(advice)
            },
        )
    }
}

#[derive(Debug, Default)]
struct RangeCheckCircuit<F: FieldExt, const RANGE: usize> {
    value: Value<F>,
}

impl<F: FieldExt, const RANGE: usize> Circuit<F> for RangeCheckCircuit<F, RANGE> {
    type Config = RangeCheckConfig<F, RANGE>;
    type FloorPlanner = V1;

    // Circuit without witnesses, called only during key generation
    fn without_witnesses(&self) -> Self {
        Self::default()
    }

    // Has the arrangement of columns. Called only during keygen, and will just call chip config most of the time
    fn configure(meta: &mut ConstraintSystem<F>) -> Self::Config {
        RangeCheckChip::configure(meta)
    }

    // Take the output of configure and floorplanner type to make the actual circuit
    // Called both at key generation time, and proving time with a specific witness
    // Will call all of the copy constraints
    fn synthesize(
        &self,
        config: Self::Config,
        mut layouter: impl Layouter<F>,
    ) -> Result<(), Error> {
        let chip = RangeCheckChip::construct(config);
        chip.assign(layouter.namespace(|| "value_check"), self.value);
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use halo2_proofs::{
        circuit::floor_planner::V1,
        dev::{FailureLocation, MockProver, VerifyFailure},
        pasta::Fp,
        plonk::{Any, Circuit},
    };

    #[test]
    fn test_range_check_correct() {
        let k: u32 = 9; // log_2 of row count
        let value = Fp::from(5);
        const RANGE: usize = 10;
        let circuit = RangeCheckCircuit::<Fp, RANGE> {
            value: Value::known(value.into()),
        };
        // This prover is faster and 'fake', but is mostly a devtool for debugging
        let prover = MockProver::run(k, &circuit, vec![]).unwrap();
        // This function will pretty-print on errors
        prover.assert_satisfied();
    }

    #[test]
    fn test_range_check_wrong() {
        let k: u32 = 9; // log_2 of row count
        let value = Fp::from(11);
        const RANGE: usize = 10;
        let circuit = RangeCheckCircuit::<Fp, RANGE> {
            value: Value::known(value.into()),
        };
        // This prover is faster and 'fake', but is mostly a devtool for debugging
        let prover = MockProver::run(k, &circuit, vec![]).unwrap();
        // This function will pretty-print on errors
        match prover.verify() {
            Err(e) => {
                println!("Error successfully achieved!");
            }
            _ => assert_eq!(1, 0),
        }
    }

    #[cfg(feature = "dev-graph")]
    #[test]
    fn print_range_chip_vanilla() {
        use plotters::prelude::*;

        let root =
            BitMapBackend::new("range-chip-vanilla-layout.png", (1024, 3096)).into_drawing_area();
        root.fill(&WHITE).unwrap();
        let root = root
            .titled("Range Chip Vanilla Layout", ("sans-serif", 60))
            .unwrap();

        let circuit = MyCircuit::<Fp, 8, 256> {
            value: Value::unknown(),
            lookup_value: Value::unknown(),
        };
        halo2_proofs::dev::CircuitLayout::default()
            .render(9, &circuit, &root)
            .unwrap();
    }
}
