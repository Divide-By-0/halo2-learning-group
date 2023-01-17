use std::marker::PhantomData;

use halo2_proofs::{
    arithmetic::FieldExt,
    circuit::{AssignedCell, Layouter, Value},
    plonk::{Advice, Assigned, Column, ConstraintSystem, Constraints, Error, Expression, Selector},
    poly::Rotation,
};

use crate::table::RangeTableConfig;

/// Decomposes an $n$-bit field element $\alpha$ into $W$ windows, each window
/// being a $K$-bit word, using a running sum $z$.
/// We constrain $K \leq 3$ for this helper.
///     $$\alpha = k_0 + (2^K) k_1 + (2^{2K}) k_2 + ... + (2^{(W-1)K}) k_{W-1}$$
///
/// $z_0$ is initialized as $\alpha$. Each successive $z_{i+1}$ is computed as
///                $$z_{i+1} = (z_{i} - k_i) / (2^K).$$
/// $z_W$ is constrained to be zero.
/// The difference between each interstitial running sum output is constrained
/// to be $K$ bits, i.e.
///                      `range_check`($k_i$, $2^K$),
/// where
/// ```text
///   range_check(word)
///     = word * (1 - word) * (2 - word) * ... * ((range - 1) - word)
/// ```
///
/// Given that the `range_check` constraint will be toggled by a selector, in
/// practice we will have a `selector * range_check(word)` expression
/// of degree `range + 1`.
///
/// This means that $2^K$ has to be at most `degree_bound - 1` in order for
/// the range check constraint to stay within the degree bound.
///
/// This is a custom built version of the decompose running sum function.

#[derive(Debug, Clone)]
/// A range-constrained value in the circuit produced by the DecomposeRangeCheckConfig.
struct RangeConstrained<F: FieldExt>(AssignedCell<Assigned<F>, F>);
// RANGE is the size of the total range we want to check.
// LOOKUP_RANGE is the size of our lookup table i.e. the max size we can lookup in one check to the table.
// NUM_BITS is the max number of bits we want to use to represent each value in the lookup range.
const RANGE: usize = 64;
const NUM_BITS: usize = 3;
const LOOKUP_RANGE: usize = 8;

#[derive(Debug, Clone)]
struct DecomposeRangeCheckConfig<F: FieldExt> {
    value: Column<Advice>,
    value_decomposed: Column<Advice>, // Assume this value perfectly decomposes
    q_decomposed: Selector,
    q_range_check: Selector,
    table: RangeTableConfig<F, LOOKUP_RANGE>,
    _marker: PhantomData<F>,
}

impl<F: FieldExt> DecomposeRangeCheckConfig<F> {
    pub fn configure(meta: &mut ConstraintSystem<F>, value: Column<Advice>) -> Self {
        let value = meta.advice_column();
        let value_decomposed = meta.advice_column();
        let q_decomposed = meta.selector();
        let q_range_check = meta.complex_selector();
        let table = RangeTableConfig::configure(meta);
        //        value     |    decomposed     |    q_range_check     |    q_decomposed
        //       --------------------------------------------------------------------------
        //          v       |         v_0       |          1           |        1
        //          -       |         v_1       |          0           |        1
        //          -       |         v_2       |          0           |        1

        // Lookup each decomposed value individually, not paying attention to bit count
        meta.lookup(|meta| {
            let q = meta.query_selector(q_decomposed);
            let decomposed_value = meta.query_advice(value_decomposed, Rotation::cur());
            vec![(q.clone() * decomposed_value, table.value)]
        });

        // Ensure that the decomposed values add up to the original value
        meta.create_gate("decompose", |meta| {
            let q = meta.query_selector(q_range_check);
            let value = meta.query_advice(value, Rotation::cur());
            let mut decomposed_values = vec![];
            let decomposed_parts = RANGE / LOOKUP_RANGE;
            for i in 0..decomposed_parts {
                decomposed_values.push(meta.query_advice(value_decomposed, Rotation(i as i32)));
            }

            // Given a range R and a value v, returns the expression
            // (v) * (1 - v) * (2 - v) * ... * (R - 1 - v)
            let decomposed_check =
                |decomposed_parts: usize,
                 value: Expression<F>,
                 decomposed_values: Vec<Expression<F>>| {
                    assert!(decomposed_parts > 0, "Empty value!");
                    assert!(
                        NUM_BITS * decomposed_parts < 64,
                        "Value doesn't fit in bits!"
                    );
                    const multiplier: usize = 1 << NUM_BITS;
                    (0..decomposed_parts).fold(
                        Expression::Constant(F::from(0 as u64)),
                        |expr, i| {
                            expr + decomposed_values[i].clone()
                                * Expression::Constant(F::from(1_u64 << (NUM_BITS * i)))
                        },
                    ) - value
                };

            Constraints::with_selector(
                q,
                [(
                    "range check",
                    decomposed_check(decomposed_parts, value, decomposed_values),
                )],
            )
        });

        Self {
            value,
            value_decomposed,
            q_decomposed,
            q_range_check,
            table,
            _marker: PhantomData,
        }
    }

    pub fn assign(
        &self,
        mut layouter: impl Layouter<F>,
        value: Value<Assigned<F>>,
    ) -> Result<RangeConstrained<F>, Error> {
        layouter.assign_region(
            || "Assign value",
            |mut region| {
                let offset = 0;

                // Enable q_range_check
                self.q_range_check.enable(&mut region, offset)?;

                // Assign value
                region
                    .assign_advice(|| "value", self.value, offset, || value)
                    .map(RangeConstrained)
            },
        )
    }
}

#[cfg(test)]
mod tests {
    use halo2_proofs::{
        circuit::floor_planner::V1,
        dev::{FailureLocation, MockProver, VerifyFailure},
        pasta::Fp,
        plonk::{Any, Circuit},
    };

    use super::*;

    #[derive(Default)]
    struct MyCircuit<F: FieldExt> {
        value: Value<Assigned<F>>,
    }

    impl<F: FieldExt> Circuit<F> for MyCircuit<F> {
        type Config = DecomposeRangeCheckConfig<F>;
        type FloorPlanner = V1;

        fn without_witnesses(&self) -> Self {
            Self::default()
        }

        fn configure(meta: &mut ConstraintSystem<F>) -> Self::Config {
            let value = meta.advice_column();
            DecomposeRangeCheckConfig::configure(meta, value)
        }

        fn synthesize(
            &self,
            config: Self::Config,
            mut layouter: impl Layouter<F>,
        ) -> Result<(), Error> {
            config.assign(layouter.namespace(|| "Assign value"), self.value)?;

            Ok(())
        }
    }

    #[test]
    fn test_range_check_1() {
        let k = 4; // 8, 128, etc

        // Successful cases
        for i in 0..RANGE {
            let circuit = MyCircuit::<Fp> {
                value: Value::known(Fp::from(i as u64).into()),
            };

            let prover = MockProver::run(k, &circuit, vec![]).unwrap();
            prover.assert_satisfied();
        }

        // Out-of-range `value = 8`
        {
            let circuit = MyCircuit::<Fp> {
                value: Value::known(Fp::from(RANGE as u64).into()),
            };
            let prover = MockProver::run(k, &circuit, vec![]).unwrap();
            assert_eq!(
                prover.verify(),
                Err(vec![VerifyFailure::ConstraintNotSatisfied {
                    constraint: ((0, "range check").into(), 0, "range check").into(),
                    location: FailureLocation::InRegion {
                        region: (0, "Assign value").into(),
                        offset: 0
                    },
                    cell_values: vec![(((Any::Advice, 0).into(), 0).into(), "0x8".to_string())]
                }])
            );
        }
    }

    #[cfg(feature = "dev-graph")]
    #[test]
    fn print_range_check_1() {
        use plotters::prelude::*;

        let root = BitMapBackend::new("range-check-1-layout.png", (1024, 3096)).into_drawing_area();
        root.fill(&WHITE).unwrap();
        let root = root
            .titled("Range Check 1 Layout", ("sans-serif", 60))
            .unwrap();

        let circuit = MyCircuit::<Fp, 8> {
            value: Value::unknown(),
        };
        halo2_proofs::dev::CircuitLayout::default()
            .render(3, &circuit, &root)
            .unwrap();
    }
}
