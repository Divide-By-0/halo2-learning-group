use halo2_proofs::{
    arithmetic::FieldExt,
    circuit::*,
    plonk::*,
    poly::Rotation,
    pasta::Fp, dev::MockProver,
};

#[derive(Clone, Debug)]
struct ACell<F: FieldExt>(AssignedCell<F, F>);
#[derive(Clone, Debug)]
struct FibonacciConfig {
    pub advice: [Column<Advice>; 3],
    pub selector: Selector,
}

struct FibonacciChip<F: FieldExt> {
    config: FibonacciConfig,
    _marker: std::marker::PhantomData<F>,
}

impl<F: FieldExt> FibonacciChip<F> {
    fn construct(config: FibonacciConfig) -> Self {
        Self {
            config,
            _marker: std::marker::PhantomData,
        }
    }

    fn configure(
        meta: &mut ConstraintSystem<F>,
        advice: [Column<Advice>; 3],
    ) -> FibonacciConfig {
        let col_a = advice[0];
        let col_b = advice[1];
        let col_c = advice[2];
        meta.enable_equality(col_a);
        meta.enable_equality(col_b);
        meta.enable_equality(col_c);
        let selector: Selector = meta.selector();

        meta.create_gate("Fibonacci", |meta| {
            let a = meta.query_advice(col_a, Rotation::cur());
            let b = meta.query_advice(col_b, Rotation::cur());
            let c = meta.query_advice(col_c, Rotation::cur());
            let s = meta.query_selector(selector);

            // a + b = c
            vec![s * (a + b - c)]
        });

        FibonacciConfig { advice: [col_a, col_b, col_c], selector }
    }

    fn assign_first_row(
        &self,
        mut layouter: impl Layouter<F>,
        a: Option<F>,
        b: Option<F>,
    ) -> Result<(ACell<F>, ACell<F>, ACell<F>), Error> {
        layouter.assign_region(
            || "first row",
            |mut region| {
                self.config.selector.enable(&mut region, 0)?;
                let a_cell = region.assign_advice(
                    || "a",
                    self.config.advice[0],
                    0,
                    || a.ok_or(Error::Synthesis),
                ).map(ACell)?;
                let b_cell = region.assign_advice(
                    || "b",
                    self.config.advice[1],
                    0,
                    || b.ok_or(Error::Synthesis),
                ).map(ACell)?;
                let c_val = a.and_then(|a| b.map(|b| a + b));

                let c_cell = region.assign_advice(
                    || "c",
                    self.config.advice[2],
                    0,
                    || c_val.ok_or(Error::Synthesis),
                ).map(ACell)?;
                Ok((a_cell, b_cell, c_cell))

                // let offset = 0;
                // self.assign_region(&mut region, offset, a, b)
            },
        )
    }

    fn assign_row(
        &self,
        mut layouter: impl Layouter<F>,
        prev_b: &ACell<F>,
        prev_c: &ACell<F>,
        // region: &mut Region<'_, F>,
        // offset: usize,
        // a: Option<F>,
        // b: Option<F>,
    ) -> Result<ACell<F>, Error> {
        layouter.assign_region(
            || "next row",
            |mut region| {
                self.config.selector.enable(&mut region, 0)?;
                prev_b.0.copy_advice(|| "a", &mut region, self.config.advice[0], 0)?;
                prev_c.0.copy_advice(|| "b", &mut region, self.config.advice[1], 0)?;
                let c_val = prev_b.0.value().and_then(
                    |b| prev_c.0.value().map(|c| *b + *c + *b)
                );
                let c_cell = region.assign_advice(
                    || "c",
                    self.config.advice[2],
                    0,
                    || c_val.ok_or(Error::Synthesis)).map(ACell);
                Ok(c_cell)
            }
        )?
    }
}

#[derive(Default)]
struct FibonacciCircuit<F: FieldExt> {
    pub a: Option<F>,
    pub b: Option<F>,
}

impl<F: FieldExt> Circuit<F> for FibonacciCircuit<F> {
    type Config = FibonacciConfig;
    type FloorPlanner = SimpleFloorPlanner;

    fn without_witnesses(&self) -> Self {
        Self::default()
    }

    fn configure(meta: &mut ConstraintSystem<F>) -> Self::Config {
        let col_a: Column<Advice> = meta.advice_column();
        let col_b: Column<Advice> = meta.advice_column();
        let col_c: Column<Advice> = meta.advice_column();
        FibonacciChip::configure(meta, [col_a, col_b, col_c])
    }

    fn synthesize(
        &self,
        config: Self::Config,
        mut layouter: impl Layouter<F>,
        // region: &mut Region<'_, F>,
    ) -> Result<(), Error> {
        let chip = FibonacciChip::construct(config);
        let (_, mut prev_b, mut prev_c) = chip.assign_first_row(
            layouter.namespace(|| "first row"),
            self.a, self.b)?; // 2 private inputs

        for _i in 3..10 {
            let c_cell = chip.assign_row(
                layouter.namespace(|| "next row"),
                &prev_b,
                &prev_c)?;
            prev_b = prev_c;
            prev_c = c_cell;
        }

        Ok(())
    }
}


fn main() {
    let k = 4;
    let a = Fp::from(1);
    let b = Fp::from(1);
    let circuit = FibonacciCircuit {
        a:Some(a), b:Some(b)
    };
    let prover = MockProver::run(k, &circuit, vec![]).unwrap();
    prover.assert_satisfied();
}
