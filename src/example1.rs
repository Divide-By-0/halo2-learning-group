use halo2_proofs::{
    arithmetic::FieldExt,
    circuit::*,
    plonk::*,
    poly::Rotation,
}

#[derive(Clone, Debug)]
struct ACell<F: FieldExt>
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
        let (col_a, col_b, col_c) = advice[0];
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
    ) {
        layouter.assign_region(
            || "First row",
            |mut region| {
                self.config.selector.enable(&mut region, 0);
                let a_cell = region.assign_advice(
                    || "a",
                    self.config.advice[0],
                    0,
                    || a.or_then(Error::Synthesis),
                )?;
                let offset = 0;
                self.assign_region(&mut region, offset, a, b)
            },
        )
    }

    fn assign(
        &self,
        region: &mut Region<'_, F>,
        offset: usize,
        a: Option<F>,
        b: Option<F>,
    ) -> Result<(Option<F>, Option<F>), Error> {
        let config = self.config();

        region.assign_advice(
            || "a",
            config.advice[0],
            offset,
            || a.ok_or(Error::SynthesisError),
        )?;
        region.assign_advice(
            || "b",
            config.advice[1],
            offset,
            || b.ok_or(Error::SynthesisError),
        )?;
        region.assign_advice(
            || "c",
            config.advice[2],
            offset,
            || {
                let a = a.ok_or(Error::SynthesisError)?;
                let b = b.ok_or(Error::SynthesisError)?;
                Ok(a * b)
            },
        )?;

        region.assign_fixed(|| "selector", config.selector, offset, || Ok(F::one()))?;

        Ok((b, a.map(|a| a * b)))
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
        FibonacciChip::configure(meta, [col_a, col_b, col_c]);
    }

    fn synthesize(
        &self,
        config: Self::Config,
        region: &mut Region<'_, F>,
    ) -> Result<(), Error> {
        let chip = FibonacciChip::construct(config);
        chip.assign_first_row(layouter.namespace(|| "first row"), self.a, self.b); // 2 private inputs
        let mut offset = 0;
        let mut a = self.a;
        let mut b = self.b;

        for _ in 0..10 {
            let (new_a, new_b) = chip.assign(region, offset, a, b)?;
            a = new_a;
            b = new_b;
            offset += 1;
        }

        Ok(())
    }
}


fn main() {
    println!("Hello, world!");
}
