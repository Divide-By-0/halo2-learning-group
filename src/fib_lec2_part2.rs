// We will build off of the lec2 version to have only one advice column instead

use halo2_proofs::{
    arithmetic::FieldExt,
    circuit::*,
    plonk::*,
    poly::Rotation,
    pasta::Fp, dev::MockProver,
};

#[derive(Clone, Debug)]
struct ACell<F: FieldExt>(AssignedCell<F, F>);

// Defines the configuration of all the columns, and all of the column definitions
// Will be incrementally populated and passed around
#[derive(Clone, Debug)]
struct FibonacciConfig {
    pub advice: [Column<Advice>; 1],
    pub selector: Selector,
    pub instance: [Column<Instance>; 1],
}

struct FibonacciChip<F: FieldExt> {
    config: FibonacciConfig,
    _marker: std::marker::PhantomData<F>,
    // In rust, when you have a struct that is generic over a type parameter (here F),
    // but the type parameter is not referenced in a field of the struct,
    // you have to use PhantomData to virtually reference the type parameter,
    // so that the compiler can track it.  Otherwise it would give an error. - Jason
}

impl<F: FieldExt> FibonacciChip<F> {
    // Default constructor
    fn construct(config: FibonacciConfig) -> Self {
        Self {
            config,
            _marker: std::marker::PhantomData,
        }
    }

    // Configure will set what type of columns things are, enable equality, create gates, and return a config with all the gates
    fn configure(
        meta: &mut ConstraintSystem<F>,
        advice: [Column<Advice>; 1],
        instance: [Column<Instance>; 1],
    ) -> FibonacciConfig {
        let col_a = advice[0];
        let selector: Selector = meta.selector();

        // enable_equality has some cost, so we only want to define it on rows where we need copy constraints
        meta.enable_equality(col_a);
        meta.enable_equality(instance[0]);

        // Defining a create_gate here applies it over every single column in the circuit
        meta.create_gate("Fibonacci", |meta| {
            let a = meta.query_advice(col_a, Rotation::cur());
            let b = meta.query_advice(col_a, Rotation::next());
            let c = meta.query_advice(col_a, Rotation(2));

            // We will use the selector column to decide when to turn this gate on and off, since we probably don't want it on every row
            let s = meta.query_selector(selector);

            // a + b = c
            vec![s * (a + b - c)]
        });

        FibonacciConfig { advice: [col_a], selector, instance }
    }

    // These assign functions are to be called by the synthesizer, and will be used to assign values to the columns (the witness)
    // The layouter will collect all the region definitions and compress it horizontally (i.e. squeeze up/down)
    // but not vertically (i.e. will not squeeze left/right, at least right now)
    fn assign(
        &self,
        mut layouter: impl Layouter<F>,
        // a: Option<F>,
        // b: Option<F>,
        nrows: usize,
    ) -> Result<(ACell<F>), Error> {
        layouter.assign_region(
            || "entire table",
            |mut region| {
                self.config.selector.enable(&mut region, 0)?;
                self.config.selector.enable(&mut region, 1)?;
                let a_cell: ACell<F> = ACell::<F>(region.assign_advice_from_instance(|| "a", self.config.instance[0], 0, self.config.advice[0], 0)?);
                let b_cell: ACell<F> = ACell::<F>(region.assign_advice_from_instance(|| "b", self.config.instance[0], 1, self.config.advice[0], 1)?);
                // let a_cell = region.assign_advice(
                //     || "a",
                //     self.config.advice[0],
                //     0,
                //     || a.ok_or(Error::Synthesis),
                // ).map(ACell)?;
                // let b_cell = region.assign_advice(
                //     || "b",
                //     self.config.advice[1],
                //     0,
                //     || b.ok_or(Error::Synthesis),
                // ).map(ACell)?;
                let mut prev_a: ACell<F> = a_cell;
                let mut prev_b: ACell<F> = b_cell;
                for i in 2..nrows {
                    if i < nrows - 2 {
                        self.config.selector.enable(&mut region, i)?;
                    }
                    let c_val = prev_a.0.value().and_then(|a| prev_b.0.value().map(|b| *a + *b));

                    let c_cell: ACell<F> = region.assign_advice(
                        || "c",
                        self.config.advice[0],
                        i,
                        || c_val.ok_or(Error::Synthesis),
                    ).map(ACell)?;
                    prev_a = prev_b;
                    prev_b = c_cell;
                }
                Ok(prev_b)
            },
        )
    }

    pub fn expose_public(&self, mut layouter: impl Layouter<F>, cell: &ACell<F>, row: usize){
        layouter.constrain_instance(
            cell.0.cell(), self.config.instance[0], row
        );
    }
}

#[derive(Default)]
struct FibonacciCircuit<F: FieldExt> {
    pub a: Option<F>,
    pub b: Option<F>,
}

// Our circuit will instantiate an instance based on the interface defined on the chip and floorplanner (layouter)
// There isn't a clear reason this and the chip aren't the same thing, except for better abstractions for complex circuits
impl<F: FieldExt> Circuit<F> for FibonacciCircuit<F> {
    type Config = FibonacciConfig;
    type FloorPlanner = SimpleFloorPlanner;

    // Circuit without witnesses, called only during key generation
    fn without_witnesses(&self) -> Self {
        Self::default()
    }

    // Has the arrangement of columns. Called only during keygen, and will just call chip config most of the time
    fn configure(meta: &mut ConstraintSystem<F>) -> Self::Config {
        let col_a: Column<Advice> = meta.advice_column();
        let instance = meta.instance_column();
        FibonacciChip::configure(meta, [col_a], [instance])
    }

    // Take the output of configure and floorplanner type to make the actual circuit
    // Called both at key generation time, and proving time with a specific witness
    // Will call all of the copy constraints
    fn synthesize(
        &self,
        config: Self::Config,
        mut layouter: impl Layouter<F>,
        // region: &mut Region<'_, F>,
    ) -> Result<(), Error> {
        let chip = FibonacciChip::construct(config);
        let mut output = chip.assign(
            layouter.namespace(|| "table"),
            // self.a, self.b,
            10
        )?; // 2 private inputs

        // Define the copy constraint from the instance column to our relevant advice cell
        // chip.expose_public(layouter.namespace(|| "private a"), &self.a?, 0);
        // chip.expose_public(layouter.namespace(|| "private b"), &self.b?, 1);
        // for _i in 3..10 {
        //     let c_cell = chip.assign_row(
        //         layouter.namespace(|| "next row"),
        //         &prev_b,
        //         &prev_c)?;
        //     prev_b = prev_c;
        //     prev_c = c_cell;
        // }
        // Define the copy constraint from the instance column to our relevant advice cell
        chip.expose_public(layouter.namespace(|| "out"), &output, 2); // Why is row 2 instead of 10?
        Ok(())
    }
}

mod tests {
    use super::*;
    #[cfg(feature = "dev-graph")]
    #[test]
    fn print(){

    let k = 4;
    let a = Fp::from(1);
    let b = Fp::from(1);
    let out = Fp::from(55);
    let circuit = FibonacciCircuit {
        a:Some(a), b:Some(b)
    };
    let mut public_inputs = vec![a, b, out];
    // This prover is faster and 'fake', but is mostly a devtool for debugging
    let prover = MockProver::run(k, &circuit, vec![public_inputs.clone()]).unwrap();
    // This function will pretty-print on errors
    prover.assert_satisfied();
    public_inputs[2] += Fp::one();
    let prover = MockProver::run(k, &circuit, vec![public_inputs.clone()]).unwrap();
    // prover.assert_satisfied();

    use plotters::prelude::*;

    let root = BitMapBackend::new("fib-2—layout.png", (1024, 7680)).into_drawing_area();
    //root.fiti(&WHITE).unwrap();
    let root1 = root.titled("Fib 2 Layout", ("sans—serif", 60)).unwrap();
    let circuit:FibonacciCircuit<Fp> = FibonacciCircuit { a: None, b: None };
    halo2_proofs::dev::CircuitLayout::default()
        .render(4, &circuit, &root1)
        .unwrap();

    }
}

// 1 1 2 3 5 8 13 21 34 55
