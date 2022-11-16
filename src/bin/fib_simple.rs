//! simple fibonacci circuit
//!
//! we are going to prove that fib(5) = 8 when fib(0) = 0, fib(1) = 1

use halo2_proofs::circuit::Cell;
use halo2_proofs::{
    arithmetic::FieldExt,
    circuit::{AssignedCell, Layouter, Region, SimpleFloorPlanner, Value},
    dev::MockProver,
    halo2curves::secp256k1::Fp,
    plonk::{Advice, Circuit, Column, ConstraintSystem, Error, Instance, Selector},
    poly::Rotation,
};
use std::marker::PhantomData;

#[derive(Debug, Clone)]
struct FibConfig {
    // [a, b, c]
    advice: [Column<Advice>; 3],
    selector: Selector,
    instance: Column<Instance>,
}

struct FibChip<F: FieldExt> {
    config: FibConfig,
    _marker: PhantomData<F>,
}

impl<F: FieldExt> FibChip<F> {
    fn construct(config: FibConfig) -> Self {
        Self {
            config,
            _marker: PhantomData,
        }
    }

    fn configure(
        meta: &mut ConstraintSystem<F>,
        [col_a, col_b, col_c]: [Column<Advice>; 3],
        selector: Selector,
        instance: Column<Instance>,
    ) -> FibConfig {
        meta.enable_equality(col_a);
        meta.enable_equality(col_b);
        meta.enable_equality(col_c);
        meta.enable_equality(instance);

        meta.create_gate("fib", |meta| {
            let a = meta.query_advice(col_a, Rotation::cur());
            let b = meta.query_advice(col_b, Rotation::cur());
            let c = meta.query_advice(col_c, Rotation::cur());

            let s = meta.query_selector(selector);

            vec![s * (a + b - c)]
        });

        FibConfig {
            advice: [col_a, col_b, col_c],
            selector,
            instance,
        }
    }

    fn assign_setup(
        &self,
        region: &mut Region<'_, F>,
        n_0: F,
        n_1: F,
    ) -> Result<(AssignedCell<F, F>, AssignedCell<F, F>, AssignedCell<F, F>), Error> {
        let [col_a, col_b, col_c] = self.config.advice;

        self.config.selector.enable(region, 0)?;

        let a = region.assign_advice(|| "a", col_a, 0, || Value::known(n_0))?;
        let b = region.assign_advice(|| "b", col_b, 0, || Value::known(n_1))?;
        let c = region.assign_advice(|| "c", col_c, 0, || Value::known(n_0 + n_1))?;

        Ok((a, b, c))
    }

    fn assign_row(
        &self,
        region: &mut Region<'_, F>,
        offset: usize,
        last_b: AssignedCell<F, F>,
        last_c: AssignedCell<F, F>,
    ) -> Result<(AssignedCell<F, F>, AssignedCell<F, F>), Error> {
        let [col_a, col_b, col_c] = self.config.advice;

        self.config.selector.enable(region, offset)?;

        let a = last_b.copy_advice(|| "a", region, col_a, offset)?;
        let b = last_c.copy_advice(|| "b", region, col_b, offset)?;
        let c = region.assign_advice(
            || "c",
            col_c,
            offset,
            || a.value().zip(b.value()).map(|(a, b)| *a + *b),
        )?;

        Ok((b, c))
    }

    fn expose_public(
        &self,
        mut layouter: impl Layouter<F>,
        initial_a: Cell,
        initial_b: Cell,
        result: Cell,
    ) -> Result<(), Error> {
        layouter.constrain_instance(initial_a, self.config.instance, 0)?;
        layouter.constrain_instance(initial_b, self.config.instance, 1)?;
        layouter.constrain_instance(result, self.config.instance, 2)?;
        Ok(())
    }
}

#[derive(Default)]
struct FibCircuit<F> {
    pub n_0: F,
    pub n_1: F,
    pub n: F,
}

impl<F: FieldExt> Circuit<F> for FibCircuit<F> {
    type Config = FibConfig;
    type FloorPlanner = SimpleFloorPlanner;

    fn without_witnesses(&self) -> Self {
        Self::default()
    }

    fn configure(meta: &mut ConstraintSystem<F>) -> Self::Config {
        let col_a = meta.advice_column();
        let col_b = meta.advice_column();
        let col_c = meta.advice_column();
        let instance = meta.instance_column();
        let selector = meta.selector();

        FibChip::configure(meta, [col_a, col_b, col_c], selector, instance)
    }

    fn synthesize(
        &self,
        config: Self::Config,
        mut layouter: impl Layouter<F>,
    ) -> Result<(), Error> {
        let chip = FibChip::construct(config);
        let (initial_a, initial_b, result) = layouter.assign_region(
            || "rows",
            |mut region| {
                let (initial_a, mut b, mut c) =
                    chip.assign_setup(&mut region, self.n_0, self.n_1)?;
                let initial_b = b.clone();
                for row in 1..self.n.get_lower_32() as usize {
                    (b, c) = chip.assign_row(&mut region, row, b, c)?;
                }
                Ok((initial_a, initial_b, c))
            },
        )?;
        chip.expose_public(
            layouter.namespace(|| "expose_public"),
            initial_a.cell(),
            initial_b.cell(),
            result.cell(),
        )?;
        Ok(())
    }
}

fn main() {
    let circuit = FibCircuit {
        n: Fp::from(5),
        n_0: Fp::from(0),
        n_1: Fp::from(1),
    };

    let prover_success = MockProver::run(
        4,
        &circuit,
        vec![vec![Fp::from(0), Fp::from(1), Fp::from(8)]],
    )
    .unwrap();
    prover_success.assert_satisfied();
    let prover_failure = MockProver::run(
        4,
        &circuit,
        vec![vec![Fp::from(1), Fp::from(1), Fp::from(8)]],
    )
    .unwrap();
    prover_failure.verify().unwrap_err();
}
