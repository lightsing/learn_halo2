//! simple fibonacci circuit
//!
//! we are going to prove that fib(n) for 0 < n < MAX_N

use halo2_proofs::circuit::{AssignedCell, Cell, Region};
use halo2_proofs::dev::MockProver;
use halo2_proofs::halo2curves::secp256k1::Fp;
use halo2_proofs::{
    arithmetic::FieldExt,
    circuit::{Layouter, SimpleFloorPlanner, Value},
    plonk::{Advice, Circuit, Column, ConstraintSystem, Error, Expression, Instance, Selector},
    poly::Rotation,
};
use std::marker::PhantomData;

#[derive(Debug, Clone)]
struct FibConfig {
    // [n, l, r, n_inv]
    advice: [Column<Advice>; 4],
    selector: Selector,
    instance: Column<Instance>,
}

struct FibChip<F: FieldExt> {
    config: FibConfig,
    _marker: PhantomData<F>,
}

impl<F: FieldExt> FibChip<F> {
    const MAX_N: usize = 370;
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
        [col_n, col_l, col_r, col_n_inv]: [Column<Advice>; 4],
        selector: Selector,
        instance: Column<Instance>,
    ) -> FibConfig {
        meta.enable_equality(col_n);
        meta.enable_equality(col_l);
        meta.enable_equality(instance);

        meta.create_gate("n inv", |meta| {
            // n * (1 - n * n_inv) = 0
            let n = meta.query_advice(col_n, Rotation::cur());
            let n_inv = meta.query_advice(col_n_inv, Rotation::cur());
            let s = meta.query_selector(selector);

            vec![s * (n.clone() * (Expression::Constant(F::one()) - n * n_inv))]
        });

        meta.create_gate("fib", |meta| {
            let n = meta.query_advice(col_n, Rotation::cur());
            let n_next = meta.query_advice(col_n, Rotation::next());
            let n_inv = meta.query_advice(col_n_inv, Rotation::cur());
            let is_n_zero = Expression::Constant(F::one()) - n.clone() * n_inv;

            let l = meta.query_advice(col_l, Rotation::cur());
            let l_next = meta.query_advice(col_l, Rotation::next());
            let r = meta.query_advice(col_r, Rotation::cur());
            let r_next = meta.query_advice(col_r, Rotation::next());

            let s = meta.query_selector(selector);

            vec![
                // n == 0 => l' = r, n != 0 => l' = r
                s.clone() * (l_next - r.clone()),
                // n == 0 => r' = r
                s.clone() * is_n_zero.clone() * (r_next.clone() - r.clone()),
                // n == 0 => n' = 0
                s.clone() * is_n_zero.clone() * n_next.clone(),
                // n != 0 => r' = l + r
                s.clone() * (Expression::Constant(F::one()) - is_n_zero.clone()) * (l + r - r_next),
                // n != 0 => n' = n - 1
                s * (Expression::Constant(F::one()) - is_n_zero)
                    * (n - n_next - Expression::Constant(F::one())),
            ]
        });

        FibConfig {
            advice: [col_n, col_l, col_r, col_n_inv],
            selector,
            instance,
        }
    }

    fn assign_next_row(
        &self,
        region: &mut Region<'_, F>,
        current_row_offset: usize,
        n: Value<F>,
        l: Value<F>,
        r: Value<F>,
        n_inv: Value<F>,
    ) -> Result<
        (
            AssignedCell<F, F>,
            AssignedCell<F, F>,
            AssignedCell<F, F>,
            AssignedCell<F, F>,
        ),
        Error,
    > {
        let [col_n, col_l, col_r, col_n_inv] = self.config.advice;

        let is_n_zero = n.and_then(|n| n_inv.map(|n_inv| F::one() - n * n_inv));
        let next_n = n
            .zip(is_n_zero)
            .map(|(n, is_n_zero)| is_n_zero * n + (F::one() - is_n_zero) * (n - F::one()));
        let next_l = r;
        let next_r = l.zip(r).and_then(|(l, r)| {
            is_n_zero.map(|is_n_zero| is_n_zero * r + (F::one() - is_n_zero) * (l + r))
        });
        let next_n_inv = next_n.map(|n| n.invert().unwrap_or_else(F::zero));

        // we are done here
        if current_row_offset != Self::MAX_N - 2 {
            self.config
                .selector
                .enable(region, current_row_offset + 1)?;
        }

        let next_n = region.assign_advice(|| "n", col_n, current_row_offset + 1, || next_n)?;
        let next_l = region.assign_advice(|| "l", col_l, current_row_offset + 1, || next_l)?;
        let next_r = region.assign_advice(|| "r", col_r, current_row_offset + 1, || next_r)?;
        let next_n_inv =
            region.assign_advice(|| "n_inv", col_n_inv, current_row_offset + 1, || next_n_inv)?;

        Ok((next_n, next_l, next_r, next_n_inv))
    }

    fn assign_setup(
        &self,
        region: &mut Region<'_, F>,
        n_0: F,
        n_1: F,
        n: F,
    ) -> Result<
        (
            AssignedCell<F, F>,
            AssignedCell<F, F>,
            AssignedCell<F, F>,
            AssignedCell<F, F>,
        ),
        Error,
    > {
        let [col_n, col_l, col_r, col_n_inv] = self.config.advice;

        self.config.selector.enable(region, 0)?;

        let n = region.assign_advice(|| "initial n", col_n, 0, || Value::known(n))?;
        let l = region.assign_advice(|| "initial l0", col_l, 0, || Value::known(n_0))?;
        let r = region.assign_advice(|| "initial l1/r0", col_r, 0, || Value::known(n_1))?;
        let n_inv = region.assign_advice(
            || "n_inv",
            col_n_inv,
            0,
            || n.value().map(|n| n.invert().unwrap_or_else(F::zero)),
        )?;
        Ok((n, l, r, n_inv))
    }

    fn expose_public(
        &self,
        mut layouter: impl Layouter<F>,
        n_cell: Cell,
        l0_cell: Cell,
        l1_cell: Cell,
        l_last_cell: Cell,
    ) -> Result<(), Error> {
        // - `l[0] = instance[0]`
        // - `l[1] = instance[1]`
        // - `l[MAX] = instance[3]` => to minimize rows that are equality enabled
        // - `n[0] = instance[2]`
        layouter.constrain_instance(l0_cell, self.config.instance, 0)?;
        layouter.constrain_instance(l1_cell, self.config.instance, 1)?;
        layouter.constrain_instance(n_cell, self.config.instance, 2)?;
        layouter.constrain_instance(l_last_cell, self.config.instance, 3)?;
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
        let col_n = meta.advice_column();
        let col_l = meta.advice_column();
        let col_r = meta.advice_column();
        let col_n_inv = meta.advice_column();
        let selector = meta.selector();
        let instance = meta.instance_column();

        FibChip::configure(meta, [col_n, col_l, col_r, col_n_inv], selector, instance)
    }

    fn synthesize(
        &self,
        config: Self::Config,
        mut layouter: impl Layouter<F>,
    ) -> Result<(), Error> {
        let chip = FibChip::construct(config);
        let (initial_n_cell, l0_cell, l1_cell, l_last_cell) = layouter.assign_region(
            || "rows",
            |mut region| {
                let (mut n, mut l, mut r, mut n_inv) =
                    chip.assign_setup(&mut region, self.n_0, self.n_1, self.n)?;
                let initial_n_cell = n.cell();
                let l0_cell = l.cell();
                (n, l, r, n_inv) = chip.assign_next_row(
                    &mut region,
                    0,
                    n.value().copied(),
                    l.value().copied(),
                    r.value().copied(),
                    n_inv.value().copied(),
                )?;
                let l1_cell = l.cell();
                for row in 2..FibChip::<F>::MAX_N {
                    (n, l, r, n_inv) = chip.assign_next_row(
                        &mut region,
                        row - 1,
                        n.value().copied(),
                        l.value().copied(),
                        r.value().copied(),
                        n_inv.value().copied(),
                    )?;
                }
                Ok((initial_n_cell, l0_cell, l1_cell, l.cell()))
            },
        )?;

        chip.expose_public(
            layouter.namespace(|| "expose public"),
            initial_n_cell,
            l0_cell,
            l1_cell,
            l_last_cell,
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
        9,
        &circuit,
        vec![vec![Fp::from(0), Fp::from(1), Fp::from(5), Fp::from(8)]],
    )
    .unwrap();
    prover_success.assert_satisfied();

    let prover_failure = MockProver::run(
        9,
        &circuit,
        vec![vec![Fp::from(0), Fp::from(1), Fp::from(5), Fp::from(18)]],
    )
    .unwrap();
    prover_failure.verify().unwrap_err();
}

#[test]
fn plot_fibo1() {
    use plotters::prelude::*;

    let root = BitMapBackend::new("fib-layout.png", (1024, 3096)).into_drawing_area();
    root.fill(&WHITE).unwrap();
    let root = root.titled("Fib Layout", ("sans-serif", 60)).unwrap();

    let circuit = FibCircuit {
        n: Fp::from(10),
        n_0: Fp::from(0),
        n_1: Fp::from(1),
    };
    halo2_proofs::dev::CircuitLayout::default()
        .mark_equality_cells(true)
        .show_equality_constraints(true)
        .render(9, &circuit, &root)
        .unwrap();
}
