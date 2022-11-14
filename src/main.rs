use halo2_proofs::circuit::AssignedCell;
use halo2_proofs::dev::MockProver;
use halo2_proofs::halo2curves::secp256k1::Fp;
use halo2_proofs::{
    arithmetic::FieldExt,
    circuit::{Layouter, SimpleFloorPlanner, Value},
    plonk::{
        Advice, Circuit, Column, ConstraintSystem, Error, Expression, Fixed, Instance, Selector,
    },
    poly::Rotation,
};
use std::marker::PhantomData;

#[derive(Debug, Clone)]
struct FibConfig {
    // constraint the row counts n, l & r calc the fib and a selector
    advice: [Column<Advice>; 4],
    // only for constraint first row values
    fist_row_selector: Selector,
    // constraint the start status
    fixed: Column<Fixed>,
    // input n and fib(n)
    instance: Column<Instance>,
}

struct FibChip<F: FieldExt> {
    config: FibConfig,
    _marker: PhantomData<F>,
}

impl<F: FieldExt> FibChip<F> {
    const MAX_N: usize = 300;
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
        [col_n, col_l, col_r, col_s]: [Column<Advice>; 4],
        fist_row_selector: Selector,
        fixed: Column<Fixed>,
        instance: Column<Instance>,
    ) -> FibConfig {
        meta.enable_equality(col_n);
        meta.enable_equality(col_l);
        meta.enable_equality(col_r);
        meta.enable_equality(col_s);
        meta.enable_constant(fixed);
        meta.enable_equality(instance);

        meta.create_gate("start status", |meta| {
            let n = meta.query_advice(col_n, Rotation::cur());
            let l = meta.query_advice(col_l, Rotation::cur());
            let r = meta.query_advice(col_r, Rotation::cur());
            let s = meta.query_advice(col_s, Rotation::cur());
            let first_row = meta.query_selector(fist_row_selector);
            let fixed = meta.query_fixed(fixed, Rotation::cur());
            let input_n = meta.query_instance(instance, Rotation::cur());

            vec![
                // initial value from fixed[0]
                first_row.clone() * (fixed.clone() - l) * (fixed.clone() - r) * (fixed - s),
                // initial value from instance[0]
                first_row * (n - input_n),
            ]
        });

        meta.create_gate("custom selector", |meta| {
            let s = meta.query_advice(col_s, Rotation::cur());
            let s_next = meta.query_advice(col_s, Rotation::next());

            vec![
                // bool value
                s.clone() * (Expression::Constant(F::one()) - s_next.clone()),
                // cannot go back to 1 once become 0
                s_next * (Expression::Constant(F::one()) - s),
            ]
        });

        meta.create_gate("decreasing counter", |meta| {
            let n = meta.query_advice(col_n, Rotation::cur());
            let n_next = meta.query_advice(col_n, Rotation::next());
            let s = meta.query_advice(col_s, Rotation::cur());

            vec![
                // n_next = n - 1
                s.clone() * (n.clone() - n_next.clone() - Expression::Constant(F::one())),
                // n_next = 0
                (Expression::Constant(F::one()) - s) * n_next,
            ]
        });

        meta.create_gate("fib", |meta| {
            let l = meta.query_advice(col_l, Rotation::cur());
            let r = meta.query_advice(col_r, Rotation::cur());
            let s = meta.query_advice(col_s, Rotation::cur());
            let r_next = meta.query_advice(col_r, Rotation::next());

            vec![
                // fib constraint
                s.clone() * (l.clone() + r.clone() - r_next.clone()),
                (Expression::Constant(F::one()) - s) * (r - r_next),
            ]
        });

        FibConfig {
            advice: [col_n, col_l, col_r, col_s],
            fist_row_selector,
            fixed,
            instance,
        }
    }

    fn assign_first_row(
        &self,
        mut layouter: impl Layouter<F>,
    ) -> Result<(AssignedCell<F, F>, AssignedCell<F, F>, AssignedCell<F, F>), Error> {
        let [col_n, col_l, col_r, col_s] = self.config.advice;

        layouter.assign_region(
            || "first row",
            |mut region| {
                self.config.fist_row_selector.enable(&mut region, 0)?;

                let n_cell = region.assign_advice_from_instance(
                    || "initial n",
                    self.config.instance,
                    0,
                    col_n,
                    0,
                )?;

                region.assign_fixed(
                    || "initial status",
                    self.config.fixed,
                    0,
                    || Value::known(F::one()),
                )?;

                let l_cell =
                    region.assign_advice_from_constant(|| "initial l", col_l, 0, F::one())?;
                let r_cell =
                    region.assign_advice_from_constant(|| "initial r", col_r, 0, F::one())?;
                region.assign_advice_from_constant(|| "initial s", col_s, 0, F::one())?;
                Ok((n_cell, l_cell, r_cell))
            },
        )
    }

    fn assign_computational_row(
        &self,
        mut layouter: impl Layouter<F>,
        last_n: AssignedCell<F, F>,
        last_l: AssignedCell<F, F>,
        last_r: AssignedCell<F, F>,
    ) -> Result<(AssignedCell<F, F>, AssignedCell<F, F>, AssignedCell<F, F>), Error> {
        let [col_n, _, col_r, col_s] = self.config.advice;
        layouter.assign_region(
            || "other rows",
            |mut region| {
                let n_cell = region.assign_advice(
                    || "n",
                    col_n,
                    0,
                    || last_n.value().map(|v| *v - F::one()),
                )?;
                let l_cell = last_r.copy_advice(|| "l", &mut region, self.config.advice[1], 0)?;
                let r_cell = region.assign_advice(
                    || "r",
                    col_r,
                    0,
                    || last_l.value().and_then(|l| last_r.value().map(|r| *l + *r)),
                )?;
                region.assign_advice(|| "s", col_s, 0, || Value::known(F::one()))?;
                Ok((n_cell, l_cell, r_cell))
            },
        )
    }

    fn assign_padding_row(
        &self,
        mut layouter: impl Layouter<F>,
        n: &AssignedCell<F, F>,
        result: &AssignedCell<F, F>,
    ) -> Result<(AssignedCell<F, F>, AssignedCell<F, F>), Error> {
        let [col_n, col_l, col_r, col_s] = self.config.advice;
        layouter.assign_region(
            || "padding row",
            |mut region| {
                let n_cell = n.copy_advice(|| "n", &mut region, col_n, 0)?;
                result.copy_advice(|| "l", &mut region, col_l, 0)?;
                let r_cell = result.copy_advice(|| "r", &mut region, col_r, 0)?;
                region.assign_advice(|| "s", col_s, 0, || Value::known(F::zero()))?;
                Ok((n_cell, r_cell))
            },
        )
    }

    fn expose_public(
        &self,
        mut layouter: impl Layouter<F>,
        n_cell: &AssignedCell<F, F>,
        r_cell: &AssignedCell<F, F>,
    ) -> Result<(), Error> {
        layouter.constrain_instance(n_cell.cell(), self.config.instance, 0)?;
        layouter.constrain_instance(r_cell.cell(), self.config.instance, 1)?;
        Ok(())
    }
}

#[derive(Default)]
struct FibCircuit<F> {
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
        let col_s = meta.advice_column();
        let fist_row_selector = meta.selector();
        let fixed = meta.fixed_column();
        let instance = meta.instance_column();

        FibChip::configure(
            meta,
            [col_n, col_l, col_r, col_s],
            fist_row_selector,
            fixed,
            instance,
        )
    }

    fn synthesize(
        &self,
        config: Self::Config,
        mut layouter: impl Layouter<F>,
    ) -> Result<(), Error> {
        let chip = FibChip::construct(config);
        let (mut n, mut l, mut r) = chip.assign_first_row(layouter.namespace(|| "first_row"))?;
        for _ in 0..self.n.get_lower_32() {
            (n, l, r) =
                chip.assign_computational_row(layouter.namespace(|| "computational row"), n, l, r)?;
        }
        for _ in self.n.get_lower_32() as usize..FibChip::<F>::MAX_N {
            (n, r) = chip.assign_padding_row(layouter.namespace(|| "padding row"), &n, &r)?;
        }
        chip.expose_public(layouter.namespace(|| "expose public"), &n, &r)?;
        Ok(())
    }
}

fn main() {
    let circuit = FibCircuit { n: Fp::from(5) };

    MockProver::run(9, &circuit, vec![vec![Fp::from(5), Fp::from(8)]]).unwrap();
    MockProver::run(9, &circuit, vec![vec![Fp::from(5), Fp::from(9)]]).unwrap();
}