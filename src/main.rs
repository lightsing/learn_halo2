use halo2_proofs::circuit::{AssignedCell, Region};
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

/// Layout
/// ```
/// |  n  |     l    |    r   |  s  | first_row | fib | fixed | instance |
/// |:---:|:--------:|:------:|:---:|:---------:|:---:|:-----:|:--------:|
/// |  n  |     1    |    1   |  1  |     1     |  1  |   1   |     n    |
/// | n-1 |     1    |    2   |  1  |     0     |  1  |       |  fib(n)  |
/// | ... |    ...   |   ...  | ... |    ...    | ... |  ...  |    ...   |
/// |  1  | fib(n-1) | fib(n) |  0  |     0     |  1  |       |          |
/// |  0  |  fib(n)  | fib(n) |  0  |     0     |  1  |       |          |
/// | ... |    ...   |   ...  | ... |    ...    | ... |  ...  |    ...   |
/// |  0  |  fib(n)  | fib(n) |  0  |     0     |  1  |       |          |
/// ```
#[derive(Debug, Clone)]
struct FibConfig {
    // constraint the row counts n, l & r calc the fib and a selector
    advice: [Column<Advice>; 4],
    // only for constraint first row values
    fist_row_selector: Selector,
    fib_selector: Selector,
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
        fib_selector: Selector,
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
            let l = meta.query_advice(col_l, Rotation::cur());
            let r = meta.query_advice(col_r, Rotation::cur());
            let s = meta.query_advice(col_s, Rotation::cur());
            let first_row = meta.query_selector(fist_row_selector);
            let fixed = meta.query_fixed(fixed, Rotation::cur());

            vec![
                // initial value from fixed[0]
                first_row.clone() * (fixed.clone() - l) * (fixed.clone() - r) * (fixed - s),
                // initial value from instance[0]
                // first_row * (n - input_n),
            ]
        });

        meta.create_gate("custom selector", |meta| {
            let s = meta.query_advice(col_s, Rotation::cur());
            let s_next = meta.query_advice(col_s, Rotation::next());
            let fib_s = meta.query_selector(fib_selector);

            vec![
                // bool value
                fib_s.clone() * s.clone() * (Expression::Constant(F::one()) - s.clone()),
                // cannot go back to 1 once become 0
                fib_s * s_next * (Expression::Constant(F::one()) - s),
            ]
        });

        meta.create_gate("decreasing counter", |meta| {
            let n = meta.query_advice(col_n, Rotation::cur());
            let n_next = meta.query_advice(col_n, Rotation::next());
            let s = meta.query_advice(col_s, Rotation::cur());
            let fib_s = meta.query_selector(fib_selector);

            vec![
                // n_next = n - 1
                fib_s.clone()
                    * s.clone()
                    * (n.clone() - n_next.clone() - Expression::Constant(F::one())),
                // n_next = 0
                fib_s * (Expression::Constant(F::one()) - s) * n_next,
            ]
        });

        meta.create_gate("fib", |meta| {
            let l = meta.query_advice(col_l, Rotation::cur());
            let r = meta.query_advice(col_r, Rotation::cur());
            let r_next = meta.query_advice(col_r, Rotation::next());
            let s = meta.query_advice(col_s, Rotation::cur());
            let fib_s = meta.query_selector(fib_selector);

            // fib_s = 1 and s = r' = l+r
            vec![
                // fib constraint r_{n+1} = l_n + r_n
                fib_s.clone() * s.clone() * (l + r.clone() - r_next.clone()),
                // result copying r_n = r_{n-1}
                fib_s * (Expression::Constant(F::one()) - s) * (r_next - r),
            ]
        });

        FibConfig {
            advice: [col_n, col_l, col_r, col_s],
            fist_row_selector,
            fib_selector,
            fixed,
            instance,
        }
    }

    fn assign_first_row(
        &self,
        mut region: &mut Region<'_, F>,
        offset: usize,
    ) -> Result<(AssignedCell<F, F>, AssignedCell<F, F>, AssignedCell<F, F>), Error> {
        let [col_n, col_l, col_r, col_s] = self.config.advice;

        self.config.fist_row_selector.enable(&mut region, offset)?;
        self.config.fib_selector.enable(&mut region, offset)?;

        let n_cell = region.assign_advice_from_instance(
            || "initial n",
            self.config.instance,
            0,
            col_n,
            offset,
        )?;

        region.assign_fixed(
            || "initial status",
            self.config.fixed,
            offset,
            || Value::known(F::one()),
        )?;
        let l_cell = region.assign_advice_from_constant(|| "initial l", col_l, offset, F::one())?;
        let r_cell = region.assign_advice_from_constant(|| "initial r", col_r, offset, F::one())?;
        region.assign_advice_from_constant(|| "s", col_s, offset, F::one())?;
        Ok((n_cell, l_cell, r_cell))
    }

    fn assign_computational_row(
        &self,
        mut region: &mut Region<'_, F>,
        offset: usize,
        is_last: bool,
        last_n: AssignedCell<F, F>,
        last_l: AssignedCell<F, F>,
        last_r: AssignedCell<F, F>,
    ) -> Result<(AssignedCell<F, F>, AssignedCell<F, F>, AssignedCell<F, F>), Error> {
        let [col_n, _, col_r, col_s] = self.config.advice;
        self.config.fib_selector.enable(&mut region, offset)?;

        let n_cell = region.assign_advice(
            || "n",
            col_n,
            offset,
            || last_n.value().map(|v| *v - F::one()),
        )?;
        let l_cell = last_r.copy_advice(|| "l", &mut region, self.config.advice[1], offset)?;
        let r_cell = region.assign_advice(
            || "r",
            col_r,
            offset,
            || last_l.value().and_then(|l| last_r.value().map(|r| *l + *r)),
        )?;
        if is_last {
            region.assign_advice(|| "s", col_s, offset, || Value::known(F::zero()))?;
        } else {
            region.assign_advice(|| "s", col_s, offset, || Value::known(F::one()))?;
        }
        Ok((n_cell, l_cell, r_cell))
    }

    fn assign_padding_row(
        &self,
        mut region: &mut Region<'_, F>,
        offset: usize,
        is_last: bool,
        result: AssignedCell<F, F>,
    ) -> Result<AssignedCell<F, F>, Error> {
        let [col_n, col_l, col_r, col_s] = self.config.advice;
        self.config.fib_selector.enable(&mut region, offset)?;
        region.assign_advice(|| "n", col_n, offset, || Value::known(F::zero()))?;
        region.assign_advice(|| "l", col_l, offset, || result.value().copied())?;

        let r_cell = region.assign_advice(|| "r", col_r, offset, || result.value().copied())?;
        region.assign_advice(|| "s", col_s, offset, || Value::known(F::zero()))?;
        if is_last {
            region.assign_advice(|| "n", col_n, offset + 1, || Value::known(F::zero()))?;
            region.assign_advice(|| "r", col_r, offset + 1, || result.value().copied())?;
            region.assign_advice(|| "l", col_l, offset + 1, || result.value().copied())?;
            region.assign_advice(|| "s", col_s, offset + 1, || Value::known(F::zero()))?;
        }
        Ok(r_cell)
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
        let fib_selector = meta.selector();
        let fixed = meta.fixed_column();
        let instance = meta.instance_column();

        FibChip::configure(
            meta,
            [col_n, col_l, col_r, col_s],
            fist_row_selector,
            fib_selector,
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
        let (initial_n, r) = layouter.assign_region(
            || "rows",
            |mut region| {
                let mut offset = 0;
                let (mut n, mut l, mut r) = chip.assign_first_row(&mut region, offset)?;
                let initial_n = n.clone();
                offset += 1;

                for _ in 1..(self.n.get_lower_32() - 1) {
                    (n, l, r) = chip.assign_computational_row(
                        &mut region,
                        offset,
                        false,
                        n.clone(),
                        l.clone(),
                        r.clone(),
                    )?;
                    offset += 1;
                }
                (_, _, r) = chip.assign_computational_row(
                    &mut region,
                    offset,
                    true,
                    n.clone(),
                    l.clone(),
                    r.clone(),
                )?;
                offset += 1;
                for _ in self.n.get_lower_32() as usize..(FibChip::<F>::MAX_N - 1) {
                    r = chip.assign_padding_row(&mut region, offset, false, r)?;
                    offset += 1;
                }
                r = chip.assign_padding_row(&mut region, offset, true, r)?;

                Ok((initial_n, r))
            },
        )?;

        chip.expose_public(layouter.namespace(|| "expose public"), &initial_n, &r)?;
        Ok(())
    }
}

fn main() {
    let circuit = FibCircuit { n: Fp::from(5) };

    let prover_success =
        MockProver::run(9, &circuit, vec![vec![Fp::from(5), Fp::from(8)]]).unwrap();
    prover_success.assert_satisfied();

    let prover_success =
        MockProver::run(9, &circuit, vec![vec![Fp::from(5), Fp::from(18)]]).unwrap();
    prover_success.verify().unwrap_err();
}

#[test]
fn plot_fibo1() {
    use plotters::prelude::*;

    let root = BitMapBackend::new("fib-layout.png", (1024, 3096)).into_drawing_area();
    root.fill(&WHITE).unwrap();
    let root = root.titled("Fib Layout", ("sans-serif", 60)).unwrap();

    let circuit = FibCircuit { n: Fp::from(5) };
    halo2_proofs::dev::CircuitLayout::default()
        .show_equality_constraints(true)
        .render(9, &circuit, &root)
        .unwrap();
}
