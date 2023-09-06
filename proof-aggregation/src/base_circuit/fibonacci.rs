//! This circuit is to check whether the output(c) is produced from the specific fibo-input(a,b),

use halo2_proofs::{arithmetic::Field, circuit::*, plonk::*, poly::Rotation};
use snark_verifier::system::halo2::Config;
use std::marker::PhantomData;

#[derive(Debug, Clone)]
struct FibonacciConfig {
    pub col_a: Column<Advice>,
    pub col_b: Column<Advice>,
    pub col_c: Column<Advice>,
    pub selector: Selector,
    pub instance: Column<Instance>,
}

impl FibonacciConfig {
    pub fn new<F: Field>(meta: &mut ConstraintSystem<F>) -> Self {
        let col_a = meta.advice_column();
        let col_b = meta.advice_column();
        let col_c = meta.advice_column();
        let selector = meta.selector();
        let instance = meta.instance_column();

        meta.enable_equality(col_a);
        meta.enable_equality(col_b);
        meta.enable_equality(col_c);
        meta.enable_equality(instance);

        meta.create_gate("add", |meta| {
            //
            // col_a | col_b | col_c | selector
            //   a      b        c       s
            //
            let s = meta.query_selector(selector);
            let a = meta.query_advice(col_a, Rotation::cur());
            let b = meta.query_advice(col_b, Rotation::cur());
            let c = meta.query_advice(col_c, Rotation::cur());
            vec![s * (a + b - c)]
        });

        Self {
            col_a,
            col_b,
            col_c,
            selector,
            instance,
        }
    }
}

// This circuit is to check whether the output(c) is produced from the specific fibo-input(a,b),
// The private input: none.
// The public input: a,b,c(output)
#[derive(Default)]
struct FibonacciCircuit<F>(PhantomData<F>);

impl<F: Field> FibonacciCircuit<F> {
    #[allow(clippy::type_complexity)]
    pub fn assign_first_row(
        &self,
        config: &FibonacciConfig,
        mut layouter: impl Layouter<F>,
    ) -> Result<(AssignedCell<F, F>, AssignedCell<F, F>, AssignedCell<F, F>), Error> {
        layouter.assign_region(
            || "first row",
            |mut region| {
                config.selector.enable(&mut region, 0)?;

                let a_cell = region.assign_advice_from_instance(
                    || "f(0)",
                    config.instance,
                    0,
                    config.col_a,
                    0,
                )?;

                let b_cell = region.assign_advice_from_instance(
                    || "f(1)",
                    config.instance,
                    1,
                    config.col_b,
                    0,
                )?;

                let c_cell = region.assign_advice(
                    || "a + b",
                    config.col_c,
                    0,
                    || a_cell.value().copied() + b_cell.value(),
                )?;

                Ok((a_cell, b_cell, c_cell))
            },
        )
    }

    pub fn assign_row(
        &self,
        config: &FibonacciConfig,
        mut layouter: impl Layouter<F>,
        prev_b: &AssignedCell<F, F>,
        prev_c: &AssignedCell<F, F>,
    ) -> Result<AssignedCell<F, F>, Error> {
        layouter.assign_region(
            || "next row",
            |mut region| {
                config.selector.enable(&mut region, 0)?;

                // Copy the value from b & c in previous row to a & b in current row
                prev_b.copy_advice(|| "a", &mut region, config.col_a, 0)?;
                prev_c.copy_advice(|| "b", &mut region, config.col_b, 0)?;

                let c_cell = region.assign_advice(
                    || "c",
                    config.col_c,
                    0,
                    || prev_b.value().copied() + prev_c.value(),
                )?;

                Ok(c_cell)
            },
        )
    }

    pub fn expose_public(
        &self,
        config: &FibonacciConfig,
        mut layouter: impl Layouter<F>,
        cell: &AssignedCell<F, F>,
        row: usize,
    ) -> Result<(), Error> {
        layouter.constrain_instance(cell.cell(), config.instance, row)
    }
}

impl<F: Field> Circuit<F> for FibonacciCircuit<F> {
    type Config = FibonacciConfig;
    type FloorPlanner = SimpleFloorPlanner;
    type Params = ();

    fn without_witnesses(&self) -> Self {
        Self::default()
    }

    fn configure(meta: &mut ConstraintSystem<F>) -> Self::Config {
        Self::Config::new(meta)
    }

    fn synthesize(
        &self,
        config: Self::Config,
        mut layouter: impl Layouter<F>,
    ) -> Result<(), Error> {
        let (_, mut prev_b, mut prev_c) =
            self.assign_first_row(&config, layouter.namespace(|| "first row"))?;

        for _i in 3..10 {
            let c_cell =
                self.assign_row(&config, layouter.namespace(|| "next row"), &prev_b, &prev_c)?;
            prev_b = prev_c;
            prev_c = c_cell;
        }

        // check with the public input.
        self.expose_public(&config, layouter.namespace(|| "out"), &prev_c, 2)?;

        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use halo2_proofs::dev::MockProver;
    use std::marker::PhantomData;

    use super::*;
    use halo2_proofs::halo2curves::pasta::Fp;

    #[test]
    fn test_fibonacci() {
        let k = 4;

        let a = Fp::from(1); // F[0]
        let b = Fp::from(1); // F[1]
        let out = Fp::from(55); // F[9]

        let circuit = FibonacciCircuit(PhantomData);

        let mut public_input = vec![a, b, out];

        let prover = MockProver::run(k, &circuit, vec![public_input.clone()]).unwrap();
        assert_eq!(prover.verify(), Ok(()));

        public_input[2] += Fp::one();
        let prover = MockProver::run(k, &circuit, vec![public_input]).unwrap();
        assert!(prover.verify().is_err());
    }
}
