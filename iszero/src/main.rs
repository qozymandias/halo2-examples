// is_zero(a : Num) -> Num { if a == 0 return 1 else return 0}
// f { 1 if x=0; 0 otherwise }
//
// eq reasoning:
//  given x we need to allow multiplicitive inverse (division where div by zero equals zero)
//  inv(x)*x = 0 when zero
//  inv(x)*x = 1 otherwise
//  therefore constraint is
//      1 - (x * inv(x)) = 0
//
//  This is because the Field is a Division Ring.
//
//  alternative approach would be to define a mini plonk circuit and configure it for this case.

use std::marker::PhantomData;

use group::ff::Field;
use halo2_proofs::circuit::AssignedCell;
use halo2_proofs::circuit::Chip;
use halo2_proofs::circuit::Layouter;
use halo2_proofs::circuit::Region;
use halo2_proofs::circuit::SimpleFloorPlanner;
use halo2_proofs::circuit::Value;
use halo2_proofs::plonk::Advice;
use halo2_proofs::plonk::Circuit;
use halo2_proofs::plonk::Column;
use halo2_proofs::plonk::ConstraintSystem;
use halo2_proofs::plonk::Error;
use halo2_proofs::plonk::Fixed;
use halo2_proofs::plonk::Instance;
use halo2_proofs::plonk::Selector;
use halo2_proofs::poly::Rotation;
use pretty_assertions::assert_eq;

trait NumericInstructions<F: Field>: Chip<F> {
    type Num;

    fn load_private(&self, layouter: impl Layouter<F>, a: Value<F>) -> Result<Self::Num, Error>;

    fn load_constant(&self, layouter: impl Layouter<F>, constant: F) -> Result<Self::Num, Error>;

    fn load_one(&self, layouter: impl Layouter<F>) -> Result<Self::Num, Error>;

    fn mul(
        &self,
        layouter: impl Layouter<F>,
        a: Self::Num,
        b: Self::Num,
    ) -> Result<Self::Num, Error>;

    fn add(
        &self,
        layouter: impl Layouter<F>,
        a: Self::Num,
        b: Self::Num,
    ) -> Result<Self::Num, Error>;

    fn sub(
        &self,
        layouter: impl Layouter<F>,
        a: Self::Num,
        b: Self::Num,
    ) -> Result<Self::Num, Error>;

    fn mult_inverse(&self, layouter: impl Layouter<F>, a: Self::Num) -> Result<Self::Num, Error>;

    fn expose_public(
        &self,
        layouter: impl Layouter<F>,
        num: Self::Num,
        row: usize,
    ) -> Result<(), Error>;
}

struct FieldChip<F: Field> {
    config: FieldConfig,
    _marker: PhantomData<F>,
}

#[derive(Clone, Debug)]
struct FieldConfig {
    advice: [Column<Advice>; 2],
    one: Column<Fixed>,
    instance: Column<Instance>,
    s_mul: Selector,
    s_add: Selector,
    s_sub: Selector,
    s_mult_inv: Selector,
}

impl<F: Field> FieldChip<F> {
    fn construct(config: <Self as Chip<F>>::Config) -> Self {
        Self {
            config,
            _marker: PhantomData,
        }
    }

    fn configure(
        meta: &mut ConstraintSystem<F>,
        advice: [Column<Advice>; 2],
        instance: Column<Instance>,
        constant: Column<Fixed>,
        one: Column<Fixed>,
    ) -> <Self as Chip<F>>::Config {
        meta.enable_equality(instance);
        meta.enable_constant(constant);
        meta.enable_constant(one);
        for column in &advice {
            meta.enable_equality(*column);
        }
        let s_mul = meta.selector();
        let s_add = meta.selector();
        let s_sub = meta.selector();
        let s_mult_inv = meta.selector();

        meta.create_gate("mul", |meta| {
            let lhs = meta.query_advice(advice[0], Rotation::cur());
            let rhs = meta.query_advice(advice[1], Rotation::cur());
            let out = meta.query_advice(advice[0], Rotation::next());
            let s_mul = meta.query_selector(s_mul);
            vec![s_mul * (lhs * rhs - out)]
        });

        meta.create_gate("add", |meta| {
            let lhs = meta.query_advice(advice[0], Rotation::cur());
            let rhs = meta.query_advice(advice[1], Rotation::cur());
            let out = meta.query_advice(advice[0], Rotation::next());
            let s_add = meta.query_selector(s_add);
            vec![s_add * (lhs + rhs - out)]
        });

        meta.create_gate("sub", |meta| {
            let lhs = meta.query_advice(advice[0], Rotation::cur());
            let rhs = meta.query_advice(advice[1], Rotation::cur());
            let out = meta.query_advice(advice[0], Rotation::next());
            let s_sub = meta.query_selector(s_sub);
            vec![s_sub * ((lhs - rhs) - out)]
        });

        // why don't we need a gate here?
        // meta.create_gate("mult_inverse", |meta| {
        //     let lhs = meta.query_advice(advice[0], Rotation::cur());
        //     // let rhs = meta.query_advice(advice[1], Rotation::cur());
        //     let out = meta.query_advice(advice[0], Rotation::next());
        //     let s_mult_inv = meta.query_selector(s_mult_inv);
        //     vec![s_mult_inv * (lhs - out) ]
        // });

        FieldConfig {
            advice,
            one,
            instance,
            s_mul,
            s_add,
            s_sub,
            s_mult_inv,
        }
    }
}

impl<F: Field> Chip<F> for FieldChip<F> {
    type Config = FieldConfig;
    type Loaded = ();

    fn config(&self) -> &Self::Config {
        &self.config
    }

    fn loaded(&self) -> &Self::Loaded {
        &()
    }
}

#[derive(Clone)]
struct Number<F: Field>(AssignedCell<F, F>);

impl<F: Field> NumericInstructions<F> for FieldChip<F> {
    type Num = Number<F>;

    fn load_private(
        &self,
        mut layouter: impl Layouter<F>,
        value: Value<F>,
    ) -> Result<Self::Num, Error> {
        let config = self.config();

        layouter.assign_region(
            || "load private",
            |mut region| {
                region
                    .assign_advice(|| "private input", config.advice[0], 0, || value)
                    .map(Number)
            },
        )
    }

    fn load_constant(
        &self,
        mut layouter: impl Layouter<F>,
        constant: F,
    ) -> Result<Self::Num, Error> {
        let config = self.config();

        layouter.assign_region(
            || "load constant",
            |mut region| {
                region
                    .assign_advice_from_constant(|| "constant value", config.advice[0], 0, constant)
                    .map(Number)
            },
        )
    }

    fn load_one(&self, mut layouter: impl Layouter<F>) -> Result<Self::Num, Error> {
        let config = self.config();

        layouter.assign_region(
            || "load one",
            |mut region| {
                region
                    .assign_fixed(|| "constant value", config.one, 0, || Value::known(F::ONE))
                    .map(Number)
            },
        )
    }

    fn mul(
        &self,
        mut layouter: impl Layouter<F>,
        a: Self::Num,
        b: Self::Num,
    ) -> Result<Self::Num, Error> {
        let config = self.config();

        layouter.assign_region(
            || "mul",
            |mut region: Region<'_, F>| {
                config.s_mul.enable(&mut region, 0)?;
                a.0.copy_advice(|| "lhs", &mut region, config.advice[0], 0)?;
                b.0.copy_advice(|| "rhs", &mut region, config.advice[1], 0)?;

                let value = a.0.value().copied() * b.0.value();

                region
                    .assign_advice(|| "lhs * rhs", config.advice[0], 1, || value)
                    .map(Number)
            },
        )
    }

    fn add(
        &self,
        mut layouter: impl Layouter<F>,
        a: Self::Num,
        b: Self::Num,
    ) -> Result<Self::Num, Error> {
        let config = self.config();

        layouter.assign_region(
            || "add",
            |mut region: Region<'_, F>| {
                config.s_add.enable(&mut region, 0)?;

                a.0.copy_advice(|| "lhs", &mut region, config.advice[0], 0)?;
                b.0.copy_advice(|| "rhs", &mut region, config.advice[1], 0)?;

                let value = a.0.value().copied() + b.0.value();

                region
                    .assign_advice(|| "lhs + rhs", config.advice[0], 1, || value)
                    .map(Number)
            },
        )
    }

    fn sub(
        &self,
        mut layouter: impl Layouter<F>,
        a: Self::Num,
        b: Self::Num,
    ) -> Result<Self::Num, Error> {
        let config = self.config();

        layouter.assign_region(
            || "sub",
            |mut region: Region<'_, F>| {
                config.s_sub.enable(&mut region, 0)?;

                a.0.copy_advice(|| "lhs", &mut region, config.advice[0], 0)?;
                b.0.copy_advice(|| "rhs", &mut region, config.advice[1], 0)?;

                let value = a.0.value().copied() - b.0.value();

                region
                    .assign_advice(|| "lhs - rhs", config.advice[0], 1, || value)
                    .map(Number)
            },
        )
    }

    fn mult_inverse(
        &self,
        mut layouter: impl Layouter<F>,
        a: Self::Num,
    ) -> Result<Self::Num, Error> {
        let config = self.config();

        layouter.assign_region(
            || "mult_inverse",
            |mut region: Region<'_, F>| {
                config.s_mult_inv.enable(&mut region, 0)?;

                a.0.copy_advice(|| "lhs", &mut region, config.advice[0], 0)?;

                let value =
                    a.0.value()
                        .copied()
                        .map(|value| value.invert().unwrap_or(F::ZERO));
                region
                    .assign_advice(|| "1/lhs", config.advice[0], 1, || value)
                    .map(Number)
            },
        )
    }

    fn expose_public(
        &self,
        mut layouter: impl Layouter<F>,
        num: Self::Num,
        row: usize,
    ) -> Result<(), Error> {
        let config = self.config();

        layouter.constrain_instance(num.0.cell(), config.instance, row)
    }
}

#[derive(Default)]
struct MyCircuit<F: Field> {
    // constant: F,
    a: Value<F>,
    // b: Value<F>,
}

impl<F: Field> Circuit<F> for MyCircuit<F> {
    type Config = FieldConfig;
    type FloorPlanner = SimpleFloorPlanner;

    fn without_witnesses(&self) -> Self {
        Self::default()
    }

    fn configure(meta: &mut ConstraintSystem<F>) -> Self::Config {
        let advice = [meta.advice_column(), meta.advice_column()];
        let instance = meta.instance_column();
        let constant = meta.fixed_column();
        let one = meta.fixed_column();

        FieldChip::configure(meta, advice, instance, constant, one)
    }

    fn synthesize(
        &self,
        config: Self::Config,
        mut layouter: impl Layouter<F>,
    ) -> Result<(), Error> {
        let field_chip = FieldChip::<F>::construct(config);
        let a = field_chip.load_private(layouter.namespace(|| "load a"), self.a)?;

        let mul_inv = field_chip.mult_inverse(layouter.namespace(|| "1/a"), a.clone())?;
        let one = field_chip.load_one(layouter.namespace(|| "load one"))?;

        let mult = field_chip.mul(
            layouter.namespace(|| "a * (-1/a) "),
            a.clone(),
            mul_inv.clone(),
        )?;

        let out = field_chip.sub(layouter.namespace(|| "1 - (a*1/a) "), one, mult)?;

        field_chip.expose_public(layouter.namespace(|| "expose c"), out, 0)
    }
}

fn main() {
    use halo2_proofs::dev::MockProver;
    use halo2_proofs::pasta::Fp;
    let k = 4;

    {
        // test zero
        let a = Fp::from(0);
        let c = Fp::from(1);

        let circuit = MyCircuit { a: Value::known(a) };

        let mut public_inputs = vec![c];

        let prover = MockProver::run(k, &circuit, vec![public_inputs.clone()]).unwrap();
        assert_eq!(prover.verify(), Ok(()));

        public_inputs[0] += Fp::one();
        let prover = MockProver::run(k, &circuit, vec![public_inputs]).unwrap();
        assert!(prover.verify().is_err());
    }

    {
        // test non zero
        let a = Fp::from(10);
        let c = Fp::from(0);

        let circuit = MyCircuit { a: Value::known(a) };

        let mut public_inputs = vec![c];

        let prover = MockProver::run(k, &circuit, vec![public_inputs.clone()]).unwrap();
        assert_eq!(prover.verify(), Ok(()));

        public_inputs[0] += Fp::one();
        let prover = MockProver::run(k, &circuit, vec![public_inputs]).unwrap();
        assert!(prover.verify().is_err());
    }

    println!("Passed assertions!");
}
