// Required to prove:
//      is_zero(a : Num) -> Num { if a == 0 return 1 else return 0 }
//
// Reasoning:
//      given x we need to allow multiplicitive inverse (division where div by zero equals zero)
//      let inv_x = multiplicitive inverse of x
//      x * inv_x = 0 when zero
//      x * inv_x = 1 otherwise
//
//      => let iszero(x, inv_x) = 1 - (in * inv)
//
//      so constraint is: f(x, inv_x, out) = 1 - (x * inv_x) - out == 0
//      where out = iszero(x, inv_x)
//
//      must constraint it to equal zero: f(x, inv_x, out) = 0
//
// Problem:
//      (inv_x = 0) always satisfy that constraint
//      => iszero(x, 0) = 1 - (x * 0)
//         a malicious prover might be able to fake inv and set it to zero,
//         which will always evaluates to 1 regardless of x.
//
// Solution:
//      add an extra constaint:
//           x * iszero(x, inv_x) == 1 when in = 0
//                                == 0 when in != 0
//
//      => constraint: f(x, inv_x) = x * (1 - (x * inv_x)) == 0, which holds when x=0
//
//      e.g. f(x, 0)) = x * (1) == 0 only if x=0
//
//      now let out = f(x, inv_x)
//      => now we must constraint the following to always equal zero:
//              f(x, inv_x, out) = x * (1 - (x * inv_x)) - out == 0
//
//      represented as a halo2 gate:
//      meta.create_gate("iszero", |meta| {
//          // ...
//
//          vec![sel * (( x * (1 - x * inv_x) ) - out)]
//      });
//
//      Which must always evaluate to zero for a valid inv_x.
//      We can illustrate this with the following truth table, and we can see it breaks
//      the constraint when we have a malicious inv_x:
//
//      | x | inv_x | 1 - x * inv_x | x * (1 - x * inv_x) | Satisfies constraint |
//      |---|-------|---------------|---------------------|----------------------|
//      | a | 1/a   | 0             | 0                   | yes                  |
//      | a | 0     | 1             | a                   | no                   |
//      | 0 | 0     | 1             | 0                   | yes                  |
//      | 0 | ?     | 1             | 0                   | yes                  |
//
//      The iszero_constraint now becomes a part of the original circuit via adding the result of it
//      to the result of the iszero circuit. Which will be the same as adding zero to the iszero result,
//      when the inv is valid, and thus if the inverse value is invalid it will break the circuit
//      and not match our public_input.

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

    fn iszero_constraint(
        &self,
        layouter: impl Layouter<F>,
        input: Self::Num,
        inv: Self::Num,
        one: Self::Num,
    ) -> Result<Self::Num, Error>;

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
    advice: [Column<Advice>; 3],
    one: Column<Fixed>,
    instance: Column<Instance>,
    s_mul: Selector,
    s_add: Selector,
    s_sub: Selector,
    s_mult_inv: Selector,
    s_iszero_constraint: Selector,
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
        advice: [Column<Advice>; 3],
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
        let s_iszero_constraint = meta.selector();

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

        meta.create_gate("iszero_constraint", |meta| {
            let input = meta.query_advice(advice[0], Rotation::cur());
            let inv = meta.query_advice(advice[1], Rotation::cur());
            let one = meta.query_advice(advice[2], Rotation::cur());
            let out = meta.query_advice(advice[0], Rotation::next());
            let sel = meta.query_selector(s_iszero_constraint);
            vec![sel * (input.clone() * (one - input.clone() * inv) - out)]
        });

        FieldConfig {
            advice,
            one,
            instance,
            s_mul,
            s_add,
            s_sub,
            s_mult_inv,
            s_iszero_constraint,
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
    // let input = meta.query_advice(advice[0], Rotation::cur());
    // let inv = meta.query_advice(advice[1], Rotation::cur());
    // let one = meta.query_advice(advice[2], Rotation::cur());

    fn iszero_constraint(
        &self,
        mut layouter: impl Layouter<F>,
        input: Self::Num,
        inv: Self::Num,
        one: Self::Num,
    ) -> Result<Self::Num, Error> {
        let config = self.config();

        layouter.assign_region(
            || "check_mult_inv",
            |mut region: Region<'_, F>| {
                config.s_iszero_constraint.enable(&mut region, 0)?;

                input
                    .0
                    .copy_advice(|| "input", &mut region, config.advice[0], 0)?;
                inv.0
                    .copy_advice(|| "inv", &mut region, config.advice[1], 0)?;
                one.0
                    .copy_advice(|| "one", &mut region, config.advice[2], 0)?;

                let value = input.0.value().copied()
                    * (one.0.value().copied()
                        - (input.0.value().copied() * inv.0.value().copied()));
                region
                    .assign_advice(
                        || "input * (one - input * inv)",
                        config.advice[0],
                        1,
                        || value,
                    )
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
        let advice = [
            meta.advice_column(),
            meta.advice_column(),
            meta.advice_column(),
        ];
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

        let iszero = field_chip.sub(
            layouter.namespace(|| "1 - (a*1/a) "),
            one.clone(),
            mult.clone(),
        )?;

        let iszero_constraint = field_chip.iszero_constraint(
            layouter.namespace(|| " a ( 1 - (a*a_inv) ) "),
            a.clone(),
            mul_inv.clone(),
            one.clone(),
        )?;

        let out = field_chip.add(
            layouter.namespace(|| " iszero  + iszero_constraint "),
            iszero.clone(),
            iszero_constraint.clone(),
        )?;
        field_chip.expose_public(layouter.namespace(|| "expose c"), out, 0)
    }
}

fn main() {
    use halo2_proofs::dev::MockProver;
    use halo2_proofs::pasta::Fp;
    let k = 5;
    use plotters::prelude::*;
    let root = BitMapBackend::new("layout.png", (1024, 768)).into_drawing_area();
    root.fill(&WHITE).unwrap();
    let root = root
        .titled("Example Circuit Layout", ("sans-serif", 60))
        .unwrap();

    {
        // test zero
        let a = Fp::from(0);
        let c = Fp::from(1);

        let circuit = MyCircuit { a: Value::known(a) };

        let mut public_inputs = vec![c];

        let prover = MockProver::run(k, &circuit, vec![public_inputs.clone()]).unwrap();
        prover.assert_satisfied();

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

        halo2_proofs::dev::CircuitLayout::default()
            .render(k, &circuit, &root)
            .unwrap();

        let prover = MockProver::run(k, &circuit, vec![public_inputs.clone()]).unwrap();
        prover.assert_satisfied();

        public_inputs[0] += Fp::one();
        let prover = MockProver::run(k, &circuit, vec![public_inputs]).unwrap();
        assert!(prover.verify().is_err());
    }

    println!("Passed assertions!");
}
