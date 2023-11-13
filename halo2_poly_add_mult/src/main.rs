// Mulitply two polynomials represented by their coefficients

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
// use pretty_assertions::assert_eq;

trait NumericInstructions<F: Field>: Chip<F> {
    type Num;

    fn load_private(
        &self,
        layouter: impl Layouter<F>,
        a: Value<F>,
        col: usize,
        row: usize,
    ) -> Result<Self::Num, Error>;

    fn load_constant(
        &self,
        layouter: impl Layouter<F>,
        constant: F,
        col: usize,
        row: usize,
    ) -> Result<Self::Num, Error>;

    fn load_zero(&self, layouter: impl Layouter<F>, row: usize) -> Result<Self::Num, Error>;
    fn load_zero_into_advice(
        &self,
        layouter: impl Layouter<F>,
        col: usize,
        row: usize,
    ) -> Result<Self::Num, Error>;
    fn load_one(&self, layouter: impl Layouter<F>, row: usize) -> Result<Self::Num, Error>;

    fn mul(
        &self,
        layouter: impl Layouter<F>,
        a: Self::Num,
        b: Self::Num,
        col: usize,
        row: usize,
    ) -> Result<Self::Num, Error>;

    fn add(
        &self,
        layouter: impl Layouter<F>,
        a: Self::Num,
        b: Self::Num,
        col: usize,
        row: usize,
    ) -> Result<Self::Num, Error>;

    fn sub(
        &self,
        layouter: impl Layouter<F>,
        a: Self::Num,
        b: Self::Num,
        col: usize,
        row: usize,
    ) -> Result<Self::Num, Error>;

    fn mult_inverse(
        &self,
        layouter: impl Layouter<F>,
        a: Self::Num,
        col: usize,
        row: usize,
    ) -> Result<Self::Num, Error>;

    fn expose_public(
        &self,
        layouter: impl Layouter<F>,
        num: Self::Num,
        row: usize,
    ) -> Result<(), Error>;
}

#[derive(Clone)]
struct Number<F: Field>(AssignedCell<F, F>);

impl<F: Field> NumericInstructions<F> for FieldChip<F> {
    type Num = Number<F>;

    fn load_private(
        &self,
        mut layouter: impl Layouter<F>,
        value: Value<F>,
        col: usize,
        row: usize,
    ) -> Result<Self::Num, Error> {
        layouter.assign_region(
            || "load private",
            |mut region| {
                region
                    .assign_advice(|| "private input", self.config().advice[col], row, || value)
                    .map(Number)
            },
        )
    }

    fn load_constant(
        &self,
        mut layouter: impl Layouter<F>,
        constant: F,
        col: usize,
        row: usize,
    ) -> Result<Self::Num, Error> {
        layouter.assign_region(
            || "load constant",
            |mut region| {
                region
                    .assign_advice_from_constant(
                        || "constant value",
                        self.config().advice[col],
                        row,
                        constant,
                    )
                    .map(Number)
            },
        )
    }
    fn load_one(&self, mut layouter: impl Layouter<F>, row: usize) -> Result<Self::Num, Error> {
        layouter.assign_region(
            || "load one",
            |mut region| {
                region
                    .assign_fixed(
                        || "load one",
                        self.config().one,
                        row,
                        || Value::known(F::ONE),
                    )
                    .map(Number)
            },
        )
    }
    fn load_zero(&self, mut layouter: impl Layouter<F>, row: usize) -> Result<Self::Num, Error> {
        layouter.assign_region(
            || "load zero",
            |mut region| {
                region
                    .assign_fixed(
                        || "load zero",
                        self.config().zero,
                        row,
                        || Value::known(F::ZERO),
                    )
                    .map(Number)
            },
        )
    }

    fn load_zero_into_advice(
        &self,
        mut layouter: impl Layouter<F>,
        col: usize,
        row: usize,
    ) -> Result<Self::Num, Error> {
        layouter.assign_region(
            || "load zero into advice",
            |mut region| {
                region
                    .assign_advice(
                        || "private input",
                        self.config().advice[col],
                        row,
                        || Value::known(F::ZERO),
                    )
                    .map(Number)
            },
        )
    }

    fn mul(
        &self,
        mut layouter: impl Layouter<F>,
        a: Self::Num,
        b: Self::Num,
        col: usize,
        row: usize,
    ) -> Result<Self::Num, Error> {
        layouter.assign_region(
            || "mul",
            |mut region: Region<'_, F>| {
                self.config().s_mul.enable(&mut region, 0)?;
                a.0.copy_advice(|| "lhs", &mut region, self.config().advice[col + 0], row)?;
                b.0.copy_advice(|| "rhs", &mut region, self.config().advice[col + 1], row)?;

                let value = a.0.value().copied() * b.0.value();

                region
                    .assign_advice(|| "lhs * rhs", self.config().advice[col + 2], row, || value)
                    .map(Number)
            },
        )
    }

    fn add(
        &self,
        mut layouter: impl Layouter<F>,
        a: Self::Num,
        b: Self::Num,
        col: usize,
        row: usize,
    ) -> Result<Self::Num, Error> {
        layouter.assign_region(
            || "add",
            |mut region: Region<'_, F>| {
                self.config().s_add.enable(&mut region, 0)?;

                a.0.copy_advice(|| "lhs", &mut region, self.config().advice[col + 0], row)?;
                b.0.copy_advice(|| "rhs", &mut region, self.config().advice[col + 1], row)?;

                let value = a.0.value().copied() + b.0.value();

                region
                    .assign_advice(|| "lhs + rhs", self.config().advice[col + 2], row, || value)
                    .map(Number)
            },
        )
    }

    fn sub(
        &self,
        mut layouter: impl Layouter<F>,
        a: Self::Num,
        b: Self::Num,
        col: usize,
        row: usize,
    ) -> Result<Self::Num, Error> {
        layouter.assign_region(
            || "sub",
            |mut region: Region<'_, F>| {
                self.config().s_sub.enable(&mut region, 0)?;

                a.0.copy_advice(|| "lhs", &mut region, self.config().advice[col + 0], row)?;
                b.0.copy_advice(|| "rhs", &mut region, self.config().advice[col + 1], row)?;

                let value = a.0.value().copied() - b.0.value();

                region
                    .assign_advice(|| "lhs - rhs", self.config().advice[col + 2], row, || value)
                    .map(Number)
            },
        )
    }

    fn mult_inverse(
        &self,
        mut layouter: impl Layouter<F>,
        a: Self::Num,
        col: usize,
        row: usize,
    ) -> Result<Self::Num, Error> {
        layouter.assign_region(
            || "mult_inverse",
            |mut region: Region<'_, F>| {
                self.config().s_mult_inv.enable(&mut region, 0)?;

                a.0.copy_advice(|| "lhs", &mut region, self.config().advice[col + 0], row)?;

                let value =
                    a.0.value()
                        .copied()
                        .map(|value| value.invert().unwrap_or(F::ZERO));
                region
                    .assign_advice(|| "1/lhs", self.config().advice[col + 1], row, || value)
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
        layouter.constrain_instance(num.0.cell(), self.config().instance, row)
    }
}

struct FieldChip<F: Field> {
    config: FieldConfig,
    _marker: PhantomData<F>,
}

#[derive(Clone, Debug)]
struct FieldConfig {
    advice: [Column<Advice>; 6],
    one: Column<Fixed>,
    zero: Column<Fixed>,
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
        advice: [Column<Advice>; 6],
        instance: Column<Instance>,
        constant: Column<Fixed>,
        one: Column<Fixed>,
        zero: Column<Fixed>,
        col: usize,
    ) -> <Self as Chip<F>>::Config {
        meta.enable_equality(instance);
        meta.enable_constant(constant);
        meta.enable_constant(one);
        meta.enable_constant(zero);
        for column in &advice {
            meta.enable_equality(*column);
        }
        let s_mul = meta.selector();
        let s_add = meta.selector();
        let s_sub = meta.selector();
        let s_mult_inv = meta.selector();

        meta.create_gate("mul", |meta| {
            let lhs = meta.query_advice(advice[col + 0], Rotation::cur());
            let rhs = meta.query_advice(advice[col + 1], Rotation::cur());
            let out = meta.query_advice(advice[col + 2], Rotation::cur());
            let s_mul = meta.query_selector(s_mul);
            vec![s_mul * (lhs * rhs - out)]
        });

        meta.create_gate("add", |meta| {
            let lhs = meta.query_advice(advice[col + 0], Rotation::cur());
            let rhs = meta.query_advice(advice[col + 1], Rotation::cur());
            let out = meta.query_advice(advice[col + 2], Rotation::cur());
            let s_add = meta.query_selector(s_add);
            vec![s_add * (lhs + rhs - out)]
        });

        meta.create_gate("sub", |meta| {
            let lhs = meta.query_advice(advice[col + 0], Rotation::cur());
            let rhs = meta.query_advice(advice[col + 1], Rotation::cur());
            let out = meta.query_advice(advice[col + 2], Rotation::cur());
            let s_sub = meta.query_selector(s_sub);
            vec![s_sub * ((lhs - rhs) - out)]
        });

        FieldConfig {
            advice,
            one,
            zero,
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

#[derive(Default)]
struct MyCircuit<F: Field> {
    // constant: F,
    a: Vec<Value<F>>,
    b: Vec<Value<F>>,
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
            meta.advice_column(),
            meta.advice_column(),
            meta.advice_column(),
        ];
        let instance = meta.instance_column();
        let constant = meta.fixed_column();
        let one = meta.fixed_column();
        let zero = meta.fixed_column();

        FieldChip::configure(meta, advice, instance, constant, one, zero, 0)
    }

    fn synthesize(
        &self,
        config: Self::Config,
        mut layouter: impl Layouter<F>,
    ) -> Result<(), Error> {
        let field_chip = FieldChip::<F>::construct(config);
        let col_start = 0;

        let a_advice = self
            .a
            .iter()
            .enumerate()
            .map(|(row, &v)| {
                field_chip.load_private(layouter.namespace(|| "load a"), v.clone(), col_start, row)
            })
            .filter_map(Result::ok)
            .collect::<Vec<_>>();
        let b_advice = self
            .b
            .iter()
            .enumerate()
            .map(|(row, &v)| {
                field_chip.load_private(layouter.namespace(|| "load b"), v, col_start + 1, row)
            })
            .filter_map(Result::ok)
            .collect::<Vec<_>>();
        let mut mults = (0..a_advice.len() + b_advice.len())
            .map(|row| {
                field_chip.load_constant(
                    layouter.namespace(|| "load zero into advice"),
                    F::ZERO,
                    col_start,
                    row,
                )
            })
            .filter_map(Result::ok)
            .collect::<Vec<_>>();

        let row_start = 0;
        for (i, av) in a_advice.iter().enumerate() {
            for (j, bv) in b_advice.iter().enumerate() {
                let mul = field_chip.mul(
                    layouter.namespace(|| "a * b "),
                    av.clone(),
                    bv.clone(),
                    col_start,
                    row_start,
                )?;

                let tmp = mults[i + j].clone();

                let add = field_chip.add(
                    layouter.namespace(|| "a + b "),
                    tmp,
                    mul,
                    col_start,
                    row_start,
                )?;

                mults[i + j] = add.clone();
            }
        }

        for (i, o) in mults.iter().enumerate() {
            field_chip.expose_public(layouter.namespace(|| "expose c"), o.clone(), i)?;
        }
        Ok(())
    }
}

fn main() {
    // use plotters::prelude::*;
    // let root = BitMapBackend::new("layout.png", (1024, 768)).into_drawing_area();
    // root.fill(&WHITE).unwrap();
    // let root = root.titled("Poly mult", ("sans-serif", 20)).unwrap();

    use halo2_proofs::dev::MockProver;
    use halo2_proofs::pasta::Fp;
    let k = 10;

    let inputs = vec![
        (
            vec![Value::known(Fp::from(1)), Value::known(Fp::from(2))],
            vec![Value::known(Fp::from(3)), Value::known(Fp::from(4))],
            vec![Fp::from(3), Fp::from(10), Fp::from(8)],
        ),
        (
            vec![Value::known(Fp::from(1)), Value::known(Fp::from(0))],
            vec![Value::known(Fp::from(3)), Value::known(Fp::from(0))],
            vec![Fp::from(3)],
        ),
        (
            vec![
                Value::known(Fp::from(1)),
                Value::known(Fp::from(2)),
                Value::known(Fp::from(3)),
            ],
            vec![
                Value::known(Fp::from(4)),
                Value::known(Fp::from(5)),
                Value::known(Fp::from(0)),
            ],
            vec![Fp::from(4), Fp::from(13), Fp::from(22), Fp::from(15)],
        ),
        (
            vec![
                Value::known(Fp::from(1)),
                Value::known(Fp::from(2)),
                Value::known(Fp::from(3)),
                Value::known(Fp::from(4)),
                Value::known(Fp::from(5)),
            ],
            vec![
                Value::known(Fp::from(6)),
                Value::known(Fp::from(7)),
                Value::known(Fp::from(8)),
                Value::known(Fp::from(9)),
                Value::known(Fp::from(10)),
            ],
            vec![
                Fp::from(6),
                Fp::from(19),
                Fp::from(40),
                Fp::from(70),
                Fp::from(110),
                Fp::from(114),
                Fp::from(106),
                Fp::from(85),
                Fp::from(50),
                Fp::from(0),
            ],
        ),
    ];

    for (a, b, mut public_inputs) in inputs {
        let circuit = MyCircuit { a: a, b: b };

        // halo2_proofs::dev::CircuitLayout::default()
        //     .show_equality_constraints(true)
        //     .render(k, &circuit, &root)
        //     .unwrap();

        let prover = MockProver::run(k, &circuit, vec![public_inputs.clone()]).unwrap();
        prover.assert_satisfied();

        public_inputs[0] += Fp::one();
        let prover = MockProver::run(k, &circuit, vec![public_inputs]).unwrap();
        assert!(prover.verify().is_err());
    }

    println!("Passed assertions!");
}
