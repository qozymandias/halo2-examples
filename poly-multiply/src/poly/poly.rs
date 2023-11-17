//! Contains utilities for performing arithmetic over univariate polynomials in
//! various forms, including computing commitments to them and provably opening
//! the committed polynomials at arbitrary points.

use group::ff::Field;
use std::{
    fmt::Debug,
    fmt::Display,
    marker::PhantomData,
    ops::{Add, Index, Mul, Sub},
};

// pub trait Basis: Copy + Debug + Send + Sync {}
#[derive(Clone, Debug)]
pub struct Coeff;
#[derive(Clone, Debug)]
pub struct Evaluation;

#[derive(Debug, Clone)]
pub struct Poly<F: Field, B> {
    vals: Vec<F>,
    _repr: PhantomData<B>,
}

impl<F: Field> Index<usize> for Poly<F, Coeff> {
    type Output = F;
    fn index(&self, i: usize) -> &F {
        &self.vals[i]
    }
}

impl<F: Field> Add for Poly<F, Coeff> {
    type Output = Self;
    fn add(self, p: Poly<F, Coeff>) -> Poly<F, Coeff> {
        assert_eq!(self.vals.len(), p.vals.len());
        let mut out = self.clone();
        for (i, v) in p.vals.iter().enumerate() {
            out.vals[i] += v;
        }
        self
    }
}

impl<F: Field> Mul for Poly<F, Coeff> {
    type Output = Self;
    fn mul(self, p: Poly<F, Coeff>) -> Poly<F, Coeff> {
        assert_eq!(self.vals.len(), p.vals.len());
        self.slow_multiply(p)
    }
}

impl<F: Field> Sub for Poly<F, Coeff> {
    type Output = Self;
    fn sub(self, p: Poly<F, Coeff>) -> Poly<F, Coeff> {
        self + (p.scalar_multiply(-F::ZERO))
    }
}


fn hex_to_decimal(hex_string: String) -> String {
    // Parse hex string into u64
    let hex_value = u64::from_str_radix(&hex_string.trim_start_matches("0x"), 16).unwrap_or(0);

    // Convert u64 to decimal string
    let decimal_string = hex_value.to_string();

    decimal_string
}

impl<F: Field, B: Debug + Clone> Poly<F, B> {
    pub fn pretty_print(&self) {
        println!("");
        print!("P(x) = ");
        for (i, v) in self.vals.iter().enumerate() {
            let mut vv = format!("{:#?}", v);
            vv = hex_to_decimal(vv);
            print!("{}x^{}", vv, i);
            if i != self.vals.len()-1 {
                print!(" + ");
            } else {
                println!("");
            }
        }
        println!("");
    }
}

impl<F: Field> Poly<F, Coeff> {
    pub fn coeff_from_vec(vals_in: Vec<F>) -> Poly<F, Coeff> {
        Poly {
            vals: vals_in,
            _repr: PhantomData,
        }
    }

    pub fn scalar_multiply(&self, p: F) -> Poly<F, Coeff> {
        Self::coeff_from_vec(self.vals.clone().iter().map(|x| x.mul(p)).collect())
    }

    pub fn inplace_scalar_multiply(&mut self, p: F) -> &Poly<F, Coeff> {
        self.vals.iter_mut().for_each(|x| *x = (*x) * p);
        self
    }

    pub fn slow_multiply(&self, p: Poly<F, Coeff>) -> Poly<F, Coeff> {
        let mut vals_out = Poly {
            vals: vec![],
            _repr: PhantomData,
        };
        for _ in 0..self.vals.len() + self.vals.len() {
            vals_out.vals.push(F::ZERO);
        }
        for (i, &x_i) in self.vals.iter().enumerate() {
            for (j, &x_j) in p.vals.iter().enumerate() {
                vals_out.vals[i + j] += x_i * x_j;
            }
        }
        vals_out
    }
}

impl<F: Field> Poly<F, Evaluation> {
    pub fn eval_from_vec(vals_in: Vec<F>) -> Poly<F, Evaluation> {
        Poly {
            vals: vals_in,
            _repr: PhantomData,
        }
    }

    pub fn lagrange_interpolation<IdxFn>(&self, index_fn : IdxFn) -> Poly<F, Coeff>
        where IdxFn : Fn(usize) -> F
    {
        let mut output = Poly::coeff_from_vec(self.vals.iter().map( |_| F::ZERO).collect());
        for (i_idx, &y_i) in self.vals.iter().enumerate() {
            let i = index_fn(i_idx);

            let mut l_i = Poly::coeff_from_vec(vec![F::ONE]);

            for j_idx in 0..self.vals.len()-1 {

                let j = index_fn(j_idx);
                if i != j {
                    // l = (x - j)(i - j) ==> (-j/i - j) * x^0 + (1/(i - j)) * x^1
                    let divisor = (i - j).invert().unwrap();
                    let coeffs = vec![-j * divisor,  divisor];
                    let p = Poly::coeff_from_vec(coeffs);
                    l_i = l_i * p;
                }
            }
            l_i.inplace_scalar_multiply(y_i);
            output = output + l_i;
        }

        return output;
    }
}

// trait PrettyPrint {
//     fn pretty_print(&self) -> String;
// }
//
// impl<F : Field, B : Debug + Clone> PrettyPrint for Poly<F, B>
// {
// }

#[cfg(test)]
mod tests {
    use super::Coeff;
    use super::Poly;
    use halo2_proofs::pasta::Fp;
    // use pasta_curves::pallas;

    #[test]
    fn test_new() {
        let inputs = vec![Fp::from(1), Fp::from(2)];

        let p: Poly<Fp, Coeff> = Poly::coeff_from_vec(inputs);
        p.pretty_print();
        assert_eq!(p.vals.len(), 2);
    }
}

// use std::fmt::Debug;
// use std::marker::PhantomData;
// // use std::ops::{Add, Deref, DerefMut, Index, IndexMut, Mul, RangeFrom, RangeFull, Sub};
//
// /// The basis over which a polynomial is described.
// pub trait Basis: Copy + Debug + Send + Sync {}
//
// /// The polynomial is defined as coefficients
// #[derive(Clone, Copy, Debug)]
// pub struct Coeff;
// impl Basis for Coeff {}
//
//
// /// Represents a univariate polynomial defined over a field and a particular
// /// basis.
// #[derive(Clone, Debug)]
// pub struct Polynomial<F, B> {
//     pub values: Vec<F>,
//     pub _marker: PhantomData<B>,
// }
