//! Contains utilities for performing arithmetic over univariate polynomials in
//! various forms, including computing commitments to them and provably opening
//! the committed polynomials at arbitrary points.

use group::ff::Field;
use std::{
    fmt::Debug,
    // fmt::Display,
    marker::PhantomData,
    // ops::{Add, Mul, Sub},
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

impl<F: Field, B: Debug + Clone> Poly<F, B> {
    pub fn pretty_print(&self) -> String {
        // let out = "todo".to_string();
        format!("{:?}", self.vals)
        // out
    }
}

impl<F: Field> Poly<F, Coeff> {
    pub fn coeff_from_vec(vals_in: Vec<F>) -> Poly<F, Coeff> {
        Poly { vals: vals_in, _repr: PhantomData }
    }
}

impl<F: Field> Poly<F, Evaluation> {
    pub fn eval_from_vec(vals_in: Vec<F>) -> Poly<F, Evaluation> {
        Poly { vals: vals_in, _repr: PhantomData }
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
    use super::Poly;
    use super::Coeff;
    use halo2_proofs::pasta::Fp;
    // use pasta_curves::pallas;

    #[test]
    fn test_new() {
        let inputs = vec![Fp::from(1), Fp::from(2)];

        let p: Poly<Fp, Coeff> = Poly::coeff_from_vec(inputs);

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
