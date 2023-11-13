

// use halo2_proofs::poly::Polynomial;
// use halo2_proofs::arithmetic::Field;
// use halo2_proofs::poly::Rotation;
// use halo2_proofs::poly::Coeff;
// use halo2_proofs::poly::EvaluationDomain;
// use halo2_proofs::poly::LagrangeCoeff;
// 
// use std::fmt::Debug;
// use std::marker::PhantomData;
// use std::ops::{Add, Deref, DerefMut, Index, IndexMut, Mul, RangeFrom, RangeFull};

// fn simple_poly_product<F>(a : Polynomial<F,Coeff>, b : Polynomial<F,Coeff>) -> Polynomial<F,Coeff>
// where F : Field

fn simple_poly_product(a : Vec<i64>, b : Vec<i64>) -> Vec<i64>
{

    let mut ret = Vec::with_capacity(a.len() + b.len());

    for _ in 0..a.len()+b.len() {
        ret.push( 0);
    }

    for (i, &a_coeff) in a.iter().enumerate() {
        for (j, &b_coeff) in b.iter().enumerate() {
            ret[i + j] += a_coeff * b_coeff;
        }
    }

    return ret;
}

// fn multiply_polynomials<F>(
//     poly_a: Polynomial<F, LagrangeCoeff>,
//     poly_b: Polynomial<F, LagrangeCoeff>,
// ) -> Polynomial<F, LagrangeCoeff>
// where 
//     F : Field,
// {
//     // Evaluate the polynomials on the same domain
//     let domain = EvaluationDomain::new(poly_a.len() + poly_b.len()).unwrap();
//     let eval_a = poly_a.evaluate_over_domain(&domain);
//     let eval_b = poly_b.evaluate_over_domain(&domain);
// 
//     // Multiply the polynomials pointwise in the evaluation domain
//     let eval_result: Vec<_> = eval_a
//         .into_iter()
//         .zip(eval_b.into_iter())
//         .map(|(a, b)| a * b)
//         .collect();
// 
//     // Interpolate the result to obtain the product polynomial
//     Polynomial::from_coefficients_vec(LagrangeCoeff::interpolate(&domain, &eval_result))
// }
// 
// fn run_poly_mult() {
//     // Example usage
//     let poly_a = Polynomial::from_coefficients_vec(vec![1, 2, 3]);
//     let poly_b = Polynomial::from_coefficients_vec(vec![4, 5]);
// 
//     let product = multiply_polynomials(poly_a, poly_b);
//     println!("Product: {:?}", product.coeffs());
// }







// #[cfg(test)]
// mod tests {
//     use halo2_proofs::arithmetic::Field;
//     use pasta_curves::pallas;
//     use rand_core::OsRng;
// 
//     use halo2_proofs::poly::Rotation;
//     use halo2_proofs::poly::EvaluationDomain;
//     use halo2_proofs::poly::Polynomial;
// 
//     use super::{simple_poly_product};
// 
//     #[test]
//     fn test_multiply() {
//         let k = 11;
//         let domain = EvaluationDomain::<pallas::Base>::new(1, k);
// 
//         // Create a random polynomial.
//         let mut poly1 = domain.empty_lagrange();
//         for coefficient in poly1.iter_mut() {
//             *coefficient = pallas::Base::random(OsRng);
//         }
//         
//         // Create a random polynomial.
//         let mut poly2 = domain.empty_lagrange();
//         for coefficient in poly2.iter_mut() {
//             *coefficient = pallas::Base::random(OsRng);
//         }
// 
//         let output = simple_poly_product(poly1.to_vec(), poly2.to_vec());
// 
//         assert_ne!(output.len(), 0);
// 
//     }
// }
fn main() {
    let out = simple_poly_product(vec![1,2,3,4,5], vec![6,7,8,9, 10]);
    for i in out {
        println!("{}", i);
    }
}
