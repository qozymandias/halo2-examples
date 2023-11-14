use halo2_proofs::arithmetic::Field;
use halo2_proofs::poly::Basis;
// use halo2_proofs::poly::Coeff;
use halo2_proofs::poly::Polynomial;
use halo2_proofs::poly::EvaluationDomain;
use halo2_proofs::pasta::Fp;


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




fn simple_poly_product<F, B, Pn>(a: &Polynomial<F, B>, b: &Polynomial<F, B>, mk_empty_fn : &Pn) -> Polynomial<F, B>
where
    F: Field,
    B: Basis,
    Pn : Fn() -> Polynomial<F,B>
{
    let mut ret = mk_empty_fn();
    for (i, &a_coeff) in a.iter().enumerate() {
        for (j, &b_coeff) in b.iter().enumerate() {
            ret[i + j] += a_coeff * b_coeff;
        }
    }
    ret
}

fn main() {
    let a_size = 2;
    let b_size = 2;
    
    assert_eq!(a_size, b_size);
    let j = a_size;
    let k = 1;

    // size is 2^k
    let domain = EvaluationDomain::<Fp>::new(j , k);
    let output_domain = EvaluationDomain::<Fp>::new(j , k*2);

    let a = domain.coeff_from_vec(vec![Fp::from(1), Fp::from(2)]);
    let b = domain.coeff_from_vec(vec![Fp::from(3), Fp::from(4)]);
    let expected_c = output_domain.coeff_from_vec( vec![Fp::from(3), Fp::from(10), Fp::from(8), Fp::from(0)]);
    let out = simple_poly_product(&a, &b, &|  | {  output_domain.empty_coeff() });
    for (i, &v) in out.iter().enumerate() {
        assert_eq!(expected_c[i], v);
        println!("{:?}x^{:?}", v, i);
    }
}
