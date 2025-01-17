//! A polynomial represented in coefficient form.

use crate::{get_best_evaluation_domain, DenseOrSparsePolynomial, EvaluationDomain, Evaluations};
use crate::{serialize::*, Field, FromBytes, PrimeField, ToBytes};
use rand::Rng;
use rayon::prelude::*;
use std::fmt;
use std::ops::{Add, AddAssign, Deref, DerefMut, Div, Mul, Neg, Sub, SubAssign};

/// Stores a polynomial in coefficient form.
#[derive(Clone, PartialEq, Eq, Hash, Default, CanonicalSerialize, CanonicalDeserialize)]
pub struct DensePolynomial<F: Field> {
    /// The coefficient of `x^i` is stored at location `i` in `self.coeffs`.
    pub coeffs: Vec<F>,
}

impl<F: Field> ToBytes for DensePolynomial<F> {
    fn write<W: Write>(&self, mut w: W) -> std::io::Result<()> {
        (self.coeffs.len() as u64).write(&mut w)?;
        for c in self.coeffs.iter() {
            c.write(&mut w)?;
        }
        Ok(())
    }
}

impl<F: Field> FromBytes for DensePolynomial<F> {
    fn read<Read: std::io::Read>(mut reader: Read) -> std::io::Result<DensePolynomial<F>> {
        let mut coeffs = vec![];
        let coeffs_count = u64::read(&mut reader)
            .map_err(|e| std::io::Error::new(std::io::ErrorKind::InvalidData, e))?;
        for _ in 0..coeffs_count {
            let coeff = F::read(&mut reader)
                .map_err(|e| std::io::Error::new(std::io::ErrorKind::InvalidData, e))?;
            coeffs.push(coeff);
        }
        Ok(DensePolynomial::from_coefficients_vec(coeffs))
    }
}

impl<F: Field> fmt::Debug for DensePolynomial<F> {
    fn fmt(&self, f: &mut fmt::Formatter) -> Result<(), fmt::Error> {
        for (i, coeff) in self.coeffs.iter().enumerate().filter(|(_, c)| !c.is_zero()) {
            if i == 0 {
                write!(f, "\n{:?}", coeff)?;
            } else if i == 1 {
                write!(f, " + \n{:?} * x", coeff)?;
            } else {
                write!(f, " + \n{:?} * x^{}", coeff, i)?;
            }
        }
        Ok(())
    }
}

impl<F: Field> Deref for DensePolynomial<F> {
    type Target = [F];

    fn deref(&self) -> &[F] {
        &self.coeffs
    }
}

impl<F: Field> DerefMut for DensePolynomial<F> {
    fn deref_mut(&mut self) -> &mut [F] {
        &mut self.coeffs
    }
}

impl<F: Field> DensePolynomial<F> {
    /// Returns the zero polynomial.
    pub fn zero() -> Self {
        Self { coeffs: Vec::new() }
    }

    /// Checks if the given polynomial is zero.
    pub fn is_zero(&self) -> bool {
        self.coeffs.len() == 0 || self.coeffs.iter().all(|coeff| coeff.is_zero())
    }

    /// Constructs a new polynomial from a list of coefficients.
    pub fn from_coefficients_slice(coeffs: &[F]) -> Self {
        Self::from_coefficients_vec(coeffs.to_vec())
    }

    /// Constructs a new polynomial from a list of coefficients.
    pub fn from_coefficients_vec(coeffs: Vec<F>) -> Self {
        let mut result = Self { coeffs };
        // While there are zeros at the end of the coefficient vector, pop them off.
        result.truncate_leading_zeros();

        result
    }

    /// Returns the degree of the polynomial.
    pub fn degree(&self) -> usize {
        if self.is_zero() {
            0
        } else {
            debug_assert!(self.coeffs.last().map_or(false, |coeff| !coeff.is_zero()));
            self.coeffs.len() - 1
        }
    }

    /// Evaluates `self` at the given `point` in the field.
    pub fn evaluate(&self, point: F) -> F {
        if self.is_zero() {
            return F::zero();
        }
        let mut powers_of_point = vec![F::one()];
        let mut cur = point;
        for _ in 0..self.degree() {
            powers_of_point.push(cur);
            cur *= &point;
        }
        let zero = F::zero();
        // Same length of powers_of_point and self.coeffs is
        // guaranted by assertion in degree() call
        powers_of_point
            .into_par_iter()
            .zip(&self.coeffs)
            .map(|(power, coeff)| power * coeff)
            .reduce(|| zero, |a, b| a + &b)
    }

    /// Perform a naive n^2 multiplicatoin of `self` by `other`.
    pub fn naive_mul(&self, other: &Self) -> Self {
        if self.is_zero() || other.is_zero() {
            DensePolynomial::zero()
        } else {
            let mut result = vec![F::zero(); self.degree() + other.degree() + 1];
            for (i, self_coeff) in self.coeffs.iter().enumerate() {
                for (j, other_coeff) in other.coeffs.iter().enumerate() {
                    result[i + j] += &(*self_coeff * other_coeff);
                }
            }
            DensePolynomial::from_coefficients_vec(result)
        }
    }

    /// Outputs a polynomial of degree `d` where each coefficient is sampled uniformly at random
    /// from the field `F`.
    pub fn rand<R: Rng>(d: usize, rng: &mut R) -> Self {
        let mut random_coeffs = Vec::new();
        for _ in 0..(d + 1) {
            random_coeffs.push(F::rand(rng));
        }
        Self::from_coefficients_vec(random_coeffs)
    }

    fn truncate_leading_zeros(&mut self) {
        while self.coeffs.last().map_or(false, |c| c.is_zero()) {
            self.coeffs.pop();
        }
    }
}

impl<F: PrimeField> DensePolynomial<F> {
    /// Multiply `self` by the vanishing polynomial for the domain `domain`.
    pub fn mul_by_vanishing_poly(&self, domain_size: usize) -> DensePolynomial<F> {
        let mut shifted = vec![F::zero(); domain_size];
        shifted.extend_from_slice(&self.coeffs);
        shifted
            .par_iter_mut()
            .zip(&self.coeffs)
            .for_each(|(s, c)| *s -= c);
        DensePolynomial::from_coefficients_vec(shifted)
    }

    /// Divide `self` by the vanishing polynomial for the domain `domain`.
    /// Returns the quotient and remainder of the division.
    pub fn divide_by_vanishing_poly(
        &self,
        domain: &Box<dyn EvaluationDomain<F>>,
    ) -> Option<(DensePolynomial<F>, DensePolynomial<F>)> {
        let self_poly: DenseOrSparsePolynomial<F> = self.into();
        let vanishing_poly: DenseOrSparsePolynomial<F> = domain.vanishing_polynomial().into();
        self_poly.divide_with_q_and_r(&vanishing_poly)
    }
}

impl<'a, 'b, F: Field> Add<&'a DensePolynomial<F>> for &'b DensePolynomial<F> {
    type Output = DensePolynomial<F>;

    fn add(self, other: &'a DensePolynomial<F>) -> DensePolynomial<F> {
        let mut result = if self.is_zero() {
            other.clone()
        } else if other.is_zero() {
            self.clone()
        } else {
            if self.degree() >= other.degree() {
                let mut result = self.clone();
                for (a, b) in result.coeffs.iter_mut().zip(&other.coeffs) {
                    *a += b
                }
                result
            } else {
                let mut result = other.clone();
                for (a, b) in result.coeffs.iter_mut().zip(&self.coeffs) {
                    *a += b
                }
                result
            }
        };
        result.truncate_leading_zeros();
        result
    }
}

impl<'a, 'b, F: Field> AddAssign<&'a DensePolynomial<F>> for DensePolynomial<F> {
    fn add_assign(&mut self, other: &'a DensePolynomial<F>) {
        if self.is_zero() {
            self.coeffs.truncate(0);
            self.coeffs.extend_from_slice(&other.coeffs);
        } else if other.is_zero() {
            return;
        } else {
            if self.degree() >= other.degree() {
                for (a, b) in self.coeffs.iter_mut().zip(&other.coeffs) {
                    *a += b
                }
            } else {
                // Add the necessary number of zero coefficients.
                self.coeffs.resize(other.coeffs.len(), F::zero());
                for (a, b) in self.coeffs.iter_mut().zip(&other.coeffs) {
                    *a += b
                }
            }
        }
        self.truncate_leading_zeros();
    }
}

impl<'a, 'b, F: Field> AddAssign<(F, &'a DensePolynomial<F>)> for DensePolynomial<F> {
    fn add_assign(&mut self, (f, other): (F, &'a DensePolynomial<F>)) {
        if self.is_zero() {
            self.coeffs.truncate(0);
            self.coeffs.extend_from_slice(&other.coeffs);
            self.coeffs.iter_mut().for_each(|c| *c *= &f);
        } else if other.is_zero() {
            return;
        } else {
            if self.degree() >= other.degree() {
                for (a, b) in self.coeffs.iter_mut().zip(&other.coeffs) {
                    *a += &(f * b);
                }
            } else {
                // Add the necessary number of zero coefficients.
                self.coeffs.resize(other.coeffs.len(), F::zero());
                for (a, b) in self.coeffs.iter_mut().zip(&other.coeffs) {
                    *a += &(f * b);
                }
            }
        }
        self.truncate_leading_zeros();
    }
}

impl<F: PrimeField> DensePolynomial<F> {
    /// Evaluate `self` over `domain`.
    pub fn evaluate_over_domain_by_ref(
        &self,
        domain: Box<dyn EvaluationDomain<F>>,
    ) -> Evaluations<F> {
        let poly: DenseOrSparsePolynomial<'_, F> = self.into();
        DenseOrSparsePolynomial::<F>::evaluate_over_domain(poly, domain)
    }

    /// Evaluate `self` over `domain`.
    pub fn evaluate_over_domain(self, domain: Box<dyn EvaluationDomain<F>>) -> Evaluations<F> {
        let poly: DenseOrSparsePolynomial<'_, F> = self.into();
        DenseOrSparsePolynomial::<F>::evaluate_over_domain(poly, domain)
    }
}

impl<F: Field> Neg for DensePolynomial<F> {
    type Output = DensePolynomial<F>;

    #[inline]
    fn neg(mut self) -> DensePolynomial<F> {
        for coeff in &mut self.coeffs {
            *coeff = -*coeff;
        }
        self
    }
}

impl<'a, 'b, F: Field> Sub<&'a DensePolynomial<F>> for &'b DensePolynomial<F> {
    type Output = DensePolynomial<F>;

    #[inline]
    fn sub(self, other: &'a DensePolynomial<F>) -> DensePolynomial<F> {
        let mut result = if self.is_zero() {
            let mut result = other.clone();
            for coeff in &mut result.coeffs {
                *coeff = -(*coeff);
            }
            result
        } else if other.is_zero() {
            self.clone()
        } else {
            if self.degree() >= other.degree() {
                let mut result = self.clone();
                for (a, b) in result.coeffs.iter_mut().zip(&other.coeffs) {
                    *a -= b
                }
                result
            } else {
                let mut result = self.clone();
                result.coeffs.resize(other.coeffs.len(), F::zero());
                for (a, b) in result.coeffs.iter_mut().zip(&other.coeffs) {
                    *a -= b;
                }
                result
            }
        };
        result.truncate_leading_zeros();
        result
    }
}

impl<'a, 'b, F: Field> SubAssign<&'a DensePolynomial<F>> for DensePolynomial<F> {
    #[inline]
    fn sub_assign(&mut self, other: &'a DensePolynomial<F>) {
        if self.is_zero() {
            self.coeffs.resize(other.coeffs.len(), F::zero());
            for (i, coeff) in other.coeffs.iter().enumerate() {
                self.coeffs[i] -= coeff;
            }
        } else if other.is_zero() {
            return;
        } else {
            if self.degree() >= other.degree() {
                for (a, b) in self.coeffs.iter_mut().zip(&other.coeffs) {
                    *a -= b
                }
            } else {
                // Add the necessary number of zero coefficients.
                self.coeffs.resize(other.coeffs.len(), F::zero());
                for (a, b) in self.coeffs.iter_mut().zip(&other.coeffs) {
                    *a -= b
                }
            }
        }
        self.truncate_leading_zeros();
    }
}

impl<'a, 'b, F: Field> Div<&'a DensePolynomial<F>> for &'b DensePolynomial<F> {
    type Output = DensePolynomial<F>;

    #[inline]
    fn div(self, divisor: &'a DensePolynomial<F>) -> DensePolynomial<F> {
        let a: DenseOrSparsePolynomial<_> = self.into();
        let b: DenseOrSparsePolynomial<_> = divisor.into();
        a.divide_with_q_and_r(&b).expect("division failed").0
    }
}

/// Performs O(nlogn) multiplication of polynomials if F is smooth.
impl<'a, 'b, F: PrimeField> Mul<&'a DensePolynomial<F>> for &'b DensePolynomial<F> {
    type Output = DensePolynomial<F>;

    #[inline]
    fn mul(self, other: &'a DensePolynomial<F>) -> DensePolynomial<F> {
        if self.is_zero() || other.is_zero() {
            DensePolynomial::zero()
        } else {
            let domain = get_best_evaluation_domain(self.coeffs.len() + other.coeffs.len())
                .expect("Field is not smooth enough to construct domain");
            let mut self_evals = self.evaluate_over_domain_by_ref(domain.clone());
            let other_evals = other.evaluate_over_domain_by_ref(domain);
            self_evals *= &other_evals;
            self_evals.interpolate()
        }
    }
}

#[cfg(all(test, feature = "bls12_381"))]
mod tests {
    use crate::domain::get_best_evaluation_domain;
    use crate::fields::bls12_381::fr::Fr;
    use crate::fields::Field;
    use crate::polynomial::*;
    use crate::UniformRand;
    use rand::thread_rng;

    #[test]
    fn double_polynomials_random() {
        let rng = &mut thread_rng();
        for degree in 0..70 {
            let p = DensePolynomial::<Fr>::rand(degree, rng);
            let p_double = &p + &p;
            let p_quad = &p_double + &p_double;
            assert_eq!(&(&(&p + &p) + &p) + &p, p_quad);
        }
    }

    #[test]
    fn add_polynomials() {
        let rng = &mut thread_rng();
        for a_degree in 0..70 {
            for b_degree in 0..70 {
                let p1 = DensePolynomial::<Fr>::rand(a_degree, rng);
                let p2 = DensePolynomial::<Fr>::rand(b_degree, rng);
                let res1 = &p1 + &p2;
                let res2 = &p2 + &p1;
                assert_eq!(res1, res2);
            }
        }
    }

    #[test]
    fn add_polynomials_with_mul() {
        let rng = &mut thread_rng();
        for a_degree in 0..70 {
            for b_degree in 0..70 {
                let mut p1 = DensePolynomial::rand(a_degree, rng);
                let p2 = DensePolynomial::rand(b_degree, rng);
                let f = Fr::rand(rng);
                let f_p2 = DensePolynomial::from_coefficients_vec(
                    p2.coeffs.iter().map(|c| f * c).collect(),
                );
                let res2 = &f_p2 + &p1;
                p1 += (f, &p2);
                let res1 = p1;
                assert_eq!(res1, res2);
            }
        }
    }

    #[test]
    fn sub_polynomials() {
        let rng = &mut thread_rng();
        let p1 = DensePolynomial::<Fr>::rand(5, rng);
        let p2 = DensePolynomial::<Fr>::rand(3, rng);
        let res1 = &p1 - &p2;
        let res2 = &p2 - &p1;
        assert_eq!(
            &res1 + &p2,
            p1,
            "Subtraction should be inverse of addition!"
        );
        assert_eq!(res1, -res2, "p2 - p1 = -(p1 - p2)");
    }

    #[test]
    fn divide_polynomials_fixed() {
        let dividend = DensePolynomial::from_coefficients_slice(&[
            "4".parse().unwrap(),
            "8".parse().unwrap(),
            "5".parse().unwrap(),
            "1".parse().unwrap(),
        ]);
        let divisor = DensePolynomial::from_coefficients_slice(&[Fr::one(), Fr::one()]); // Construct a monic linear polynomial.
        let result = &dividend / &divisor;
        let expected_result = DensePolynomial::from_coefficients_slice(&[
            "4".parse().unwrap(),
            "4".parse().unwrap(),
            "1".parse().unwrap(),
        ]);
        assert_eq!(expected_result, result);
    }

    #[test]
    fn divide_polynomials_random() {
        let rng = &mut thread_rng();

        for a_degree in 0..70 {
            for b_degree in 0..70 {
                let dividend = DensePolynomial::<Fr>::rand(a_degree, rng);
                let divisor = DensePolynomial::<Fr>::rand(b_degree, rng);
                if let Some((quotient, remainder)) = DenseOrSparsePolynomial::divide_with_q_and_r(
                    &(&dividend).into(),
                    &(&divisor).into(),
                ) {
                    assert_eq!(dividend, &(&divisor * &quotient) + &remainder)
                }
            }
        }
    }

    #[test]
    fn evaluate_polynomials() {
        let rng = &mut thread_rng();
        for a_degree in 0..70 {
            let p = DensePolynomial::rand(a_degree, rng);
            let point: Fr = Fr::from(10u64);
            let mut total = Fr::zero();
            for (i, coeff) in p.coeffs.iter().enumerate() {
                total += &(point.pow(&[i as u64]) * coeff);
            }
            assert_eq!(p.evaluate(point), total);
        }
    }

    #[test]
    fn mul_polynomials_random() {
        let rng = &mut thread_rng();
        for a_degree in 0..70 {
            for b_degree in 0..70 {
                let a = DensePolynomial::<Fr>::rand(a_degree, rng);
                let b = DensePolynomial::<Fr>::rand(b_degree, rng);
                assert_eq!(&a * &b, a.naive_mul(&b))
            }
        }
    }

    #[test]
    fn mul_by_vanishing_poly() {
        let rng = &mut thread_rng();
        for size in 1..18 {
            let domain = get_best_evaluation_domain::<Fr>(1 << size).unwrap();
            for degree in 0..70 {
                let p = DensePolynomial::<Fr>::rand(degree, rng);
                let ans1 = p.mul_by_vanishing_poly(domain.size());
                let ans2 = &p * &domain.vanishing_polynomial().into();
                assert_eq!(ans1, ans2);
            }
        }
    }
}
