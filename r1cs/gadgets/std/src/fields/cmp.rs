use std::cmp::Ordering;
use algebra::PrimeField;
use r1cs_core::{ConstraintSystemAbstract, SynthesisError};
use crate::{boolean::Boolean, bits::ToBitsGadget, eq::EqGadget};
use crate::cmp::ComparisonGadget;
use crate::fields::{fp::FpGadget, FieldGadget};

// implement functions for FpGadget that are useful to implement the ComparisonGadget
impl<F: PrimeField> FpGadget<F> {

    /// Helper function to enforce that `self <= (p-1)/2`.
    pub fn enforce_smaller_or_equal_than_mod_minus_one_div_two<CS: ConstraintSystemAbstract<F>>(
        &self,
        mut cs: CS,
    ) -> Result<(), SynthesisError> {
        // It's okay to use `to_non_unique_bits` bits here because we're enforcing
        // self <= (p-1)/2, which implies self < p.
        let bits_be = self.to_bits(cs.ns(|| "to bits"))?;
        let bits_le = bits_be.into_iter().rev().collect::<Vec<_>>();
        let _ = Boolean::enforce_smaller_or_equal_than_le(
            cs.ns(|| "enforce smaller or equal"),
            &bits_le,
            &F::modulus_minus_one_div_two(),
        )?;
        Ok(())
    }

    /// Helper function to check `self < other` and output a result bit. This
    /// function assumes `self` and `other` are `<= (p-1)/2` and does not
    /// generate constraints to verify that.
    // Note that `len((p-1)/2) = len(p) - 1 = CAPACITY`.
    pub fn is_smaller_than_unchecked<CS: ConstraintSystemAbstract<F>>(&self, mut cs: CS, other: &Self) -> Result<Boolean, SynthesisError> {
        // Since `a = self` and `b = other` are from `[0, (p-1)/2]`, we know that
        // ``
        //      self - other
        // ``
        // is from the range `[-(p-1)/2, (p-1)/2]`, where this range has no overlap
        // due to modular reduction.  Hence
        //
        // ``
        //      0 <= 2 * (self - other) <= (p-1),
        // ``
        // and the least significant bit of `2 * (self - other) mod p` is zero.
        // Otherwise, if `self < other`, then
        // ``
        //      2 * (self - other) mod p =  2 * (self - other) + p
        // ``
        // which is a positive odd number, having least significant bit equal to `1`.
        // To assure the right decision we need to return the least significant
        // bit of the NATIVE bit representation of `2 * (self - other)`. Hence we
        // need to use `to_bits_strict()`.
        Ok(self.sub(cs.ns(|| "sub"), other)?
            .double(cs.ns(|| "double"))?
            .to_bits_strict(cs.ns(|| "to bits"))? // returns big endian
            .into_iter().rev().collect::<Vec<_>>()
            .first()
            .unwrap()
            .clone())
    }

    pub fn enforce_smaller_than_unchecked<CS: ConstraintSystemAbstract<F>>(&self, mut cs: CS, other: &Self) -> Result<(), SynthesisError> {
        let is_smaller = self.is_smaller_than_unchecked(cs.ns(|| "is smaller unchecked"), other)?;
        is_smaller.enforce_equal(cs.ns(|| "enforce smaller than"), &Boolean::constant(true))
    }

    /// Variant of `enforce_cmp` that assumes `self` and `other` are `<= (p-1)/2` and
    /// does not generate constraints to verify that.
    fn enforce_cmp_unchecked<CS: ConstraintSystemAbstract<F>>(
        &self,
        mut cs: CS,
        other: &Self,
        ordering: Ordering,
        should_also_check_equality: bool,
    ) -> Result<(), SynthesisError> {
        let is_cmp = self.is_cmp_unchecked(cs.ns(|| "is cmp unchecked"), other, ordering, should_also_check_equality)?;
        is_cmp.enforce_equal(cs.ns(|| "enforce cmp"), &Boolean::constant(true))
    }

    /// Variant of `is_cmp` that assumes `self` and `other` are `<= (p-1)/2` and does not generate
    /// constraints to verify that.
    // It differs from the default implementation of `is_cmp` only by
    // calling `is_smaller_than_unchecked` in place of `is_smaller_than` for efficiency given that
    // there is no need to verify that `self` and `other` are `<= (p-1)/2`
    fn is_cmp_unchecked<CS: ConstraintSystemAbstract<F>>(
        &self,
        mut cs: CS,
        other: &Self,
        ordering: Ordering,
        should_also_check_equality: bool,
    ) -> Result<Boolean, SynthesisError> {
        let (left, right) = match (ordering, should_also_check_equality) {
            (Ordering::Less, false) | (Ordering::Greater, true) => (self, other),
            (Ordering::Greater, false) | (Ordering::Less, true) => (other, self),
            (Ordering::Equal, _) => return self.is_eq(cs, other),
        };

        let is_smaller = left.is_smaller_than_unchecked(cs.ns(|| "is smaller"), right)?;

        if should_also_check_equality {
            return Boolean::xor(cs.ns(|| "negating cmp outcome"), &is_smaller, &Boolean::constant(true))
        }

        Ok(is_smaller)
    }
}

impl<ConstraintF: PrimeField> ComparisonGadget<ConstraintF> for FpGadget<ConstraintF> {
    fn is_smaller_than<CS: ConstraintSystemAbstract<ConstraintF>>(&self, mut cs: CS, other: &Self) -> Result<Boolean, SynthesisError> {
        self.enforce_smaller_or_equal_than_mod_minus_one_div_two(cs.ns(|| "self smaller or equal mod"))?;
        other.enforce_smaller_or_equal_than_mod_minus_one_div_two(cs.ns(|| "other smaller or equal mod"))?;
        self.is_smaller_than_unchecked(cs.ns(|| "is smaller unchecked"), other)
    }

    fn enforce_smaller_than<CS: ConstraintSystemAbstract<ConstraintF>>(&self, mut cs: CS, other: &Self) -> Result<(), SynthesisError> {
        self.enforce_smaller_or_equal_than_mod_minus_one_div_two(cs.ns(|| "self smaller or equal mod"))?;
        other.enforce_smaller_or_equal_than_mod_minus_one_div_two(cs.ns(|| "other smaller or equal mod"))?;
        self.enforce_smaller_than_unchecked(cs.ns(|| "enforce smaller than unchecked"), other)
    }
}

#[cfg(test)]
mod test {
    use std::cmp::Ordering;
    use rand::{Rng, thread_rng};
    use r1cs_core::{ConstraintSystem, ConstraintSystemAbstract, ConstraintSystemDebugger, SynthesisMode};
    use crate::{algebra::{UniformRand, PrimeField,
                          fields::tweedle::Fr, Group,
    }, fields::fp::FpGadget};
    use crate::{alloc::{AllocGadget, ConstantGadget}, cmp::ComparisonGadget};

    macro_rules! test_cmp_function {
        ($cmp_func: tt) => {
            let mut rng = &mut thread_rng();
            fn rand_in_range<R: Rng>(rng: &mut R) -> Fr {
                let pminusonedivtwo: Fr = Fr::modulus_minus_one_div_two().into();
                let mut r;
                loop {
                    r = Fr::rand(rng);
                    if r <= pminusonedivtwo {
                        break;
                    }
                }
                r
            }
            for i in 0..10 {
                let mut cs = ConstraintSystem::<Fr>::new(SynthesisMode::Debug);

                let a = rand_in_range(&mut rng);
                let a_var = FpGadget::<Fr>::alloc(&mut cs.ns(|| "generate_a"), || Ok(a)).unwrap();
                let b = rand_in_range(&mut rng);
                let b_var = FpGadget::<Fr>::alloc(&mut cs.ns(|| "generate_b"), || Ok(b)).unwrap();

                match a.cmp(&b) {
                    Ordering::Less => {
                        a_var.$cmp_func(cs.ns(|| "enforce less"), &b_var, Ordering::Less, false).unwrap();
                        a_var.$cmp_func(cs.ns(|| "enforce less equal"), &b_var, Ordering::Less, true).unwrap();
                    }
                    Ordering::Greater => {
                        a_var.$cmp_func(cs.ns(|| "enforce greater"), &b_var, Ordering::Greater, false).unwrap();
                        a_var.$cmp_func(cs.ns(|| "enforce greater equal"), &b_var, Ordering::Greater, true).unwrap();
                    }
                    _ => {}
                }

                if i == 0 {
                    println!("number of constraints: {}", cs.num_constraints());
                }
                if !cs.is_satisfied(){
                    println!("{:?}", cs.which_is_unsatisfied());
                }
                assert!(cs.is_satisfied());
            }
            println!("Finished with satisfaction tests");

            for _i in 0..10 {
                let mut cs = ConstraintSystem::<Fr>::new(SynthesisMode::Debug);
                let a = rand_in_range(&mut rng);
                let a_var = FpGadget::<Fr>::alloc(&mut cs.ns(|| "generate_a"), || Ok(a)).unwrap();
                let b = rand_in_range(&mut rng);
                let b_var = FpGadget::<Fr>::alloc(&mut cs.ns(|| "generate_b"), || Ok(b)).unwrap();

                match b.cmp(&a) {
                    Ordering::Less => {
                        a_var.$cmp_func(cs.ns(|| "enforce less"), &b_var, Ordering::Less, false).unwrap();
                        a_var.$cmp_func(cs.ns(|| "enforce less equal"),&b_var, Ordering::Less, true).unwrap();
                    }
                    Ordering::Greater => {
                        a_var.$cmp_func(cs.ns(|| "enforce greater"),&b_var, Ordering::Greater, false).unwrap();
                        a_var.$cmp_func(cs.ns(|| "enforce greater equal"),&b_var, Ordering::Greater, true).unwrap();
                    }
                    _ => {}
                }
                assert!(!cs.is_satisfied());
            }

            for _i in 0..10 {
                let mut cs = ConstraintSystem::<Fr>::new(SynthesisMode::Debug);
                let a = rand_in_range(&mut rng);
                let a_var = FpGadget::<Fr>::alloc(&mut cs.ns(|| "generate_a"), || Ok(a)).unwrap();
                a_var.$cmp_func(cs.ns(|| "enforce less"),&a_var, Ordering::Less, false).unwrap();

                assert!(!cs.is_satisfied());
            }

            for _i in 0..10 {
                let mut cs = ConstraintSystem::<Fr>::new(SynthesisMode::Debug);
                let a = rand_in_range(&mut rng);
                let a_var = FpGadget::<Fr>::alloc(&mut cs.ns(|| "generate_a"), || Ok(a)).unwrap();
                a_var.$cmp_func(cs.ns(|| "enforce less"),&a_var, Ordering::Less, true).unwrap();
                if !cs.is_satisfied(){
                    println!("{:?}", cs.which_is_unsatisfied());
                }
                assert!(cs.is_satisfied());
            }

            // test corner case when operands are extreme values of range [0, (p-1)/2] of
            // admissible values
            let mut cs = ConstraintSystem::<Fr>::new(SynthesisMode::Debug);
            let max_val: Fr = Fr::modulus_minus_one_div_two().into();
            let max_var = FpGadget::<Fr>::alloc(&mut cs.ns(|| "generate_max"), || Ok(max_val)).unwrap();
            let zero_var = FpGadget::<Fr>::from_value(cs.ns(|| "alloc zero"), &Fr::zero());
            zero_var.$cmp_func(cs.ns(|| "enforce 0 <= (p-1) div 2"), &max_var, Ordering::Less, true).unwrap();

            assert!(cs.is_satisfied());

            // test when one of the operands is beyond (p-1)/2
            let out_range_var = FpGadget::<Fr>::alloc(&mut cs.ns(|| "generate_out_range"), || Ok(max_val.double())).unwrap();
            zero_var.$cmp_func(cs.ns(|| "enforce 0 <= p-1"), &out_range_var, Ordering::Less, true).unwrap();
            assert!(!cs.is_satisfied());
        }
    }

    #[test]
    fn test_cmp() {
        test_cmp_function!(enforce_cmp);
    }

    #[test]
    fn test_cmp_unchecked() {
        test_cmp_function!(enforce_cmp_unchecked);
    }
}