use crate::{
    boolean::Boolean,
    fields::fp::FpGadget,
    prelude::*,
    ToBitsGadget,
};
use algebra::PrimeField;
use r1cs_core::{ConstraintSystemAbstract, SynthesisError};
use core::cmp::Ordering;

impl<F: PrimeField> FpGadget<F> {
    /// This function enforces the ordering between `self` and `other` if `should_enforce == true`,
    /// enforce nothing otherwise. If `self` should also be checked for equality,
    /// e.g. `self <= other` instead of `self < other`, set `should_also_check_quality` to `true`.
    /// This variant verifies `self` and `other` are `<= (p-1)/2`.
    pub fn conditional_enforce_cmp<CS: ConstraintSystemAbstract<F>>(
        &self,
        mut cs: CS,
        other: &FpGadget<F>,
        should_enforce: &Boolean,
        ordering: Ordering,
        should_also_check_equality: bool,
    ) -> Result<(), SynthesisError> {
        let is_cmp = self.is_cmp(cs.ns(|| "cmp outcome"), other, ordering, should_also_check_equality)?;

        is_cmp.conditional_enforce_equal(cs.ns(|| "cond enforce cmp"), &Boolean::constant(true), should_enforce)
    }

    /// This function enforces the ordering between `self` and `other`. The
    /// constraint system will not be satisfied otherwise. If `self` should
    /// also be checked for equality, e.g. `self <= other` instead of `self <
    /// other`, set `should_also_check_quality` to `true`. This variant
    /// verifies `self` and `other` are `<= (p-1)/2`.
    pub fn enforce_cmp<CS: ConstraintSystemAbstract<F>>(
        &self,
        mut cs: CS,
        other: &FpGadget<F>,
        ordering: Ordering,
        should_also_check_equality: bool,
    ) -> Result<(), SynthesisError> {
        self.conditional_enforce_cmp(&mut cs, other, &Boolean::constant(true), ordering, should_also_check_equality)
    }

    /// This function enforces the ordering between `self` and `other` if `should_enforce == true`,
    /// enforce nothing otherwise. If `self` should also be checked for equality,
    /// e.g. `self <= other` instead of `self < other`, set `should_also_check_quality` to `true`.
    /// This variant assumes `self` and `other` are `<= (p-1)/2` and does not generate
    /// constraints to verify that.
    pub fn conditional_enforce_cmp_unchecked<CS: ConstraintSystemAbstract<F>>(
        &self,
        mut cs: CS,
        other: &FpGadget<F>,
        should_enforce: &Boolean,
        ordering: Ordering,
        should_also_check_equality: bool,
    ) -> Result<(), SynthesisError> {
        let is_cmp = self.is_cmp_unchecked(cs.ns(|| "unchecked cmp outcome"), other, ordering, should_also_check_equality)?;

        is_cmp.conditional_enforce_equal(cs.ns(|| "cond enforce cmp"), &Boolean::constant(true), should_enforce)
    }

    /// This function enforces the ordering between `self` and `other`. The
    /// constraint system will not be satisfied otherwise. If `self` should
    /// also be checked for equality, e.g. `self <= other` instead of `self <
    /// other`, set `should_also_check_quality` to `true`. This variant
    /// assumes `self` and `other` are `<= (p-1)/2` and does not generate
    /// constraints to verify that.
    pub fn enforce_cmp_unchecked<CS: ConstraintSystemAbstract<F>>(
        &self,
        mut cs: CS,
        other: &FpGadget<F>,
        ordering: Ordering,
        should_also_check_equality: bool,
    ) -> Result<(), SynthesisError> {
        self.conditional_enforce_cmp_unchecked(&mut cs, other, &Boolean::constant(true), ordering, should_also_check_equality)
    }

    /// This function checks the ordering between `self` and `other`. It outputs
    /// self `Boolean` that contains the result - `1` if true, `0`
    /// otherwise. The constraint system will be satisfied in any case. If
    /// `self` should also be checked for equality, e.g. `self <= other`
    /// instead of `self < other`, set `should_also_check_quality` to
    /// `true`. This variant verifies `self` and `other` are `<= (p-1)/2`.
    pub fn is_cmp<CS: ConstraintSystemAbstract<F>>(
        &self,
        mut cs: CS,
        other: &FpGadget<F>,
        ordering: Ordering,
        should_also_check_equality: bool,
    ) -> Result<Boolean, SynthesisError> {
        self.enforce_smaller_or_equal_than_mod_minus_one_div_two(cs.ns(|| "self smaller or equal mod"))?;
        other.enforce_smaller_or_equal_than_mod_minus_one_div_two(cs.ns(|| "other smaller or equal mod"))?;
        self.is_cmp_unchecked(cs.ns(|| "is cmp unchecked"), other, ordering, should_also_check_equality)
    }

    /// This function checks the ordering between `self` and `other`. It outputs
    /// a `Boolean` that contains the result - `1` if true, `0` otherwise.
    /// The constraint system will be satisfied in any case. If `self`
    /// should also be checked for equality, e.g. `self <= other` instead of
    /// `self < other`, set `should_also_check_quality` to `true`. This
    /// variant assumes `self` and `other` are `<= (p-1)/2` and does not
    /// generate constraints to verify that.
    pub fn is_cmp_unchecked<CS: ConstraintSystemAbstract<F>>(
        &self,
        mut cs: CS,
        other: &FpGadget<F>,
        ordering: Ordering,
        should_also_check_equality: bool,
    ) -> Result<Boolean, SynthesisError> {
        // The ordering with equality is verified by exploiting the following identities:
        // - x <= y iff !(y < x)
        // - x >= y iff !(x < y)
        let (left, right) = match (ordering, should_also_check_equality) {
            (Ordering::Less, false) | (Ordering::Greater, true) => (self, other),
            (Ordering::Greater, false) | (Ordering::Less, true) => (other, self),
            (Ordering::Equal, _) => return self.is_eq(cs.ns(|| "is eq"), other),
        };

        let is_smaller = left.is_smaller_than_unchecked(cs.ns(|| "is smaller"), right)?;

        if should_also_check_equality {
            return Ok(is_smaller.not())
        }

        Ok(is_smaller)

    }

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
    /// function verifies `self` and `other` are `<= (p-1)/2`.
    fn is_smaller_than<CS: ConstraintSystemAbstract<F>>(&self, mut cs: CS, other: &FpGadget<F>) -> Result<Boolean, SynthesisError> {
        self.enforce_smaller_or_equal_than_mod_minus_one_div_two(cs.ns(|| "self smaller or equal mod"))?;
        other.enforce_smaller_or_equal_than_mod_minus_one_div_two(cs.ns(|| "other smaller or equal mod"))?;
        self.is_smaller_than_unchecked(cs.ns(|| "is smaller unchecked"), other)
    }

    /// Helper function to check `self < other` and output a result bit. This
    /// function assumes `self` and `other` are `<= (p-1)/2` and does not
    /// generate constraints to verify that.
    // Note that `len((p-1)/2) = len(p) - 1 = CAPACITY`.
    fn is_smaller_than_unchecked<CS: ConstraintSystemAbstract<F>>(&self, mut cs: CS, other: &FpGadget<F>) -> Result<Boolean, SynthesisError> {
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

    /// Helper function to enforce `self < other`. This function verifies `self`
    /// and `other` are `<= (p-1)/2`.
    fn enforce_smaller_than<CS: ConstraintSystemAbstract<F>>(&self, mut cs: CS, other: &FpGadget<F>) -> Result<(), SynthesisError> {
        self.enforce_smaller_or_equal_than_mod_minus_one_div_two(cs.ns(|| "self smaller or equal mod"))?;
        other.enforce_smaller_or_equal_than_mod_minus_one_div_two(cs.ns(|| "other smaller or equal mod"))?;
        self.enforce_smaller_than_unchecked(cs.ns(|| "enforce smaller unchecked"), other)
    }

    /// Helper function to enforce `self < other`. This function assumes `self`
    /// and `other` are `<= (p-1)/2` and does not generate constraints to
    /// verify that.
    fn enforce_smaller_than_unchecked<CS: ConstraintSystemAbstract<F>>(&self, mut cs: CS, other: &FpGadget<F>) -> Result<(), SynthesisError> {
        let is_smaller_than = self.is_smaller_than_unchecked(cs.ns(|| "is smaller"), other)?;
        let lc_one = CS::one();
        cs.enforce(
            || "Enforce smaller then",
            |lc| lc + is_smaller_than.lc(CS::one(), F::one()),
            |lc| lc + lc_one.clone(),
            |lc| lc + lc_one
        );
        Ok(())
    }
}

#[cfg(all(test, feature = "bls12_377"))]
mod test {
    use std::cmp::Ordering;
    use rand::{Rng, thread_rng};

    use r1cs_core::{ConstraintSystemAbstract, ConstraintSystem, SynthesisMode, ConstraintSystemDebugger};
    use crate::{algebra::{UniformRand, PrimeField,
                          fields::bls12_377::Fr, Field,
    }, fields::{fp::FpGadget, FieldGadget}};
    use crate::{alloc::AllocGadget, boolean::Boolean};

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

    macro_rules! test_cmp_function {
        ($cmp_func: tt, $should_enforce: expr, $should_fail_with_invalid_operands: expr) => {
            let mut rng = &mut thread_rng();
            let should_enforce = Boolean::constant($should_enforce);
            for _i in 0..10 {
                let mut cs = ConstraintSystem::<Fr>::new(SynthesisMode::Debug);

                let a = rand_in_range(&mut rng);
                let a_var = FpGadget::<Fr>::alloc(&mut cs.ns(|| "generate_a"), || Ok(a)).unwrap();
                let b = rand_in_range(&mut rng);
                let b_var = FpGadget::<Fr>::alloc(&mut cs.ns(|| "generate_b"), || Ok(b)).unwrap();

                match a.cmp(&b) {
                    Ordering::Less => {
                        a_var.$cmp_func(cs.ns(|| "enforce less"), &b_var, &should_enforce, Ordering::Less, false).unwrap();
                        a_var.$cmp_func(cs.ns(|| "enforce less equal"), &b_var, &should_enforce, Ordering::Less, true).unwrap();
                    }
                    Ordering::Greater => {
                        a_var.$cmp_func(cs.ns(|| "enforce greater"), &b_var, &should_enforce, Ordering::Greater, false).unwrap();
                        a_var.$cmp_func(cs.ns(|| "enforce greater equal"), &b_var, &should_enforce, Ordering::Greater, true).unwrap();
                    }
                    _ => {}
                }

                if !cs.is_satisfied(){
                    println!("{:?}", cs.which_is_unsatisfied());
                }
                assert!(cs.is_satisfied());
            }

            for _i in 0..10 {
                let mut cs = ConstraintSystem::<Fr>::new(SynthesisMode::Debug);
                let a = rand_in_range(&mut rng);
                let a_var = FpGadget::<Fr>::alloc(&mut cs.ns(|| "generate_a"), || Ok(a)).unwrap();
                let b = rand_in_range(&mut rng);
                let b_var = FpGadget::<Fr>::alloc(&mut cs.ns(|| "generate_b"), || Ok(b)).unwrap();

                match b.cmp(&a) {
                    Ordering::Less => {
                        a_var.$cmp_func(cs.ns(|| "enforce less"), &b_var, &should_enforce, Ordering::Less, false).unwrap();
                        a_var.$cmp_func(cs.ns(|| "enforce less equal"),&b_var, &should_enforce, Ordering::Less, true).unwrap();
                    }
                    Ordering::Greater => {
                        a_var.$cmp_func(cs.ns(|| "enforce greater"),&b_var, &should_enforce, Ordering::Greater, false).unwrap();
                        a_var.$cmp_func(cs.ns(|| "enforce greater equal"),&b_var, &should_enforce, Ordering::Greater, true).unwrap();
                    }
                    _ => {}
                }
                assert!($should_enforce ^ cs.is_satisfied()); // check that constraints are satisfied iff should_enforce == false
            }

            for _i in 0..10 {
                let mut cs = ConstraintSystem::<Fr>::new(SynthesisMode::Debug);
                let a = rand_in_range(&mut rng);
                let a_var = FpGadget::<Fr>::alloc(&mut cs.ns(|| "generate_a"), || Ok(a)).unwrap();
                a_var.$cmp_func(cs.ns(|| "enforce less"),&a_var, &should_enforce, Ordering::Less, false).unwrap();

                assert!($should_enforce ^ cs.is_satisfied());
            }

            for _i in 0..10 {
                let mut cs = ConstraintSystem::<Fr>::new(SynthesisMode::Debug);
                let a = rand_in_range(&mut rng);
                let a_var = FpGadget::<Fr>::alloc(&mut cs.ns(|| "generate_a"), || Ok(a)).unwrap();
                a_var.$cmp_func(cs.ns(|| "enforce less"),&a_var, &should_enforce, Ordering::Less, true).unwrap();
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
            let zero_var = FpGadget::<Fr>::zero(cs.ns(|| "alloc zero")).unwrap();
            zero_var.$cmp_func(cs.ns(|| "enforce 0 <= (p-1) div 2"), &max_var, &should_enforce, Ordering::Less, true).unwrap();

            assert!(cs.is_satisfied());

            // test when one of the operands is beyond (p-1)/2
            let out_range_var = FpGadget::<Fr>::alloc(&mut cs.ns(|| "generate_out_range"), || Ok(max_val.double())).unwrap();
            zero_var.$cmp_func(cs.ns(|| "enforce 0 <= p-1"), &out_range_var, &should_enforce, Ordering::Less, true).unwrap();
            assert!($should_fail_with_invalid_operands ^ cs.is_satisfied());
        }
    }


    #[test]
    fn test_cmp() {
        test_cmp_function!(conditional_enforce_cmp, true, true);
        test_cmp_function!(conditional_enforce_cmp, false, true);
    }

    #[test]
    fn test_cmp_unchecked() {
        test_cmp_function!(conditional_enforce_cmp_unchecked, true, true);
        test_cmp_function!(conditional_enforce_cmp_unchecked, false, false);
    }

    macro_rules! test_smaller_than_func {
        ($is_smaller_func: tt, $enforce_smaller_func: tt) => {
            let mut rng = &mut thread_rng();
            for _ in 0..10 {
                let mut cs = ConstraintSystem::<Fr>::new(SynthesisMode::Debug);

                let a = rand_in_range(&mut rng);
                let a_var = FpGadget::<Fr>::alloc(&mut cs.ns(|| "generate_a"), || Ok(a)).unwrap();
                let b = rand_in_range(&mut rng);
                let b_var = FpGadget::<Fr>::alloc(&mut cs.ns(|| "generate_b"), || Ok(b)).unwrap();

                let is_smaller = a_var.$is_smaller_func(cs.ns(|| "is smaller"), &b_var).unwrap();

                a_var.$enforce_smaller_func(cs.ns(|| "enforce smaller"), &b_var).unwrap();

                match a.cmp(&b) {
                    Ordering::Less => {
                        assert!(is_smaller.get_value().unwrap());
                        assert!(cs.is_satisfied());
                    }
                    Ordering::Greater | Ordering::Equal => {
                        assert!(!is_smaller.get_value().unwrap());
                        assert!(!cs.is_satisfied())
                    }
                }
            }
            for _ in 0..10 {
                let mut cs = ConstraintSystem::<Fr>::new(SynthesisMode::Debug);
                let a = rand_in_range(&mut rng);
                let a_var = FpGadget::<Fr>::alloc(&mut cs.ns(|| "generate_a"), || Ok(a)).unwrap();
                let is_smaller = a_var.$is_smaller_func(cs.ns(|| "is smaller"),&a_var).unwrap();
                // check that a.is_smaller(a) == false
                assert!(!is_smaller.get_value().unwrap());
                a_var.$enforce_smaller_func(cs.ns(|| "enforce is smaller"), &a_var).unwrap();
                assert!(!cs.is_satisfied());
            }

            // test corner case when operands are extreme values of range [0, (p-1)/2] of
            // admissible values
            let mut cs = ConstraintSystem::<Fr>::new(SynthesisMode::Debug);
            let max_val: Fr = Fr::modulus_minus_one_div_two().into();
            let max_var = FpGadget::<Fr>::alloc(&mut cs.ns(|| "generate_max"), || Ok(max_val)).unwrap();
            let zero_var = FpGadget::<Fr>::zero(cs.ns(|| "alloc zero")).unwrap();
            let is_smaller = zero_var.$is_smaller_func(cs.ns(|| "0 is smaller than (p-1) div 2"), &max_var).unwrap();
            assert!(is_smaller.get_value().unwrap());
            zero_var.$enforce_smaller_func(cs.ns(|| "enforce 0 <= (p-1) div 2"), &max_var).unwrap();
            assert!(cs.is_satisfied());

            // test when one of the operands is beyond (p-1)/2
            let out_range_var = FpGadget::<Fr>::alloc(&mut cs.ns(|| "generate_out_range"), || Ok(max_val.double())).unwrap();
            zero_var.$enforce_smaller_func(cs.ns(|| "enforce 0 <= p-1"), &out_range_var).unwrap();
            assert!(!cs.is_satisfied());
        }
    }

    #[test]
    fn test_smaller_than() {
        test_smaller_than_func!(is_smaller_than, enforce_smaller_than);
    }

    #[test]
    fn test_smaller_than_unchecked() {
        test_smaller_than_func!(is_smaller_than_unchecked, enforce_smaller_than_unchecked);
    }


}