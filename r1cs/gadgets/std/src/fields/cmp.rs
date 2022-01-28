use std::cmp::Ordering;
use algebra::PrimeField;
use r1cs_core::{ConstraintSystemAbstract, SynthesisError};
use crate::{boolean::Boolean, bits::{ToBitsGadget, FromBitsGadget}, eq::EqGadget, select::CondSelectGadget};
use crate::cmp::ComparisonGadget;
use crate::fields::{fp::FpGadget, FieldGadget};

// implement functions for FpGadget that are useful to implement the ComparisonGadget
impl<F: PrimeField> FpGadget<F> {

    /// Helper function that allows to compare 2 slices of 2 bits, outputting 2 Booleans:
    /// the former (resp. the latter) one is true iff the big-endian integer represented by the
    /// first slice is smaller (resp. is equal) than the big-endian integer represented by the second slice
    fn compare_msbs<CS:ConstraintSystemAbstract<F>>(mut cs: CS, first: &[Boolean], second: &[Boolean])
        -> Result<(Boolean, Boolean), SynthesisError> {
        assert_eq!(first.len(), 2);
        assert_eq!(second.len(), 2);

        let a = first[0];
        let b = first[1];
        let c = second[0];
        let d = second[1];

        // is_less corresponds to the Boolean function: !a*(c+!b*d)+(!b*c*d),
        // which is true iff first < second, where + is Boolean OR and * is Boolean AND
        let bd = Boolean::and(cs.ns(|| "!bd"), &b.not(), &d)?;
        let first_tmp = Boolean::or(cs.ns(|| "!a + !bd"), &a.not(), &bd)?;
        let second_tmp = Boolean::and(cs.ns(|| "!a!bd"), &a.not(), &bd)?;
        let is_less = Boolean::conditionally_select(cs.ns(|| "is less"), &c, &first_tmp, &second_tmp)?;

        // is_eq corresponds to the Boolean function: !((a xor c) + (b xor d)),
        // which is true iff first == second
        let first_tmp = Boolean::xor(cs.ns(|| "a xor c"), &a, &c)?;
        let second_tmp = Boolean::xor(cs.ns(|| "b xor d"), &b, &d)?;
        let is_eq = Boolean::or(cs.ns(|| "is eq"), &first_tmp, &second_tmp)?.not();

        Ok((is_less, is_eq))
    }

    /// Output a Boolean that is true iff `self` < `other`. Here `self` and `other`
    /// can be arbitrary field elements, they are not constrained to be at most (p-1)/2
    pub fn is_smaller_than_unrestricted<CS:ConstraintSystemAbstract<F>>(
        &self,
        mut cs: CS,
        other: &Self,
    ) -> Result<Boolean, SynthesisError> {
        let self_bits = self.to_bits_strict(cs.ns(|| "first op to bits"))?;
        let other_bits = other.to_bits_strict(cs.ns(|| "second op to bits"))?;
        // extract the least significant MODULUS_BITS-2 bits and convert them to a field element,
        // which is necessarily lower than (p-1)/2
        let fp_for_self_lsbs = FpGadget::<F>::from_bits(cs.ns(|| "pack second op MSBs"), &self_bits[2..])?;
        let fp_for_other_lsbs = FpGadget::<F>::from_bits(cs.ns(|| "pack second op LSBs"), &other_bits[2..])?;

        // since the field elements are lower than (p-1)/2, we can compare it with the efficient approach
        let is_less_lsbs = fp_for_self_lsbs.is_smaller_than_unchecked(cs.ns(|| "compare LSBs"), &fp_for_other_lsbs)?;


        // obtain two Booleans: the former (resp. the latter) one is true iff the integer
        // represented by the 2 MSBs of self is smaller (resp. is equal) than the integer
        // represented by the 2 MSBs of other
        let (is_less_msbs, is_eq_msbs) = Self::compare_msbs(cs.ns(|| "compare MSBs"), &self_bits[..2], &other_bits[..2])?;

        // Equivalent to is_less_msbs OR is_eq_msbs AND is_less_msbs, given that is_less_msbs and
        // is_eq_msbs cannot be true at the same time
        Boolean::conditionally_select(cs, &is_eq_msbs, &is_less_lsbs, &is_less_msbs)
    }

    /// Enforce than `self` < `other`. Here `self` and `other` they are arbitrary field elements,
    /// they are not constrained to be at most (p-1)/2
    pub fn enforce_smaller_than_unrestricted<CS: ConstraintSystemAbstract<F>>(&self, mut cs: CS, other: &Self) -> Result<(), SynthesisError> {
        let is_smaller = self.is_smaller_than_unrestricted(cs.ns(|| "is smaller unchecked"), other)?;
        is_smaller.enforce_equal(cs.ns(|| "enforce smaller than"), &Boolean::constant(true))
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
    pub fn enforce_cmp_unchecked<CS: ConstraintSystemAbstract<F>>(
        &self,
        mut cs: CS,
        other: &Self,
        ordering: Ordering,
        should_also_check_equality: bool,
    ) -> Result<(), SynthesisError> {
        self.conditional_enforce_cmp_unchecked(&mut cs, other, &Boolean::constant(true), ordering, should_also_check_equality)
    }

    /// Variant of `conditional_enforce_cmp` that assumes `self` and `other` are `<= (p-1)/2` and
    /// does not generate constraints to verify that.
    pub fn conditional_enforce_cmp_unchecked<CS: ConstraintSystemAbstract<F>>(
        &self,
        mut cs: CS,
        other: &Self,
        should_enforce: &Boolean,
        ordering: Ordering,
        should_also_check_equality: bool,
    ) -> Result<(), SynthesisError> {
        let is_cmp = self.is_cmp_unchecked(cs.ns(|| "is cmp unchecked"), other, ordering, should_also_check_equality)?;
        is_cmp.conditional_enforce_equal(cs.ns(|| "conditionally enforce cmp"), &Boolean::constant(true), should_enforce)
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
            return Ok(is_smaller.not());
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
    }, fields::{fp::FpGadget, FieldGadget}};
    use crate::{alloc::{AllocGadget, ConstantGadget}, cmp::ComparisonGadget, boolean::Boolean};

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
            println!("Finished with satisfaction tests");

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
                    Ordering::Less  => {
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
            let zero_var = FpGadget::<Fr>::from_value(cs.ns(|| "alloc zero"), &Fr::zero());
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

    macro_rules! test_smaller_than_unrestricted {
        ($rand_func: tt) => {
            let mut rng = &mut thread_rng();

            for _ in 0..10 {
                let mut cs = ConstraintSystem::<Fr>::new(SynthesisMode::Debug);

                let a = $rand_func(&mut rng);
                let a_var = FpGadget::<Fr>::alloc(&mut cs.ns(|| "generate_a"), || Ok(a)).unwrap();
                let b = $rand_func(&mut rng);
                let b_var = FpGadget::<Fr>::alloc(&mut cs.ns(|| "generate_b"), || Ok(b)).unwrap();
                let is_smaller = a_var.is_smaller_than_unrestricted(cs.ns(|| "is smaller"), &b_var).unwrap();
                a_var.enforce_smaller_than_unrestricted(cs.ns(|| "enforce is smaller"), &b_var).unwrap();

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
                let a = $rand_func(&mut rng);
                let a_var = FpGadget::<Fr>::alloc(&mut cs.ns(|| "generate_a"), || Ok(a)).unwrap();
                let is_smaller = a_var.is_smaller_than_unrestricted(cs.ns(|| "is smaller"),&a_var).unwrap();
                // check that a.is_smaller(a) == false
                assert!(!is_smaller.get_value().unwrap());
                a_var.enforce_smaller_than_unrestricted(cs.ns(|| "enforce is smaller"), &a_var).unwrap();
                assert!(!cs.is_satisfied());
            }

            // test corner case where the operands are extreme values of range [0, p-1] of
            // admissible values
            let mut cs = ConstraintSystem::<Fr>::new(SynthesisMode::Debug);
            let max_val: Fr = Fr::modulus_minus_one_div_two().into();
            let max_val = max_val.double();
            let max_var = FpGadget::<Fr>::alloc(&mut cs.ns(|| "generate_max"), || Ok(max_val)).unwrap();
            let zero_var = FpGadget::<Fr>::from_value(cs.ns(|| "alloc zero"), &Fr::zero());
            let is_smaller = zero_var.is_smaller_than_unrestricted(cs.ns(|| "0 is smaller than p-1"), &max_var).unwrap();
            assert!(is_smaller.get_value().unwrap());
            zero_var.enforce_smaller_than_unrestricted(cs.ns(|| "enforce 0 <= (p-1) div 2"), &max_var).unwrap();
            assert!(cs.is_satisfied());
        }
    }

    #[test]
    fn test_smaller_than_unrestricted() {
        fn rand_higher<R: Rng>(rng: &mut R) -> Fr {
            let pminusonedivtwo: Fr = Fr::modulus_minus_one_div_two().into();
            let mut r;
            loop {
                r = Fr::rand(rng);
                if r > pminusonedivtwo {
                    break;
                }
            }
            r
        }

        fn field_uniform_rand<R: Rng>(rng: &mut R) -> Fr {
            Fr::rand(rng)
        }
        // test with random field elements >(p-1)/2
        test_smaller_than_unrestricted!(rand_higher);
        // test with random field elements <=(p-1)/2
        test_smaller_than_unrestricted!(rand_in_range);
        // test with arbitrary field elements
        test_smaller_than_unrestricted!(field_uniform_rand);
    }
}