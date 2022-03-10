use std::cmp::Ordering;
use algebra::PrimeField;
use r1cs_core::{ConstraintSystemAbstract, SynthesisError};
use crate::{boolean::Boolean, bits::{ToBitsGadget, FromBitsGadget}, eq::EqGadget, select::CondSelectGadget};
use crate::cmp::ComparisonGadget;
use crate::fields::{fp::FpGadget, FieldGadget};

// this macro allows to implement the `unchecked` and `restricted` variants of the `enforce_cmp`,
// `conditional_enforce_cmp` and `is_cmp` functions. The macro is useful as the implementations
// are the same except for the call to the correspondent `is_smaller_than_restricted` or
// `is_smaller_than_unchecked` function.
macro_rules! implement_cmp_functions_variants {
        ($variant: tt) => {
            paste::item! {
                pub fn [<enforce_cmp_ $variant>]<CS: ConstraintSystemAbstract<F>>(
                    &self,
                    mut cs: CS,
                    other: &Self,
                    ordering: Ordering,
                    should_also_check_equality: bool,
                ) -> Result<(), SynthesisError> {
                    self.[<conditional_enforce_cmp_ $variant>](&mut cs, other, &Boolean::constant(true), ordering, should_also_check_equality)
                }

                pub fn  [<conditional_enforce_cmp_ $variant>]<CS: ConstraintSystemAbstract<F>>(
                    &self,
                    mut cs: CS,
                    other: &Self,
                    should_enforce: &Boolean,
                    ordering: Ordering,
                    should_also_check_equality: bool,
                ) -> Result<(), SynthesisError> {
                    let is_cmp = self.[<is_cmp_ $variant>](cs.ns(|| "is cmp"), other, ordering, should_also_check_equality)?;
                    is_cmp.conditional_enforce_equal(cs.ns(|| "conditional enforce cmp"), &Boolean::constant(true), should_enforce)
                }

                pub fn [<is_cmp_ $variant>]<CS: ConstraintSystemAbstract<F>>(
                    &self,
                    mut cs: CS,
                    other: &Self,
                    ordering: Ordering,
                    should_also_check_equality: bool,
                ) -> Result<Boolean, SynthesisError> {
                    let (left, right) = match (ordering, should_also_check_equality) {
                        (Ordering::Less, false) | (Ordering::Greater, true) => (self, other),
                        (Ordering::Greater, false) | (Ordering::Less, true) => (other, self),
                        (Ordering::Equal, _) => return self.is_eq(cs.ns(|| "is equal is is_cmp"), other),
                    };

                    let is_smaller = left.[<is_smaller_than_ $variant>](cs, right)?;

                    if should_also_check_equality {
                        return Ok(is_smaller.not());
                    }

                    Ok(is_smaller)
                }
            }
        };
    }

// implement functions for FpGadget that are useful to implement the ComparisonGadget
impl<F: PrimeField> FpGadget<F> {

    /// Helper function that allows to compare 2 slices of 2 bits, outputting 2 Booleans:
    /// the former (resp. the latter) one is true iff the big-endian integer represented by the
    /// first slice is smaller (resp. is equal) than the big-endian integer represented by the second slice
    fn compare_msbs<CS:ConstraintSystemAbstract<F>>(mut cs: CS, first: &[Boolean], second: &[Boolean])
        -> Result<(Boolean, Boolean), SynthesisError> {
        assert_eq!(first.len(), 2);
        assert_eq!(second.len(), 2);

        let a = first[0]; // a = msb(first)
        let b = first[1]; // b = lsb(first)
        let c = second[0]; // c = msb(second)
        let d = second[1]; // d = lsb(second)

        // is_less corresponds to the Boolean function: !a*(c+!b*d)+(!b*c*d)
        // which is true iff first < second, where + is Boolean OR and * is Boolean AND. Indeed:
        // | first | second | a | b | c | d | is_less |
        // |   0   |    0   | 0 | 0 | 0 | 0 |    0    |
        // |   0   |    1   | 0 | 0 | 0 | 1 |    1    |
        // |   0   |    2   | 0 | 0 | 1 | 0 |    1    |
        // |   0   |    3   | 0 | 0 | 1 | 1 |    1    |
        // |   1   |    0   | 0 | 1 | 0 | 0 |    0    |
        // |   1   |    1   | 0 | 1 | 0 | 1 |    0    |
        // |   1   |    2   | 0 | 1 | 1 | 0 |    1    |
        // |   1   |    3   | 0 | 1 | 1 | 1 |    1    |
        // |   2   |    0   | 1 | 0 | 0 | 0 |    0    |
        // |   2   |    1   | 1 | 0 | 0 | 1 |    0    |
        // |   2   |    2   | 1 | 0 | 1 | 0 |    0    |
        // |   2   |    3   | 1 | 0 | 1 | 1 |    1    |
        // |   3   |    0   | 1 | 1 | 0 | 0 |    0    |
        // |   3   |    1   | 1 | 1 | 0 | 1 |    0    |
        // |   3   |    2   | 1 | 1 | 1 | 0 |    0    |
        // |   3   |    3   | 1 | 1 | 1 | 1 |    0    |

        // To reduce the number of constraints, the Boolean function is computed as follows:
        // is_less = !a + !b*d if c=1, !a*!b*d if c=0

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
    /// function requires that `self` and `other` are `<= (p-1)/2` and imposes
    /// constraints to verify that.
    pub fn is_smaller_than_restricted<CS: ConstraintSystemAbstract<F>>(&self, mut cs: CS, other: &Self) -> Result<Boolean, SynthesisError> {
        self.enforce_smaller_or_equal_than_mod_minus_one_div_two(cs.ns(|| "self smaller or equal mod"))?;
        other.enforce_smaller_or_equal_than_mod_minus_one_div_two(cs.ns(|| "other smaller or equal mod"))?;
        self.is_smaller_than_unchecked(cs.ns(|| "is smaller unchecked"), other)
    }


    /// Helper function to enforce that `self < other`. This
    /// function requires that `self` and `other` are `<= (p-1)/2` and imposes
    /// constraints to verify that.
    pub fn enforce_smaller_than_restricted<CS: ConstraintSystemAbstract<F>>(&self, mut cs: CS, other: &Self) -> Result<(), SynthesisError> {
        self.enforce_smaller_or_equal_than_mod_minus_one_div_two(cs.ns(|| "self smaller or equal mod"))?;
        other.enforce_smaller_or_equal_than_mod_minus_one_div_two(cs.ns(|| "other smaller or equal mod"))?;
        self.enforce_smaller_than_unchecked(cs.ns(|| "enforce smaller than unchecked"), other)
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

    // Variants of cmp functions that assume `self` and `other` are `<= (p-1)/2` and
    // do not generate constraints to verify that.
    implement_cmp_functions_variants!(unchecked);
    // Variants of cmp functions that require `self` and `other` are `<= (p-1)/2` and
    // impose constraints to verify that.
    implement_cmp_functions_variants!(restricted);

}

impl<ConstraintF: PrimeField> ComparisonGadget<ConstraintF> for FpGadget<ConstraintF> {
    /// Output a Boolean that is true iff `self` < `other`. Here `self` and `other`
    /// can be arbitrary field elements, they are not constrained to be at most (p-1)/2
    fn is_smaller_than<CS:ConstraintSystemAbstract<ConstraintF>>(
        &self,
        mut cs: CS,
        other: &Self,
    ) -> Result<Boolean, SynthesisError> {
        let self_bits = self.to_bits_strict(cs.ns(|| "first op to bits"))?;
        let other_bits = other.to_bits_strict(cs.ns(|| "second op to bits"))?;
        // extract the least significant MODULUS_BITS-2 bits and convert them to a field element,
        // which is necessarily lower than (p-1)/2
        let fp_for_self_lsbs = FpGadget::<ConstraintF>::from_bits(cs.ns(|| "pack second op MSBs"), &self_bits[2..])?;
        let fp_for_other_lsbs = FpGadget::<ConstraintF>::from_bits(cs.ns(|| "pack second op LSBs"), &other_bits[2..])?;

        // since the field elements are lower than (p-1)/2, we can compare it with the efficient approach
        let is_less_lsbs = fp_for_self_lsbs.is_smaller_than_unchecked(cs.ns(|| "compare LSBs"), &fp_for_other_lsbs)?;


        // obtain two Booleans:
        // - `is_less_msbs` is true iff the integer represented by the 2 MSBs of self is smaller
        // than the integer represented by the 2 MSBs of other
        // - `is_eq_msbs` is true iff the integer represented by the 2 MSBs of self is equal
        // to the integer represented by the 2 MSBs of other
        let (is_less_msbs, is_eq_msbs) = Self::compare_msbs(cs.ns(|| "compare MSBs"), &self_bits[..2], &other_bits[..2])?;

        // `self < other` iff `is_less_msbs OR is_eq_msbs AND is_less_lsbs`
        // Given that `is_less_msbs` and `is_eq_msbs` cannot be true at the same time,
        // the formula is equivalent to the following conditionally select; indeed:
        // - if `is_eq_msbs = true`, then `is_less_msbs = false`, thus `self < other` iff `is_less_lsbs = true`
        // - if `is_eq_msbs = false`, then `self < other` iff `is_less_msbs = true`
        Boolean::conditionally_select(cs, &is_eq_msbs, &is_less_lsbs, &is_less_msbs)
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

    macro_rules! test_cmp_function {
        ($cmp_func: tt, $should_enforce: expr) => {
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
                        assert!($should_enforce ^ cs.is_satisfied()); // check that constraints are satisfied iff should_enforce == false
                        if $should_enforce {
                            assert_eq!(cs.which_is_unsatisfied().unwrap(), "enforce less/conditional enforce cmp/conditional_equals");
                        }
                        // reinitialize cs to check for equality
                        let mut cs = ConstraintSystem::<Fr>::new(SynthesisMode::Debug);
                        let a_var = FpGadget::<Fr>::alloc(&mut cs.ns(|| "generate_a"), || Ok(a)).unwrap();
                        let b_var = FpGadget::<Fr>::alloc(&mut cs.ns(|| "generate_b"), || Ok(b)).unwrap();
                        a_var.$cmp_func(cs.ns(|| "enforce less equal"),&b_var, &should_enforce, Ordering::Less, true).unwrap();
                        assert!($should_enforce ^ cs.is_satisfied()); // check that constraints are satisfied iff should_enforce == false
                        if $should_enforce {
                            assert_eq!(cs.which_is_unsatisfied().unwrap(), "enforce less equal/conditional enforce cmp/conditional_equals");
                        }
                    }
                    Ordering::Greater => {
                        a_var.$cmp_func(cs.ns(|| "enforce greater"),&b_var, &should_enforce, Ordering::Greater, false).unwrap();
                        if $should_enforce {
                            assert_eq!(cs.which_is_unsatisfied().unwrap(), "enforce greater/conditional enforce cmp/conditional_equals");
                        }
                        // reinitialize cs to check for equality
                        let mut cs = ConstraintSystem::<Fr>::new(SynthesisMode::Debug);
                        let a_var = FpGadget::<Fr>::alloc(&mut cs.ns(|| "generate_a"), || Ok(a)).unwrap();
                        let b_var = FpGadget::<Fr>::alloc(&mut cs.ns(|| "generate_b"), || Ok(b)).unwrap();
                        a_var.$cmp_func(cs.ns(|| "enforce greater equal"),&b_var, &should_enforce, Ordering::Greater, true).unwrap();
                        if $should_enforce {
                            assert_eq!(cs.which_is_unsatisfied().unwrap(), "enforce greater equal/conditional enforce cmp/conditional_equals");
                        }

                    }
                    _ => {}
                }
            }

            for _i in 0..10 {
                let mut cs = ConstraintSystem::<Fr>::new(SynthesisMode::Debug);
                let a = rand_in_range(&mut rng);
                let a_var = FpGadget::<Fr>::alloc(&mut cs.ns(|| "generate_a"), || Ok(a)).unwrap();
                a_var.$cmp_func(cs.ns(|| "enforce less"),&a_var, &should_enforce, Ordering::Less, false).unwrap();

                assert!($should_enforce ^ cs.is_satisfied());
                if $should_enforce {
                    assert_eq!(cs.which_is_unsatisfied().unwrap(), "enforce less/conditional enforce cmp/conditional_equals");
                }
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
        }
    }

    fn test_corner_cases_cmp(should_enforce_flag: bool) {
        // test corner case where the operands are extreme values of range [0, p-1] of
        // admissible values
        let should_enforce = Boolean::constant(should_enforce_flag);
        let mut cs = ConstraintSystem::<Fr>::new(SynthesisMode::Debug);
        let max_val: Fr = Fr::modulus_minus_one_div_two().into();
        let max_val = max_val.double();
        let max_var = FpGadget::<Fr>::alloc(&mut cs.ns(|| "generate_max"), || Ok(max_val)).unwrap();
        let zero_var = FpGadget::<Fr>::from_value(cs.ns(|| "alloc zero"), &Fr::zero());
        max_var.conditional_enforce_cmp(cs.ns(|| "enforce p-1 > 0"), &zero_var, &should_enforce, Ordering::Greater, false).unwrap();
        assert!(cs.is_satisfied());
    }

    macro_rules! test_corner_case_restricted_cmp {
        ($conditional_enforce_cmp_func: tt, $should_enforce_flag: expr, $should_fail_with_invalid_operands: expr, $unsatisfied_constraint: expr) => {
            // test corner case when operands are extreme values of range [0, (p-1)/2] of
            // admissible values
            let should_enforce = Boolean::constant($should_enforce_flag);
            let mut cs = ConstraintSystem::<Fr>::new(SynthesisMode::Debug);
            let max_val: Fr = Fr::modulus_minus_one_div_two().into();
            let max_var = FpGadget::<Fr>::alloc(&mut cs.ns(|| "generate_max"), || Ok(max_val)).unwrap();
            let zero_var = FpGadget::<Fr>::zero(cs.ns(|| "alloc zero")).unwrap();
            zero_var.$conditional_enforce_cmp_func(cs.ns(|| "enforce 0 <= (p-1) div 2"), &max_var, &should_enforce, Ordering::Less, true).unwrap();

            assert!(cs.is_satisfied());

            // test when one of the operands is beyond (p-1)/2
            let out_range_var = FpGadget::<Fr>::alloc(&mut cs.ns(|| "generate_out_range"), || Ok(max_val.double())).unwrap();
            zero_var.$conditional_enforce_cmp_func(cs.ns(|| "enforce 0 <= p-1"), &out_range_var, &should_enforce, Ordering::Less, true).unwrap();
            assert!($should_fail_with_invalid_operands ^ cs.is_satisfied());
            if $should_fail_with_invalid_operands {
                assert_eq!(cs.which_is_unsatisfied().unwrap(), $unsatisfied_constraint);
            }
        }
    }

    #[test]
    fn test_cmp() {
        test_cmp_function!(conditional_enforce_cmp, true);
        test_corner_cases_cmp(true);
        test_cmp_function!(conditional_enforce_cmp, false);
        test_corner_cases_cmp(false);
    }

    #[test]
    fn test_cmp_unchecked() {
        test_cmp_function!(conditional_enforce_cmp_unchecked, true);
        test_corner_case_restricted_cmp!(conditional_enforce_cmp_unchecked, true, true, "enforce 0 <= p-1/conditional enforce cmp/conditional_equals");
        test_cmp_function!(conditional_enforce_cmp_unchecked, false);
        test_corner_case_restricted_cmp!(conditional_enforce_cmp_unchecked, false, false, "enforce 0 <= p-1/conditional enforce cmp/conditional_equals");
    }

    #[test]
    fn test_cmp_restricted() {
        test_cmp_function!(conditional_enforce_cmp_restricted, true);
        test_corner_case_restricted_cmp!(conditional_enforce_cmp_restricted, true, true, "enforce 0 <= p-1/is cmp/self smaller or equal mod/enforce smaller or equal/enforce equal/conditional_equals");
        test_cmp_function!(conditional_enforce_cmp_restricted, false);
        test_corner_case_restricted_cmp!(conditional_enforce_cmp_restricted, false, true, "enforce 0 <= p-1/is cmp/self smaller or equal mod/enforce smaller or equal/enforce equal/conditional_equals");
    }

    macro_rules! test_smaller_than_func {
        ($is_smaller_func: tt, $enforce_smaller_func: tt, $rand_func: tt, $unsatisfied_constraint: expr) => {
            let mut rng = &mut thread_rng();
            for _ in 0..10 {
                let mut cs = ConstraintSystem::<Fr>::new(SynthesisMode::Debug);

                let a = $rand_func(&mut rng);
                let a_var = FpGadget::<Fr>::alloc(&mut cs.ns(|| "generate_a"), || Ok(a)).unwrap();
                let b = $rand_func(&mut rng);
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
                        assert!(!cs.is_satisfied());
                        assert_eq!(cs.which_is_unsatisfied().unwrap(), $unsatisfied_constraint);
                    }
                }
            }

            for _ in 0..10 {
                let mut cs = ConstraintSystem::<Fr>::new(SynthesisMode::Debug);
                let a = $rand_func(&mut rng);
                let a_var = FpGadget::<Fr>::alloc(&mut cs.ns(|| "generate_a"), || Ok(a)).unwrap();
                let is_smaller = a_var.$is_smaller_func(cs.ns(|| "is smaller"),&a_var).unwrap();
                // check that a.is_smaller(a) == false
                assert!(!is_smaller.get_value().unwrap());
                a_var.$enforce_smaller_func(cs.ns(|| "enforce smaller"), &a_var).unwrap();
                assert!(!cs.is_satisfied());
                assert_eq!(cs.which_is_unsatisfied().unwrap(), $unsatisfied_constraint);
            }
        }
    }

    fn test_corner_cases_smaller_than() {
        // test corner case where the operands are extreme values of range [0, p-1] of
        // admissible values
        let mut cs = ConstraintSystem::<Fr>::new(SynthesisMode::Debug);
        let max_val: Fr = Fr::modulus_minus_one_div_two().into();
        let max_val = max_val.double();
        let max_var = FpGadget::<Fr>::alloc(&mut cs.ns(|| "generate_max"), || Ok(max_val)).unwrap();
        let zero_var = FpGadget::<Fr>::from_value(cs.ns(|| "alloc zero"), &Fr::zero());
        let is_smaller = zero_var.is_smaller_than(cs.ns(|| "0 is smaller than p-1"), &max_var).unwrap();
        assert!(is_smaller.get_value().unwrap());
        zero_var.enforce_smaller_than(cs.ns(|| "enforce 0 < p-1"), &max_var).unwrap();
        assert!(cs.is_satisfied());
    }

    #[test]
    fn test_smaller_than() {
        // test with random field elements >(p-1)/2
        test_smaller_than_func!(is_smaller_than, enforce_smaller_than, rand_higher, "enforce smaller/enforce is smaller/conditional_equals");
        // test with random field elements <=(p-1)/2
        test_smaller_than_func!(is_smaller_than, enforce_smaller_than, rand_in_range, "enforce smaller/enforce is smaller/conditional_equals");
        // test with arbitrary field elements
        test_smaller_than_func!(is_smaller_than, enforce_smaller_than, field_uniform_rand, "enforce smaller/enforce is smaller/conditional_equals");
        // test corner case
        test_corner_cases_smaller_than();
    }

    macro_rules! test_corner_case_smaller_than_restricted {
        ($is_smaller_func: tt, $enforce_smaller_func: tt, $unsatisfied_constraint: expr) => {
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
            assert_eq!(cs.which_is_unsatisfied().unwrap(), $unsatisfied_constraint);
        }
    }

    #[test]
    fn test_smaller_than_restricted() {
        test_smaller_than_func!(is_smaller_than_restricted, enforce_smaller_than_restricted, rand_in_range, "enforce smaller/enforce smaller than unchecked/enforce smaller than/conditional_equals");
        test_corner_case_smaller_than_restricted!(is_smaller_than_restricted, enforce_smaller_than_restricted, "enforce 0 <= p-1/other smaller or equal mod/enforce smaller or equal/enforce equal/conditional_equals");
    }

    #[test]
    fn test_smaller_than_unchecked() {
        test_smaller_than_func!(is_smaller_than_unchecked, enforce_smaller_than_unchecked, rand_in_range, "enforce smaller/enforce smaller than/conditional_equals");
        test_corner_case_smaller_than_restricted!(is_smaller_than_unchecked, enforce_smaller_than_unchecked, "enforce 0 <= p-1/enforce smaller than/conditional_equals");
    }
}