use crate::prelude::*;
use algebra::{Field, FpParameters, PrimeField};
use r1cs_core::{ConstraintSystemAbstract, LinearCombination, SynthesisError, Variable};
use crate::fields::fp::FpGadget;

/// Specifies how to generate constraints that check for equality for two variables of type `Self`.
pub trait EqGadget<ConstraintF: Field>: Eq {
    /// Output a `Boolean` value representing whether `self.value() == other.value()`.
    fn is_eq<CS: ConstraintSystemAbstract<ConstraintF>>(
        &self,
        cs: CS,
        other: &Self,
    ) -> Result<Boolean, SynthesisError>;

    /// Output a `Boolean` value representing whether `self.value() != other.value()`.
    ///
    /// By default, this is defined as `self.is_eq(other)?.not()`.
    fn is_neq<CS: ConstraintSystemAbstract<ConstraintF>>(
        &self,
        cs: CS,
        other: &Self,
    ) -> Result<Boolean, SynthesisError> {
        Ok(self.is_eq(cs, other)?.not())
    }

    /// If `should_enforce == true`, enforce that `self` and `other` are equal; else,
    /// enforce a vacuously true statement.
    ///
    /// A safe default implementation is provided that generates the following constraints:
    /// `self.is_eq(other)?.conditional_enforce_equal(&Boolean::TRUE, should_enforce)`.
    ///
    /// More efficient specialized implementation may be possible; implementors
    /// are encouraged to carefully analyze the efficiency and safety of these.
    fn conditional_enforce_equal<CS: ConstraintSystemAbstract<ConstraintF>>(
        &self,
        mut cs: CS,
        other: &Self,
        should_enforce: &Boolean,
    ) -> Result<(), SynthesisError> {
        self.is_eq(cs.ns(|| "is_eq(self, other)"), &other)?
            .conditional_enforce_equal(
                cs.ns(|| "enforce condition"),
                &Boolean::constant(true),
                should_enforce,
            )
    }

    /// Enforce that `self` and `other` are equal.
    ///
    /// A safe default implementation is provided that generates the following constraints:
    /// `self.conditional_enforce_equal(other, &Boolean::TRUE)`.
    ///
    /// More efficient specialized implementation may be possible; implementors
    /// are encouraged to carefully analyze the efficiency and safety of these.
    fn enforce_equal<CS: ConstraintSystemAbstract<ConstraintF>>(
        &self,
        cs: CS,
        other: &Self,
    ) -> Result<(), SynthesisError> {
        self.conditional_enforce_equal(cs, other, &Boolean::constant(true))
    }

    /// If `should_enforce == true`, enforce that `self` and `other` are *not* equal; else,
    /// enforce a vacuously true statement.
    ///
    /// A safe default implementation is provided that generates the following constraints:
    /// `self.is_neq(other)?.conditional_enforce_equal(&Boolean::TRUE, should_enforce)`.
    ///
    /// More efficient specialized implementation may be possible; implementors
    /// are encouraged to carefully analyze the efficiency and safety of these.
    fn conditional_enforce_not_equal<CS: ConstraintSystemAbstract<ConstraintF>>(
        &self,
        mut cs: CS,
        other: &Self,
        should_enforce: &Boolean,
    ) -> Result<(), SynthesisError> {
        self.is_neq(cs.ns(|| "is_neq(self, other)"), &other)?
            .conditional_enforce_equal(
                cs.ns(|| "enforce condition"),
                &Boolean::constant(true),
                should_enforce,
            )
    }

    /// Enforce that `self` and `other` are *not* equal.
    ///
    /// A safe default implementation is provided that generates the following constraints:
    /// `self.conditional_enforce_not_equal(other, &Boolean::TRUE)`.
    ///
    /// More efficient specialized implementation may be possible; implementors
    /// are encouraged to carefully analyze the efficiency and safety of these.
    fn enforce_not_equal<CS: ConstraintSystemAbstract<ConstraintF>>(
        &self,
        cs: CS,
        other: &Self,
    ) -> Result<(), SynthesisError> {
        self.conditional_enforce_not_equal(cs, other, &Boolean::constant(true))
    }
}

impl<T: EqGadget<ConstraintF>, ConstraintF: Field> EqGadget<ConstraintF> for [T] {
    fn is_eq<CS: ConstraintSystemAbstract<ConstraintF>>(
        &self,
        mut cs: CS,
        other: &Self,
    ) -> Result<Boolean, SynthesisError> {
        assert_eq!(self.len(), other.len());
        assert!(!self.is_empty());
        let mut results = Vec::with_capacity(self.len());
        for (i, (a, b)) in self.iter().zip(other).enumerate() {
            results.push(a.is_eq(cs.ns(|| format!("is_eq_{}", i)), b)?);
        }
        Boolean::kary_and(cs.ns(|| "kary and"), &results)
    }

    fn conditional_enforce_equal<CS: ConstraintSystemAbstract<ConstraintF>>(
        &self,
        mut cs: CS,
        other: &Self,
        condition: &Boolean,
    ) -> Result<(), SynthesisError> {
        assert_eq!(self.len(), other.len());
        for (i, (a, b)) in self.iter().zip(other).enumerate() {
            a.conditional_enforce_equal(
                cs.ns(|| format!("conditional_enforce_equal_{}", i)),
                b,
                condition,
            )?;
        }
        Ok(())
    }
}



// helper function that computes a linear combination of the bits of `self` and `other` which
// corresponds to the difference between two field elements a,b, where a (resp. b) is the field
// element whose little-endian bit representation is `self` (resp. other).
// The function returns also a-b over the field (wrapped in an Option) and a flag
// that specifies if all the bits in both `self` and `other` are constants.
fn compute_diff<ConstraintF, CS>(self_bits: &[Boolean], mut cs: CS, other_bits: &[Boolean]) -> (LinearCombination<ConstraintF>, Option<ConstraintF>, bool)
    where
        ConstraintF: PrimeField,
        CS: ConstraintSystemAbstract<ConstraintF>,
{
    let field_bits = ConstraintF::Params::CAPACITY as usize;
    assert!(self_bits.len() <= field_bits);
    assert!(other_bits.len() <= field_bits);

    let (self_lc, self_in_field, is_self_constant) = Boolean::bits_to_linear_combination(&mut cs, self_bits.iter());
    let (other_lc, other_in_field, is_other_constant) = Boolean::bits_to_linear_combination(&mut cs, other_bits.iter());

    let diff_in_field = match (self_in_field, other_in_field) {
        (Some(self_val), Some(other_val)) => Some(self_val-other_val),
        _ => None,
    };
    let all_constants = is_self_constant && is_other_constant;

    (self_lc - other_lc, diff_in_field, all_constants)
}

impl<ConstraintF: PrimeField> EqGadget<ConstraintF> for Vec<Boolean> {
    fn is_eq<CS: ConstraintSystemAbstract<ConstraintF>>(
        &self,
        mut cs: CS,
        other: &Self,
    ) -> Result<Boolean, SynthesisError> {
        assert_eq!(self.len(), other.len());
        //let len = self.len();
        let field_bits = ConstraintF::Params::CAPACITY as usize;
        // Since `self` and `other` may not be packed in a single field element,
        // we process them in chunks of size field_bits and then employ
        // `self` == `other` iff each pair of chunks are equal
        let mut chunk_eq_gadgets = Vec::new();
        for (i, (self_chunk, other_chunk)) in self.chunks(field_bits).zip(other.chunks(field_bits)).enumerate() {

            let (diff_lc, diff_in_field, all_constants) = compute_diff(self_chunk, cs.ns(|| format!("compute diff for chunk {}", i)), other_chunk);

            if all_constants && diff_in_field.is_some() {
                return Ok(Boolean::constant(diff_in_field.unwrap().is_zero()));
            }

            let is_chunk_eq = Boolean::alloc(cs.ns(|| format!("alloc is_eq flag for chunk {}", i)), || {
                let diff = diff_in_field.ok_or(SynthesisError::AssignmentMissing)?;
                Ok(diff.is_zero())
            })?;

            let inv = diff_in_field.map(|diff| {
                match diff.inverse() {
                    Some(inv) => inv,
                    None => ConstraintF::one(), // in this case the value of inv does not matter for the constraint
                }
            });

            let inv_var = FpGadget::<ConstraintF>::alloc(cs.ns(|| format!("alloc inv for chunk {}", i)), || {inv.ok_or(SynthesisError::AssignmentMissing)})?;

            // enforce constraints:
            // is_eq * diff_lc = 0 enforces that is_eq == 0 when diff_lc != 0, i.e., when self != other
            // inv * diff_lc = 1 - is_eq enforces that is_eq == 1 when diff_lc == 0, i.e., when self == other
            cs.enforce(|| format!("enforce is not eq for chunk {}", i), |_| is_chunk_eq.lc(CS::one(), ConstraintF::one()), |lc| lc + &diff_lc, |lc| lc);
            cs.enforce(|| format!("enforce is eq for chunk {}", i), |lc| &inv_var.get_variable() + lc, |lc| lc + &diff_lc, |_| is_chunk_eq.not().lc(CS::one(), ConstraintF::one()));

            // let is_eq = BooleanVec(self_chunk).is_eq(cs.ns(|| format!("equality for chunk {}", i)), &BooleanVec(other_chunk))?;
            chunk_eq_gadgets.push(is_chunk_eq);
        }

        if chunk_eq_gadgets.len() == 0 {
            return  Ok(Boolean::constant(true))
        }

        Boolean::kary_and(cs.ns(|| "is eq"), chunk_eq_gadgets.as_slice())
    }

    fn conditional_enforce_equal<CS: ConstraintSystemAbstract<ConstraintF>>
    (&self, mut cs: CS, other: &Self, should_enforce: &Boolean) -> Result<(), SynthesisError> {
        assert_eq!(self.len(), other.len());
        // split `self` and `other` in chunks of size field_bits and enforce equality between each
        // pair of chunks
        let field_bits = ConstraintF::Params::CAPACITY as usize;
        for (i, (self_chunk, other_chunk)) in self.chunks(field_bits).zip(other.chunks(field_bits)).enumerate() {

            let (diff_lc, diff_in_field, all_constants) = compute_diff(self_chunk, cs.ns(|| format!("compute diff for chunk {}", i)), other_chunk);

            if all_constants && diff_in_field.is_some() && should_enforce.is_constant() {
                if should_enforce.get_value().unwrap() && !diff_in_field.unwrap().is_zero() {
                    return Err(SynthesisError::Unsatisfiable)
                }
                return Ok(())
            }

            // enforce that diff_lc*should_enforce = 0, which enforces that diff_lc = 0 if should_enforce=1, while it enforces nothing if should_enforce=0
            cs.enforce(|| format!("conditionally enforce equal for chunk {}", i), |lc| lc + &diff_lc, |_| should_enforce.lc(CS::one(), ConstraintF::one()), |lc| lc);
        }

        Ok(())
    }

    fn conditional_enforce_not_equal<CS: ConstraintSystemAbstract<ConstraintF>>
    (&self, mut cs: CS, other: &Self, should_enforce: &Boolean) -> Result<(), SynthesisError> {
        assert_eq!(self.len(), other.len());
        let field_bits = ConstraintF::Params::CAPACITY as usize;
        let len = self.len();
        if field_bits < len {
            // In this case we cannot split in chunks here, as it's not true that if two bit vectors
            // are not equal, then they are not equal chunkwise too. Therefore, we
            // compute a Boolean which is true iff `self != `other` and we conditionally
            // enforce it to be true
            let is_neq = self.is_neq(cs.ns(|| "is not equal"), other)?;
            return is_neq.conditional_enforce_equal(cs, &Boolean::constant(true), should_enforce)
        }
        // instead, if `self` and `other` can be packed in a single field element, we can
        // conditionally enforce their inequality, which is more efficient that calling is_neq
        let (diff_lc, diff_in_field, all_constants) = compute_diff(self.as_slice(), &mut cs, other.as_slice());

        if all_constants && diff_in_field.is_some() && should_enforce.is_constant() {
            if should_enforce.get_value().unwrap() && diff_in_field.unwrap().is_zero() {
                return Err(SynthesisError::Unsatisfiable);
            }
            return Ok(())
        }

        let inv = diff_in_field.map(|diff| {
            match diff.inverse() {
                Some(inv) => inv,
                None => ConstraintF::one(), //in this case the value of inv does not matter for the constraint
            }
        });

        let inv_var = FpGadget::<ConstraintF>::alloc(cs.ns(|| "alloc inv"), || {
            let cond = should_enforce.get_value().ok_or(SynthesisError::AssignmentMissing)?;
            if cond {
                return inv.ok_or(SynthesisError::AssignmentMissing)
            }
            // should not enforce anything, so set inv_var to 0 to trivially satisfy the constraint
            Ok(ConstraintF::zero())
        })?;

        // enforce that diff_lc*inv_var = should_enforce, which enforces that diff_lc != 0 if
        // should_enforce=1, while it enforces no constraint on diff_lc when should_enforce = 0,
        // since inv can be trivially set by the prover to 0 to satisfy the constraint
        cs.enforce(|| "conditionally enforce not equal", |lc| lc + &diff_lc, |lc| &inv_var.get_variable() + lc, |_| should_enforce.lc(CS::one(), ConstraintF::one()));

        Ok(())
    }

}

/// A struct for collecting identities of linear combinations of Booleans to serve
/// a more efficient equality enforcement (by packing them in parallel into constraint
/// field elements).
/// Used for simulating arithmetic operations modulo a power of 2.
pub struct MultiEq<ConstraintF: PrimeField, CS: ConstraintSystemAbstract<ConstraintF>> {
    cs: CS,
    // a counter for the number of used equality constraints
    ops: usize,
    // the "size" of the identity, i.e. the bit length of the maximum value
    // that can be obtained by the linear combination.
    bits_used: usize,
    // the left hand side of the identity
    lhs: LinearCombination<ConstraintF>,
    // the right hand side of the identity
    rhs: LinearCombination<ConstraintF>,
}

impl<ConstraintF: PrimeField, CS: ConstraintSystemAbstract<ConstraintF>> MultiEq<ConstraintF, CS> {
    pub fn new(cs: CS) -> Self {
        MultiEq {
            cs,
            ops: 0,
            bits_used: 0,
            lhs: LinearCombination::zero(),
            rhs: LinearCombination::zero(),
        }
    }

    fn accumulate(&mut self) {
        let ops = self.ops;
        let lhs = self.lhs.clone();
        let rhs = self.rhs.clone();
        self.cs.enforce(
            || format!("multieq {}", ops),
            |_| lhs,
            |lc| lc + CS::one(),
            |_| rhs,
        );
        self.lhs = LinearCombination::zero();
        self.rhs = LinearCombination::zero();
        self.bits_used = 0;
        self.ops += 1;
    }

    /// Enforces simulatenously the MultiEq `self` and `lhs == rhs` of the at most `num_bits` large
    /// linear combinations `lhs` and `rhs`.
    pub fn enforce_equal(
        // the MultiEq
        &mut self,
        // the number of bits used for lhs and rhs, must be < capacity of `ConstraintF`
        num_bits: usize,
        // the linear combinations to be aggregated in `self`
        lhs: &LinearCombination<ConstraintF>,
        rhs: &LinearCombination<ConstraintF>,
    ) {
        // Check if we will exceed the capacity. If yes, then use accumulate on `self` first.
        if (ConstraintF::Params::CAPACITY as usize) <= (self.bits_used + num_bits) {
            self.accumulate();
        }

        assert!((ConstraintF::Params::CAPACITY as usize) > (self.bits_used + num_bits));
        // Since we do not exceed the capacity, cumulate (lhs,rhs) in `self` by appending
        let frmstr = ConstraintF::from_str("2").unwrap_or_default();

        let coeff = frmstr.pow(&[self.bits_used as u64]);
        self.lhs = self.lhs.clone() + (coeff, lhs);
        self.rhs = self.rhs.clone() + (coeff, rhs);
        self.bits_used += num_bits;
    }
}

impl<ConstraintF: PrimeField, CS: ConstraintSystemAbstract<ConstraintF>> Drop
    for MultiEq<ConstraintF, CS>
{
    fn drop(&mut self) {
        if self.bits_used > 0 {
            self.accumulate();
        }
    }
}

impl<ConstraintF: PrimeField, CS: ConstraintSystemAbstract<ConstraintF>>
    ConstraintSystemAbstract<ConstraintF> for MultiEq<ConstraintF, CS>
{
    type Root = Self;

    fn one() -> Variable {
        CS::one()
    }

    fn alloc<F, A, AR>(&mut self, annotation: A, f: F) -> Result<Variable, SynthesisError>
    where
        F: FnOnce() -> Result<ConstraintF, SynthesisError>,
        A: FnOnce() -> AR,
        AR: Into<String>,
    {
        self.cs.alloc(annotation, f)
    }

    fn alloc_input<F, A, AR>(&mut self, annotation: A, f: F) -> Result<Variable, SynthesisError>
    where
        F: FnOnce() -> Result<ConstraintF, SynthesisError>,
        A: FnOnce() -> AR,
        AR: Into<String>,
    {
        self.cs.alloc_input(annotation, f)
    }

    fn enforce<A, AR, LA, LB, LC>(&mut self, annotation: A, a: LA, b: LB, c: LC)
    where
        A: FnOnce() -> AR,
        AR: Into<String>,
        LA: FnOnce(LinearCombination<ConstraintF>) -> LinearCombination<ConstraintF>,
        LB: FnOnce(LinearCombination<ConstraintF>) -> LinearCombination<ConstraintF>,
        LC: FnOnce(LinearCombination<ConstraintF>) -> LinearCombination<ConstraintF>,
    {
        self.cs.enforce(annotation, a, b, c)
    }

    fn push_namespace<NR, N>(&mut self, name_fn: N)
    where
        NR: Into<String>,
        N: FnOnce() -> NR,
    {
        self.cs.get_root().push_namespace(name_fn)
    }

    fn pop_namespace(&mut self) {
        self.cs.get_root().pop_namespace()
    }

    fn get_root(&mut self) -> &mut Self::Root {
        self
    }

    fn num_constraints(&self) -> usize {
        self.cs.num_constraints()
    }

    fn eval_lc(&self, lc: &LinearCombination<ConstraintF>) -> Result<Option<ConstraintF>, SynthesisError> {
        self.cs.eval_lc(lc)
    }
}

#[cfg(test)]
mod test {
    use rand::{thread_rng, Rng};
    use r1cs_core::{ConstraintSystem, SynthesisMode, ConstraintSystemAbstract, ConstraintSystemDebugger};
    use algebra::fields::{tweedle::Fr, PrimeField, FpParameters};
    use crate::{boolean::Boolean, alloc::AllocGadget, eq::EqGadget};

    #[test]
    fn test_eq_for_boolean_vec() {
        let rng = &mut thread_rng();
        const FIELD_BITS: usize = <Fr as PrimeField>::Params::CAPACITY as usize;
        // test with vectors whose length is either smaller or greater than the field capacity
        const VEC_LENGTHS: [usize; 3] = [FIELD_BITS /2, FIELD_BITS, FIELD_BITS *2];
        for len in &VEC_LENGTHS {
            let num_chunks = *len/ FIELD_BITS + if *len % FIELD_BITS != 0 {1} else {0};
            let mut cs = ConstraintSystem::<Fr>::new(SynthesisMode::Debug);

            let vec1 = (0..*len).map(|_| rng.gen()).collect::<Vec<bool>>();
            let vec2 = (0..*len).map(|_| rng.gen()).collect::<Vec<bool>>();

            let vec1_var = vec1.iter().enumerate().map(|(i, bit)| {
                match i % 3 {
                    0 => Boolean::constant(*bit),
                    1 => Boolean::alloc(cs.ns(|| format!("alloc vec1 bit {}", i)), || Ok(*bit)).unwrap(),
                    2 => Boolean::alloc(cs.ns(|| format!("alloc vec1 bit {}", i)), || Ok(*bit)).unwrap().not(),
                    _ => Boolean::Constant(false),
                }
            }).collect::<Vec<_>>();
            let vec2_var = vec2.iter().enumerate().map(|(i, bit)| {
                match i % 3 {
                    0 => Boolean::alloc(cs.ns(|| format!("alloc vec2 bit {}", i)), || Ok(*bit)).unwrap().not(),
                    1 => Boolean::constant(*bit),
                    2 => Boolean::alloc(cs.ns(|| format!("alloc vec2 bit {}", i)), || Ok(*bit)).unwrap(),
                    _ => Boolean::Constant(false),
                }
            }).collect::<Vec<_>>();

            // test functions on vectors which are distinct
            let is_eq = vec1_var.is_eq(cs.ns(|| "vec1 == vec2"), &vec2_var).unwrap();
            assert!(!is_eq.get_value().unwrap());
            assert!(cs.is_satisfied());

            let is_neq = vec1_var.is_neq(cs.ns(|| "vec1 != vec2"), &vec2_var).unwrap();
            assert!(is_neq.get_value().unwrap());
            assert!(cs.is_satisfied());

            vec1_var.enforce_not_equal(cs.ns(|| "enforce vec1 != vec2"), &vec2_var).unwrap();
            assert!(cs.is_satisfied());
            vec1_var.conditional_enforce_equal(cs.ns(|| "fake enforce vec1 == vec2"), &vec2_var, &Boolean::constant(false)).unwrap();
            assert!(cs.is_satisfied());
            vec1_var.conditional_enforce_equal(cs.ns(|| "enforce vec1 == vec2"), &vec2_var, &Boolean::constant(true)).unwrap();
            assert!(!cs.is_satisfied());

            // test functions on vectors which are equal
            let mut cs = ConstraintSystem::<Fr>::new(SynthesisMode::Debug);
            let vec1_var = vec1.iter().enumerate().map(|(i, bit)| {
                match i % 3 {
                    0 => Boolean::constant(*bit),
                    1 => Boolean::alloc(cs.ns(|| format!("alloc vec1 bit {}", i)), || Ok(*bit)).unwrap(),
                    2 => Boolean::alloc(cs.ns(|| format!("alloc vec1 bit {}", i)), || Ok(*bit)).unwrap().not(),
                    _ => Boolean::Constant(false),
                }
            }).collect::<Vec<_>>();
            let vec1_var_copy = vec1.iter().enumerate().map(|(i, bit)| {
                match i % 3 {
                    0 => Boolean::alloc(cs.ns(|| format!("alloc vec1 copy bit {}", i)), || Ok(*bit)).unwrap(),
                    1 => Boolean::constant(*bit),
                    2 => Boolean::alloc(cs.ns(|| format!("alloc vec1 copy bit {}", i)), || Ok(*bit)).unwrap().not(),
                    _ => Boolean::Constant(false),
                }
            }).collect::<Vec<_>>();
            let num_constraints = cs.num_constraints();
            let is_eq = vec1_var.is_eq(cs.ns(|| "vec1 == vec1"), &vec1_var_copy).unwrap();
            assert!(is_eq.get_value().unwrap());
            assert!(cs.is_satisfied());
            assert_eq!(num_constraints + 3 + 4*(num_chunks-1), cs.num_constraints());

            let num_constraints = cs.num_constraints();
            let is_neq = vec1_var.is_neq(cs.ns(|| "vec1 != vec1"), &vec1_var_copy).unwrap();
            assert!(!is_neq.get_value().unwrap());
            assert!(cs.is_satisfied());
            assert_eq!(num_constraints + 3 + 4*(num_chunks-1), cs.num_constraints());

            let num_constraints = cs.num_constraints();
            vec1_var.enforce_equal(cs.ns(|| "enforce vec1 == vec1"), &vec1_var_copy).unwrap();
            assert!(cs.is_satisfied());
            assert_eq!(num_constraints + num_chunks, cs.num_constraints());
            vec1_var.conditional_enforce_not_equal(cs.ns(|| "fake enforce vec1!=vec1"), &vec1_var_copy, &Boolean::constant(false)).unwrap();
            assert!(cs.is_satisfied());
            let num_constraints = cs.num_constraints();
            vec1_var.conditional_enforce_not_equal(cs.ns(|| "enforce vec1!=vec1"), &vec1_var_copy, &Boolean::constant(true)).unwrap();
            assert!(!cs.is_satisfied());
            assert_eq!(num_constraints + 4*(num_chunks-1) + if num_chunks == 1 {1} else {4}, cs.num_constraints());
        }


    }
}
