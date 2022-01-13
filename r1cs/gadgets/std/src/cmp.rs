use std::cmp::Ordering;
use algebra::Field;
use r1cs_core::{ConstraintSystemAbstract, SynthesisError};
use crate::boolean::Boolean;
use crate::eq::EqGadget;

pub trait ComparisonGadget<ConstraintF: Field>: Sized + EqGadget<ConstraintF>
{
    /// Output a `Boolean` gadget which is equal to `self < other`
    fn is_smaller_than<CS: ConstraintSystemAbstract<ConstraintF>>(&self, cs: CS, other: &Self) -> Result<Boolean, SynthesisError>;

    /// Enforce in the constraint system `cs` that `self < other`
    fn enforce_smaller_than<CS: ConstraintSystemAbstract<ConstraintF>>(&self, cs: CS, other: &Self) -> Result<(), SynthesisError>;

    /// Output a `Boolean` gadget which is true iff the given order relationship between `self`
    /// and `other` holds. If `should_also_check_equality` is true, then the order relationship
    /// is not strict (e.g., `self <= other` must hold rather than `self < other`).
    // The ordering relationship with equality is verified by exploiting the following identities:
    // - x <= y iff !(y < x)
    // - x >= y iff !(x < y)
    fn is_cmp<CS: ConstraintSystemAbstract<ConstraintF>>(
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


        let is_smaller = left.is_smaller_than(cs.ns(|| "is smaller"), right)?;

        if should_also_check_equality {
            return Ok(is_smaller.not())
        }

        Ok(is_smaller)
    }

    /// Enforce the given order relationship between `self` and `other`.
    /// If `should_also_check_equality` is true, then the order relationship is not strict
    /// (e.g., `self <= other` is enforced rather than `self < other`).
    // Default implementation calls `is_cmp` to get a Boolean which is true iff the order
    // relationship holds, and then enforce this Boolean to be true
    fn enforce_cmp<CS: ConstraintSystemAbstract<ConstraintF>>(
        &self,
        mut cs: CS,
        other: &Self,
        ordering: Ordering,
        should_also_check_equality: bool,
    ) -> Result<(), SynthesisError> {
        let is_cmp = self.is_cmp(cs.ns(|| "cmp outcome"), other, ordering, should_also_check_equality)?;

        is_cmp.enforce_equal(cs.ns(|| "enforce cmp"), &Boolean::constant(true))
    }
}