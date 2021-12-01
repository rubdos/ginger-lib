//! A submodule of low-level function for modular reduction/normalization of non-native field gadgets.
use algebra::{
    biginteger::BigInteger,
    fields::{FpParameters, PrimeField},
};

use crate::{
    fields::{
        fp::FpGadget,
        nonnative::{nonnative_field_gadget::NonNativeFieldGadget, params::get_params},
    },
    overhead,
    prelude::*,
};
use r1cs_core::{ConstraintSystemAbstract, SynthesisError};
use std::{cmp::min, marker::PhantomData, vec::Vec};

use num_bigint::BigUint;
use num_integer::Integer;
use num_traits::{One, Zero};

use crate::fields::FieldGadget;

/// Recombines the large integer value from a vector of (not necessarily normalized) limbs.
pub fn limbs_to_bigint<ConstraintF: PrimeField>(
    bits_per_limb: usize,
    limbs: &[ConstraintF],
) -> BigUint {
    let mut val = BigUint::zero();
    let mut big_cur = BigUint::one();
    let two = BigUint::from(2u32);
    for limb in limbs.iter().rev() {
        let mut limb_repr = limb.into_repr().to_bits();
        limb_repr.reverse(); //We need them in little endian
        let mut small_cur = big_cur.clone();
        for limb_bit in limb_repr.iter() {
            if *limb_bit {
                val += &small_cur;
            }
            small_cur *= 2u32;
        }
        big_cur *= two.pow(bits_per_limb as u32);
    }

    val
}

/// Converts an unsigned big integer `bigint` into an element from the constraint field F_p by
/// computing (bigint mod p).
pub fn bigint_to_constraint_field<ConstraintF: PrimeField>(bigint: &BigUint) -> ConstraintF {
    let mut val = ConstraintF::zero();
    let mut cur = ConstraintF::one();
    let bytes = bigint.to_bytes_be();

    let basefield_256 = ConstraintF::from_repr(<ConstraintF as PrimeField>::BigInt::from(256));

    for byte in bytes.iter().rev() {
        let bytes_basefield = ConstraintF::from(*byte as u128);
        val += cur * bytes_basefield;

        cur *= &basefield_256;
    }

    val
}

/// The collections of methods for reducing the presentations of NonNativeFieldGadgets
pub struct Reducer<SimulationF: PrimeField, ConstraintF: PrimeField> {
    pub simulation_phantom: PhantomData<SimulationF>,
    pub constraint_phantom: PhantomData<ConstraintF>,
}

impl<SimulationF: PrimeField, ConstraintF: PrimeField> Reducer<SimulationF, ConstraintF> {
    /// Convert a limb of `num_bits` into a vector of Boolean gadgets.
    /// Allowing `num_bits` to be at most `ConstraintF::size_in_bits() - 1` for efficient 'unpacking'.
    // Consumes `num_bits` + 1 constraints.
    pub fn limb_to_bits<CS: ConstraintSystemAbstract<ConstraintF>>(
        mut cs: CS,
        limb: &FpGadget<ConstraintF>,
        num_bits: usize,
    ) -> Result<Vec<Boolean>, SynthesisError> {
        let num_bits = min(num_bits, ConstraintF::Params::CAPACITY as usize);

        // we extract the bits from the `num_bits` least significant bits
        let to_skip = ConstraintF::size_in_bits() - num_bits;
        assert!(to_skip <= ConstraintF::size_in_bits());

        limb.to_bits_with_length_restriction(cs.ns(|| "limb to bits"), to_skip)
    }

    /// Reduction to normal form, which again has no excess in its limbs.
    pub fn reduce<CS: ConstraintSystemAbstract<ConstraintF>>(
        mut cs: CS,
        elem: &mut NonNativeFieldGadget<SimulationF, ConstraintF>,
    ) -> Result<(), SynthesisError> {
        // Alloc of a non-native in normal form (not necessarily below the
        // non-native modulus)
        let new_elem = NonNativeFieldGadget::alloc(cs.ns(|| "alloc normal form"), || {
            Ok(elem.get_value().unwrap_or_default())
        })?;
        elem.enforce_equal(cs.ns(|| "elem == new_elem"), &new_elem)?;
        *elem = new_elem;
        Ok(())
    }

    /// Reduction to be enforced after additions.
    /// Checks if the resulting elem is still "small" enough for a multiplication, and
    /// reduces it otherwise.
    pub fn post_add_reduce<CS: ConstraintSystemAbstract<ConstraintF>>(
        cs: CS,
        elem: &mut NonNativeFieldGadget<SimulationF, ConstraintF>,
    ) -> Result<(), SynthesisError> {
        let params = get_params(SimulationF::size_in_bits(), ConstraintF::size_in_bits());
        let surfeit = overhead!(elem.num_of_additions_over_normal_form + ConstraintF::one()) + 1;

        if ConstraintF::size_in_bits() > 2 * params.bits_per_limb + surfeit + 1 {
            Ok(())
        } else {
            Self::reduce(cs, elem)
        }
    }

    /// Reduction used before multiplication to reduce the representations in a way that allows efficient multiplication
    pub fn pre_mul_reduce<CS: ConstraintSystemAbstract<ConstraintF>>(
        mut cs: CS,
        elem: &mut NonNativeFieldGadget<SimulationF, ConstraintF>,
        elem_other: &mut NonNativeFieldGadget<SimulationF, ConstraintF>,
    ) -> Result<(), SynthesisError> {
        let params = get_params(SimulationF::size_in_bits(), ConstraintF::size_in_bits());

        if 2 * params.bits_per_limb + algebra::log2(params.num_limbs) as usize
            > ConstraintF::size_in_bits() - 1
        {
            panic!("The current limb parameters do not support multiplication.");
        }

        // TODO: Try to understand if one can write the optional reduction of one
        // (or both) of the factors more elegantly.
        let mut i = 0;
        loop {
            let prod_of_num_of_additions = (elem.num_of_additions_over_normal_form
                + ConstraintF::one())
                * (elem_other.num_of_additions_over_normal_form + ConstraintF::one());
            // overhead_limb = (num_add(a) + 1)(num_add(b)+1) * num_limbs
            // Why the product of the num_of_additions and not the sum?
            let overhead_limb = overhead!(prod_of_num_of_additions.mul(&ConstraintF::from_repr(
                <ConstraintF as PrimeField>::BigInt::from((params.num_limbs) as u64)
            )));
            let bits_per_mulresult_limb = 2 * (params.bits_per_limb + 1) + overhead_limb;

            // if the product of limbs has bit length < than length(modulus),
            // there is nothing to do.
            if bits_per_mulresult_limb < ConstraintF::size_in_bits() {
                break;
            }

            // otherwise we reduce the factor which is expected to have larger excess
            // over normal form.
            if elem.num_of_additions_over_normal_form
                >= elem_other.num_of_additions_over_normal_form
            {
                Self::reduce(cs.ns(|| format!("reduce elem {}", i)), elem)?;
            } else {
                Self::reduce(cs.ns(|| format!("reduce elem other {}", i)), elem_other)?;
            }
            i += 1;
        }

        Ok(())
    }

    /// Reduction to the normal form
    pub fn pre_eq_reduce<CS: ConstraintSystemAbstract<ConstraintF>>(
        cs: CS,
        elem: &mut NonNativeFieldGadget<SimulationF, ConstraintF>,
    ) -> Result<(), SynthesisError> {
        if elem.is_in_the_normal_form {
            return Ok(());
        }

        Self::reduce(cs, elem)
    }

    /// The low-level function for the equality check of two non-natives 
    /// ``
    ///     left = Sum_{i=0..} left[i]*A^i, 
    ///     right= Sum_{i=0..} right[i]*A^i
    /// `` 
    /// as big integers, given as equally long slices of limbs 
    /// ``
    ///     [left[0],left[1],...], 
    ///     [right[0],right[1],...],
    /// `` 
    /// where each limb being length bounded by `bits_per_limb + surfeit`.
    /// Takes 
    ///      `(S-1) * (1 + bits_per_limb + surfeit) + 2`
    /// constraints, where 
    //  ``
    //      S = Floor[
    //          (ConstraintF::CAPACITY - 2 - (bits_per_limb + surfeit)) / shift_per_limb
    //      ] + 1.
    // ``
    pub fn group_and_check_equality<CS: ConstraintSystem<ConstraintF>>(
        mut cs: CS,
        // The additional number of bits beyond `bits_per_limb`
        surfeit: usize,
        // The number of bits  
        bits_per_limb: usize,
        // defines arity of the limb representation, i.e. `A= 2^{shift_per_limb}`.
        // Security note: must be >= 2.
        shift_per_limb: usize,
        left: &[FpGadget<ConstraintF>],
        right: &[FpGadget<ConstraintF>],
    ) -> Result<(), SynthesisError> {
        let zero = FpGadget::<ConstraintF>::zero(cs.ns(|| "hardcode zero"))?;

        let mut limb_pairs = Vec::<(FpGadget<ConstraintF>, FpGadget<ConstraintF>)>::new();
        // We group the limbs so that we can handle their sum
        // ``
        //      group_total = limb[0]*1 + limb[1]*A + ... + limb[S-1]*A^{S-1},
        // ``
        // within a single constraint field element, where `A = 2^shift_per_limb`.
        // Assuming `A >= 2`, we have 
        // `` 
        //   len(limb[0]*1 + limb[1]*A) <= bits_per_limb + surfeit + len(A) + 1,
        //   len(limb[0]*1 + limb[1]*A + limb[2]*A^2) <= bits_per_limb + surfeit + 2 * len(A) + 1,
        //   ...
        //   len(limb[0]*1 + limb[1]*A + ... + limb[S-1]*A^{S-1}) <=
        //                       <= bits_per_limb + surfeit + (S-1) * len(A) + 1
        // ``
        // and hence 
        // ``
        //   len(group_total) <= bits_per_group 
        //              = bits_per_limb + surfeit + (S-1) * len(A) + 1.  
        // ``
        // To assure that the following operations on the totals do not exceed the capacity, 
        // it is sufficient to demand 
        // ``
        //  bits_per_group + 1 <= ConstraintF::CAPACITY,
        // ``
        // as described in the comments below. This yields 
        // ``
        //      bits_per_limb + surfeit + (S-1) * shift_per_limb + 2 <= ConstraintF::CAPACITY,
        // ``
        // and thus
        // ``
        //      S - 1 = Floor[
        //          (ConstraintF::CAPACITY - 2 - (bits_per_limb + surfeit)) / shift_per_limb
        //      ].
        // ``
    
        // TODO: The following formula computes 
        //      S = Ceil[
        //          (ConstraintF::CAPACITY - 2 - (bits_per_limb + surfeit)) / shift_per_limb
        //      ] 
        //        =  (ConstraintF::CAPACITY - 2 - (bits_per_limb + surfeit) + shift_per_limb - 1) 
        //           / shift_per_limb,
        // which differs sometimes from `Floor[] + 1`. 
        let num_limb_in_a_group = (ConstraintF::size_in_bits()
            - 1
            - surfeit
            - 1 
            - 1 
            - 1
            - (bits_per_limb - shift_per_limb))
            / shift_per_limb;

        // Compute the powers of the arity for a group of limbs, i.e.
        // `shift_array = [1, A, A^2, ..., A^(num_limbs_per_group-1)}]`.
        let shift_array = {
            let mut array = Vec::new();
            let mut cur = ConstraintF::one().into_repr();
            for _ in 0..num_limb_in_a_group {
                array.push(ConstraintF::from_repr(cur));
                cur.muln(shift_per_limb as u32);
            }

            array
        };

        // zip the limbs of `left` and `right` and reverse to little endian order.
        for (left_limb, right_limb) in left.iter().zip(right.iter()).rev() {
            limb_pairs.push((left_limb.clone(), right_limb.clone()));
        }

        let mut groupped_limb_pairs =
            Vec::<(FpGadget<ConstraintF>, FpGadget<ConstraintF>, usize)>::new();

        for (i, limb_pairs_in_a_group) in limb_pairs.chunks(num_limb_in_a_group).enumerate() {
            let mut left_total_limb = zero.clone();
            let mut right_total_limb = zero.clone();

            // For each group `[limb[0],...limb[S-1]]`, where `S = num_limbs_per_group`, 
            // we compute 
            // `group_total = limb[0]*1 + limb[1]*A + ... limb[S-1]*A^{S-1}`.
            // This is done for both left and right operands.
            for (j, ((left_limb, right_limb), shift)) in limb_pairs_in_a_group
                .iter()
                .zip(shift_array.iter())
                .enumerate()
            {
                let left_mul = left_limb
                    .mul_by_constant(cs.ns(|| format!("left_limb * shift {},{}", i, j)), shift)?;
                left_total_limb.add_in_place(
                    cs.ns(|| format!("left_total_limb += left_mul {},{}", i, j)),
                    &left_mul,
                )?;

                let right_mul = right_limb
                    .mul_by_constant(cs.ns(|| format!("right_limb * shift {},{}", i, j)), shift)?;
                right_total_limb.add_in_place(
                    cs.ns(|| format!("right_total_limb += right_mul {},{}", i, j)),
                    &right_mul,
                )?;
            }

            groupped_limb_pairs.push((
                left_total_limb,
                right_total_limb,
                limb_pairs_in_a_group.len(),
            ));
        }

        // The following code is ported from [[Bellman]].
        // The equality of two `A`-ary representations `[L[0],L[1],..]` and `[R[0],R[1],..]` with 
        // oversized limbs is proven by enforcing their *shifted* differences 
        //      `[L[0] + (- R[0] + shift_constant) , 
        //          L[1] + (- R[1] + shift_constant), 
        //              ..]`, 
        // to represent 
        //      `Sum_{i>=0} shift_constant * A^i`.
        // The constant `shift_constant = 2^{bits_per_group }` is to circumvent underflows, 
        // yet still not producing overflows. With this choice  
        //      `- R[i] + shift_constant` 
        // is from the range `[0, 2^{bits_per_group} ]`, the sum `L[i] + shift_constant - R[i]` 
        // is from the range `[0, 2^{bits_per_group + 1} )` hence has at most `bits_per_group` many
        // bits. (The latter follows from the observation, that `shift_constant - R[i]` is equal to 
        // to the edge case `2^{bits_per_group}` if and only if `R[i] = 0`.)
        // Since the length of the carries are throughout `<= bits_per_limb + surfeit`, see below, the 
        // `L[i] + carry[i-1]` is still at most `bits_per_group` long, and hence the overall sum 
        // ``
        //      L[i] + carry[i-1] + (shift_constant - R[i]) 
        // `` 
        // is of length `<= bits_per_group + 1`.   
        //
        // [Bellman]: https://github.com/alex-ozdemir/bellman-bignat/blob/master/src/mp/bignat.rs#L567
        let mut carry_in = zero;
        let mut carry_in_value = ConstraintF::zero();
        let mut accumulated_extra = BigUint::zero();
        // The group totals have arity `A^S = 2^{S*shift_per_limb}`.
        for (group_id, (left_total_limb, right_total_limb, num_limb_in_this_group)) in
            groupped_limb_pairs.iter().enumerate()
        {
            // Carry and remainder are subject to the following constraints: 
            // The quotient-remainder constraint
            //   shift_constant + carry_in + group_total_left - group_total_right 
            //          == carry * A^S + 0 + (shift_constant % A^S),
            // and the length restrictions for the carry
            //        len(carry) <= bits_per_limb + surfeit.        
            // These length bound assures that no modular reduction takes place on both 
            // sides of the quotient-remainder constraint.

            // NOTE: the carries are length bounded by `bits_per_limb + surfeit`, assuming 
            // `shift_per_limb>=2`. This can be seen as follows.
            //      carry[0] = 0,
            // and hence the first carry satisfies
            //      len(carry[1]) = bits_per_group - shift_per_limb * S 
            //           =  bits_per_limb + surfeit + 1 - shift_per_limb
            //           <= bits_per_limb + surfeit.
            // All further carries satisfy
            //      len(carry[i]) = bits_per_group + 1 - shift_per_limb * S 
            //          =  bits_per_limb + surfeit + 2 - shift_per_limb
            //          <=  bits_per_limb + surfeit,
            // under the assumption that `shift_per_limb>= 2`.
            
            // TODO: set an assert for `shift_per_limb>=2`

            // Computing the shift constant `pad_limb_repr`:
            // ``
            //   shift_constant = 2^{bits_per_group + 1} 
            //      = 2^{bits_per_limb + surfeit + (S-1) * shift_per_limb + 2 }. 
            // ``
            let mut pad_limb_repr: <ConstraintF as PrimeField>::BigInt =
                ConstraintF::one().into_repr();

            pad_limb_repr.muln(
                (surfeit
                    + (bits_per_limb - shift_per_limb)
                    + shift_per_limb * num_limb_in_this_group
                    + 1
                    + 1) as u32,
            );
            let pad_limb = ConstraintF::from_repr(pad_limb_repr);

            let left_total_limb_value = left_total_limb.get_value().unwrap_or_default();
            let right_total_limb_value = right_total_limb.get_value().unwrap_or_default();

            let mut carry_value =
                left_total_limb_value + carry_in_value + pad_limb - right_total_limb_value;

            let mut carry_repr = carry_value.into_repr();
            carry_repr.divn((shift_per_limb * num_limb_in_this_group) as u32);

            carry_value = ConstraintF::from_repr(carry_repr);

            // The length restriction of the carry is proven below.
            let carry = FpGadget::<ConstraintF>::alloc(
                cs.ns(|| format!("alloc carry {}", group_id)),
                || Ok(carry_value),
            )?;

            // We add the shift_constant to the accumulator
            accumulated_extra += limbs_to_bigint(bits_per_limb, &[pad_limb]);

            // accumulated_extra = A^S * new_accumulated_extra + remainder, 
            // with remainder < A^S, or equivalently
            let (new_accumulated_extra, remainder) = accumulated_extra.div_rem(
                &BigUint::from(2u64).pow((shift_per_limb * num_limb_in_this_group) as u32),
            );
            let remainder_limb = bigint_to_constraint_field::<ConstraintF>(&remainder);

            // Now we enforce the quotient remainder constraint.
            //      left_total_limb + pad_limb + carry_in - right_total_limb
            //   ==  carry * A^S + remainder
            let eqn_left = left_total_limb
                .add_constant(
                    cs.ns(|| format!("left_total_limb + pad_limb {}", group_id)),
                    &pad_limb,
                )?
                .add(
                    cs.ns(|| format!("left_total_limb + pad_limb + carry_in {}", group_id)),
                    &carry_in,
                )?
                .sub(
                    cs.ns(|| {
                        format!(
                            "left_total_limb + pad_limb + carry_in - right_total_limb {}",
                            group_id
                        )
                    }),
                    right_total_limb,
                )?;

            let eqn_right = carry
                    .mul_by_constant(
                        cs.ns(|| format!("carry * 2^(shift_per_limb * num_limb_in_this_group) {}", group_id)),
                        &ConstraintF::from(2u64).pow(&[(shift_per_limb * num_limb_in_this_group) as u64])
                    )?
                    .add_constant(
                        cs.ns(|| format!("carry * 2^(shift_per_limb * num_limb_in_this_group) + remainder_limb {}", group_id)),
                        &remainder_limb
                    )?;

            eqn_left.enforce_equal(
                cs.ns(|| format!("eqn_left == eqn_right {}", group_id)),
                &eqn_right,
            )?;

            accumulated_extra = new_accumulated_extra;
            carry_in = carry.clone();
            carry_in_value = carry_value;

            if group_id == groupped_limb_pairs.len() - 1 {
                // The highest significant group is treated differently:
                // the carry must be equal the accumulated shifts.
                let accumulated_extra_g = FpGadget::<ConstraintF>::from_value(
                    cs.ns(|| format!("hardcode accumulated_extra {}", group_id)),
                    &bigint_to_constraint_field(&accumulated_extra),
                );
                carry.enforce_equal(
                    cs.ns(|| format!("carry == accumulated_extra {}", group_id)),
                    &accumulated_extra_g,
                )?;
            } else {
                // The length restriction for the carry
                // Costs `surfeit + bits_per_limb` many constraints.
                Reducer::<SimulationF, ConstraintF>::limb_to_bits(
                    cs.ns(|| format!("carry_to_bits_{}", group_id)),
                    &carry,
                    surfeit + bits_per_limb,
                )?;
            }
        }

        Ok(())
    }
}
