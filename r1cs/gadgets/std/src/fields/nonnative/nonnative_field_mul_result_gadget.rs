use crate::{
    fields::{
        fp::FpGadget,
        nonnative::{
            nonnative_field_gadget::NonNativeFieldGadget,
            params::get_params,
            reduce::{bigint_to_constraint_field, limbs_to_bigint, Reducer},
        },
    },
    bitlen,
    prelude::*,
    FromGadget,
};
use algebra::fields::{FpParameters, PrimeField};
use num_bigint::BigUint;
use r1cs_core::{ConstraintSystemAbstract, SynthesisError};
use std::{marker::PhantomData, vec::Vec};
use core::cmp::max;

#[derive(Debug)]
#[must_use]
/// The gadget for the non-reduced products of `NonNativeFieldGadget`s. 
pub struct NonNativeFieldMulResultGadget<SimulationF: PrimeField, ConstraintF: PrimeField> {
    /// Limbs of the product representation, starting with the most significant limb.
    /// Normal form corresponds to the limb sizes 
    /// ``
    ///     bits_per_limb[i] = 2 * NonNativeFieldParams::bits_per_limb,
    /// ``
    /// for all except the most significant limb, for which 
    /// ``
    ///     bits_per_limb[0] = 2 * (NonNativeFieldParams::bits_per_limb
    ///                                         % SimulationF::bit_size()).
    /// ``
    pub limbs: Vec<FpGadget<ConstraintF>>,
    /// As `num_add_over_normal_form` for `NonNativeGadget`s, keeps track of the limb 
    /// size bound 
    /// ``
    ///     limbs[i] < (prod_of_num_additions + 1) * 2^bits_per_limb[i].
    /// ``
    pub num_add_over_normal_form: ConstraintF,
    #[doc(hidden)]
    pub simulation_phantom: PhantomData<SimulationF>,
}

impl<SimulationF: PrimeField, ConstraintF: PrimeField>
    FromGadget<&NonNativeFieldGadget<SimulationF, ConstraintF>, ConstraintF>
    for NonNativeFieldMulResultGadget<SimulationF, ConstraintF>
{
    fn from<CS: ConstraintSystemAbstract<ConstraintF>>(
        other: &NonNativeFieldGadget<SimulationF, ConstraintF>,
        cs: CS,
    ) -> Result<Self, SynthesisError> {
        let params = get_params(SimulationF::size_in_bits(), ConstraintF::size_in_bits());

        let mut limbs = other.limbs.clone();
        limbs.reverse();
        limbs.resize(2 * params.num_limbs - 1, FpGadget::<ConstraintF>::zero(cs)?);
        limbs.reverse();

        let num_add_over_normal_form =
            other.num_of_additions_over_normal_form + &ConstraintF::one();

        Ok(Self {
            limbs,
            num_add_over_normal_form,
            simulation_phantom: PhantomData,
        })
    }
}

impl<SimulationF: PrimeField, ConstraintF: PrimeField>
    NonNativeFieldMulResultGadget<SimulationF, ConstraintF>
{
    /// Get the value of the multiplication result
    pub fn value(&self) -> Result<SimulationF, SynthesisError> {
        let params = get_params(SimulationF::size_in_bits(), ConstraintF::size_in_bits());

        let p_representations =
            NonNativeFieldGadget::<SimulationF, ConstraintF>::get_limbs_representations_from_big_integer(
                &<SimulationF as PrimeField>::Params::MODULUS
            )?;
        let p_bigint = limbs_to_bigint(params.bits_per_limb, &p_representations);

        let mut limbs_values = Vec::<ConstraintF>::new();
        for limb in self.limbs.iter() {
            limbs_values.push(limb.get_value().unwrap_or_default());
        }
        let value_bigint = limbs_to_bigint(params.bits_per_limb, &limbs_values);

        let res = bigint_to_constraint_field::<SimulationF>(&(value_bigint % p_bigint));
        Ok(res)
    }

    /// Reducing a NonNativeMulResultGadget back to a non-native field gadget
    /// in normal form. Assumes that 
    /// ``
    ///     2 * bits_per_limb + surfeit + len(num_limbs) <= CAPACITY - 2.
    /// ``
    /// where 
    /// ``
    ///     bits_per_limb = NonNativeFieldParams::bits_per_limb, 
    ///     surfeit = len(num_add(self) + 1), 
    ///     num_limbs = NonNativeFieldParams::num_limbs.
    /// ``
    // Costs
    // ``
    //     C =  len(p) + surfeit 
    //          +  num_limbs^2
    //          +  (S-1) * (3 + bits_per_limb + surfeit + len(num_limbs)) + 1
    // ``
    // constraints, where 
    // ``
    //    S - 1 = Floor[
    //          (ConstraintF::CAPACITY - 2 - surfeit  - len(num_limbs)) / bits_per_limb
    //          ] - 2.
    // ``
    pub fn reduce<CS: ConstraintSystemAbstract<ConstraintF>>(
        &self,
        mut cs: CS,
    ) -> Result<NonNativeFieldGadget<SimulationF, ConstraintF>, SynthesisError> {
        // This is just paraphrasing the reduction of non-natives. We enforce the large integer 
        // equality
        // ``
        //    Sum_{i=0..} limb[i] * A^i = k * p + r,
        // ``
        // where `0 <= r < 2^len(p)` and `k >= 0`, by means of `group_and_check_equality()`. 
        // As the left hand side is length bounded by
        // ``
        //   Sum_{i=0..} limb[i] * A^i < (num_adds + 1) * 2^{2*len(p)}
        // ``
        // the quotient `k` is length bounded by
        // ``
        //      len(k) <= len(p) + len(num_adds + 1). 
        // `` 
        let params = get_params(SimulationF::size_in_bits(), ConstraintF::size_in_bits());

        // Note: To assure that the limb-wise computation of the `k * p + r` does not 
        // exceed the capacity bound, we demand 
        // ``
        //     2 * bits_per_limb + surfeit + len(num_limbs) <= CAPACITY.
        // ``
        // However, as the final `group_and_check_equality()` panics iff
        // ``
        //     2 * bits_per_limb + surfeit + len(num_limbs) > CAPACITY - 2.
        // ``
        // there is no need to throw an error here.
    
        // Step 1: get p
        let p_representations =
            NonNativeFieldGadget::<SimulationF, ConstraintF>::get_limbs_representations_from_big_integer(
                &<SimulationF as PrimeField>::Params::MODULUS,
            )?;
        let p_bigint = limbs_to_bigint(params.bits_per_limb, &p_representations);

        let mut p_gadget_limbs = Vec::new();
        for (i, limb) in p_representations.iter().enumerate() {
            p_gadget_limbs.push(FpGadget::<ConstraintF>::from_value(
                cs.ns(|| format!("hardcode limb {}", i)),
                limb,
            ));
        }
        let p_gadget = NonNativeFieldGadget::<SimulationF, ConstraintF> {
            limbs: p_gadget_limbs,
            num_of_additions_over_normal_form: ConstraintF::zero(),
            is_in_the_normal_form: true,
            simulation_phantom: PhantomData,
        };

        // Step 2: compute surfeit
        let surfeit = bitlen!(self.num_add_over_normal_form + ConstraintF::one());

        // Step 3: allocate k,
        // Costs `C = len(p) + surfeit` constraints.
        let k_bits = {
            let mut res = Vec::new();

            let mut limbs_values = Vec::<ConstraintF>::new();
            for limb in self.limbs.iter() {
                limbs_values.push(limb.get_value().unwrap_or_default());
            }

            let value_bigint = limbs_to_bigint(params.bits_per_limb, &limbs_values);
            let mut k_cur = value_bigint / p_bigint; // drops the remainder

            // The total length of k
            // TODO: The length is oversized. Drop the + 1 here.
            let total_len = SimulationF::size_in_bits() + surfeit + 1;

            for i in 0..total_len {
                res.push(Boolean::alloc(
                    cs.ns(|| format!("alloc k bit {}", i)),
                    || Ok(&k_cur % 2u64 == BigUint::from(1u64)),
                )?);
                k_cur /= 2u64; // drops the remainder
            }
            res
        };

        // We define the non-native gadget of `k` by using exactly `num_limbs`
        // limbs, having all limbs except the most significant one in normal form.
        let k_limbs = {
            let zero = FpGadget::zero(cs.ns(|| "hardcode zero for k_limbs"))?;
            let mut limbs = Vec::new();

            let mut k_bits_cur = k_bits.clone();

            for i in 0..params.num_limbs {
                let this_limb_size = if i != params.num_limbs - 1 {
                    params.bits_per_limb
                } else {
                    // The most significant limb is oversized by 
                    // `surfeit = len(num_adds + 1)`
                    k_bits.len() - (params.num_limbs - 1) * params.bits_per_limb
                };

                let this_limb_bits = k_bits_cur[0..this_limb_size].to_vec();
                k_bits_cur = k_bits_cur[this_limb_size..].to_vec();

                let mut limb = zero.clone();
                let mut cur = ConstraintF::one();

                for (j, bit) in this_limb_bits.iter().enumerate() {
                    limb = limb.conditionally_add_constant(
                        cs.ns(|| format!("add bit {} for limb {}", j, i)),
                        bit,
                        cur,
                    )?;
                    cur.double_in_place();
                }
                limbs.push(limb);
            }

            limbs.reverse();
            limbs
        };

        // TODO: let us remove the declaration of `num_adds` as it is not used 
        // anyway.
        let k_gadget = NonNativeFieldGadget::<SimulationF, ConstraintF> {
            limbs: k_limbs,
            num_of_additions_over_normal_form: self.num_add_over_normal_form,
            is_in_the_normal_form: false,
            simulation_phantom: PhantomData,
        };

        // alloc r in normal form. 
        // Costs `C = len(p)` constraints.
        let r_gadget =
            NonNativeFieldGadget::<SimulationF, ConstraintF>::alloc(cs.ns(|| "alloc r"), || {
                self.value()
            })?;

        // Compute the product representation for `k*p`
        // Costs `C =  num_limbs^2` constraintss.
        let mut prod_limbs = Vec::new();
        let zero = FpGadget::<ConstraintF>::zero(cs.ns(|| "hardcode zero for step 1"))?;

        for _ in 0..2 * params.num_limbs - 1 {
            prod_limbs.push(zero.clone());
        }

        for i in 0..params.num_limbs {
            for j in 0..params.num_limbs {
                let mul_result = p_gadget.limbs[i].mul(
                    cs.ns(|| format!("mul_result = p_gadget.limbs[{}] * k_gadget.limbs[{}]", i, j)),
                    &k_gadget.limbs[j],
                )?;
                prod_limbs[i + j] = prod_limbs[i + j].add(
                    cs.ns(|| {
                        format!(
                            "prod_limbs[{},{}] = prod_limbs[{},{}] + mul_result",
                            i, j, i, j
                        )
                    }),
                    &mul_result,
                )?;
            }
        }

        // Compute the limbs of `k * p + r`. Does not cost any constraint.
        // TODO: Let us remove the `num_adds` declaration, as it is not used anyway.
        // The surfeit for the limbs of `k*p + r` is bounded by
        // ``
        //      surfeit(kp + r) <= len(num_limbs) + surfeit(k)
        //                  = len(num_limbs) + len(num_adds + 1)
        // ``
        let mut kp_plus_r_gadget = Self {
            limbs: prod_limbs,
            num_add_over_normal_form: ConstraintF::from(params.num_limbs as u64) 
                * (p_gadget.num_of_additions_over_normal_form + ConstraintF::one())
                * (k_gadget.num_of_additions_over_normal_form + ConstraintF::one()) 
                + ConstraintF::one(),
            simulation_phantom: PhantomData,
        };
        let surfeit_kp_plus_r = bitlen!(kp_plus_r_gadget.num_add_over_normal_form + ConstraintF::one());

        let kp_plus_r_limbs_len = kp_plus_r_gadget.limbs.len();
        for (i, limb) in r_gadget.limbs.iter().rev().enumerate() {
            kp_plus_r_gadget.limbs[kp_plus_r_limbs_len - 1 - i].add_in_place(
                cs.ns(|| {
                    format!(
                        "kp_plus_r_gadget.limbs[{}] + r_gadget.limbs_rev[{}]",
                        kp_plus_r_limbs_len - 1 - i,
                        i
                    )
                }),
                limb,
            )?;
        }

        // Assumes that 
        // ``
        //     2 * bits_per_limb + surfeit + len(num_limbs) <= CAPACITY - 2.
        // ``
        // Costs
        // ``
        //      (S-1) * (1 + 2*bits_per_limb + surfeit + len(num_limbs) + 2 - bits_per_limb) + 1
        // ``
        // constraints, with
        // ``
        //  S - 1 = Floor[
        //          (ConstraintF::CAPACITY - 2 - (2 * bits_per_limb + surfeit  + len(num_limbs)) / bits_per_limb
        //      ] 
        //        = Floor[
        //          (ConstraintF::CAPACITY - 2 - (surfeit  + len(num_limbs)) / bits_per_limb
        //      ] - 2.
        // ``
        Reducer::<SimulationF, ConstraintF>::group_and_check_equality(
            cs.ns(|| "group and check equality"),
            // TODO: let us simply put `len(num_limbs) + surfeit`.
            max(surfeit, surfeit_kp_plus_r),
            // bits_per_limb
            2 * params.bits_per_limb,
            // shift_per_limb
            params.bits_per_limb,
            &self.limbs,
            &kp_plus_r_gadget.limbs,
        )?;

        Ok(r_gadget)
    }

    /// Add unreduced elements.
    pub fn add<CS: ConstraintSystemAbstract<ConstraintF>>(
        &self,
        mut cs: CS,
        other: &Self,
    ) -> Result<Self, SynthesisError> {
        let mut new_limbs = Vec::new();

        for (i, (l1, l2)) in self.limbs.iter().zip(other.limbs.iter()).enumerate() {
            let new_limb = l1.add(cs.ns(|| format!("l1_{} + l2_{}", i, i)), l2)?;
            new_limbs.push(new_limb);
        }

        Ok(Self {
            limbs: new_limbs,
            num_add_over_normal_form: self.num_add_over_normal_form
                + other.num_add_over_normal_form,
            simulation_phantom: PhantomData,
        })
    }

    /// Add native constant elem
    pub fn add_constant<CS: ConstraintSystemAbstract<ConstraintF>>(
        &self,
        mut cs: CS,
        other: &SimulationF,
    ) -> Result<Self, SynthesisError> {
        let mut other_limbs =
            NonNativeFieldGadget::<SimulationF, ConstraintF>::get_limbs_representations(other)?;
        other_limbs.reverse();

        let mut new_limbs = Vec::new();

        for (i, limb) in self.limbs.iter().rev().enumerate() {
            if i < other_limbs.len() {
                let new_limb = limb.add_constant(
                    cs.ns(|| format!("limb_{} + other_limb_{}", i, i)),
                    &other_limbs[i],
                )?;
                new_limbs.push(new_limb);
            } else {
                new_limbs.push((*limb).clone());
            }
        }

        new_limbs.reverse();

        Ok(Self {
            limbs: new_limbs,
            num_add_over_normal_form: self.num_add_over_normal_form + ConstraintF::one(),
            simulation_phantom: PhantomData,
        })
    }
}
