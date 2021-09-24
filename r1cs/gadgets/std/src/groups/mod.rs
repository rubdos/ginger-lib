use crate::prelude::*;
use algebra::{Field, PrimeField, Group};
use r1cs_core::{ConstraintSystem, SynthesisError};

use std::{borrow::Borrow, fmt::Debug};

pub mod curves;

pub use self::curves::short_weierstrass::{bls12, bn, mnt};

#[cfg(feature = "nonnative")]
pub mod nonnative;

pub trait GroupGadget<G: Group, ConstraintF: Field>:
    Sized
    + ToBytesGadget<ConstraintF>
    + EqGadget<ConstraintF>
    + ToBitsGadget<ConstraintF>
    + CondSelectGadget<ConstraintF>
    + AllocGadget<G, ConstraintF>
    + ConstantGadget<G, ConstraintF>
    + Clone
    + Debug
{
    type Value: Debug;
    type Variable;

    fn get_value(&self) -> Option<Self::Value>;

    fn get_variable(&self) -> Self::Variable;

    fn zero<CS: ConstraintSystem<ConstraintF>>(cs: CS) -> Result<Self, SynthesisError>;

    fn is_zero<CS: ConstraintSystem<ConstraintF>>(&self, cs: CS) -> Result<Boolean, SynthesisError>;

    fn add<CS: ConstraintSystem<ConstraintF>>(
        &self,
        cs: CS,
        other: &Self,
    ) -> Result<Self, SynthesisError>;

    fn sub<CS: ConstraintSystem<ConstraintF>>(
        &self,
        mut cs: CS,
        other: &Self,
    ) -> Result<Self, SynthesisError> {
        let neg_other = other.negate(cs.ns(|| "Negate other"))?;
        self.add(cs.ns(|| "Self - other"), &neg_other)
    }

    fn add_constant<CS: ConstraintSystem<ConstraintF>>(
        &self,
        cs: CS,
        other: &G,
    ) -> Result<Self, SynthesisError>;

    fn sub_constant<CS: ConstraintSystem<ConstraintF>>(
        &self,
        mut cs: CS,
        other: &G,
    ) -> Result<Self, SynthesisError> {
        let neg_other = -(*other);
        self.add_constant(cs.ns(|| "Self - other"), &neg_other)
    }

    fn double_in_place<CS: ConstraintSystem<ConstraintF>>(
        &mut self,
        cs: CS,
    ) -> Result<(), SynthesisError>;

    fn negate<CS: ConstraintSystem<ConstraintF>>(&self, cs: CS) -> Result<Self, SynthesisError>;

    /// Variable base exponentiation.
    /// Inputs must be specified in *little-endian* form.
    /// If the addition law is incomplete for the identity element,
    /// `result` must not be the identity element.
    fn mul_bits<'a, CS: ConstraintSystem<ConstraintF>>(
        &self,
        mut cs: CS,
        bits: impl Iterator<Item = &'a Boolean>,
    ) -> Result<Self, SynthesisError> {
        let mut power = self.clone();
        let mut acc = Self::zero(cs.ns(|| "alloc acc"))?;
        for (i, bit) in bits.enumerate() {
            let new_encoded = acc.add(&mut cs.ns(|| format!("Add {}-th power", i)), &power)?;
            acc = Self::conditionally_select(
                &mut cs.ns(|| format!("Select {}", i)),
                bit.borrow(),
                &new_encoded,
                &acc,
            )?;
            power.double_in_place(&mut cs.ns(|| format!("{}-th Doubling", i)))?;
        }
        Ok(acc)
    }

    fn precomputed_base_scalar_mul<'a, CS, I, B>(
        &mut self,
        mut cs: CS,
        scalar_bits_with_base_powers: I,
    ) -> Result<(), SynthesisError>
    where
        CS: ConstraintSystem<ConstraintF>,
        I: Iterator<Item = (B, &'a G)>,
        B: Borrow<Boolean>,
        G: 'a,
    {
        for (i, (bit, base_power)) in scalar_bits_with_base_powers.enumerate() {
            let new_encoded = self.add_constant(
                &mut cs.ns(|| format!("Add {}-th base power", i)),
                &base_power,
            )?;
            *self = Self::conditionally_select(
                &mut cs.ns(|| format!("Conditional Select {}", i)),
                bit.borrow(),
                &new_encoded,
                &self,
            )?;
        }
        Ok(())
    }

    /// Fixed base exponentiation, slighlty different interface from
    /// `precomputed_base_scalar_mul`. Inputs must be specified in
    /// *little-endian* form. If the addition law is incomplete for
    /// the identity element, `result` must not be the identity element.
    fn mul_bits_fixed_base<CS: ConstraintSystem<ConstraintF>>(
        base: &G,
        mut cs: CS,
        bits: &[Boolean],
    ) -> Result<Self, SynthesisError> {
        let base_g = Self::from_value(cs.ns(|| "hardcode base"), base);
        base_g.mul_bits(cs, bits.into_iter())
    }

    fn precomputed_base_3_bit_signed_digit_scalar_mul<'a, CS, I, J, B>(
        _: CS,
        _: &[B],
        _: &[J],
    ) -> Result<Self, SynthesisError>
    where
        CS: ConstraintSystem<ConstraintF>,
        I: Borrow<[Boolean]>,
        J: Borrow<[I]>,
        B: Borrow<[G]>,
    {
        Err(SynthesisError::AssignmentMissing)
    }

    fn precomputed_base_multiscalar_mul<'a, CS, T, I, B>(
        mut cs: CS,
        bases: &[B],
        scalars: I,
    ) -> Result<Self, SynthesisError>
    where
        CS: ConstraintSystem<ConstraintF>,
        T: 'a + ToBitsGadget<ConstraintF> + ?Sized,
        I: Iterator<Item = &'a T>,
        B: Borrow<[G]>,
    {
        let mut result = Self::zero(&mut cs.ns(|| "Declare Result"))?;
        // Compute ∏(h_i^{m_i}) for all i.
        for (i, (bits, base_powers)) in scalars.zip(bases).enumerate() {
            let base_powers = base_powers.borrow();
            let bits = bits.to_bits(&mut cs.ns(|| format!("Convert Scalar {} to bits", i)))?;
            result.precomputed_base_scalar_mul(
                cs.ns(|| format!("Chunk {}", i)),
                bits.iter().zip(base_powers),
            )?;
        }
        Ok(result)
    }

    fn cost_of_add() -> usize;

    fn cost_of_double() -> usize;
}

/// The 'constant' length transformation for scalar multiplication of a group
/// with scalar field `ScalarF`. 
/// Implements the non-native big integer addition of the scalar, given as 
/// little endian vector of BooleanGadgets `bits`, with `MODULUS` the modulus
/// of the scalar field. The result is a vector of Booleans always one bit longer
/// than `MODULUS`, possibly having a leading zero.
pub(crate) fn scalar_bits_to_constant_length<
    'a,
    ConstraintF: PrimeField,
    ScalarF: PrimeField,
    CS: ConstraintSystem<ConstraintF>
>(
    mut cs: CS,
    bits: Vec<Boolean>
) -> Result<Vec<Boolean>, SynthesisError>
{
    use crate::fields::nonnative::{
        NonNativeFieldParams, nonnative_field_gadget::NonNativeFieldGadget,
    };
    use algebra::FpParameters;

    assert!(bits.len() <= ScalarF::size_in_bits());

    // We 'misuse' the conversion algorithms of NonNativeFieldGadget in order 
    // to convert BigInteger/bits to limbs.
    // TODO: Refactor code so that we do not have explicit calls to NonNativeGadgets
    let params = {
        // bits per limb is the remainder of len mod max_
        let bits_per_limb =  std::cmp::min((ConstraintF::Params::CAPACITY - 1) as usize, ScalarF::size_in_bits());
        // ceil(ScalarF::size_in_bits()/bits_per_limb)
        let num_limbs = (ScalarF::size_in_bits() + bits_per_limb - 1)/bits_per_limb;

        // println!("Capacity {}", ConstraintF::Params::CAPACITY as usize);
        // println!("Scalar field size {}", ScalarF::size_in_bits());
        // println!("bits_per_limb {}", bits_per_limb);
        // println!("num_limbs {}", num_limbs);

        NonNativeFieldParams{ num_limbs, bits_per_limb }
    };

    // Convert the scalar field modulus `MODULUS` to its limbs.
    let mut scalar_char_limbs = NonNativeFieldGadget::<
        ScalarF, ConstraintF>::get_limbs_representations_from_big_integer_with_params(
        params, &<ScalarF as PrimeField>::Params::MODULUS
    )?;
    scalar_char_limbs.reverse(); // Convert to LE limbs order

    // Pack `bits` into its limbs.
    // TODO: when refactored, we will merge the constraints from `from_bits_with_params`
    // into the linear combinations for the limb-wise sum
    let mut bits_bigendian = bits;
    bits_bigendian.reverse();
    let mut scalar_limbs = NonNativeFieldGadget::<ScalarF, ConstraintF>::from_bits_with_params(
        cs.ns(|| "scalar from bits"),
        bits_bigendian.as_slice(),  // from_bits takes big endian representation
        params
    )?.limbs;
    scalar_limbs.reverse(); // Convert to LE limbs order

    // We compute the sum over the limbs taking carries into account
    let mut sum_limbs_bits: Vec<Boolean> = Vec::with_capacity(ScalarF::size_in_bits() + 1); // LE
    let mut carry_bit = Boolean::Constant(false);
    let mut to_be_processed = ScalarF::size_in_bits();
    let mut used_in_limb: usize;

    for (i, (scalar_limb, scalar_char_limb)) in scalar_limbs
        .into_iter()
        .zip(scalar_char_limbs.into_iter())
        .enumerate()
        {
            
            if to_be_processed < params.bits_per_limb{
                used_in_limb = to_be_processed;            
            } else {
                used_in_limb = params.bits_per_limb;
            }
            
            // add the limb of the scalar with that of `MODULUS`
            let mut sum_limb = scalar_limb.add_constant(
                cs.ns(|| format!("scalar_limb + scalar_char_limb {}", i)),
                &scalar_char_limb
            )?;

            println!("scalar limb {}: {}",i,scalar_limb.get_value().unwrap());
            println!("modul. limb {}: {}",i,scalar_char_limb);
            println!("sum limb {}: {}",i,sum_limb.get_value().unwrap());

            // add the previous carry to the limb
            sum_limb = sum_limb.conditionally_add_constant(
                cs.ns(|| format!("add carry {}", i)),
                &carry_bit,
                ConstraintF::one(),
            )?;
            

            // unpack `sum_limb` into its `used_in_limb + 1` many bits. 
            let to_skip = <ConstraintF::BasePrimeField as PrimeField>::size_in_bits() - (used_in_limb + 1);
            let mut sum_limb_bits = sum_limb.to_bits_with_length_restriction(
                cs.ns(|| format!("sum_limb to_bits_with_length_restriction {}", i)),
                to_skip
            )?;
            sum_limb_bits.reverse();
            // The leading bit is the carry for the next significant limb
            carry_bit = sum_limb_bits.pop().unwrap();

            sum_limbs_bits.append(&mut sum_limb_bits);
            to_be_processed -= used_in_limb;
        }

    assert_eq!(to_be_processed, 0, "not all bits processed");
    
    // The last carry is part of the result.
    sum_limbs_bits.push(carry_bit);
    Ok(sum_limbs_bits)
}

#[cfg(test)]
pub(crate) mod test {
    use algebra::{Field, PrimeField, FpParameters, BigInteger, Group, UniformRand, ToBits};
    use r1cs_core::ConstraintSystem;

    use crate::{prelude::*, test_constraint_system::TestConstraintSystem};
    use rand::thread_rng;

    #[allow(dead_code)]
    pub(crate) fn group_test<
        ConstraintF: Field,
        G: Group,
        GG: GroupGadget<G, ConstraintF, Value = G>,
    >()
    {
        let mut cs = TestConstraintSystem::<ConstraintF>::new();

        let a: G = UniformRand::rand(&mut thread_rng());
        let b: G = UniformRand::rand(&mut thread_rng());

        let a = GG::alloc(&mut cs.ns(|| "generate_a"), || Ok(a)).unwrap();
        let b = GG::alloc(&mut cs.ns(|| "generate_b"), || Ok(b)).unwrap();

        let zero = GG::zero(cs.ns(|| "Zero")).unwrap();
        assert_eq!(zero, zero);

        // a == a
        assert_eq!(a, a);

        // a + 0 = a
        assert_eq!(a.add(cs.ns(|| "a_plus_zero"), &zero).unwrap(), a);
        // a - 0 = a
        assert_eq!(a.sub(cs.ns(|| "a_minus_zero"), &zero).unwrap(), a);
        // a - a = 0
        assert_eq!(a.sub(cs.ns(|| "a_minus_a"), &a).unwrap(), zero);

        // a + b = b + a
        let a_b = a.add(cs.ns(|| "a_plus_b"), &b).unwrap();
        let b_a = b.add(cs.ns(|| "b_plus_a"), &a).unwrap();
        assert_eq!(a_b, b_a);
        // (a + b) + a = a + (b + a)
        let ab_a = a_b.add(&mut cs.ns(|| "a_b_plus_a"), &a).unwrap();
        let a_ba = a.add(&mut cs.ns(|| "a_plus_b_a"), &b_a).unwrap();
        assert_eq!(ab_a, a_ba);

        // a.double() = a + a
        let a_a = a.add(cs.ns(|| "a + a"), &a).unwrap();
        let mut a2 = a.clone();
        a2.double_in_place(cs.ns(|| "2a")).unwrap();
        assert_eq!(a2, a_a);
        // b.double() = b + b
        let mut b2 = b.clone();
        b2.double_in_place(cs.ns(|| "2b")).unwrap();
        let b_b = b.add(cs.ns(|| "b + b"), &b).unwrap();
        assert_eq!(b2, b_b);

        let _ = a.to_bytes(&mut cs.ns(|| "ToBytes")).unwrap();
        let _ = a.to_bytes_strict(&mut cs.ns(|| "ToBytes Strict")).unwrap();

        let _ = b.to_bytes(&mut cs.ns(|| "b ToBytes")).unwrap();
        let _ = b
            .to_bytes_strict(&mut cs.ns(|| "b ToBytes Strict"))
            .unwrap();
        assert!(cs.is_satisfied());
    }

    #[allow(dead_code)]
    pub(crate) fn group_test_with_unsafe_add<
        ConstraintF: Field,
        G: Group,
        GG: GroupGadget<G, ConstraintF, Value = G>,
    >()
    {
        let mut cs = TestConstraintSystem::<ConstraintF>::new();

        let a: G = UniformRand::rand(&mut thread_rng());
        let b: G = UniformRand::rand(&mut thread_rng());

        let a = GG::alloc(&mut cs.ns(|| "generate_a"), || Ok(a)).unwrap();
        let b = GG::alloc(&mut cs.ns(|| "generate_b"), || Ok(b)).unwrap();

        let zero = GG::zero(cs.ns(|| "Zero")).unwrap();
        assert_eq!(zero, zero);

        // a == a
        assert_eq!(a, a);

        // a + b = b + a
        let a_b = a.add(cs.ns(|| "a_plus_b"), &b).unwrap();
        let b_a = b.add(cs.ns(|| "b_plus_a"), &a).unwrap();
        assert_eq!(a_b, b_a);

        // (a + b) + a = a + (b + a)
        let ab_a = a_b.add(&mut cs.ns(|| "a_b_plus_a"), &a).unwrap();
        let a_ba = a.add(&mut cs.ns(|| "a_plus_b_a"), &b_a).unwrap();
        assert_eq!(ab_a, a_ba);

        // a.double() + b = (a + b) + a: Testing double() using b as shift
        let mut a2 = a.clone();
        a2.double_in_place(cs.ns(|| "2a")).unwrap();
        let a2_b = a2.add(cs.ns(|| "2a + b"), &b).unwrap();

        let a_b_a = a.add(cs.ns(|| "a + b"), &b).unwrap()
            .add(cs.ns(|| "a + b + a"), &a).unwrap();
        assert_eq!(a2_b, a_b_a);

        // (b.double() + a) = (b + a) + b: Testing double() using a as shift
        let mut b2 = b.clone();
        b2.double_in_place(cs.ns(|| "2b")).unwrap();
        let b2_a = b2.add(cs.ns(|| "2b + a"), &a).unwrap();

        let b_a_b = b.add(cs.ns(|| "b + a"), &a).unwrap()
            .add(cs.ns(|| "b + a + b"), &b).unwrap();
        assert_eq!(b2_a, b_a_b);

        let _ = a.to_bytes(&mut cs.ns(|| "ToBytes")).unwrap();
        let _ = a.to_bytes_strict(&mut cs.ns(|| "ToBytes Strict")).unwrap();

        let _ = b.to_bytes(&mut cs.ns(|| "b ToBytes")).unwrap();
        let _ = b
            .to_bytes_strict(&mut cs.ns(|| "b ToBytes Strict"))
            .unwrap();
        assert!(cs.is_satisfied());
    }

    /// Tests the 'constant' length transformation of `scalar_bits_to_constant_length` against
    /// the result of 'native' big integer arithmetics.
    #[allow(dead_code)]
    fn scalar_bits_to_constant_length_test<
        ConstraintF: PrimeField,
        G: Group,
    >()
    {
        for _ in 0..30 {
            let mut cs = TestConstraintSystem::<ConstraintF>::new();
            let rng = &mut thread_rng();

            let a = G::ScalarField::rand(rng);
            let mut a_bigint = a.into_repr();
            println!("scalar bigint: {}", a_bigint);
            println!("modulus bigint: {}", <G::ScalarField as PrimeField>::Params::MODULUS);
            // the 'native' addition of the scalar a and the scalar field modulus
            let carry = a_bigint.add_nocarry(&<G::ScalarField as PrimeField>::Params::MODULUS);
            println!("sum bigint: {}", a_bigint);
            // add_nocarry should never return a non-zero as the BigInt's are always oversized to
            // prevent this.
            assert_eq!(carry, false, "add_nocarry overflow.");

            // get the bits in little endian order. 
            // Note: `to_bits()` seems not to skip leading zeroes
            let mut native_result = a_bigint.to_bits();
            native_result.reverse();

            // Checking plausability of native sum
            let expected_len = <G::ScalarField as PrimeField>::size_in_bits() + 1;
            assert_eq!(native_result[expected_len..], vec![false; native_result.len() - expected_len], "unexpected large native result");
            assert!(
                native_result[expected_len-1] == true ||
                (native_result[expected_len-1] == false && native_result[expected_len-2] == true),
                "unexpected value of native result"
            );

            // Alloc a vector of Boolean Gadgets with values according to the scalar bits, little endian.
            let mut a_bits_gadget = Vec::<Boolean>::alloc(cs.ns(|| "a bits"), || Ok(a.write_bits())).unwrap();
            a_bits_gadget.reverse();

            // Compute the sum by means of the arithmetic circuit of `scalar_bits_to_constant_length()`
            let gadget_result = crate::groups::scalar_bits_to_constant_length::<_, G::ScalarField, _>(
                cs.ns(|| "a bits to constant length"), a_bits_gadget
            )
                .unwrap()
                .into_iter()
                .map(|b| b.get_value().unwrap())
                .collect::<Vec<bool>>();

            // check equality with the native sum
            assert_eq!(expected_len, gadget_result.len(), "Native and circuit length not equal");
            assert_eq!(native_result[..expected_len], gadget_result, "Native and circuit value not equal");

            assert!(cs.is_satisfied());
        }
    }

    #[allow(dead_code)]
    pub(crate) fn mul_bits_test<
        ConstraintF: Field,
        G: Group,
        GG: GroupGadget<G, ConstraintF, Value = G>,
    >()
    {
        scalar_bits_to_constant_length_test::<<ConstraintF as Field>::BasePrimeField, G>();

        /*use crate::algebra::ToBits;

        for _ in 0..10 {
            let mut cs = TestConstraintSystem::<ConstraintF>::new();
            let rng = &mut thread_rng();

            let g: G = UniformRand::rand(rng);
            let gg = GG::alloc(cs.ns(|| "generate_g"), || Ok(g)).unwrap();

            let a = G::ScalarField::rand(rng);
            let b = G::ScalarField::rand(rng);
            //let ab = a * &b;
            let a_plus_b = a + &b;

            let mut a_bits = Vec::<Boolean>::alloc(cs.ns(|| "a bits"), || Ok(a.write_bits())).unwrap();
            a_bits.reverse();

            let mut b_bits = Vec::<Boolean>::alloc(cs.ns(|| "b bits"), || Ok(b.write_bits())).unwrap();
            b_bits.reverse();

            //let ab_bits = Vec::<Boolean>::alloc(cs.ns(|| "ab bits"), ||Ok(ab.write_bits())).unwrap();
            let mut a_plus_b_bits = Vec::<Boolean>::alloc(cs.ns(|| "a_plus_b bits"), || Ok(a_plus_b.write_bits())).unwrap();
            a_plus_b_bits.reverse();

            // Additivity test: a * G + b * G = (a + b) * G
            let x = cs.num_constraints();
            let a_times_gg_vb = gg.mul_bits(cs.ns(|| "a * G"), a_bits.iter()).unwrap();
            println!("Variable base SM exponent len {}, num_constraints: {}", a_bits.len(), cs.num_constraints() - x);

            let x = cs.num_constraints();
            let a_times_gg_fb = GG::mul_bits_fixed_base(&g, cs.ns(|| "fb a * G"), a_bits.as_slice()).unwrap();
            println!("Fixed base SM exponent len {}, num_constraints: {}", a_bits.len(), cs.num_constraints() - x);
            assert_eq!(a_times_gg_vb.get_value().unwrap(), g.mul(&a)); // Check native result
            assert_eq!(a_times_gg_fb.get_value().unwrap(), g.mul(&a)); // Check native result

            let b_times_gg_vb = gg.mul_bits(cs.ns(|| "b * G"), b_bits.iter()).unwrap();
            let b_times_gg_fb = GG::mul_bits_fixed_base(&g, cs.ns(|| "fb b * G"), b_bits.as_slice()).unwrap();
            assert_eq!(b_times_gg_vb.get_value().unwrap(), g.mul(&b)); // Check native result
            assert_eq!(b_times_gg_fb.get_value().unwrap(), g.mul(&b)); // Check native result

            let a_plus_b_times_gg_vb = gg.mul_bits(cs.ns(|| "(a + b) * G"), a_plus_b_bits.iter()).unwrap();
            let a_plus_b_times_gg_fb = GG::mul_bits_fixed_base(&g, cs.ns(|| "fb (a + b) * G"), a_plus_b_bits.as_slice()).unwrap();
            assert_eq!(a_plus_b_times_gg_vb.get_value().unwrap(), g.mul(&(a + &b))); // Check native result
            assert_eq!(a_plus_b_times_gg_fb.get_value().unwrap(), g.mul(&(a + &b))); // Check native result

            a_times_gg_vb
                .add(cs.ns(|| "a * G + b * G"), &b_times_gg_vb).unwrap()
                .enforce_equal(cs.ns(|| "a * G + b * G = (a + b) * G"), &a_plus_b_times_gg_vb).unwrap();

            a_times_gg_fb
                .add(cs.ns(|| "fb a * G + b * G"), &b_times_gg_fb).unwrap()
                .enforce_equal(cs.ns(|| "fb a * G + b * G = (a + b) * G"), &a_plus_b_times_gg_fb).unwrap();

            assert!(cs.is_satisfied());
        }*/
    }
}