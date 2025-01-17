use algebra::Field;
use std::fmt::Debug;

use primitives::crh::{FieldBasedHash, FixedLengthCRH};
use r1cs_core::{ConstraintSystemAbstract, SynthesisError};

use r1cs_std::prelude::*;

pub mod bowe_hopwood;
pub mod injective_map;
pub mod pedersen;

pub mod sbox;
pub use self::sbox::*;

pub mod poseidon;
pub use self::poseidon::*;

pub trait FixedLengthCRHGadget<H: FixedLengthCRH, ConstraintF: Field>: Sized {
    type OutputGadget: EqGadget<ConstraintF>
        + ToBytesGadget<ConstraintF>
        + CondSelectGadget<ConstraintF>
        + AllocGadget<H::Output, ConstraintF>
        + Debug
        + Clone
        + Sized;
    type ParametersGadget: AllocGadget<H::Parameters, ConstraintF> + Clone;

    fn check_evaluation_gadget<CS: ConstraintSystemAbstract<ConstraintF>>(
        cs: CS,
        parameters: &Self::ParametersGadget,
        input: &[UInt8],
    ) -> Result<Self::OutputGadget, SynthesisError>;
}

pub trait FieldBasedHashGadget<H: FieldBasedHash<Data = ConstraintF>, ConstraintF: Field>:
    Sized
{
    type DataGadget: FieldGadget<ConstraintF, ConstraintF>;

    fn enforce_hash_constant_length<CS: ConstraintSystemAbstract<ConstraintF>>(
        cs: CS,
        input: &[Self::DataGadget],
    ) -> Result<Self::DataGadget, SynthesisError>;
}

pub trait FieldHasherGadget<
    H: FieldBasedHash<Data = ConstraintF>,
    ConstraintF: Field,
    HG: FieldBasedHashGadget<H, ConstraintF>,
>
{
    fn enforce_hash<CS: ConstraintSystemAbstract<ConstraintF>>(
        &self,
        cs: CS,
        personalization: Option<&[HG::DataGadget]>,
    ) -> Result<HG::DataGadget, SynthesisError>;
}

#[cfg(test)]
mod test {
    use crate::FieldBasedHashGadget;
    use algebra::PrimeField;
    use primitives::FieldBasedHash;
    use r1cs_core::{
        ConstraintSystem, ConstraintSystemAbstract, ConstraintSystemDebugger, SynthesisMode,
    };
    use r1cs_std::{alloc::AllocGadget, fields::fp::FpGadget};

    pub(crate) fn constant_length_field_based_hash_gadget_native_test<
        F: PrimeField,
        H: FieldBasedHash<Data = F>,
        HG: FieldBasedHashGadget<H, F, DataGadget = FpGadget<F>>,
    >(
        inputs: Vec<F>,
    ) {
        let mut cs = ConstraintSystem::<F>::new(SynthesisMode::Debug);

        let primitive_result = {
            let mut digest = H::init_constant_length(inputs.len(), None);
            inputs.iter().for_each(|elem| {
                digest.update(*elem);
            });
            digest.finalize().unwrap()
        };

        let mut input_gadgets = Vec::with_capacity(inputs.len());
        inputs.into_iter().enumerate().for_each(|(i, elem)| {
            let elem_gadget =
                HG::DataGadget::alloc(cs.ns(|| format!("alloc input {}", i)), || Ok(elem)).unwrap();
            input_gadgets.push(elem_gadget);
        });

        let gadget_result = HG::enforce_hash_constant_length(
            cs.ns(|| "check_poseidon_gadget"),
            input_gadgets.as_slice(),
        )
        .unwrap();

        assert_eq!(primitive_result, gadget_result.value.unwrap());

        if !cs.is_satisfied() {
            println!("{:?}", cs.which_is_unsatisfied());
        }
        assert!(cs.is_satisfied());
    }
}
