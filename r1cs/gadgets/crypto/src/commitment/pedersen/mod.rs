use algebra::{to_bytes, Group, ToBytes};
use primitives::{
    commitment::pedersen::{PedersenCommitment, PedersenParameters, PedersenRandomness},
    crh::pedersen::PedersenWindow,
};
use r1cs_core::{ConstraintSystemAbstract, SynthesisError};

use crate::commitment::CommitmentGadget;
use algebra::fields::{Field, PrimeField};
use r1cs_std::prelude::*;
use std::{borrow::Borrow, marker::PhantomData};

#[derive(Derivative)]
#[derivative(Clone(bound = "G: Group, W: PedersenWindow, ConstraintF: Field"))]
pub struct PedersenCommitmentGadgetParameters<G: Group, W: PedersenWindow, ConstraintF: Field> {
    params: PedersenParameters<G>,
    #[doc(hidden)]
    _group: PhantomData<G>,
    #[doc(hidden)]
    _engine: PhantomData<ConstraintF>,
    #[doc(hidden)]
    _window: PhantomData<W>,
}

#[derive(Clone, Debug)]
pub struct PedersenRandomnessGadget(Vec<UInt8>);

pub struct PedersenCommitmentGadget<G: Group, ConstraintF: Field, GG: GroupGadget<G, ConstraintF>>(
    #[doc(hidden)] PhantomData<*const G>,
    #[doc(hidden)] PhantomData<*const GG>,
    PhantomData<ConstraintF>,
);

impl<ConstraintF, G, GG, W> CommitmentGadget<PedersenCommitment<G, W>, ConstraintF>
    for PedersenCommitmentGadget<G, ConstraintF, GG>
where
    ConstraintF: PrimeField,
    G: Group,
    GG: GroupGadget<G, ConstraintF>,
    W: PedersenWindow,
{
    type OutputGadget = GG;
    type ParametersGadget = PedersenCommitmentGadgetParameters<G, W, ConstraintF>;
    type RandomnessGadget = PedersenRandomnessGadget;

    fn check_commitment_gadget<CS: ConstraintSystemAbstract<ConstraintF>>(
        mut cs: CS,
        parameters: &Self::ParametersGadget,
        input: &[UInt8],
        r: &Self::RandomnessGadget,
    ) -> Result<Self::OutputGadget, SynthesisError> {
        if (input.len() * 8) > (W::WINDOW_SIZE * W::NUM_WINDOWS) {
            return Err(SynthesisError::Other(format!(
                "incorrect input length: {:?}",
                input.len()
            )));
        }

        let mut padded_input = input.to_vec();
        // Pad if input length is less than `W::WINDOW_SIZE * W::NUM_WINDOWS`.
        if (input.len() * 8) < W::WINDOW_SIZE * W::NUM_WINDOWS {
            let current_length = input.len();
            for _ in current_length..((W::WINDOW_SIZE * W::NUM_WINDOWS) / 8) {
                padded_input.push(UInt8::constant(0u8));
            }
        }

        if padded_input.len() * 8 != W::WINDOW_SIZE * W::NUM_WINDOWS {
            return Err(SynthesisError::Other(
                "padded input length verification failed".to_owned(),
            ));
        }
        if parameters.params.generators.len() != W::NUM_WINDOWS {
            return Err(SynthesisError::Other(format!(
                "Number of generators: {} not enough for the selected num_windows: {}",
                parameters.params.generators.len(),
                W::NUM_WINDOWS
            )));
        }

        // Allocate new variable for commitment output.
        let input_in_bits: Vec<_> = padded_input
            .iter()
            .flat_map(|byte| byte.into_bits_le())
            .collect();
        let input_in_bits = input_in_bits.chunks(W::WINDOW_SIZE);
        let mut result = GG::precomputed_base_multiscalar_mul(
            cs.ns(|| "multiexp"),
            &parameters.params.generators,
            input_in_bits,
        )?;

        // Compute h^r
        let rand_bits: Vec<_> = r.0.iter().flat_map(|byte| byte.into_bits_le()).collect();
        result.precomputed_base_scalar_mul(
            cs.ns(|| "Randomizer"),
            rand_bits
                .iter()
                .zip(&parameters.params.randomness_generator),
        )?;

        Ok(result)
    }
}

impl<G, W, ConstraintF> AllocGadget<PedersenParameters<G>, ConstraintF>
    for PedersenCommitmentGadgetParameters<G, W, ConstraintF>
where
    G: Group,
    W: PedersenWindow,
    ConstraintF: PrimeField,
{
    fn alloc<F, T, CS: ConstraintSystemAbstract<ConstraintF>>(
        _cs: CS,
        value_gen: F,
    ) -> Result<Self, SynthesisError>
    where
        F: FnOnce() -> Result<T, SynthesisError>,
        T: Borrow<PedersenParameters<G>>,
    {
        let temp = value_gen()?;
        let parameters = temp.borrow().clone();

        Ok(PedersenCommitmentGadgetParameters {
            params: parameters,
            _group: PhantomData,
            _engine: PhantomData,
            _window: PhantomData,
        })
    }

    fn alloc_input<F, T, CS: ConstraintSystemAbstract<ConstraintF>>(
        _cs: CS,
        value_gen: F,
    ) -> Result<Self, SynthesisError>
    where
        F: FnOnce() -> Result<T, SynthesisError>,
        T: Borrow<PedersenParameters<G>>,
    {
        let temp = value_gen()?;
        let parameters = temp.borrow().clone();

        Ok(PedersenCommitmentGadgetParameters {
            params: parameters,
            _group: PhantomData,
            _engine: PhantomData,
            _window: PhantomData,
        })
    }
}

impl<G, ConstraintF> AllocGadget<PedersenRandomness<G>, ConstraintF> for PedersenRandomnessGadget
where
    G: Group,
    ConstraintF: PrimeField,
{
    fn alloc<F, T, CS: ConstraintSystemAbstract<ConstraintF>>(
        cs: CS,
        value_gen: F,
    ) -> Result<Self, SynthesisError>
    where
        F: FnOnce() -> Result<T, SynthesisError>,
        T: Borrow<PedersenRandomness<G>>,
    {
        let temp = value_gen()?;
        let randomness = to_bytes![temp.borrow().0].unwrap();
        Ok(PedersenRandomnessGadget(UInt8::alloc_vec(cs, &randomness)?))
    }

    fn alloc_input<F, T, CS: ConstraintSystemAbstract<ConstraintF>>(
        cs: CS,
        value_gen: F,
    ) -> Result<Self, SynthesisError>
    where
        F: FnOnce() -> Result<T, SynthesisError>,
        T: Borrow<PedersenRandomness<G>>,
    {
        let temp = value_gen()?;
        let randomness = to_bytes![temp.borrow().0].unwrap();
        Ok(PedersenRandomnessGadget(UInt8::alloc_input_vec(
            cs,
            &randomness,
        )?))
    }
}

#[cfg(test)]
mod test {
    use crate::commitment::{pedersen::PedersenCommitmentGadget, CommitmentGadget};
    use algebra::curves::{jubjub::JubJubProjective as JubJub, ProjectiveCurve};
    use algebra::{
        fields::jubjub::{fq::Fq, fr::Fr},
        UniformRand,
    };
    use primitives::{
        commitment::{
            pedersen::{PedersenCommitment, PedersenRandomness},
            CommitmentScheme,
        },
        crh::pedersen::PedersenWindow,
    };
    use r1cs_core::{
        ConstraintSystem, ConstraintSystemAbstract, ConstraintSystemDebugger, SynthesisMode,
    };
    use r1cs_std::{instantiated::jubjub::JubJubGadget, prelude::*};
    use rand::thread_rng;

    #[test]
    fn commitment_gadget_test() {
        let mut cs = ConstraintSystem::<Fq>::new(SynthesisMode::Debug);

        #[derive(Clone, PartialEq, Eq, Hash)]
        pub(super) struct Window;

        impl PedersenWindow for Window {
            const WINDOW_SIZE: usize = 4;
            const NUM_WINDOWS: usize = 8;
        }

        let input = [1u8; 4];

        let rng = &mut thread_rng();

        type TestCOMM = PedersenCommitment<JubJub, Window>;
        type TestCOMMGadget = PedersenCommitmentGadget<JubJub, Fq, JubJubGadget>;

        let randomness = PedersenRandomness(Fr::rand(rng));

        let parameters = PedersenCommitment::<JubJub, Window>::setup(rng).unwrap();
        let primitive_result =
            PedersenCommitment::<JubJub, Window>::commit(&parameters, &input, &randomness).unwrap();

        let input_bytes =
            UInt8::alloc_input_vec(cs.ns(|| "alloc input bytes as public input"), &input).unwrap();

        let randomness =
            <TestCOMMGadget as CommitmentGadget<TestCOMM, Fq>>::RandomnessGadget::alloc_input(
                &mut cs.ns(|| "gadget_randomness"),
                || Ok(&randomness),
            )
            .unwrap();
        let gadget_parameters =
            <TestCOMMGadget as CommitmentGadget<TestCOMM, Fq>>::ParametersGadget::alloc(
                &mut cs.ns(|| "gadget_parameters"),
                || Ok(&parameters),
            )
            .unwrap();
        let gadget_result =
            <TestCOMMGadget as CommitmentGadget<TestCOMM, Fq>>::check_commitment_gadget(
                &mut cs.ns(|| "gadget_evaluation"),
                &gadget_parameters,
                &input_bytes,
                &randomness,
            )
            .unwrap();

        let primitive_result = primitive_result.into_affine();
        assert_eq!(primitive_result.x, gadget_result.x.value.unwrap());
        assert_eq!(primitive_result.y, gadget_result.y.value.unwrap());
        assert!(cs.is_satisfied());
    }
}
