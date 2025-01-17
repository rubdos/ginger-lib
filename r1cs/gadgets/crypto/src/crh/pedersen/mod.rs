use crate::FixedLengthCRHGadget;
use algebra::{Field, Group};
use primitives::crh::pedersen::{PedersenCRH, PedersenParameters, PedersenWindow};
use r1cs_core::{ConstraintSystemAbstract, SynthesisError};
use r1cs_std::prelude::*;
use std::{borrow::Borrow, marker::PhantomData};

#[derive(Derivative)]
#[derivative(Clone(
    bound = "G: Group, W: PedersenWindow, ConstraintF: Field, GG: GroupGadget<G, ConstraintF>"
))]
pub struct PedersenCRHGadgetParameters<
    G: Group,
    W: PedersenWindow,
    ConstraintF: Field,
    GG: GroupGadget<G, ConstraintF>,
> {
    params: PedersenParameters<G>,
    _group_g: PhantomData<GG>,
    _engine: PhantomData<ConstraintF>,
    _window: PhantomData<W>,
}

pub struct PedersenCRHGadget<G: Group, ConstraintF: Field, GG: GroupGadget<G, ConstraintF>> {
    #[doc(hidden)]
    _group: PhantomData<*const G>,
    #[doc(hidden)]
    _group_gadget: PhantomData<*const GG>,
    #[doc(hidden)]
    _engine: PhantomData<ConstraintF>,
}

impl<ConstraintF, G, GG, W> FixedLengthCRHGadget<PedersenCRH<G, W>, ConstraintF>
    for PedersenCRHGadget<G, ConstraintF, GG>
where
    ConstraintF: Field,
    G: Group,
    GG: GroupGadget<G, ConstraintF>,
    W: PedersenWindow,
{
    type OutputGadget = GG;
    type ParametersGadget = PedersenCRHGadgetParameters<G, W, ConstraintF, GG>;

    fn check_evaluation_gadget<CS: ConstraintSystemAbstract<ConstraintF>>(
        cs: CS,
        parameters: &Self::ParametersGadget,
        input: &[UInt8],
    ) -> Result<Self::OutputGadget, SynthesisError> {
        let mut padded_input = input.to_vec();
        // Pad the input if it is not the current length.
        if input.len() * 8 < W::WINDOW_SIZE * W::NUM_WINDOWS {
            let current_length = input.len();
            for _ in current_length..(W::WINDOW_SIZE * W::NUM_WINDOWS / 8) {
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
                "Incorrect pp of size {:?}x{:?} for window params {:?}x{:?}",
                parameters.params.generators[0].len(),
                parameters.params.generators.len(),
                W::WINDOW_SIZE,
                W::NUM_WINDOWS
            )));
        }

        // Allocate new variable for the result.
        let input_in_bits: Vec<_> = padded_input
            .iter()
            .flat_map(|byte| byte.into_bits_le())
            .collect();
        let input_in_bits = input_in_bits.chunks(W::WINDOW_SIZE);
        let result =
            GG::precomputed_base_multiscalar_mul(cs, &parameters.params.generators, input_in_bits)?;

        Ok(result)
    }
}

impl<G: Group, W: PedersenWindow, ConstraintF: Field, GG: GroupGadget<G, ConstraintF>>
    AllocGadget<PedersenParameters<G>, ConstraintF>
    for PedersenCRHGadgetParameters<G, W, ConstraintF, GG>
{
    fn alloc<F, T, CS: ConstraintSystemAbstract<ConstraintF>>(
        _cs: CS,
        value_gen: F,
    ) -> Result<Self, SynthesisError>
    where
        F: FnOnce() -> Result<T, SynthesisError>,
        T: Borrow<PedersenParameters<G>>,
    {
        let params = value_gen()?.borrow().clone();
        Ok(PedersenCRHGadgetParameters {
            params,
            _group_g: PhantomData,
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
        let params = value_gen()?.borrow().clone();
        Ok(PedersenCRHGadgetParameters {
            params,
            _group_g: PhantomData,
            _engine: PhantomData,
            _window: PhantomData,
        })
    }
}

#[cfg(test)]
mod test {
    use algebra::fields::bls12_381::fr::Fr;
    use rand::{thread_rng, Rng};

    use crate::crh::{pedersen::PedersenCRHGadget, FixedLengthCRH, FixedLengthCRHGadget};
    use algebra::curves::{jubjub::JubJubProjective as JubJub, ProjectiveCurve};
    use primitives::crh::pedersen::{PedersenCRH, PedersenWindow};
    use r1cs_core::{
        ConstraintSystem, ConstraintSystemAbstract, ConstraintSystemDebugger, SynthesisMode,
    };
    use r1cs_std::{instantiated::jubjub::JubJubGadget, prelude::*};

    type TestCRH = PedersenCRH<JubJub, Window>;
    type TestCRHGadget = PedersenCRHGadget<JubJub, Fr, JubJubGadget>;

    #[derive(Clone, PartialEq, Eq, Hash)]
    pub(super) struct Window;

    impl PedersenWindow for Window {
        const WINDOW_SIZE: usize = 128;
        const NUM_WINDOWS: usize = 8;
    }

    fn generate_input<CS: ConstraintSystemAbstract<Fr>, R: Rng>(
        mut cs: CS,
        rng: &mut R,
    ) -> ([u8; 128], Vec<UInt8>) {
        let mut input = [1u8; 128];
        rng.fill_bytes(&mut input);

        let mut input_bytes = vec![];
        for (byte_i, input_byte) in input.iter().enumerate() {
            let cs = cs.ns(|| format!("input_byte_gadget_{}", byte_i));
            input_bytes.push(UInt8::alloc(cs, || Ok(*input_byte)).unwrap());
        }
        (input, input_bytes)
    }

    #[test]
    fn crh_primitive_gadget_test() {
        let rng = &mut thread_rng();
        let mut cs = ConstraintSystem::<Fr>::new(SynthesisMode::Debug);

        let (input, input_bytes) = generate_input(&mut cs, rng);
        println!("number of constraints for input: {}", cs.num_constraints());

        let parameters = TestCRH::setup(rng).unwrap();
        let primitive_result = TestCRH::evaluate(&parameters, &input).unwrap();

        let gadget_parameters =
            <TestCRHGadget as FixedLengthCRHGadget<TestCRH, Fr>>::ParametersGadget::alloc(
                &mut cs.ns(|| "gadget_parameters"),
                || Ok(&parameters),
            )
            .unwrap();
        println!(
            "number of constraints for input + params: {}",
            cs.num_constraints()
        );

        let gadget_result =
            <TestCRHGadget as FixedLengthCRHGadget<TestCRH, Fr>>::check_evaluation_gadget(
                &mut cs.ns(|| "gadget_evaluation"),
                &gadget_parameters,
                &input_bytes,
            )
            .unwrap();

        println!("number of constraints total: {}", cs.num_constraints());

        let primitive_result = primitive_result.into_affine();
        assert_eq!(primitive_result.x, gadget_result.x.value.unwrap());
        assert_eq!(primitive_result.y, gadget_result.y.value.unwrap());
        assert!(cs.is_satisfied());
    }
}
