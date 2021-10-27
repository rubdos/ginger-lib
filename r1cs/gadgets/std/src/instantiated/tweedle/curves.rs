use algebra::{fields::tweedle::{Fq, Fr}, curves::tweedle::{
    dee::TweedledeeParameters,
    dum::TweedledumParameters,
}};
use crate::{
    groups::curves::short_weierstrass::short_weierstrass_jacobian::AffineGadget,
    instantiated::tweedle::{FqGadget, FrGadget},
};

pub type TweedleDeeGadget = AffineGadget<TweedledeeParameters, Fq, FqGadget>;
pub type TweedleDumGadget = AffineGadget<TweedledumParameters, Fr, FrGadget>;

#[cfg(test)]
mod test {
    use r1cs_core::ConstraintSystem;
    use crate::{
        prelude::*,
        test_constraint_system::TestConstraintSystem,
        instantiated::tweedle::{
            TweedleDeeGadget,
            TweedleDumGadget,
        },
        groups::EndoMulCurveGadget,
    };
    use algebra::{UniformRand, AffineCurve, ProjectiveCurve, EndoMulCurve, fields::tweedle::{
        Fq, Fr,
    }, curves::tweedle::{
        dee::Projective as DeeProjective,
        dum::Projective as DumProjective,
    }, PrimeField, BigInteger};
    use rand::thread_rng;

    #[test]
    fn test_dee() {
        crate::groups::test::group_test_with_incomplete_add::<
            _, _, TweedleDeeGadget
        >();
        crate::groups::test::mul_bits_test::<
            _, _, TweedleDeeGadget
        >();
    }

    #[test]
    fn test_dum() {
        crate::groups::test::group_test_with_incomplete_add::<
            _, _, TweedleDumGadget
        >();
        crate::groups::test::mul_bits_test::<
            _, _, TweedleDumGadget
        >();
    }

    #[test]
    /// Tests equality of the result enforced by `endo_mul()` 
    /// with the corresponding scalar multiple. 
    fn test_endo_dee()
    {
        let mut cs = TestConstraintSystem::<Fq>::new();

        let a_native = DeeProjective::rand(&mut thread_rng()).into_affine();
        let a = TweedleDeeGadget::alloc(&mut cs.ns(|| "generate_a"), || Ok(a_native.into_projective())).unwrap();

        let scalar: Fr = u128::rand(&mut thread_rng()).into();

        let b_native = scalar.into_repr().to_bits().as_slice()[0..128].to_vec();
        let b = b_native
            .iter()
            .map(|&bit| Boolean::constant(bit))
            .collect::<Vec<_>>();

        let r_native = a_native.endo_mul(b_native).unwrap().into_affine();
        let r = a.endo_mul(cs.ns(|| "endo mul"), &b).unwrap().get_value().unwrap().into_affine();

        assert_eq!(r_native, r);
    }

    #[test]
    /// Tests equality of the result enforced by `endo_mul()` 
    /// with the corresponding scalar multiple. 
    fn test_endo_dum()
    {
        let mut cs = TestConstraintSystem::<Fr>::new();

        let a_native = DumProjective::rand(&mut thread_rng()).into_affine();
        let a = TweedleDumGadget::alloc(&mut cs.ns(|| "generate_a"), || Ok(a_native.into_projective())).unwrap();

        let scalar: Fq = u128::rand(&mut thread_rng()).into();

        let b_native = scalar.into_repr().to_bits().as_slice()[0..128].to_vec();
        let b = b_native
            .iter()
            .map(|&bit| Boolean::constant(bit))
            .collect::<Vec<_>>();

        let r_native = a_native.endo_mul(b_native).unwrap().into_affine();
        let r = a.endo_mul(cs.ns(|| "endo mul"), &b).unwrap().get_value().unwrap().into_affine();

        assert_eq!(r_native, r);
    }
}
