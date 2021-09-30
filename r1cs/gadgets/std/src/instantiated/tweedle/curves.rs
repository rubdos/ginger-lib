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

#[test]
fn test_dee() {
    crate::groups::test::group_test_with_unsafe_add::<
        _, _, TweedleDeeGadget
    >();
}

#[test]
fn test_dum() {
    crate::groups::test::group_test_with_unsafe_add::<
        _, _, TweedleDumGadget
    >();
}

#[test]
fn test_endo_dee()
{
    use r1cs_core::ConstraintSystem;
    use crate::{
        prelude::*,
        test_constraint_system::TestConstraintSystem,
    };
    use algebra::{
        UniformRand, BitIterator, AffineCurve, ProjectiveCurve,
        curves::tweedle::dee::Projective as DeeProjective,
    };
    use rand::thread_rng;

    let mut cs = TestConstraintSystem::<Fq>::new();

    let a = DeeProjective::rand(&mut thread_rng()).into_affine();
    let aa = TweedleDeeGadget::alloc(&mut cs.ns(|| "generate_a"), || Ok(a.into_projective())).unwrap();

    let seed = [0x378237, 0x3298983, 0x90902203, 0x839283782];
    let b = BitIterator::new(seed)
        .map(|bit| bit)
        .collect::<Vec<_>>();
    let bb = BitIterator::new(seed)
        .map(|bit| Boolean::constant(bit))
        .collect::<Vec<_>>();

    let r = a.endo_mul(b).into_affine();
    let rr = aa.endo_mul(cs.ns(|| "endo mul"), &bb).unwrap().get_value().unwrap().into_affine();

    assert_eq!(r, rr);
}
