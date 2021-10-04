use algebra::{
    fields::{
        Field,
        secp256k1::Fq as secp256k1Fq,
        bn_382::Fr as BN382Fr,
    },
    curves::secp256k1::Secp256k1Parameters,
    groups::Group,
    UniformRand,
    ToBits,
};
use r1cs_core::ConstraintSystem;
use crate::{
    alloc::AllocGadget,
    bits::boolean::Boolean,
    groups::{
        GroupGadget,
        nonnative::short_weierstrass_jacobian::GroupAffineNonNativeGadget,
        test::group_test_with_incomplete_add,
    },
    test_constraint_system::TestConstraintSystem,
};
use rand::thread_rng;


#[allow(dead_code)]
pub(crate) fn mul_bits_test<
    ConstraintF: Field,
    G: Group,
    GG: GroupGadget<G, ConstraintF, Value = G>,
>()
{
    let mut cs: TestConstraintSystem<ConstraintF> = TestConstraintSystem::<ConstraintF>::new();
    let rng = &mut thread_rng();

    // Sample random base
    let g: G = UniformRand::rand(rng);
    let gg = GG::alloc(cs.ns(|| "generate_g"), || Ok(g)).unwrap();

    // Sample random scalar
    let a = G::ScalarField::rand(rng);

    // Alloc its bits on the circuit
    let mut a_bits = Vec::<Boolean>::alloc(cs.ns(|| "a bits"), || Ok(a.write_bits())).unwrap();
    a_bits.reverse();

    // Variable base scalar multiplication
    let x = cs.num_constraints();
    let a_times_gg_vb = gg.mul_bits(cs.ns(|| "a * G"), a_bits.iter()).unwrap();
    println!("Variable base SM exponent len {}, num_constraints: {}", a_bits.len(), cs.num_constraints() - x);

    // Fixed base scalar multiplication
    let x = cs.num_constraints();
    let a_times_gg_fb = GG::mul_bits_fixed_base(&g, cs.ns(|| "fb a * G"), a_bits.as_slice()).unwrap();
    println!("Fixed base SM exponent len {}, num_constraints: {}", a_bits.len(), cs.num_constraints() - x);

    // Compare with native results
    assert_eq!(a_times_gg_vb.get_value().unwrap(), g.mul(&a));
    assert_eq!(a_times_gg_fb.get_value().unwrap(), g.mul(&a));

    assert!(cs.is_satisfied());
}

macro_rules! nonnative_test_individual {
    ($test_method:ident, $test_name:ident, $num_samples:expr, $group_params:ty, $test_constraint_field:ty, $test_simulation_field:ty) => {
        paste::item! {
            #[test]
            fn [<$test_method _ $test_name:lower>]() {
                for _ in 0..$num_samples {
                    $test_method::<_, _, GroupAffineNonNativeGadget<$group_params, $test_constraint_field, $test_simulation_field>>();
                }
            }
        }
    };
}

#[allow(unused_macros)]
macro_rules! nonnative_group_test {
    ($test_name:ident, $num_samples:expr, $group_params:ty, $test_constraint_field:ty, $test_simulation_field:ty) => {
        nonnative_test_individual!(
            group_test,
            $test_name,
            $num_samples,
            $group_params,
            $test_constraint_field,
            $test_simulation_field
        );
        nonnative_test_individual!(
            mul_bits_test,
            $test_name,
            $num_samples,
            $group_params,
            $test_constraint_field,
            $test_simulation_field
        );
    };
}

macro_rules! nonnative_group_test_unsafe_add {
    ($test_name:ident, $num_samples:expr, $group_params:ty, $test_constraint_field:ty, $test_simulation_field:ty) => {
        nonnative_test_individual!(
            group_test_with_incomplete_add,
            $test_name,
            $num_samples,
            $group_params,
            $test_constraint_field,
            $test_simulation_field
        );
        nonnative_test_individual!(
            mul_bits_test,
            $test_name,
            $num_samples,
            $group_params,
            $test_constraint_field,
            $test_simulation_field
        );
    };
}

nonnative_group_test_unsafe_add!(
    Bn382Frsecp256k1Fq,
    1,
    Secp256k1Parameters,
    BN382Fr,
    secp256k1Fq
);