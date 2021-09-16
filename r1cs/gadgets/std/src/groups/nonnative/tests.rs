use algebra::{
    fields::{
        tweedle::{Fq as TweedleFq, Fr as TweedleFr},
        bn_382::{Fq as BN382Fq, Fr as BN382Fr},
    },
    curves::{
        tweedle::{
            dee::TweedledeeParameters, dum::TweedledumParameters
        },
    }
};

use crate::groups::test::*;
use crate::groups::nonnative::nonnative_group_gadget::GroupAffineNonNativeGadget;

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
        /*nonnative_test_individual!(
            mul_bits_test,
            $test_name,
            $num_samples,
            $group_params,
            $test_constraint_field,
            $test_simulation_field
        );*/
    };
}

macro_rules! nonnative_group_test_unsafe_add {
    ($test_name:ident, $num_samples:expr, $group_params:ty, $test_constraint_field:ty, $test_simulation_field:ty) => {
        nonnative_test_individual!(
            group_test_with_unsafe_add,
            $test_name,
            $num_samples,
            $group_params,
            $test_constraint_field,
            $test_simulation_field
        );
        /*nonnative_test_individual!(
            mul_bits_test,
            $test_name,
            $num_samples,
            $group_params,
            $test_constraint_field,
            $test_simulation_field
        );*/
    };
}

nonnative_group_test_unsafe_add!(
    Bn382FrTweedleFq,
    1,
    TweedledeeParameters,
    BN382Fr,
    TweedleFq
);

nonnative_group_test_unsafe_add!(
    Bn382FqTweedleFr,
    1,
    TweedledumParameters,
    BN382Fq,
    TweedleFr
);