use crate::{
    tweedle::{FqGadget, FrGadget},
    groups::curves::short_weierstrass::AffineGadget
};
use algebra::{
    fields::tweedle::{Fq, Fr},
    curves::tweedle::{
        dee::TweedledeeParameters,
        dum::TweedledumParameters
    }
};

pub type DeeGadget = AffineGadget<TweedledeeParameters, Fq, FqGadget>;
pub type DumGadget = AffineGadget<TweedledumParameters, Fr, FrGadget>;

#[test]
fn test() {
    crate::groups::test::group_test_with_unsafe_add::<
        _, _, DeeGadget,
    >();
    crate::groups::test::group_test_with_unsafe_add::<
        _, _, DumGadget,
    >();
}
