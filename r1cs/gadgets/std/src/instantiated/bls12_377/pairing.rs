use algebra::curves::bls12_377::Bls12_377Parameters as Parameters;

pub type PairingGadget = crate::pairing::bls12::PairingGadget<Parameters>;

#[cfg(test)]
mod test {
    use super::*;
    use serial_test::serial;

    #[serial]
    #[test]
    fn test() {
        crate::pairing::tests::bilinearity_test::<algebra::curves::bls12_377::Bls12_377, _, PairingGadget>()
    }
}

