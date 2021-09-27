use algebra::curves::bn_382::Bn382Parameters;

pub type PairingGadget = crate::pairing::bn::PairingGadget<Bn382Parameters>;

#[cfg(test)]
mod test {
    use super::*;
    use serial_test::serial;

    #[serial]
    #[test]
    fn test() {
        crate::pairing::tests::bilinearity_test::<algebra::curves::bn_382::Bn382, _, PairingGadget>()
    }
}
