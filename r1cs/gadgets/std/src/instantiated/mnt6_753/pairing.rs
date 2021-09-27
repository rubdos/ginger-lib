use algebra::curves::mnt6753::MNT6_753Parameters as Parameters;

pub type PairingGadget = crate::pairing::mnt6::MNT6PairingGadget<Parameters>;

#[cfg(test)]
mod test {
    use super::*;
    use serial_test::serial;

    #[serial]
    #[test]
    fn test() {
        crate::pairing::tests::bilinearity_test::<algebra::curves::mnt6753::MNT6, _, PairingGadget>()
    }
}
