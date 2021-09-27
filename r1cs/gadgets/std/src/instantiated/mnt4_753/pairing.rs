use algebra::curves::mnt4753::MNT4_753Parameters as Parameters;

pub type PairingGadget = crate::pairing::mnt4::MNT4PairingGadget<Parameters>;

#[cfg(test)]
mod test {
    use super::*;
    use serial_test::serial;

    #[serial]
    #[test]
    fn test() {
        crate::pairing::tests::bilinearity_test::<algebra::curves::mnt4753::MNT4, _, PairingGadget>()
    }
}
