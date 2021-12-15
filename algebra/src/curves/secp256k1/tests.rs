use crate::{
    curves::{
        secp256k1::{Affine, Projective, Secp256k1Parameters},
        tests::{curve_tests, sw_jacobian_curve_serialization_test},
        AffineCurve, ProjectiveCurve,
    },
    fields::secp256k1::Fr,
    groups::tests::group_test,
    FromBytes, SemanticallyValid,
};
use hex_literal::hex;
use rand::{Rng, SeedableRng};
use rand_xorshift::XorShiftRng;

#[test]
fn test_secp256k1_projective_curve() {
    curve_tests::<Projective>();
    sw_jacobian_curve_serialization_test::<Secp256k1Parameters>();
}

#[test]
fn test_secp256k1_projective_group() {
    let mut rng = XorShiftRng::seed_from_u64(1234567890u64);
    let a: Projective = rng.gen();
    let b: Projective = rng.gen();
    group_test(a, b);
}

#[test]
fn test_secp256k1_generator() {
    let generator = Affine::prime_subgroup_generator();
    assert!(generator.is_on_curve());
    assert!(generator.is_in_correct_subgroup_assuming_on_curve());
}

fn to_internal_repr(mut x: Vec<u8>, mut y: Vec<u8>) -> Projective {
    // Hex is in big-endian but FromBytes accepts only in little-endian, so we need to reverse.
    // Plus, we represent the Field using a BigInteger320, e.g. with 40 bytes instead of 32, so we need to pad.
    x.reverse();
    x.append(&mut vec![0u8; 8]);
    y.reverse();
    y.append(&mut vec![0u8; 8]);

    // Collect both coordinates
    x.append(&mut y);

    // Push infinity flag being 0
    x.push(0u8);

    // Read point (let's use the FromBytes for simplicity)
    Affine::read(&x[..]).unwrap().into_projective()
}

#[test]
/// Repeated addition with the generator. Test vectors are taken from
/// https://github.com/RustCrypto/elliptic-curves/blob/master/k256/src/test_vectors/group.rs
fn test_secp256k1_addition_correctness() {
    const ADD_TEST_VECTORS: &[([u8; 32], [u8; 32])] = &[
        (
            hex!("79BE667EF9DCBBAC55A06295CE870B07029BFCDB2DCE28D959F2815B16F81798"),
            hex!("483ADA7726A3C4655DA4FBFC0E1108A8FD17B448A68554199C47D08FFB10D4B8"),
        ),
        (
            hex!("C6047F9441ED7D6D3045406E95C07CD85C778E4B8CEF3CA7ABAC09B95C709EE5"),
            hex!("1AE168FEA63DC339A3C58419466CEAEEF7F632653266D0E1236431A950CFE52A"),
        ),
        (
            hex!("F9308A019258C31049344F85F89D5229B531C845836F99B08601F113BCE036F9"),
            hex!("388F7B0F632DE8140FE337E62A37F3566500A99934C2231B6CB9FD7584B8E672"),
        ),
        (
            hex!("E493DBF1C10D80F3581E4904930B1404CC6C13900EE0758474FA94ABE8C4CD13"),
            hex!("51ED993EA0D455B75642E2098EA51448D967AE33BFBDFE40CFE97BDC47739922"),
        ),
        (
            hex!("2F8BDE4D1A07209355B4A7250A5C5128E88B84BDDC619AB7CBA8D569B240EFE4"),
            hex!("D8AC222636E5E3D6D4DBA9DDA6C9C426F788271BAB0D6840DCA87D3AA6AC62D6"),
        ),
        (
            hex!("FFF97BD5755EEEA420453A14355235D382F6472F8568A18B2F057A1460297556"),
            hex!("AE12777AACFBB620F3BE96017F45C560DE80F0F6518FE4A03C870C36B075F297"),
        ),
        (
            hex!("5CBDF0646E5DB4EAA398F365F2EA7A0E3D419B7E0330E39CE92BDDEDCAC4F9BC"),
            hex!("6AEBCA40BA255960A3178D6D861A54DBA813D0B813FDE7B5A5082628087264DA"),
        ),
        (
            hex!("2F01E5E15CCA351DAFF3843FB70F3C2F0A1BDD05E5AF888A67784EF3E10A2A01"),
            hex!("5C4DA8A741539949293D082A132D13B4C2E213D6BA5B7617B5DA2CB76CBDE904"),
        ),
        (
            hex!("ACD484E2F0C7F65309AD178A9F559ABDE09796974C57E714C35F110DFC27CCBE"),
            hex!("CC338921B0A7D9FD64380971763B61E9ADD888A4375F8E0F05CC262AC64F9C37"),
        ),
        (
            hex!("A0434D9E47F3C86235477C7B1AE6AE5D3442D49B1943C2B752A68E2A47E247C7"),
            hex!("893ABA425419BC27A3B6C7E693A24C696F794C2ED877A1593CBEE53B037368D7"),
        ),
        (
            hex!("774AE7F858A9411E5EF4246B70C65AAC5649980BE5C17891BBEC17895DA008CB"),
            hex!("D984A032EB6B5E190243DD56D7B7B365372DB1E2DFF9D6A8301D74C9C953C61B"),
        ),
        (
            hex!("D01115D548E7561B15C38F004D734633687CF4419620095BC5B0F47070AFE85A"),
            hex!("A9F34FFDC815E0D7A8B64537E17BD81579238C5DD9A86D526B051B13F4062327"),
        ),
        (
            hex!("F28773C2D975288BC7D1D205C3748651B075FBC6610E58CDDEEDDF8F19405AA8"),
            hex!("0AB0902E8D880A89758212EB65CDAF473A1A06DA521FA91F29B5CB52DB03ED81"),
        ),
        (
            hex!("499FDF9E895E719CFD64E67F07D38E3226AA7B63678949E6E49B241A60E823E4"),
            hex!("CAC2F6C4B54E855190F044E4A7B3D464464279C27A3F95BCC65F40D403A13F5B"),
        ),
        (
            hex!("D7924D4F7D43EA965A465AE3095FF41131E5946F3C85F79E44ADBCF8E27E080E"),
            hex!("581E2872A86C72A683842EC228CC6DEFEA40AF2BD896D3A5C504DC9FF6A26B58"),
        ),
        (
            hex!("E60FCE93B59E9EC53011AABC21C23E97B2A31369B87A5AE9C44EE89E2A6DEC0A"),
            hex!("F7E3507399E595929DB99F34F57937101296891E44D23F0BE1F32CCE69616821"),
        ),
        (
            hex!("DEFDEA4CDB677750A420FEE807EACF21EB9898AE79B9768766E4FAA04A2D4A34"),
            hex!("4211AB0694635168E997B0EAD2A93DAECED1F4A04A95C0F6CFB199F69E56EB77"),
        ),
        (
            hex!("5601570CB47F238D2B0286DB4A990FA0F3BA28D1A319F5E7CF55C2A2444DA7CC"),
            hex!("C136C1DC0CBEB930E9E298043589351D81D8E0BC736AE2A1F5192E5E8B061D58"),
        ),
        (
            hex!("2B4EA0A797A443D293EF5CFF444F4979F06ACFEBD7E86D277475656138385B6C"),
            hex!("85E89BC037945D93B343083B5A1C86131A01F60C50269763B570C854E5C09B7A"),
        ),
        (
            hex!("4CE119C96E2FA357200B559B2F7DD5A5F02D5290AFF74B03F3E471B273211C97"),
            hex!("12BA26DCB10EC1625DA61FA10A844C676162948271D96967450288EE9233DC3A"),
        ),
    ];

    let gen = Projective::prime_subgroup_generator();
    let mut curr_point = gen;

    for (i, (x, y)) in ADD_TEST_VECTORS.iter().enumerate() {
        let test_point = to_internal_repr(x.to_vec(), y.to_vec());
        assert!(
            test_point.is_valid(),
            "Validity test failed for point {}",
            i
        );
        assert_eq!(
            test_point, curr_point,
            "Computed value doesn't match test one for point {}",
            i
        );
        curr_point += &gen;
    }
}

#[test]
/// Scalar multiplication with the generator. Test vectors are taken from
/// https://github.com/RustCrypto/elliptic-curves/blob/master/k256/src/test_vectors/group.rs
fn test_secp256k1_mul_bits_correctness() {
    use std::ops::Mul;

    pub const MUL_TEST_VECTORS: &[([u8; 32], [u8; 32], [u8; 32])] = &[
        (
            hex!("000000000000000000000000000000000000000000000000018EBBB95EED0E13"),
            hex!("A90CC3D3F3E146DAADFC74CA1372207CB4B725AE708CEF713A98EDD73D99EF29"),
            hex!("5A79D6B289610C68BC3B47F3D72F9788A26A06868B4D8E433E1E2AD76FB7DC76"),
        ),
        (
            hex!("0000000000000000000000000000000000159D893D4CDD747246CDCA43590E13"),
            hex!("E5A2636BCFD412EBF36EC45B19BFB68A1BC5F8632E678132B885F7DF99C5E9B3"),
            hex!("736C1CE161AE27B405CAFD2A7520370153C2C861AC51D6C1D5985D9606B45F39"),
        ),
        (
            hex!("3FFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFAEABB739ABD2280EEFF497A3340D9050"),
            hex!("A6B594B38FB3E77C6EDF78161FADE2041F4E09FD8497DB776E546C41567FEB3C"),
            hex!("71444009192228730CD8237A490FEBA2AFE3D27D7CC1136BC97E439D13330D55"),
        ),
        (
            hex!("7FFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF5D576E7357A4501DDFE92F46681B20A0"),
            hex!("00000000000000000000003B78CE563F89A0ED9414F5AA28AD0D96D6795F9C63"),
            hex!("3F3979BF72AE8202983DC989AEC7F2FF2ED91BDD69CE02FC0700CA100E59DDF3"),
        ),
        (
            hex!("BFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF0C0325AD0376782CCFDDC6E99C28B0F0"),
            hex!("E24CE4BEEE294AA6350FAA67512B99D388693AE4E7F53D19882A6EA169FC1CE1"),
            hex!("8B71E83545FC2B5872589F99D948C03108D36797C4DE363EBD3FF6A9E1A95B10"),
        ),
        (
            hex!("FFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEBAAEDCE6AF48A03BBFD25E8CD036412D"),
            hex!("4CE119C96E2FA357200B559B2F7DD5A5F02D5290AFF74B03F3E471B273211C97"),
            hex!("ED45D9234EF13E9DA259E05EF57BB3989E9D6B7D8E269698BAFD77106DCC1FF5"),
        ),
        (
            hex!("FFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEBAAEDCE6AF48A03BBFD25E8CD036412E"),
            hex!("2B4EA0A797A443D293EF5CFF444F4979F06ACFEBD7E86D277475656138385B6C"),
            hex!("7A17643FC86BA26C4CBCF7C4A5E379ECE5FE09F3AFD9689C4A8F37AA1A3F60B5"),
        ),
        (
            hex!("FFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEBAAEDCE6AF48A03BBFD25E8CD036412F"),
            hex!("5601570CB47F238D2B0286DB4A990FA0F3BA28D1A319F5E7CF55C2A2444DA7CC"),
            hex!("3EC93E23F34146CF161D67FBCA76CAE27E271F438C951D5E0AE6D1A074F9DED7"),
        ),
        (
            hex!("FFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEBAAEDCE6AF48A03BBFD25E8CD0364130"),
            hex!("DEFDEA4CDB677750A420FEE807EACF21EB9898AE79B9768766E4FAA04A2D4A34"),
            hex!("BDEE54F96B9CAE9716684F152D56C251312E0B5FB56A3F09304E660861A910B8"),
        ),
        (
            hex!("FFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEBAAEDCE6AF48A03BBFD25E8CD0364131"),
            hex!("E60FCE93B59E9EC53011AABC21C23E97B2A31369B87A5AE9C44EE89E2A6DEC0A"),
            hex!("081CAF8C661A6A6D624660CB0A86C8EFED6976E1BB2DC0F41E0CD330969E940E"),
        ),
        (
            hex!("FFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEBAAEDCE6AF48A03BBFD25E8CD0364132"),
            hex!("D7924D4F7D43EA965A465AE3095FF41131E5946F3C85F79E44ADBCF8E27E080E"),
            hex!("A7E1D78D57938D597C7BD13DD733921015BF50D427692C5A3AFB235F095D90D7"),
        ),
        (
            hex!("FFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEBAAEDCE6AF48A03BBFD25E8CD0364133"),
            hex!("499FDF9E895E719CFD64E67F07D38E3226AA7B63678949E6E49B241A60E823E4"),
            hex!("353D093B4AB17AAE6F0FBB1B584C2B9BB9BD863D85C06A4339A0BF2AFC5EBCD4"),
        ),
        (
            hex!("FFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEBAAEDCE6AF48A03BBFD25E8CD0364134"),
            hex!("F28773C2D975288BC7D1D205C3748651B075FBC6610E58CDDEEDDF8F19405AA8"),
            hex!("F54F6FD17277F5768A7DED149A3250B8C5E5F925ADE056E0D64A34AC24FC0EAE"),
        ),
        (
            hex!("FFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEBAAEDCE6AF48A03BBFD25E8CD0364135"),
            hex!("D01115D548E7561B15C38F004D734633687CF4419620095BC5B0F47070AFE85A"),
            hex!("560CB00237EA1F285749BAC81E8427EA86DC73A2265792AD94FAE4EB0BF9D908"),
        ),
        (
            hex!("FFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEBAAEDCE6AF48A03BBFD25E8CD0364136"),
            hex!("774AE7F858A9411E5EF4246B70C65AAC5649980BE5C17891BBEC17895DA008CB"),
            hex!("267B5FCD1494A1E6FDBC22A928484C9AC8D24E1D20062957CFE28B3536AC3614"),
        ),
        (
            hex!("FFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEBAAEDCE6AF48A03BBFD25E8CD0364137"),
            hex!("A0434D9E47F3C86235477C7B1AE6AE5D3442D49B1943C2B752A68E2A47E247C7"),
            hex!("76C545BDABE643D85C4938196C5DB3969086B3D127885EA6C3411AC3FC8C9358"),
        ),
        (
            hex!("FFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEBAAEDCE6AF48A03BBFD25E8CD0364138"),
            hex!("ACD484E2F0C7F65309AD178A9F559ABDE09796974C57E714C35F110DFC27CCBE"),
            hex!("33CC76DE4F5826029BC7F68E89C49E165227775BC8A071F0FA33D9D439B05FF8"),
        ),
        (
            hex!("FFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEBAAEDCE6AF48A03BBFD25E8CD0364139"),
            hex!("2F01E5E15CCA351DAFF3843FB70F3C2F0A1BDD05E5AF888A67784EF3E10A2A01"),
            hex!("A3B25758BEAC66B6D6C2F7D5ECD2EC4B3D1DEC2945A489E84A25D3479342132B"),
        ),
        (
            hex!("FFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEBAAEDCE6AF48A03BBFD25E8CD036413A"),
            hex!("5CBDF0646E5DB4EAA398F365F2EA7A0E3D419B7E0330E39CE92BDDEDCAC4F9BC"),
            hex!("951435BF45DAA69F5CE8729279E5AB2457EC2F47EC02184A5AF7D9D6F78D9755"),
        ),
        (
            hex!("FFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEBAAEDCE6AF48A03BBFD25E8CD036413B"),
            hex!("FFF97BD5755EEEA420453A14355235D382F6472F8568A18B2F057A1460297556"),
            hex!("51ED8885530449DF0C4169FE80BA3A9F217F0F09AE701B5FC378F3C84F8A0998"),
        ),
        (
            hex!("FFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEBAAEDCE6AF48A03BBFD25E8CD036413C"),
            hex!("2F8BDE4D1A07209355B4A7250A5C5128E88B84BDDC619AB7CBA8D569B240EFE4"),
            hex!("2753DDD9C91A1C292B24562259363BD90877D8E454F297BF235782C459539959"),
        ),
        (
            hex!("FFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEBAAEDCE6AF48A03BBFD25E8CD036413D"),
            hex!("E493DBF1C10D80F3581E4904930B1404CC6C13900EE0758474FA94ABE8C4CD13"),
            hex!("AE1266C15F2BAA48A9BD1DF6715AEBB7269851CC404201BF30168422B88C630D"),
        ),
        (
            hex!("FFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEBAAEDCE6AF48A03BBFD25E8CD036413E"),
            hex!("F9308A019258C31049344F85F89D5229B531C845836F99B08601F113BCE036F9"),
            hex!("C77084F09CD217EBF01CC819D5C80CA99AFF5666CB3DDCE4934602897B4715BD"),
        ),
        (
            hex!("FFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEBAAEDCE6AF48A03BBFD25E8CD036413F"),
            hex!("C6047F9441ED7D6D3045406E95C07CD85C778E4B8CEF3CA7ABAC09B95C709EE5"),
            hex!("E51E970159C23CC65C3A7BE6B99315110809CD9ACD992F1EDC9BCE55AF301705"),
        ),
        (
            hex!("FFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEBAAEDCE6AF48A03BBFD25E8CD0364140"),
            hex!("79BE667EF9DCBBAC55A06295CE870B07029BFCDB2DCE28D959F2815B16F81798"),
            hex!("B7C52588D95C3B9AA25B0403F1EEF75702E84BB7597AABE663B82F6F04EF2777"),
        ),
    ];

    let gen = Projective::prime_subgroup_generator();

    for (i, (scalar, x, y)) in MUL_TEST_VECTORS.iter().enumerate() {
        let test_point = to_internal_repr(x.to_vec(), y.to_vec());
        assert!(
            test_point.is_valid(),
            "Validity test failed for point {}",
            i
        );

        let test_scalar = {
            let mut scalar = scalar.to_vec();
            scalar.reverse();
            scalar.append(&mut vec![0u8; 8]);
            Fr::read(&scalar[..]).unwrap()
        };
        assert!(
            test_scalar.is_valid(),
            "Validity test failed for scalar {}",
            i
        );

        assert_eq!(
            test_point,
            gen.mul(&test_scalar),
            "Computed value doesn't match test one for point {}",
            i
        );
    }
}