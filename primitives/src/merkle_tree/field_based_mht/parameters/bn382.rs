use algebra::{
    fields::bn_382::Fr as BN382Fr,
    biginteger::BigInteger384,
    field_new,
};

use crate::{
    crh::poseidon::BN382FrPoseidonHash,
    FieldBasedMerkleTreePrecomputedZeroConstants,
};

// PoseidonHash("This represents an empty Merkle Root for a BN382FrPoseidonHash based Merkle Tree.")
pub const BN382_PHANTOM_MERKLE_ROOT: BN382Fr =
    field_new!(BN382Fr, BigInteger384([
        99773930179339435,
        348923504295496314,
        646079944679159593,
        7944079026413204524,
        7188710039817985762,
        1508748032991309384
    ]));

pub const BN382_MHT_POSEIDON_PARAMETERS: FieldBasedMerkleTreePrecomputedZeroConstants<'static, BN382FrPoseidonHash> =
    FieldBasedMerkleTreePrecomputedZeroConstants {
        nodes: &[
            field_new!(BN382Fr, BigInteger384([0, 0, 0, 0, 0, 0])),
            field_new!(BN382Fr, BigInteger384([15745522788649903907, 16652409264296773101, 9580329627252538379, 14449588676843283900, 18075316901601731326, 2096864981361276526])),
            field_new!(BN382Fr, BigInteger384([2268444023388143544, 17298360647738556748, 94373253860962130, 8702337489709032691, 9644208621815391130, 2264890757681590843])),
            field_new!(BN382Fr, BigInteger384([7083298892765997525, 8892407521668137791, 9197215395346518622, 6847703070393882449, 15815800337722272215, 2146152396506143110])),
            field_new!(BN382Fr, BigInteger384([750322402422095458, 16665857403862931511, 12073911270502074268, 8433108039675190344, 1300689657487132566, 1020791768747886572])),
            field_new!(BN382Fr, BigInteger384([11281746813136010846, 18274249872713361110, 9851530189728317185, 3338120257635833108, 3801524501259031095, 248287800870448076])),
            field_new!(BN382Fr, BigInteger384([2390950906608007984, 4903832209033298596, 2925749861501906773, 4464995168837234610, 9918609401679022161, 895224401408241737])),
            field_new!(BN382Fr, BigInteger384([15795463120980401949, 13683817975310161826, 14943758995704371758, 2963047471043258611, 15560137637823847687, 1970079961753011829])),
            field_new!(BN382Fr, BigInteger384([1525930063762604551, 7821861940372891874, 3288493529010705295, 10088419980085533439, 13145259179765681517, 1322404108891623173])),
            field_new!(BN382Fr, BigInteger384([2684330210395719551, 11286208450053283994, 15699938099991331709, 18412623006990068853, 9501317450489141331, 172059031072665217])),
            field_new!(BN382Fr, BigInteger384([5819165191195505318, 12153225337826917781, 12327240005547992139, 12207354228153053751, 3901867814770348889, 1438981947430405828])),
            field_new!(BN382Fr, BigInteger384([11214241094396042753, 11173876455926953396, 15814145438405569553, 18144677296528908006, 18412396687004136456, 1258927997344890989])),
            field_new!(BN382Fr, BigInteger384([10049953164942675478, 16416714521945791933, 17041185386399416490, 17642836562955912768, 18183804977083255435, 2419907683556989366])),
            field_new!(BN382Fr, BigInteger384([5442062389265456001, 3809170157598981025, 171581856662145032, 7823864420716956396, 14190301556270692975, 1925674956519263100])),
            field_new!(BN382Fr, BigInteger384([12294189776828093222, 9695787539924999054, 17265012360232765539, 15244771273107585498, 15265697462822524160, 846181752110206430])),
            field_new!(BN382Fr, BigInteger384([11185085303686312588, 16902728784831515441, 13164449473289657618, 9549239001699138221, 13043374568401809638, 1642958620195066185])),
            field_new!(BN382Fr, BigInteger384([1390697583764602093, 14358331455140202139, 9806658171340269129, 8251375617867637901, 12151248349977502804, 455921830939517914])),
            field_new!(BN382Fr, BigInteger384([11612053044891427379, 5419547329233500692, 3523066411176134140, 15564341640990073183, 2067829022235025120, 702528074150429489])),
            field_new!(BN382Fr, BigInteger384([15036289228239389000, 14265335863058877392, 11472396836099736148, 7427258307910247530, 10268179225463705622, 789369268217915113])),
            field_new!(BN382Fr, BigInteger384([8435340205313937413, 10115055377697127058, 8316231521312999546, 3213801747455134400, 10644744892564093098, 194996373114334014])),
            field_new!(BN382Fr, BigInteger384([4417166319706354555, 18059889370229157288, 599731290899030549, 17740477437781096438, 10743946805919141448, 1255980265141921671])),
            field_new!(BN382Fr, BigInteger384([8379846358161539910, 6730457586677095487, 99799092274867936, 16494583908071785679, 6131352036353445598, 504757793675923016])),
            field_new!(BN382Fr, BigInteger384([7618790430717705224, 12238331599640839364, 12280407896864119921, 137671061885254939, 6588285525951378421, 273021015830318700])),
            field_new!(BN382Fr, BigInteger384([17528843338993259910, 11393449507679100721, 11488252380054515768, 18396438892385169693, 12522428348938437892, 1510220287719859806])),
            field_new!(BN382Fr, BigInteger384([5232897846370952646, 12001959983773961376, 9990356515457113967, 4288647813762202340, 17920480461628008312, 103086131588975747])),
            field_new!(BN382Fr, BigInteger384([10374214577556168333, 9568513405429223927, 4041489790504288062, 1760049514128843854, 10173782315457415666, 1025079754491591784])),
            field_new!(BN382Fr, BigInteger384([3291658613665006523, 10085844144893116188, 7463547707207073869, 8938960150472038668, 6430176952637505497, 857170116659665625])),
            field_new!(BN382Fr, BigInteger384([14336914415971211635, 1330236931851483464, 4008678658071972853, 17937936022335619031, 11606575996835638030, 33779966529900173])),
            field_new!(BN382Fr, BigInteger384([4119134980068298511, 13571526693966906484, 1253155045129486578, 18284510512721817313, 167811198719422876, 2075510430651685609])),
            field_new!(BN382Fr, BigInteger384([9941799784249624573, 9692743588374875612, 15318421689942954724, 809466338861083538, 16874927241240321727, 1626992884838856495])),
            field_new!(BN382Fr, BigInteger384([2157626871658178935, 7767126464003660972, 10971073601222306380, 4429093238836685086, 10135931595697065579, 1849474545255355787])),
            field_new!(BN382Fr, BigInteger384([4618320067891861322, 4616642654378070010, 15518097436041631420, 2843648375168158222, 9969860661831651300, 1847121686185607012])),
        ],
        merkle_arity: 2,
    };

#[cfg(test)]
mod test {

    use algebra::{
        fields::bn_382::Fr, Field,
    };
    use crate::{
        crh::BN382FrPoseidonHash,
        merkle_tree::field_based_mht::parameters::{
            generate_phantom_merkle_root_from_magic_string,
            generate_mht_empty_nodes,
        },
        FieldBasedMerkleTreePrecomputedZeroConstants
    };
    use super::{
        BN382_PHANTOM_MERKLE_ROOT, BN382_MHT_POSEIDON_PARAMETERS
    };

    #[ignore]
    #[test]
    fn test_generate_bn382_phantom_merkle_root(){
        let expected_root = generate_phantom_merkle_root_from_magic_string::<Fr, BN382FrPoseidonHash>(
            "This represents an empty Merkle Root for a BN382FrPoseidonHash based Merkle Tree."
        );
        assert_eq!(expected_root, BN382_PHANTOM_MERKLE_ROOT);
    }


    #[ignore]
    #[test]
    fn test_generate_binary_bn382_mht_empty_nodes() {
        let merkle_arity = 2;
        let max_height = 32;

        let empty_nodes = generate_mht_empty_nodes::<Fr, BN382FrPoseidonHash>(merkle_arity, max_height, Fr::zero());
        assert_eq!(empty_nodes.len(), max_height);

        let params = FieldBasedMerkleTreePrecomputedZeroConstants::<BN382FrPoseidonHash> {
            nodes: empty_nodes.as_slice(), merkle_arity
        };
        assert_eq!(params, BN382_MHT_POSEIDON_PARAMETERS)
    }
}


