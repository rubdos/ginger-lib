use crate::fields::nonnative::NonNativeFieldParams;

/// Obtain the parameters from a `ConstraintSystem`'s cache or generate a new one
#[must_use]
pub const fn get_params(target_field_size: usize, base_field_size: usize) -> NonNativeFieldParams {
    let (num_of_limbs, limb_size) =
        find_parameters(base_field_size, target_field_size);
    NonNativeFieldParams {
        num_limbs: num_of_limbs,
        bits_per_limb: limb_size,
    }
}

/// Finding parameters which optimize the number of constraints of a `single mul_without_prereduce()`
/// and a subsequent `reduce()`, assuming `surfeit = 10`.
pub const fn find_parameters(
    base_field_prime_length: usize,
    target_field_prime_bit_length: usize,
) -> (usize, usize) {
    let mut found = false;
    let mut min_cost = 0usize;
    let mut min_cost_limb_size = 0usize;
    let mut min_cost_num_of_limbs = 0usize;

    let surfeit = 10;

    let mut max_limb_size = (base_field_prime_length - 1 - surfeit - 1) / 2 - 1;
    if max_limb_size > target_field_prime_bit_length {
        max_limb_size = target_field_prime_bit_length;
    }
    let mut limb_size = 1;

    while limb_size <= max_limb_size {
        let num_of_limbs = (target_field_prime_bit_length + limb_size - 1) / limb_size;

        let group_size =
            (base_field_prime_length - 1 - surfeit - 1 - 1 - limb_size + limb_size - 1) / limb_size;
        let num_of_groups = (2 * num_of_limbs - 1 + group_size - 1) / group_size;

        let mut this_cost = 0;
        this_cost += 6 * num_of_limbs * num_of_limbs;

        this_cost += target_field_prime_bit_length * 3 + target_field_prime_bit_length; // allocation of k
        this_cost += target_field_prime_bit_length * 3
            + target_field_prime_bit_length
            + num_of_limbs; // allocation of r
        this_cost += num_of_limbs * num_of_limbs + 2 * (2 * num_of_limbs - 1); // compute kp
        this_cost += num_of_limbs
            + num_of_groups
            + 6 * num_of_groups
            + (num_of_groups - 1) * (2 * limb_size + surfeit) * 4
            + 2; // equality check


        if !found || this_cost < min_cost {
            found = true;
            min_cost = this_cost;
            min_cost_limb_size = limb_size;
            min_cost_num_of_limbs = num_of_limbs;
        }

        limb_size += 1;
    }

    (min_cost_num_of_limbs, min_cost_limb_size)
}
