use crate::fields::nonnative::NonNativeFieldParams;

/// Obtain the parameters from a `ConstraintSystem`'s cache or generate a new one
#[must_use]
pub const fn get_params(target_field_size: usize, base_field_size: usize) -> NonNativeFieldParams {
    let (num_of_limbs, limb_size, _) =
        find_parameters(base_field_size, target_field_size);
    NonNativeFieldParams {
        num_limbs: num_of_limbs,
        bits_per_limb: limb_size,
    }
}

/// Finding parameters which minimize the number of constraints of a `single mul_without_prereduce()`
/// and a subsequent `reduce()`, assuming that for both operands
/// ``
///     num_adds + 1 = 2^10 - 1.
/// `` 
pub(crate) const fn find_parameters(
    base_field_prime_length: usize,
    target_field_prime_length: usize,
) -> (usize, usize, usize) {
    // A `single mul_without_prereduce()` with a subsequent `reduce()` costs
    // ``
    // DDT: num_limbs^2 constraints due to the multiplication x = a * b
    // DDT: len(p) + surfeit constraints for enforcing k such that x = k * p + r 
    // DDT: len(p) constraints for enforcing r
    // DDT: Zero constraints  (len(p)^2 linear combinations) for computing the product k * r
    // DDT: (bits_per_group - num_limbs_in_a_group*bits_per_limb) boolean constraints due to carries for each group except the last one.
    // DDT: We should have that 
    //      max_group_value = (2^(2*bits_per_limb + surfeit) - 1)*(1 +  2^bits_per_limb + ... + 2^((num_limbs_in_a_group-1)*bits_per_limbs))
    //                      < 2^(2*bits_per_limb + surfeit) * ( 2^(num_limbs_in_a_group * bits_per_limb ) - 1) / ( 2^bits_per_limb - 1)
    //      It follows that 
    //          bits_per_group = len(max_group_value) = 2 * bits_per_limb + surfeit + num_limbs_in_a_group * bits_per_limb - bits_per_limb + 1
    //      where the final "+1" is ude to the fact that (x-1)/(y-1) < 2*x/y.
    //      So we should need bits_per_limb + surfeit + 1 boolean constraints needed for enforcing the carries.
    //      There can be a linear combination which links the value of the carry to its bits decomposition.
    // DDT: So, in my opinion, the right number of constraints is:
    //      C = num_limbs^2 + 2*len(p) + surfeit + (num_groups - 1)*(bits_per_limb + surfeit + 1)
    // DDT: I don't understand the final "+1" in the estimate to what is related.
    // OLD ESTIMATE:      
    // C =  2 *(len(p) + num_limbs^2) + surfeit' 
    // +  (num_groups - 1) * (3 + bits_per_limb + surfeit') + 1
    // ``
    // constraints, where 
    // ``
    //      surfeit' =  len(num_limbs * (num_adds(prod) + 1) + 1)
    //              = len(num_limbs^2 * (num_add(L)+1) * (num_add(R) + 1)),
    //      num_groups = Ceil[ 2*num_limbs / S],
    // ``
    // DDT: I think that "surfeit" should be = len(num_limbs * (num_add(L)+1) * (num_add(R) + 1)).
    //      In fact, we know a priori that limb(L) < (2^bits_per_limb-1)*(num_add(L)+1) and the same for R.
    //      Then clearly limb(product) <= num_limbs*(2^bits_per_limb-1)^2*(num_add(L)+1)(num_add(R)+1)
    //      So the surfeit, i.e. the number of extra bits of the product exceeding 2*bits_per_limb should be
    //      len(num_limbs * (num_add(L)+1) * (num_add(R) + 1)).
    // and
    // ``
    //    S - 1 = Floor[
    //          (ConstraintF::CAPACITY - 2 - surfeit') / bits_per_limb
    //          ] - 2.
    // ``
    // DDT: S (= num_limbs_in_a_group in my notation) shuld be the maximum value that bits_per_groups does not exceed CAPACITY.
    //      So, since  bits_per_group = surfeit + (num_limbs_in_a_group) * bits_per_limb  + bits_per_limb + 1
    //      We can define S = floor( (CAPACITY - surfeit - bits_per_limb - 1) / bits_per_limb)
    //                      = floor( (CAPACITY - surfeit - 1) / bits_per_limb) - 1
    // Assumes that
    // ``
    //     2 * bits_per_limb + surfeit' <= CAPACITY - 2.
    // ``
    // DDT: before changing the code, I want to be sure that Ulrich agrees with the modifications in the inline comments.
    let mut first = true;
    let mut min_cost = 0usize;
    let mut min_cost_limb_size = 0usize;
    let mut min_cost_num_of_limbs = 0usize;

    // NOTE: with our choice of `surfeit` the following computations do 
    // not cause overflows when using `usize`. 
    let surfeit = 10u32;
    let num_adds_plus_one = 2usize.pow(surfeit) - 1;
    let capacity = base_field_prime_length  - 1;
    let mut bits_per_limb = 1usize;

    while bits_per_limb <= target_field_prime_length - 1  {
        let num_limbs = (target_field_prime_length  + bits_per_limb - 1)/ bits_per_limb; 

        // computing the product representation
        let mut constraints = num_limbs * num_limbs;
        // num adds over product normal form for the product
        let num_add_prod = num_limbs 
            * num_adds_plus_one
            * num_adds_plus_one
            - 1;
        // TODO: this computes the bit length instead of the ceil log_2,
        // which might cause slightly different results.
        let surfeit_prod = std::mem::size_of::<u128>() * 8 - 
           ((num_add_prod + 1) as u128).leading_zeros() as usize;

        // alloc k and r 
        constraints += 2*target_field_prime_length + surfeit_prod;
        // computing k*p + r
        constraints += num_limbs * num_limbs;

        // The surfeit caused by (k*p + r)
        let num_add_kp_r = num_limbs * (num_add_prod + 1);  
        // TODO: this computes the bit length instead of the ceil log_2,
        // which might cause slightly different results.
        let surfeit_kp_r = std::mem::size_of::<u128>() * 8 - 
           ((num_add_kp_r + 1) as u128).leading_zeros() as usize;
   
        // check if the security assumption holds, if not continue 
        // jump to the start of the loop
        if 2 * bits_per_limb + surfeit_kp_r > capacity - 2 {
            bits_per_limb += 1;
            continue;
        }
        // The number of limbs per group.
        // ``
        //    S - 1 = Floor[
        //          (ConstraintF::CAPACITY - 2 - (2*bits_per_limb + surfeit')) / bits_per_limb
        //          ].
        // ``
        let s =  (capacity - 2 - (2 * bits_per_limb + surfeit_kp_r))/bits_per_limb  + 1;
        // num_groups = Ceil[(2*num_limbs)/ S]
        let num_groups = (2*num_limbs + s - 1)/s;
        // ``
        //      (num_groups - 1) * (1 + 2*bits_per_limb + surfeit_kp_r + 2 - bits_per_limb) + 2
        // ``
        constraints += (num_groups - 1) * (3 + bits_per_limb + surfeit_kp_r) + 2;
                
        if first || constraints < min_cost {
            first = false;
            min_cost = constraints;
            min_cost_limb_size = bits_per_limb;
            min_cost_num_of_limbs = num_limbs;
        }
        bits_per_limb += 1;
    }

    (min_cost_num_of_limbs, min_cost_limb_size, min_cost)
}
