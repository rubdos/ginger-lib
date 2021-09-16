//! A module for simulating the group arithmetics of short Weierstrass curves 
//! over non-native fields. 
pub mod nonnative_group_gadget;

#[cfg(test)]
mod tests;

// TODO: Adopt a similar structure as for the module ../group/curves