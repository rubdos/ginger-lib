use crate::bits::{boolean::Boolean, uint8::UInt8};
use algebra::Field;
use r1cs_core::{ConstraintSystem, SynthesisError};

pub mod boolean;
pub mod uint32;
pub mod uint64;
pub mod uint8;

pub trait ToBitsGadget<ConstraintF: Field> {
    fn to_bits<CS: ConstraintSystem<ConstraintF>>(
        &self,
        cs: CS,
    ) -> Result<Vec<Boolean>, SynthesisError>;

    /// Additionally checks if the produced list of booleans is 'valid'.
    fn to_bits_strict<CS: ConstraintSystem<ConstraintF>>(
        &self,
        cs: CS,
    ) -> Result<Vec<Boolean>, SynthesisError>;

    /// Outputs the little-endian bit representation of `Self`
    fn to_bits_le<CS: ConstraintSystemAbstract<ConstraintF>>(
        &self,
        cs: CS,
    ) -> Result<Vec<Boolean>, SynthesisError> {
        let mut bits = self.to_bits(cs)?;
        bits.reverse();
        Ok(bits)
    }

    /// Converts `Self` to little-endian bit representation, checking if the bit representation is
    /// 'valid'
    fn to_bits_strict_le<CS: ConstraintSystemAbstract<ConstraintF>>(
        &self,
        cs: CS,
     ) -> Result<Vec<Boolean>, SynthesisError> {
        let mut bits = self.to_bits_strict(cs)?;
        bits.reverse();
        Ok(bits)
    }
}

pub trait FromBitsGadget<ConstraintF: Field>
where
    Self: Sized,
{
    /// Given a bit representation `bits` of bit len not bigger than CAPACITY
    /// (i.e. MODULUS - 1) of `Self` in *big endian* form, reconstructs a `Self`.
    fn from_bits<CS: ConstraintSystem<ConstraintF>>(
        cs: CS,
        bits: &[Boolean],
    ) -> Result<Self, SynthesisError>;

    /// Reconstruct a `Self` from its *little endian* bit representation `bits` of bit len not
    /// higher than CAPACITY (i.e. MODULUS - 1)
    fn from_bits_le<CS: ConstraintSystemAbstract<ConstraintF>>(
        cs: CS,
        bits: &[Boolean],
    ) -> Result<Self, SynthesisError> {
        let big_endian_bits: Vec<_> = bits.iter().rev().map(|el| *el).collect();
        Self::from_bits(cs, &big_endian_bits)
    }
}

impl<ConstraintF: Field> ToBitsGadget<ConstraintF> for Boolean {
    fn to_bits<CS: ConstraintSystem<ConstraintF>>(
        &self,
        _: CS,
    ) -> Result<Vec<Boolean>, SynthesisError> {
        Ok(vec![*self])
    }

    fn to_bits_strict<CS: ConstraintSystem<ConstraintF>>(
        &self,
        _: CS,
    ) -> Result<Vec<Boolean>, SynthesisError> {
        Ok(vec![*self])
    }
}

impl<ConstraintF: Field> ToBitsGadget<ConstraintF> for [Boolean] {
    fn to_bits<CS: ConstraintSystem<ConstraintF>>(
        &self,
        _cs: CS,
    ) -> Result<Vec<Boolean>, SynthesisError> {
        Ok(self.to_vec())
    }

    fn to_bits_strict<CS: ConstraintSystem<ConstraintF>>(
        &self,
        _cs: CS,
    ) -> Result<Vec<Boolean>, SynthesisError> {
        Ok(self.to_vec())
    }
}
impl<ConstraintF: Field> ToBitsGadget<ConstraintF> for Vec<Boolean> {
    fn to_bits<CS: ConstraintSystem<ConstraintF>>(
        &self,
        _cs: CS,
    ) -> Result<Vec<Boolean>, SynthesisError> {
        Ok(self.clone())
    }

    fn to_bits_strict<CS: ConstraintSystem<ConstraintF>>(
        &self,
        _cs: CS,
    ) -> Result<Vec<Boolean>, SynthesisError> {
        Ok(self.clone())
    }
}

impl<ConstraintF: Field> ToBitsGadget<ConstraintF> for [UInt8] {
    fn to_bits<CS: ConstraintSystem<ConstraintF>>(
        &self,
        _cs: CS,
    ) -> Result<Vec<Boolean>, SynthesisError> {
        let mut result = Vec::with_capacity(&self.len() * 8);
        for byte in self {
            result.extend_from_slice(&byte.into_bits_le());
        }
        Ok(result)
    }

    fn to_bits_strict<CS: ConstraintSystem<ConstraintF>>(
        &self,
        cs: CS,
    ) -> Result<Vec<Boolean>, SynthesisError> {
        self.to_bits(cs)
    }
}

pub trait ToBytesGadget<ConstraintF: Field> {
    fn to_bytes<CS: ConstraintSystem<ConstraintF>>(
        &self,
        cs: CS,
    ) -> Result<Vec<UInt8>, SynthesisError>;

    /// Additionally checks if the produced list of booleans is 'valid'.
    fn to_bytes_strict<CS: ConstraintSystem<ConstraintF>>(
        &self,
        cs: CS,
    ) -> Result<Vec<UInt8>, SynthesisError>;
}

pub trait ToCompressedBitsGadget<ConstraintF: Field> {
    /// Enforce compression of an element through serialization of the x coordinate and storing
    /// a sign bit for the y coordinate. For GT elements we assume x <-> c1 and y <-> c0 to avoid
    /// confusion. When enforcing byte serialization of a field element, "x_in_field" and "y_in_field"
    /// flags could be set in order to enforce too that their bit representation is under the
    /// field modulus (default behaviour is both set to false).
    fn to_compressed<CS: ConstraintSystem<ConstraintF>>(
        &self,
        cs: CS,
    ) -> Result<Vec<Boolean>, SynthesisError>;
}

impl<ConstraintF: Field> ToBytesGadget<ConstraintF> for [UInt8] {
    fn to_bytes<CS: ConstraintSystem<ConstraintF>>(
        &self,
        _cs: CS,
    ) -> Result<Vec<UInt8>, SynthesisError> {
        Ok(self.to_vec())
    }

    fn to_bytes_strict<CS: ConstraintSystem<ConstraintF>>(
        &self,
        cs: CS,
    ) -> Result<Vec<UInt8>, SynthesisError> {
        self.to_bytes(cs)
    }
}

impl<'a, ConstraintF: Field, T: 'a + ToBytesGadget<ConstraintF>> ToBytesGadget<ConstraintF>
    for &'a T
{
    fn to_bytes<CS: ConstraintSystem<ConstraintF>>(
        &self,
        cs: CS,
    ) -> Result<Vec<UInt8>, SynthesisError> {
        (*self).to_bytes(cs)
    }

    fn to_bytes_strict<CS: ConstraintSystem<ConstraintF>>(
        &self,
        cs: CS,
    ) -> Result<Vec<UInt8>, SynthesisError> {
        self.to_bytes(cs)
    }
}

impl<'a, ConstraintF: Field> ToBytesGadget<ConstraintF> for &'a [UInt8] {
    fn to_bytes<CS: ConstraintSystem<ConstraintF>>(
        &self,
        _cs: CS,
    ) -> Result<Vec<UInt8>, SynthesisError> {
        Ok(self.to_vec())
    }

    fn to_bytes_strict<CS: ConstraintSystem<ConstraintF>>(
        &self,
        cs: CS,
    ) -> Result<Vec<UInt8>, SynthesisError> {
        self.to_bytes(cs)
    }
}
