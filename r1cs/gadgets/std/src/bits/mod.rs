use crate::bits::boolean::Boolean;
use algebra::{Field, PrimeField};
use r1cs_core::{ConstraintSystemAbstract, SynthesisError};
use crate::alloc::{AllocGadget, ConstantGadget};
use crate::eq::{EqGadget, MultiEq};
use crate::select::CondSelectGadget;
use std::fmt::Debug;
use std::ops::{Shl, Shr};
//use rand::{Rng, thread_rng};

pub mod boolean;

#[macro_use]
pub mod macros;
impl_uint_gadget!(U8, 8, u8, uint8);
impl_uint_gadget!(UInt64, 64, u64, uint64);
impl_uint_gadget!(UInt32, 32, u32, uint32);
impl_uint_gadget!(UInt16, 16, u16, uint16);
impl_uint_gadget!(UInt128, 128, u128, uint128);

// This type alias allows to implement byte serialization/de-serialization functions inside the
// `impl_uint_gadget` macro.
// Indeed, the macro providing implementations of UIntGadget requires to refer to the u8 gadget
// type for byte serialization/de-serialization functions. The type alias allows to employ a type
// defined outside the macro in the interface of byte serialization functions, hence allowing to
// implement them inside the `impl_uint_gadget` macro
pub type UInt8 = uint8::U8;

pub trait ToBitsGadget<ConstraintF: Field> {
    fn to_bits<CS: ConstraintSystemAbstract<ConstraintF>>(
        &self,
        cs: CS,
    ) -> Result<Vec<Boolean>, SynthesisError>;

    /// Additionally checks if the produced list of booleans is 'valid'.
    fn to_bits_strict<CS: ConstraintSystemAbstract<ConstraintF>>(
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
    fn from_bits<CS: ConstraintSystemAbstract<ConstraintF>>(
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

// this trait allows to move out rotl and rotr from UIntGadget, in turn allowing to avoid specifying
// for the compiler a field ConstraintF every time these methods are called, which requires a
// verbose syntax (e.g., UIntGadget::<ConstraintF>::rotl(&gadget_variable, i)
pub trait RotateUInt {
    /// Rotate left `self` by `by` bits.
    fn rotl(&self, by: usize) -> Self;

    /// Rotate right `self` by `by` bits.
    fn rotr(&self, by: usize) -> Self;
}

pub trait UIntGadget<ConstraintF: PrimeField, N: Sized>:
Sized
+ Clone
+ Debug
+ Eq
+ PartialEq
+ EqGadget<ConstraintF>
+ ToBitsGadget<ConstraintF>
+ FromBitsGadget<ConstraintF>
+ ToBytesGadget<ConstraintF>
+ CondSelectGadget<ConstraintF>
+ AllocGadget<N, ConstraintF>
+ ConstantGadget<N, ConstraintF>
+ Shr<usize>
+ Shl<usize>
+ RotateUInt
{
    /// XOR `self` with `other`
    fn xor<CS>(&self, cs: CS, other: &Self) -> Result<Self, SynthesisError>
        where
            CS: ConstraintSystemAbstract<ConstraintF>;

    /// OR `self` with `other`
    fn or<CS>(&self, cs: CS, other: &Self) -> Result<Self, SynthesisError>
        where
            CS: ConstraintSystemAbstract<ConstraintF>;

    /// AND `self` with `other`
    fn and<CS>(&self, cs: CS, other: &Self) -> Result<Self, SynthesisError>
        where
            CS: ConstraintSystemAbstract<ConstraintF>;

    /// Bitwise NOT of `self`
    fn not<CS>(&self, cs: CS) -> Self
        where
            CS: ConstraintSystemAbstract<ConstraintF>;



    /// Perform modular addition of several `Self` objects.
    fn addmany<CS, M>(cs: M, operands: &[Self]) -> Result<Self, SynthesisError>
        where
            CS: ConstraintSystemAbstract<ConstraintF>,
            M: ConstraintSystemAbstract<ConstraintF, Root = MultiEq<ConstraintF, CS>>;

    /// Perform modular addition of `self` and `other`. The default implementation just invokes
    /// `addmany`, it may be overridden in case addition of 2 values may be performed more
    /// efficiently than addition of n >= 3 values
    fn add<CS, M>(&self, cs: M, other: &Self) -> Result<Self, SynthesisError>
        where
            CS: ConstraintSystemAbstract<ConstraintF>,
            M: ConstraintSystemAbstract<ConstraintF, Root = MultiEq<ConstraintF, CS>>
    {
        Self::addmany(cs, &[self.clone(), other.clone()])
    }

    /// Add `self` to `other` if `cond` is True, otherwise do nothing.
    fn conditionally_add<CS, M>(
        &self,
        mut cs: M,
        cond: &Boolean,
        other: &Self
    ) -> Result<Self, SynthesisError>
        where
            CS: ConstraintSystemAbstract<ConstraintF>,
            M: ConstraintSystemAbstract<ConstraintF, Root = MultiEq<ConstraintF, CS>>
    {
        let sum = self.add(cs.ns(|| "compute sum"), other)?;
        Self::conditionally_select(cs.ns(|| "conditionally select values"), cond, &sum, self)
    }


    /// Perform addition of several `Self` objects, checking that no overflows occur.
    fn addmany_nocarry<CS, M>(cs: M, operands: &[Self]) -> Result<Self, SynthesisError>
        where
            CS: ConstraintSystemAbstract<ConstraintF>,
            M: ConstraintSystemAbstract<ConstraintF, Root = MultiEq<ConstraintF, CS>>;


    /// Perform addition of `self` and `other`, checking that no overflows occur.
    /// The default implementation just invokes `addmany`, it may be overridden in case addition
    /// of 2 values may be performed more efficiently than addition of n >= 3 values
    fn add_nocarry<CS, M>(&self, cs: M, other: &Self) -> Result<Self, SynthesisError>
        where
            CS: ConstraintSystemAbstract<ConstraintF>,
            M: ConstraintSystemAbstract<ConstraintF, Root = MultiEq<ConstraintF, CS>>
    {
        Self::addmany_nocarry(cs, &[self.clone(), other.clone()])
    }

    /// Add `self` to `other` if `cond` is True, checking that no overflows occur, otherwise do nothing.
    fn conditionally_add_nocarry<CS, M>(
        &self,
        mut cs: M,
        cond: &Boolean,
        other: &Self
    ) -> Result<Self, SynthesisError>
        where
        CS: ConstraintSystemAbstract<ConstraintF>,
        M: ConstraintSystemAbstract<ConstraintF, Root = MultiEq<ConstraintF, CS>>
    {
        let sum = self.add_nocarry(cs.ns(|| "compute sum"), other)?;
        Self::conditionally_select(cs.ns(|| "conditionally select values"), cond, &sum, self)
    }

    /// Perform modular subtraction of `other` from `self`
    fn sub<CS, M>(&self, cs: M, other: &Self) -> Result<Self, SynthesisError>
        where
            CS: ConstraintSystemAbstract<ConstraintF>,
            M: ConstraintSystemAbstract<ConstraintF, Root = MultiEq<ConstraintF, CS>>;

    /// Perform modular subtraction of `other` from `self` if `cond` is True, otherwise do nothing
    fn conditionally_sub<CS, M>(
        &self,
        mut cs: M,
        cond: &Boolean,
        other: &Self
    ) -> Result<Self, SynthesisError>
        where
            CS: ConstraintSystemAbstract<ConstraintF>,
            M: ConstraintSystemAbstract<ConstraintF, Root = MultiEq<ConstraintF, CS>>
    {
        let diff = self.sub(cs.ns(|| "sub"), other)?;
        Self::conditionally_select(cs.ns(|| "conditionally select result"), cond, &diff, self)
    }

    /// Subtract `other` from `self`, checking that no borrows occur (i.e., that self - other >= 0)
    fn sub_noborrow<CS, M>(&self, cs: M, other: &Self) -> Result<Self, SynthesisError>
        where
            CS: ConstraintSystemAbstract<ConstraintF>,
            M: ConstraintSystemAbstract<ConstraintF, Root = MultiEq<ConstraintF, CS>>;

    /// Subtract `other` from `self` if `cond` is True, checking that no borrows occur, otherwise do nothing
    fn conditionally_sub_noborrow<CS, M>(
        &self,
        mut cs: M,
        cond: &Boolean,
        other: &Self
    ) -> Result<Self, SynthesisError>
        where
            CS: ConstraintSystemAbstract<ConstraintF>,
            M: ConstraintSystemAbstract<ConstraintF, Root = MultiEq<ConstraintF, CS>>
    {
        let diff = self.sub_noborrow(cs.ns(|| "sub"), other)?;
        Self::conditionally_select(cs.ns(|| "conditionally select result"), cond, &diff, &self)
    }

    /// Perform modular multiplication of several `Self` objects.
    fn mulmany<CS>(cs: CS, operands: &[Self]) -> Result<Self, SynthesisError>
        where
            CS: ConstraintSystemAbstract<ConstraintF>;

    /// Perform modular multiplication of `self` and `other`
    fn mul<CS>(&self, cs: CS, other: &Self) -> Result<Self, SynthesisError>
        where
            CS: ConstraintSystemAbstract<ConstraintF> {
        Self::mulmany(cs, &[self.clone(), other.clone()])
    }

    /// Multiply `self` to `other` if `cond` is true, do nothing otherwise
    fn conditionally_mul<CS>(&self, mut cs: CS, cond: &Boolean, other: &Self) -> Result<Self, SynthesisError>
        where
            CS: ConstraintSystemAbstract<ConstraintF> {
        let product = self.mul(cs.ns(|| "mul values"), other)?;
        Self::conditionally_select(cs.ns(|| "cond select mul result"), cond, &product, self)
    }

    /// Perform multiplication of several `Self` objects, checking that no overflows occur
    fn mulmany_nocarry<CS>(cs: CS, operands: &[Self]) -> Result<Self, SynthesisError>
        where
            CS: ConstraintSystemAbstract<ConstraintF>;

    /// Multiply `self` to `other`, checking that no overflows occur
    fn mul_nocarry<CS>(&self, cs: CS, other: &Self) -> Result<Self, SynthesisError>
        where
            CS: ConstraintSystemAbstract<ConstraintF> {
        Self::mulmany_nocarry(cs, &[self.clone(), other.clone()])
    }

    /// Multiply `self` to `other` if `cond` is true, do nothing otherwise
    fn conditionally_mul_nocarry<CS>(&self, mut cs: CS, cond: &Boolean, other: &Self) -> Result<Self, SynthesisError>
        where
            CS: ConstraintSystemAbstract<ConstraintF> {
        let product = self.mul_nocarry(cs.ns(|| "mul values"), other)?;
        Self::conditionally_select(cs.ns(|| "cond select mul result"), cond, &product, self)
    }

}

impl<ConstraintF: Field> ToBitsGadget<ConstraintF> for Boolean {
    fn to_bits<CS: ConstraintSystemAbstract<ConstraintF>>(
        &self,
        _: CS,
    ) -> Result<Vec<Boolean>, SynthesisError> {
        Ok(vec![*self])
    }

    fn to_bits_strict<CS: ConstraintSystemAbstract<ConstraintF>>(
        &self,
        _: CS,
    ) -> Result<Vec<Boolean>, SynthesisError> {
        Ok(vec![*self])
    }
}

impl<ConstraintF: Field> ToBitsGadget<ConstraintF> for [Boolean] {
    fn to_bits<CS: ConstraintSystemAbstract<ConstraintF>>(
        &self,
        _cs: CS,
    ) -> Result<Vec<Boolean>, SynthesisError> {
        Ok(self.to_vec())
    }

    fn to_bits_strict<CS: ConstraintSystemAbstract<ConstraintF>>(
        &self,
        _cs: CS,
    ) -> Result<Vec<Boolean>, SynthesisError> {
        Ok(self.to_vec())
    }
}
impl<ConstraintF: Field> ToBitsGadget<ConstraintF> for Vec<Boolean> {
    fn to_bits<CS: ConstraintSystemAbstract<ConstraintF>>(
        &self,
        _cs: CS,
    ) -> Result<Vec<Boolean>, SynthesisError> {
        Ok(self.clone())
    }

    fn to_bits_strict<CS: ConstraintSystemAbstract<ConstraintF>>(
        &self,
        _cs: CS,
    ) -> Result<Vec<Boolean>, SynthesisError> {
        Ok(self.clone())
    }
}

impl<ConstraintF: Field> ToBitsGadget<ConstraintF> for [UInt8] {
    fn to_bits<CS: ConstraintSystemAbstract<ConstraintF>>(
        &self,
        _cs: CS,
    ) -> Result<Vec<Boolean>, SynthesisError> {
        let mut result = Vec::with_capacity(&self.len() * 8);
        for byte in self {
            result.extend_from_slice(&byte.into_bits_le());
        }
        Ok(result)
    }

    fn to_bits_strict<CS: ConstraintSystemAbstract<ConstraintF>>(
        &self,
        cs: CS,
    ) -> Result<Vec<Boolean>, SynthesisError> {
        self.to_bits(cs)
    }
}

pub trait ToBytesGadget<ConstraintF: Field> {
    fn to_bytes<CS: ConstraintSystemAbstract<ConstraintF>>(
        &self,
        cs: CS,
    ) -> Result<Vec<UInt8>, SynthesisError>;

    /// Additionally checks if the produced list of booleans is 'valid'.
    fn to_bytes_strict<CS: ConstraintSystemAbstract<ConstraintF>>(
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
    fn to_compressed<CS: ConstraintSystemAbstract<ConstraintF>>(
        &self,
        cs: CS,
    ) -> Result<Vec<Boolean>, SynthesisError>;
}

impl<ConstraintF: Field> ToBytesGadget<ConstraintF> for [UInt8] {
    fn to_bytes<CS: ConstraintSystemAbstract<ConstraintF>>(
        &self,
        _cs: CS,
    ) -> Result<Vec<UInt8>, SynthesisError> {
        Ok(self.to_vec())
    }

    fn to_bytes_strict<CS: ConstraintSystemAbstract<ConstraintF>>(
        &self,
        cs: CS,
    ) -> Result<Vec<UInt8>, SynthesisError> {
        self.to_bytes(cs)
    }
}

impl<'a, ConstraintF: Field, T: 'a + ToBytesGadget<ConstraintF>> ToBytesGadget<ConstraintF>
    for &'a T
{
    fn to_bytes<CS: ConstraintSystemAbstract<ConstraintF>>(
        &self,
        cs: CS,
    ) -> Result<Vec<UInt8>, SynthesisError> {
        (*self).to_bytes(cs)
    }

    fn to_bytes_strict<CS: ConstraintSystemAbstract<ConstraintF>>(
        &self,
        cs: CS,
    ) -> Result<Vec<UInt8>, SynthesisError> {
        self.to_bytes(cs)
    }
}

impl<'a, ConstraintF: Field> ToBytesGadget<ConstraintF> for &'a [UInt8] {
    fn to_bytes<CS: ConstraintSystemAbstract<ConstraintF>>(
        &self,
        _cs: CS,
    ) -> Result<Vec<UInt8>, SynthesisError> {
        Ok(self.to_vec())
    }

    fn to_bytes_strict<CS: ConstraintSystemAbstract<ConstraintF>>(
        &self,
        cs: CS,
    ) -> Result<Vec<UInt8>, SynthesisError> {
        self.to_bytes(cs)
    }
}
