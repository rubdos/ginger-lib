macro_rules! impl_uint_gadget {
    ($type_name: ident, $bit_size: expr, $native_type: ident, $mod_name: ident) => {
        pub mod $mod_name {

            use crate::{boolean::{Boolean, AllocatedBit}, fields::{fp::FpGadget, FieldGadget}, eq::{EqGadget, MultiEq}, ToBitsGadget, FromBitsGadget, ToBytesGadget, RotateUInt, UIntGadget, select::CondSelectGadget, bits::UInt8, Assignment, cmp::ComparisonGadget};

            use r1cs_core::{ConstraintSystemAbstract, SynthesisError, LinearCombination};
            use crate::alloc::{AllocGadget, ConstantGadget};

            use algebra::{fields::{PrimeField, FpParameters}, ToConstraintField};

            use std::{borrow::Borrow, ops::{Shl, Shr}, convert::TryInto, cmp::Ordering};


            #[derive(Clone, Debug)]
            pub struct $type_name {
                // Least significant bit_gadget first
                pub(crate) bits: Vec<Boolean>,
                pub(crate) value: Option<$native_type>,
            }

            impl $type_name {
                pub fn get_value(&self) -> Option<$native_type> {
                    self.value
                }

                pub fn constant(value: $native_type) -> Self {
                    let mut bits = Vec::with_capacity($bit_size);

                    for i in 0..$bit_size {
                        let bit = (value >> i) & 1;
                        bits.push(Boolean::constant(bit == 1));
                    }

                    Self {
                        bits,
                        value: Some(value),
                    }
                }

                pub fn alloc_vec<ConstraintF, CS, T>(
                    mut cs: CS,
                    values: &[T],
                ) -> Result<Vec<Self>, SynthesisError>
                where
                    ConstraintF: PrimeField,
                    CS: ConstraintSystemAbstract<ConstraintF>,
                    T: Into<Option<$native_type>> + Copy,
                {
                    let mut output_vec = Vec::with_capacity(values.len());
                    for (i, value) in values.iter().enumerate() {
                        let val: Option<$native_type> = Into::into(*value);
                        let alloc_val = Self::alloc(&mut cs.ns(|| format!("el_{}", i)), || val.get())?;
                        output_vec.push(alloc_val);
                    }
                    Ok(output_vec)
                }

                /// Allocates a vector of `u8`'s by first converting (chunks of) them to
                /// `ConstraintF` elements, (thus reducing the number of input allocations),
                /// and then converts this list of `ConstraintF` gadgets back into
                /// bits and then packs chunks of such into `Self`.
                fn alloc_input_vec_from_bytes<ConstraintF, CS>(
                    mut cs: CS,
                    values: &[u8],
                ) -> Result<Vec<Self>, SynthesisError>
                where
                    ConstraintF: PrimeField,
                    CS: ConstraintSystemAbstract<ConstraintF>,
                {
                    let field_elements: Vec<ConstraintF> =
                        ToConstraintField::<ConstraintF>::to_field_elements(values).unwrap();

                    let max_size = (<ConstraintF as PrimeField>::Params::CAPACITY / 8) as usize;

                    let mut allocated_bits = Vec::new();
                    for (i, (field_element, byte_chunk)) in field_elements
                        .into_iter()
                        .zip(values.chunks(max_size))
                        .enumerate()
                    {
                        let fe = FpGadget::alloc_input(&mut cs.ns(|| format!("Field element {}", i)), || {
                            Ok(field_element)
                        })?;

                        // Let's use the length-restricted variant of the ToBitsGadget to remove the
                        // padding: the padding bits are not constrained to be zero, so any field element
                        // passed as input (as long as it has the last bits set to the proper value) can
                        // satisfy the constraints. This kind of freedom might not be desiderable in
                        // recursive SNARK circuits, where the public inputs of the inner circuit are
                        // usually involved in other kind of constraints inside the wrap circuit.
                        let to_skip: usize =
                            <ConstraintF as PrimeField>::Params::MODULUS_BITS as usize - (byte_chunk.len() * 8);
                        let mut fe_bits = fe.to_bits_with_length_restriction(
                            cs.ns(|| format!("Convert fe to bits {}", i)),
                            to_skip,
                        )?;

                        // FpGadget::to_bits outputs a big-endian binary representation of
                        // fe_gadget's value, so we have to reverse it to get the little-endian
                        // form.
                        fe_bits.reverse();

                        allocated_bits.extend_from_slice(fe_bits.as_slice());
                    }

                    // pad with additional zero bits to have a number of bits which is multiple of $bit_size
                    while allocated_bits.len() % $bit_size != 0 {
                        allocated_bits.push(Boolean::constant(false));
                    }

                    // Chunk up slices of $bit_size bits into bytes.
                    Ok(allocated_bits[..]
                        .chunks($bit_size)
                        .enumerate()
                        .map(|(i, chunk)| Self::from_bits_le(cs.ns(|| format!("pack input chunk {}", i)), chunk))
                        .collect::<Result<_, SynthesisError>>()?)
                }

                /// Allocates a vector of `Self` from a slice of values of $native_type by serializing
                /// them to sequence of bytes and then converting them to a sequence of `ConstraintF`
                /// elements, (thus reducing the number of input allocations);
                ///Then,  this list of `ConstraintF` gadgets is converted back into
                /// bits and then packs chunks of such into `Self`.
                pub fn alloc_input_vec<ConstraintF, CS, T>(
                    cs: CS,
                    values: &[T],
                ) -> Result<Vec<Self>, SynthesisError>
                where
                    ConstraintF: PrimeField,
                    CS: ConstraintSystemAbstract<ConstraintF>,
                    T: Into<$native_type> + Copy,
                {
                    // convert values to vector of bytes
                    let mut values_to_bytes = Vec::new();
                    for val in values {
                        let val_bytes = Into::<$native_type>::into(*val).to_le_bytes();
                        values_to_bytes.extend_from_slice(&val_bytes[..]);
                    }
                    // alloc vector of `Self` from vector of bytes, minimizing the number of
                    // `ConstraintF` elements allocated
                    Self::alloc_input_vec_from_bytes(cs, values_to_bytes.as_slice())
                }

                /// Construct a constant vector of `Self` from a vector of `$native_type`
                pub fn constant_vec<T: Into<$native_type> + Copy>(values: &[T]) -> Vec<Self> {
                    let mut result = Vec::new();
                    for val in values {
                        result.push(Self::constant((*val).into()));
                    }
                    result
                }

                /// enforces that self >= other. This function is provided as it is much efficient
                /// in terms of constraints with respect to the default implementation of
                /// ComparisonGadget, which relies on the smaller_than functions
                pub fn enforce_greater_or_equal_than<ConstraintF, CS>(&self, mut cs: CS, other: &Self)
                -> Result<(), SynthesisError>
                where
                    ConstraintF: PrimeField,
                    CS: ConstraintSystemAbstract<ConstraintF>,
                {
                    // self >= other iff self - other does not underflow
                    let mut multi_eq = MultiEq::new(&mut cs);
                    let _ = self.sub_noborrow(&mut multi_eq, other)?;

                    Ok(())
                }

                // Return little endian representation of self. Will be removed when to_bits_le and
                // from_bits_le will be merged.
                pub fn into_bits_le(&self) -> Vec<Boolean> {
                    self.bits.to_vec()
                }

                // Construct self from its little endian bit representation. Will be removed when
                // to_bits_le and from_bits_le will be merged.
                pub fn from_bits_le<ConstraintF, CS>(cs: CS, bits: &[Boolean]) -> Result<Self, SynthesisError>
                where
                    ConstraintF: PrimeField,
                    CS: ConstraintSystemAbstract<ConstraintF>,
                {
                    let be_bits = bits.iter().rev().map(|el| *el).collect::<Vec<_>>();
                    Self::from_bits(cs, &be_bits)
                }

                // Construct Self from a little endian byte representation, provided in the form of
                // byte gadgets
                pub fn from_bytes(bytes: &[UInt8]) -> Result<Self, SynthesisError> {
                    assert!(bytes.len()*8 <= $bit_size);
                    let mut bits = Vec::with_capacity($bit_size);
                    let mut value: Option<$native_type> = Some(0);
                    for (i, byte) in bytes.iter().enumerate() {
                        value = match byte.get_value() {
                            Some(val) => value.as_mut().map(|v| {
                                let val_native_type: $native_type = val.into();
                                *v |= val_native_type << (i*8);
                                *v}),
                            None => None,
                        };
                        bits.append(&mut byte.into_bits_le());
                    }

                    // pad with 0 bits to get to $bit_size
                    while bits.len() != $bit_size {
                        bits.push(Boolean::constant(false));
                    }

                    Ok(Self{
                        bits,
                        value,
                    })
                }

                /// This function allows to multiply `self` and `other` with a variant of
                /// double & add algorithm.
                /// It is useful when the field ConstraintF is too small to employ the much more
                /// efficient algorithm employed in multiplication functions of the UIntGadget.
                /// If `no_carry` is true, then the function checks that the multiplication
                /// does not overflow, otherwise modular multiplication with no overflow checking
                /// is performed
                fn mul_with_double_and_add<ConstraintF, CS>(&self, mut cs: CS, other: &Self,
                no_carry: bool) -> Result<Self, SynthesisError>
                where
                    ConstraintF: PrimeField,
                    CS: ConstraintSystemAbstract<ConstraintF>,

                {
                    let field_bits = ConstraintF::Params::CAPACITY as usize;
                    // max_overflow_bits are the maximum number of non-zero bits a `Self` element
                    // can have to be multiplied to another `Self` without overflowing the field
                    let max_overflow_bits = field_bits - $bit_size;
                    // given a base b = 2^m, where m=2^max_overflow_bits, the `other` operand is
                    // represented in base b with digits of m bits. Then, the product self*other
                    // is computed by the following summation:
                    // sum_{i from 0 to h-1} ((self*b^i) % 2^$bit_size * digit_i), where h is the
                    // number of digits employed to represent other in base b
                    let mut coeff = self.clone(); // coeff will hold self*b^i mod 2^$bit_size for digit i
                    let mut operands = Vec::new(); // operands will accumulate all the operands of the summation
                    for (i, digit) in other.bits.chunks(max_overflow_bits).enumerate() {
                        // multiply digit to coeff over the field, since digit < b,
                        // then we are sure no field overflow will occur
                        let be_bits = digit.iter().rev().map(|bit| *bit).collect::<Vec<_>>();
                        let digit_in_field = FpGadget::<ConstraintF>::from_bits(cs.ns(|| format!("digit {} to field", i)), &be_bits[..])?;
                        let coeff_bits = coeff.to_bits(cs.ns(|| format!("unpack coeff for digit {}", i)))?;
                        let coeff_in_field = FpGadget::<ConstraintF>::from_bits(cs.ns(|| format!("coeff for digit {} to field", i)), &coeff_bits[..])?;
                        let tmp_result = coeff_in_field.mul(cs.ns(|| format!("tmp result for digit {}", i)), &digit_in_field)?;
                        let result_bits = if no_carry {
                            // ensure that tmp_result can be represented with $bit_size bits to
                            // ensure that no native type overflow has happened in the multiplication
                            tmp_result.to_bits_with_length_restriction(cs.ns(|| format!("to bits for digit {}", i)), field_bits + 1 - $bit_size)?
                        } else {
                            let result_bits = tmp_result.to_bits_with_length_restriction(cs.ns(|| format!("to bits for digit {}", i)), 1)?;
                            result_bits
                            .iter()
                            .skip(max_overflow_bits)
                            .map(|el| *el)
                            .collect::<Vec<_>>()
                        };
                        // addend is equal to coeff*digit mod 2^$bit_size
                        let addend = $type_name::from_bits(cs.ns(|| format!("packing addend for digit {}", i)), &result_bits[..])?;
                        operands.push(addend);
                        // move coeff from self*b^i mod 2^$bit_size to self*b^(i+1) mod 2^$bit_size
                        coeff = coeff.shl(max_overflow_bits);
                    }
                    let mut multi_eq = MultiEq::new(&mut cs);
                    if no_carry {
                        return $type_name::addmany_nocarry(multi_eq.ns(|| "add operands"), &operands)
                    } else {
                        return $type_name::addmany(multi_eq.ns(|| "add operands"), &operands)
                    }
                }

                /// This function allows to multiply a set of operands with a variant of
                /// double & add algorithm.
                /// It is useful when the field ConstraintF is too small to employ the much more
                /// efficient algorithm employed in multiplication functions of the UIntGadget.
                /// If `no_carry` is true, then the function checks that the multiplication
                /// does not overflow, otherwise modular multiplication with no overflow checking
                /// is performed
                fn mulmany_with_double_and_add<ConstraintF, CS>(mut cs: CS, operands: &[Self],
                no_carry: bool) -> Result<Self, SynthesisError>
                where
                    ConstraintF: PrimeField,
                    CS: ConstraintSystemAbstract<ConstraintF>,
                {
                    let mut result = operands[0].mul_with_double_and_add(cs.ns(|| "double and add first operands"), &operands[1], no_carry)?;
                    for (i, op) in operands.iter().skip(2).enumerate() {
                        result = result.mul_with_double_and_add(cs.ns(|| format!("double and add operand {}", i)),op, no_carry)?;
                    }
                    Ok(result)
                }

            }

            impl PartialEq for $type_name {
                fn eq(&self, other: &Self) -> bool {
                    self.value.is_some() && other.value.is_some() && self.value == other.value
            }
}

            impl Eq for $type_name {}

            impl<ConstraintF: PrimeField> EqGadget<ConstraintF> for $type_name {
                fn is_eq<CS: ConstraintSystemAbstract<ConstraintF>>(
                    &self,
                    cs: CS,
                    other: &Self,
                ) -> Result<Boolean, SynthesisError> {
                    self.bits.is_eq(cs, &other.bits)
                }

                fn conditional_enforce_equal<CS: ConstraintSystemAbstract<ConstraintF>>(
                    &self,
                    cs: CS,
                    other: &Self,
                    should_enforce: &Boolean,
                ) -> Result<(), SynthesisError> {
                    self.bits.conditional_enforce_equal(cs, &other.bits, should_enforce)
                }

                fn conditional_enforce_not_equal<CS: ConstraintSystemAbstract<ConstraintF>>(
                    &self,
                    cs: CS,
                    other: &Self,
                    should_enforce: &Boolean,
                ) -> Result<(), SynthesisError> {
                    self.bits.conditional_enforce_not_equal(cs, &other.bits, should_enforce)
                }
            }

            impl<ConstraintF: PrimeField> AllocGadget<$native_type, ConstraintF> for $type_name {
                fn alloc<F, T, CS>(mut cs: CS, value_gen: F) -> Result<Self, SynthesisError>
                where
                CS: ConstraintSystemAbstract<ConstraintF>,
                F: FnOnce() -> Result<T, SynthesisError>,
                T: Borrow<$native_type>
                {
                    let value = value_gen().map(|val| *val.borrow());
                    let bit_values = match value {
                        Ok(val) => {
                            let mut bits = Vec::with_capacity($bit_size);
                            for i in 0..$bit_size {
                                let bit = (val >> i) & 1;
                                bits.push(Some(bit == 1));
                            }
                            bits
                        },
                        _ => vec![None; $bit_size]
                    };

                    let bits = bit_values.into_iter().enumerate().map(|(i, val)| {
                        Ok(Boolean::from(AllocatedBit::alloc(
                            &mut cs.ns(|| format!("allocated bit_gadget {}", i)),
                            || val.ok_or(SynthesisError::AssignmentMissing)
                        )?))
                    }).collect::<Result<Vec<_>, SynthesisError>>()?;

                    Ok(Self{
                        bits,
                        value: value.ok(),
                    })
                }

                fn alloc_input<F, T, CS>(mut cs: CS, value_gen: F) -> Result<Self, SynthesisError>
                where
                CS: ConstraintSystemAbstract<ConstraintF>,
                F: FnOnce() -> Result<T, SynthesisError>,
                T: Borrow<$native_type>
                {
                    assert!($bit_size <= ConstraintF::Params::CAPACITY);
                    let mut value = None;
                    let field_element = FpGadget::<ConstraintF>::alloc_input(cs.ns(|| "alloc_input as field element"), || {
                        let val = value_gen().map(|val| *val.borrow())?;
                        value = Some(val);
                        Ok(ConstraintF::from(val))
                    })?;

                    let to_skip_bits: usize = ConstraintF::Params::MODULUS_BITS as usize - $bit_size;

                    let mut bits = field_element.to_bits_with_length_restriction(
                        &mut cs.ns(|| "field element to bits"), to_skip_bits
                    )?;

                    // need to reverse bits since to_bits_with_length_restriction generates a
                    // big-endian representation, while Self requires bits in little-endian order
                    bits.reverse();

                    Ok(Self{
                        bits,
                        value,
                    })
                }
            }

            impl<ConstraintF: PrimeField> ToBitsGadget<ConstraintF> for $type_name {
                    fn to_bits<CS: ConstraintSystemAbstract<ConstraintF>>(
                        &self,
                        _cs: CS,
                    ) -> Result<Vec<Boolean>, SynthesisError> {
                        //Need to reverse bits since to_bits must return a big-endian representation
                        let le_bits = self.bits.iter().rev().map(|el| *el).collect::<Vec<_>>();
                        Ok(le_bits)
                    }

                    fn to_bits_strict<CS: ConstraintSystemAbstract<ConstraintF>>(
                        &self,
                        cs: CS,
                    ) -> Result<Vec<Boolean>, SynthesisError> {
                        self.to_bits(cs)
                    }
            }

            impl<ConstraintF: PrimeField> FromBitsGadget<ConstraintF> for $type_name {
                fn from_bits<CS: ConstraintSystemAbstract<ConstraintF>>(
                    _cs: CS,
                    bits: &[Boolean],
                ) -> Result<Self, SynthesisError> {
                    if bits.len() != $bit_size {
                        let mut error_msg = String::from(concat!("error: building ", stringify!($type_name)));
                        error_msg.push_str(format!("from slice of {} bits", bits.len()).as_str());
                        return Err(SynthesisError::Other(error_msg))
                    }
                    let mut le_bits = Vec::with_capacity($bit_size);
                    let mut value: Option<$native_type> = Some(0);
                    for (i, el) in bits.iter().rev().enumerate() {
                        le_bits.push(*el);
                        value = match el.get_value() {
                            Some(bit) => value.as_mut().map(|v| {*v |=
                            if bit {
                                let mask: $native_type = 1;
                                mask << i
                            } else {
                                0
                            }; *v}),
                            None => None,
                        };
                    }

                    Ok(Self {
                        bits: le_bits,
                        value,
                    })
                }
            }


            impl<ConstraintF: PrimeField> ToBytesGadget<ConstraintF> for $type_name {
                fn to_bytes<CS: ConstraintSystemAbstract<ConstraintF>>(
                    &self,
                    _cs: CS,
                ) -> Result<Vec<UInt8>, SynthesisError> {
                    const NUM_BYTES: usize = $bit_size/8 + if $bit_size % 8 == 0 {0} else {1};
                    let byte_values =  match self.value {
                        Some(val) => {
                            let mut values = [None; NUM_BYTES];
                            for i in 0..NUM_BYTES {
                                let byte_value: u8 = ((val >> i*8) & 255).try_into().unwrap();
                                values[i] = Some(byte_value);
                            }
                            values
                        },
                        None => [None; NUM_BYTES]
                    };
                    Ok(self.bits.as_slice().chunks(8).zip(byte_values.iter()).map(|(el, val)| UInt8{
                        bits: el.to_vec(),
                        value: *val,
                    }).collect::<Vec<UInt8>>())
                 }

                 fn to_bytes_strict<CS: ConstraintSystemAbstract<ConstraintF>>(
                    &self,
                    cs: CS,
                ) -> Result<Vec<UInt8>, SynthesisError> {
                    self.to_bytes(cs)
                }

            }

            impl<ConstraintF: PrimeField> ConstantGadget<$native_type, ConstraintF> for $type_name {
                fn from_value<CS: ConstraintSystemAbstract<ConstraintF>>(_cs: CS, value: &$native_type) -> Self {
                    $type_name::constant(*value)
                }

                fn get_constant(&self) -> $native_type {
                    self.get_value().unwrap()
                }
            }

            impl<ConstraintF: PrimeField> CondSelectGadget<ConstraintF> for $type_name {
                fn conditionally_select<CS: ConstraintSystemAbstract<ConstraintF>>(
                    mut cs: CS,
                    cond: &Boolean,
                    first: &Self,
                    second: &Self,
                ) -> Result<Self, SynthesisError> {
                    let bits = first.bits.iter().zip(second.bits.iter()).enumerate().map(|(i, (t, f))| Boolean::conditionally_select(cs.ns(|| format!("cond select bit {}", i)), cond, t, f)).collect::<Result<Vec<_>, SynthesisError>>()?;

                    assert_eq!(bits.len(), $bit_size); // this assert should always be verified if first and second are built only with public methods

                    let value = match cond.get_value() {
                        Some(cond_bit) => if cond_bit {first.get_value()} else {second.get_value()},
                        None => None,
                    };

                    Ok(Self{
                        bits,
                        value,
                    })
                }

                fn cost() -> usize {
                    $bit_size * <Boolean as CondSelectGadget<ConstraintF>>::cost()
                }
            }

            impl Shl<usize> for $type_name {
                type Output = Self;

                fn shl(self, rhs: usize) -> Self::Output {
                    let by = if rhs >= $bit_size {
                        panic!("overflow due to left shift of {} bits for {}", rhs, stringify!($type_name));
                    } else {
                        rhs
                    };

                    let bits = vec![Boolean::constant(false); by]
                        .iter() // append rhs zeros as least significant bits
                        .chain(self.bits.iter()) // Chain existing bits as most significant bits starting from least significant ones
                        .take($bit_size) // Crop after $bit_size bits
                        .map(|el| *el)
                        .collect();

                    Self {
                        bits,
                        value: self.value.map(|v| v << by as $native_type),
                    }
                }
            }

            impl Shr<usize> for $type_name {
                type Output = Self;

                fn shr(self, rhs: usize) -> Self::Output {
                    let by = if rhs >= $bit_size {
                        panic!("overflow due to right shift of {} bits for {}", rhs, stringify!($type_name));
                    } else {
                        rhs
                    };

                    let bits = self
                    .bits
                    .iter()
                    .skip(by) // skip least significant bits which are removed by the shift
                    .chain(vec![Boolean::constant(false); by].iter()) // append zeros as most significant bits
                    .map(|el| *el)
                    .collect();

                    Self {
                        bits,
                        value: self.value.map(|v| v >> by as $native_type),
                    }
                }
            }


            impl RotateUInt for $type_name {
                fn rotl(&self, by: usize) -> Self {
                    let by = by % $bit_size;

                    let bits = self
                    .bits
                    .iter()
                    .skip($bit_size - by)
                    .chain(self.bits.iter())
                    .take($bit_size)
                    .map(|el| *el)
                    .collect();

                    Self {
                        bits,
                        value: self.value.map(|v| v.rotate_left(by as u32)),
                    }
                }

                fn rotr(&self, by: usize) -> Self {
                    let by = by % $bit_size;

                    let bits = self
                    .bits
                    .iter()
                    .skip(by)
                    .chain(self.bits.iter())
                    .take($bit_size)
                    .map(|el| *el)
                    .collect();

                    Self {
                        bits,
                        value: self.value.map(|v| v.rotate_right(by as u32)),
                    }
                }
            }

            //this macro allows to implement the binary bitwise operations already available for Booleans (i.e., XOR, OR, AND)
            macro_rules! impl_binary_bitwise_operation {
                    ($func_name: ident, $op: tt, $boolean_func: tt) =>  {
                        fn $func_name<CS: ConstraintSystemAbstract<ConstraintF>>(&self, mut cs: CS, other: &Self)
                                -> Result<Self, SynthesisError> {
                                    let bits = self.bits.iter()
                                    .zip(other.bits.iter())
                                    .enumerate()
                                    .map(|(i , (b1, b2))| Boolean::$boolean_func(cs.ns(|| format!("apply binary operation to bit {}", i)), &b1, &b2))
                                    .collect::<Result<Vec<Boolean>, SynthesisError>>()?;

                                    let value = match other.value {
                                        Some(val) => self.value.map(|v| v $op val),
                                        None => None,
                                    };

                                    Ok(Self {
                                        bits,
                                        value,
                                    })
                                }
                    }
                }

            // this macro generates the code to handle the case when too many operands are provided
            // to addmany/addmany_nocarry/mulmany/mulmany_nocarry functions.
            // The operands are split in batches of $max_num_operands elements,
            // and each batch is processed independently, aggregating the intermediate result to
            // obtain the final outcome of the operation applied to all the operands
            macro_rules! handle_numoperands_opmany {
                ($opmany_func: tt, $cs: tt, $operands: tt, $max_num_operands: tt) => {
                        // compute the aggregate result over batches of max_num_operands
                        let mut result = $type_name::$opmany_func($cs.ns(|| "first batch of operands"), &$operands[..$max_num_operands])?;
                        for (i, next_operands) in $operands[$max_num_operands..].chunks($max_num_operands-1).enumerate() {
                            let mut current_batch = vec![result];
                            current_batch.extend_from_slice(next_operands);
                            result = $type_name::$opmany_func($cs.ns(|| format!("{}-th batch of operands", i+1)), current_batch.as_slice())?;
                        }
                        return Ok(result);
                }
            }

            impl<ConstraintF: PrimeField> UIntGadget<ConstraintF, $native_type> for $type_name {

                impl_binary_bitwise_operation!(xor, ^, xor);
                impl_binary_bitwise_operation!(or, |, or);
                impl_binary_bitwise_operation!(and, &, and);

                fn not<CS: ConstraintSystemAbstract<ConstraintF>>(&self, _cs: CS) -> Self {
                    let bits = self.bits.iter().map(|el| el.not()).collect::<Vec<_>>();

                    Self {
                        bits,
                        value: self.value.map(|el| !el),
                    }
                }

                fn addmany<CS, M>(mut cs: M, operands: &[Self]) -> Result<Self, SynthesisError>
                where
                    CS: ConstraintSystemAbstract<ConstraintF>,
                    M: ConstraintSystemAbstract<ConstraintF, Root = MultiEq<ConstraintF, CS>>
                {
                    let num_operands = operands.len();
                    let field_bits = (ConstraintF::Params::CAPACITY) as usize;
                    // in this case it is not possible to enforce the correctness of the addition
                    // of at least 2 elements for the field ConstraintF
                    assert!(field_bits > $bit_size);
                    assert!(num_operands >= 2); // Weird trivial cases that should never happen

                    let overflow_bits = (num_operands as f64).log2().ceil() as usize;
                    if field_bits < $bit_size + overflow_bits {
                        // in this case addition of num_operands elements over field would overflow,
                        // thus it would not be possible to ensure the correctness of the result.
                        // Therefore, the operands are split in smaller slices, and the sum is
                        // enforced by multiple calls to addmany over these smaller slices

                        // given the field ConstraintF and the $bit_size, compute the maximum number
                        // of operands for which we can enforce correctness of the result
                        let max_overflow_bits = field_bits - $bit_size;
                        let max_num_operands = 1usize << max_overflow_bits;
                        handle_numoperands_opmany!(addmany, cs, operands, max_num_operands);
                    }

                    /*
                    Result is computed as follows:
                    Without loss of generality, consider 2 operands a, b, with their little-endian
                    bit representations, and n = $bit_size.
                    The addition is computed as ADD(a,b)=2^0a_0 + 2^1a_1 + ... + 2^(n-1)a_{n-1} +
                    2^0b_0 + 2^1b_1 + ... + 2^(n-1)b_{n-1} in the ConstraintF field.
                    Then, m = $bit_size + overflow_bits Booleans res_0,...,res_{m-1} are allocated as
                    witness, and it is enforced that ADD(a,b) == 2^0res_0 + 2^1res_1 + ... + 2^(m-1)res_{m-1}.
                    Then, the Booleans res_0,...,res_{n-1} represent the result modulo 2^n (assuming
                    that no field overflow occurs in computing ADD(a,b),
                    which is checked with the initial assertions), which is returned.
                     */


                    // result_value is the sum of all operands in the ConstraintF field,
                    // which is employed in the constraint
                    let mut result_value: Option<ConstraintF> = Some(ConstraintF::zero());
                    // modular_result_value is the sum of all operands mod 2^$bit_size,
                    // which represents the actual result of the operation
                    let mut modular_result_value: Option<$native_type> = Some(0);


                    let mut lc = LinearCombination::zero();

                    let mut all_constants = true;

                    for op in operands {
                        // compute value of the result
                        match op.value {
                            Some(val) => {
                                modular_result_value = modular_result_value.as_mut().map(|v| {
                              let (updated_val, _overflow) = v.overflowing_add($native_type::from(val)); //don't care if addition overflows
                              updated_val
                            });
                            result_value = result_value.as_mut().map(|v| {
                                let field_val = ConstraintF::from(val);
                                *v = *v + field_val;
                                *v});
                                },
                            // if at least one of the operands is unset, then the result cannot be computed
                            None => { modular_result_value = None;
                            result_value = None
                            },
                        };

                        let (current_lc, _, is_op_constant) = Boolean::bits_to_linear_combination(op.bits.iter(), CS::one());
                        lc = lc + current_lc;
                        all_constants &= is_op_constant;
                    }

                    if all_constants && result_value.is_some() {
                        return Ok($type_name::from_value(cs.ns(|| "alloc constant result"), &modular_result_value.unwrap()));
                    }

                    let result_bits = match result_value {
                        Some(f) => f.write_bits().iter().rev().map(|b| Some(*b)).collect::<Vec<_>>(),
                        None => vec![None; ConstraintF::Params::MODULUS_BITS as usize],
                    };
                    // create linear combination for result bits
                    let mut coeff = ConstraintF::one();
                    let mut result_lc = LinearCombination::zero();
                    let mut result_bits_gadgets = Vec::with_capacity($bit_size);
                    for i in 0..$bit_size+overflow_bits {
                        let alloc_bit = Boolean::alloc(cs.ns(|| format!("alloc result bit {}", i)), || result_bits[i].ok_or(SynthesisError::AssignmentMissing))?;

                        result_lc = result_lc + &alloc_bit.lc(CS::one(), coeff);

                        coeff.double_in_place();

                        if i < $bit_size {
                            // only the first $bit_size variables are useful for further operations on the result
                            result_bits_gadgets.push(alloc_bit);
                        }
                    }

                    cs.get_root().enforce_equal($bit_size+overflow_bits, &lc, &result_lc);

                    Ok(Self {
                        bits: result_bits_gadgets,
                        value: modular_result_value,
                    })
                }

                fn addmany_nocarry<CS, M>(mut cs: M, operands: &[Self]) -> Result<Self, SynthesisError>
                where
                    CS: ConstraintSystemAbstract<ConstraintF>,
                    M: ConstraintSystemAbstract<ConstraintF, Root = MultiEq<ConstraintF, CS>> {
                    let num_operands = operands.len();
                    let field_bits = (ConstraintF::Params::CAPACITY) as usize;
                    // in this case it is not possible to enforce the correctness of the addition
                    // of at least 2 elements for the field ConstraintF
                    assert!(field_bits > $bit_size);
                    assert!(num_operands >= 2); // Weird trivial cases that should never happen

                    let overflow_bits = (num_operands as f64).log2().ceil() as usize;
                    if field_bits < $bit_size + overflow_bits {
                        // in this case addition of num_operands elements over field would overflow,
                        // thus it would not be possible to ensure the correctness of the result.
                        // Therefore, the operands are split in smaller slices, and the sum is
                        // enforced by multiple calls to addmany_nocarry over these smaller slices

                        // given the field ConstraintF and the $bit_size, compute the maximum number
                        // of operands for which we can enforce correctness of the result
                        let max_overflow_bits = field_bits - $bit_size;
                        let max_num_operands = 1usize << max_overflow_bits;
                        handle_numoperands_opmany!(addmany_nocarry, cs, operands, max_num_operands);
                    }

                    /*
                    Result is computed as follows.
                    Without loss of generality, consider 2 operands a, b, with their little-endian
                    bit representations, and n = $bit_size.
                    The addition is computed as ADD(a,b)=2^0a_0 + 2^1a_1 + ... + 2^(n-1)a_{n-1} +
                    2^0b_0 + 2^1b_1 + ... + 2^(n-1)b_{n-1} in the ConstraintF field.
                    Then, n Booleans res_0,...,res_{n-1} are allocated as witness, and it is
                    enforced that ADD(a,b) == 2^0res_0 + 2^1res_1 + ... + 2^(n-1)res_{n-1}.
                    Such constraint is verified iff ADD(a,b) can be represented with at most n bits,
                    that is iff the addition does not overflow (assuming that ADD(a,b) does not
                    overflow in the field, which is checked with the initial assertions)
                    */

                    let mut result_value: Option<$native_type> = Some(0);
                    // this flag allows to verify if the addition of operands overflows, which allows
                    // to return an error in case a set of constants whose sum is overflowing is provided
                    let mut is_overflowing = false;

                    let mut lc = LinearCombination::zero();

                    let mut all_constants = true;

                    for op in operands {
                        // compute value of the result
                        result_value = match op.value {
                            Some(val) => result_value.as_mut().map(|v| {
                              let (updated_val, overflow) = v.overflowing_add($native_type::from(val));
                              is_overflowing |= overflow;
                              updated_val
                            }),
                            // if at least one of the operands is unset, then the result cannot be computed
                            None => None,
                        };

                        let (current_lc, _, is_op_constant) = Boolean::bits_to_linear_combination(op.bits.iter(), CS::one());
                        lc = lc + current_lc;
                        all_constants &= is_op_constant;
                    }

                    if all_constants && result_value.is_some() {
                        if is_overflowing {
                            return Err(SynthesisError::Unsatisfiable);
                        }
                        return Ok($type_name::from_value(cs.ns(|| "alloc constant result"), &result_value.unwrap()));
                    }
                    let result_var = $type_name::alloc(cs.ns(|| "alloc result"), || result_value.ok_or(SynthesisError::AssignmentMissing))?;

                    let (result_lc, _, _) = Boolean::bits_to_linear_combination(result_var.bits.iter(), CS::one());

                    cs.get_root().enforce_equal($bit_size, &lc, &result_lc);

                    Ok(result_var)
                }

                fn mulmany<CS>(mut cs: CS, operands: &[Self]) -> Result<Self, SynthesisError>
                where CS: ConstraintSystemAbstract<ConstraintF> {
                    let num_operands = operands.len();
                    let field_bits = (ConstraintF::Params::CAPACITY) as usize;
                    assert!(num_operands >= 2);

                    // corner case: check if all operands are constants before allocating any variable
                    let mut all_constants = true;
                    let mut result_value: Option<$native_type> = Some(1);
                    for op in operands {
                        for bit in &op.bits {
                            all_constants &= bit.is_constant();
                        }

                        result_value = match op.value {
                            Some(val) => result_value.as_mut().map(|v| v.overflowing_mul(val).0),
                            None => None,
                        }
                    }

                    if all_constants && result_value.is_some() {
                        return Ok($type_name::from_value(cs.ns(|| "alloc constant result"), &result_value.unwrap()));
                    }

                    assert!(field_bits > $bit_size); // minimum requirement on field size to compute multiplication of at least 2 elements without overflowing the field

                    if field_bits < 2*$bit_size {
                        return $type_name::mulmany_with_double_and_add(cs.ns(|| "double and add"), operands, false);
                    }

                    if field_bits < num_operands*$bit_size {
                        let max_num_operands = field_bits/$bit_size;
                        handle_numoperands_opmany!(mulmany, cs, operands, max_num_operands);
                    }


                    /*
                    Result is computed as follows.
                    Without loss of generality, consider 3 operands a, b, c and n = $bit_size.
                    The operands are converted to field gadgets fa, fb, fc employing their big-endian
                    bit representations.
                    Then, the product of all this elements over the field is computed with
                    num_operands-1 (i.e., 2 in this case) constraints:
                    - a*b=tmp
                    - tmp*c=res
                    Field gadget res is then converted to its big-endian bit representation, and only
                    the n least significant bits are returned as the result, which thus corresponds
                    to the a*b*c mod 2^n (assuming that no field overflow occurs in computing a*b*c,
                    which is checked with the initial assertions)
                    */

                    let op0_bits = operands[0].to_bits(cs.ns(|| "unpack first operand"))?;
                    let op1_bits = operands[1].to_bits(cs.ns(|| "unpack second operand"))?;
                    let field_op0 = FpGadget::<ConstraintF>::from_bits(cs.ns(|| "alloc operand 0 in field"), &op0_bits[..])?;
                    let field_op1 = FpGadget::<ConstraintF>::from_bits(cs.ns(|| "alloc operand 1 in field"), &op1_bits[..])?;
                    let mut result = field_op0.mul(cs.ns(|| "mul op0 and op1"), &field_op1)?;
                    for (i, op) in operands.iter().enumerate().skip(2) {
                        let op_bits = op.to_bits(cs.ns(|| format!("unpack operand {}", i)))?;
                        let field_op = FpGadget::<ConstraintF>::from_bits(cs.ns(|| format!("alloc operand {} in field", i)), &op_bits[..])?;
                        result = result.mul(cs.ns(|| format!("mul op {}", i)), &field_op)?;
                    }

                    let skip_leading_bits = field_bits + 1 - num_operands*$bit_size;
                    let result_bits = result.to_bits_with_length_restriction(cs.ns(|| "unpack result field element"), skip_leading_bits)?;
                    let result_lsbs = result_bits
                    .iter()
                    .skip((num_operands-1)*$bit_size)
                    .map(|el| *el)
                    .collect::<Vec<_>>();

                    $type_name::from_bits(cs.ns(|| "packing result"), &result_lsbs[..])
                }

                fn mulmany_nocarry<CS>(mut cs: CS, operands: &[Self]) -> Result<Self, SynthesisError>
                where CS: ConstraintSystemAbstract<ConstraintF> {
                    let num_operands = operands.len();
                    let field_bits = (ConstraintF::Params::CAPACITY) as usize;
                    assert!(num_operands >= 2);

                    // corner case: check if all operands are constants before allocating any variable
                    let mut all_constants = true;
                    let mut result_value: Option<$native_type> = Some(1);
                    let mut is_overflowing = false;
                    for op in operands {
                        for bit in &op.bits {
                            all_constants &= bit.is_constant();
                        }

                        result_value = match op.value {
                            Some(val) => result_value.as_mut().map(|v| {
                                let (updated_val, overflow) = v.overflowing_mul(val);
                                is_overflowing |= overflow;
                                updated_val
                            }),
                            None => None,
                        }
                    }

                    if all_constants && result_value.is_some() {
                        if is_overflowing{
                            return Err(SynthesisError::Unsatisfiable);
                        } else {
                            return Ok($type_name::from_value(cs.ns(|| "alloc constant result"), &result_value.unwrap()));
                        }
                    }

                    assert!(field_bits > $bit_size); // minimum requirement on field size to compute multiplication of at least 2 elements without overflowing the field

                    if field_bits < 2*$bit_size {
                        return $type_name::mulmany_with_double_and_add(cs.ns(|| "double and add"), operands, true);
                    }

                    if field_bits < num_operands*$bit_size {
                        let max_num_operands = field_bits/$bit_size;
                        handle_numoperands_opmany!(mulmany_nocarry, cs, operands, max_num_operands);
                    }

                    /*
                    Result is computed as follows.
                    Without loss of generality, consider 3 operands a, b, c and n = $bit_size.
                    The operands are converted to field gadgets fa, fb, fc employing their big-endian
                    bit representations.
                    Then, the product of all this elements over the field is computed with
                    num_operands-1 (i.e., 2 in this case) constraints:
                    - a*b=tmp
                    - tmp*c=res
                    Field gadget res is then converted to a big-endian bit representation employing
                    only n bits. If this conversion succeeds, then it means that a*b*c does not
                    overflow 2^n (assuming that no field overflow occurs in computing a*b*c, which
                    is checked by the initial assertions), and such n bits represent the final
                    product
                    */

                    let op0_bits = operands[0].to_bits(cs.ns(|| "unpack first operand"))?;
                    let op1_bits = operands[1].to_bits(cs.ns(|| "unpack second operand"))?;
                    let field_op0 = FpGadget::<ConstraintF>::from_bits(cs.ns(|| "alloc operand 0 in field"), &op0_bits[..])?;
                    let field_op1 = FpGadget::<ConstraintF>::from_bits(cs.ns(|| "alloc operand 1 in field"), &op1_bits[..])?;
                    let mut result = field_op0.mul(cs.ns(|| "mul op0 and op1"), &field_op1)?;
                    for (i, op) in operands.iter().enumerate().skip(2) {
                        let op_bits = op.to_bits(cs.ns(|| format!("unpack operand {}", i)))?;
                        let field_op = FpGadget::<ConstraintF>::from_bits(cs.ns(|| format!("alloc operand {} in field", i)), &op_bits[..])?;
                        result = result.mul(cs.ns(|| format!("mul op {}", i)), &field_op)?;
                    }

                    let skip_leading_bits = field_bits + 1 - $bit_size; // we want to verify that the field element for the product of operands can be represented with $bit_size bits to ensure that there is no overflow
                    let result_bits = result.to_bits_with_length_restriction(cs.ns(|| "unpack result field element"), skip_leading_bits)?;
                    assert_eq!(result_bits.len(), $bit_size);
                    $type_name::from_bits(cs.ns(|| "packing result"), &result_bits[..])
                }

                fn sub<CS, M>(&self, mut cs: M, other: &Self) -> Result<Self, SynthesisError>
                where
                    CS: ConstraintSystemAbstract<ConstraintF>,
                    M: ConstraintSystemAbstract<ConstraintF, Root = MultiEq<ConstraintF, CS>>
                {
                    // this assertion checks that the field is big enough: that is, the field must
                    // be able to represent integers up to 2^($bit_size+1)
                    assert!(ConstraintF::Params::CAPACITY > $bit_size);

                    /* Result is computed as follows.
                    Consider 2 operands a,b with their little-endian bit representations,
                    and n=$bit_size.
                    The subtraction is computed as SUB(a,b)=2^0a_0 + 2^1a_1 + ... + 2^(n-1)a_{n-1} -
                    2^0b_0 - 2^1b_1 - ... - 2^(n-1)b_{n-1} in the ConstraintF field.
                    Then, allocate n+1 bits res_0,...,res_{n} and enforce that
                    SUB(a,b) + 2^n == 2^0res_0 + 2^1res_1 + ... + 2^nres_n.
                    The addition of 2^n is useful in case other >= self to avoid
                    field underflows, which would require to allocate as many bits as the field
                    modulus. Only the first n bits are returned as the result of the
                    subtraction (since the result must be computed modulo 2^n), hence the addition
                    of 2^n has no impact on the final result
                    */

                    // max_value is a field element equal to 2^$bit_size
                    let max_value = ConstraintF::from($native_type::MAX) + ConstraintF::one();
                    // lc will be constructed as SUB(self,other)+2^$bit_size
                    let mut lc = (max_value, CS::one()).into();
                    let (self_lc, _, is_self_constant) = Boolean::bits_to_linear_combination(self.bits.iter(), CS::one());
                    let (other_lc, _, is_other_constant) = Boolean::bits_to_linear_combination(other.bits.iter(), CS::one());
                    lc = lc + self_lc - other_lc;
                    let all_constants = is_self_constant && is_other_constant;

                    // diff = self - other mod 2^$bit_size,
                    // while diff_in_field = self - other + 2^$bit_size over the ConstraintF field
                    let (diff, diff_in_field) = match (self.value, other.value) {
                        (Some(val1), Some(val2)) => {
                           let (diff, _) = val1.overflowing_sub(val2); // don't care if there is an underflow
                           let fe1 = ConstraintF::from(val1);
                           let fe2 = ConstraintF::from(val2);
                           (Some(diff), Some(fe1 - fe2 + max_value))
                        },
                        _ => (None, None),
                    };

                    if all_constants && diff.is_some() {
                        return Ok($type_name::from_value(cs.ns(|| "alloc constant result"), &diff.unwrap()));
                    }

                    // convert diff_in_field to little-endian bit representation
                    let diff_bits = match diff_in_field {
                        Some(diff) => diff.write_bits().iter().rev().map(|b| Some(*b)).collect::<Vec<_>>(),
                        None => vec![None; $bit_size+1],
                    };

                    let mut result_bits = Vec::with_capacity($bit_size);
                    // result_lc is constructed as 2^0diff_bits[0]+2^1diff_bits[1]+...+2^($bit_size)diff_bits[$bit_size]
                    let mut result_lc = LinearCombination::zero();
                    let mut coeff = ConstraintF::one();
                    for i in 0..$bit_size+1 {
                        let diff_bit = Boolean::alloc(cs.ns(|| format!("alloc diff bit {}", i)), || diff_bits[i].ok_or(SynthesisError::AssignmentMissing))?;

                        result_lc = result_lc + &diff_bit.lc(CS::one(), coeff);

                        coeff.double_in_place();

                        if i < $bit_size {
                            // only $bit_size bit are useful for the result,
                            // as the result must be modulo 2^$bit_size
                            result_bits.push(diff_bit);
                        }
                    }

                    cs.get_root().enforce_equal($bit_size+1, &lc, &result_lc);

                    Ok(Self{
                        bits: result_bits,
                        value: diff,
                    })

                }

                fn sub_noborrow<CS, M>(&self, mut cs: M, other: &Self) -> Result<Self, SynthesisError>
                where
                    CS: ConstraintSystemAbstract<ConstraintF>,
                    M: ConstraintSystemAbstract<ConstraintF, Root = MultiEq<ConstraintF, CS>>
                {
                    // this assertion checks that the field is big enough: subtraction of any 2
                    // values in $native_type must be a field element that cannot be represented as
                    // $native_type
                    assert!(ConstraintF::Params::CAPACITY > $bit_size);

                    /* Result is computed as follows.
                    Consider 2 operands a,b with their little-endian bit representations,
                    and n=$bit_size.
                    The subtraction is computed as SUB(a,b)=2^0a_0 + 2^1a_1 + ... + 2^(n-1)a_{n-1} -
                    2^0b_0 - 2^1b_1 - ... - 2^(n-1)b_{n-1} in the ConstraintF field.
                    Then, allocate n bits res_0,...,res_{n-1} and enforce that
                    SUB(a,b) == 2^0res_0 + 2^1res_1 + ... + 2^(n-1)res_{n-1}.
                    Such constraint is satisfied iff SUB(a,b) can be represented with n bits,
                    that is iff no field underflow occurs in the computation of SUB(a,b), which holds
                    iff a - b does not underflow
                     */

                    // lc is constructed as SUB(self, other)
                    let (self_lc, _, is_self_constant) = Boolean::bits_to_linear_combination(self.bits.iter(), CS::one());
                    let (other_lc, _, is_other_constant) = Boolean::bits_to_linear_combination(other.bits.iter(), CS::one());
                    let lc = self_lc - other_lc;
                    let all_constants = is_self_constant && is_other_constant;

                    let (diff, is_underflowing) = match (self.value, other.value) {
                        (Some(val1), Some(val2)) => {
                           let (diff, underflow) = val1.overflowing_sub(val2);
                            (Some(diff), underflow)
                        },
                        _ => (None, false),
                    };


                    if all_constants && diff.is_some() {
                        if is_underflowing {
                            return Err(SynthesisError::Unsatisfiable)
                        } else {
                            return Ok($type_name::from_value(cs.ns(|| "alloc constant result"), &diff.unwrap()))
                        }
                    }

                    let diff_var = Self::alloc(cs.ns(|| "alloc diff"), || diff.ok_or(SynthesisError::AssignmentMissing))?;

                    let (diff_lc, _, _) = Boolean::bits_to_linear_combination(diff_var.bits.iter(), CS::one());

                    cs.get_root().enforce_equal($bit_size, &lc, &diff_lc);

                    Ok(diff_var)
                }
            }

            impl<ConstraintF: PrimeField> ComparisonGadget<ConstraintF> for $type_name {
                fn is_smaller_than<CS: ConstraintSystemAbstract<ConstraintF>>(&self, mut cs: CS, other: &Self)
                -> Result<Boolean, SynthesisError>
                {
                    // this assertion checks that the field is big enough: subtraction of any 2
                    // values in $native_type must be a field element that cannot be represented as
                    // $native_type
                    assert!(ConstraintF::Params::CAPACITY > $bit_size);


                    /* Result is computed as follows.
                    Consider 2 operands a,b with their little-endian bit representations,
                    and n=$bit_size.
                    Compute n bits diff_0,...,diff_{n-1} which represents a - b mod 2^n employing
                    sub function, and then compute the term
                    DELTA(a,b,diff) = 2^0a_0 + 2^1a_1 + ... + 2^(n-1)a_{n-1} -
                    2^0b_0 - 2^1b_1 - ... - 2^(n-1)b_{n-1} - 2^0diff_0 - 2^1diff_1 - ...
                    - 2^(n-1)diff_{n-1} in the ConstraintF field.
                    Since diff is a field element equal to a-b mod 2^n, then it holds that
                    DELTA(a,b,diff) == 0 iff a >= b.
                    To compute the result, allocate a Boolean res and a field element v,
                    and enforces these 2 constraints:
                    - (1-res)*DELTA(a,b,diff) = 0
                    - v*DELTA(a,b,diff) == res
                    The first constraint ensures that res=1 when DELTA(a,b,diff)!=0, which holds iff
                    a < b; the second constraint ensures that res=0 when DELTA(a,b,diff)=0, which holds
                    iff a >= b. Note that to satisfy the second constraint when res=1, the prover
                    must set v to the multiplicative inverse of DELTA(a,b,diff), which necessarily
                    exists when res=1 as DELTA(a,b,diff) != 0
                     */

                    let diff_var = {
                        // add a scope for multi_eq as constraints are enforced when variable is
                        // dropped
                        let mut multi_eq = MultiEq::new(&mut cs);
                        self.sub(multi_eq.ns(|| "a - b mod 2^n"), other)?
                    };

                    let (self_lc, _, is_self_constant) = Boolean::bits_to_linear_combination(self.bits.iter(), CS::one());
                    let (other_lc, _, is_other_constant) = Boolean::bits_to_linear_combination(other.bits.iter(), CS::one());
                    let (diff_lc, _, is_diff_constant) = Boolean::bits_to_linear_combination(diff_var.bits.iter(), CS::one());

                    let delta_lc = self_lc - other_lc - diff_lc;
                    let all_constants = is_self_constant && is_other_constant && is_diff_constant;

                    let (diff_val, is_underflowing, delta) = match (self.get_value(), other.get_value()) {
                        (Some(value1), Some(value2)) => {
                            let (diff, underflow) = value1.overflowing_sub(value2);
                            // compute delta = self - other - diff in the field,
                            // where diff = self - other mod 2^$bit_size
                            let self_in_field = ConstraintF::from(value1);
                            let other_in_field = ConstraintF::from(value2);
                            let diff_in_field = ConstraintF::from(diff);
                            let delta = self_in_field - other_in_field - diff_in_field;
                            (Some(diff), Some(underflow), Some(delta))
                        },
                        _ => (None, None, None),
                    };

                    if all_constants && diff_val.is_some() {
                        return Ok(Boolean::constant(is_underflowing.unwrap()))
                    }

                    //ToDo: It should not be necessary to allocate it as a Boolean gadget,
                    // can be done when a Boolean::from(FieldGadget) will be implemented
                    let is_smaller = Boolean::alloc(cs.ns(|| "alloc result"), || is_underflowing.ok_or(SynthesisError::AssignmentMissing))?;

                    let inv = delta.map(|delta| {
                        match delta.inverse() {
                            Some(inv) => inv,
                            None => ConstraintF::one(), // delta is 0, so we can set any value
                        }
                    });

                    let inv_var = FpGadget::<ConstraintF>::alloc(cs.ns(|| "alloc inv"), || inv.ok_or(SynthesisError::AssignmentMissing))?;

                    // enforce constraints:
                    // (1 - is_smaller) * delta_lc = 0 enforces that is_smaller == 1 when delta != 0, i.e., when a < b
                    // inv * delta_lc = is_smaller enforces that is_smaller == 0 when delta == 0, i.e., when a >= b
                    cs.enforce(|| "enforce is smaller == true", |_| is_smaller.not().lc(CS::one(), ConstraintF::one()), |lc| lc + &delta_lc, |lc| lc);
                    cs.enforce(|| "enforce is smaller == false", |lc| &inv_var.get_variable() + lc, |lc| lc + &delta_lc, |_| is_smaller.lc(CS::one(), ConstraintF::one()));

                    Ok(is_smaller)
                }

                fn enforce_smaller_than<CS: ConstraintSystemAbstract<ConstraintF>>
                (&self, mut cs: CS, other: &Self) -> Result<(), SynthesisError> {
                    // first enforce that self <= other, which holds iff other - self does not underflow
                    let diff = {
                        let mut multi_eq = MultiEq::new(&mut cs);
                        other.sub_noborrow(&mut multi_eq, self)?
                    };
                    // then, enforce that other - self is non zero, which holds iff the difference
                    // has at least a non zero bit
                    Boolean::enforce_or(cs.ns(|| "enforce self != other"), &diff.bits)
                }

                // override the default implementation to exploit the fact that enforcing constraint
                // is cheaper than computing a Boolean gadget with the comparison outcome
                fn enforce_cmp<CS: ConstraintSystemAbstract<ConstraintF>>(
                    &self,
                    mut cs: CS,
                    other: &Self,
                    ordering: Ordering,
                    should_also_check_equality: bool,
                ) -> Result<(), SynthesisError> {
                    let (left, right) = match (ordering, should_also_check_equality) {
                        (Ordering::Less, false) | (Ordering::Greater, true) => (self, other),
                        (Ordering::Greater, false) | (Ordering::Less, true) => (other, self),
                        (Ordering::Equal, _) => return self.enforce_equal(cs, other),
                    };

                    if should_also_check_equality {
                        left.enforce_greater_or_equal_than(cs.ns(|| "enforce greater equal"), right)
                    } else {
                        left.enforce_smaller_than(cs.ns(|| "enforce smaller than"), right)
                    }
                }

            }



            #[cfg(test)]
            mod test {
                use super::$type_name;
                use rand::{Rng, thread_rng};
                use algebra::{fields::tweedle::Fr, Group, Field, FpParameters, PrimeField};
                use r1cs_core::{
                    ConstraintSystem, ConstraintSystemAbstract, ConstraintSystemDebugger, SynthesisMode, SynthesisError,
                };

                use std::{ops::{Shl, Shr}, cmp::Ordering, cmp::max};

                use crate::{alloc::{AllocGadget, ConstantGadget}, eq::{EqGadget, MultiEq}, boolean::Boolean, ToBitsGadget, FromBitsGadget, ToBytesGadget, RotateUInt, UIntGadget, select::CondSelectGadget, bits::UInt8, cmp::ComparisonGadget};


                fn test_uint_gadget_value(val: $native_type, alloc_val: &$type_name, check_name: &str) {
                    assert_eq!(alloc_val.get_value().unwrap(), val, "assertion on value fails for check: {}", check_name);
                    for i in 0..$bit_size {
                        assert_eq!(alloc_val.bits[i].get_value().unwrap(), (val >> i) & 1 == 1, "assertion on {} bit fails for check: {}", i, check_name);
                    }
                }

                #[derive(Copy, Clone, Debug)]
                enum OperandType {
                    True,
                    False,
                    AllocatedTrue,
                    AllocatedFalse,
                    NegatedAllocatedTrue,
                    NegatedAllocatedFalse,
                }
                #[derive(Copy, Clone, Debug)]
                enum VariableType {
                    Constant,
                    Allocated,
                    PublicInput,
                }

                static VARIABLE_TYPES: [VariableType; 3] = [
                        VariableType::Constant,
                        VariableType::Allocated,
                        VariableType::PublicInput,
                    ];

                static BOOLEAN_TYPES: [OperandType; 6] = [
                        OperandType::True,
                        OperandType::False,
                        OperandType::AllocatedTrue,
                        OperandType::AllocatedFalse,
                        OperandType::NegatedAllocatedTrue,
                        OperandType::NegatedAllocatedFalse,
                    ];

                // utility function employed to allocate either a variable, a public input or a constant
                fn alloc_fn(cs: &mut ConstraintSystem::<Fr>, name: &str, alloc_type: &VariableType, value: $native_type) -> $type_name {
                     match *alloc_type {
                        VariableType::Allocated => $type_name::alloc(cs.ns(|| name), || Ok(value)).unwrap(),
                        VariableType::PublicInput => $type_name::alloc_input(cs.ns(|| name), || Ok(value)).unwrap(),
                        VariableType::Constant => $type_name::from_value(cs.ns(|| name), &value),
                    }
                }

                // utility function employed to allocate a Boolean gadget for all possible types
                fn alloc_boolean_cond(cs: &mut ConstraintSystem::<Fr>, name: &str, alloc_type: &OperandType) -> Boolean {
                    let cs = cs.ns(|| name);

                    match alloc_type {
                        OperandType::True => Boolean::constant(true),
                        OperandType::False => Boolean::constant(false),
                        OperandType::AllocatedTrue => {
                            Boolean::alloc(cs, || Ok(true)).unwrap()
                        }
                        OperandType::AllocatedFalse => {
                            Boolean::alloc(cs, || Ok(false)).unwrap()
                        }
                        OperandType::NegatedAllocatedTrue => {
                            Boolean::alloc(cs, || Ok(true)).unwrap().not()
                        }
                        OperandType::NegatedAllocatedFalse => {
                            Boolean::alloc(cs, || Ok(false)).unwrap().not()
                        }
                    }
                }

                #[test]
                fn test_eq_gadget() {
                    let rng = &mut thread_rng();

                    let mut cs = ConstraintSystem::<Fr>::new(SynthesisMode::Debug);

                    let val: $native_type = rng.gen();

                    let witness = $type_name::alloc(cs.ns(|| "alloc value"), || Ok(val)).unwrap();
                    let public_input = $type_name::alloc(cs.ns(|| "alloc input value"), || Ok(val)).unwrap();

                    let cmp = witness.is_eq(cs.ns(|| "witness == public_input"), &public_input).unwrap();
                    assert!(cmp.get_value().unwrap());

                    witness.enforce_equal(cs.ns(|| "enforce witness == public_input"), &public_input).unwrap();
                    assert!(cs.is_satisfied());

                    witness.conditional_enforce_not_equal(cs.ns(|| "fake enforce witness != public_input"), &public_input, &Boolean::constant(false)).unwrap();
                    assert!(cs.is_satisfied()); //cs should still be satisfied as the previous inequality should not be enforced


                    let witness_ne = $type_name::alloc(cs.ns(|| "alloc value+1"), || Ok(val+1)).unwrap();

                    let cmp = witness_ne.is_neq(cs.ns(|| "val+1 != val"), &public_input).unwrap();
                    assert!(cmp.get_value().unwrap());

                    witness_ne.enforce_not_equal(cs.ns(|| "enforce val != val+1"), &public_input).unwrap();
                    assert!(cs.is_satisfied());

                    let cmp = witness.is_eq(cs.ns(|| "val == val+1"), &witness_ne).unwrap();
                    assert!(!cmp.get_value().unwrap());

                    witness.conditional_enforce_equal(cs.ns(|| "fake enforce val == val+1"), &witness_ne, &Boolean::constant(false)).unwrap();
                    assert!(cs.is_satisfied()); //cs should be satisfied since the previous equality should not be enforced

                    witness.enforce_equal(cs.ns(|| "enforce val == val+1"), &witness_ne).unwrap();
                    assert!(!cs.is_satisfied());
                    assert_eq!(cs.which_is_unsatisfied().unwrap(), "enforce val == val+1/conditionally enforce equal for chunk 0");
                }


                #[test]
                fn test_alloc() {
                    let rng = &mut thread_rng();

                    let mut cs = ConstraintSystem::<Fr>::new(SynthesisMode::Debug);

                    let val: $native_type =  rng.gen();

                    let value_gen = |val: Option<$native_type>| {
                        val.ok_or(SynthesisError::Other("no value".to_string()))
                    };

                    let alloc_var = $type_name::alloc(cs.ns(|| "alloc val"), || value_gen(Some(val))).unwrap();
                    let alloc_input_var = $type_name::alloc_input(cs.ns(|| "alloc input val"), || value_gen(Some(val))).unwrap();

                    test_uint_gadget_value(val, &alloc_var, "alloc variable");
                    test_uint_gadget_value(val, &alloc_input_var, "alloc public input");

                    //try allocating no value
                    let alloc_err = $type_name::alloc(cs.ns (|| "alloc empty val"), || value_gen(None)).unwrap_err();
                    let alloc_input_err = $type_name::alloc_input(cs.ns (|| "alloc empty input val"), || value_gen(None)).unwrap_err();

                    assert!(
                        match alloc_err {
                        SynthesisError::AssignmentMissing => true,
                            _ => false,
                    }
                    );
                    assert!(
                        match alloc_input_err {
                        SynthesisError::Other(_) => true,
                            _ => false,
                    }
                    );

                    //allocating no value in cs in setup mode should yield no error -> unwrap should not panic
                    let mut cs = ConstraintSystem::<Fr>::new(SynthesisMode::Setup);
                    let _ = $type_name::alloc(cs.ns (|| "alloc empty val"), || value_gen(None)).unwrap();
                    let _ = $type_name::alloc_input(cs.ns (|| "alloc empty input val"), || value_gen(None)).unwrap();

                    // test constant generation
                    let const_val: $native_type = rng.gen();

                    let uint_const = $type_name::from_value(cs.ns(|| "alloc const val"), &const_val);

                    test_uint_gadget_value(const_val, &uint_const, "alloc constant");
                    assert_eq!(const_val, ConstantGadget::<$native_type, Fr>::get_constant(&uint_const));
                }

                #[test]
                fn test_alloc_vec() {
                    let rng = &mut thread_rng();

                    let mut cs = ConstraintSystem::<Fr>::new(SynthesisMode::Debug);

                    let vec_len: usize = rng.gen_range(15..30);
                    // compute values
                    let values = (0..vec_len).map(|_| rng.gen()).collect::<Vec<$native_type>>();

                    let alloc_vec = $type_name::alloc_vec(cs.ns(|| "alloc vec"), &values).unwrap();

                    for (i, (alloc_val, val)) in alloc_vec.iter().zip(values.iter()).enumerate() {
                        test_uint_gadget_value(*val, alloc_val, format!("test vec element {}", i).as_str());
                    }

                    // try allocating no values
                    let empty_values = (0..vec_len).map(|_| None).collect::<Vec<Option<$native_type>>>();

                    let alloc_err = $type_name::alloc_vec(cs.ns(|| "alloc empty vec"), &empty_values).unwrap_err();

                    assert!(
                        match alloc_err {
                        SynthesisError::AssignmentMissing => true,
                            _ => false,
                    }
                    );

                    //allocating no value in cs in setup mode should yield no error -> unwrap should not panic
                    let mut cs = ConstraintSystem::<Fr>::new(SynthesisMode::Setup);
                    let _ = $type_name::alloc_vec(cs.ns (|| "alloc empty vec"), &empty_values).unwrap();
                }

                #[test]
                fn test_alloc_input_vec() {
                    let rng = &mut thread_rng();

                    let mut cs = ConstraintSystem::<Fr>::new(SynthesisMode::Debug);

                    let vec_len: usize = rng.gen_range($bit_size..$bit_size*2);

                    // allocate input vector of VEC_LEN $native_type elements
                    let input_vec = (0..vec_len).map(|_| rng.gen()).collect::<Vec<$native_type>>();

                    let alloc_vec = $type_name::alloc_input_vec(cs.ns(|| "alloc input vec"), &input_vec).unwrap();

                    for (i, (input_value, alloc_el)) in input_vec.iter().zip(alloc_vec.iter()).enumerate() {
                        let input_el = $type_name::constant(*input_value);
                        input_el.enforce_equal(cs.ns(|| format!("eq for chunk {}", i)), &alloc_el).unwrap();
                        assert_eq!(*input_value, alloc_el.get_value().unwrap());
                    }

                    assert!(cs.is_satisfied());

                    // test allocation of vector of constants from vector of $native_type elements
                    let constant_vec = $type_name::constant_vec(&input_vec);

                    for (i, (input_value, alloc_el)) in input_vec.iter().zip(constant_vec.iter()).enumerate() {
                        let input_el = $type_name::constant(*input_value);
                        input_el.enforce_equal(cs.ns(|| format!("eq for chunk {} of constant vec", i)), &alloc_el).unwrap();
                        assert_eq!(*input_value, alloc_el.get_value().unwrap());
                    }


                     assert!(cs.is_satisfied());

                }

                #[test]
                fn test_bit_serialization() {
                    let rng = &mut thread_rng();

                    for var_type in VARIABLE_TYPES.iter() {
                        let mut cs = ConstraintSystem::<Fr>::new(SynthesisMode::Debug);

                        let val: $native_type = rng.gen();

                        let alloc_var = alloc_fn(&mut cs, "alloc var", var_type, val);

                        let bits = alloc_var.to_bits(cs.ns(|| "unpack variable")).unwrap();
                        assert_eq!(bits.len(), $bit_size, "unpacking value");

                        let reconstructed_var = $type_name::from_bits(cs.ns(|| "pack bits"), &bits).unwrap();
                        test_uint_gadget_value(val, &reconstructed_var, "packing bits");
                    }
                }

                #[test]
                fn test_byte_serialization() {
                    let rng = &mut thread_rng();

                    for var_type in VARIABLE_TYPES.iter() {
                        let mut cs = ConstraintSystem::<Fr>::new(SynthesisMode::Debug);

                        let val: $native_type = rng.gen();

                        let alloc_var = alloc_fn(&mut cs, "alloc var", var_type, val);

                        let bytes = alloc_var.to_bytes(cs.ns(|| "unpack variable")).unwrap();
                        assert_eq!(bytes.len(), $bit_size/8);

                        let reconstructed_var = $type_name::from_bytes(&bytes).unwrap();
                        test_uint_gadget_value(val, &reconstructed_var, "packing bytes");

                        let bits = alloc_var.to_bits(cs.ns(|| "unpack to bits")).unwrap();
                        for (i, (bit_chunk, byte)) in bits.chunks(8).zip(bytes.iter().rev()).enumerate() {
                            let reconstructed_byte = UInt8::from_bits(cs.ns(|| format!("pack byte {} from bits", i)),&bit_chunk).unwrap();
                            reconstructed_byte.enforce_equal(cs.ns(|| format!("check equality for byte {}", i)), byte).unwrap();
                        }
                        assert!(cs.is_satisfied());
                    }
                }

                #[test]
                fn test_from_bits() {
                    let rng = &mut thread_rng();
                    let mut cs = ConstraintSystem::<Fr>::new(SynthesisMode::Debug);

                    let mut bits = Vec::with_capacity($bit_size); // vector of Booleans
                    let mut bit_values = Vec::with_capacity($bit_size); // vector of the actual values wrapped by Booleans found in bits vector
                    for i in 0..$bit_size {
                        let bit_value: bool = rng.gen();
                        // we test all types of Booleans
                        match i % 3 {
                            0 => {
                                bit_values.push(bit_value);
                                bits.push(Boolean::Constant(bit_value))
                            },
                            1 => {
                                bit_values.push(bit_value);
                                let bit = Boolean::alloc(cs.ns(|| format!("alloc bit {}", i)), || Ok(bit_value)).unwrap();
                                bits.push(bit)
                            },
                            2 => {
                                bit_values.push(!bit_value);
                                let bit = Boolean::alloc(cs.ns(|| format!("alloc bit {}", i)), || Ok(bit_value)).unwrap();
                                bits.push(bit.not())
                            },
                            _ => {},
                            }
                    }


                    let uint_gadget = $type_name::from_bits(cs.ns(|| "pack random bits"), &bits).unwrap();
                    let value = uint_gadget.get_value().unwrap();

                    for (i, el) in uint_gadget.bits.iter().enumerate() {
                        let bit = el.get_value().unwrap();
                        assert_eq!(bit, bits[$bit_size-1-i].get_value().unwrap());
                        assert_eq!(bit, bit_values[$bit_size-1-i]);
                        assert_eq!(bit, (value >> i) & 1 == 1);
                    }

                    // check that to_bits(from_bits(bits)) == bits
                    let unpacked_bits = uint_gadget.to_bits(cs.ns(|| "unpack bits")).unwrap();

                    for (bit1, bit2) in bits.iter().zip(unpacked_bits.iter()) {
                        assert_eq!(bit1, bit2);
                    }

                    //check that an error is returned if more than $bit_size bits are unpacked
                    let mut bits = Vec::with_capacity($bit_size+1);
                    for _ in 0..$bit_size+1 {
                        bits.push(Boolean::constant(false));
                    }

                    let _ = $type_name::from_bits(cs.ns(|| "unpacking too many bits"), &bits).unwrap_err();
                }

                #[test]
                fn test_shifts() {
                    let rng = &mut thread_rng();

                    for var_type in VARIABLE_TYPES.iter() {
                        let mut cs = ConstraintSystem::<Fr>::new(SynthesisMode::Debug);

                        let value: $native_type = rng.gen();

                        // test sequence of shifts
                        let mut alloc_var = alloc_fn(&mut cs, "alloc var", var_type, value);
                        for by in 0..$bit_size {
                            let shr_var = alloc_var.shr(by);
                            test_uint_gadget_value(value >> by, &shr_var, format!("right shift by {} bits", by).as_str());
                            alloc_var = shr_var.shl(by);
                            test_uint_gadget_value((value >> by) << by, &alloc_var, format!("left shift by {} bits", by).as_str());
                        }

                        assert!(cs.is_satisfied());

                    }
                }

                #[test]
                #[should_panic(expected="overflow due to left shift")]
                fn test_invalid_left_shift() {
                    let rng = &mut thread_rng();

                    let mut cs = ConstraintSystem::<Fr>::new(SynthesisMode::Debug);
                    let var_type = &VARIABLE_TYPES[rng.gen::<usize>() % 3];
                    let value: $native_type = rng.gen();

                    let alloc_var = alloc_fn(&mut cs, "alloc var", var_type, value);
                    let _shl_var = alloc_var.shl($bit_size*2);
                }

                #[test]
                #[should_panic(expected="overflow due to right shift")]
                fn test_invalid_right_shift() {
                    let rng = &mut thread_rng();

                    let mut cs = ConstraintSystem::<Fr>::new(SynthesisMode::Debug);
                    let var_type = &VARIABLE_TYPES[rng.gen::<usize>() % 3];
                    let value: $native_type = rng.gen();

                    let alloc_var = alloc_fn(&mut cs, "alloc var", var_type, value);
                    let _shl_var = alloc_var.shr($bit_size*2);
                }

                #[test]
                fn test_rotations() {
                    let rng = &mut thread_rng();

                    for var_type in VARIABLE_TYPES.iter() {
                        let mut cs = ConstraintSystem::<Fr>::new(SynthesisMode::Debug);

                        let value: $native_type = rng.gen();

                        let alloc_var = alloc_fn(&mut cs, "alloc var", var_type, value);
                        for i in 0..$bit_size {
                            let rotl_var = alloc_var.rotl(i);
                            test_uint_gadget_value(value.rotate_left(i as u32), &rotl_var, format!("left rotation by {}", i).as_str());
                            let rotr_var = rotl_var.rotr(i);
                            test_uint_gadget_value(value, &rotr_var, format!("right rotation by {}", i).as_str());
                        }

                        //check rotations are ok even if by > $bit_size
                        let by = $bit_size*2;
                        let rotl_var = alloc_var.rotl(by);
                        test_uint_gadget_value(value.rotate_left(by as u32), &rotl_var, format!("left rotation by {}", by).as_str());

                        let rotr_var = alloc_var.rotl(by);
                        test_uint_gadget_value(value.rotate_right(by as u32), &rotr_var, format!("right rotation by {}", by).as_str());
                    }
                }

                #[test]
                fn test_bitwise_operations() {
                    let rng = &mut thread_rng();
                    for var_type_a in VARIABLE_TYPES.iter() {
                        for var_type_b in VARIABLE_TYPES.iter() {
                            let mut cs = ConstraintSystem::<Fr>::new(SynthesisMode::Debug);

                            let a: $native_type = rng.gen();
                            let b: $native_type = rng.gen();
                            let res_xor = a ^ b;
                            let res_or = a | b;
                            let res_and = a & b;
                            let res_nand = !res_and;

                            let alloc_a = alloc_fn(&mut cs, "alloc first value", var_type_a, a);
                            let alloc_b = alloc_fn(&mut cs, "alloc second value", var_type_b, b);

                            let xor_var = alloc_a.xor(cs.ns(|| "a xor b"), &alloc_b).unwrap();
                            let or_var = alloc_a.or(cs.ns(|| "a or b"), &alloc_b).unwrap();
                            let and_var = alloc_a.and(cs.ns(|| "a and b"), &alloc_b).unwrap();
                            let nand_var = and_var.not(cs.ns(|| "a nand b"));

                            test_uint_gadget_value(res_xor, &xor_var, format!("xor between {:?} {:?}", var_type_a, var_type_b).as_str());
                            test_uint_gadget_value(res_or, &or_var, format!("or between {:?} {:?}", var_type_a, var_type_b).as_str());
                            test_uint_gadget_value(res_and, &and_var, format!("and between {:?} {:?}", var_type_a, var_type_b).as_str());
                            test_uint_gadget_value(res_nand, &nand_var, format!("nand between {:?} {:?}", var_type_a, var_type_b).as_str());

                            assert!(cs.is_satisfied());
                        }
                    }
                }

                #[test]
                fn test_cond_select() {
                    let rng = &mut thread_rng();

                    //random generates a and b numbers and check all the conditions for each couple
                    for condition in BOOLEAN_TYPES.iter() {
                        for var_a_type in VARIABLE_TYPES.iter() {
                            for var_b_type in VARIABLE_TYPES.iter() {
                                let mut cs = ConstraintSystem::<Fr>::new(SynthesisMode::Debug);
                                let cond;
                                let a;
                                let b;
                                let a_val: $native_type = rng.gen();
                                let b_val: $native_type = rng.gen();
                                {
                                    cond = alloc_boolean_cond(&mut cs, "cond", condition);
                                }
                                {
                                    a = alloc_fn(&mut cs, "var_a",var_a_type,a_val);
                                    b = alloc_fn(&mut cs, "var_b",var_b_type,b_val);
                                }
                                let before = cs.num_constraints();
                                let c = $type_name::conditionally_select(&mut cs, &cond, &a, &b).unwrap();
                                let after = cs.num_constraints();

                                assert!(
                                    cs.is_satisfied(),
                                    "failed with operands: cond: {:?}, a: {:?}, b: {:?}",
                                    condition,
                                    a,
                                    b,
                                );
                                test_uint_gadget_value(if cond.get_value().unwrap() {
                                        a_val
                                    } else {
                                        b_val
                                    }, &c, "conditional select");

                                assert!(<$type_name as CondSelectGadget<Fr>>::cost() >= after - before);
                            }
                        }
                    }
                }

                #[test]
                fn test_addmany() {
                    const NUM_OPERANDS: usize = 10;
                    let rng = &mut thread_rng();
                    let mut cs = ConstraintSystem::<Fr>::new(SynthesisMode::Debug);

                    let operand_values = (0..NUM_OPERANDS).map(|_| rng.gen()).collect::<Vec<$native_type>>();

                    let operands = operand_values.iter().enumerate().map(|(i, val)| {
                        alloc_fn(&mut cs, format!("alloc operand {}", i).as_str(), &VARIABLE_TYPES[i % 3], *val)
                    }).collect::<Vec<_>>();

                    let result_value: $native_type = operand_values.iter().map(|el| *el).reduce(|a,b| a.overflowing_add(b).0).unwrap();

                    let result_var = {
                        // add a scope for multi_eq CS as the constraints are enforced when the variable is dropped
                        let mut multi_eq = MultiEq::new(&mut cs);
                        $type_name::addmany(multi_eq.ns(|| "add operands"), &operands).unwrap()
                    };

                    test_uint_gadget_value(result_value, &result_var, "result correctness");
                    assert!(cs.is_satisfied());

                    // negative test
                    let bit_gadget_path = "add operands/alloc result bit 0/boolean";
                    if cs.get(bit_gadget_path).is_zero() {
                        cs.set(bit_gadget_path, Fr::one());
                    } else {
                        cs.set(bit_gadget_path, Fr::zero());
                    }
                    assert!(!cs.is_satisfied());
                    assert_eq!(cs.which_is_unsatisfied().unwrap(), "multieq 0");

                    // test with all constants
                    let mut cs = ConstraintSystem::<Fr>::new(SynthesisMode::Debug);
                    let operands = operand_values.iter().enumerate().map(|(i, val)| {
                        alloc_fn(&mut cs, format!("alloc constant operand {}", i).as_str(), &VARIABLE_TYPES[0], *val)
                    }).collect::<Vec<_>>();
                    let num_constraints = cs.num_constraints();

                    let result_var = {
                        // add a scope for multi_eq CS as the constraints are enforced when the variable is dropped
                        let mut multi_eq = MultiEq::new(&mut cs);
                        $type_name::addmany(multi_eq.ns(|| "add constant operands"), &operands).unwrap()
                    };

                    test_uint_gadget_value(result_value, &result_var, "sum of constants result correctness");
                    assert!(cs.is_satisfied());
                    assert_eq!(cs.num_constraints(), num_constraints);
                }

                #[test]
                #[allow(unconditional_panic)] // otherwise test will not compile for uint128, as field is too small
                fn test_mulmany() {
                    const MAX_NUM_OPERANDS: usize = (<Fr as PrimeField>::Params::CAPACITY) as usize/$bit_size ;
                    const NUM_OPERANDS: usize = MAX_NUM_OPERANDS*2+5;
                    // we want to test a case when the operands must be split in multiple chunks
                    assert!(NUM_OPERANDS > MAX_NUM_OPERANDS);


                    let rng = &mut thread_rng();
                    let mut cs = ConstraintSystem::<Fr>::new(SynthesisMode::Debug);

                    let operand_values = (0..NUM_OPERANDS).map(|_| rng.gen()).collect::<Vec<$native_type>>();

                    let operands = operand_values.iter().enumerate().map(|(i, val)| {
                        alloc_fn(&mut cs, format!("alloc operand {}", i).as_str(), &VARIABLE_TYPES[i % 3], *val)
                    }).collect::<Vec<_>>();

                    let result_value: $native_type = operand_values.iter().map(|el| *el).reduce(|a,b| a.overflowing_mul(b).0).unwrap();

                    let result_var = $type_name::mulmany(cs.ns(|| "mul operands"), &operands).unwrap();

                    test_uint_gadget_value(result_value, &result_var, "result correctness");
                    assert!(cs.is_satisfied());


                    if MAX_NUM_OPERANDS >= 2 { // negative tests are skipped if if double and add must be used because the field is too small
                        // negative test on first batch
                        let bit_gadget_path = "mul operands/first batch of operands/unpack result field element/bit 0/boolean";
                        if cs.get(bit_gadget_path).is_zero() {
                            cs.set(bit_gadget_path, Fr::one());
                        } else {
                            cs.set(bit_gadget_path, Fr::zero());
                        }
                        assert!(!cs.is_satisfied());
                        assert_eq!(cs.which_is_unsatisfied().unwrap(), "mul operands/first batch of operands/unpack result field element/unpacking_constraint");

                        // set bit value back
                        if cs.get(bit_gadget_path).is_zero() {
                            cs.set(bit_gadget_path, Fr::one());
                        } else {
                            cs.set(bit_gadget_path, Fr::zero());
                        }
                        assert!(cs.is_satisfied());

                        // negative test on allocated field element: skip if double and add must be used because the field is too small
                        let num_batches = (NUM_OPERANDS-MAX_NUM_OPERANDS)/(MAX_NUM_OPERANDS-1);
                        let bit_gadget_path = format!("mul operands/{}-th batch of operands/unpack result field element/bit 0/boolean", num_batches);
                        if cs.get(&bit_gadget_path).is_zero() {
                            cs.set(&bit_gadget_path, Fr::one());
                        } else {
                            cs.set(&bit_gadget_path, Fr::zero());
                        }
                        assert!(!cs.is_satisfied());
                        assert_eq!(cs.which_is_unsatisfied().unwrap(), format!("mul operands/{}-th batch of operands/unpack result field element/unpacking_constraint", num_batches));

                        // set bit value back
                        if cs.get(&bit_gadget_path).is_zero() {
                            cs.set(&bit_gadget_path, Fr::one());
                        } else {
                            cs.set(&bit_gadget_path, Fr::zero());
                        }
                        assert!(cs.is_satisfied());
                    }

                    let operands = operand_values.iter().enumerate().map(|(i, val)| {
                        alloc_fn(&mut cs, format!("alloc constant operand {}", i).as_str(), &VARIABLE_TYPES[0], *val)
                    }).collect::<Vec<_>>();
                    let num_constraints = cs.num_constraints();
                    let result_var = $type_name::mulmany(cs.ns(|| "mul constant operands"), &operands).unwrap();

                    test_uint_gadget_value(result_value, &result_var, "mul of constants result correctness");
                    assert!(cs.is_satisfied());
                    // check that no additional constraints are introduced if the operands are all constant values
                    assert_eq!(cs.num_constraints(), num_constraints)

                }

                #[test]
                fn test_conditional_modular_arithmetic_operations() {
                    let rng = &mut thread_rng();
                    for condition in BOOLEAN_TYPES.iter() {
                        for var_type_op1 in VARIABLE_TYPES.iter() {
                            for var_type_op2 in VARIABLE_TYPES.iter() {
                                let mut cs = ConstraintSystem::<Fr>::new(SynthesisMode::Debug);

                                let op1: $native_type = rng.gen();
                                let op2: $native_type = rng.gen();
                                let add_result_val = op1.overflowing_add(op2).0;
                                let mul_result_val = op1.overflowing_mul(op2).0;
                                let sub_result_val = op1.overflowing_sub(op2).0;

                                let op1_var = alloc_fn(&mut cs, "alloc op1", &var_type_op1, op1);
                                let op2_var = alloc_fn(&mut cs, "alloc op2", &var_type_op2, op2);
                                let cond_var = alloc_boolean_cond(&mut cs, "alloc condition", condition);

                                let (add_result_var, sub_result_var) = {
                                    // add a scope for multi_eq CS as the constraints are enforced when the variable is dropped
                                    let mut multi_eq = MultiEq::new(&mut cs);
                                    let add_result = op1_var.conditionally_add(multi_eq.ns(|| "conditionally add"), &cond_var, &op2_var).unwrap();
                                    let sub_result = op1_var.conditionally_sub(multi_eq.ns(|| "conditionally sub"), &cond_var, &op2_var).unwrap();
                                    (add_result, sub_result)
                                };
                                let mul_result_var = op1_var.conditionally_mul(&mut cs, &cond_var, &op2_var).unwrap();

                                test_uint_gadget_value(if cond_var.get_value().unwrap() {
                                    add_result_val
                                    } else {
                                    op1
                                }, &add_result_var, "addition correctness");
                                test_uint_gadget_value(if cond_var.get_value().unwrap() {
                                    mul_result_val
                                    } else {
                                    op1
                                }, &mul_result_var, "multiplication correctness");
                                test_uint_gadget_value(if cond_var.get_value().unwrap() {
                                    sub_result_val
                                    } else {
                                    op1
                                }, &sub_result_var, "subtraction correctness");

                                assert!(cs.is_satisfied());
                            }
                        }
                    }
                }

                #[test]
                fn test_addmany_nocarry() {
                    const NUM_OPERANDS: $native_type = 10;
                    let rng = &mut thread_rng();
                    let mut cs = ConstraintSystem::<Fr>::new(SynthesisMode::Debug);

                    let max_value = $native_type::MAX/NUM_OPERANDS; // generate operands in this range to ensure no overflow occurs when summing them
                    let operand_values = (0..NUM_OPERANDS).map(|_| rng.gen_range(0..max_value)).collect::<Vec<$native_type>>();

                    let operands = operand_values.iter().enumerate().map(|(i, val)| {
                        alloc_fn(&mut cs, format!("alloc operand {}", i).as_str(), &VARIABLE_TYPES[i % 3], *val)
                    }).collect::<Vec<_>>();

                    // computation of result_value will panic in case of addition overflows, but it
                    // should never happen given how we generate operand_values
                    let result_value: $native_type = operand_values.iter().sum();

                    let result_var = {
                        // add a scope for multi_eq CS as the constraints are enforced when the variable is dropped
                        let mut multi_eq = MultiEq::new(&mut cs);
                        $type_name::addmany_nocarry(multi_eq.ns(|| "add operands"), &operands).unwrap()
                    };

                    test_uint_gadget_value(result_value, &result_var, "result correctness");
                    assert!(cs.is_satisfied());

                    // negative test
                    let bit_gadget_path = "add operands/alloc result/allocated bit_gadget 0/boolean";
                    if cs.get(bit_gadget_path).is_zero() {
                        cs.set(bit_gadget_path, Fr::one());
                    } else {
                        cs.set(bit_gadget_path, Fr::zero());
                    }
                    assert!(!cs.is_satisfied());
                    assert_eq!(cs.which_is_unsatisfied().unwrap(), "multieq 0");

                    // set bit value back
                    if cs.get(bit_gadget_path).is_zero() {
                        cs.set(bit_gadget_path, Fr::one());
                    } else {
                        cs.set(bit_gadget_path, Fr::zero());
                    }
                    assert!(cs.is_satisfied());

                    // test with all constants
                    let num_constraints = cs.num_constraints();
                    let operands = operand_values.iter().enumerate().map(|(i, val)| {
                        alloc_fn(&mut cs, format!("alloc constant operand {}", i).as_str(), &VARIABLE_TYPES[0], *val)
                    }).collect::<Vec<_>>();

                     let result_var = {
                        // add a scope for multi_eq CS as the constraints are enforced when the variable is dropped
                        let mut multi_eq = MultiEq::new(&mut cs);
                        $type_name::addmany_nocarry(multi_eq.ns(|| "add constant operands"), &operands).unwrap()
                    };

                    test_uint_gadget_value(result_value, &result_var, "sum of constants result correctness");
                    assert!(cs.is_satisfied());
                    assert_eq!(num_constraints, cs.num_constraints()); // check that no constraints are added when operands are all constants

                    // check that constraints are not satisfied in case of overflow
                    let mut cs = ConstraintSystem::<Fr>::new(SynthesisMode::Debug);
                    let operand_values = (0..NUM_OPERANDS).map(|_| rng.gen_range(max_value..=$native_type::MAX)).collect::<Vec<$native_type>>();

                    let operands = operand_values.iter().enumerate().map(|(i, val)| {
                        alloc_fn(&mut cs, format!("alloc operand {}", i).as_str(), &VARIABLE_TYPES[i % 3], *val)
                    }).collect::<Vec<_>>();

                    let mut is_overflowing = false;
                    let result_value: $native_type = operand_values.iter().map(|el| *el).reduce(|a,b| {
                        let (updated_sum, overflow) = a.overflowing_add(b);
                        is_overflowing |= overflow;
                        updated_sum
                    }).unwrap();
                    //check that the addition actually overflows, which should always happen given how we generate operand values
                    assert!(is_overflowing);

                    let result_var = {
                        // add a scope for multi_eq CS as the constraints are enforced when the variable is dropped
                        let mut multi_eq = MultiEq::new(&mut cs);
                        $type_name::addmany_nocarry(multi_eq.ns(|| "add overflowing operands"), &operands).unwrap()
                    };

                    // result should still be corrected, but constraints should not be verified
                    test_uint_gadget_value(result_value, &result_var, "result of overflowing add correctness");
                    assert!(!cs.is_satisfied(), "checking overflow constraint");
                    assert_eq!(cs.which_is_unsatisfied().unwrap(), "multieq 0");
                }

                #[test]
                #[allow(unconditional_panic)] // otherwise test will not compile for uint128, as field is too small
                fn test_mulmany_nocarry() {
                    const MAX_NUM_OPERANDS: usize = (<Fr as PrimeField>::Params::CAPACITY) as usize/$bit_size ;
                    const NUM_OPERANDS: usize = MAX_NUM_OPERANDS*2+5;

                    // we want to test a case when the operands must be split in multiple chunks
                    assert!(NUM_OPERANDS > MAX_NUM_OPERANDS);

                    let rng = &mut thread_rng();
                    let mut cs = ConstraintSystem::<Fr>::new(SynthesisMode::Debug);

                    let max_value: $native_type = 1 << ($bit_size/NUM_OPERANDS); // generate operands in this range to ensure no overflow occurs when multiplying them
                    let operand_values = (0..NUM_OPERANDS).map(|_| rng.gen_range(0..max_value)).collect::<Vec<$native_type>>();

                    let operands = operand_values.iter().enumerate().map(|(i, val)| {
                        alloc_fn(&mut cs, format!("alloc operand {}", i).as_str(), &VARIABLE_TYPES[i % 3], *val)
                    }).collect::<Vec<_>>();

                    // computation of result_value will panic in case of addition overflows, but it
                    // should never happen given how we generate operand_values
                    let result_value: $native_type = operand_values.iter().map(|el| *el).reduce(|a, b| a*b).unwrap();

                    let result_var = $type_name::mulmany_nocarry(cs.ns(|| "mul operands"), &operands).unwrap();

                    test_uint_gadget_value(result_value, &result_var, "result correctness");
                    assert!(cs.is_satisfied());

                    if MAX_NUM_OPERANDS >= 2 { // negative tests are skipped if double and add must be used because the field is too small
                        // negative test on first batch
                        let bit_gadget_path = "mul operands/first batch of operands/unpack result field element/bit 0/boolean";
                        if cs.get(bit_gadget_path).is_zero() {
                            cs.set(bit_gadget_path, Fr::one());
                        } else {
                            cs.set(bit_gadget_path, Fr::zero());
                        }
                        assert!(!cs.is_satisfied());
                        assert_eq!(cs.which_is_unsatisfied().unwrap(), "mul operands/first batch of operands/unpack result field element/unpacking_constraint");

                        // set bit value back
                        if cs.get(bit_gadget_path).is_zero() {
                            cs.set(bit_gadget_path, Fr::one());
                        } else {
                            cs.set(bit_gadget_path, Fr::zero());
                        }
                        assert!(cs.is_satisfied());

                        // negative test on allocated field element

                        let num_batches = (NUM_OPERANDS-MAX_NUM_OPERANDS)/(MAX_NUM_OPERANDS-1);
                        let bit_gadget_path = format!("mul operands/{}-th batch of operands/unpack result field element/bit 0/boolean", num_batches);
                        if cs.get(&bit_gadget_path).is_zero() {
                            cs.set(&bit_gadget_path, Fr::one());
                        } else {
                            cs.set(&bit_gadget_path, Fr::zero());
                        }
                        assert!(!cs.is_satisfied());
                        assert_eq!(cs.which_is_unsatisfied().unwrap(), format!("mul operands/{}-th batch of operands/unpack result field element/unpacking_constraint", num_batches));


                        // set bit value back
                        if cs.get(&bit_gadget_path).is_zero() {
                            cs.set(&bit_gadget_path, Fr::one());
                        } else {
                            cs.set(&bit_gadget_path, Fr::zero());
                        }
                        assert!(cs.is_satisfied());
                    }

                    // test with all constants
                    let num_constraints = cs.num_constraints();
                    let operands = operand_values.iter().enumerate().map(|(i, val)| {
                        alloc_fn(&mut cs, format!("alloc constant operand {}", i).as_str(), &VARIABLE_TYPES[0], *val)
                    }).collect::<Vec<_>>();

                    let result_var = $type_name::mulmany_nocarry(cs.ns(|| "mul constant operands"), &operands).unwrap();

                    test_uint_gadget_value(result_value, &result_var, "sum of constants result correctness");
                    assert!(cs.is_satisfied());
                    assert_eq!(num_constraints, cs.num_constraints()); // check that no constraints are added when operands are all constants

                    // check that constraints are not satisfied in case of overflow
                    let mut cs = ConstraintSystem::<Fr>::new(SynthesisMode::Debug);
                    let min_value = 1 << ($bit_size/max(MAX_NUM_OPERANDS, 2)); // generate operands higher than this value to ensure that overflow occurs when processing the first batch of operands
                    let operand_values = (0..NUM_OPERANDS).map(|_| rng.gen_range(min_value..=$native_type::MAX)).collect::<Vec<$native_type>>();

                    let operands = operand_values.iter().enumerate().map(|(i, val)| {
                        alloc_fn(&mut cs, format!("alloc operand {}", i).as_str(), &VARIABLE_TYPES[i % 3], *val)
                    }).collect::<Vec<_>>();


                    let mut is_overflowing = false;
                    let result_value: $native_type = operand_values.iter().map(|el| *el).reduce(|a,b| {
                        let (updated_sum, overflow) = a.overflowing_mul(b);
                        is_overflowing |= overflow;
                        updated_sum
                    }).unwrap();
                    //check that the multiplication actually overflows, which should always happen given how we generate operand values
                    assert!(is_overflowing);

                    let result_var = $type_name::mulmany_nocarry(cs.ns(|| "mul overflowing operands"), &operands).unwrap();

                    test_uint_gadget_value(result_value, &result_var, "result of overflowing mul correctness");
                    assert!(!cs.is_satisfied());
                    if MAX_NUM_OPERANDS >= 2 {
                        assert_eq!(cs.which_is_unsatisfied().unwrap(), "mul overflowing operands/first batch of operands/unpack result field element/unpacking_constraint");
                    } else { // double and add case
                        assert_eq!(cs.which_is_unsatisfied().unwrap(), "mul overflowing operands/double and add/double and add first operands/to bits for digit 0/unpacking_constraint");
                    }

                }

                #[test]
                fn test_conditional_no_carry_arithmetic_operations() {
                    const OPERATIONS: [&str; 2] = ["add", "mul"];
                    let rng = &mut thread_rng();
                    for condition in BOOLEAN_TYPES.iter() {
                    for var_type_op1 in VARIABLE_TYPES.iter() {
                            for var_type_op2 in VARIABLE_TYPES.iter() {
                                for op in &OPERATIONS {
                                    let mut cs = ConstraintSystem::<Fr>::new(SynthesisMode::Debug);

                                    let is_add = *op == "add";

                                    let max_value: $native_type = if is_add {
                                        $native_type::MAX/2
                                    } else {
                                        1 << ($bit_size/2)
                                    };

                                    let op1: $native_type = rng.gen_range(0..max_value);
                                    let op2: $native_type = rng.gen_range(0..max_value);
                                    let (result_val, overflow) = if is_add {
                                        op1.overflowing_add(op2)
                                    } else {
                                        op1.overflowing_mul(op2)
                                    };
                                    // check that performing op on operands do not overflow, which should never happen given how we generate the operands
                                    assert!(!overflow);


                                    let op1_var = alloc_fn(&mut cs, "alloc op1", &var_type_op1, op1);
                                    let op2_var = alloc_fn(&mut cs, "alloc op2", &var_type_op2, op2);
                                    let cond_var = alloc_boolean_cond(&mut cs, "alloc conditional", condition);

                                    let result_var = if is_add {
                                        // add a scope for multi_eq CS as the constraints are enforced when the variable is dropped
                                        let mut multi_eq = MultiEq::new(&mut cs);
                                        op1_var.conditionally_add_nocarry(&mut multi_eq, &cond_var, &op2_var).unwrap()
                                    } else {
                                        op1_var.conditionally_mul_nocarry(&mut cs, &cond_var, &op2_var).unwrap()
                                    };

                                    test_uint_gadget_value(if cond_var.get_value().unwrap() {
                                        result_val
                                        } else {
                                        op1
                                    }, &result_var, format!("{} correctness", op).as_str());
                                    assert!(cs.is_satisfied());

                                    // check that addition with overflow fails
                                    let mut cs = ConstraintSystem::<Fr>::new(SynthesisMode::Debug);

                                    let op1: $native_type = rng.gen_range(max_value..=$native_type::MAX);
                                    let op2: $native_type = rng.gen_range(max_value..=$native_type::MAX);

                                    let (result_val, overflow) = if is_add {
                                        op1.overflowing_add(op2)
                                    } else {
                                        op1.overflowing_mul(op2)
                                    };
                                    // check that addition of operands overflows, which should always happen given how we generate the operands
                                    assert!(overflow);

                                    let op1_var = alloc_fn(&mut cs, "alloc op1", &var_type_op1, op1);
                                    let op2_var = alloc_fn(&mut cs, "alloc op2", &var_type_op2, op2);
                                    let cond_var = alloc_boolean_cond(&mut cs, "alloc conditional", condition);

                                    let result = if is_add {
                                        // add a scope for multi_eq CS as the constraints are enforced when the variable is dropped
                                        let mut multi_eq = MultiEq::new(&mut cs);
                                        op1_var.conditionally_add_nocarry(multi_eq.ns(|| "conditionally add no carry"), &cond_var, &op2_var)
                                    } else {
                                        op1_var.conditionally_mul_nocarry(&mut cs, &cond_var, &op2_var)
                                    };
                                    // Need to distinguish between operands being both constant or not,
                                    // as in the former case the operation should return an error
                                    // rather than unsatisfied constraints
                                    match (var_type_op1, var_type_op2) {
                                        (VariableType::Constant, VariableType::Constant) => {
                                                match result.unwrap_err() {
                                                SynthesisError::Unsatisfiable => (),
                                                _ => assert!(false, "invalid error returned by {}", if is_add {"conditionally_add_nocarry"} else {"conditionally_mul_nocarry"})
                                            };
                                            continue;
                                        },
                                        (_, _) => (),
                                        };
                                    let result_var = result.unwrap();

                                    // result should still be correct, but constraints should not be satisfied
                                    test_uint_gadget_value(if cond_var.get_value().unwrap() {
                                        result_val
                                    } else {
                                        op1
                                    }, &result_var, format!("{} correctness", op).as_str());
                                    assert!(!cs.is_satisfied(), "checking overflow constraint for {:?} {:?} {}", var_type_op1, var_type_op2, is_add);
                                    if is_add {
                                        assert_eq!(cs.which_is_unsatisfied().unwrap(), "multieq 0");
                                    } else {
                                        let field_bits = (<Fr as PrimeField>::Params::CAPACITY) as usize;
                                        if field_bits < 2*$bit_size { // double and add case
                                            assert_eq!(cs.which_is_unsatisfied().unwrap(), "mul values/double and add/double and add first operands/to bits for digit 0/unpacking_constraint");
                                        } else {
                                            assert_eq!(cs.which_is_unsatisfied().unwrap(), "mul values/unpack result field element/unpacking_constraint");
                                        }
                                    }
                                }
                            }
                        }
                    }
                }

                #[test]
                fn test_subtraction() {
                    let rng = &mut thread_rng();
                    for condition in BOOLEAN_TYPES.iter() {
                        for var_type_op1 in VARIABLE_TYPES.iter() {
                            for var_type_op2 in VARIABLE_TYPES.iter() {
                                let mut cs = ConstraintSystem::<Fr>::new(SynthesisMode::Debug);

                                let op1: $native_type = rng.gen();
                                let op2: $native_type = rng.gen();

                                let (left, right, var_type_left, var_type_right) = match op1.cmp(&op2) {
                                    Ordering::Less => (op2, op1, &var_type_op2, &var_type_op1),
                                    Ordering::Greater | Ordering::Equal => (op1, op2, &var_type_op1, &var_type_op2),
                                };

                                // compute subtraction and check that no underflow occurs
                                let (diff, underflow) = left.overflowing_sub(right);
                                assert!(!underflow);

                                let left_op = alloc_fn(&mut cs, "alloc left op", var_type_left, left);
                                let right_op = alloc_fn(&mut cs, "alloc right op", var_type_right, right);
                                let cond_var = alloc_boolean_cond(&mut cs, "alloc conditional", condition);

                                let result_var = {
                                    // add a scope for multi_eq CS as the constraints are enforced when the variable is dropped
                                    let mut multi_eq = MultiEq::new(&mut cs);
                                    left_op.conditionally_sub_noborrow(&mut multi_eq, &cond_var, &right_op).unwrap()
                                };
                                test_uint_gadget_value(if cond_var.get_value().unwrap() {
                                    diff
                                } else {
                                    left
                                }, &result_var, "sub without underflow correctness");
                                assert!(cs.is_satisfied());

                                // check that subtraction with underflows fails
                                let mut cs = ConstraintSystem::<Fr>::new(SynthesisMode::Debug);

                                let op1: $native_type = rng.gen();
                                let op2: $native_type = rng.gen();

                                let (left, right, var_type_left, var_type_right) = match op1.cmp(&op2) {
                                    Ordering::Less => (op1, op2, &var_type_op1, &var_type_op2),
                                    Ordering::Greater => (op2, op1, &var_type_op2, &var_type_op1),
                                    Ordering::Equal => {
                                        // make left < right by choosing left=op1 and right=op2+1
                                        let (right, overflow) = op2.overflowing_add(1);
                                        if overflow {
                                            // if op2+1 overflows, then it is zero, hence swap with op1
                                            (right, op1, &var_type_op2, &var_type_op1)
                                        } else {
                                            (op1, right, &var_type_op1, &var_type_op2)
                                        }
                                    },
                                };

                                // compute subtraction and check that underflow occurs
                                let (diff, underflow) = left.overflowing_sub(right);
                                assert!(underflow);

                                let left_op = alloc_fn(&mut cs, "alloc left op", var_type_left, left);
                                let right_op = alloc_fn(&mut cs, "alloc right op", var_type_right, right);
                                let cond_var = alloc_boolean_cond(&mut cs, "alloc conditional", condition);

                                let result = {
                                    // add a scope for multi_eq CS as the constraints are enforced when the variable is dropped
                                    let mut multi_eq = MultiEq::new(&mut cs);
                                    left_op.conditionally_sub_noborrow(&mut multi_eq, &cond_var, &right_op)
                                };

                                // Need to distinguish between operands being both constant or not,
                                // as in the former case the operation should return an error
                                // rather than unsatisfied constraints
                                let result_var = match (var_type_op1, var_type_op2) {
                                    (VariableType::Constant, VariableType::Constant) => {
                                            match result.unwrap_err() {
                                            SynthesisError::Unsatisfiable => (),
                                            err => assert!(false, "invalid error returned by sub_noborrow: {}", err)
                                        };
                                        continue;
                                    },
                                    (_, _) => result.unwrap(),
                                };

                                test_uint_gadget_value(if cond_var.get_value().unwrap() {
                                    diff
                                } else {
                                    left
                                }, &result_var, "sub with underflow correctness");
                                assert!(!cs.is_satisfied());
                                assert_eq!(cs.which_is_unsatisfied().unwrap(), "multieq 0");
                            }
                        }
                    }
                }

                #[test]
                fn test_cmp_gadget() {
                    let rng = &mut thread_rng();
                    const NUM_RUNS: usize = 10;

                    // helper closure which is useful to deal with the error returned by enforce cmp
                    // function if both the operands are constant and the comparison is
                    // unsatisfiable on such constants
                    let handle_constant_operands = |cs: &ConstraintSystem::<Fr>, must_be_satisfied: bool, cmp_result: Result<(), SynthesisError>, var_type_op1: &VariableType, var_type_op2: &VariableType, is_constant: bool, assertion_label, unsatisfied_constraint| {
                        match (*var_type_op1, *var_type_op2, is_constant) {
                            (VariableType::Constant, VariableType::Constant, true) => {
                                if must_be_satisfied {
                                    cmp_result.unwrap()
                                } else {
                                    match cmp_result.unwrap_err() {
                                        SynthesisError::Unsatisfiable | SynthesisError::AssignmentMissing => assert!(true),
                                        err => assert!(false, "wrong error returned with constant operands in {}: {}", assertion_label, err),
                                    }
                                }
                            },
                            _ => {
                                cmp_result.unwrap();
                                assert!(!(cs.is_satisfied() ^ must_be_satisfied), "{} for {:?} {:?}", assertion_label, var_type_op1, var_type_op2);
                                if !must_be_satisfied {
                                    assert_eq!(cs.which_is_unsatisfied().unwrap(), unsatisfied_constraint);
                                }
                            }
                        }
                    };

                    for var_type_op1 in VARIABLE_TYPES.iter() {
                        for var_type_op2 in VARIABLE_TYPES.iter() {
                            for _ in 0..NUM_RUNS {
                                let mut cs = ConstraintSystem::<Fr>::new(SynthesisMode::Debug);

                                let a: $native_type = rng.gen();
                                let b: $native_type = rng.gen();

                                let a_var = alloc_fn(&mut cs, "alloc a", var_type_op1, a);
                                let b_var = alloc_fn(&mut cs, "alloc b", var_type_op2, b);

                                let is_smaller_var = a_var.is_smaller_than(cs.ns(|| "a < b"), &b_var).unwrap();
                                let (is_smaller, is_equal) = match a.cmp(&b) {
                                    Ordering::Less  => {
                                        assert!(is_smaller_var.get_value().unwrap());
                                        assert!(cs.is_satisfied(), "is smaller");
                                        (true, false)
                                    }
                                    Ordering::Greater => {
                                        assert!(!is_smaller_var.get_value().unwrap());
                                        assert!(cs.is_satisfied(), "is not smaller");
                                        (false, false)
                                    }
                                    Ordering::Equal => {
                                        assert!(!is_smaller_var.get_value().unwrap());
                                        assert!(cs.is_satisfied(), "is not smaller");
                                        (false, true)
                                    }
                                };

                                // test when operands are equal
                                let is_smaller_var = a_var.is_smaller_than(cs.ns(|| "a < a"), &a_var).unwrap();
                                assert!(!is_smaller_var.get_value().unwrap());
                                assert!(cs.is_satisfied());

                                // test enforce_smaller_than
                                let enforce_ret = a_var.enforce_smaller_than(cs.ns(|| "enforce a < b"), &b_var);
                                handle_constant_operands(&cs, is_smaller, enforce_ret, var_type_op1, var_type_op2, true, "enforce_smaller_than test", if is_equal {"enforce a < b/enforce self != other/enforce or"} else {"enforce a < b/multieq 0"});

                                // test equality
                                let mut cs = ConstraintSystem::<Fr>::new(SynthesisMode::Debug);
                                let a_var = alloc_fn(&mut cs, "alloc a", var_type_op1, a);
                                let enforce_ret = a_var.enforce_smaller_than(cs.ns(|| "enforce a < a"), &a_var);
                                handle_constant_operands(&cs, false, enforce_ret, var_type_op1, &VariableType::Constant, true, "enforce a < a test", "enforce a < a/enforce self != other/enforce or");

                                // test all comparisons
                                let mut cs = ConstraintSystem::<Fr>::new(SynthesisMode::Debug);
                                let a_var = alloc_fn(&mut cs, "alloc a", var_type_op1, a);
                                let b_var = alloc_fn(&mut cs, "alloc b", var_type_op2, b);
                                match a.cmp(&b) {
                                    Ordering::Less => {
                                        let enforce_res = a_var.enforce_cmp(cs.ns(|| "enforce less"), &b_var, Ordering::Less, false);
                                        handle_constant_operands(&cs, true, enforce_res, var_type_op1, var_type_op2, true, "enforce less test", "");
                                        let enforce_res = a_var.enforce_cmp(cs.ns(|| "enforce less equal"), &b_var, Ordering::Less, true);
                                        handle_constant_operands(&cs, true, enforce_res, var_type_op1, var_type_op2, true, "enforce less equal test", "");
                                    }
                                    Ordering::Greater => {
                                        let enforce_res = a_var.enforce_cmp(cs.ns(|| "enforce greater"), &b_var, Ordering::Greater, false);
                                        handle_constant_operands(&cs, true, enforce_res, var_type_op1, var_type_op2, true, "enforce greater test", "");
                                        let enforce_res = a_var.enforce_cmp(cs.ns(|| "enforce greater equal"), &b_var, Ordering::Greater, true);
                                        handle_constant_operands(&cs, true, enforce_res, var_type_op1, var_type_op2, true, "enforce greater equal test", "");
                                    }
                                    _ => {}
                                }


                                // negative test
                                match b.cmp(&a) {
                                    Ordering::Less => {
                                        let enforce_res = a_var.enforce_cmp(cs.ns(|| "enforce less"), &b_var, Ordering::Less, false);
                                        handle_constant_operands(&cs, false, enforce_res, var_type_op1, var_type_op2, true, "enforce less negative test", "enforce less/enforce smaller than/multieq 0");
                                        // reinitialize cs to test also equality
                                        let mut cs = ConstraintSystem::<Fr>::new(SynthesisMode::Debug);
                                        let a_var = alloc_fn(&mut cs, "alloc a", var_type_op1, a);
                                        let b_var = alloc_fn(&mut cs, "alloc b", var_type_op2, b);
                                        let enforce_res = a_var.enforce_cmp(cs.ns(|| "enforce less equal"),&b_var, Ordering::Less, true);
                                        handle_constant_operands(&cs, false, enforce_res, var_type_op1, var_type_op2, true, "enforce less equal negative test", "enforce less equal/enforce greater equal/multieq 0");

                                    }
                                    Ordering::Greater => {
                                        let enforce_res = a_var.enforce_cmp(cs.ns(|| "enforce greater"),&b_var, Ordering::Greater, false);
                                        handle_constant_operands(&cs, false, enforce_res, var_type_op1, var_type_op2, true, "enforce greater negative test", "enforce greater/enforce smaller than/multieq 0");
                                        // reinitialize cs to test also equality
                                        let mut cs = ConstraintSystem::<Fr>::new(SynthesisMode::Debug);
                                        let a_var = alloc_fn(&mut cs, "alloc a", var_type_op1, a);
                                        let b_var = alloc_fn(&mut cs, "alloc b", var_type_op2, b);
                                        let enforce_res = a_var.enforce_cmp(cs.ns(|| "enforce greater equal"),&b_var, Ordering::Greater, true);
                                        handle_constant_operands(&cs, false, enforce_res, var_type_op1, var_type_op2, true, "enforce greater equal negative test", "enforce greater equal/enforce greater equal/multieq 0");
                                    }
                                    _ => {}
                                }

                                // test equality with enforce_cmp
                                let mut cs = ConstraintSystem::<Fr>::new(SynthesisMode::Debug);
                                let a_var = alloc_fn(&mut cs, "alloc a", var_type_op1, a);

                                let enforce_ret = a_var.enforce_cmp(cs.ns(|| "enforce a <= a"), &a_var, Ordering::Less, true);
                                handle_constant_operands(&cs, true, enforce_ret, var_type_op1, &VariableType::Constant, true, "enforce less equal on same variable test", "");
                                let enforce_ret = a_var.enforce_cmp(cs.ns(|| "enforce a < a"), &a_var, Ordering::Less, false);
                                handle_constant_operands(&cs, false, enforce_ret, var_type_op1, &VariableType::Constant, true, "enforce less on same variable test", "enforce a < a/enforce smaller than/enforce self != other/enforce or");

                                // test conditional_enforce_cmp
                                for condition in BOOLEAN_TYPES.iter() {
                                    let mut cs = ConstraintSystem::<Fr>::new(SynthesisMode::Debug);
                                    let a: $native_type = rng.gen();
                                    let b: $native_type = rng.gen();
                                    let a_var = alloc_fn(&mut cs, "alloc a", var_type_op1, a);
                                    let b_var = alloc_fn(&mut cs, "alloc b", var_type_op2, b);
                                    let cond = alloc_boolean_cond(&mut cs, "alloc cond", condition);
                                    match a.cmp(&b) {
                                        Ordering::Less => {
                                            let enforce_res = a_var.conditional_enforce_cmp(cs.ns(|| "enforce less"), &b_var, &cond, Ordering::Less, false);
                                            handle_constant_operands(&cs, true, enforce_res, var_type_op1, var_type_op2, cond.is_constant(), "enforce less test", "");
                                            let enforce_res = a_var.conditional_enforce_cmp(cs.ns(|| "enforce less equal"), &b_var, &cond, Ordering::Less, true);
                                            handle_constant_operands(&cs, true, enforce_res, var_type_op1, var_type_op2, cond.is_constant(), "enforce less equal test", "");
                                            let enforce_res = a_var.conditional_enforce_smaller_than(cs.ns(|| "conditional enforce smaller than"), &b_var, &cond);
                                            handle_constant_operands(&cs, true, enforce_res, var_type_op1, var_type_op2, cond.is_constant(), "conditional enforce smaller than positive test", "");
                                        }
                                        Ordering::Greater => {
                                            let enforce_res = a_var.conditional_enforce_cmp(cs.ns(|| "enforce greater"), &b_var, &cond, Ordering::Greater, false);
                                            handle_constant_operands(&cs, true, enforce_res, var_type_op1, var_type_op2, cond.is_constant(), "enforce greater test", "");
                                            let enforce_res = a_var.conditional_enforce_cmp(cs.ns(|| "enforce greater equal"), &b_var, &cond, Ordering::Greater, true);
                                            handle_constant_operands(&cs, true, enforce_res, var_type_op1, var_type_op2, cond.is_constant(), "enforce greater equal test", "");
                                            let enforce_res = a_var.conditional_enforce_smaller_than(cs.ns(|| "conditional enforce smaller than"), &b_var, &cond);
                                            handle_constant_operands(&cs, !cond.get_value().unwrap(), enforce_res, var_type_op1, var_type_op2, cond.is_constant(), "conditional enforce smaller than negative test", "conditional enforce smaller than/conditional enforce is smaller/conditional_equals");
                                        }
                                        _ => {}
                                    }
                                    // negative tests
                                    let mut cs = ConstraintSystem::<Fr>::new(SynthesisMode::Debug);
                                    let a_var = alloc_fn(&mut cs, "alloc a", var_type_op1, a);
                                    let b_var = alloc_fn(&mut cs, "alloc b", var_type_op2, b);
                                    let cond = alloc_boolean_cond(&mut cs, "alloc cond", condition);
                                    match b.cmp(&a) {
                                        Ordering::Less => {
                                            let enforce_res = a_var.conditional_enforce_cmp(cs.ns(|| "enforce less"), &b_var, &cond, Ordering::Less, false);
                                            handle_constant_operands(&cs, !cond.get_value().unwrap(), enforce_res, var_type_op1, var_type_op2, cond.is_constant(), "cond enforce less negative test", "enforce less/conditional enforce cmp/conditional_equals");
                                            // reinitialize cs to test also equality
                                            let mut cs = ConstraintSystem::<Fr>::new(SynthesisMode::Debug);
                                            let a_var = alloc_fn(&mut cs, "alloc a", var_type_op1, a);
                                            let b_var = alloc_fn(&mut cs, "alloc b", var_type_op2, b);
                                            let cond = alloc_boolean_cond(&mut cs, "alloc cond", condition);
                                            let enforce_res = a_var.conditional_enforce_cmp(cs.ns(|| "enforce less equal"),&b_var, &cond, Ordering::Less, true);
                                            handle_constant_operands(&cs, !cond.get_value().unwrap(), enforce_res, var_type_op1, var_type_op2, cond.is_constant(), "cond enforce less equal negative test", "enforce less equal/conditional enforce cmp/conditional_equals");

                                        }
                                        Ordering::Greater => {
                                            let enforce_res = a_var.conditional_enforce_cmp(cs.ns(|| "enforce greater"),&b_var, &cond, Ordering::Greater, false);
                                            handle_constant_operands(&cs, !cond.get_value().unwrap(), enforce_res, var_type_op1, var_type_op2, cond.is_constant(), "cond enforce greater negative test", "enforce greater/conditional enforce cmp/conditional_equals");
                                            // reinitialize cs to test also equality
                                            let mut cs = ConstraintSystem::<Fr>::new(SynthesisMode::Debug);
                                            let a_var = alloc_fn(&mut cs, "alloc a", var_type_op1, a);
                                            let b_var = alloc_fn(&mut cs, "alloc b", var_type_op2, b);
                                            let cond = alloc_boolean_cond(&mut cs, "alloc cond", condition);
                                            let enforce_res = a_var.conditional_enforce_cmp(cs.ns(|| "enforce greater equal"),&b_var, &cond, Ordering::Greater, true);
                                            handle_constant_operands(&cs, !cond.get_value().unwrap(), enforce_res, var_type_op1, var_type_op2, cond.is_constant(), "cond enforce greater equal negative test", "enforce greater equal/conditional enforce cmp/conditional_equals");
                                        }
                                        _ => {}
                                    }
                                    // test with the same variable
                                    let mut cs = ConstraintSystem::<Fr>::new(SynthesisMode::Debug);
                                    let a_var = alloc_fn(&mut cs, "alloc a", var_type_op1, a);
                                    let cond = alloc_boolean_cond(&mut cs, "alloc cond", condition);

                                    let enforce_ret = a_var.conditional_enforce_cmp(cs.ns(|| "enforce a <= a"), &a_var, &cond, Ordering::Less, true);
                                    handle_constant_operands(&cs, true, enforce_ret, var_type_op1, &VariableType::Constant, cond.is_constant(), "cond enforce less equal on same variable test", "");
                                    let enforce_ret = a_var.conditional_enforce_cmp(cs.ns(|| "conditional enforce a > a"), &a_var, &cond, Ordering::Greater, false);
                                    handle_constant_operands(&cs, !cond.get_value().unwrap(), enforce_ret, var_type_op1, &VariableType::Constant, cond.is_constant(), "cond enforce grater on same variable test", "conditional enforce a > a/conditional enforce cmp/conditional_equals");
                                    // reinitialize cs to test also enforce_smaller_than
                                    let mut cs = ConstraintSystem::<Fr>::new(SynthesisMode::Debug);
                                    let a_var = alloc_fn(&mut cs, "alloc a", var_type_op1, a);
                                    let cond = alloc_boolean_cond(&mut cs, "alloc cond", condition);
                                    let enforce_ret = a_var.conditional_enforce_smaller_than(cs.ns(|| "conditional enforce a < a"), &a_var, &cond);
                                    handle_constant_operands(&cs, !cond.get_value().unwrap(), enforce_ret, var_type_op1, &VariableType::Constant, cond.is_constant(), "cond enforce smaller than on same variable test", "conditional enforce a < a/conditional enforce is smaller/conditional_equals");
                                }
                            }
                        }
                    }
                }

            }

            }
    }
}
