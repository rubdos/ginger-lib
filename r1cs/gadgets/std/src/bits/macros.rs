macro_rules! impl_uint_gadget {
    ($type_name: ident, $bit_size: expr, $native_type: ident, $mod_name: ident) => {
        pub mod $mod_name {

            use crate::{boolean::{Boolean, AllocatedBit}, fields::{fp::FpGadget, FieldGadget}, eq::{EqGadget, MultiEq}, ToBitsGadget, FromBitsGadget, ToBytesGadget, RotateUInt, UIntGadget, select::CondSelectGadget, bits::UInt8, Assignment};

            use r1cs_core::{ConstraintSystemAbstract, SynthesisError, LinearCombination};
            use crate::alloc::{AllocGadget, ConstantGadget};

            use algebra::{fields::{PrimeField, FpParameters}, ToConstraintField};

            use std::{borrow::Borrow, ops::{Shl, Shr}, convert::TryInto};


            //ToDo: remove public use of fields
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
                pub fn alloc_input_vec<ConstraintF, CS>(
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

                /// Construct a constant vector of `Self` from a vector of `u8`
                pub fn constant_vec(values: &[u8]) -> Vec<Self> {
                    const BYTES_PER_ELEMENT: usize = $bit_size/8;
                    let mut result = Vec::new();
                    for bytes in values.chunks(BYTES_PER_ELEMENT) {
                        let mut value: $native_type = 0;
                        for (i, byte) in bytes.iter().enumerate() {
                            let byte: $native_type = (*byte).into();
                            value |= byte << (i*8);
                        }
                        result.push(Self::constant(value));
                    }
                    result
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

                //ToDO: check if the default implementation is better than the probably buggy one for [Boolean]
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
                    let mut value = None;
                    //ToDo: verify if ConstraintF must be a PrimeField
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
                    let bits = first.bits.iter().zip(second.bits.iter()).enumerate().map(|(i, (t, f))| Boolean::conditionally_select(&mut cs.ns(|| format!("cond select bit {}", i)), cond, t, f)).collect::<Result<Vec<_>, SynthesisError>>()?;

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
                        $bit_size-1
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
                        $bit_size-1
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
                                    .map(|(i , (b1, b2))| Boolean::$boolean_func(cs.ns(|| format!("xor bit {}", i)), &b1, &b2))
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
                        let num_operands = $operands.len();
                        // compute the aggregate result over batches of max_num_operands
                        let mut result = $type_name::$opmany_func($cs.ns(|| "first batch of operands"), &$operands[..$max_num_operands])?;
                        let mut operands_processed = $max_num_operands;
                        while operands_processed < num_operands {
                            let last_op_to_process = if operands_processed + $max_num_operands - 1 > num_operands {
                                num_operands
                            } else {
                                operands_processed + $max_num_operands - 1
                            };
                            let mut next_operands = $operands[operands_processed..last_op_to_process].iter().cloned().collect::<Vec<_>>();
                            next_operands.push(result);
                            result = $type_name::$opmany_func($cs.ns(|| format!("operands from {} to {}", operands_processed, last_op_to_process)), &next_operands[..])?;
                            operands_processed += $max_num_operands - 1;
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
                    let field_bits = (ConstraintF::Params::MODULUS_BITS - 1) as usize;
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

                        let mut coeff = ConstraintF::one();
                        for bit in &op.bits {
                            lc = lc + &bit.lc(CS::one(), coeff);

                            all_constants &= bit.is_constant();

                            coeff.double_in_place();
                        }
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
                    let field_bits = (ConstraintF::Params::MODULUS_BITS - 1) as usize;
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

                        let mut coeff = ConstraintF::one();
                        for bit in &op.bits {
                            lc = lc + &bit.lc(CS::one(), coeff);

                            all_constants &= bit.is_constant();

                            coeff.double_in_place();
                        }
                    }

                    if all_constants && result_value.is_some() {
                        if is_overflowing {
                            return Err(SynthesisError::Unsatisfiable);
                        }
                        return Ok($type_name::from_value(cs.ns(|| "alloc constant result"), &result_value.unwrap()));
                    }

                    let result_var = $type_name::alloc(cs.ns(|| "alloc result"), || result_value.ok_or(SynthesisError::AssignmentMissing))?;

                    let mut coeff = ConstraintF::one();
                    let mut result_lc = LinearCombination::zero();

                    for bit in result_var.bits.iter() {
                        result_lc = result_lc + &bit.lc(CS::one(), coeff);

                        coeff.double_in_place();
                    }

                    cs.get_root().enforce_equal($bit_size, &lc, &result_lc);

                    Ok(result_var)
                }

                fn mulmany<CS>(mut cs: CS, operands: &[Self]) -> Result<Self, SynthesisError>
                where CS: ConstraintSystemAbstract<ConstraintF> {
                    let num_operands = operands.len();
                    let field_bits = (ConstraintF::Params::MODULUS_BITS - 1) as usize;
                    assert!(num_operands >= 2);
                    assert!(field_bits >= 2*$bit_size); // minimum requirement on field size to compute multiplication of at least 2 elements without overflowing the field

                    if field_bits < num_operands*$bit_size {
                        let max_num_operands = field_bits/$bit_size;
                        handle_numoperands_opmany!(mulmany, cs, operands, max_num_operands);
                    }

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
                    let field_bits = (ConstraintF::Params::MODULUS_BITS - 1) as usize;
                    assert!(num_operands >= 2);
                    assert!(field_bits >= 2*$bit_size); // minimum requirement on field size to compute multiplication of at least 2 elements without overflowing the field

                    if field_bits < num_operands*$bit_size {
                        let max_num_operands = field_bits/$bit_size;
                        handle_numoperands_opmany!(mulmany_nocarry, cs, operands, max_num_operands);
                    }

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

            }



            #[cfg(test)]
            mod test {
                use super::$type_name;
                use rand::{Rng, thread_rng};
                use algebra::{fields::tweedle::Fr, Group, Field, FpParameters, PrimeField};
                use r1cs_core::{
                    ConstraintSystem, ConstraintSystemAbstract, ConstraintSystemDebugger, SynthesisMode, SynthesisError,
                };

                use std::ops::{Shl, Shr};

                use crate::{alloc::{AllocGadget, ConstantGadget}, eq::{EqGadget, MultiEq}, boolean::Boolean, ToBitsGadget, FromBitsGadget, ToBytesGadget, RotateUInt, UIntGadget, select::CondSelectGadget, bits::UInt8};


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
                    println!("vec len: {}", vec_len);
                    // allocate input vector of VEC_LEN random bytes
                    let input_vec = (0..vec_len).map(|_| rng.gen()).collect::<Vec<u8>>();

                    let alloc_vec = $type_name::alloc_input_vec(cs.ns(|| "alloc input vec"), &input_vec).unwrap();

                    for (i, (input_bytes, alloc_el)) in input_vec.chunks_exact($bit_size/8).zip(alloc_vec.iter()).enumerate() {
                        let input_bytes_gadgets = UInt8::constant_vec(&input_bytes);
                        let input_el = $type_name::from_bytes(&input_bytes_gadgets).unwrap();
                        input_el.enforce_equal(cs.ns(|| format!("eq for chunk {}", i)), &alloc_el).unwrap();
                        assert_eq!(input_el.get_value().unwrap(), alloc_el.get_value().unwrap());
                    }

                    assert!(cs.is_satisfied());

                    // test allocation of vector of constants from vector of bytes
                    let constant_vec = $type_name::constant_vec(&input_vec);

                    for (i, (input_bytes, alloc_el)) in input_vec.chunks($bit_size/8).zip(constant_vec.iter()).enumerate() {
                        let input_bytes_gadgets = input_bytes.iter().enumerate()
                        .map(|(j, byte)| UInt8::from_value(cs.ns(|| format!("alloc byte {} in chunk {}", j, i)), byte))
                        .collect::<Vec<_>>();
                        let input_el = $type_name::from_bytes(&input_bytes_gadgets).unwrap();
                        input_el.enforce_equal(cs.ns(|| format!("eq for chunk {} of constant vec", i)), &alloc_el).unwrap();
                        assert_eq!(input_el.get_value().unwrap(), alloc_el.get_value().unwrap());
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



                        // check that shl(var, by) == shl(var, $bit_size-1) for by > $bit_size
                        let alloc_var = alloc_fn(&mut cs, "alloc var for invalid shl", var_type, value);
                        let by = $bit_size*2;
                        let shl_var = alloc_var.shl(by);
                        test_uint_gadget_value(value << $bit_size-1, &shl_var, "invalid left shift");

                        // check that shr(var, by) == shr(var, $bit_size) for by > $bit_size
                        let alloc_var = alloc_fn(&mut cs, "alloc var for invalid shr", var_type, value);
                        let by = $bit_size*2;
                        let shr_var = alloc_var.shr(by);
                        test_uint_gadget_value(value >> $bit_size-1, &shr_var, "invalid right shift");

                        assert!(cs.is_satisfied());
                    }
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


                            let alloc_xor = alloc_fn(&mut cs, "alloc xor result", var_type_a, res_xor);
                            let alloc_or = alloc_fn(&mut cs, "alloc or result", var_type_b, res_or);
                            let alloc_and = alloc_fn(&mut cs, "alloc and result", var_type_a, res_and);
                            let alloc_nand = alloc_fn(&mut cs, "alloc nand result", var_type_b, res_nand);

                            alloc_xor.enforce_equal(cs.ns(|| "check xor result"), &xor_var).unwrap();
                            alloc_or.enforce_equal(cs.ns(|| "check or result"), &or_var).unwrap();
                            alloc_and.enforce_equal(cs.ns(|| "check and result"), &and_var).unwrap();
                            alloc_nand.enforce_equal(cs.ns(|| "check nand result"), &nand_var).unwrap();

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
                fn test_mulmany() {
                    const MAX_NUM_OPERANDS: usize = (<Fr as PrimeField>::Params::MODULUS_BITS-1) as usize/$bit_size ;
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



                    // negative test on first batch
                    let bit_gadget_path = "mul operands/first batch of operands/unpack result field element/bit 0/boolean";
                    if cs.get(bit_gadget_path).is_zero() {
                        cs.set(bit_gadget_path, Fr::one());
                    } else {
                        cs.set(bit_gadget_path, Fr::zero());
                    }
                    assert!(!cs.is_satisfied());

                    // set bit value back
                    if cs.get(bit_gadget_path).is_zero() {
                        cs.set(bit_gadget_path, Fr::one());
                    } else {
                        cs.set(bit_gadget_path, Fr::zero());
                    }
                    assert!(cs.is_satisfied());

                    // negative test on allocated field element
                    let mut last_batch_start_operand = MAX_NUM_OPERANDS + (NUM_OPERANDS-MAX_NUM_OPERANDS)/(MAX_NUM_OPERANDS-1)*(MAX_NUM_OPERANDS-1);
                    if last_batch_start_operand == NUM_OPERANDS {
                        last_batch_start_operand -= MAX_NUM_OPERANDS-1;
                    }
                    let bit_gadget_path = format!("mul operands/operands from {} to {}/unpack result field element/bit 0/boolean", last_batch_start_operand, NUM_OPERANDS);
                    if cs.get(&bit_gadget_path).is_zero() {
                        cs.set(&bit_gadget_path, Fr::one());
                    } else {
                        cs.set(&bit_gadget_path, Fr::zero());
                    }
                    assert!(!cs.is_satisfied());

                    // set bit value back
                    if cs.get(&bit_gadget_path).is_zero() {
                        cs.set(&bit_gadget_path, Fr::one());
                    } else {
                        cs.set(&bit_gadget_path, Fr::zero());
                    }
                    assert!(cs.is_satisfied());

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
                fn test_modular_arithmetic_operations() {
                    let rng = &mut thread_rng();
                    for condition in BOOLEAN_TYPES.iter() {
                        for var_type_op1 in VARIABLE_TYPES.iter() {
                            for var_type_op2 in VARIABLE_TYPES.iter() {
                                let mut cs = ConstraintSystem::<Fr>::new(SynthesisMode::Debug);

                                let op1: $native_type = rng.gen();
                                let op2: $native_type = rng.gen();
                                let add_result_val = op1.overflowing_add(op2).0;
                                let mul_result_val = op1.overflowing_mul(op2).0;

                                let op1_var = alloc_fn(&mut cs, "alloc op1", &var_type_op1, op1);
                                let op2_var = alloc_fn(&mut cs, "alloc op2", &var_type_op2, op2);
                                let cond_var = alloc_boolean_cond(&mut cs, "alloc condition", condition);

                                let add_result_var = {
                                    // add a scope for multi_eq CS as the constraints are enforced when the variable is dropped
                                    let mut multi_eq = MultiEq::new(&mut cs);
                                    op1_var.conditionally_add(&mut multi_eq, &cond_var, &op2_var).unwrap()
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
                                }, &mul_result_var, "addition correctness");
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
                }

                #[test]
                fn test_mulmany_nocarry() {
                    const MAX_NUM_OPERANDS: usize = (<Fr as PrimeField>::Params::MODULUS_BITS-1) as usize/$bit_size ;
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

                    // negative test on first batch
                    let bit_gadget_path = "mul operands/first batch of operands/unpack result field element/bit 0/boolean";
                    if cs.get(bit_gadget_path).is_zero() {
                        cs.set(bit_gadget_path, Fr::one());
                    } else {
                        cs.set(bit_gadget_path, Fr::zero());
                    }
                    assert!(!cs.is_satisfied());

                    // set bit value back
                    if cs.get(bit_gadget_path).is_zero() {
                        cs.set(bit_gadget_path, Fr::one());
                    } else {
                        cs.set(bit_gadget_path, Fr::zero());
                    }
                    assert!(cs.is_satisfied());

                    // negative test on allocated field element
                    let mut last_batch_start_operand = MAX_NUM_OPERANDS + (NUM_OPERANDS-MAX_NUM_OPERANDS)/(MAX_NUM_OPERANDS-1)*(MAX_NUM_OPERANDS-1);
                    if last_batch_start_operand == NUM_OPERANDS {
                        last_batch_start_operand -= MAX_NUM_OPERANDS-1;
                    }
                    let bit_gadget_path = format!("mul operands/operands from {} to {}/unpack result field element/bit 0/boolean", last_batch_start_operand, NUM_OPERANDS);
                    if cs.get(&bit_gadget_path).is_zero() {
                        cs.set(&bit_gadget_path, Fr::one());
                    } else {
                        cs.set(&bit_gadget_path, Fr::zero());
                    }
                    assert!(!cs.is_satisfied());

                    // set bit value back
                    if cs.get(&bit_gadget_path).is_zero() {
                        cs.set(&bit_gadget_path, Fr::one());
                    } else {
                        cs.set(&bit_gadget_path, Fr::zero());
                    }
                    assert!(cs.is_satisfied());

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
                    let operand_values = (0..NUM_OPERANDS).map(|_| rng.gen_range(max_value..=$native_type::MAX)).collect::<Vec<$native_type>>();

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
                }

                #[test]
                fn test_no_carry_arithmetic_operations() {
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

                                    let result = if is_add {
                                        // add a scope for multi_eq CS as the constraints are enforced when the variable is dropped
                                        let mut multi_eq = MultiEq::new(&mut cs);
                                        op1_var.conditionally_add_nocarry(&mut multi_eq, &cond_var, &op2_var)
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
                                            return;
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
                                    assert!(!cs.is_satisfied(), "checking overflow constraint for {:?} {:?}", var_type_op1, var_type_op2);

                                }
                            }
                        }
                    }
                }

                }

            }
    }
}

pub mod test_mod {}