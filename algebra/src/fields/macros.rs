macro_rules! impl_prime_field_serializer {
    ($field: ident, $params: ident, $byte_size: expr) => {
        impl<P: $params> CanonicalSerializeWithFlags for $field<P> {
            fn serialize_with_flags<W: Write, F: Flags>(
                &self,
                mut writer: W,
                flags: F,
            ) -> Result<(), SerializationError> {
                // All reasonable `Flags` should be less than 8 bits in size
                // (256 values are enough for anyone!)
                if F::BIT_SIZE > 8 {
                    return Err(SerializationError::NotEnoughSpace);
                }

                // Get the minimum number of bytes required to represent the field element + the flags
                let output_byte_size = buffer_byte_size(P::MODULUS_BITS as usize + F::BIT_SIZE);

                // Write out `self` to a temporary buffer.
                // The size of the buffer is computed in this way because $byte_size
                // may actually be bigger than output_byte_size: this happens when,
                // for some reason, the number of bytes required to represent P::MODULUS_BITS
                // is bigger than (P::MODULUS_BITS/8) + 1
                let buffer_size = std::cmp::max($byte_size, output_byte_size);
                let mut bytes = vec![0u8; buffer_size];
                self.write(&mut bytes[..$byte_size])?;

                // Mask out the bits of the last byte that correspond to the flag.
                bytes[output_byte_size - 1] |= flags.u8_bitmask();

                writer.write_all(&bytes[..])?;
                Ok(())
            }

            // The size is computed in this way because $byte_size
            // may actually be bigger than output_byte_size: this happens when,
            // for some reason, the number of bytes required to represent P::MODULUS_BITS
            // is bigger than (P::MODULUS_BITS/8) + 1
            fn serialized_size_with_flags<F: Flags>(&self) -> usize {
                std::cmp::max(
                    $byte_size,
                    buffer_byte_size(P::MODULUS_BITS as usize + F::BIT_SIZE),
                )
            }
        }

        impl<P: $params> CanonicalSerialize for $field<P> {
            #[inline]
            fn serialize<W: Write>(&self, writer: W) -> Result<(), SerializationError> {
                self.serialize_with_flags(writer, EmptyFlags)
            }

            #[inline]
            fn serialized_size(&self) -> usize {
                self.serialized_size_with_flags::<EmptyFlags>()
            }
        }

        impl<P: $params> CanonicalDeserializeWithFlags for $field<P> {
            fn deserialize_with_flags<R: Read, F: Flags>(
                mut reader: R,
            ) -> Result<(Self, F), SerializationError> {
                // All reasonable `Flags` should be less than 8 bits in size
                // (256 values are enough for anyone!)
                if F::BIT_SIZE > 8 {
                    return Err(SerializationError::NotEnoughSpace);
                }

                // Get the minimum number of bytes required to represent the field element + the flags
                let output_byte_size = buffer_byte_size(P::MODULUS_BITS as usize + F::BIT_SIZE);

                // The size of the buffer is computed in this way because $byte_size
                // may actually be bigger than output_byte_size: this happens when,
                // for some reason, the number of bytes required to represent P::MODULUS_BITS
                // is bigger than (P::MODULUS_BITS/8) + 1
                let buffer_size = std::cmp::max($byte_size, output_byte_size);
                let mut bytes = vec![0; buffer_size];
                reader.read_exact(&mut bytes[..])?;

                // Remove the flags in the expected position
                let flags = F::from_u8_remove_flags(&mut bytes[output_byte_size - 1])
                    .ok_or(SerializationError::UnexpectedFlags)?;

                // Read the field element and return it along with the flags
                Ok((Self::read(&bytes[..$byte_size])?, flags))
            }
        }

        impl<P: $params> CanonicalDeserialize for $field<P> {
            fn deserialize<R: Read>(reader: R) -> Result<Self, SerializationError> {
                Self::deserialize_with_flags::<R, EmptyFlags>(reader).map(|(r, _)| r)
            }
        }
    };
}

macro_rules! impl_Fp {
    ($Fp:ident, $FpParameters:ident, $BigInteger:ident, $BigIntegerType:ty, $limbs:expr) => {
        pub trait $FpParameters: FpParameters<BigInt = $BigIntegerType> {}

        #[derive(Derivative)]
        #[derivative(
            Default(bound = ""),
            Hash(bound = ""),
            Clone(bound = ""),
            Copy(bound = ""),
            Debug(bound = ""),
            PartialEq(bound = ""),
            Eq(bound = "")
        )]
        #[derive(Serialize, Deserialize)]
        #[serde(transparent)]
        pub struct $Fp<P>(
            pub $BigIntegerType,
            #[derivative(Debug = "ignore")]
            #[doc(hidden)]
            #[serde(skip)]
            pub PhantomData<P>,
        );

        impl<P> $Fp<P> {
            #[inline]
            pub const fn new(element: $BigIntegerType) -> Self {
                Self(element, PhantomData)
            }
        }

        impl<P: $FpParameters> $Fp<P> {
            /// Perform modular reduction on `self`.
            /// NOTE: This function simply subtracts `P::MODULUS` from `self`,
            /// so the modular reduction is correct if and only if `self` is
            /// not larger than `2 * P::MODULUS`
            #[inline]
            fn reduce(&mut self) {
                if !self.is_valid() {
                    self.0.sub_noborrow(&P::MODULUS);
                }
            }

            impl_montgomery_reduction!($limbs);
        }

        impl<P: $FpParameters> Field for $Fp<P> {
            type BasePrimeField = Self;

            #[inline]
            fn zero() -> Self {
                $Fp::<P>($BigInteger::from(0), PhantomData)
            }

            #[inline]
            fn is_zero(&self) -> bool {
                self.0.is_zero()
            }

            #[inline]
            fn double(&self) -> Self {
                let mut temp = *self;
                temp.double_in_place();
                temp
            }

            #[inline]
            fn double_in_place(&mut self) -> &mut Self {
                // This cannot exceed the backing capacity.
                self.0.mul2();
                // However, it may need to be reduced.
                self.reduce();
                self
            }

            #[inline]
            fn one() -> Self {
                $Fp::<P>(P::R, PhantomData)
            }

            #[inline]
            fn is_one(&self) -> bool {
                self.0 == P::R
            }

            #[inline]
            fn is_odd(&self) -> bool {
                self.into_repr().is_odd()
            }

            #[inline]
            fn characteristic<'a>() -> &'a [u64] {
                P::MODULUS.as_ref()
            }

            #[inline]
            fn square(&self) -> Self {
                let mut temp = self.clone();
                temp.square_in_place();
                temp
            }

            impl_field_square_in_place!($limbs);

            /// [Guajardo Kumar Paar Pelzl]: https://link.springer.com/article/10.1007/s10440-006-9046-1
            /// Efficient Software-Implementation of Finite Fields with Applications to
            /// Cryptography
            /// Algorithm 17 (Montgomery Inversion in Fp).
            #[inline]
            fn inverse(&self) -> Option<Self> {
                if self.is_zero() {
                    None
                } else {
                    let zero = $BigInteger::from(0);

                    let mut v = self.0;
                    let mut u = P::MODULUS;
                    let mut r = $BigInteger::from(0);
                    let mut s = $BigInteger::from(1);
                    let mut k: u16 = 0;
                    // TODO: Make it independent from the limb size
                    let two_n : u16 = 2 * 64 * $limbs; // R2 = 2^two_n mod MODULUS
                    // At each step we want to have the following equalities:
                    // something * p + r*A = - u,    something * p + s*A = v
                    // The inverse at the end will be -r mod p. The sign is due to the fact
                    // that our big integers are unsigned so we can work with positive numbers.
                    // The arithmetic can be improved drastically since, at the beginning,
                    // r and s are very small.
                    while v != zero {
                        while u.is_even() {
                            u.div2();
                            if v.is_even() {
                                v.div2();
                            } else {
                                s.mul2();
                            }
                            k += 1;
                        }

                        while v.is_even() {
                            v.div2();
                            r.mul2();
                            k += 1;
                        }

                        if u > v {
                            u.sub_noborrow(&v);
                            u.div2();
                            r.add_nocarry(&s);
                            s.mul2();
                        } else {
                            v.sub_noborrow(&u);
                            v.div2();
                            s.add_nocarry(&r);
                            r.mul2();
                        }
                        k += 1;
                    }
                    // Up to now, r*A = - 2^k mod p for k in range(n,2n)
                    k = two_n - k;
                    if r >= P::MODULUS {
                        r.sub_noborrow(&P::MODULUS);
                    }
                    for _ in 0..k {
                        r.mul2();
                        if r >= P::MODULUS {
                            r.sub_noborrow(&P::MODULUS);
                        }
                    }
                    return Some(-Self::from_repr_raw(r));
                }
            }

            fn inverse_in_place(&mut self) -> Option<&mut Self> {
                if let Some(inverse) = self.inverse() {
                    *self = inverse;
                    Some(self)
                } else {
                    None
                }
            }

            #[inline]
            // TODO: Let byte_size = $limbs * 8. Generalize this function to the case in which
            //       byte_size + 1 > output_byte_size
            fn from_random_bytes_with_flags<F: Flags>(bytes: &[u8]) -> Option<(Self, F)> {
                if F::BIT_SIZE > 8 {
                    return None
                } else {
                    let mut result_bytes = [0u8; $limbs * 8 + 1];
                    // Copy the input into a temporary buffer.
                    result_bytes.iter_mut().zip(bytes).for_each(|(result, input)| {
                        *result = *input;
                    });
                    // This mask retains everything in the last limb
                    // that is below `P::MODULUS_BITS`.
                    let last_limb_mask = (u64::MAX >> P::REPR_SHAVE_BITS).to_le_bytes();
                    let mut last_bytes_mask = [0u8; 9];
                    last_bytes_mask[..8].copy_from_slice(&last_limb_mask);


                    // Length of the buffer containing the field element and the flag.
                    let output_byte_size = buffer_byte_size(P::MODULUS_BITS as usize + F::BIT_SIZE);
                    // Location of the flag is the last byte of the serialized
                    // form of the field element.
                    let flag_location = output_byte_size - 1;

                    // At which byte is the flag located in the last limb?
                    let flag_location_in_last_limb = flag_location - (8 * ($limbs - 1));

                    // Take all but the last 9 bytes.
                    let last_bytes = &mut result_bytes[8 * ($limbs - 1)..];

                    // The mask only has the last `F::BIT_SIZE` bits set
                    let flags_mask = u8::MAX.checked_shl(8 - (F::BIT_SIZE as u32)).unwrap_or(0);

                    // Mask away the remaining bytes, and try to reconstruct the
                    // flag
                    let mut flags: u8 = 0;
                    for (i, (b, m)) in last_bytes.iter_mut().zip(&last_bytes_mask).enumerate() {
                        if i == flag_location_in_last_limb {
                            flags = *b & flags_mask
                        }
                        *b &= m;
                    }
                    CanonicalDeserialize::deserialize(&result_bytes[..($limbs * 8)])
                        .ok()
                        .and_then(|f| F::from_u8(flags).map(|flag| (f, flag)))
                }
            }

            #[inline]
            fn frobenius_map(&mut self, _: usize) {
                // No-op: No effect in a prime field.
            }
        }

        impl<P: $FpParameters> PrimeField for $Fp<P> {
            type Params = P;
            type BigInt = $BigIntegerType;

            #[inline]
            fn from_repr(r: $BigIntegerType) -> Self {
                let mut r = $Fp(r, PhantomData);
                if r.is_valid() {
                    r.mul_assign(&$Fp(P::R2, PhantomData));
                    r
                } else {
                    Self::zero()
                }
            }

            impl_field_into_repr!($limbs, $BigIntegerType);

            #[inline]
            fn from_repr_raw(r: $BigIntegerType) -> Self {
                let r = $Fp(r, PhantomData);
                if r.is_valid() {
                    r
                } else {
                    Self::zero()
                }
            }

            #[inline]
            fn into_repr_raw(&self) -> $BigIntegerType {
                let r = *self;
                r.0
            }

            #[inline]
            fn multiplicative_generator() -> Self {
                $Fp::<P>(P::GENERATOR, PhantomData)
            }

            #[inline]
            fn root_of_unity() -> Self {
                $Fp::<P>(P::ROOT_OF_UNITY, PhantomData)
            }

            #[inline]
            fn full_root_of_unity() -> Option<Self> {
                match P::FULL_ROOT_OF_UNITY {
                    Some(v) => Some($Fp::<P>(v, PhantomData)),
                    None => None
                }
            }
        }

        impl<P: $FpParameters> SquareRootField for $Fp<P> {
            #[inline]
            fn legendre(&self) -> LegendreSymbol {
                use crate::fields::LegendreSymbol::*;

                if self.is_zero() {
                    return Zero;
                }

                // s = self^((MODULUS - 1) // 2)
                let s = self.pow(P::MODULUS_MINUS_ONE_DIV_TWO);
                if s.is_one() {
                    QuadraticResidue
                } else {
                    QuadraticNonResidue
                }
            }

            #[inline]
            fn sqrt(&self) -> Option<Self> {
                sqrt_impl!(Self, P, self)
            }

            fn sqrt_in_place(&mut self) -> Option<&mut Self> {
                (*self).sqrt().map(|sqrt| {
                    *self = sqrt;
                    self
                })
            }
        }

        impl<P: $FpParameters> Ord for $Fp<P> {
            #[inline(always)]
            fn cmp(&self, other: &Self) -> Ordering {
                self.into_repr().cmp(&other.into_repr())
            }
        }

        impl<P: $FpParameters> PartialOrd for $Fp<P> {
            #[inline(always)]
            fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
                Some(self.cmp(other))
            }
        }

        impl_prime_field_from_int!($Fp, u128, $FpParameters);
        impl_prime_field_from_int!($Fp, u64, $FpParameters);
        impl_prime_field_from_int!($Fp, u32, $FpParameters);
        impl_prime_field_from_int!($Fp, u16, $FpParameters);
        impl_prime_field_from_int!($Fp, u8, $FpParameters);

        impl_prime_field_standard_sample!($Fp, $FpParameters);

        impl_prime_field_serializer!($Fp, $FpParameters, $limbs * 8);

        impl<P: $FpParameters> ToBytes for $Fp<P> {
            #[inline]
            fn write<W: Write>(&self, writer: W) -> IoResult<()> {
                self.into_repr().write(writer)
            }
        }

        impl<P: $FpParameters> FromBytes for $Fp<P> {
            #[inline]
            fn read<R: Read>(reader: R) -> IoResult<Self> {
                $BigInteger::read(reader).and_then( |b|
                    if b.is_zero() {
                        Ok($Fp::zero())
                    } else {
                        let f = $Fp::from_repr(b);
                        if f == $Fp::zero() {
                            Err(IoError::new(
                                ErrorKind::InvalidData,
                                "Attempt to deserialize a field element over the modulus")
                            )
                        } else {
                            Ok(f)
                        }
                    }
                )
            }
        }

        impl<P: $FpParameters> SemanticallyValid for $Fp<P> {
            #[inline]
            fn is_valid(&self) -> bool {
                self.0 < P::MODULUS
            }
        }

        impl<P: $FpParameters> FromStr for $Fp<P> {
            type Err = ();

            /// Interpret a string of numbers as a (congruent) prime field element.
            /// Does not accept unnecessary leading zeroes or a blank string.
            fn from_str(s: &str) -> Result<Self, Self::Err> {
                if s.is_empty() {
                    return Err(());
                }

                if s == "0" {
                    return Ok(Self::zero());
                }

                let mut res = Self::zero();

                let ten = Self::from_repr(<Self as PrimeField>::BigInt::from(10));

                let mut first_digit = true;

                for c in s.chars() {
                    match c.to_digit(10) {
                        Some(c) => {
                            if first_digit {
                                if c == 0 {
                                    return Err(());
                                }

                                first_digit = false;
                            }

                            res.mul_assign(&ten);
                            res.add_assign(&Self::from_repr(<Self as PrimeField>::BigInt::from(
                                u64::from(c),
                            )));
                        },
                        None => {
                            return Err(());
                        },
                    }
                }
                if !res.is_valid() {
                    Err(())
                } else {
                    Ok(res)
                }
            }
        }

        impl<P: $FpParameters> Display for $Fp<P> {
            #[inline]
            fn fmt(&self, f: &mut Formatter<'_>) -> FmtResult {
                write!(f, stringify!($Fp"({})"), self.into_repr())
            }
        }

        impl<P: $FpParameters> Neg for $Fp<P> {
            type Output = Self;
            #[inline]
            #[must_use]
            fn neg(self) -> Self {
                if !self.is_zero() {
                    let mut tmp = P::MODULUS.clone();
                    tmp.sub_noborrow(&self.0);
                    $Fp::<P>(tmp, PhantomData)
                } else {
                    self
                }
            }
        }

        impl<'a, P: $FpParameters> Add<&'a $Fp<P>> for $Fp<P> {
            type Output = Self;

            #[inline]
            fn add(self, other: &Self) -> Self {
                let mut result = self.clone();
                result.add_assign(other);
                result
            }
        }

        impl<'a, P: $FpParameters> Sub<&'a $Fp<P>> for $Fp<P> {
            type Output = Self;

            #[inline]
            fn sub(self, other: &Self) -> Self {
                let mut result = self.clone();
                result.sub_assign(other);
                result
            }
        }

        impl<'a, P: $FpParameters> Mul<&'a $Fp<P>> for $Fp<P> {
            type Output = Self;

            #[inline]
            fn mul(self, other: &Self) -> Self {
                let mut result = self.clone();
                result.mul_assign(other);
                result
            }
        }

        impl<'a, P: $FpParameters> MulShort<&'a $Fp<P>> for $Fp<P> {
            type Output = Self;

            #[inline]
            fn mul_short(self, other: &Self) -> Self {
                let mut result = self.clone();
                result.mul_short_assign(other);
                result
            }
        }

        impl<'a, P: $FpParameters> Div<&'a $Fp<P>> for $Fp<P> {
            type Output = Self;

            #[inline]
            fn div(self, other: &Self) -> Self {
                let mut result = self.clone();
                result.mul_assign(&other.inverse().unwrap());
                result
            }
        }

        impl_additive_ops_from_ref!($Fp, $FpParameters);
        impl_multiplicative_ops_from_ref!($Fp, $FpParameters);
        impl_mul_short!($Fp, $FpParameters);

        impl<'a, P: $FpParameters> AddAssign<&'a Self> for $Fp<P> {
            #[inline]
            fn add_assign(&mut self, other: &Self) {
                // This cannot exceed the backing capacity.
                self.0.add_nocarry(&other.0);
                // However, it may need to be reduced
                self.reduce();
            }
        }

        impl<'a, P: $FpParameters> SubAssign<&'a Self> for $Fp<P> {
            #[inline]
            fn sub_assign(&mut self, other: &Self) {
                // If `other` is larger than `self`, add the modulus to self first.
                if other.0 > self.0 {
                    self.0.add_nocarry(&P::MODULUS);
                }
                self.0.sub_noborrow(&other.0);
            }
        }

        impl<'a, P: $FpParameters> MulAssign<&'a Self> for $Fp<P> {
            impl_field_mul_assign!($limbs);
        }

        impl<'a, P: $FpParameters> MulShortAssign<&'a Self> for $Fp<P> {
            impl_field_mul_short_assign!($limbs);
        }

        impl<'a, P: $FpParameters> DivAssign<&'a Self> for $Fp<P> {
            #[inline]
            fn div_assign(&mut self, other: &Self) {
                self.mul_assign(&other.inverse().unwrap());
            }
        }

        impl<P: $FpParameters> From<num_bigint::BigUint> for $Fp<P> {
            #[inline]
            fn from(val: num_bigint::BigUint) -> $Fp<P> {
                $Fp::<P>::from_le_bytes_mod_order(&val.to_bytes_le())
            }
        }

        impl<P: $FpParameters> From<$Fp<P>> for num_bigint::BigUint {
            #[inline]
            fn from(other: $Fp<P>) -> Self {
                other.into_repr().into()
            }
        }
    }
}
