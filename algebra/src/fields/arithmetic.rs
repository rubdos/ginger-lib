macro_rules! impl_montgomery_reduction {
    ($limbs:expr) => {
        #[inline]
        #[unroll_for_loops]
        fn montgomery_reduction(&mut self, r: &mut [u64; $limbs * 2]) {
            let mut _carry2 = 0;
            for i in 0..$limbs {
                let k = r[i].wrapping_mul(P::INV);
                let mut carry = 0;
                fa::mac_with_carry(r[i], k, P::MODULUS.0[0], &mut carry);
                for j in 1..$limbs {
                    r[j + i] = fa::mac_with_carry(r[j + i], k, P::MODULUS.0[j], &mut carry);
                }
                r[$limbs + i] = fa::adc(r[$limbs + i], _carry2, &mut carry);
                _carry2 = carry;
            }
            (self.0).0.copy_from_slice(&r[$limbs..]);
            self.reduce();
        }
    };
}

/// This modular multiplication algorithm uses Montgomery
/// reduction for efficient implementation. It also additionally
/// uses the "no-carry optimization" outlined
/// [here](https://hackmd.io/@zkteam/modular_multiplication) if
/// `P::MODULUS` has (a) a non-zero MSB, and (b) at least one
/// zero bit in the rest of the modulus.
macro_rules! impl_field_mul_assign {
    ($limbs:expr) => {
        #[inline]
        #[unroll_for_loops]
        fn mul_assign(&mut self, other: &Self) {
            // Checking the modulus at compile time
            let first_bit_set = P::MODULUS.0[$limbs - 1] >> 63 != 0;
            let mut all_bits_set = P::MODULUS.0[$limbs - 1] == !0 - (1 << 63);
            for i in 1..$limbs {
                all_bits_set &= P::MODULUS.0[$limbs - i - 1] == !0u64;
            }
            let _no_carry: bool = !(first_bit_set || all_bits_set);

            // No-carry optimisation applied to CIOS
            if _no_carry {
                #[cfg(use_asm)]
                #[allow(unsafe_code, unused_mut)]
                {
                    if $limbs <= 6 {
                        #[allow(unsafe_code)]
                        llvm_asm_mul!($limbs, (self.0).0, (other.0).0, P::MODULUS.0, P::INV);
                        self.reduce();
                        return;
                    }
                }
                let mut r = [0u64; $limbs];
                let mut carry1 = 0u64;
                let mut carry2 = 0u64;

                for i in 0..$limbs {
                    r[0] = fa::mac(r[0], (self.0).0[0], (other.0).0[i], &mut carry1);
                    let k = r[0].wrapping_mul(P::INV);
                    fa::mac_discard(r[0], k, P::MODULUS.0[0], &mut carry2);
                    for j in 1..$limbs {
                        r[j] = fa::mac_with_carry(r[j], (self.0).0[j], (other.0).0[i], &mut carry1);
                        r[j - 1] = fa::mac_with_carry(r[j], k, P::MODULUS.0[j], &mut carry2);
                    }
                    r[$limbs - 1] = carry1 + carry2;
                }
                (self.0).0 = r;
                self.reduce();
            // Alternative implementation
            } else {
                let mut r = [0u64; $limbs * 2];

                for i in 0..$limbs {
                    let mut carry = 0;
                    for j in 0..$limbs {
                        r[j + i] =
                            fa::mac_with_carry(r[j + i], (self.0).0[i], (other.0).0[j], &mut carry);
                    }
                    r[$limbs + i] = carry;
                }
                self.montgomery_reduction(&mut r)
            }
        }
    };
}

macro_rules! impl_field_mul_short_assign {
    ($limbs: expr) => {
        #[inline]
        #[unroll_for_loops]
        // Partial, or short, Montgomery multiplication. Computes the product
        //      R*xy mod p = (R*x mod p)*(R_s * y mod p)
        // for y having a 1-limb sized representation (R_s*y mod p) w.r.t. the
        // "short" Montgomery constant R_s = 2^64.
        //TODO: Can we write the assembly equivalent of this ? Is it worth ?
        //TODO: Probably there's a more compact way to write this
        fn mul_short_assign(&mut self, other: &Self) {
            let mut r = [0u64; $limbs + 1];
            let mut carry1 = 0u64;
            let mut carry2 = 0u64;

            for i in 0..$limbs {
                r[i] = fa::mac_with_carry(0, (self.0).0[0], (other.0).0[i], &mut carry1);
            }
            r[$limbs] = carry1;

            let k = r[0].wrapping_mul(P::INV);
            fa::mac_with_carry(r[0], k, P::MODULUS.0[0], &mut carry2);
            for i in 1..$limbs {
                r[i] = fa::mac_with_carry(r[i], k, P::MODULUS.0[i], &mut carry2);
            }
            r[$limbs] = fa::adc(r[$limbs], 0, &mut carry2);

            for i in 0..$limbs {
                (self.0).0[i] = r[i + 1];
            }
            self.reduce();
        }
    };
}

macro_rules! impl_field_into_repr {
    ($limbs:expr, $BigIntegerType:ty) => {
        #[inline]
        #[unroll_for_loops]
        fn into_repr(&self) -> $BigIntegerType {
            let mut tmp = self.0;
            let mut r = tmp.0;
            // Montgomery Reduction
            for i in 0..$limbs {
                let k = r[i].wrapping_mul(P::INV);
                let mut carry = 0;

                fa::mac_with_carry(r[i], k, P::MODULUS.0[0], &mut carry);
                for j in 1..$limbs {
                    r[(j + i) % $limbs] =
                        fa::mac_with_carry(r[(j + i) % $limbs], k, P::MODULUS.0[j], &mut carry);
                }
                r[i % $limbs] = carry;
            }
            tmp.0 = r;
            tmp
        }
    };
}

macro_rules! impl_field_square_in_place {
    ($limbs: expr) => {
        #[inline]
        #[unroll_for_loops]
        #[allow(unused_braces)]
        fn square_in_place(&mut self) -> &mut Self {
            // Checking the modulus at compile time
            let first_bit_set = P::MODULUS.0[$limbs - 1] >> 63 != 0;
            let mut all_bits_set = P::MODULUS.0[$limbs - 1] == !0 - (1 << 63);
            for i in 1..$limbs {
                all_bits_set &= P::MODULUS.0[$limbs - i - 1] == !0u64;
            }
            let _no_carry: bool = !(first_bit_set || all_bits_set);

            #[cfg(use_asm)]
            #[allow(unsafe_code, unused_mut)]
            {
                if $limbs <= 6 && _no_carry {
                    #[allow(unsafe_code)]
                    llvm_asm_square!($limbs, (self.0).0, P::MODULUS.0, P::INV);
                    self.reduce();
                    return self;
                }
            }
            let mut r = [0u64; $limbs * 2];

            let mut carry = 0;
            for i in 0..$limbs {
                if i < $limbs - 1 {
                    for j in 0..$limbs {
                        if j >= i + 1 {
                            r[i + j] = fa::mac_with_carry(
                                r[i + j],
                                (self.0).0[i],
                                (self.0).0[j],
                                &mut carry,
                            );
                        }
                    }
                    r[$limbs + i] = carry;
                    carry = 0;
                }
            }
            r[$limbs * 2 - 1] = r[$limbs * 2 - 2] >> 63;
            for i in 0..$limbs {
                r[$limbs * 2 - 2 - i] =
                    (r[$limbs * 2 - 2 - i] << 1) | (r[$limbs * 2 - 3 - i] >> 63);
            }
            for i in 3..$limbs {
                r[$limbs + 1 - i] = (r[$limbs + 1 - i] << 1) | (r[$limbs - i] >> 63);
            }
            r[1] = r[1] << 1;

            for i in 0..$limbs {
                r[2 * i] = fa::mac_with_carry(r[2 * i], (self.0).0[i], (self.0).0[i], &mut carry);
                r[2 * i + 1] = fa::adc(r[2 * i + 1], 0, &mut carry);
            }
            self.montgomery_reduction(&mut r);
            self
        }
    };
}

macro_rules! impl_field_bigint_conv {
    ($field: ident, $bigint: ident, $params: ident) => {
        impl<P: $params> Into<$bigint> for $field<P> {
            fn into(self) -> $bigint {
                self.into_repr()
            }
        }

        impl<P: $params> From<$bigint> for $field<P> {
            fn from(int: $bigint) -> Self {
                Self::from_repr(int)
            }
        }
    };
}

macro_rules! impl_prime_field_standard_sample {
    ($field: ident, $params: ident) => {
        impl<P: $params> rand::distributions::Distribution<$field<P>>
            for rand::distributions::Standard
        {
            #[inline]
            fn sample<R: rand::Rng + ?Sized>(&self, rng: &mut R) -> $field<P> {
                loop {
                    let mut tmp = $field(rng.sample(rand::distributions::Standard), PhantomData);

                    assert!(P::REPR_SHAVE_BITS <= 64);
                    let mask = if P::REPR_SHAVE_BITS == 64 {
                        0
                    } else {
                        std::u64::MAX >> P::REPR_SHAVE_BITS
                    };
                    tmp.0.as_mut().last_mut().map(|val| *val &= mask);

                    if tmp.is_valid() {
                        return tmp;
                    }
                }
            }
        }
    };
}

macro_rules! impl_prime_field_from_int {
    ($field: ident, u128, $params: ident) => {
        impl<P: $params> From<u128> for $field<P> {
            fn from(other: u128) -> Self {
                let upper = (other >> 64) as u64;
                let lower = ((other << 64) >> 64) as u64;
                let mut default_int = P::BigInt::default();
                default_int.0[0] = lower;
                default_int.0[1] = upper;
                Self::from_repr(default_int)
            }
        }
    };
    ($field: ident, $int: ident, $params: ident) => {
        impl<P: $params> From<$int> for $field<P> {
            fn from(other: $int) -> Self {
                Self::from_repr(P::BigInt::from(u64::from(other)))
            }
        }
    };
}

macro_rules! sqrt_impl {
    ($Self:ident, $P:tt, $self:expr) => {{
        use crate::fields::LegendreSymbol::*;
        // https://eprint.iacr.org/2012/685.pdf (page 12, algorithm 5)
        // Actually this is just normal Tonelli-Shanks; since `P::Generator`
        // is a quadratic non-residue, `P::ROOT_OF_UNITY = P::GENERATOR ^ t`
        // is also a quadratic non-residue (since `t` is odd).
        match $self.legendre() {
            Zero => Some(*$self),
            QuadraticNonResidue => None,
            QuadraticResidue => {
                let mut z = $Self::qnr_to_t();
                let mut w = $self.pow($P::T_MINUS_ONE_DIV_TWO);
                let mut x = w * $self;
                let mut b = x * &w;

                let mut v = $P::TWO_ADICITY as usize;
                // t = self^t
                #[cfg(debug_assertions)]
                {
                    let mut check = b;
                    for _ in 0..(v - 1) {
                        check.square_in_place();
                    }
                    if !check.is_one() {
                        eprintln!("Input is not a square root, but it passed the QR test");
                        return None;
                    }
                }

                while !b.is_one() {
                    let mut k = 0usize;

                    let mut b2k = b;
                    while !b2k.is_one() {
                        // invariant: b2k = b^(2^k) after entering this loop
                        b2k.square_in_place();
                        k += 1;
                    }

                    let j = v - k - 1;
                    w = z;
                    for _ in 0..j {
                        w.square_in_place();
                    }

                    z = w.square();
                    b *= &z;
                    x *= &w;
                    v = k;
                }

                Some(x)
            }
        }
    }};
}

#[macro_export]
macro_rules! impl_additive_ops_from_ref {
    ($type: ident, $params: ident) => {
        #[allow(unused_qualifications)]
        impl<P: $params> std::ops::Add<Self> for $type<P> {
            type Output = Self;

            #[inline]
            fn add(self, other: Self) -> Self {
                let mut result = self;
                result.add_assign(&other);
                result
            }
        }

        #[allow(unused_qualifications)]
        impl<'a, P: $params> std::ops::Add<&'a mut Self> for $type<P> {
            type Output = Self;

            #[inline]
            fn add(self, other: &'a mut Self) -> Self {
                let mut result = self;
                result.add_assign(&*other);
                result
            }
        }

        #[allow(unused_qualifications)]
        impl<P: $params> std::ops::Sub<Self> for $type<P> {
            type Output = Self;

            #[inline]
            fn sub(self, other: Self) -> Self {
                let mut result = self;
                result.sub_assign(&other);
                result
            }
        }

        #[allow(unused_qualifications)]
        impl<'a, P: $params> std::ops::Sub<&'a mut Self> for $type<P> {
            type Output = Self;

            #[inline]
            fn sub(self, other: &'a mut Self) -> Self {
                let mut result = self;
                result.sub_assign(&*other);
                result
            }
        }

        #[allow(unused_qualifications)]
        impl<P: $params> std::iter::Sum<Self> for $type<P> {
            fn sum<I: Iterator<Item = Self>>(iter: I) -> Self {
                iter.fold(Self::zero(), std::ops::Add::add)
            }
        }

        #[allow(unused_qualifications)]
        impl<'a, P: $params> std::iter::Sum<&'a Self> for $type<P> {
            fn sum<I: Iterator<Item = &'a Self>>(iter: I) -> Self {
                iter.fold(Self::zero(), std::ops::Add::add)
            }
        }

        #[allow(unused_qualifications)]
        impl<P: $params> std::ops::AddAssign<Self> for $type<P> {
            fn add_assign(&mut self, other: Self) {
                self.add_assign(&other)
            }
        }

        #[allow(unused_qualifications)]
        impl<P: $params> std::ops::SubAssign<Self> for $type<P> {
            fn sub_assign(&mut self, other: Self) {
                self.sub_assign(&other)
            }
        }

        #[allow(unused_qualifications)]
        impl<'a, P: $params> std::ops::AddAssign<&'a mut Self> for $type<P> {
            fn add_assign(&mut self, other: &'a mut Self) {
                self.add_assign(&*other)
            }
        }

        #[allow(unused_qualifications)]
        impl<'a, P: $params> std::ops::SubAssign<&'a mut Self> for $type<P> {
            fn sub_assign(&mut self, other: &'a mut Self) {
                self.sub_assign(&*other)
            }
        }
    };
}

#[macro_export]
macro_rules! impl_multiplicative_ops_from_ref {
    ($type: ident, $params: ident) => {
        #[allow(unused_qualifications)]
        impl<P: $params> std::ops::Mul<Self> for $type<P> {
            type Output = Self;

            #[inline]
            fn mul(self, other: Self) -> Self {
                let mut result = self;
                result.mul_assign(&other);
                result
            }
        }

        #[allow(unused_qualifications)]
        impl<P: $params> std::ops::Div<Self> for $type<P> {
            type Output = Self;

            #[inline]
            fn div(self, other: Self) -> Self {
                let mut result = self;
                result.div_assign(&other);
                result
            }
        }

        #[allow(unused_qualifications)]
        impl<'a, P: $params> std::ops::Mul<&'a mut Self> for $type<P> {
            type Output = Self;

            #[inline]
            fn mul(self, other: &'a mut Self) -> Self {
                let mut result = self;
                result.mul_assign(&*other);
                result
            }
        }

        #[allow(unused_qualifications)]
        impl<'a, P: $params> std::ops::Div<&'a mut Self> for $type<P> {
            type Output = Self;

            #[inline]
            fn div(self, other: &'a mut Self) -> Self {
                let mut result = self;
                result.div_assign(&*other);
                result
            }
        }

        #[allow(unused_qualifications)]
        impl<P: $params> std::iter::Product<Self> for $type<P> {
            fn product<I: Iterator<Item = Self>>(iter: I) -> Self {
                iter.fold(Self::one(), std::ops::Mul::mul)
            }
        }

        #[allow(unused_qualifications)]
        impl<'a, P: $params> std::iter::Product<&'a Self> for $type<P> {
            fn product<I: Iterator<Item = &'a Self>>(iter: I) -> Self {
                iter.fold(Self::one(), Mul::mul)
            }
        }

        #[allow(unused_qualifications)]
        impl<P: $params> std::ops::MulAssign<Self> for $type<P> {
            fn mul_assign(&mut self, other: Self) {
                self.mul_assign(&other)
            }
        }

        #[allow(unused_qualifications)]
        impl<'a, P: $params> std::ops::DivAssign<&'a mut Self> for $type<P> {
            fn div_assign(&mut self, other: &'a mut Self) {
                self.div_assign(&*other)
            }
        }

        #[allow(unused_qualifications)]
        impl<'a, P: $params> std::ops::MulAssign<&'a mut Self> for $type<P> {
            fn mul_assign(&mut self, other: &'a mut Self) {
                self.mul_assign(&*other)
            }
        }

        #[allow(unused_qualifications)]
        impl<P: $params> std::ops::DivAssign<Self> for $type<P> {
            fn div_assign(&mut self, other: Self) {
                self.div_assign(&other)
            }
        }
    };
}

#[macro_export]
macro_rules! impl_mul_short {
    ($type: ident, $params: ident) => {
        #[allow(unused_qualifications)]
        impl<P: $params> MulShort<Self> for $type<P> {
            type Output = Self;

            #[inline]
            fn mul_short(self, other: Self) -> Self {
                let mut result = self;
                result.mul_short_assign(&other);
                result
            }
        }

        #[allow(unused_qualifications)]
        impl<'a, P: $params> MulShort<&'a mut Self> for $type<P> {
            type Output = Self;

            #[inline]
            fn mul_short(self, other: &'a mut Self) -> Self {
                let mut result = self;
                result.mul_short_assign(&*other);
                result
            }
        }

        #[allow(unused_qualifications)]
        impl<P: $params> MulShortAssign<Self> for $type<P> {
            #[inline]
            fn mul_short_assign(&mut self, other: Self) {
                self.mul_short_assign(&other)
            }
        }

        #[allow(unused_qualifications)]
        impl<'a, P: $params> MulShortAssign<&'a mut Self> for $type<P> {
            #[inline]
            fn mul_short_assign(&mut self, other: &'a mut Self) {
                self.mul_short_assign(&*other)
            }
        }
    };
}
