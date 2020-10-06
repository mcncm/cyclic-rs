#![allow(incomplete_features)]
#![feature(const_generics)]
#![feature(const_fn)]

//! Simple library for generic cyclic groups, rings of integers, and prime
//! fields. Rather than providing single operations like modular exponentiation
//! or modular division, Cyclic provides type-safe ring-valued integers that
//! work the way you expect.
//!
//! Because of its reliance on const generics and compile-time computing
//! for primality checking, Cyclic currently only builds with the nightly
//! toolchain.
//!
//! # Examples
//!
//! Using Cyclic is easy: the crate provides a macro, `res!`, that takes an
//! unsigned integer and produces its residue class.
//!
//! ```
//! use cyclic::res;
//! const N: u32 = 7;
//!
//! let r = res![3; N];
//! assert_eq!(r.0, 3);
//!
//! let s = res![11; N];
//! assert_eq!(s.0, 4);
//!
//! assert_eq!(r + s, res![0; N]);
//! assert_eq!(r - s, res![6; N]);
//! assert_eq!(r * s, res![5; N]);
//! assert_eq!(r / s, res![6; N]);
//!
//! assert_eq!(res![2; 3].pow(1_000_000), res![1; 3])
//! ```
//!
//! The following code, on the other hand, will fail to compile:
//!
//! ```compile_fail,E0308
//! use cyclic::res;
//! let r = res![1; 6] + res![4; 12];
//! ```
//!
//! Attempted division in a ring of composite order will panic:
//!
//! ```should_panic,
//! use cyclic::res;
//! let r = res![2; 4] / res![3; 4];
//! ```
//!
//! The primality of the modulus is checked at compile time, so this incurs no
//! runtime cost.
//!
//! # Crate Feature Flags
//!
//! - `composite_order_division`: enabling this feature suppresses panics when
//!   dividing in a ring that is not of prime order. It becomes the programmer's
//!   responsibility to remember that only elements relatively prime to the
//!   modulus have well-defined inverses.
//!
//! # Crate Status
//!
//! This crate is brand-new, and although it is "feature-complete" in a narrow
//! sense, there are still things to be done.
//!
//! - The crate currently only builds on nightly.
//! - Currently, the `Modular` type is generic over the modulus, but not the
//!   integer type, which is constrained to be `u32`. This is due to an
//!   unfortunate technical limitation of the current implementation of const
//!   generics, which will hopefully be corrected one day.
//! - The crate should support `no_std`.
//!
//! There are a number of other improvements I would like to make to this crate:
//!
//! - Montgomery multiplication for large exponents
//!
//! - Compile-time error for attempted division in a composite-order ring. I
//!   consider this change pretty important, but it's waiting on some const
//!   generic features that don't exist yet.
//!
//! - Possible feature flags for different algorithms.
//!

type Int = u32;

pub mod modular {
    use super::primes::is_prime;
    use super::utils::bit_len;
    use super::Int;
    use std::cmp::PartialEq;
    use std::ops;

    #[derive(Debug, Clone, Copy)]
    pub struct Modular<const N: Int>(pub Int);

    #[macro_export]
    macro_rules! res {
        ($value:expr ; $modulus:ident) => {
            $crate::modular::Modular::<$modulus>::new($value)
        };
        ($value:expr ; $modulus:literal) => {
            $crate::modular::Modular::<$modulus>::new($value)
        };
    }

    /// A ring type taking values in Z/nZ, for any positive n.
    ///
    /// # Examples
    ///
    /// ```
    /// use cyclic::modular::Modular;
    ///
    /// const N: u32 = 6;
    /// let r = Modular::<N>::new(2);
    /// let s = Modular::<N>::new(3);
    ///
    /// assert_eq!((r * s).0, 0);
    /// ```
    ///
    /// ```compile_fail,E0308
    /// use cyclic::modular::Modular;
    ///
    /// let r = Modular::<3>::new(1);
    /// let s = Modular::<4>::new(1);
    ///
    /// let absurd = r + s;
    /// ```
    impl<const N: Int> Modular<N> {
        const PRIMALITY: bool = is_prime(N);
        const MAX_INT_POW: u32 = Int::max_value().count_ones() / bit_len(N);

        pub fn new(val: Int) -> Self {
            Self { 0: val % { N } }
        }

        /// Raises `self` to the power of `exp`, using the underlying integral
        /// type's `pow` method.
        fn int_pow(self, exp: u32) -> Self {
            Self::new(self.0.pow(exp))
        }

        /// Raises `self` to the power of `expt`, using a native Modular
        /// implementation of the repeated-squaring algorithm.
        fn mod_pow(self, exp: u32) -> Self {
            let mut acc = Self::new(1);
            let mut inc = self;
            for n in 0..bit_len(exp) {
                if exp & (1 << n) != 0 {
                    acc *= inc
                }
                inc *= inc;
            }
            acc
        }

        pub fn pow(self, exp: u32) -> Self {
            if exp <= Self::MAX_INT_POW {
                self.int_pow(exp)
            } else {
                self.mod_pow(exp)
            }
        }
    }

    #[test]
    fn mod_pow_ok() {
        let m = Modular::<7>::new(3);
        for exp in 1..=7 {
            assert_eq!(m.int_pow(exp), m.mod_pow(exp));
        }
    }

    /// Returns the additive inverse of a ring element.
    impl<const N: Int> ops::Neg for Modular<{ N }> {
        type Output = Self;

        fn neg(self) -> Self::Output {
            Self::new({ N } - self.0)
        }
    }

    /// Adds ring elements modulo `N`.
    impl<const N: Int> ops::Add for Modular<{ N }> {
        type Output = Self;

        fn add(self, other: Self) -> Self::Output {
            Self::new(self.0 + other.0)
        }
    }

    /// Multiplies ring elements modulo `N`.
    impl<const N: Int> ops::Mul for Modular<{ N }> {
        type Output = Self;

        fn mul(self, other: Self) -> Self::Output {
            Self::new(self.0 * other.0)
        }
    }

    /// Subtracts ring elements modulo `N`.
    impl<const N: Int> ops::Sub for Modular<{ N }> {
        type Output = Self;

        fn sub(self, other: Self) -> Self::Output {
            Self::new((N - other.0) + self.0)
        }
    }

    /// Divides field elements modulo `N`.
    ///
    /// Division is implemented with the extended Euclidean algorithm. There
    /// *might* be cases where the naive exponentiation algorithm is slightly
    /// faster; it might be worth feature-flagging this.
    ///
    /// # Panics
    ///
    /// This currently panics for composite `N`; as const generics are
    /// stabilized I hope to promote this to a compile-time check with a `where
    /// is_prime({ N })` clause. This panic can be disabled by compiling with
    /// the `composite_order_division` feature.
    impl<const N: Int> ops::Div for Modular<{ N }> {
        type Output = Self;
        fn div(self, other: Self) -> Self::Output {
            if !cfg!(feature = "composite_order_division") {
                assert!(Self::PRIMALITY);
            }
            if other.0 == 0 {
                panic!("attempt to divide by zero mod {}", { N });
            }

            let (mut quot_prev, mut rem_prev) = ({ N / other.0 }, { N % other.0 });
            let mut acc_prev = res![0; N];

            let mut acc = res![1; N];
            let inv = match rem_prev {
                0 => acc,
                _ => {
                    let (mut quot, mut rem) = (other.0 / rem_prev, other.0 % rem_prev);
                    while rem != 0 {
                        let acc_tmp = acc;
                        acc = acc_prev - acc * res![quot_prev; N];
                        acc_prev = acc_tmp;

                        let (quot_tmp, rem_tmp) = (quot, rem);
                        quot = rem_prev / rem;
                        rem = rem_prev % rem;
                        quot_prev = quot_tmp;
                        rem_prev = rem_tmp;
                    }
                    acc_prev - acc * res![quot_prev; N]
                }
            };
            self * inv
        }
    }

    // NOTE: is there a tiny performance cost from the indirection in my
    // implementations of the `Assign` traits?
    impl<const N: Int> ops::AddAssign for Modular<{ N }> {
        fn add_assign(&mut self, other: Self) {
            *self = *self + other
        }
    }

    impl<const N: Int> ops::MulAssign for Modular<{ N }> {
        fn mul_assign(&mut self, other: Self) {
            *self = *self * other
        }
    }

    impl<const N: Int> ops::SubAssign for Modular<{ N }> {
        fn sub_assign(&mut self, other: Self) {
            *self = *self - other
        }
    }

    impl<const N: Int> ops::DivAssign for Modular<{ N }> {
        fn div_assign(&mut self, other: Self) {
            *self = *self / other
        }
    }

    impl<const N: Int> PartialEq for Modular<{ N }> {
        fn eq(&self, other: &Self) -> bool {
            self.0 == other.0
        }
    }

    impl<const N: Int> From<Int> for Modular<{ N }> {
        fn from(n: Int) -> Self {
            Self::new(n)
        }
    }
}

mod utils {
    use super::Int;

    pub const fn bit_len(n: Int) -> u32 {
        let int_size = Int::max_value().count_ones();
        int_size - n.leading_zeros()
    }

    #[test]
    fn bit_len_ok() {
        assert_eq!(bit_len(0), 0);
        assert_eq!(bit_len(1), 1);
        assert_eq!(bit_len(2), 2);
        assert_eq!(bit_len(3), 2);
        assert_eq!(bit_len(4), 3);
    }
}

mod primes {
    use super::utils::bit_len;
    use super::Int;

    /// Checks that all values less than or equal to `inf`, other than 1, are
    /// coprime to `n`, and returns `true` if this is the case.
    const fn inferior_values_indivisible(n: Int, inf: Int) -> bool {
        // This function is necessary--must be written in the following unusual
        // style--because of constraints imposed by `const fn` in the current
        // rustc release.
        //
        // Because of the unfortunate limitation of using recursive calls for
        // compile-time primality testing, it would be very nice if I could
        // optimize away some of these calls. It's likely that a better
        // algorithm could remove this burden.
        //
        // NOTE: this obtuse style should no longer be necessary as of Rust 1.46

        match inf {
            1 => true,
            _ => match n % inf {
                0 => false,
                _ => inferior_values_indivisible(n, inf - 1),
            },
        }
    }

    #[test]
    fn inferior_values_indivisible_ok() {
        // Primes should test coprime to all 1 < n < p
        assert!(inferior_values_indivisible(3, 2));
        assert!(inferior_values_indivisible(5, 4));
        assert!(inferior_values_indivisible(7, 6));

        // Composites should not!
        assert!(!inferior_values_indivisible(6, 5));

        // But this should pass for composite numbers on values less than their
        // least divisor
        assert!(inferior_values_indivisible(35, 4));
    }

    /// A compile-time primality checker. This users a naive and inefficient
    /// primality test that checks divisbility by all integer values up to the
    /// square root of N.
    pub const fn is_prime(n: Int) -> bool {
        // This function must be written in the following unusual style because
        // of constraints imposed by `const fn` in the current rustc release.
        // Unfortunately, this means that `N` is limited by the default maximum
        // stack size.
        //
        // NOTE: this obtuse style should no longer be necessary as of Rust 1.46
        match n {
            0 | 1 => false,
            _ => {
                let bit_len_limit = 2 << (bit_len(n) >> 1);
                let test_limit = match bit_len_limit >= n {
                    true => n - 1,
                    false => bit_len_limit,
                };
                inferior_values_indivisible(n, test_limit)
            }
        }
    }

    #[test]
    fn is_prime_ok() {
        // primes should test correctly
        assert!(is_prime(3));
        assert!(is_prime(5));
        assert!(is_prime(7));
        assert!(is_prime(11));
        assert!(is_prime(13));
        assert!(is_prime(17));

        // 0 and 1 should fail
        assert!(!is_prime(0));
        assert!(!is_prime(1));

        // ...and so should composites.
        assert!(!is_prime(4));
        assert!(!is_prime(6));
        assert!(!is_prime(8));
        assert!(!is_prime(9));
        assert!(!is_prime(10));
        assert!(!is_prime(12));
    }
}

#[cfg(test)]
mod tests {
    use super::primes::is_prime;
    use super::res;
    use super::Int;

    const N: Int = 7;

    #[test]
    fn residue_class_equality() {
        for v in 0..N {
            let m = res![v; N];
            for n in 0..=4 {
                assert_eq!(m, res![v + n * N; N]);
            }
        }
    }

    #[test]
    fn neg_ok() {
        for v in 0..N {
            let m = res![v; N];
            assert_eq!(-m, res![N - v; N]);
        }
    }

    #[test]
    fn add_ok() {
        for v1 in 0..N {
            for v2 in 0..N {
                let m1 = res![v1; N];
                let m2 = res![v2; N];
                assert_eq!(m1 + m2, res![v1 + v2; N]);
            }
        }
    }

    #[test]
    fn mul_ok() {
        for v1 in 0..N {
            for v2 in 0..N {
                let m1 = res![v1; N];
                let m2 = res![v2; N];
                assert_eq!(m1 * m2, res![v1 * v2; N]);
            }
        }
    }

    #[test]
    fn sub_ok() {
        for v1 in 0..N {
            for v2 in 0..N {
                let m1 = res![v1; N];
                let m2 = res![v2; N];
                assert_eq!(m1 - m2, res![v1; N] + (-res![v2; N]));
            }
        }
    }

    #[test]
    fn div_ok() {
        for v1 in 1..N {
            for v2 in 1..N {
                let m1 = res![v1; N];
                let m2 = res![v2; N];
                assert_eq!((m1 / m2) * m2, m1);
            }
        }
    }

    #[test]
    #[should_panic]
    fn div_zero_fail() {
        let _m = res![4; N] / res![0; N];
    }

    #[cfg(not(feature = "composite_order_division"))]
    #[test]
    #[should_panic]
    fn div_composite_fail() {
        const COMPOSITE: Int = 6;
        let m1 = res![4; COMPOSITE];
        let m2 = res![2; COMPOSITE];
        let _m = m1 / m2;
    }

    #[test]
    fn pow_ok() {
        for v in 0..=N {
            for exp in 0..=10 {
                let m = res![v; N];
                assert_eq!(m.pow(exp), res![v.pow(exp); N]);
            }
        }
    }

    #[test]
    fn pow_cyclic_order() {
        assert!(is_prime(N));
        for v in 2..N {
            let m = res![v; N];
            assert_eq!(m.pow(N - 1), res![1; N]);
        }
    }

    #[test]
    fn big_pow_ok() {
        const MODULUS: Int = 3;
        const POW: u32 = 1_000_000;
        let m = res![2; MODULUS];
        for exp in POW..=(POW + 10) {
            assert_eq!(
                m.pow(exp),
                if exp % 2 == 0 {
                    res![1; MODULUS]
                } else {
                    res![2; MODULUS]
                }
            );
        }
    }
}
