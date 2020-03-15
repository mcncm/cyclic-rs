#![allow(incomplete_features)]
#![feature(const_generics)]
#![feature(const_fn)]
#![feature(const_if_match)]

pub type Int = u32;

/// TODO: here are some behaviors I would like.
///
/// * Implementations should depend on magnitude of N, and be determined at
///   compile time. For example there may be extra care taken with respect to
///   wrapping for large-enough `N`, and small exponentials might be best
///   implemented by repeated multiplication.
///
/// * Wrapping ranges should be added (This doesn't seem to be possible using
///   the built-in `std::ops::Range`, which expects a type implementing
///   `PartialOrd`)
///
/// * Study optimizations from theory of finite groups, and apply some of them!

pub mod modular {
    use super::primes::is_prime;
    use super::utils::bit_len;
    use super::Int;
    use std::cmp::PartialEq;
    use std::ops;

    #[derive(Debug, Clone, Copy)]
    pub struct Modular<const N: Int>(Int);

    impl<const N: Int> Modular<{ N }> {
        const PRIMALITY: bool = is_prime({ N });
        const MAX_INT_POW: u32 = Int::max_value().count_ones() / bit_len({ N });

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
            let mut acc = Self::new(0);
            let mut inc = self;
            for n in 0..bit_len(self.0) {
                if exp & (1 << n) != 0 {
                    acc += inc
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

    /// Returns the inverse in the additive group.
    impl<const N: Int> ops::Neg for Modular<{ N }> {
        type Output = Self;

        fn neg(self) -> Self::Output {
            Self::new({ N } - self.0)
        }
    }

    impl<const N: Int> ops::Add for Modular<{ N }> {
        type Output = Self;

        fn add(self, other: Self) -> Self::Output {
            Self::new(self.0 + other.0)
        }
    }

    impl<const N: Int> ops::Mul for Modular<{ N }> {
        type Output = Self;

        fn mul(self, other: Self) -> Self::Output {
            Self::new(self.0 * other.0)
        }
    }

    impl<const N: Int> ops::Sub for Modular<{ N }> {
        type Output = Self;

        fn sub(self, other: Self) -> Self::Output {
            Self::new((N - other.0) + self.0)
        }
    }

    /// Division for prime modulus. This currently panics for composite `N`; as
    /// const generics are stabilized I hope to promote this to a compile-time
    /// check with a `where is_prime({ N })` clause.
    impl<const N: Int> ops::Div for Modular<{ N }> {
        type Output = Self;
        fn div(self, other: Self) -> Self::Output {
            assert!(Self::PRIMALITY);
            // Maximally naive implementation. Replace with the extended
            // euclidean division algorithm.
            let mut inv: Int = 1;
            for n in 1..({ N }) {
                if Self::new(other.0) * Self::new(n) == Self::new(1) {
                    inv = n;
                }
            }
            self * Self::new(inv)
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

    #[macro_export]
    macro_rules! modulo {
        ($value:expr ; $modulus:ident) => {
            crate::modular::Modular::<$modulus>::new($value)
        };
        ($value:expr ; $modulus:literal) => {
            crate::modular::Modular::<$modulus>::new($value)
        };
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
    const fn inferior_values_coprime(n: Int, inf: Int) -> bool {
        // This function is necessary--must be written in the following unusual
        // style--because of constraints imposed by `const fn` in the current
        // rustc release.
        //
        // Because of the unfortunate limitation of using recursive calls for
        // compile-time primality testing, it would be very nice if I could
        // optimize away some of these calls. It's likely that a better
        // algorithm could remove this burden.
        match inf {
            1 => true,
            _ => match n % inf {
                0 => false,
                _ => inferior_values_coprime(n, inf - 1),
            },
        }
    }

    #[test]
    fn inferior_values_coprime_ok() {
        // Primes should test coprime to all 1 < n < p
        assert!(inferior_values_coprime(3, 2));
        assert!(inferior_values_coprime(5, 4));
        assert!(inferior_values_coprime(7, 6));

        // Composites should not!
        assert!(!inferior_values_coprime(6, 5));

        // But this should pass for composite numbers on values less than their
        // least divisor
        assert!(inferior_values_coprime(35, 4));
    }

    /// A compile=time primality checker. This users a naive and inefficient
    /// primality test that checks divisbility by all integer values up to the
    /// square root of N.
    pub const fn is_prime(n: Int) -> bool {
        // This function must be written in the following unusual style because
        // of constraints imposed by `const fn` in the current rustc release.
        // Unfortunately, this means that `N` is limited by the default maximum
        // stack size.
        match n {
            0 | 1 => false,
            _ => {
                let bit_len_limit = 2 << (bit_len(n) >> 1);
                let test_limit = match bit_len_limit >= n {
                    true => n - 1,
                    false => bit_len_limit,
                };
                inferior_values_coprime(n, test_limit)
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
    use super::modulo;
    use super::Int;

    const N: Int = 7;

    #[test]
    fn residue_class_equality() {
        for v in 0..N {
            let m = modulo![v; N];
            for n in 0..=4 {
                assert_eq!(m, modulo![v + n * N; N]);
            }
        }
    }

    #[test]
    fn neg_ok() {
        for v in 0..N {
            let m = modulo![v; N];
            assert_eq!(-m, modulo![N - v; N]);
        }
    }

    #[test]
    fn add_ok() {
        for v1 in 0..N {
            for v2 in 0..N {
                let m1 = modulo![v1; N];
                let m2 = modulo![v2; N];
                assert_eq!(m1 + m2, modulo![v1 + v2; N]);
            }
        }
    }

    #[test]
    fn mul_ok() {
        for v1 in 0..N {
            for v2 in 0..N {
                let m1 = modulo![v1; N];
                let m2 = modulo![v2; N];
                assert_eq!(m1 * m2, modulo![v1 * v2; N]);
            }
        }
    }

    #[test]
    fn sub_ok() {
        for v1 in 0..N {
            for v2 in 0..N {
                let m1 = modulo![v1; N];
                let m2 = modulo![v2; N];
                assert_eq!(m1 - m2, modulo![v1; N] + (-modulo![v2; N]));
            }
        }
    }

    #[test]
    fn div_ok() {
        for v1 in 1..N {
            for v2 in 1..N {
                let m1 = modulo![v1; N];
                let m2 = modulo![v2; N];
                assert_eq!((m1 / m2) * m2, m1);
            }
        }
    }

    #[test]
    #[should_panic]
    fn div_fail_composite() {
        const COMPOSITE: Int = 6;
        let m1 = modulo![4; COMPOSITE];
        let m2 = modulo![2; COMPOSITE];
        let _m = m1 / m2;
    }

    #[test]
    fn pow_ok() {
        for v in 0..=N {
            for exp in 0..=10 {
                let m = modulo![v; N];
                assert_eq!(m.pow(exp), modulo![v.pow(exp); N]);
            }
        }
    }
}
