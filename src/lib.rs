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
mod modular {
    use super::primes::is_prime;
    use super::Int;
    use std::cmp::PartialEq;
    use std::ops::{Add, Div, Mul, Neg, Sub};

    #[derive(Debug, Clone, Copy)]
    pub struct Modular<const N: Int>(Int);

    impl<const N: Int> Modular<{ N }> {
        const PRIMALITY: bool = is_prime({ N });

        pub fn new(val: Int) -> Self {
            Self { 0: val % { N } }
        }

        /// Raises `self` to the power of `exp`, using the underlying integral
        /// type's `pow` method.
        pub fn pow(self, exp: u32) -> Self {
            Self::new(self.0.pow(exp))
        }
    }

    impl<const N: Int> Neg for Modular<{ N }> {
        type Output = Self;

        fn neg(self) -> Self::Output {
            Self::new({ N } - self.0)
        }
    }

    impl<const N: Int> Add for Modular<{ N }> {
        type Output = Self;

        fn add(self, other: Self) -> Self::Output {
            Self::new(self.0 + other.0)
        }
    }

    impl<const N: Int> Mul for Modular<{ N }> {
        type Output = Self;

        fn mul(self, other: Self) -> Self::Output {
            Self::new(self.0 * other.0)
        }
    }

    impl<const N: Int> Sub for Modular<{ N }> {
        type Output = Self;

        fn sub(self, other: Self) -> Self::Output {
            Self::new((N - other.0) + self.0)
        }
    }

    /// Division for prime modulus. This currently fails at runtime for
    /// composite `N`; as const generics are stabilized I hope to promote this
    /// to a compile-time check with a `where is_prime({ N })` clause.
    impl<const N: Int> Div for Modular<{ N }> {
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

    impl<const N: Int> PartialEq for Modular<{ N }> {
        fn eq(&self, other: &Self) -> bool {
            self.0 == other.0
        }
    }
}

mod primes {
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

    const fn bit_len(n: Int) -> u32 {
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
    use super::modular::Modular;
    use super::Int;

    const MODULUS: Int = 7;

    #[test]
    fn residue_class_equality() {
        for v in 0..MODULUS {
            let m = Modular::<MODULUS>::new(v);
            for n in 0..=4 {
                assert_eq!(m, Modular::<MODULUS>::new(v + n * MODULUS));
            }
        }
    }

    #[test]
    fn neg_ok() {
        for v in 0..MODULUS {
            let m = Modular::<MODULUS>::new(v);
            assert_eq!(-m, Modular::<MODULUS>::new(MODULUS - v));
        }
    }

    #[test]
    fn add_ok() {
        for v1 in 0..MODULUS {
            for v2 in 0..MODULUS {
                let m1 = Modular::<MODULUS>::new(v1);
                let m2 = Modular::<MODULUS>::new(v2);
                assert_eq!(m1 + m2, Modular::<MODULUS>::new(v1 + v2));
            }
        }
    }

    #[test]
    fn mul_ok() {
        for v1 in 0..MODULUS {
            for v2 in 0..MODULUS {
                let m1 = Modular::<MODULUS>::new(v1);
                let m2 = Modular::<MODULUS>::new(v2);
                assert_eq!(m1 * m2, Modular::<MODULUS>::new(v1 * v2));
            }
        }
    }

    #[test]
    fn sub_ok() {
        for v1 in 0..MODULUS {
            for v2 in 0..MODULUS {
                let m1 = Modular::<MODULUS>::new(v1);
                let m2 = Modular::<MODULUS>::new(v2);
                assert_eq!(
                    m1 - m2,
                    Modular::<MODULUS>::new(v1) + (-Modular::<MODULUS>::new(v2))
                );
            }
        }
    }

    #[test]
    fn div_ok() {
        for v1 in 1..MODULUS {
            for v2 in 1..MODULUS {
                let m1 = Modular::<MODULUS>::new(v1);
                let m2 = Modular::<MODULUS>::new(v2);
                assert_eq!((m1 / m2) * m2, m1,);
            }
        }
    }

    #[test]
    #[should_panic]
    fn div_fail_composite() {
        const COMPOSITE: Int = 6;
        let m1 = Modular::<COMPOSITE>::new(4);
        let m2 = Modular::<COMPOSITE>::new(2);
        let _m = m1 / m2;
    }

    #[test]
    fn pow_ok() {
        for v in 0..=MODULUS {
            for exp in 0..=10 {
                let m = Modular::<MODULUS>::new(v);
                assert_eq!(m.pow(exp), Modular::<MODULUS>::new(v.pow(exp)));
            }
        }
    }
}
