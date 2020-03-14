#![allow(incomplete_features)]
#![feature(const_generics)]

pub type Int = u32;

/// TODO: here are some behaviors I would like.
///
/// * Implementations should depend on magnitude of N, and be determined at
///   compile time. For example there may be extra care taken with respect to
///   wrapping for large-enough `N`, and small exponentials might be best
///   implemented by repeated multiplication.
///
/// * Wrapping ranges should be added.
mod modular {
    use super::Int;
    use std::cmp::PartialEq;
    use std::ops::{Add, Mul, Neg, Sub};

    #[derive(Debug)]
    pub struct Modular<const N: Int>(Int);

    impl<const N: Int> Modular<{ N }> {
        pub fn new(val: Int) -> Self {
            Self { 0: val % { N } }
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
            Self::new((self.0 + other.0) % { N })
        }
    }

    impl<const N: Int> Mul for Modular<{ N }> {
        type Output = Self;

        fn mul(self, other: Self) -> Self::Output {
            Self::new((self.0 * other.0) % { N })
        }
    }

    impl<const N: Int> Sub for Modular<{ N }> {
        type Output = Self;

        fn sub(self, other: Self) -> Self::Output {
            Self::new((N - other.0) + self.0)
        }
    }

    impl<const N: Int> PartialEq for Modular<{ N }> {
        fn eq(&self, other: &Self) -> bool {
            self.0 == other.0
        }
    }
}

#[cfg(test)]
mod tests {
    use super::modular::Modular;
    use super::Int;

    const MODULUS: Int = 7;

    #[test]
    fn residue_class_equality() {
        for v in 0..=MODULUS {
            let m = Modular::<MODULUS>::new(v);
            for n in 0..=4 {
                assert_eq!(m, Modular::<MODULUS>::new(v + n * MODULUS));
            }
        }
    }

    #[test]
    fn neg_correct() {
        for v in 0..=MODULUS {
            let m = Modular::<MODULUS>::new(v);
            assert_eq!(-m, Modular::<MODULUS>::new(MODULUS - v));
        }
    }

    #[test]
    fn add_correct() {
        for v1 in 0..=MODULUS {
            for v2 in 0..=MODULUS {
                let m1 = Modular::<MODULUS>::new(v1);
                let m2 = Modular::<MODULUS>::new(v2);
                assert_eq!(m1 + m2, Modular::<MODULUS>::new(v1 + v2));
            }
        }
    }

    #[test]
    fn mul_correct() {
        for v1 in 0..=MODULUS {
            for v2 in 0..=MODULUS {
                let m1 = Modular::<MODULUS>::new(v1);
                let m2 = Modular::<MODULUS>::new(v2);
                assert_eq!(m1 * m2, Modular::<MODULUS>::new(v1 * v2));
            }
        }
    }

    #[test]
    fn sub_correct() {
        for v1 in 0..=MODULUS {
            for v2 in 0..=MODULUS {
                let m1 = Modular::<MODULUS>::new(v1);
                let m2 = Modular::<MODULUS>::new(v2);
                assert_eq!(
                    m1 - m2,
                    Modular::<MODULUS>::new(v1) + (-Modular::<MODULUS>::new(v2))
                );
            }
        }
    }
}
