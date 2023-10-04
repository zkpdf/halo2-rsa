use std::marker::PhantomData;

mod chip;
mod instructions;
mod utils;
pub use chip::*;
pub use instructions::*;
pub use utils::*;

use halo2_base::{utils::BigPrimeField, AssignedValue};
use halo2_ecc::bigint::OverflowInteger;
use num_bigint::BigUint;

#[derive(Debug, Clone)]
pub struct AssignedBigUint<F: BigPrimeField, T: RangeType> {
    int: OverflowInteger<F>,
    value: BigUint,
    _t: PhantomData<T>,
}

impl<F: BigPrimeField, T: RangeType> AssignedBigUint<F, T> {
    pub fn new(int: OverflowInteger<F>, value: BigUint) -> Self {
        Self {
            int,
            value,
            _t: PhantomData,
        }
    }

    pub fn limb(&self, i: usize) -> &AssignedValue<F> {
        &self.int.limbs[i]
    }

    pub fn num_limbs(&self) -> usize {
        self.int.limbs.len()
    }

    pub fn limbs(&self) -> &[AssignedValue<F>] {
        &self.int.limbs
    }

    pub fn value(&self) -> BigUint {
        self.value.clone()
    }

    pub fn extend_limbs(&self, num_extend_limbs: usize, zero_value: AssignedValue<F>) -> Self {
        let max_limb_bits = self.int_ref().max_limb_bits;
        let pre_num_limbs = self.num_limbs();
        let mut limbs = self.int.limbs.clone();
        for _ in 0..num_extend_limbs {
            limbs.push(zero_value.clone());
        }
        assert_eq!(pre_num_limbs + num_extend_limbs, limbs.len());
        let int = OverflowInteger::new(limbs, max_limb_bits);
        Self::new(int, self.value())
    }

    pub fn slice_limbs(&self, min: usize, max: usize) -> Self {
        let max_limb_bits = self.int_ref().max_limb_bits;
        let value = self.value();
        let limbs = &self.int.limbs;
        let int = OverflowInteger::new(limbs[min..=max].to_vec(), max_limb_bits);
        Self::new(int, value)
    }

    pub fn int_ref(&self) -> &OverflowInteger<F> {
        &self.int
    }
}

impl<F: BigPrimeField> AssignedBigUint<F, Fresh> {
    pub fn to_muled(self) -> AssignedBigUint<F, Muled> {
        AssignedBigUint::new(self.int, self.value)
    }
}

impl<F: BigPrimeField> AssignedBigUint<F, Muled> {
    pub fn to_fresh_unsafe(self) -> AssignedBigUint<F, Fresh> {
        AssignedBigUint::new(self.int, self.value)
    }
}

/// Trait for types representing a range of the limb.
pub trait RangeType: Clone {}

/// [`RangeType`] assigned to [`AssignedLimb`] and [`AssignedInteger`] that are not multiplied yet.
///
/// The maximum value of the [`Fresh`] type limb is defined in the chip implementing [`BigIntInstructions`] trait.
/// For example, [`BigIntChip`] has an `limb_width` parameter and limits the size of the [`Fresh`] type limb to be less than `2^(limb_width)`.
#[derive(Debug, Clone)]
pub struct Fresh {}
impl RangeType for Fresh {}

/// [`RangeType`] assigned to [`AssignedLimb`] and [`AssignedInteger`] that are already multiplied.
///
/// The value of the [`Muled`] type limb may overflow the maximum value of the [`Fresh`] type limb.
/// You can convert the [`Muled`] type integer to the [`Fresh`] type integer by calling [`BigIntInstructions::refresh`] function.
#[derive(Debug, Clone)]
pub struct Muled {}
impl RangeType for Muled {}