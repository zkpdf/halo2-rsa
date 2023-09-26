//! This library provides a RSA verification circuit compatible with the [halo2 library developed by privacy-scaling-explorations team](https://github.com/privacy-scaling-explorations/halo2).
//!
//! A chip in this library, [`RSAConfig`], defines constraints for verifying the RSA relations, specifically modular power `x^e mod n` and [pkcs1v15 signature](https://www.rfc-editor.org/rfc/rfc3447) verification.
//! Its circuit configuration differs depending on whether the exponent parameter `e` of the RSA public key is variable or fixed.
//! For example, since `e` is often fixed to `65537` in the case of pkcs1v15 signature verification, defining `e` as a fixed parameter [`RSAPubE::Fix`] can optimize the number of constraints.

pub mod big_uint;
use std::marker::PhantomData;

pub use big_uint::*;

use halo2_base::{
    utils::BigPrimeField,
    AssignedValue,
};
use num_bigint::BigUint;

mod chip;
mod instructions;
pub use chip::*;
pub use instructions::*;

/// A parameter `e` in the RSA public key that is about to be assigned.
#[derive(Clone, Debug)]
pub enum RSAPubE {
    /// A variable parameter `e`.
    Var(BigUint),
    /// A fixed parameter `e`.
    Fix(BigUint),
}

/// A parameter `e` in the assigned RSA public key.
#[derive(Clone, Debug)]
pub enum AssignedRSAPubE<F: BigPrimeField> {
    /// A variable parameter `e`.
    Var(AssignedValue<F>),
    /// A fixed parameter `e`.
    Fix(BigUint),
}

/// RSA public key that is about to be assigned.
#[derive(Clone, Debug)]
pub struct RSAPublicKey<F: BigPrimeField> {
    /// a modulus parameter
    pub n: BigUint,
    /// an exponent parameter
    pub e: RSAPubE,
    _f: PhantomData<F>,
}

impl<F: BigPrimeField> RSAPublicKey<F> {
    /// Creates new [`RSAPublicKey`] from `n` and `e`.
    ///
    /// # Arguments
    /// * n - an integer of `n`.
    /// * e - a parameter `e`.
    ///
    /// # Return values
    /// Returns new [`RSAPublicKey`].
    pub fn new(n: BigUint, e: RSAPubE) -> Self {
        Self {
            n,
            e,
            _f: PhantomData,
        }
    }
}

/// An assigned RSA public key.
#[derive(Clone, Debug)]
pub struct AssignedRSAPublicKey<F: BigPrimeField> {
    /// a modulus parameter
    pub n: AssignedBigUint<F, Fresh>,
    /// an exponent parameter
    pub e: AssignedRSAPubE<F>,
}

impl<F: BigPrimeField> AssignedRSAPublicKey<F> {
    /// Creates new [`AssignedRSAPublicKey`] from assigned `n` and `e`.
    ///
    /// # Arguments
    /// * n - an assigned integer of `n`.
    /// * e - an assigned parameter `e`.
    ///
    /// # Return values
    /// Returns new [`AssignedRSAPublicKey`].
    pub fn new(n: AssignedBigUint<F, Fresh>, e: AssignedRSAPubE<F>) -> Self {
        Self { n, e }
    }
}

/// RSA signature that is about to be assigned.
#[derive(Clone, Debug)]
pub struct RSASignature<F: BigPrimeField> {
    c: BigUint,
    _f: PhantomData<F>,
}

impl<F: BigPrimeField> RSASignature<F> {
    /// Creates new [`RSASignature`] from its integer.
    ///
    /// # Arguments
    /// * c - an integer of the signature.
    ///
    /// # Return values
    /// Returns new [`RSASignature`].
    pub fn new(c: BigUint) -> Self {
        Self { c, _f: PhantomData }
    }

    // pub fn without_witness() -> Self {
    //     let c = Value::unknown();
    //     Self { c, _f: PhantomData }
    // }
}

/// An assigned RSA signature.
#[derive(Clone, Debug)]
pub struct AssignedRSASignature<F: BigPrimeField> {
    c: AssignedBigUint<F, Fresh>,
}

impl<F: BigPrimeField> AssignedRSASignature<F> {
    /// Creates new [`AssignedRSASignature`] from its assigned integer.
    ///
    /// # Arguments
    /// * c - an assigned integer of the signature.
    ///
    /// # Return values
    /// Returns new [`AssignedRSASignature`].
    pub fn new(c: AssignedBigUint<F, Fresh>) -> Self {
        Self { c }
    }
}