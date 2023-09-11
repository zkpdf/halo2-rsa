use crate::big_uint::BigUintInstructions;
use crate::{
    AssignedBigUint, AssignedRSAPubE, AssignedRSAPublicKey, AssignedRSASignature, BigUintConfig,
    Fresh, RSAInstructions, RSAPubE, RSAPublicKey, RSASignature,
};
use halo2_base::halo2_proofs::plonk::Error;
use halo2_base::QuantumCell;
use halo2_base::{
    gates::{flex_gate::GateChip, range::RangeChip, GateInstructions, RangeInstructions},
    utils::{biguint_to_fe, fe_to_biguint, BigPrimeField},
    AssignedValue, Context,
};

use num_bigint::BigUint;

/// Configuration for [`RSAConfig`].
#[derive(Clone, Debug)]
pub struct RSAConfig<F: BigPrimeField> {
    /// Configuration for [`BigUintConfig`].
    biguint_config: BigUintConfig<F>,
    /// The default bit length of [`Fresh`] type integers in this chip.
    default_bits: usize,
    /// The bit length of exponents.
    exp_bits: usize,
}

impl<F: BigPrimeField> RSAInstructions<F> for RSAConfig<F> {
    /// Assigns a [`AssignedRSAPublicKey`].
    ///
    /// # Arguments
    /// * `ctx` - a region context.
    /// * `public_key` - a RSA public key to assign.
    ///
    /// # Return values
    /// Returns a new [`AssignedRSAPublicKey`].
    fn assign_public_key(
        &self,
        ctx: &mut Context<F>,
        public_key: RSAPublicKey<F>,
    ) -> Result<AssignedRSAPublicKey<F>, Error> {
        let biguint_config = self.biguint_config();
        let n = biguint_config.assign_integer(ctx, &public_key.n, self.default_bits)?;
        let e = match public_key.e {
            RSAPubE::Var(e) => {
                let assigned = ctx.load_witness(biguint_to_fe(&e));
                self.range().range_check(ctx, assigned, self.exp_bits);
                AssignedRSAPubE::Var(assigned)
            }
            RSAPubE::Fix(e) => AssignedRSAPubE::Fix(e),
        };
        Ok(AssignedRSAPublicKey::new(n, e))
    }

    /// Assigns a [`AssignedRSASignature`].
    ///
    /// # Arguments
    /// * `ctx` - a region context.
    /// * `signature` - a RSA signature to assign.
    ///
    /// # Return values
    /// Returns a new [`AssignedRSASignature`].
    fn assign_signature(
        &self,
        ctx: &mut Context<F>,
        signature: RSASignature<F>,
    ) -> Result<AssignedRSASignature<F>, Error> {
        let biguint_config = self.biguint_config();
        let c = biguint_config.assign_integer(ctx, &signature.c, self.default_bits)?;
        Ok(AssignedRSASignature::new(c))
    }

    /// Given a base `x`, a RSA public key (e,n), performs the modular power `x^e mod n`.
    ///
    /// # Arguments
    /// * `ctx` - a region context.
    /// * `x` - a base integer.
    /// * `public_key` - an assigned RSA public key.
    ///
    /// # Return values
    /// Returns the modular power result `x^e mod n` as [`AssignedBigUint<F, Fresh>`].
    fn modpow_public_key(
        &self,
        ctx: &mut Context<F>,
        x: &AssignedBigUint<F, Fresh>,
        public_key: &AssignedRSAPublicKey<F>,
    ) -> Result<AssignedBigUint<F, Fresh>, Error> {
        let biguint_config = self.biguint_config();
        biguint_config.assert_in_field(ctx, x, &public_key.n)?;
        let powed = match &public_key.e {
            AssignedRSAPubE::Var(e) => {
                biguint_config.pow_mod(ctx, x, e, &public_key.n, self.exp_bits)
            }
            AssignedRSAPubE::Fix(e) => biguint_config.pow_mod_fixed_exp(ctx, x, e, &public_key.n),
        }?;
        Ok(powed)
    }

    /// Given a RSA public key, a message hashed with SHA256, and a pkcs1v15 signature, verifies the signature with the public key and the hashed messaged.
    ///
    /// # Arguments
    /// * `ctx` - a region context.
    /// * `public_key` - an assigned RSA public key.
    /// * `hashed_msg` - an assigned integer of the message hashed with SHA256.
    /// * `signature` - an assigned pkcs1v15 signature.
    ///
    /// # Return values
    /// Returns the assigned bit as [`AssignedValue<F>`].
    /// If `signature` is valid for `public_key` and `hashed_msg`, the bit is equivalent to one.
    /// Otherwise, the bit is equivalent to zero.
    fn verify_pkcs1v15_signature(
        &self,
        ctx: &mut Context<F>,
        public_key: &AssignedRSAPublicKey<F>,
        hashed_msg: &[AssignedValue<F>],
        signature: &AssignedRSASignature<F>,
    ) -> Result<AssignedValue<F>, Error> {
        assert_eq!(self.biguint_config.limb_bits(), 64);
        let gate = self.gate();
        let mut is_eq = ctx.load_constant(F::one());
        let powed = self.modpow_public_key(ctx, &signature.c, public_key)?;
        let hash_len = hashed_msg.len();
        assert_eq!(hash_len, 4);
        // 1. Check hashed data
        // 64 * 4 = 256 bit, that is the first 4 numbers.
        for (limb, hash) in powed.limbs()[0..hash_len].iter().zip(hashed_msg.iter()) {
            let is_hash_eq = gate.is_equal(
                ctx,
                QuantumCell::Existing(*limb),
                QuantumCell::Existing(*hash),
            );
            is_eq = gate.and(
                ctx,
                QuantumCell::Existing(is_eq),
                QuantumCell::Existing(is_hash_eq),
            );
        }

        // 2. Check hash prefix and 1 byte 0x00
        // sha256/152 bit
        // 0b00110000001100010011000000001101000001100000100101100000100001100100100000000001011001010000001100000100000000100000000100000101000000000000010000100000
        let is_prefix_64_1_eq = gate.is_equal(
            ctx,
            QuantumCell::Existing(powed.limbs()[hash_len]),
            QuantumCell::Constant(biguint_to_fe(&BigUint::from(217300885422736416u64))),
        );
        let is_prefix_64_2_eq = gate.is_equal(
            ctx,
            QuantumCell::Existing(powed.limbs()[hash_len + 1]),
            QuantumCell::Constant(biguint_to_fe(&BigUint::from(938447882527703397u64))),
        );
        let is_eq = gate.and(
            ctx,
            QuantumCell::Existing(is_eq),
            QuantumCell::Existing(is_prefix_64_1_eq),
        );
        let is_eq = gate.and(
            ctx,
            QuantumCell::Existing(is_eq),
            QuantumCell::Existing(is_prefix_64_2_eq),
        );
        // remain 24 bit
        let u32_v: BigUint = BigUint::from(1usize) << 32;
        let (remain_low, remain_high) = {
            let a = powed.limb(hash_len + 2).value();
            let big_v = fe_to_biguint(a);
            let low = biguint_to_fe::<F>(&(&big_v % &u32_v));
            let high = biguint_to_fe::<F>(&(&big_v / &u32_v));
            (low, high)
        };
        let range = self.range();
        let remain_low = ctx.load_witness(remain_low);
        range.range_check(ctx, remain_low, 32);
        let remain_high = ctx.load_witness(remain_high);
        range.range_check(ctx, remain_high, 32);
        let remain_concat = gate.mul_add(
            ctx,
            QuantumCell::Existing(remain_high),
            QuantumCell::Constant(biguint_to_fe(&u32_v)),
            QuantumCell::Existing(remain_low),
        );
        gate.is_equal(
            ctx,
            QuantumCell::Existing(powed.limbs()[hash_len + 2]),
            QuantumCell::Existing(remain_concat),
        );
        let is_prefix_32_eq = gate.is_equal(
            ctx,
            QuantumCell::Existing(remain_low),
            QuantumCell::Constant(biguint_to_fe(&BigUint::from(3158320u32))),
        );
        let is_eq = gate.and(
            ctx,
            QuantumCell::Existing(is_eq),
            QuantumCell::Existing(is_prefix_32_eq),
        );

        // 3. Check PS and em[1] = 1. the same code like golang std lib rsa.VerifyPKCS1v15
        let is_ff_32_eq = gate.is_equal(
            ctx,
            QuantumCell::Existing(remain_high),
            QuantumCell::Constant(biguint_to_fe(&BigUint::from(4294967295u32))),
        );
        let mut is_eq = gate.and(
            ctx,
            QuantumCell::Existing(is_eq),
            QuantumCell::Existing(is_ff_32_eq),
        );
        let num_limbs = self.default_bits / self.biguint_config().limb_bits();
        for limb in powed.limbs()[(hash_len + 3)..(num_limbs - 1)].iter() {
            let is_ff_64_eq = gate.is_equal(
                ctx,
                QuantumCell::Existing(*limb),
                QuantumCell::Constant(biguint_to_fe(&BigUint::from(18446744073709551615u64))),
            );
            is_eq = gate.and(
                ctx,
                QuantumCell::Existing(is_eq),
                QuantumCell::Existing(is_ff_64_eq),
            );
        }
        //562949953421311 = 0b1111111111111111111111111111111111111111111111111 = 0x00 || 0x01 || (0xff)^*
        let is_last_em_eq = gate.is_equal(
            ctx,
            QuantumCell::Existing(powed.limbs()[num_limbs - 1]),
            QuantumCell::Constant(biguint_to_fe(&BigUint::from(562949953421311u64))),
        );
        let is_eq = gate.and(
            ctx,
            QuantumCell::Existing(is_eq),
            QuantumCell::Existing(is_last_em_eq),
        );
        Ok(is_eq.clone())
    }
}

impl<F: BigPrimeField> RSAConfig<F> {
    /// Creates new [`RSAConfig`] from [`BigUintInstructions`].
    ///
    /// # Arguments
    /// * biguint_config - a configuration for [`BigUintConfig`].
    /// * default_bits - the default bit length of [`Fresh`] type integers in this chip.
    /// * exp_bits - the bit length of exponents.
    ///
    /// # Return values
    /// Returns new [`RSAConfig`].
    pub fn construct(
        biguint_config: BigUintConfig<F>,
        default_bits: usize,
        exp_bits: usize,
    ) -> Self {
        Self {
            biguint_config,
            default_bits,
            exp_bits,
        }
    }

    /// Getter for [`BigUintConfig`].
    pub fn biguint_config(&self) -> &BigUintConfig<F> {
        &self.biguint_config
    }

    /// Getter for [`GateChip`].
    pub fn gate(&self) -> &GateChip<F> {
        &self.biguint_config.gate()
    }

    /// Getter for [`RangeChip`].
    pub fn range(&self) -> &RangeChip<F> {
        &self.biguint_config.range()
    }
}

#[cfg(test)]
mod test {
    use crate::big_uint::decompose_biguint;
    use std::str::FromStr;
    use super::*;
    use halo2_base::halo2_proofs::{
        dev::MockProver,
        halo2curves::bn256::Fr,
    };
    use halo2_base::gates::RangeChip;
    use halo2_base::gates::builder::{
        GateThreadBuilder, RangeCircuitBuilder
    };
    use crate::big_pow_mod;

    #[test]
    fn test_2048_modpow_public_key() {        
        let k: usize = 18;

        // Circuit inputs
        let limb_bits = 64;
        let default_bits = 2048;
        let exp_bits = 5;
        let default_e = 65537 as u32;
        
        // Configure builder
        let mut builder = GateThreadBuilder::<Fr>::mock();

        let lookup_bits: usize = k - 1;
        // NOTE: Need to set var to load lookup table
        std::env::set_var("LOOKUP_BITS", lookup_bits.to_string());

        let range = RangeChip::<Fr>::default(lookup_bits);
        let bigint_chip = BigUintConfig::construct(range, limb_bits);
        let chip = RSAConfig::construct(bigint_chip, default_bits, exp_bits);
        let ctx = builder.main(0);
        let e_fix = RSAPubE::Fix(BigUint::from(default_e));
        let n_big = BigUint::from_str("27333278531038650284292446400685983964543820405055158402397263907659995327446166369388984969315774410223081038389734916442552953312548988147687296936649645550823280957757266695625382122565413076484125874545818286099364801140117875853249691189224238587206753225612046406534868213180954324992542640955526040556053150097561640564120642863954208763490114707326811013163227280580130702236406906684353048490731840275232065153721031968704703853746667518350717957685569289022049487955447803273805415754478723962939325870164033644600353029240991739641247820015852898600430315191986948597672794286676575642204004244219381500407").unwrap();
        let public_key = RSAPublicKey::new(n_big.clone(), e_fix);
        let public_key = chip.assign_public_key(ctx, public_key);
        let msg_big = BigUint::from_str("83814198383102558219731078260892729932246618004265700685467928187377105751529").unwrap();
        let msg_assigned = chip.biguint_config.assign_integer(
            ctx,
            &msg_big.clone(),
            default_bits,
        );

        let powed = chip.modpow_public_key(ctx, &msg_assigned.unwrap(), &public_key.unwrap());
        let expected_powed = big_pow_mod(&msg_big, &BigUint::from(default_e), &n_big);
        let expected_powed = chip.biguint_config().assign_constant(ctx, expected_powed);
        chip.biguint_config().assert_equal_fresh(ctx, &powed.unwrap(), &expected_powed.unwrap()).unwrap();

        // Minimum rows is the number of rows used for blinding factors
        // This depends on the circuit itself, but we can guess the number and change it if something breaks (default 9 usually works)
        builder.config(k, Some(9));

        // Create mock circuit
        let circuit = RangeCircuitBuilder::mock(builder);

        // Run mock prover to ensure output is correct
        MockProver::run(k as u32, &circuit, vec![]).unwrap().assert_satisfied();
    }

    #[test]
    fn test_bad_2048_modpow_public_key() {        
        let k: usize = 18;

        // Circuit inputs
        let limb_bits = 64;
        let default_bits = 2048;
        let exp_bits = 5;
        let default_e = 65537 as u32;
        
        // Configure builder
        let mut builder = GateThreadBuilder::<Fr>::mock();

        let lookup_bits: usize = k - 1;
        // NOTE: Need to set var to load lookup table
        std::env::set_var("LOOKUP_BITS", lookup_bits.to_string());

        let range = RangeChip::<Fr>::default(lookup_bits);
        let bigint_chip = BigUintConfig::construct(range, limb_bits);
        let chip = RSAConfig::construct(bigint_chip, default_bits, exp_bits);
        let ctx = builder.main(0);
        let e_fix = RSAPubE::Fix(BigUint::from(default_e));
        let n_big = BigUint::from_str("27333278531038650284292446400685983964543820405055158402397263907659995327446166369388984969315774410223081038389734916442552953312548988147687296936649645550823280957757266695625382122565413076484125874545818286099364801140117875853249691189224238587206753225612046406534868213180954324992542640955526040556053150097561640564120642863954208763490114707326811013163227280580130702236406906684353048490731840275232065153721031968704703853746667518350717957685569289022049487955447803273805415754478723962939325870164033644600353029240991739641247820015852898600430315191986948597672794286676575642204004244219381500407").unwrap();
        let public_key = RSAPublicKey::new(n_big.clone(), e_fix);
        let public_key = chip.assign_public_key(ctx, public_key);
        let msg_big = BigUint::from_str("83814198383102558219731078260892729932246618004265700685467928187377105751529").unwrap();
        let msg_assigned = chip.biguint_config.assign_integer(
            ctx,
            &msg_big.clone(),
            default_bits,
        );

        let powed = chip.modpow_public_key(ctx, &msg_assigned.unwrap(), &public_key.unwrap());
        let powed = powed.unwrap().clone();
        let max = chip.biguint_config().max_value(ctx, powed.num_limbs());
        chip.biguint_config().assert_equal_fresh(ctx, &powed, &max.unwrap()).unwrap();

        // Minimum rows is the number of rows used for blinding factors
        // This depends on the circuit itself, but we can guess the number and change it if something breaks (default 9 usually works)
        builder.config(k, Some(9));

        // Create mock circuit
        let circuit = RangeCircuitBuilder::mock(builder);

        // Run mock prover to ensure output is correct
        let is_err = MockProver::run(k as u32, &circuit, vec![]).unwrap().verify().is_err();
        assert_eq!(is_err, true);
    }

    #[test]
    fn test_1024_modpow_public_key() {        
        let k: usize = 18;

        // Circuit inputs
        let limb_bits = 64;
        let default_bits = 1024;
        let exp_bits = 5;
        let default_e = 65537 as u32;
        
        // Configure builder
        let mut builder = GateThreadBuilder::<Fr>::mock();

        let lookup_bits: usize = k - 1;
        // NOTE: Need to set var to load lookup table
        std::env::set_var("LOOKUP_BITS", lookup_bits.to_string());

        let range = RangeChip::<Fr>::default(lookup_bits);
        let bigint_chip = BigUintConfig::construct(range, limb_bits);
        let chip = RSAConfig::construct(bigint_chip, default_bits, exp_bits);
        let ctx = builder.main(0);
        let e_fix = RSAPubE::Fix(BigUint::from(default_e));
        let n_big = BigUint::from_str("107289837545940078268745022404080197756713492641688496535588794073231113663754058018862686762411228470731274703520877348777567694438387351688322419762264406460523426827357314688051865748955987197068553714344169462788708049399769970047547738378550534865494278049193738022398562701983786771227004540503235555427").unwrap();
        let public_key = RSAPublicKey::new(n_big.clone(), e_fix);
        let public_key = chip.assign_public_key(ctx, public_key);
        let msg_big = BigUint::from_str("77929134187608511922495239264200453516249189680211783157419138967626951463678384095540409755596022527110500588052868475990692956380263184337020353767554108632525056703455094349084868832834519825911531623507412532278652516715214908372427289788659924082086149173428600500839052600213260337159219251648111234888").unwrap();
        let msg_assigned = chip.biguint_config.assign_integer(
            ctx,
            &msg_big.clone(),
            default_bits,
        );

        let powed = chip.modpow_public_key(ctx, &msg_assigned.unwrap(), &public_key.unwrap());
        let expected_powed = big_pow_mod(&msg_big, &BigUint::from(default_e), &n_big);
        let expected_powed = chip.biguint_config().assign_constant(ctx, expected_powed);
        chip.biguint_config().assert_equal_fresh(ctx, &powed.unwrap(), &expected_powed.unwrap()).unwrap();

        // Minimum rows is the number of rows used for blinding factors
        // This depends on the circuit itself, but we can guess the number and change it if something breaks (default 9 usually works)
        builder.config(k, Some(9));

        // Create mock circuit
        let circuit = RangeCircuitBuilder::mock(builder);

        // Run mock prover to ensure output is correct
        MockProver::run(k as u32, &circuit, vec![]).unwrap().assert_satisfied();
    }

    #[test]
    fn test_bad_1024_modpow_public_key() {        
        let k: usize = 18;

        // Circuit inputs
        let limb_bits = 64;
        let default_bits = 1024;
        let exp_bits = 5;
        let default_e = 65537 as u32;
        
        // Configure builder
        let mut builder = GateThreadBuilder::<Fr>::mock();

        let lookup_bits: usize = k - 1;
        // NOTE: Need to set var to load lookup table
        std::env::set_var("LOOKUP_BITS", lookup_bits.to_string());

        let range = RangeChip::<Fr>::default(lookup_bits);
        let bigint_chip = BigUintConfig::construct(range, limb_bits);
        let chip = RSAConfig::construct(bigint_chip, default_bits, exp_bits);
        let ctx = builder.main(0);
        let e_fix = RSAPubE::Fix(BigUint::from(default_e));
        let n_big = BigUint::from_str("107289837545940078268745022404080197756713492641688496535588794073231113663754058018862686762411228470731274703520877348777567694438387351688322419762264406460523426827357314688051865748955987197068553714344169462788708049399769970047547738378550534865494278049193738022398562701983786771227004540503235555427").unwrap();
        let public_key = RSAPublicKey::new(n_big.clone(), e_fix);
        let public_key = chip.assign_public_key(ctx, public_key);
        let msg_big = BigUint::from_str("77929134187608511922495239264200453516249189680211783157419138967626951463678384095540409755596022527110500588052868475990692956380263184337020353767554108632525056703455094349084868832834519825911531623507412532278652516715214908372427289788659924082086149173428600500839052600213260337159219251648111234888").unwrap();
        let msg_assigned = chip.biguint_config.assign_integer(
            ctx,
            &msg_big.clone(),
            default_bits,
        );

        let powed = chip.modpow_public_key(ctx, &msg_assigned.unwrap(), &public_key.unwrap());
        let powed = powed.unwrap().clone();
        let max = chip.biguint_config().max_value(ctx, powed.num_limbs());
        chip.biguint_config().assert_equal_fresh(ctx, &powed, &max.unwrap()).unwrap();

        // Minimum rows is the number of rows used for blinding factors
        // This depends on the circuit itself, but we can guess the number and change it if something breaks (default 9 usually works)
        builder.config(k, Some(9));

        // Create mock circuit
        let circuit = RangeCircuitBuilder::mock(builder);

        // Run mock prover to ensure output is correct
        let is_err = MockProver::run(k as u32, &circuit, vec![]).unwrap().verify().is_err();
        assert_eq!(is_err, true);
    }

    #[test]
    fn test_2048_verify_pkcs1v15_signature() {        
        let k: usize = 18;

        // Circuit inputs
        let limb_bits = 64;
        let default_bits = 2048;
        let exp_bits = 5;
        let default_e = 65537 as u32;
        
        // Configure builder
        let mut builder = GateThreadBuilder::<Fr>::mock();

        let lookup_bits: usize = k - 1;
        // NOTE: Need to set var to load lookup table
        std::env::set_var("LOOKUP_BITS", lookup_bits.to_string());

        let range = RangeChip::<Fr>::default(lookup_bits);
        let bigint_chip = BigUintConfig::construct(range, limb_bits);
        let chip = RSAConfig::construct(bigint_chip, default_bits, exp_bits);
        let ctx = builder.main(0);
        let e_fix = RSAPubE::Fix(BigUint::from(default_e));
        let n_big = BigUint::from_str("27333278531038650284292446400685983964543820405055158402397263907659995327446166369388984969315774410223081038389734916442552953312548988147687296936649645550823280957757266695625382122565413076484125874545818286099364801140117875853249691189224238587206753225612046406534868213180954324992542640955526040556053150097561640564120642863954208763490114707326811013163227280580130702236406906684353048490731840275232065153721031968704703853746667518350717957685569289022049487955447803273805415754478723962939325870164033644600353029240991739641247820015852898600430315191986948597672794286676575642204004244219381500407").unwrap();
        let public_key = RSAPublicKey::new(n_big, e_fix);
        let public_key = chip.assign_public_key(ctx, public_key);
        let sign_big = BigUint::from_str("27166015521685750287064830171899789431519297967327068200526003963687696216659347317736779094212876326032375924944649760206771585778103092909024744594654706678288864890801000499430246054971129440518072676833029702477408973737931913964693831642228421821166326489172152903376352031367604507095742732994611253344812562891520292463788291973539285729019102238815435155266782647328690908245946607690372534644849495733662205697837732960032720813567898672483741410294744324300408404611458008868294953357660121510817012895745326996024006347446775298357303082471522757091056219893320485806442481065207020262668955919408138704593").unwrap();
        let sign = RSASignature::new(sign_big);
        let sign = chip.assign_signature(ctx, sign);
        let hashed_msg_big = BigUint::from_str("83814198383102558219731078260892729932246618004265700685467928187377105751529").unwrap();
        let hashed_msg_limbs = decompose_biguint::<Fr>(&hashed_msg_big, 4, 256/4);
        let hashed_msg_assigned = hashed_msg_limbs.into_iter().map(|limb| ctx.load_witness(limb)).collect::<Vec<AssignedValue<Fr>>>();
        
        let is_valid = chip.verify_pkcs1v15_signature(ctx, &public_key.unwrap(), &hashed_msg_assigned, &sign.unwrap());

        chip.gate().assert_is_const(ctx, &is_valid.unwrap(), &Fr::one());

        // Minimum rows is the number of rows used for blinding factors
        // This depends on the circuit itself, but we can guess the number and change it if something breaks (default 9 usually works)
        builder.config(k, Some(9));

        // Create mock circuit
        let circuit = RangeCircuitBuilder::mock(builder);

        // Run mock prover to ensure output is correct
        MockProver::run(k as u32, &circuit, vec![]).unwrap().assert_satisfied();
    }

    #[test]
    fn test_bad_2048_verify_pkcs1v15_signature() {        
        let k: usize = 18;

        // Circuit inputs
        let limb_bits = 64;
        let default_bits = 2048;
        let exp_bits = 5;
        let default_e = 65537 as u32;
        
        // Configure builder
        let mut builder = GateThreadBuilder::<Fr>::mock();

        let lookup_bits: usize = k - 1;
        // NOTE: Need to set var to load lookup table
        std::env::set_var("LOOKUP_BITS", lookup_bits.to_string());

        let range = RangeChip::<Fr>::default(lookup_bits);
        let bigint_chip = BigUintConfig::construct(range, limb_bits);
        let chip = RSAConfig::construct(bigint_chip, default_bits, exp_bits);
        let ctx = builder.main(0);
        let e_fix = RSAPubE::Fix(BigUint::from(default_e));
        let n_big = BigUint::from_str("27333278531038650284292446400685983964543820405055158402397263907659995327446166369388984969315774410223081038389734916442552953312548988147687296936649645550823280957757266695625382122565413076484125874545818286099364801140117875853249691189224238587206753225612046406534868213180954324992542640955526040556053150097561640564120642863954208763490114707326811013163227280580130702236406906684353048490731840275232065153721031968704703853746667518350717957685569289022049487955447803273805415754478723962939325870164033644600353029240991739641247820015852898600430315191986948597672794286676575642204004244219381500407").unwrap();
        let public_key = RSAPublicKey::new(n_big, e_fix);
        let public_key = chip.assign_public_key(ctx, public_key);
        
        // Input bad signature
        let sign_big = BigUint::from_str("1234").unwrap();
        let sign = RSASignature::new(sign_big);
        let sign = chip.assign_signature(ctx, sign);
        let hashed_msg_big = BigUint::from_str("83814198383102558219731078260892729932246618004265700685467928187377105751529").unwrap();
        let hashed_msg_limbs = decompose_biguint::<Fr>(&hashed_msg_big, 4, 256/4);
        let hashed_msg_assigned = hashed_msg_limbs.into_iter().map(|limb| ctx.load_witness(limb)).collect::<Vec<AssignedValue<Fr>>>();
        
        let is_valid = chip.verify_pkcs1v15_signature(ctx, &public_key.unwrap(), &hashed_msg_assigned, &sign.unwrap());

        chip.gate().assert_is_const(ctx, &is_valid.unwrap(), &Fr::one());
        // Minimum rows is the number of rows used for blinding factors
        // This depends on the circuit itself, but we can guess the number and change it if something breaks (default 9 usually works)
        builder.config(k, Some(9));

        // Create mock circuit
        let circuit = RangeCircuitBuilder::mock(builder);

        // Run mock prover to ensure output is correct
        let is_err = MockProver::run(k as u32, &circuit, vec![]).unwrap().verify().is_err();
        assert_eq!(is_err, true);
    }

    #[test]
    fn test_2048_verify_pkcs1v15_signature_2() {        
        let k: usize = 18;

        // Circuit inputs
        let limb_bits = 64;
        let default_bits = 2048;
        let exp_bits = 5;
        let default_e = 65537 as u32;
        
        // Configure builder
        let mut builder = GateThreadBuilder::<Fr>::mock();

        let lookup_bits: usize = k - 1;
        // NOTE: Need to set var to load lookup table
        std::env::set_var("LOOKUP_BITS", lookup_bits.to_string());

        let range = RangeChip::<Fr>::default(lookup_bits);
        let bigint_chip = BigUintConfig::construct(range, limb_bits);
        let chip = RSAConfig::construct(bigint_chip, default_bits, exp_bits);
        let ctx = builder.main(0);
        let e_fix = RSAPubE::Fix(BigUint::from(default_e));
        let n_big = BigUint::from_str("24226501697440012621102249466312043787685293040734225606346036389705515508545746221669035424138747582133889500686654172873671086178893587422987328751464627501601101326475761646014534358699943642495332701081302954020983110372109611581202820849485662540890985814355975252780310958088652613376767040069489530039075302709233494829280591680666351811024913107949144932224439129715181798714328219977771472462901856297952813239115577652450722815852332547886777292613005505949100406231716599634852632308325816916535875123863510650526931916871614411907700873376659841257216885666098127478325534982891697988739616416855214839339").unwrap();
        let public_key = RSAPublicKey::new(n_big, e_fix);
        let public_key = chip.assign_public_key(ctx, public_key);
        let sign_big = BigUint::from_str("18928545496959757512579438348223103860103247450097569223971486743312798156950374943336714741350742176674694049986481729075548718599712271054643150030165230392897481507710187505775911256946250999396358633095137650326818007610162375520522758780751710735664264200260854016867498935206556916247099180950775474524799944404833222133011134000549939512938205188018503377612813102061504146765520561811620128786062447005833886367575841545493555268747671930923697279690399480501746857825917608323993022396398648205737336204493624060285359455268389160802763426461171262704764369336704988874821898000892148693988241020931055723252").unwrap();
        let sign = RSASignature::new(sign_big);
        let sign = chip.assign_signature(ctx, sign);
        let hashed_msg_big = BigUint::from_str("83814198383102558219731078260892729932246618004265700685467928187377105751529").unwrap();
        let hashed_msg_limbs = decompose_biguint::<Fr>(&hashed_msg_big, 4, 256/4);
        let hashed_msg_assigned = hashed_msg_limbs.into_iter().map(|limb| ctx.load_witness(limb)).collect::<Vec<AssignedValue<Fr>>>();

        let is_valid = chip.verify_pkcs1v15_signature(ctx, &public_key.unwrap(), &hashed_msg_assigned, &sign.unwrap());

        chip.gate().assert_is_const(ctx, &is_valid.unwrap(), &Fr::one());

        // Minimum rows is the number of rows used for blinding factors
        // This depends on the circuit itself, but we can guess the number and change it if something breaks (default 9 usually works)
        builder.config(k, Some(9));

        // Create mock circuit
        let circuit = RangeCircuitBuilder::mock(builder);

        // Run mock prover to ensure output is correct
        MockProver::run(k as u32, &circuit, vec![]).unwrap().assert_satisfied();
    }

    #[test]
    fn test_bad_2048_verify_pkcs1v15_signature_2() {        
        let k: usize = 18;

        // Circuit inputs
        let limb_bits = 64;
        let default_bits = 2048;
        let exp_bits = 5;
        let default_e = 65537 as u32;
        
        // Configure builder
        let mut builder = GateThreadBuilder::<Fr>::mock();

        let lookup_bits: usize = k - 1;
        // NOTE: Need to set var to load lookup table
        std::env::set_var("LOOKUP_BITS", lookup_bits.to_string());

        let range = RangeChip::<Fr>::default(lookup_bits);
        let bigint_chip = BigUintConfig::construct(range, limb_bits);
        let chip = RSAConfig::construct(bigint_chip, default_bits, exp_bits);
        let ctx = builder.main(0);
        let e_fix = RSAPubE::Fix(BigUint::from(default_e));
        let n_big = BigUint::from_str("24226501697440012621102249466312043787685293040734225606346036389705515508545746221669035424138747582133889500686654172873671086178893587422987328751464627501601101326475761646014534358699943642495332701081302954020983110372109611581202820849485662540890985814355975252780310958088652613376767040069489530039075302709233494829280591680666351811024913107949144932224439129715181798714328219977771472462901856297952813239115577652450722815852332547886777292613005505949100406231716599634852632308325816916535875123863510650526931916871614411907700873376659841257216885666098127478325534982891697988739616416855214839339").unwrap();
        let public_key = RSAPublicKey::new(n_big, e_fix);
        let public_key = chip.assign_public_key(ctx, public_key);
        
        // Input bad signature
        let sign_big = BigUint::from_str("18928545496959757512579438348223103860103247450097569223971486743312798156950374943336714741350742176674694049986481729075548718599712271054643150030165230392897481507710187505775911256946250999396358633095137650326818007610162375520522758780751710735664264200260854016867498935206556916247099180950775474524799944404833222133011134000549939512938205188018503377612813102061504146765520561811620128786062447005833886367575841545493555268747671930923697279690399480501746857825917608323993022396398648205737336204493624060285359455268389160802763426461171262704764369336704988874821898000892148693988241020931055723251").unwrap();
        let sign = RSASignature::new(sign_big);
        let sign = chip.assign_signature(ctx, sign);
        let hashed_msg_big = BigUint::from_str("83814198383102558219731078260892729932246618004265700685467928187377105751529").unwrap();
        let hashed_msg_limbs = decompose_biguint::<Fr>(&hashed_msg_big, 4, 256/4);
        let hashed_msg_assigned = hashed_msg_limbs.into_iter().map(|limb| ctx.load_witness(limb)).collect::<Vec<AssignedValue<Fr>>>();
        
        let is_valid = chip.verify_pkcs1v15_signature(ctx, &public_key.unwrap(), &hashed_msg_assigned, &sign.unwrap());

        chip.gate().assert_is_const(ctx, &is_valid.unwrap(), &Fr::one());
        // Minimum rows is the number of rows used for blinding factors
        // This depends on the circuit itself, but we can guess the number and change it if something breaks (default 9 usually works)
        builder.config(k, Some(9));

        // Create mock circuit
        let circuit = RangeCircuitBuilder::mock(builder);

        // Run mock prover to ensure output is correct
        let is_err = MockProver::run(k as u32, &circuit, vec![]).unwrap().verify().is_err();
        assert_eq!(is_err, true);
    }

}