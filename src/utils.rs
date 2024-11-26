use bellpepper::gadgets::num::AllocatedNum;
use bellpepper_core::{
    boolean::{AllocatedBit, Boolean},
    ConstraintSystem, LinearCombination, SynthesisError,
};
use crypto_bigint::{Encoding, U256};
use ff::{PrimeField, PrimeFieldBits};

fn field_into_allocated_bits_le<Scalar, CS>(
    mut cs: CS,
    value: Option<Scalar>,
    n: usize, // number of bits
) -> Result<Vec<AllocatedBit>, SynthesisError>
where
    Scalar: PrimeField,
    Scalar: PrimeFieldBits,
    CS: ConstraintSystem<Scalar>,
{
    // Deconstruct in big-endian bit order
    let values = match value {
        Some(ref value) => {
            let field_char = Scalar::char_le_bits();
            let mut field_char = field_char.into_iter().rev();

            let mut tmp = Vec::with_capacity(Scalar::NUM_BITS as usize);

            let mut found_one = false;
            for b in value.to_le_bits().into_iter().rev() {
                // Skip leading bits
                found_one |= field_char.next().unwrap();
                if !found_one {
                    continue;
                }

                tmp.push(Some(b));
            }

            let out_bits: Vec<Option<bool>> = tmp.iter().rev().take(n).cloned().collect();
            assert_eq!(out_bits.len(), n);

            out_bits
        }
        None => vec![None; n],
    };

    // Allocate in little-endian order
    let bits = values
        .into_iter()
        .enumerate()
        .map(|(i, b)| AllocatedBit::alloc(cs.namespace(|| format!("bit {}", i)), b))
        .collect::<Result<Vec<_>, SynthesisError>>()?;

    assert_eq!(bits.len(), n);

    Ok(bits)
}

pub fn num_to_bits_le<Scalar, CS>(
    mut cs: CS,
    num: AllocatedNum<Scalar>,
    n: usize, //number of bits
) -> Result<Vec<Boolean>, SynthesisError>
where
    CS: ConstraintSystem<Scalar>,
    Scalar: PrimeFieldBits,
{
    let bits = field_into_allocated_bits_le(&mut cs, num.get_value(), n)?;

    let mut lc = LinearCombination::zero();
    let mut coeff = Scalar::ONE;

    for bit in bits.iter() {
        lc = lc + (coeff, bit.get_variable());

        coeff = coeff.double();
    }

    lc = lc - num.get_variable();

    cs.enforce(|| "unpacking constraint", |lc| lc, |lc| lc, |_| lc);

    Ok(bits.into_iter().map(Boolean::from).collect())
}

// Returns true if num0 < num1
pub fn is_less<Scalar, CS>(
    mut cs: CS,
    num0: AllocatedNum<Scalar>,
    num1: AllocatedNum<Scalar>,
    n: usize, //number of bits
) -> Result<Boolean, SynthesisError>
where
    CS: ConstraintSystem<Scalar>,
    Scalar: PrimeField<Repr = [u8; 32]>,
    Scalar: PrimeFieldBits,
{
    assert!(n < 255);
    let two_pow_n = Scalar::from_repr((U256::from(1u64) << n).to_le_bytes()).unwrap();
    let alloc_two_pow_n =
        AllocatedNum::alloc(&mut cs.namespace(|| "alloc two_pow_n"), || Ok(two_pow_n))?;
    let diff = sub(&mut cs.namespace(|| "num0 - num1"), &num0, &num1)?;
    let diff_plus = diff.add(&mut cs.namespace(|| "diff + two_pow_n"), &alloc_two_pow_n)?;

    let bits = field_into_allocated_bits_le(&mut cs, diff_plus.get_value(), n + 1)?;

    Ok(Boolean::from(bits[n].clone()).not())
}

// Returns true if num0 > num1
pub fn is_greater<Scalar, CS>(
    mut cs: CS,
    num0: AllocatedNum<Scalar>,
    num1: AllocatedNum<Scalar>,
    n: usize, //number of bits
) -> Result<Boolean, SynthesisError>
where
    CS: ConstraintSystem<Scalar>,
    Scalar: PrimeField<Repr = [u8; 32]>,
    Scalar: PrimeFieldBits,
{
    is_less(&mut cs, num1, num0, n)
}

// Returns true if num0 >= num1
pub fn is_greater_eq<Scalar, CS>(
    mut cs: CS,
    num0: AllocatedNum<Scalar>,
    num1: AllocatedNum<Scalar>,
    n: usize, //number of bits
) -> Result<Boolean, SynthesisError>
where
    CS: ConstraintSystem<Scalar>,
    Scalar: PrimeField<Repr = [u8; 32]>,
    Scalar: PrimeFieldBits,
{
    let one = AllocatedNum::alloc(&mut cs.namespace(|| "alloc one"), || Ok(Scalar::ONE))?;
    let num0_plus_one = num0.add(&mut cs.namespace(|| "num0 + 1"), &one)?;
    is_less(&mut cs, num1, num0_plus_one, n)
}

/// Returns (self - other)
pub fn sub<CS, Scalar>(
    mut cs: CS,
    a: &AllocatedNum<Scalar>,
    other: &AllocatedNum<Scalar>,
) -> Result<AllocatedNum<Scalar>, SynthesisError>
where
    CS: ConstraintSystem<Scalar>,
    Scalar: PrimeField,
{
    let res = AllocatedNum::alloc(cs.namespace(|| "res"), || {
        let mut tmp = a.get_value().ok_or(SynthesisError::AssignmentMissing)?;
        tmp.sub_assign(other.get_value().ok_or(SynthesisError::AssignmentMissing)?);

        Ok(tmp)
    })?;

    // Constrain: (a - b) * 1 = a - b
    cs.enforce(
        || "subtraction constraint",
        |lc| lc + a.get_variable() - other.get_variable(),
        |lc| lc + CS::one(),
        |lc| lc + res.get_variable(),
    );

    Ok(res)
}

/// Returns (-self)
pub fn neg<CS, Scalar>(
    mut cs: CS,
    a: &AllocatedNum<Scalar>,
) -> Result<AllocatedNum<Scalar>, SynthesisError>
where
    CS: ConstraintSystem<Scalar>,
    Scalar: PrimeField,
{
    let res = AllocatedNum::alloc(cs.namespace(|| "neg num"), || {
        let tmp = a
            .get_value()
            .ok_or(SynthesisError::AssignmentMissing)?
            .neg();

        Ok(tmp)
    })?;

    // Constrain: (self + var) = 0
    cs.enforce(
        || "negation constraint",
        |lc| lc,
        |lc| lc,
        |lc| lc + a.get_variable() + res.get_variable(),
    );

    Ok(res)
}

/// Returns the bit `self == 0`
pub fn is_zero<CS, Scalar>(mut cs: CS, a: &AllocatedNum<Scalar>) -> Result<Boolean, SynthesisError>
where
    CS: ConstraintSystem<Scalar>,
    Scalar: PrimeField,
{
    let out = AllocatedBit::alloc(&mut cs.namespace(|| "out bit"), {
        let input_value = a.get_value().ok_or(SynthesisError::AssignmentMissing)?;
        Some(input_value == Scalar::ZERO)
    })?;
    let multiplier = AllocatedNum::alloc(&mut cs.namespace(|| "zero or inverse"), || {
        let tmp = a.get_value().ok_or(SynthesisError::AssignmentMissing)?;

        if tmp.is_zero().into() {
            Ok(Scalar::ZERO)
        } else {
            Ok(tmp.invert().unwrap())
        }
    })?;

    cs.enforce(
        || "multiplier * input === 1 - out",
        |lc| lc + multiplier.get_variable(),
        |lc| lc + a.get_variable(),
        |lc| lc + CS::one() - out.get_variable(),
    );

    cs.enforce(
        || "out * input === 0",
        |lc| lc + out.get_variable(),
        |lc| lc + a.get_variable(),
        |lc| lc,
    );
    Ok(Boolean::from(out))
}

/// Takes two allocated numbers (self, other) and returns
/// the bit `self==other`
pub fn is_equal<CS, Scalar>(
    mut cs: CS,
    a: &AllocatedNum<Scalar>,
    other: &AllocatedNum<Scalar>,
) -> Result<Boolean, SynthesisError>
where
    CS: ConstraintSystem<Scalar>,
    Scalar: PrimeField,
{
    let diff = sub(&mut cs.namespace(|| "self-other"), a, other)?;
    is_zero(cs, &diff)
}

/// Takes two allocated numbers (a, b) and returns
/// a if condition is false, and b otherwise
pub fn conditionally_select<CS, Scalar>(
    mut cs: CS,
    a: &AllocatedNum<Scalar>,
    b: &AllocatedNum<Scalar>,
    condition: &Boolean,
) -> Result<AllocatedNum<Scalar>, SynthesisError>
where
    CS: ConstraintSystem<Scalar>,
    Scalar: PrimeField,
{
    let c = AllocatedNum::alloc(&mut cs.namespace(|| "alloc output"), || {
        if condition
            .get_value()
            .ok_or(SynthesisError::AssignmentMissing)?
        {
            Ok(b.get_value().ok_or(SynthesisError::AssignmentMissing)?)
        } else {
            Ok(a.get_value().ok_or(SynthesisError::AssignmentMissing)?)
        }
    })?;
    cs.enforce(
        || "condition * (a - b) === a - c",
        |_| condition.lc(CS::one(), Scalar::ONE),
        |lc| lc + a.get_variable() - b.get_variable(),
        |lc| lc + a.get_variable() - c.get_variable(),
    );

    Ok(c)
}

#[cfg(test)]
mod test {
    use super::*;
    use bellpepper_core::test_cs::TestConstraintSystem;
    use ff::Field;
    // use halo2curves::secp256k1::Fp;
    use nova::provider::Secp256k1Engine;
    use nova::traits::Engine;
    use rand::Rng;
    use rand_core::SeedableRng;
    use rand_xorshift::XorShiftRng;
    use std::ops::SubAssign;

    type Fp = <Secp256k1Engine as Engine>::Base;

    #[test]
    fn test_into_bits() {
        let mut rng = XorShiftRng::from_seed([
            0x59, 0x62, 0xbe, 0x3d, 0x76, 0x3d, 0x31, 0x8d, 0x17, 0xdb, 0x37, 0x32, 0x54, 0x06,
            0xbc, 0xe5,
        ]);

        for _ in 0..200 {
            let r = Fp::random(&mut rng);
            let mut cs = TestConstraintSystem::<Fp>::new();

            let n = AllocatedNum::alloc(&mut cs, || Ok(r)).unwrap();

            let bits = num_to_bits_le(&mut cs, n, Fp::NUM_BITS as usize).unwrap();

            assert!(cs.is_satisfied());

            for (i, b) in r.to_le_bits().iter().enumerate() {
                match bits.get(i) {
                    Some(Boolean::Is(a)) => assert_eq!(b, a.get_value().unwrap()),
                    Some(_) => unreachable!(),
                    None => assert!(!b),
                };
            }

            cs.set("num", Fp::random(&mut rng));
            assert!(!cs.is_satisfied());
            cs.set("num", r);
            assert!(cs.is_satisfied());
            assert_eq!(cs.num_constraints(), 257);

            for i in 0..Fp::NUM_BITS {
                let name = format!("bit {}/boolean", i);
                let cur = cs.get(&name);
                let mut tmp = Fp::ONE;
                tmp.sub_assign(&cur);
                cs.set(&name, tmp);
                assert!(!cs.is_satisfied());
                cs.set(&name, cur);
                assert!(cs.is_satisfied());
            }
        }

        for _ in 0..200 {
            let r = Fp::from_u128(rng.gen());
            let mut cs = TestConstraintSystem::<Fp>::new();

            let n = AllocatedNum::alloc(&mut cs, || Ok(r)).unwrap();

            let bits = num_to_bits_le(&mut cs, n, 128 as usize).unwrap();

            assert!(cs.is_satisfied());

            for (i, b) in r.to_le_bits().iter().enumerate() {
                match bits.get(i) {
                    Some(Boolean::Is(a)) => assert_eq!(b, a.get_value().unwrap()),
                    Some(_) => unreachable!(),
                    None => assert!(!b),
                };
            }

            cs.set("num", Fp::random(&mut rng));
            assert!(!cs.is_satisfied());
            cs.set("num", r);
            assert!(cs.is_satisfied());
            assert_eq!(cs.num_constraints(), 129);

            for i in 0..128 {
                let name = format!("bit {}/boolean", i);
                let cur = cs.get(&name);
                let mut tmp = Fp::ONE;
                tmp.sub_assign(&cur);
                cs.set(&name, tmp);
                assert!(!cs.is_satisfied());
                cs.set(&name, cur);
                assert!(cs.is_satisfied());
            }
        }
    }

    #[test]
    fn test_is_less() {
        let mut rng = rand::thread_rng();

        for _ in 0..100 {
            let in1 = Fp::from_u128(rng.gen());
            let in2 = Fp::from_u128(rng.gen());

            let mut cs = TestConstraintSystem::<Fp>::new();

            let in1_int = U256::from_le_bytes(in1.to_repr());
            let in2_int = U256::from_le_bytes(in2.to_repr());

            let in1_var: AllocatedNum<Fp> =
                AllocatedNum::alloc(cs.namespace(|| "in1"), || Ok(in1)).unwrap();
            let in2_var: AllocatedNum<Fp> =
                AllocatedNum::alloc(cs.namespace(|| "in2"), || Ok(in2)).unwrap();
            let op = is_less(&mut cs, in1_var, in2_var, 128)
                .unwrap()
                .get_value()
                .unwrap();

            assert_eq!(in1_int < in2_int, op);
            assert!(cs.is_satisfied());
            assert_eq!(cs.num_constraints(), 131);
        }
    }

    #[test]
    fn test_is_greater() {
        let mut rng = rand::thread_rng();

        for _ in 0..100 {
            let in1 = Fp::from_u128(rng.gen());
            let in2 = Fp::from_u128(rng.gen());

            let mut cs = TestConstraintSystem::<Fp>::new();

            let in1_int = U256::from_le_bytes(in1.to_repr());
            let in2_int = U256::from_le_bytes(in2.to_repr());

            let in1_var: AllocatedNum<Fp> =
                AllocatedNum::alloc(cs.namespace(|| "in1"), || Ok(in1)).unwrap();
            let in2_var: AllocatedNum<Fp> =
                AllocatedNum::alloc(cs.namespace(|| "in2"), || Ok(in2)).unwrap();
            let op = is_greater(&mut cs, in1_var, in2_var, 128)
                .unwrap()
                .get_value()
                .unwrap();

            assert_eq!(in1_int > in2_int, op);
            assert!(cs.is_satisfied());
            assert_eq!(cs.num_constraints(), 131);
        }
    }

    #[test]
    fn test_is_greater_eq() {
        let mut rng = rand::thread_rng();

        for _ in 0..100 {
            let in1 = Fp::from_u128(rng.gen());
            let in2 = Fp::from_u128(rng.gen());

            let mut cs = TestConstraintSystem::<Fp>::new();

            let in1_int = U256::from_le_bytes(in1.to_repr());
            let in2_int = U256::from_le_bytes(in2.to_repr());

            let in1_var: AllocatedNum<Fp> =
                AllocatedNum::alloc(cs.namespace(|| "in1"), || Ok(in1)).unwrap();
            let in2_var: AllocatedNum<Fp> =
                AllocatedNum::alloc(cs.namespace(|| "in2"), || Ok(in2)).unwrap();
            let op = is_greater_eq(&mut cs, in1_var, in2_var, 128)
                .unwrap()
                .get_value()
                .unwrap();

            assert_eq!(in1_int > in2_int, op);
            assert!(cs.is_satisfied());
            assert_eq!(cs.num_constraints(), 132);
        }

        for _ in 0..100 {
            let in1 = Fp::from_u128(rng.gen());

            let mut cs = TestConstraintSystem::<Fp>::new();

            let in1_var: AllocatedNum<Fp> =
                AllocatedNum::alloc(cs.namespace(|| "in1"), || Ok(in1)).unwrap();

            let op = is_greater_eq(&mut cs, in1_var.clone(), in1_var, 128)
                .unwrap()
                .get_value()
                .unwrap();

            assert_eq!(true, op);
            assert!(cs.is_satisfied());
            assert_eq!(cs.num_constraints(), 132);
        }
    }
}
