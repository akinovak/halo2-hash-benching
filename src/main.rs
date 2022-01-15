#![allow(dead_code)]
pub mod sha256;

use halo2::{
    circuit::{Layouter, SimpleFloorPlanner},
    pasta::pallas::Base as Fp,
    plonk::{Circuit, ConstraintSystem, Error},
    dev::MockProver,
};
use ff::{PrimeField};
use bitvec::prelude::*;
use crate::sha256::{BlockWord, Table16Chip, Table16Config, Sha256, DIGEST_SIZE};



// since we alyaws work wiht constant input lenghts it will always be:
// 256(field size element in bits) + 1(1) + 191(0)  + 64(bigendian of input size)
fn fp_to_sha256_input(x: Fp) -> Vec<BlockWord> {
    let repr = x.to_repr();
    let mut one = bitvec![1; 1];
    let mut zeros = bitvec![0; 191];
    let be: u64 = 64;

    let bitified: Vec<_> = repr.iter().
                        map(|x| x.view_bits::<Msb0>()).collect();

    let mut bitified: BitVec = bitified.into_iter().flat_map(|x| x.to_bitvec()).collect();
    bitified.append(&mut one);
    bitified.append(&mut zeros);
    bitified.extend_from_bitslice(be.view_bits::<Msb0>());

    let iter = bitified.chunks(32);
    let input: Vec<BlockWord> = iter.map(|chunk| BlockWord(Some(chunk.load::<u32>())))
                    .collect();

    input
}

fn digest_to_fp(digest: [BlockWord; DIGEST_SIZE]) -> Fp {
    let iter = digest.chunks(2);

    let raw_repr = iter.map(|chunk| ((chunk[0].to_repr() as u64) << 32) | (chunk[1].to_repr() as u64))
                                    .collect::<Vec<u64>>();

    let raw_repr: [u64; 4] = raw_repr.as_slice().try_into().unwrap();
    Fp::from_raw(raw_repr)
}  

fn lebs2ip<const K: usize>(bits: &[bool; K]) -> u64 {
    assert!(K <= 64);
    bits.iter()
        .enumerate()
        .fold(0u64, |acc, (i, b)| acc + if *b { 1 << i } else { 0 })
}

fn main() {
    struct MyCircuit {}

    impl Circuit<Fp> for MyCircuit {
        type Config = Table16Config;
        type FloorPlanner = SimpleFloorPlanner;

        fn without_witnesses(&self) -> Self {
            MyCircuit {}
        }

        fn configure(meta: &mut ConstraintSystem<Fp>) -> Self::Config {
            Table16Chip::configure(meta)
        }

        fn synthesize(
            &self,
            config: Self::Config,
            mut layouter: impl Layouter<Fp>,
        ) -> Result<(), Error> {
            let table16_chip = Table16Chip::construct(config.clone());
            Table16Chip::load(config, &mut layouter)?;

            let x = Fp::one();
            let input = fp_to_sha256_input(x);

            let digest = Sha256::digest(table16_chip, layouter.namespace(|| "'abc'"), &input)?;
            let hashed = digest_to_fp(digest.to_repr());
            println!("{:?}", hashed);

            Ok(())
        }
    }

    let circuit: MyCircuit = MyCircuit {};

    let k = 17;

    let prover = MockProver::<Fp>::run(k, &circuit, vec![]).unwrap();
    // assert_eq!(prover.verify(), Ok(()));
}
