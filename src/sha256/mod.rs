//! Gadget and chips for the [SHA-256] hash function.
//!
//! [SHA-256]: https://tools.ietf.org/html/rfc6234
//! 
#![allow(dead_code)]
#![allow(unused_variables)]
use std::cmp::min;
use std::convert::TryInto;
use std::fmt;
use halo2::{
    arithmetic::FieldExt,
    circuit::{Chip, Layouter},
    plonk::Error,
};

mod table16;

pub use table16::{BlockWord, Table16Chip, Table16Config};

/// The size of a SHA-256 block, in 32-bit words.
pub const BLOCK_SIZE: usize = 16;
/// The size of a SHA-256 digest, in 32-bit words.
pub const DIGEST_SIZE: usize = 8;

/// The set of circuit instructions required to use the [`Sha256`] gadget.
pub trait Sha256Instructions<F: FieldExt>: Chip<F> {
    /// Variable representing the SHA-256 internal state.
    type State: Clone + fmt::Debug;
    /// Variable representing a 32-bit word of the input block to the SHA-256 compression
    /// function.
    type BlockWord: Copy + fmt::Debug + Default;

    /// Places the SHA-256 IV in the circuit, returning the initial state variable.
    fn initialization_vector(&self, layouter: &mut impl Layouter<F>) -> Result<Self::State, Error>;

    /// Creates an initial state from the output state of a previous block
    fn initialization(
        &self,
        layouter: &mut impl Layouter<F>,
        init_state: &Self::State,
    ) -> Result<Self::State, Error>;

    /// Starting from the given initialized state, processes a block of input and returns the
    /// final state.
    fn compress(
        &self,
        layouter: &mut impl Layouter<F>,
        initialized_state: &Self::State,
        input: [Self::BlockWord; BLOCK_SIZE],
    ) -> Result<Self::State, Error>;

    /// Converts the given state into a message digest.
    fn digest(
        &self,
        layouter: &mut impl Layouter<F>,
        state: &Self::State,
    ) -> Result<[Self::BlockWord; DIGEST_SIZE], Error>;
}

/// The output of a SHA-256 circuit invocation.
#[derive(Debug)]
pub struct Sha256Digest<BlockWord>([BlockWord; DIGEST_SIZE]);

impl Sha256Digest<BlockWord> {
    pub fn to_repr(&self) -> [BlockWord; DIGEST_SIZE] {
        self.0
    }
}

/// A gadget that constrains a SHA-256 invocation. It supports input at a granularity of
/// 32 bits.
#[derive(Debug)]
pub struct Sha256<F: FieldExt, CS: Sha256Instructions<F>> {
    chip: CS,
    state: CS::State,
    cur_block: Vec<CS::BlockWord>,
    length: usize,
}

impl<F: FieldExt, Sha256Chip: Sha256Instructions<F>> Sha256<F, Sha256Chip> {
    /// Create a new hasher instance.
    pub fn new(chip: Sha256Chip, mut layouter: impl Layouter<F>) -> Result<Self, Error> {
        let state = chip.initialization_vector(&mut layouter)?;
        Ok(Sha256 {
            chip,
            state,
            cur_block: Vec::with_capacity(BLOCK_SIZE),
            length: 0,
        })
    }

    /// Digest data, updating the internal state.
    pub fn update(
        &mut self,
        mut layouter: impl Layouter<F>,
        mut data: &[Sha256Chip::BlockWord],
    ) -> Result<(), Error> {
        self.length += data.len() * 32;

        // Fill the current block, if possible.
        let remaining = BLOCK_SIZE - self.cur_block.len();
        let (l, r) = data.split_at(min(remaining, data.len()));
        self.cur_block.extend_from_slice(l);
        data = r;

        // If we still don't have a full block, we are done.
        if self.cur_block.len() < BLOCK_SIZE {
            return Ok(());
        }

        // Process the now-full current block.
        self.state = self.chip.compress(
            &mut layouter,
            &self.state,
            self.cur_block[..]
                .try_into()
                .expect("cur_block.len() == BLOCK_SIZE"),
        )?;
        self.cur_block.clear();

        // Process any additional full blocks.
        let mut chunks_iter = data.chunks_exact(BLOCK_SIZE);
        for chunk in &mut chunks_iter {
            self.state = self.chip.initialization(&mut layouter, &self.state)?;
            self.state = self.chip.compress(
                &mut layouter,
                &self.state,
                chunk.try_into().expect("chunk.len() == BLOCK_SIZE"),
            )?;
        }

        // Cache the remaining partial block, if any.
        let rem = chunks_iter.remainder();
        self.cur_block.extend_from_slice(rem);

        Ok(())
    }

    /// Retrieve result and consume hasher instance.
    pub fn finalize(
        mut self,
        mut layouter: impl Layouter<F>,
    ) -> Result<Sha256Digest<Sha256Chip::BlockWord>, Error> {
        // Pad the remaining block
        if !self.cur_block.is_empty() {
            let padding = vec![Sha256Chip::BlockWord::default(); BLOCK_SIZE - self.cur_block.len()];
            self.cur_block.extend_from_slice(&padding);
            self.state = self.chip.initialization(&mut layouter, &self.state)?;
            self.state = self.chip.compress(
                &mut layouter,
                &self.state,
                self.cur_block[..]
                    .try_into()
                    .expect("cur_block.len() == BLOCK_SIZE"),
            )?;
        }
        self.chip
            .digest(&mut layouter, &self.state)
            .map(Sha256Digest)
    }

    /// Convenience function to compute hash of the data. It will handle hasher creation,
    /// data feeding and finalization.
    pub fn digest(
        chip: Sha256Chip,
        mut layouter: impl Layouter<F>,
        data: &[Sha256Chip::BlockWord],
    ) -> Result<Sha256Digest<Sha256Chip::BlockWord>, Error> {
        let mut hasher = Self::new(chip, layouter.namespace(|| "init"))?;
        hasher.update(layouter.namespace(|| "update"), data)?;
        hasher.finalize(layouter.namespace(|| "finalize"))
    }
}

fn main() {
    use halo2::{
        circuit::{Layouter, SimpleFloorPlanner},
        pasta::pallas::Base as Fp,
        plonk::{Circuit, ConstraintSystem, Error},
        dev::MockProver,
    };

    use crate::sha256::table16::{Bits};

    fn lebs2ip<const K: usize>(bits: &[bool; K]) -> u64 {
        assert!(K <= 64);
        bits.iter()
            .enumerate()
            .fold(0u64, |acc, (i, b)| acc + if *b { 1 << i } else { 0 })
    }

    // since we alyaws work wiht constant input lenghts it will always be:
    // 256(field size element in bits) + 1(1) + 511(0)  + 256(bigendian of input size)
    fn append_for_sha(x: Fp) {
        // println!("{:?}");
    }


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

            // Test vector: "abc"
            let test_input = [
                BlockWord(Some(0b01100111011000100110001110000000)),
                // BlockWord(Some(0b00000000000000000000000000000000)),
                // BlockWord(Some(0b00000000000000000000000000000000)),
                // BlockWord(Some(0b00000000000000000000000000000000)),
                // BlockWord(Some(0b00000000000000000000000000000000)),
                // BlockWord(Some(0b00000000000000000000000000000000)),
                // BlockWord(Some(0b00000000000000000000000000000000)),
                // BlockWord(Some(0b00000000000000000000000000000000)),
                // BlockWord(Some(0b01100111011000100110001110000000)),
                // BlockWord(Some(0b00000000000000000000000000000000)),
                // BlockWord(Some(0b00000000000000000000000000000000)),
                // BlockWord(Some(0b00000000000000000000000000000000)),
                // BlockWord(Some(0b00000000000000000000000000000000)),
                // BlockWord(Some(0b00000000000000000000000000000000)),
                // BlockWord(Some(0b00000000000000000000000000000000)),
                // BlockWord(Some(0b00000000000000000000000000000000)),
            ];

            // Create a message of length 31 blocks
            // let mut input = Vec::with_capacity(BLOCK_SIZE);
            // for _ in 0..2 {
            //     input.extend_from_slice(&test_input);
            // }

            let digest = Sha256::digest(table16_chip, layouter.namespace(|| "'abc'"), &test_input);

            if digest.is_err() {
                println!("{:?}", digest);
                // panic!("Hash is worng"):
            } else {

            }
            // let digest = digest.0.to_vec();

            // let bitified = digest.iter().map(|block_word| Bits::from(block_word.0.unwrap())).collect::<Vec<Bits<32>>>();
            // println!("{:?}", bitified);

            // let flattened = bitified.into_iter()
            //                         .flat_map(|bit_word| bit_word.0.to_vec())
            //                         .collect::<Vec<bool>>();

            // println!("{:?}", flattened);
            // assert_eq!(256, flattened.len());

            // let raw: [u64; 4] = [
            //     lebs2ip::<64>(&flattened[192..256].try_into().unwrap()),
            //     lebs2ip::<64>(&flattened[128..192].try_into().unwrap()),
            //     lebs2ip::<64>(&flattened[64..128].try_into().unwrap()),
            //     lebs2ip::<64>(&flattened[0..64].try_into().unwrap()),
            // ];

            // println!("{:?}", raw);

            // let element = Fp::from_raw(raw);
            // println!("{:?}", element);

            // 28948022309329048855892746252171976963363056481941560715954676764349967630337
            // 11722212130318025828472231660672967367233855363386404338905765869709624705793
            // let bits = Bits::from([true; 32]);
            // for block_word in &digest {
            //     let to_uint = block_word.0.unwrap();
            //     let bits = Bits::from(to_uint);
            //     println!("{:?}", bits);

            // }

            // let a = [1, 2, 3];

// the sum of all of the elements of the array
            // let sum = a.iter().fold(&[], |acc, x| [acc, [x]].concat());

            // let flattened = digest.iter().fold(&[] | accumulator, block_word | 
            //     // let to_uint = block_word.0.unwrap();
            //     // let bits = Bits::from(to_uint);
            //     // [accumulator, second].concat()
            //     [accumulator, &[0, 1, 2]].concat()
            // )

            // let merged = digest.iter().
            //                     flat_map(| block_word | 
            //                         let to_uint = block_word.0.unwrap();
            //                         Bits::from(to_uint)
            //                     )

            // println!("{:?}", digest.len());
            // println!("{:?}", digest.len());
            // println!("finsihed");

            Ok(())
        }
    }

    let circuit: MyCircuit = MyCircuit {};

    let k = 17;

    let prover = MockProver::<Fp>::run(k, &circuit, vec![]).unwrap();
    // assert_eq!(prover.verify(), Ok(()));
    // println!("finsihed");
}
