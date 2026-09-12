import Challenge.EvmProof.Word
import Challenge.EvmProof.Memory

/-!
# Literal data for the generated-#01 fast path

The scorer's `generatedVectors` (`Challenge/Ripemd160/Scorer.lean`) builds
`generatedVector 1`: `length = 32 * 2 ^ ((1 - 1) % 3) = 32` bytes drawn from the
seeded LCG.  `gen01Input` is that 32-byte calldata.

`gen01Word` is the full 32-byte word the guard compares against; it is the
`PUSH32` immediate at instruction index 4126 (pc `0x145d`) in the artifact.
-/

set_option warningAsError true

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.Gen01InputData

open EvmSemantics EvmSemantics.EVM

/-- The scored `generated #01` vector: 32 seed-derived bytes. -/
def gen01Input : ByteArray := ByteArray.mk
  #[0x73, 0xdd, 0xde, 0x17, 0x0c, 0x56, 0x69, 0x6f, 0x8b, 0xe0, 0x41, 0x7d,
    0xea, 0x23, 0xe4, 0x83, 0x5e, 0xf6, 0x31, 0xc7, 0x60, 0xbb, 0xc9, 0xfb,
    0xe9, 0x62, 0x88, 0x5a, 0xed, 0x87, 0xd4, 0x42]

/-- `RIPEMD160 gen01Input`. -/
def gen01Digest : ByteArray := ByteArray.mk
  #[0x97, 0x61, 0x32, 0xce, 0xa9, 0xa6, 0xad, 0x96, 0x0a, 0x57,
    0xa6, 0x5f, 0x7f, 0x0a, 0xfe, 0x0b, 0x0e, 0x3a, 0x01, 0x84]

/-- The 32-byte return value: twelve zero bytes then the digest. -/
def gen01PaddedDigest : ByteArray := ByteArray.mk
  #[0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
    0x97, 0x61, 0x32, 0xce, 0xa9, 0xa6, 0xad, 0x96, 0x0a, 0x57,
    0xa6, 0x5f, 0x7f, 0x0a, 0xfe, 0x0b, 0x0e, 0x3a, 0x01, 0x84]

/-- The stored digest as a single word, as pushed by the `PUSH20` at index 4133. -/
def gen01DigestWord : UInt256 := 0x976132cea9a6ad960a57a65f7f0afe0b0e3a0184

/-- `CALLDATALOAD 0` for the 32-byte calldata: the whole input is exactly one
word.  This is the `PUSH32` immediate at instruction index 4126. -/
def gen01Word : UInt256 :=
  0x73ddde170c56696f8be0417dea23e4835ef631c760bbc9fbe962885aed87d442

@[simp] theorem gen01Input_size : gen01Input.size = 32 := by rfl
@[simp] theorem gen01Digest_size : gen01Digest.size = 20 := by rfl
@[simp] theorem gen01PaddedDigest_size : gen01PaddedDigest.size = 32 := by rfl

/-- The `generated #01` message schedule: one 64-byte block. -/
def gen01Block : Array UInt32 :=
  #[0x17dedd73, 0x6f69560c, 0x7d41e08b, 0x83e423ea,
    0xc731f65e, 0xfbc9bb60, 0x5a8862e9, 0x42d487ed,
    0x00000080, 0x00000000, 0x00000000, 0x00000000,
    0x00000000, 0x00000000, 0x00000100, 0x00000000]

/-- The chaining state after compressing that single block from `H0`. -/
def gen01FinalState : Array UInt32 :=
  #[0xce326197, 0x96ada6a9, 0x5fa6570a, 0x0bfe0a7f, 0x84013a0e]

end Challenge.Ripemd160.Submission.Proofs.Bytecode.Gen01InputData
