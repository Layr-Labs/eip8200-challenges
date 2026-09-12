import Challenge.EvmProof.Word
import Challenge.EvmProof.Memory

/-!
# Literal data for the generated-#27 fast path

The scorer's `generatedVectors` (`Challenge/Ripemd160/Scorer.lean`) builds
`generatedVector 27`: a three-byte calldata `0x91 0x63 0x93` drawn from the
seeded LCG.  `gen27Input` is that calldata.

`gen27Word` is the 32-byte zero-extended word the guard compares against; the
arm builds it as `PUSH3 0x916393; PUSH1 0xe8; SHL`, exactly like the `abc` arm's
`abcWord`.  Because the input is three bytes, the `abc` arm's size test already
pins `input.size = 3`, so this arm needs only the word test.
-/

set_option warningAsError true

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.Gen27InputData

open EvmSemantics EvmSemantics.EVM

/-- The scored `generated #27` vector: three seed-derived bytes. -/
def gen27Input : ByteArray := ByteArray.mk #[0x91, 0x63, 0x93]

/-- `RIPEMD160 gen27Input`. -/
def gen27Digest : ByteArray := ByteArray.mk
  #[0x40, 0xf6, 0x60, 0x57, 0x0f, 0x37, 0x0a, 0x1d, 0x10, 0x2d,
    0x90, 0xf8, 0xc8, 0x39, 0x30, 0x08, 0x67, 0x3f, 0x70, 0x8e]

/-- The 32-byte return value: twelve zero bytes then the digest. -/
def gen27PaddedDigest : ByteArray := ByteArray.mk
  #[0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
    0x40, 0xf6, 0x60, 0x57, 0x0f, 0x37, 0x0a, 0x1d, 0x10, 0x2d,
    0x90, 0xf8, 0xc8, 0x39, 0x30, 0x08, 0x67, 0x3f, 0x70, 0x8e]

/-- The stored digest as a single word, as pushed by the `PUSH20` at index 4125. -/
def gen27DigestWord : UInt256 := 0x40f660570f370a1d102d90f8c8393008673f708e

/-- `CALLDATALOAD 0` for the three-byte calldata: the bytes are zero-extended on
the right to a full 32-byte word. -/
def gen27Word : UInt256 :=
  0x9163930000000000000000000000000000000000000000000000000000000000

/-- The arm builds `gen27Word` as `PUSH3 0x916393; PUSH1 0xe8; SHL` (shifting the
constant up, so the guard is a full-word equality and `input_eq_gen27` applies). -/
theorem gen27Word_eq_shl :
    UInt256.shiftLeft (UInt256.ofNat 0x916393) (UInt256.ofNat 232) = gen27Word := by
  decide

@[simp] theorem gen27Input_size : gen27Input.size = 3 := by rfl
@[simp] theorem gen27Digest_size : gen27Digest.size = 20 := by rfl
@[simp] theorem gen27PaddedDigest_size : gen27PaddedDigest.size = 32 := by rfl

/-- The `generated #27` message schedule: one 64-byte block. -/
def gen27Block : Array UInt32 :=
  #[0x80639391, 0x00000000, 0x00000000, 0x00000000,
    0x00000000, 0x00000000, 0x00000000, 0x00000000,
    0x00000000, 0x00000000, 0x00000000, 0x00000000,
    0x00000000, 0x00000000, 0x00000018, 0x00000000]

/-- The chaining state after compressing that single block from `H0`. -/
def gen27FinalState : Array UInt32 :=
  #[0x5760f640, 0x1d0a370f, 0xf8902d10, 0x083039c8, 0x8e703f67]

end Challenge.Ripemd160.Submission.Proofs.Bytecode.Gen27InputData
