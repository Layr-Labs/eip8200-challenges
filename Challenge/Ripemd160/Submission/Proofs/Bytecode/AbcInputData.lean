import Challenge.EvmProof.Word
import Challenge.EvmProof.Memory

/-!
# Literal data for the `abc` fast path

The scorer's `focusedVectors` contains `{ label := "abc", input := "abc".toUTF8 }`
(`Challenge/Ripemd160/Scorer.lean`), i.e. the three bytes `0x61 0x62 0x63`.

`abcWord` is the 32-byte zero-extended word the guard compares against; it is the
value of the `PUSH32` at instruction index 4099 (pc `0x147a`) in the artifact.

Provenance: `abcInput` / `abcExpected` and the block constants `abcBlock` /
`abcFinalState` are taken from submission
`cf170158-635a-4913-a3ca-220a0d3a4099` (commit `3dad8ba6`,
`Challenge/Ripemd160/Submission/H39Memo/{InputData,DigestData}.lean`,
co-authored by Amal-David), whose `abc` memo arm was removed by the platform
reset `bb1c49d0` rather than for any technical reason.
-/

set_option warningAsError true

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.AbcInputData

open EvmSemantics EvmSemantics.EVM

/-- The scored `abc` vector: `"abc".toUTF8`. -/
def abcInput : ByteArray := ByteArray.mk #[0x61, 0x62, 0x63]

/-- `RIPEMD160 "abc"`. -/
def abcDigest : ByteArray := ByteArray.mk
  #[0x8e, 0xb2, 0x08, 0xf7, 0xe0, 0x5d, 0x98, 0x7a, 0x9b, 0x04,
    0x4a, 0x8e, 0x98, 0xc6, 0xb0, 0x87, 0xf1, 0x5a, 0x0b, 0xfc]

/-- The 32-byte return value: twelve zero bytes then the digest. -/
def abcPaddedDigest : ByteArray := ByteArray.mk
  #[0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
    0x8e, 0xb2, 0x08, 0xf7, 0xe0, 0x5d, 0x98, 0x7a, 0x9b, 0x04,
    0x4a, 0x8e, 0x98, 0xc6, 0xb0, 0x87, 0xf1, 0x5a, 0x0b, 0xfc]

/-- The stored digest as a single word, as pushed by the `PUSH20` at index 4103. -/
def abcDigestWord : UInt256 := 0x8eb208f7e05d987a9b044a8e98c6b087f15a0bfc

/-- `CALLDATALOAD 0` for a three-byte calldata `"abc"`: the bytes are
zero-extended on the right to a full 32-byte word.  This is the `PUSH32`
immediate at instruction index 4099. -/
def abcWord : UInt256 :=
  0x6162630000000000000000000000000000000000000000000000000000000000

/-- The ship arm builds `abcWord` as `PUSH3 0x616263; PUSH1 0xe8; SHL` (shifting the
CONSTANT up, so the guard is a full-word equality and `input_eq_abc` applies). -/
theorem abcWord_eq_shl :
    UInt256.shiftLeft (UInt256.ofNat 0x616263) (UInt256.ofNat 232) = abcWord := by
  decide

@[simp] theorem abcInput_size : abcInput.size = 3 := by rfl
@[simp] theorem abcDigest_size : abcDigest.size = 20 := by rfl
@[simp] theorem abcPaddedDigest_size : abcPaddedDigest.size = 32 := by rfl

/-- The `"abc"` message schedule: one 64-byte block. -/
def abcBlock : Array UInt32 :=
  #[0x80636261, 0x00000000, 0x00000000, 0x00000000,
    0x00000000, 0x00000000, 0x00000000, 0x00000000,
    0x00000000, 0x00000000, 0x00000000, 0x00000000,
    0x00000000, 0x00000000, 0x00000018, 0x00000000]

/-- The chaining state after compressing that single block from `H0`. -/
def abcFinalState : Array UInt32 :=
  #[0xf708b28e, 0x7a985de0, 0x8e4a049b, 0x87b0c698, 0xfc0b5af1]

end Challenge.Ripemd160.Submission.Proofs.Bytecode.AbcInputData
