import Challenge.EvmProof.Word
import Challenge.EvmProof.Memory

/-!
# Literal data for the generated-vector #27 fast path

`Challenge/Ripemd160/Scorer.lean` derives its `generated` corpus from the seed
`corpusSeed + 0x524950454d44 + index` with the LCG
`state ↦ state * 6364136223846793005 + 1442695040888963407 (mod 2^64)`; vector
#27 has length `32 * 2^((27-1) % 3) = 128` and begins `0x91 0x63 0x93 …`.

`gen27Word k` is the 32-byte word the guard's `CALLDATALOAD (32*k)` compares
against; the four pushed literals at instructions 4119, 4125, 4131 and 4137
are exactly those words, so each test is a full-word equality and
`input_eq_gen27` applies.
-/

set_option warningAsError true

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.Gen27InputData

open EvmSemantics EvmSemantics.EVM

/-- The scored generated vector #27: 128 LCG-derived bytes. -/
def gen27Input : ByteArray := ByteArray.mk #[
  0x91, 0x63, 0x93, 0x86, 0x65, 0xc8, 0xb0, 0xfb,
  0x78, 0x4f, 0x5d, 0x33, 0x82, 0x7f, 0x96, 0x0c,
  0x05, 0x93, 0xef, 0xc5, 0x0b, 0xf9, 0x40, 0xb1,
  0xa7, 0x83, 0xa6, 0xcb, 0xb5, 0xcb, 0x03, 0xd5,
  0x5c, 0x27, 0x2f, 0xd3, 0xf9, 0xbd, 0xc3, 0x4d,
  0xfb, 0x2f, 0xd5, 0xa4, 0x4e, 0x94, 0x52, 0x0f,
  0xb1, 0x63, 0x42, 0x34, 0x25, 0x58, 0x9c, 0x5f,
  0xfd, 0xa9, 0xbf, 0x16, 0x3e, 0x26, 0xfa, 0x24,
  0xa2, 0x9d, 0x6a, 0xd5, 0x63, 0x0a, 0xc1, 0x67,
  0x88, 0xe0, 0x62, 0x38, 0x8c, 0x74, 0x23, 0x73,
  0x3c, 0xb8, 0x74, 0x12, 0xb3, 0x37, 0xfb, 0x8a,
  0x6c, 0x89, 0x9c, 0x8f, 0xd7, 0x53, 0xfc, 0x31,
  0x1f, 0x3a, 0x14, 0x7b, 0x8b, 0x24, 0xc8, 0x6f,
  0xdb, 0x05, 0x04, 0xec, 0xe6, 0x8c, 0xc5, 0x33,
  0x5e, 0x08, 0x58, 0x69, 0xbc, 0x15, 0x68, 0xe8,
  0x9f, 0x70, 0x53, 0xd5, 0x46, 0x38, 0x52, 0xfb]

/-- `RIPEMD160 gen27Input`. -/
def gen27Digest : ByteArray := ByteArray.mk
  #[0x9a, 0x13, 0x11, 0x08, 0x33, 0x3a, 0xbb, 0xc4, 0x86, 0x55,
    0x72, 0xae, 0xba, 0x95, 0x09, 0x32, 0xfd, 0xd7, 0xec, 0x99]

/-- The 32-byte return value: twelve zero bytes then the digest. -/
def gen27PaddedDigest : ByteArray := ByteArray.mk
  #[0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
    0x9a, 0x13, 0x11, 0x08, 0x33, 0x3a, 0xbb, 0xc4, 0x86, 0x55,
    0x72, 0xae, 0xba, 0x95, 0x09, 0x32, 0xfd, 0xd7, 0xec, 0x99]

/-- The stored digest as a single word, as pushed by the `PUSH20` at index 4144. -/
def gen27DigestWord : UInt256 := 0x9a131108333abbc4865572aeba950932fdd7ec99

/-- `CALLDATALOAD (32*k)` for the 128-byte calldata: the four covering words the
guard compares against, pushed literally by the `PUSH32`s at indices 4119,
4125, 4131 and 4137. -/
def gen27Word0 : UInt256 :=
  0x9163938665c8b0fb784f5d33827f960c0593efc50bf940b1a783a6cbb5cb03d5
def gen27Word1 : UInt256 :=
  0x5c272fd3f9bdc34dfb2fd5a44e94520fb163423425589c5ffda9bf163e26fa24
def gen27Word2 : UInt256 :=
  0xa29d6ad5630ac16788e062388c7423733cb87412b337fb8a6c899c8fd753fc31
def gen27Word3 : UInt256 :=
  0x1f3a147b8b24c86fdb0504ece68cc5335e085869bc1568e89f7053d5463852fb

/-- The pushed literals at indices 4119, 4125, 4131 and 4137 are exactly
`gen27Word0` … `gen27Word3`: `PUSH32` needs no shift, so each guard test is a
full-word equality and `input_eq_gen27` applies. -/

@[simp] theorem gen27Input_size : gen27Input.size = 128 := by rfl
@[simp] theorem gen27Digest_size : gen27Digest.size = 20 := by rfl
@[simp] theorem gen27PaddedDigest_size : gen27PaddedDigest.size = 32 := by rfl

/-- The `gen27Input` message schedule: two full data blocks plus the padding
tail block (three 64-byte blocks total). -/
def gen27Block0 : Array UInt32 :=
  #[0x86936391, 0xfbb0c865, 0x335d4f78, 0x0c967f82,
    0xc5ef9305, 0xb140f90b, 0xcba683a7, 0xd503cbb5,
    0xd32f275c, 0x4dc3bdf9, 0xa4d52ffb, 0x0f52944e,
    0x344263b1, 0x5f9c5825, 0x16bfa9fd, 0x24fa263e]

def gen27Block1 : Array UInt32 :=
  #[0xd56a9da2, 0x67c10a63, 0x3862e088, 0x7323748c,
    0x1274b83c, 0x8afb37b3, 0x8f9c896c, 0x31fc53d7,
    0x7b143a1f, 0x6fc8248b, 0xec0405db, 0x33c58ce6,
    0x6958085e, 0xe86815bc, 0xd553709f, 0xfb523846]

/-- The padding tail: `0x80`, zeros, then the 1024-bit length as a little-endian
quad word.  `paddedMessage gen27Input = gen27Input ++ gen27Tail`. -/
def gen27Tail : ByteArray := ByteArray.mk #[
  0x80, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 0, 0, 0,
  0, 4, 0, 0, 0, 0, 0, 0]

@[simp] theorem gen27Tail_size : gen27Tail.size = 64 := by decide

def gen27TailWords : Array UInt32 :=
  #[0x00000080, 0x00000000, 0x00000000, 0x00000000,
    0x00000000, 0x00000000, 0x00000000, 0x00000000,
    0x00000000, 0x00000000, 0x00000000, 0x00000000,
    0x00000000, 0x00000000, 0x00000400, 0x00000000]

/-- The chaining state after compressing block 0 from `H0`. -/
def gen27H1 : Array UInt32 :=
  #[0x7d95f789, 0x133ab702, 0x4c80c062, 0xda83335a, 0x1a5e92c9]

/-- The chaining state after compressing block 1. -/
def gen27H2 : Array UInt32 :=
  #[0xd2039ccc, 0x772e51a8, 0x1402e1f2, 0xe0c141d0, 0xd0b6279b]

/-- The chaining state after compressing the tail block: emits `gen27Digest`. -/
def gen27FinalState : Array UInt32 :=
  #[0x0811139a, 0xc4bb3a33, 0xae725586, 0x320995ba, 0x99ecd7fd]

end Challenge.Ripemd160.Submission.Proofs.Bytecode.Gen27InputData
