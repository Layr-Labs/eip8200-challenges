import Challenge.Ripemd160.Spec
import Challenge.Ripemd160.Submission.Proofs.Bytecode.HashSpecBridge
import Challenge.Ripemd160.Submission.Proofs.Bytecode.CompressionCorrect
import Init.Tactics
import Mathlib.Tactic.NormNum

set_option warningAsError true
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000

/-! Kernel-checked specification for the exact three-byte input `abc`. -/

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.TinyABCSpec

open Challenge.Ripemd160
open EvmSemantics
open EvmSemantics.Crypto

def inputBytes : ByteArray := ByteArray.mk #[0x61, 0x62, 0x63]

def digestNat : Nat :=
  0x8eb208f7e05d987a9b044a8e98c6b087f15a0bfc

def abcDigest : ByteArray := ByteArray.mk #[0x8e, 0xb2, 0x08, 0xf7, 0xe0, 0x5d, 0x98, 0x7a, 0x9b, 0x04, 0x4a, 0x8e, 0x98, 0xc6, 0xb0, 0x87, 0xf1, 0x5a, 0x0b, 0xfc]

def abcOutput : ByteArray := ByteArray.mk #[0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x8e, 0xb2, 0x08, 0xf7, 0xe0, 0x5d, 0x98, 0x7a, 0x9b, 0x04, 0x4a, 0x8e, 0x98, 0xc6, 0xb0, 0x87, 0xf1, 0x5a, 0x0b, 0xfc]

private def abcPaddedBlock : ByteArray :=
  ByteArray.mk #[0x61, 0x62, 0x63, 0x80, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x18, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00]

private def abcWords : Array UInt32 := #[0x80636261, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x18, 0x0]

private def abcWord (i : Nat) : UInt32 := abcWords[i]!

private def leftSegment (start count : Nat) (x : Compression.Working) :
    Compression.Working :=
  (List.range' start count).foldl
    (fun x i => CompressionCorrect.leftStep abcWord i x) x

private def rightSegment (start count : Nat) (x : Compression.Working) :
    Compression.Working :=
  (List.range' start count).foldl
    (fun x i => CompressionCorrect.rightStep abcWord i x) x

private theorem leftRounds_eq_segment (start count : Nat)
    (x : Compression.Working) :
    CompressionCorrect.leftRounds abcWord (start + count) x =
      leftSegment start count
        (CompressionCorrect.leftRounds abcWord start x) := by
  induction count with
  | zero => rfl
  | succ count ih =>
      rw [show start + (count + 1) = (start + count) + 1 by omega,
        CompressionCorrect.leftRounds, ih]
      simp [leftSegment, List.range'_concat, List.foldl_append]

private theorem rightRounds_eq_segment (start count : Nat)
    (x : Compression.Working) :
    CompressionCorrect.rightRounds abcWord (start + count) x =
      rightSegment start count
        (CompressionCorrect.rightRounds abcWord start x) := by
  induction count with
  | zero => rfl
  | succ count ih =>
      rw [show start + (count + 1) = (start + count) + 1 by omega,
        CompressionCorrect.rightRounds, ih]
      simp [rightSegment, List.range'_concat, List.foldl_append]

private theorem leftSegment_add (start count₁ count₂ : Nat)
    (x : Compression.Working) :
    leftSegment start (count₁ + count₂) x =
      leftSegment (start + count₁) count₂ (leftSegment start count₁ x) := by
  unfold leftSegment
  rw [← List.range'_append_1, List.foldl_append]

private theorem rightSegment_add (start count₁ count₂ : Nat)
    (x : Compression.Working) :
    rightSegment start (count₁ + count₂) x =
      rightSegment (start + count₁) count₂ (rightSegment start count₁ x) := by
  unfold rightSegment
  rw [← List.range'_append_1, List.foldl_append]

private theorem leftRounds_80 (x : Compression.Working) :
    CompressionCorrect.leftRounds abcWord 80 x =
      leftSegment 72 8
        (leftSegment 64 8
          (leftSegment 56 8
            (leftSegment 48 8
              (leftSegment 40 8
                (leftSegment 32 8
                  (leftSegment 24 8
                    (leftSegment 16 8
                      (leftSegment 8 8 (leftSegment 0 8 x))))))))) := by
  rw [leftRounds_eq_segment 0 80 x]
  simp only [CompressionCorrect.leftRounds]
  rw [leftSegment_add 0 8 72, leftSegment_add 8 8 64,
    leftSegment_add 16 8 56, leftSegment_add 24 8 48,
    leftSegment_add 32 8 40, leftSegment_add 40 8 32,
    leftSegment_add 48 8 24, leftSegment_add 56 8 16,
    leftSegment_add 64 8 8]

private theorem rightRounds_80 (x : Compression.Working) :
    CompressionCorrect.rightRounds abcWord 80 x =
      rightSegment 72 8
        (rightSegment 64 8
          (rightSegment 56 8
            (rightSegment 48 8
              (rightSegment 40 8
                (rightSegment 32 8
                  (rightSegment 24 8
                    (rightSegment 16 8
                      (rightSegment 8 8 (rightSegment 0 8 x))))))))) := by
  rw [rightRounds_eq_segment 0 80 x]
  simp only [CompressionCorrect.rightRounds]
  rw [rightSegment_add 0 8 72, rightSegment_add 8 8 64,
    rightSegment_add 16 8 56, rightSegment_add 24 8 48,
    rightSegment_add 32 8 40, rightSegment_add 40 8 32,
    rightSegment_add 48 8 24, rightSegment_add 56 8 16,
    rightSegment_add 64 8 8]

def initHash : Compression.HashState :=
  { h0 := 0x67452301, h1 := 0xEFCDAB89, h2 := 0x98BADCFE,
    h3 := 0x10325476, h4 := 0xC3D2E1F0 }

def finalHash : Compression.HashState :=
  {h0 := 0xf708b28e, h1 := 0x7a985de0, h2 := 0x8e4a049b, h3 := 0x87b0c698, h4 := 0xfc0b5af1 }

private def initWorking : Compression.Working :=
  { a := 0x67452301, b := 0xEFCDAB89, c := 0x98BADCFE,
    d := 0x10325476, e := 0xC3D2E1F0 }

private def leftW1 : Compression.Working :=
  {a := 0xe1904f4d, b := 0x3d6f601f, c := 0x150bd8a8, d := 0xafd8cb54, e := 0x519c803a }

private def leftW2 : Compression.Working :=
  {a := 0xb2925676, b := 0x597bf629, c := 0x85861d02, d := 0x53c14c52, e := 0x17d1bef0 }

private def leftW3 : Compression.Working :=
  {a := 0xbc5add7a, b := 0x4d4d4377, c := 0x42ecc93, d := 0x332f4ff0, e := 0xcc352d05 }

private def leftW4 : Compression.Working :=
  {a := 0x287f668c, b := 0x2d30fa02, c := 0xb6a665c6, d := 0x8477bbdc, e := 0x8acc6ef6 }

private def leftW5 : Compression.Working :=
  {a := 0xe5897b54, b := 0x960f7bfd, c := 0x681d30b9, d := 0x3796c9fb, e := 0x40326761 }

private def leftW6 : Compression.Working :=
  {a := 0x2c01a201, b := 0x77367f5e, c := 0xdbc5a2cb, d := 0xaf097749, e := 0x6ea06d1d }

private def leftW7 : Compression.Working :=
  {a := 0xfe70c9fa, b := 0x5e3201fc, c := 0xa96be4c7, d := 0xdc45fdd6, e := 0xbfe80483 }

private def leftW8 : Compression.Working :=
  {a := 0xcc3ad1a8, b := 0xf44b53a7, c := 0x210769b3, d := 0xabd4f9e6, e := 0x96081053 }

private def leftW9 : Compression.Working :=
  {a := 0x190096b6, b := 0xba84c782, c := 0xa719d8bc, d := 0xb8e44189, e := 0xa0eed4a6 }

private def leftW10 : Compression.Working :=
  {a := 0x641129ca, b := 0xd563bfdc, c := 0xb2cdc01, d := 0x6e413468, e := 0xfc433da8 }

private def rightW1 : Compression.Working :=
  {a := 0xcade6e4a, b := 0xe755f422, c := 0x8b2d9fb3, d := 0xc2664b96, e := 0x247fcbe4 }

private def rightW2 : Compression.Working :=
  {a := 0xfdb61089, b := 0xff459078, c := 0x3d16242d, d := 0xfd356cf, e := 0x5a1576 }

private def rightW3 : Compression.Working :=
  {a := 0x85ccb989, b := 0x5fc74686, c := 0x82f89bd1, d := 0xf159a090, e := 0xb49ebd17 }

private def rightW4 : Compression.Working :=
  {a := 0xa4372b30, b := 0x2999255a, c := 0xaa98adb5, d := 0x86d69581, e := 0xf5897a18 }

private def rightW5 : Compression.Working :=
  {a := 0x2d22eb17, b := 0xc699295b, c := 0x333f2212, d := 0xe5b74a20, e := 0xa1b7ec14 }

private def rightW6 : Compression.Working :=
  {a := 0x69baff37, b := 0x65a60151, c := 0xc9b17f72, d := 0x59b28ddb, e := 0xb1f68d95 }

private def rightW7 : Compression.Working :=
  {a := 0x30b1e709, b := 0xb43484f4, c := 0x5b99238d, d := 0x58e52773, e := 0x5611fbc9 }

private def rightW8 : Compression.Working :=
  {a := 0xec68bac6, b := 0x5dca4d12, c := 0xa625f112, d := 0xd34c985d, e := 0xdfe5b6b1 }

private def rightW9 : Compression.Working :=
  {a := 0x6c94a6fd, b := 0x4f5ca4a5, c := 0x27754f3a, d := 0x4d697f76, e := 0x5d1f17ed }

private def rightW10 : Compression.Working :=
  {a := 0x81d4727d, b := 0x5fccbade, c := 0xbf627814, d := 0xfc0e2b04, e := 0x739c4c7a }

private theorem workingOfHash_init :
    CompressionCorrect.workingOfHash initHash = initWorking := by
  rfl

private theorem left_seg0 : leftSegment 0 8 initWorking = leftW1 := by
  rfl

private theorem left_seg1 : leftSegment 8 8 leftW1 = leftW2 := by
  rfl

private theorem left_seg2 : leftSegment 16 8 leftW2 = leftW3 := by
  rfl

private theorem left_seg3 : leftSegment 24 8 leftW3 = leftW4 := by
  rfl

private theorem left_seg4 : leftSegment 32 8 leftW4 = leftW5 := by
  rfl

private theorem left_seg5 : leftSegment 40 8 leftW5 = leftW6 := by
  rfl

private theorem left_seg6 : leftSegment 48 8 leftW6 = leftW7 := by
  rfl

private theorem left_seg7 : leftSegment 56 8 leftW7 = leftW8 := by
  rfl

private theorem left_seg8 : leftSegment 64 8 leftW8 = leftW9 := by
  rfl

private theorem left_seg9 : leftSegment 72 8 leftW9 = leftW10 := by
  rfl

private theorem right_seg0 : rightSegment 0 8 initWorking = rightW1 := by
  rfl

private theorem right_seg1 : rightSegment 8 8 rightW1 = rightW2 := by
  rfl

private theorem right_seg2 : rightSegment 16 8 rightW2 = rightW3 := by
  rfl

private theorem right_seg3 : rightSegment 24 8 rightW3 = rightW4 := by
  rfl

private theorem right_seg4 : rightSegment 32 8 rightW4 = rightW5 := by
  rfl

private theorem right_seg5 : rightSegment 40 8 rightW5 = rightW6 := by
  rfl

private theorem right_seg6 : rightSegment 48 8 rightW6 = rightW7 := by
  rfl

private theorem right_seg7 : rightSegment 56 8 rightW7 = rightW8 := by
  rfl

private theorem right_seg8 : rightSegment 64 8 rightW8 = rightW9 := by
  rfl

private theorem right_seg9 : rightSegment 72 8 rightW9 = rightW10 := by
  rfl

private theorem left_abc_final :
    CompressionCorrect.leftRounds abcWord 80
      (CompressionCorrect.workingOfHash initHash) = leftW10 := by
  rw [workingOfHash_init, leftRounds_80]
  rw [left_seg0, left_seg1, left_seg2, left_seg3, left_seg4]
  rw [left_seg5, left_seg6, left_seg7, left_seg8, left_seg9]

private theorem right_abc_final :
    CompressionCorrect.rightRounds abcWord 80
      (CompressionCorrect.workingOfHash initHash) = rightW10 := by
  rw [workingOfHash_init, rightRounds_80]
  rw [right_seg0, right_seg1, right_seg2, right_seg3, right_seg4]
  rw [right_seg5, right_seg6, right_seg7, right_seg8, right_seg9]

theorem compress_abc :
    CompressionCorrect.compressModel abcWord initHash = finalHash := by
  unfold CompressionCorrect.compressModel
  rw [left_abc_final, right_abc_final]
  rfl

private theorem schedule_abc :
    CompressionCorrect.schedule abcPaddedBlock 0 = abcWords := by
  unfold CompressionCorrect.schedule
    EvmSemantics.Crypto.Ripemd160.readLE32
  simp only [Std.Legacy.Range.forIn_eq_forIn_range',
    Std.Legacy.Range.size, Nat.sub_zero, Nat.add_sub_cancel,
    Nat.div_one, pure_bind, List.forIn_pure_yield_eq_foldl,
    Id.run_pure]
  rfl

private theorem word_fun_abc :
    (fun i => (CompressionCorrect.schedule abcPaddedBlock 0)[i]!) =
      abcWord := by
  rw [schedule_abc]
  rfl

private theorem hashArray_init :
    CompressionCorrect.hashArray initHash =
      EvmSemantics.Crypto.Ripemd160.H0 := by
  rfl

private theorem compressBlock_abc :
    EvmSemantics.Crypto.Ripemd160.compressBlock
      EvmSemantics.Crypto.Ripemd160.H0 abcPaddedBlock 0 =
      CompressionCorrect.hashArray finalHash := by
  have hbridge :=
    CompressionCorrect.compressModel_eq_compressBlock
      abcPaddedBlock 0 initHash
  rw [hashArray_init, word_fun_abc, compress_abc] at hbridge
  exact hbridge.symm

private theorem paddedMessage_abc :
    Padding.paddedMessage inputBytes = abcPaddedBlock := by
  have hzero : Padding.zeroBytes inputBytes.size =
      ByteArray.mk (Array.replicate 52 0) := by
    norm_num [Padding.zeroBytes, Padding.zeroCount, Padding.paddedLength, inputBytes, ByteArray.size]
  have hlen : Padding.lengthBytes inputBytes = ByteArray.mk #[24, 0, 0, 0, 0, 0, 0, 0] := by
    apply ByteArray.ext_getElem
    · simp only [Padding.lengthBytes, ByteArray.size_ofFn]
      rfl
    · intro i hleft hright
      have hi : i < 8 := by simpa only [Padding.lengthBytes, ByteArray.size_ofFn] using hleft
      rw [Padding.lengthByte inputBytes i hi]
      interval_cases i <;> rfl
  unfold Padding.paddedMessage
  rw [hzero, hlen]
  decide

private theorem paddedLength_abc :
    Padding.paddedLength inputBytes.size / 64 = 1 := by
  decide

private theorem absorb_abc :
    SpecBridge.absorbBlocks EvmSemantics.Crypto.Ripemd160.H0
      (Padding.paddedMessage inputBytes) 0 1 =
      CompressionCorrect.hashArray finalHash := by
  rw [paddedMessage_abc]
  have hsucc := SpecBridge.absorbBlocks_succ
    EvmSemantics.Crypto.Ripemd160.H0 abcPaddedBlock 0 0
  simp only [SpecBridge.absorbBlocks_zero, Nat.zero_add,
    Nat.zero_mul] at hsucc
  rw [hsucc]
  exact compressBlock_abc

private theorem emit_abc :
    SpecBridge.emitDigest
      (CompressionCorrect.hashArray finalHash) = abcDigest := by
  unfold SpecBridge.emitDigest
    EvmSemantics.Crypto.Ripemd160.writeLE32
  simp only [Std.Legacy.Range.forIn_eq_forIn_range',
    Std.Legacy.Range.size, Nat.sub_zero, Nat.add_sub_cancel,
    Nat.div_one, pure_bind, List.forIn_pure_yield_eq_foldl,
    Id.run_pure]
  rfl

private theorem paddedHash_abc :
    SpecBridge.paddedHash inputBytes = abcDigest := by
  unfold SpecBridge.paddedHash
  rw [paddedLength_abc, absorb_abc]
  exact emit_abc

theorem hash_abc :
    EvmSemantics.Crypto.Ripemd160.hash inputBytes =
      abcDigest := by
  have h := HashSpecBridge.paddedHash_eq_hash inputBytes
  rw [paddedHash_abc] at h
  exact h.symm

theorem spec_abc :
    Challenge.Ripemd160.spec inputBytes = abcOutput := by
  unfold Challenge.Ripemd160.spec
  simp only [Std.Legacy.Range.forIn_eq_forIn_range',
    Std.Legacy.Range.size, Nat.sub_zero, Nat.add_sub_cancel,
    Nat.div_one, pure_bind, List.forIn_pure_yield_eq_foldl,
    Id.run_pure]
  rw [hash_abc]
  rfl

end Challenge.Ripemd160.Submission.Proofs.Bytecode.TinyABCSpec
