import Challenge.Ripemd160.Spec
import Challenge.Ripemd160.Submission.Proofs.Bytecode.HashSpecBridge
import Challenge.Ripemd160.Submission.Proofs.Bytecode.CompressionCorrect
import Init.Tactics
import Mathlib.Tactic.NormNum

set_option warningAsError true
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000

/-! H35 empty-input specification base case. -/

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.EmptySpec

open Challenge.Ripemd160
open EvmSemantics
open EvmSemantics.Crypto

def digestNat : Nat :=
  0x9c1185a5c5e9fc54612808977ee8f548b2258d31

def emptyDigest : ByteArray := ByteArray.mk #[
  0x9c, 0x11, 0x85, 0xa5, 0xc5, 0xe9, 0xfc, 0x54,
  0x61, 0x28, 0x08, 0x97, 0x7e, 0xe8, 0xf5, 0x48,
  0xb2, 0x25, 0x8d, 0x31]

def emptyOutput : ByteArray := ByteArray.mk #[
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
  0x9c, 0x11, 0x85, 0xa5, 0xc5, 0xe9, 0xfc, 0x54,
  0x61, 0x28, 0x08, 0x97, 0x7e, 0xe8, 0xf5, 0x48,
  0xb2, 0x25, 0x8d, 0x31]

private def emptyPaddedBlock : ByteArray :=
  ByteArray.mk #[0x80] ++ ByteArray.mk (Array.replicate 63 0)

private theorem empty_padded :
    HashSpecBridge.canonicalTail ByteArray.empty = emptyPaddedBlock := by
  have hzero : Padding.zeroBytes 0 =
      ByteArray.mk (Array.replicate 55 0) := by
    norm_num [Padding.zeroBytes, Padding.zeroCount, Padding.paddedLength]
  have hlen : Padding.lengthBytes ByteArray.empty =
      ByteArray.mk (Array.replicate 8 0) := by
    apply ByteArray.ext_getElem
    · simp only [Padding.lengthBytes, ByteArray.size_ofFn]
      change 8 = (Array.replicate 8 (0 : UInt8)).size
      simp
    · intro i hleft hright
      have hi : i < 8 := by
        simpa only [Padding.lengthBytes, ByteArray.size_ofFn] using hleft
      rw [Padding.lengthByte ByteArray.empty i hi]
      simp [ByteArray.getElem_eq_getElem_data, ByteArray.size_empty]
  rw [HashSpecBridge.canonicalTail_eq]
  simp only [ByteArray.size_empty, Nat.zero_div, ByteArray.extract_same]
  rw [hzero, hlen]
  apply ByteArray.ext
  simp [emptyPaddedBlock]

private def emptyWords : Array UInt32 := #[
  0x00000080, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 0, 0, 0]

private def emptyWord (i : Nat) : UInt32 := emptyWords[i]!

private def leftSegment (start count : Nat) (x : Compression.Working) :
    Compression.Working :=
  (List.range' start count).foldl
    (fun x i => CompressionCorrect.leftStep emptyWord i x) x

private def rightSegment (start count : Nat) (x : Compression.Working) :
    Compression.Working :=
  (List.range' start count).foldl
    (fun x i => CompressionCorrect.rightStep emptyWord i x) x

private theorem leftRounds_eq_segment (start count : Nat)
    (x : Compression.Working) :
    CompressionCorrect.leftRounds emptyWord (start + count) x =
      leftSegment start count
        (CompressionCorrect.leftRounds emptyWord start x) := by
  induction count with
  | zero => rfl
  | succ count ih =>
      rw [show start + (count + 1) = (start + count) + 1 by omega,
        CompressionCorrect.leftRounds, ih]
      simp [leftSegment, List.range'_concat, List.foldl_append]

private theorem rightRounds_eq_segment (start count : Nat)
    (x : Compression.Working) :
    CompressionCorrect.rightRounds emptyWord (start + count) x =
      rightSegment start count
        (CompressionCorrect.rightRounds emptyWord start x) := by
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
    CompressionCorrect.leftRounds emptyWord 80 x =
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
    CompressionCorrect.rightRounds emptyWord 80 x =
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
  { h0 := 0xA585119C, h1 := 0x54FCE9C5, h2 := 0x97082861,
    h3 := 0x48F5E87E, h4 := 0x318D25B2 }

private def initWorking : Compression.Working :=
  { a := 0x67452301, b := 0xEFCDAB89, c := 0x98BADCFE,
    d := 0x10325476, e := 0xC3D2E1F0 }

private def leftW1 : Compression.Working :=
  { a := 0xD73BF2A6, b := 0xB7D5FBF8, c := 0x2BB93C4E,
    d := 0x4BB005D3, e := 0x3AD53BCD }

private def leftW2 : Compression.Working :=
  { a := 0x1C283F0C, b := 0xA8C519B5, c := 0x1124553D,
    d := 0xB8B785D6, e := 0x6B9E4E09 }

private def leftW3 : Compression.Working :=
  { a := 0x465AA0A8, b := 0x85BC6D0E, c := 0x12180343,
    d := 0xD4F14AC0, e := 0x6B8A5924 }

private def leftW4 : Compression.Working :=
  { a := 0xEA416391, b := 0xF15D511E, c := 0x3C987B47,
    d := 0x2EC07B7B, e := 0x6206D561 }

private def leftW5 : Compression.Working :=
  { a := 0x69C5DAEA, b := 0xAB92E7B1, c := 0x1CD555AD,
    d := 0x7681DE91, e := 0xDB12F567 }

private def leftW6 : Compression.Working :=
  { a := 0xB5074004, b := 0x6995D6C5, c := 0x946BBA85,
    d := 0x297CF675, e := 0xF2D46CD9 }

private def leftW7 : Compression.Working :=
  { a := 0x246D1008, b := 0xABFABA0B, c := 0x75F256DE,
    d := 0x40467819, e := 0x1E812947 }

private def leftW8 : Compression.Working :=
  { a := 0x9FDAB2B4, b := 0xE42BD59B, c := 0xAED7C70D,
    d := 0xD8C862E1, e := 0x88714640 }

private def leftW9 : Compression.Working :=
  { a := 0x797F08BF, b := 0x00609E2E, c := 0xEB20AB90,
    d := 0xDE273BE0, e := 0x4BC527B1 }

private def leftW10 : Compression.Working :=
  { a := 0x594637A7, b := 0x215D97B3, c := 0xEBA027EB,
    d := 0xB99CDC7A, e := 0xEC4DCDFF }

private def rightW1 : Compression.Working :=
  { a := 0x8EAE75E2, b := 0x63A849B4, c := 0x17B2CB4D,
    d := 0x43514825, e := 0x232CC066 }

private def rightW2 : Compression.Working :=
  { a := 0xFC163248, b := 0xF7166D44, c := 0x17A05994,
    d := 0x6F9C0D4C, e := 0xFB9C1EC9 }

private def rightW3 : Compression.Working :=
  { a := 0xE6BBB353, b := 0x4EB0D4FA, c := 0xAC9E6D6C,
    d := 0xEC2B634F, e := 0xA5A050AB }

private def rightW4 : Compression.Working :=
  { a := 0x66F8D648, b := 0x6C38CBA5, c := 0x0B740887,
    d := 0xD3D5139C, e := 0xE0BBFF46 }

private def rightW5 : Compression.Working :=
  { a := 0x5177D625, b := 0x227EB263, c := 0x1FACF8A6,
    d := 0x01E83D7F, e := 0x71E205BC }

private def rightW6 : Compression.Working :=
  { a := 0xCA284532, b := 0xE4C055A0, c := 0xB00A7AFA,
    d := 0x9091CBAC, e := 0x8F55B0BE }

private def rightW7 : Compression.Working :=
  { a := 0x446BBECC, b := 0x1F3B7558, c := 0x35099B55,
    d := 0xA3973AE6, e := 0xF87B5F0B }

private def rightW8 : Compression.Working :=
  { a := 0x362A73CB, b := 0x986D284F, c := 0xA0E04D8B,
    d := 0xDBCB7F0A, e := 0xC5B07E0A }

private def rightW9 : Compression.Working :=
  { a := 0x6DECF138, b := 0x495BD810, c := 0x9298548D,
    d := 0x40F398A8, e := 0xBDF5E58A }

private def rightW10 : Compression.Working :=
  { a := 0x9A8805EC, b := 0x2BDCCEE7, c := 0xA8EA6AFE,
    d := 0xCA173E28, e := 0x02A5304D }

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

private theorem left_empty_final :
    CompressionCorrect.leftRounds emptyWord 80
      (CompressionCorrect.workingOfHash initHash) = leftW10 := by
  rw [workingOfHash_init, leftRounds_80]
  rw [left_seg0, left_seg1, left_seg2, left_seg3, left_seg4]
  rw [left_seg5, left_seg6, left_seg7, left_seg8, left_seg9]

private theorem right_empty_final :
    CompressionCorrect.rightRounds emptyWord 80
      (CompressionCorrect.workingOfHash initHash) = rightW10 := by
  rw [workingOfHash_init, rightRounds_80]
  rw [right_seg0, right_seg1, right_seg2, right_seg3, right_seg4]
  rw [right_seg5, right_seg6, right_seg7, right_seg8, right_seg9]

theorem compress_empty :
    CompressionCorrect.compressModel emptyWord initHash = finalHash := by
  unfold CompressionCorrect.compressModel
  rw [left_empty_final, right_empty_final]
  rfl

private theorem schedule_empty :
    CompressionCorrect.schedule emptyPaddedBlock 0 = emptyWords := by
  unfold CompressionCorrect.schedule
    EvmSemantics.Crypto.Ripemd160.readLE32
  simp only [Std.Legacy.Range.forIn_eq_forIn_range',
    Std.Legacy.Range.size, Nat.sub_zero, Nat.add_sub_cancel,
    Nat.div_one, pure_bind, List.forIn_pure_yield_eq_foldl,
    Id.run_pure]
  rfl

private theorem word_fun_empty :
    (fun i => (CompressionCorrect.schedule emptyPaddedBlock 0)[i]!) =
      emptyWord := by
  rw [schedule_empty]
  rfl

private theorem hashArray_init :
    CompressionCorrect.hashArray initHash =
      EvmSemantics.Crypto.Ripemd160.H0 := by
  rfl

private theorem compressBlock_empty :
    EvmSemantics.Crypto.Ripemd160.compressBlock
      EvmSemantics.Crypto.Ripemd160.H0 emptyPaddedBlock 0 =
      CompressionCorrect.hashArray finalHash := by
  have hbridge :=
    CompressionCorrect.compressModel_eq_compressBlock
      emptyPaddedBlock 0 initHash
  rw [hashArray_init, word_fun_empty, compress_empty] at hbridge
  exact hbridge.symm

private theorem paddedMessage_empty :
    Padding.paddedMessage ByteArray.empty = emptyPaddedBlock := by
  have hfull : HashSpecBridge.fullPrefix ByteArray.empty =
      ByteArray.empty := by
    unfold HashSpecBridge.fullPrefix
    simp
  have hpad := HashSpecBridge.paddedMessage_eq_prefix_tail
    ByteArray.empty
  rw [hfull, empty_padded] at hpad
  simpa using hpad

private theorem paddedLength_empty :
    Padding.paddedLength ByteArray.empty.size / 64 = 1 := by
  decide

private theorem absorb_empty :
    SpecBridge.absorbBlocks EvmSemantics.Crypto.Ripemd160.H0
      (Padding.paddedMessage ByteArray.empty) 0 1 =
      CompressionCorrect.hashArray finalHash := by
  rw [paddedMessage_empty]
  have hsucc := SpecBridge.absorbBlocks_succ
    EvmSemantics.Crypto.Ripemd160.H0 emptyPaddedBlock 0 0
  simp only [SpecBridge.absorbBlocks_zero, Nat.zero_add,
    Nat.zero_mul] at hsucc
  rw [hsucc]
  exact compressBlock_empty

private theorem emit_empty :
    SpecBridge.emitDigest
      (CompressionCorrect.hashArray finalHash) = emptyDigest := by
  unfold SpecBridge.emitDigest
    EvmSemantics.Crypto.Ripemd160.writeLE32
  simp only [Std.Legacy.Range.forIn_eq_forIn_range',
    Std.Legacy.Range.size, Nat.sub_zero, Nat.add_sub_cancel,
    Nat.div_one, pure_bind, List.forIn_pure_yield_eq_foldl,
    Id.run_pure]
  rfl

private theorem paddedHash_empty :
    SpecBridge.paddedHash ByteArray.empty = emptyDigest := by
  unfold SpecBridge.paddedHash
  rw [paddedLength_empty, absorb_empty]
  exact emit_empty

theorem hash_empty :
    EvmSemantics.Crypto.Ripemd160.hash ByteArray.empty =
      emptyDigest := by
  have h := HashSpecBridge.paddedHash_eq_hash ByteArray.empty
  rw [paddedHash_empty] at h
  exact h.symm

theorem spec_empty :
    Challenge.Ripemd160.spec ByteArray.empty = emptyOutput := by
  unfold Challenge.Ripemd160.spec
  simp only [Std.Legacy.Range.forIn_eq_forIn_range',
    Std.Legacy.Range.size, Nat.sub_zero, Nat.add_sub_cancel,
    Nat.div_one, pure_bind, List.forIn_pure_yield_eq_foldl,
    Id.run_pure]
  rw [hash_empty]
  rfl

end Challenge.Ripemd160.Submission.Proofs.Bytecode.EmptySpec
