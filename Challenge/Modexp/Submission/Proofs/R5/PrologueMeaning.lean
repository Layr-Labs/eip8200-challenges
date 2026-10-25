import Challenge.Modexp.Submission.Proofs.R5.PrologueRun
import Challenge.Modexp.Submission.Proofs.R5.Digits
set_option warningAsError true
set_option linter.unusedSimpArgs false
set_option maxRecDepth 40000
set_option maxHeartbeats 16000000
set_option exponentiation.threshold 4096

/-!
# What the r5 prologue leaves behind

After the eight stores of `proSeg` the scratch words are `inv' = ninv << 16` at 0xc0,
`M = 2^240 - 1` at 0xe0, `n0` at 0xa0 and the base digits `b0..b4` at 0x00..0x80; the input
windows (N at 0x000, B at 0x100, A at 0x840) are read before they could be overwritten, and A is
never overwritten. The digits are those of `Digits`.
-/

namespace CycleSubmission.R5.PrologueMeaning
open EvmSemantics Challenge.EvmProof.Word
open Challenge.Modexp.Submission.Proofs
open CycleSubmission.WordArithmetic CycleSubmission.R5.Digits
open CycleSubmission.R5.ExecPrologue CycleSubmission.R5.PrologueRun

theorem size32 (v : Nat) : (Data.Bytes.natToBytesPadded v 32).size = 32 := by
  simp [Data.Bytes.natToBytesPadded, ByteArray.size]

/-- A read past a 32-byte store. -/
theorem read_past (mem : ByteArray) (v a b : Nat) (h : b + 32 ≤ a ∨ a + 32 ≤ b) :
    MachineState.readWord (MachineState.writeBytes mem (Data.Bytes.natToBytesPadded v 32) a) b =
      MachineState.readWord mem b :=
  Challenge.EvmProof.Memory.readWord_writeBytes_disjoint mem _ b a (by rw [size32]; exact h)

/-- A read of the stored word. -/
theorem read_same (mem : ByteArray) (w : UInt256) (a : Nat) :
    MachineState.readWord (MachineState.writeBytes mem (Data.Bytes.natToBytesPadded w.toNat 32) a) a = w :=
  Challenge.EvmProof.Memory.readWord_writeWord mem a w

theorem mask_word : UInt256.shiftRight (UInt256.lnot (UInt256.ofNat 0)) (UInt256.ofNat 16) = M := by
  unfold M; decide

theorem prime_word : UInt256.shiftRight (UInt256.lnot (UInt256.ofNat 0)) (UInt256.ofNat 5) =
    CycleSubmission.WordArithmetic.P := by
  unfold CycleSubmission.WordArithmetic.P; decide

section
variable (mem : ByteArray) (f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 : UInt256)

/-- The memory after the eight stores. -/
abbrev M7 : ByteArray := proSegM7 mem f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15

theorem m7_inv : MachineState.readWord (M7 mem f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15) 192 =
    UInt256.shiftLeft f11 (UInt256.ofNat 16) := by
  simp (config := { decide := true }) only [M7, proSegM7, proSegM6, proSegM5, proSegM4, proSegM3, proSegM2,
    proSegM1, proSegM0, pro_mem, blk5344_mem, blk5352_mem, blk5393_mem, blk5403_mem, blk5414_mem,
    blk5425_mem, blk5436_mem, read_past, read_same, proSegV0_0, pro_o0]

theorem m7_mask : MachineState.readWord (M7 mem f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15) 224 = M := by
  simp (config := { decide := true }) only [M7, proSegM7, proSegM6, proSegM5, proSegM4, proSegM3, proSegM2,
    proSegM1, proSegM0, pro_mem, blk5344_mem, blk5352_mem, blk5393_mem, blk5403_mem, blk5414_mem,
    blk5425_mem, blk5436_mem, read_past, read_same, mask_word]

theorem m7_n0 : MachineState.readWord (proSegM7 mem f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15) 160 = UInt256.land M (MachineState.readWord mem 96) := by
  simp (config := { decide := true }) only [proSegM7, proSegM6, proSegM5, proSegM4, proSegM3, proSegM2, proSegM1, proSegM0, pro_mem, blk5344_mem, blk5352_mem, blk5393_mem, blk5403_mem, blk5414_mem, blk5425_mem, blk5436_mem,
    read_past, read_same, mask_word]

theorem m7_b0 : MachineState.readWord (proSegM7 mem f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15) 0 = UInt256.land M (MachineState.readWord mem 352) := by
  simp (config := { decide := true }) only [proSegM7, proSegM6, proSegM5, proSegM4, proSegM3, proSegM2, proSegM1, proSegM0, pro_mem, blk5344_mem, blk5352_mem, blk5393_mem, blk5403_mem, blk5414_mem, blk5425_mem, blk5436_mem,
    read_past, read_same, mask_word]

theorem m7_b1 : MachineState.readWord (proSegM7 mem f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15) 32 = UInt256.land M (MachineState.readWord mem 322) := by
  simp (config := { decide := true }) only [proSegM7, proSegM6, proSegM5, proSegM4, proSegM3, proSegM2, proSegM1, proSegM0, pro_mem, blk5344_mem, blk5352_mem, blk5393_mem, blk5403_mem, blk5414_mem, blk5425_mem, blk5436_mem,
    read_past, read_same, mask_word]

theorem m7_b2 : MachineState.readWord (proSegM7 mem f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15) 64 = UInt256.land M (MachineState.readWord mem 292) := by
  simp (config := { decide := true }) only [proSegM7, proSegM6, proSegM5, proSegM4, proSegM3, proSegM2, proSegM1, proSegM0, pro_mem, blk5344_mem, blk5352_mem, blk5393_mem, blk5403_mem, blk5414_mem, blk5425_mem, blk5436_mem,
    read_past, read_same, mask_word]

theorem m7_b3 : MachineState.readWord (proSegM7 mem f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15) 96 = UInt256.land M (MachineState.readWord mem 262) := by
  simp (config := { decide := true }) only [proSegM7, proSegM6, proSegM5, proSegM4, proSegM3, proSegM2, proSegM1, proSegM0, pro_mem, blk5344_mem, blk5352_mem, blk5393_mem, blk5403_mem, blk5414_mem, blk5425_mem, blk5436_mem,
    read_past, read_same, mask_word]

theorem m7_b4 : MachineState.readWord (proSegM7 mem f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15) 128 = UInt256.shiftRight (MachineState.readWord mem 256) (UInt256.ofNat 192) := by
  simp (config := { decide := true }) only [proSegM7, proSegM6, proSegM5, proSegM4, proSegM3, proSegM2, proSegM1, proSegM0, pro_mem, blk5344_mem, blk5352_mem, blk5393_mem, blk5403_mem, blk5414_mem, blk5425_mem, blk5436_mem,
    read_past, read_same, mask_word]

theorem m7_mask' : MachineState.readWord (proSegM7 mem f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15) 224 = M := by
  simp (config := { decide := true }) only [proSegM7, proSegM6, proSegM5, proSegM4, proSegM3, proSegM2, proSegM1, proSegM0, pro_mem, blk5344_mem, blk5352_mem, blk5393_mem, blk5403_mem, blk5414_mem, blk5425_mem, blk5436_mem,
    read_past, read_same, mask_word]

theorem m7_inv' : MachineState.readWord (proSegM7 mem f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15) 192 = proSegV0_0 mem f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 := by
  simp (config := { decide := true }) only [proSegM7, proSegM6, proSegM5, proSegM4, proSegM3, proSegM2, proSegM1, proSegM0, pro_mem, blk5344_mem, blk5352_mem, blk5393_mem, blk5403_mem, blk5414_mem, blk5425_mem, blk5436_mem,
    read_past, read_same, mask_word, proSegV0_0, pro_o0]

theorem m7_high (a : Nat) (ha : 256 ≤ a) :
    MachineState.readWord (proSegM7 mem f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15) a = MachineState.readWord mem a := by
  simp (disch := omega) only [proSegM7, proSegM6, proSegM5, proSegM4, proSegM3, proSegM2, proSegM1, proSegM0, pro_mem, blk5344_mem, blk5352_mem, blk5393_mem, blk5403_mem, blk5414_mem, blk5425_mem, blk5436_mem,
    read_past]

theorem v_n1 : proSegV2_0 mem f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 = UInt256.land M (MachineState.readWord mem 66) := by
  simp (config := { decide := true }) only [proSegV2_0, blk5352_o0, proSegM7, proSegM6, proSegM5, proSegM4, proSegM3, proSegM2, proSegM1, proSegM0, pro_mem, blk5344_mem, blk5352_mem, blk5393_mem, blk5403_mem, blk5414_mem, blk5425_mem, blk5436_mem,
    read_past, read_same, mask_word]

theorem v_n2 : proSegV2_1 mem f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 = UInt256.land M (MachineState.readWord mem 36) := by
  simp (config := { decide := true }) only [proSegV2_1, blk5352_o1, proSegM7, proSegM6, proSegM5, proSegM4, proSegM3, proSegM2, proSegM1, proSegM0, pro_mem, blk5344_mem, blk5352_mem, blk5393_mem, blk5403_mem, blk5414_mem, blk5425_mem, blk5436_mem,
    read_past, read_same, mask_word]

theorem v_n3 : proSegV2_2 mem f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 = UInt256.land M (MachineState.readWord mem 6) := by
  simp (config := { decide := true }) only [proSegV2_2, blk5352_o2, proSegM7, proSegM6, proSegM5, proSegM4, proSegM3, proSegM2, proSegM1, proSegM0, pro_mem, blk5344_mem, blk5352_mem, blk5393_mem, blk5403_mem, blk5414_mem, blk5425_mem, blk5436_mem,
    read_past, read_same, mask_word]

theorem v_n4 : proSegV2_3 mem f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 = UInt256.shiftRight (MachineState.readWord mem 0) (UInt256.ofNat 192) := by
  simp (config := { decide := true }) only [proSegV2_3, blk5352_o3, proSegM7, proSegM6, proSegM5, proSegM4, proSegM3, proSegM2, proSegM1, proSegM0, pro_mem, blk5344_mem, blk5352_mem, blk5393_mem, blk5403_mem, blk5414_mem, blk5425_mem, blk5436_mem,
    read_past, read_same, mask_word]

theorem v_P : proSegV2_4 mem f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 = CycleSubmission.WordArithmetic.P := by
  simp only [proSegV2_4, blk5352_o4, prime_word]

theorem v_inv : proSegV0_0 mem f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 = UInt256.shiftLeft f11 (UInt256.ofNat 16) := rfl

theorem v_x4 : proSegV8_1 mem f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 =
    UInt256.shiftRight (MachineState.readWord mem 2112) (UInt256.ofNat 16) := by
  simp only [proSegV8_1, blk5446_o1, m7_high mem f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 2112 (by decide)]

theorem v_cond : proSegV8_0 mem f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 = UInt256.eq (UInt256.ofNat 1099511627775)
    (UInt256.shiftRight (UInt256.shiftRight (MachineState.readWord mem 2112) (UInt256.ofNat 16)) (UInt256.ofNat 200)) := by
  simp only [proSegV8_0, blk5446_o0, m7_high mem f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 2112 (by decide)]

end

end CycleSubmission.R5.PrologueMeaning
