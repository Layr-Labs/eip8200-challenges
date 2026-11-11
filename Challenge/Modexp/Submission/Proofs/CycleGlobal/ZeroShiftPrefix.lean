import Challenge.Modexp.Submission.Proofs.CycleGlobal.ShiftStates
import Challenge.Modexp.Submission.Proofs.CycleGlobal.ShiftPaths
import Challenge.Modexp.Submission.Proofs.CycleGlobal.PCCertificate
import Challenge.Modexp.Submission.Proofs.Fast.CompactConstants
noncomputable section
set_option maxRecDepth 40000
set_option maxHeartbeats 8000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
namespace CycleSubmission.Global.Fast.Shift
open Challenge.Modexp.Submission.Proofs
open Challenge.Modexp.Submission.Proofs.Fast
open Challenge.Modexp.Submission.Proofs.Fast.Shift
open Challenge.Modexp.Submission.Proofs.Bytecode
open EvmSemantics EvmSemantics.EVM

@[simp] theorem zeroPrefixPC2838 : CycleSubmission.Artifact.artifact.instructionPC 2844 = 3711 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem zeroPrefixPC2839 : CycleSubmission.Artifact.artifact.instructionPC 2845 = 3712 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem zeroPrefixPC2840 : CycleSubmission.Artifact.artifact.instructionPC 2846 = 3713 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem zeroPrefixPC2841 : CycleSubmission.Artifact.artifact.instructionPC 2847 = 3716 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem zeroPrefixPC2842 : CycleSubmission.Artifact.artifact.instructionPC 2848 = 3719 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem zeroPrefixPC2843 : CycleSubmission.Artifact.artifact.instructionPC 2849 = 3720 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem zeroPrefixPC2844 : CycleSubmission.Artifact.artifact.instructionPC 2850 = 3723 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem zeroPrefixPC2845 : CycleSubmission.Artifact.artifact.instructionPC 2851 = 3724 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem zeroPrefixPC2846 : CycleSubmission.Artifact.artifact.instructionPC 2852 = 3727 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem zeroPrefixPC2847 : CycleSubmission.Artifact.artifact.instructionPC 2853 = 3728 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem zeroPrefixPC2848 : CycleSubmission.Artifact.artifact.instructionPC 2854 = 3731 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem zeroPrefixPC2964 : CycleSubmission.Artifact.artifact.instructionPC 2970 = 3879 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem zeroPrefixPC2965 : CycleSubmission.Artifact.artifact.instructionPC 2971 = 3880 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem zeroPrefixPC2966 : CycleSubmission.Artifact.artifact.instructionPC 2972 = 3881 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem zeroPrefixPC2967 : CycleSubmission.Artifact.artifact.instructionPC 2973 = 3884 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem zeroPrefixPC2968 : CycleSubmission.Artifact.artifact.instructionPC 2974 = 3887 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem zeroPrefixPC2969 : CycleSubmission.Artifact.artifact.instructionPC 2975 = 3888 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem zeroPrefixPC2970 : CycleSubmission.Artifact.artifact.instructionPC 2976 = 3891 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem zeroPrefixPC2971 : CycleSubmission.Artifact.artifact.instructionPC 2977 = 3892 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem zeroPrefixPC2972 : CycleSubmission.Artifact.artifact.instructionPC 2978 = 3895 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem zeroPrefixPC2973 : CycleSubmission.Artifact.artifact.instructionPC 2979 = 3896 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem zeroPrefixPC2974 : CycleSubmission.Artifact.artifact.instructionPC 2980 = 3899 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl

def zeroJoinState (z : UInt256) (s : State) (mem : ByteArray)
    (n bsize esize msize k : Nat) : State :=
  {s with pc := UInt256.ofNat (headPC n + 29)
          memory := uMem0 mem n
          stack := MachineState.readWord (uMem mem n) 2112 ::
            MachineState.readWord (uMem mem n) 2080 :: UInt256.ofNat k ::
            entrySlots z (uMem mem n) n bsize esize (phaseTag s) ++ outer n bsize esize msize}

theorem jumpDestZeroJoin8 : Decode.isValidJumpDest CycleSubmission.Artifact.bytecode 2713 = true := by
  have h := CycleSubmission.Global.Binding.jumpDest 2106 (by rw [CycleSubmission.Artifact.instruction_get]; rfl)
  have hp : CycleSubmission.Artifact.artifact.instructionPC 2106 = 2713 := by
    rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
  simpa only [hp] using h

theorem run_zeroPrefix8 (z : UInt256) (s : State) (mem : ByteArray)
    (n bsize esize msize k : Nat) (hn : n = 8)
    (hshift : (MachineState.readWord mem 1536).toNat = 0)
    (hbs : bsize = 32*n) (hact : 88 ≤ s.activeWords.toNat)
    (hcode : s.executionEnv.code = CycleSubmission.Artifact.bytecode)
    (hrun : s.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock blkZero8
      (shiftLoopState z s mem n bsize esize msize k) =
      some (zeroJoinState z s mem n bsize esize msize k) := by
  have hhead : headPC n = 2684 := by simp [headPC, hn]
  have hmod : (32*n) % 2^256 = 32*n := Nat.mod_eq_of_lt (by omega)
  have hpc : loopPC mem n = 3711 := by
    simp [loopPC, CycleSubmission.Global.ZeroShiftMath.head,
      CycleSubmission.Global.ZeroShiftMath.zeroHead, hshift, hn]
  have hfix := Exp.activeWords_fix2 s 2080 (32*n) 2112 (32*n)
    (by omega) (by omega) (by omega) (by omega) hact
  have h2080 := Monpro.activeWords_fix s 2080 32 (by decide) (by omega) hact
  have h2112 := Monpro.activeWords_fix s 2112 32 (by decide) (by omega) hact
  have huv : ∀ a, a + 32 ≤ 2080 → MachineState.readWord (uMem mem n) a =
      MachineState.readWord mem a := by
    intro a ha; exact Shift.uMem_readWord_disjoint mem n a (Or.inl ha)
  have hr2080 := uMem0_readWord mem n 2080 (by omega)
  have hr2112 := uMem0_readWord mem n 2112 (by omega)
  have hu1312 := huv 1312 (by omega)
  have hu1344 := huv 1344 (by omega)
  have hu1376 := huv 1376 (by omega)
  have hu1408 := huv 1408 (by omega)
  have hu1440 := huv 1440 (by omega)
  have hu1472 := huv 1472 (by omega)
  have hu1504 := huv 1504 (by omega)
  have hu1632 := huv 1632 (by omega)
  have hu1664 := huv 1664 (by omega)
  have hu1568 := huv 1568 (by omega)
  have hu1536 := huv 1536 (by omega)
  have hu32 := huv 32 (by omega)
  subst n
  simp (config := {maxSteps := 400000})
    [blkZero8, zeroJoinState, shiftLoopState, slotKState, entrySlots, headWord, loopPC,
      opAt, pushAt, wfOp, hhead, hpc, hshift, hmod,
      CycleSubmission.Global.ZeroShiftMath.head, CycleSubmission.Global.ZeroShiftMath.zeroHead, CycleSubmission.Global.ZeroShiftMath.normalHead, headPC,
      Challenge.EvmProof.Stepper.runLocatedBlock, Challenge.EvmProof.Stepper.runLocated,
      Challenge.EvmProof.Stepper.runInstr, hcode, hrun, hbs,
      outer, Exp.outer, uMem0, Exp.mcopyMem,
      State.activeWordsAfterUInt256, State.activeWordsAfterUInt256_2,
      hfix, h2080, h2112, hr2080, hr2112,
      hu1312, hu1344, hu1376, hu1408, hu1440, hu1472, hu1504, hu1632, hu1664, hu1568, hu1536, hu32,
      jumpDestZeroJoin8, Challenge.EvmProof.Word.literal_eq_ofNat,
      Challenge.EvmProof.Word.word_toNat_ofNat, Challenge.EvmProof.Word.succ_ofNat_mod,
      Challenge.EvmProof.Word.ofNat_add_mod]
  exact ⟨hr2112, hr2080⟩

theorem jumpDestZeroJoin4 : Decode.isValidJumpDest CycleSubmission.Artifact.bytecode 10721 = true := by
  have h := CycleSubmission.Global.Binding.jumpDest 8245 (by rw [CycleSubmission.Artifact.instruction_get]; rfl)
  have hp : CycleSubmission.Artifact.artifact.instructionPC 8245 = 10721 := by
    rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
  simpa only [hp] using h

theorem run_zeroPrefix4 (z : UInt256) (s : State) (mem : ByteArray)
    (n bsize esize msize k : Nat) (hn : n = 4)
    (hshift : (MachineState.readWord mem 1536).toNat = 0)
    (hbs : bsize = 32*n) (hact : 88 ≤ s.activeWords.toNat)
    (hcode : s.executionEnv.code = CycleSubmission.Artifact.bytecode)
    (hrun : s.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock blkZero4
      (shiftLoopState z s mem n bsize esize msize k) =
      some (zeroJoinState z s mem n bsize esize msize k) := by
  have hhead : headPC n = 10692 := by simp [headPC, hn]
  have hmod : (32*n) % 2^256 = 32*n := Nat.mod_eq_of_lt (by omega)
  have hpc : loopPC mem n = 3879 := by
    simp [loopPC, CycleSubmission.Global.ZeroShiftMath.head,
      CycleSubmission.Global.ZeroShiftMath.zeroHead, hshift, hn]
  have hfix := Exp.activeWords_fix2 s 2080 (32*n) 2112 (32*n)
    (by omega) (by omega) (by omega) (by omega) hact
  have h2080 := Monpro.activeWords_fix s 2080 32 (by decide) (by omega) hact
  have h2112 := Monpro.activeWords_fix s 2112 32 (by decide) (by omega) hact
  have huv : ∀ a, a + 32 ≤ 2080 → MachineState.readWord (uMem mem n) a =
      MachineState.readWord mem a := by
    intro a ha; exact Shift.uMem_readWord_disjoint mem n a (Or.inl ha)
  have hr2080 := uMem0_readWord mem n 2080 (by omega)
  have hr2112 := uMem0_readWord mem n 2112 (by omega)
  have hu1312 := huv 1312 (by omega)
  have hu1344 := huv 1344 (by omega)
  have hu1376 := huv 1376 (by omega)
  have hu1408 := huv 1408 (by omega)
  have hu1440 := huv 1440 (by omega)
  have hu1472 := huv 1472 (by omega)
  have hu1504 := huv 1504 (by omega)
  have hu1632 := huv 1632 (by omega)
  have hu1664 := huv 1664 (by omega)
  have hu1568 := huv 1568 (by omega)
  have hu1536 := huv 1536 (by omega)
  have hu32 := huv 32 (by omega)
  subst n
  simp (config := {maxSteps := 400000})
    [blkZero4, zeroJoinState, shiftLoopState, slotKState, entrySlots, headWord, loopPC,
      opAt, pushAt, wfOp, hhead, hpc, hshift, hmod,
      CycleSubmission.Global.ZeroShiftMath.head, CycleSubmission.Global.ZeroShiftMath.zeroHead, CycleSubmission.Global.ZeroShiftMath.normalHead, headPC,
      Challenge.EvmProof.Stepper.runLocatedBlock, Challenge.EvmProof.Stepper.runLocated,
      Challenge.EvmProof.Stepper.runInstr, hcode, hrun, hbs,
      outer, Exp.outer, uMem0, Exp.mcopyMem,
      State.activeWordsAfterUInt256, State.activeWordsAfterUInt256_2,
      hfix, h2080, h2112, hr2080, hr2112,
      hu1312, hu1344, hu1376, hu1408, hu1440, hu1472, hu1504, hu1632, hu1664, hu1568, hu1536, hu32,
      jumpDestZeroJoin4, Challenge.EvmProof.Word.literal_eq_ofNat,
      Challenge.EvmProof.Word.word_toNat_ofNat, Challenge.EvmProof.Word.succ_ofNat_mod,
      Challenge.EvmProof.Word.ofNat_add_mod]
  exact ⟨hr2112, hr2080⟩

theorem jumpDestLoop2684 : Decode.isValidJumpDest CycleSubmission.Artifact.bytecode 2684 = true := by
  have h := CycleSubmission.Global.Binding.jumpDest 2087 (by rw [CycleSubmission.Artifact.instruction_get]; rfl)
  have hp : CycleSubmission.Artifact.artifact.instructionPC 2087 = 2684 := by
    rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
  simpa only [hp] using h

theorem jumpDestLoop10692 : Decode.isValidJumpDest CycleSubmission.Artifact.bytecode 10692 = true := by
  have h := CycleSubmission.Global.Binding.jumpDest 8226 (by rw [CycleSubmission.Artifact.instruction_get]; rfl)
  have hp : CycleSubmission.Artifact.artifact.instructionPC 8226 = 10692 := by
    rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
  simpa only [hp] using h

theorem jumpDestLoop3711 : Decode.isValidJumpDest CycleSubmission.Artifact.bytecode 3711 = true := by
  have h := CycleSubmission.Global.Binding.jumpDest 2844 (by rw [CycleSubmission.Artifact.instruction_get]; rfl)
  have hp : CycleSubmission.Artifact.artifact.instructionPC 2844 = 3711 := by
    rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
  simpa only [hp] using h

theorem jumpDestLoop3879 : Decode.isValidJumpDest CycleSubmission.Artifact.bytecode 3879 = true := by
  have h := CycleSubmission.Global.Binding.jumpDest 2970 (by rw [CycleSubmission.Artifact.instruction_get]; rfl)
  have hp : CycleSubmission.Artifact.artifact.instructionPC 2970 = 3879 := by
    rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
  simpa only [hp] using h

theorem jumpDestLoop (mem : ByteArray) (n : Nat) :
    Decode.isValidJumpDest CycleSubmission.Artifact.bytecode (loopPC mem n) = true := by
  unfold loopPC CycleSubmission.Global.ZeroShiftMath.head
    CycleSubmission.Global.ZeroShiftMath.zeroHead CycleSubmission.Global.ZeroShiftMath.normalHead
  split_ifs
  · exact jumpDestLoop3879
  · exact jumpDestLoop3711
  · exact jumpDestLoop10692
  · exact jumpDestLoop2684

end CycleSubmission.Global.Fast.Shift
