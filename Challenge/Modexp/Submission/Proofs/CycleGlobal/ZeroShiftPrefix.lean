import Challenge.Modexp.Submission.Proofs.CycleGlobal.ShiftTrace2
import Challenge.Modexp.Submission.Proofs.CycleGlobal.ZeroRemainderMath
import Challenge.Modexp.Submission.Proofs.CycleGlobal.ZeroShiftWords
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
open CycleSubmission.Global.ZeroShiftMath
open CycleSubmission.Global.ZeroRemainderMath
abbrev zeroJoinState := estimate40
@[simp] theorem rhoPC2142 : CycleSubmission.Artifact.artifact.instructionPC 2142 = 2760 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem rhoPC2854 : CycleSubmission.Artifact.artifact.instructionPC 2854 = 3719 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem rhoPC2855 : CycleSubmission.Artifact.artifact.instructionPC 2855 = 3720 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem rhoPC2856 : CycleSubmission.Artifact.artifact.instructionPC 2856 = 3723 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem rhoPC2857 : CycleSubmission.Artifact.artifact.instructionPC 2857 = 3726 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem rhoPC2858 : CycleSubmission.Artifact.artifact.instructionPC 2858 = 3729 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem rhoPC2859 : CycleSubmission.Artifact.artifact.instructionPC 2859 = 3730 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem rhoPC2860 : CycleSubmission.Artifact.artifact.instructionPC 2860 = 3733 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem rhoPC2861 : CycleSubmission.Artifact.artifact.instructionPC 2861 = 3734 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem rhoPC2862 : CycleSubmission.Artifact.artifact.instructionPC 2862 = 3737 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem rhoPC2863 : CycleSubmission.Artifact.artifact.instructionPC 2863 = 3738 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem rhoPC2864 : CycleSubmission.Artifact.artifact.instructionPC 2864 = 3739 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem rhoPC2865 : CycleSubmission.Artifact.artifact.instructionPC 2865 = 3740 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem rhoPC2866 : CycleSubmission.Artifact.artifact.instructionPC 2866 = 3741 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem rhoPC2867 : CycleSubmission.Artifact.artifact.instructionPC 2867 = 3742 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem rhoPC2868 : CycleSubmission.Artifact.artifact.instructionPC 2868 = 3743 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem rhoPC2869 : CycleSubmission.Artifact.artifact.instructionPC 2869 = 3744 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem rhoPC2870 : CycleSubmission.Artifact.artifact.instructionPC 2870 = 3745 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem rhoPC2871 : CycleSubmission.Artifact.artifact.instructionPC 2871 = 3746 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem rhoPC2872 : CycleSubmission.Artifact.artifact.instructionPC 2872 = 3747 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem rhoPC2873 : CycleSubmission.Artifact.artifact.instructionPC 2873 = 3748 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem rhoPC2874 : CycleSubmission.Artifact.artifact.instructionPC 2874 = 3749 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem rhoPC2875 : CycleSubmission.Artifact.artifact.instructionPC 2875 = 3750 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem rhoPC2876 : CycleSubmission.Artifact.artifact.instructionPC 2876 = 3751 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem rhoPC2877 : CycleSubmission.Artifact.artifact.instructionPC 2877 = 3752 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem rhoPC2878 : CycleSubmission.Artifact.artifact.instructionPC 2878 = 3754 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem rhoPC2879 : CycleSubmission.Artifact.artifact.instructionPC 2879 = 3755 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem rhoPC2880 : CycleSubmission.Artifact.artifact.instructionPC 2880 = 3756 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem rhoPC2881 : CycleSubmission.Artifact.artifact.instructionPC 2881 = 3757 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem rhoPC2882 : CycleSubmission.Artifact.artifact.instructionPC 2882 = 3758 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem rhoPC2883 : CycleSubmission.Artifact.artifact.instructionPC 2883 = 3759 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem rhoPC2884 : CycleSubmission.Artifact.artifact.instructionPC 2884 = 3760 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem rhoPC2885 : CycleSubmission.Artifact.artifact.instructionPC 2885 = 3761 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem rhoPC2886 : CycleSubmission.Artifact.artifact.instructionPC 2886 = 3764 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem rhoPC3002 : CycleSubmission.Artifact.artifact.instructionPC 3002 = 3899 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem rhoPC3003 : CycleSubmission.Artifact.artifact.instructionPC 3003 = 3900 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem rhoPC3004 : CycleSubmission.Artifact.artifact.instructionPC 3004 = 3902 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem rhoPC3005 : CycleSubmission.Artifact.artifact.instructionPC 3005 = 3905 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem rhoPC3006 : CycleSubmission.Artifact.artifact.instructionPC 3006 = 3908 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem rhoPC3007 : CycleSubmission.Artifact.artifact.instructionPC 3007 = 3909 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem rhoPC3008 : CycleSubmission.Artifact.artifact.instructionPC 3008 = 3912 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem rhoPC3009 : CycleSubmission.Artifact.artifact.instructionPC 3009 = 3913 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem rhoPC3010 : CycleSubmission.Artifact.artifact.instructionPC 3010 = 3916 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem rhoPC3011 : CycleSubmission.Artifact.artifact.instructionPC 3011 = 3917 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem rhoPC3012 : CycleSubmission.Artifact.artifact.instructionPC 3012 = 3918 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem rhoPC3013 : CycleSubmission.Artifact.artifact.instructionPC 3013 = 3919 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem rhoPC3014 : CycleSubmission.Artifact.artifact.instructionPC 3014 = 3920 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem rhoPC3015 : CycleSubmission.Artifact.artifact.instructionPC 3015 = 3921 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem rhoPC3016 : CycleSubmission.Artifact.artifact.instructionPC 3016 = 3922 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem rhoPC3017 : CycleSubmission.Artifact.artifact.instructionPC 3017 = 3923 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem rhoPC3018 : CycleSubmission.Artifact.artifact.instructionPC 3018 = 3924 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem rhoPC3019 : CycleSubmission.Artifact.artifact.instructionPC 3019 = 3925 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem rhoPC3020 : CycleSubmission.Artifact.artifact.instructionPC 3020 = 3926 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem rhoPC3021 : CycleSubmission.Artifact.artifact.instructionPC 3021 = 3927 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem rhoPC3022 : CycleSubmission.Artifact.artifact.instructionPC 3022 = 3928 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem rhoPC3023 : CycleSubmission.Artifact.artifact.instructionPC 3023 = 3929 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem rhoPC3024 : CycleSubmission.Artifact.artifact.instructionPC 3024 = 3930 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem rhoPC3025 : CycleSubmission.Artifact.artifact.instructionPC 3025 = 3931 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem rhoPC3026 : CycleSubmission.Artifact.artifact.instructionPC 3026 = 3933 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem rhoPC3027 : CycleSubmission.Artifact.artifact.instructionPC 3027 = 3934 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem rhoPC3028 : CycleSubmission.Artifact.artifact.instructionPC 3028 = 3935 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem rhoPC3029 : CycleSubmission.Artifact.artifact.instructionPC 3029 = 3936 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem rhoPC3030 : CycleSubmission.Artifact.artifact.instructionPC 3030 = 3937 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem rhoPC3031 : CycleSubmission.Artifact.artifact.instructionPC 3031 = 3938 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem rhoPC3032 : CycleSubmission.Artifact.artifact.instructionPC 3032 = 3939 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem rhoPC3033 : CycleSubmission.Artifact.artifact.instructionPC 3033 = 3940 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem rhoPC3034 : CycleSubmission.Artifact.artifact.instructionPC 3034 = 3943 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
@[simp] theorem rhoPC8318 : CycleSubmission.Artifact.artifact.instructionPC 8318 = 10783 := by
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
theorem jumpDestZeroJoin8 : Decode.isValidJumpDest CycleSubmission.Artifact.bytecode 2760 = true := by
  have h := CycleSubmission.Global.Binding.jumpDest 2142 (by rw [CycleSubmission.Artifact.instruction_get]; rfl)
  simpa only [rhoPC2142] using h
theorem run_zeroPrefix8 (z : UInt256) (s : State) (mem : ByteArray)
    (n bsize esize msize k : Nat) (hn : n = 8)
    (hpre : PreOK mem) (hd : (MachineState.readWord mem 0).toNat ≠ 0)
    (hshift : (MachineState.readWord mem 1536).toNat = 0)
    (hbs : bsize = 32*n) (hact : 88 ≤ s.activeWords.toNat)
    (hcode : s.executionEnv.code = CycleSubmission.Artifact.bytecode)
    (hrun : s.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock blkZero8
      (shiftLoopState z s mem n bsize esize msize k) =
      some (zeroJoinState z s mem n bsize esize msize k) := by
  have hkw : MachineState.readWord mem 1536 = UInt256.ofNat 0 := by
    apply Challenge.EvmProof.Word.word_ext
    exact hshift
  have hsw := zero_complement mem hpre hd hkw
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
  have hkU : MachineState.readWord (uMem mem n) 1536 = UInt256.ofNat 0 := hu1536.trans hkw
  have hxU : MachineState.readWord (uMem mem n) 1600 = UInt256.ofNat 256 :=
    (huv 1600 (by omega)).trans hsw
  have hpreU := PreOK_uMem mem n (by omega) hpre
  have hdU : (MachineState.readWord (uMem mem n) 0).toNat ≠ 0 := by
    rw [huv 0 (by omega)]; exact hd
  have hinv := (divisor_and_inverse (uMem mem n) hpreU hdU hkU).2
  let rho := UInt256.addMod (MachineState.readWord (uMem mem n) 2112)
    (UInt256.mulMod (MachineState.readWord (uMem mem n) 2080)
      (MachineState.readWord (uMem mem n) 1632) (MachineState.readWord (uMem mem n) 1568))
    (MachineState.readWord (uMem mem n) 1568)
  have hres := residual (MachineState.readWord (uMem mem n) 0)
    (MachineState.readWord (uMem mem n) 1664)
    (MachineState.readWord (uMem mem n) 2112) rho hinv
  have hu0 := huv 0 (by omega)
  dsimp only [rho] at hres
  simp only [← hr2080, ← hr2112, hu0, hu1664, hu1632, hu1568] at hres
  subst n
  simp (config := {maxSteps := 900000})
    [blkZero8, zeroJoinState, estimate40, shiftLoopState, slotKState, entrySlots, aprevSlot, hdSlot,
      headWord, loopPC, headPC, opAt, pushAt, wfOp, hshift, hkw, hsw,
      CycleSubmission.Global.ZeroShiftMath.head, CycleSubmission.Global.ZeroShiftMath.zeroHead,
      CycleSubmission.Global.ZeroShiftMath.normalHead,
      Challenge.EvmProof.Stepper.runLocatedBlock, Challenge.EvmProof.Stepper.runLocated,
      Challenge.EvmProof.Stepper.runInstr, hcode, hrun, hbs,
      outer, Exp.outer, uMem0, Exp.mcopyMem,
      State.activeWordsAfterUInt256, State.activeWordsAfterUInt256_2,
      hfix, h2080, h2112, hr2080, hr2112,
      hu1312, hu1344, hu1376, hu1408, hu1440, hu1472, hu1504, hu1632, hu1664, hu1568, hu1536, hu32,
      hkU, hxU, shr_zero, shl_256, add_ofNat_zero,
      jumpDestZeroJoin8, Challenge.EvmProof.Word.literal_eq_ofNat,
      Challenge.EvmProof.Word.word_toNat_ofNat, Challenge.EvmProof.Word.succ_ofNat_mod,
      Challenge.EvmProof.Word.ofNat_add_mod, List.exchange, CycleSubmission.Prepared.Arithmetic.amC,
      CycleSubmission.Prepared.Arithmetic.mulC, rho] at hres ⊢
  simp only [← hr2080, ← hr2112, hu0, uMem0, Exp.mcopyMem, hres]
  trivial
#print axioms run_zeroPrefix8
theorem jumpDestZeroJoin4 : Decode.isValidJumpDest CycleSubmission.Artifact.bytecode 10783 = true := by
  have h := CycleSubmission.Global.Binding.jumpDest 8318 (by rw [CycleSubmission.Artifact.instruction_get]; rfl)
  simpa only [rhoPC8318] using h
theorem run_zeroPrefix4 (z : UInt256) (s : State) (mem : ByteArray)
    (n bsize esize msize k : Nat) (hn : n = 4)
    (hpre : PreOK mem) (hd : (MachineState.readWord mem 0).toNat ≠ 0)
    (hshift : (MachineState.readWord mem 1536).toNat = 0)
    (hbs : bsize = 32*n) (hact : 88 ≤ s.activeWords.toNat)
    (hcode : s.executionEnv.code = CycleSubmission.Artifact.bytecode)
    (hrun : s.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock blkZero4
      (shiftLoopState z s mem n bsize esize msize k) =
      some (zeroJoinState z s mem n bsize esize msize k) := by
  have hkw : MachineState.readWord mem 1536 = UInt256.ofNat 0 := by
    apply Challenge.EvmProof.Word.word_ext
    exact hshift
  have hsw := zero_complement mem hpre hd hkw
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
  have hkU : MachineState.readWord (uMem mem n) 1536 = UInt256.ofNat 0 := hu1536.trans hkw
  have hxU : MachineState.readWord (uMem mem n) 1600 = UInt256.ofNat 256 :=
    (huv 1600 (by omega)).trans hsw
  have hpreU := PreOK_uMem mem n (by omega) hpre
  have hdU : (MachineState.readWord (uMem mem n) 0).toNat ≠ 0 := by
    rw [huv 0 (by omega)]; exact hd
  have hinv := (divisor_and_inverse (uMem mem n) hpreU hdU hkU).2
  let rho := UInt256.addMod (MachineState.readWord (uMem mem n) 2112)
    (UInt256.mulMod (MachineState.readWord (uMem mem n) 2080)
      (MachineState.readWord (uMem mem n) 1632) (MachineState.readWord (uMem mem n) 1568))
    (MachineState.readWord (uMem mem n) 1568)
  have hres := residual (MachineState.readWord (uMem mem n) 0)
    (MachineState.readWord (uMem mem n) 1664)
    (MachineState.readWord (uMem mem n) 2112) rho hinv
  have hu0 := huv 0 (by omega)
  dsimp only [rho] at hres
  simp only [← hr2080, ← hr2112, hu0, hu1664, hu1632, hu1568] at hres
  subst n
  simp (config := {maxSteps := 900000})
    [blkZero4, zeroJoinState, estimate40, shiftLoopState, slotKState, entrySlots, aprevSlot, hdSlot,
      headWord, loopPC, headPC, opAt, pushAt, wfOp, hshift, hkw, hsw,
      CycleSubmission.Global.ZeroShiftMath.head, CycleSubmission.Global.ZeroShiftMath.zeroHead,
      CycleSubmission.Global.ZeroShiftMath.normalHead,
      Challenge.EvmProof.Stepper.runLocatedBlock, Challenge.EvmProof.Stepper.runLocated,
      Challenge.EvmProof.Stepper.runInstr, hcode, hrun, hbs,
      outer, Exp.outer, uMem0, Exp.mcopyMem,
      State.activeWordsAfterUInt256, State.activeWordsAfterUInt256_2,
      hfix, h2080, h2112, hr2080, hr2112,
      hu1312, hu1344, hu1376, hu1408, hu1440, hu1472, hu1504, hu1632, hu1664, hu1568, hu1536, hu32,
      hkU, hxU, shr_zero, shl_256, add_ofNat_zero,
      jumpDestZeroJoin4, Challenge.EvmProof.Word.literal_eq_ofNat,
      Challenge.EvmProof.Word.word_toNat_ofNat, Challenge.EvmProof.Word.succ_ofNat_mod,
      Challenge.EvmProof.Word.ofNat_add_mod, List.exchange, CycleSubmission.Prepared.Arithmetic.amC,
      CycleSubmission.Prepared.Arithmetic.mulC, rho] at hres ⊢
  simp only [← hr2080, ← hr2112, hu0, uMem0, Exp.mcopyMem, hres]
  trivial
#print axioms run_zeroPrefix4
theorem jumpDestLoop2684 : Decode.isValidJumpDest CycleSubmission.Artifact.bytecode 2700 = true := by
  have h := CycleSubmission.Global.Binding.jumpDest 2097 (by rw [CycleSubmission.Artifact.instruction_get]; rfl)
  have hp : CycleSubmission.Artifact.artifact.instructionPC 2097 = 2700 := by
    rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
  simpa only [hp] using h
theorem jumpDestLoop10692 : Decode.isValidJumpDest CycleSubmission.Artifact.bytecode 10724 = true := by
  have h := CycleSubmission.Global.Binding.jumpDest 8273 (by rw [CycleSubmission.Artifact.instruction_get]; rfl)
  have hp : CycleSubmission.Artifact.artifact.instructionPC 8273 = 10724 := by
    rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
  simpa only [hp] using h
theorem jumpDestLoop3711 : Decode.isValidJumpDest CycleSubmission.Artifact.bytecode 3719 = true := by
  have h := CycleSubmission.Global.Binding.jumpDest 2854 (by rw [CycleSubmission.Artifact.instruction_get]; rfl)
  have hp : CycleSubmission.Artifact.artifact.instructionPC 2854 = 3719 := by
    rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
  simpa only [hp] using h
theorem jumpDestLoop3879 : Decode.isValidJumpDest CycleSubmission.Artifact.bytecode 3899 = true := by
  have h := CycleSubmission.Global.Binding.jumpDest 3002 (by rw [CycleSubmission.Artifact.instruction_get]; rfl)
  have hp : CycleSubmission.Artifact.artifact.instructionPC 3002 = 3899 := by
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
