import Challenge.Modexp.Submission.Proofs.Fast.ShiftDispatchTrace
import Challenge.Modexp.Submission.Proofs.Fast.ShiftCell0
import Challenge.Modexp.Submission.Proofs.Fast.ShiftCell1
import Challenge.Modexp.Submission.Proofs.Fast.ShiftCell2
import Challenge.Modexp.Submission.Proofs.Fast.ShiftCell3
import Challenge.Modexp.Submission.Proofs.Fast.CompactConstants
import Challenge.Modexp.Submission.Proofs.Fast.ShiftTrace1

set_option warningAsError false
set_option maxRecDepth 40000
set_option maxHeartbeats 8000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

/-!
# Block reductions of the shift-reduce base conversion, part 2

The shift loop: `u` construction, the quotient estimate, the limb pass, the
middle block, the repair rounds, the `CSUB` call and the exits.
-/

namespace Challenge.Modexp.Submission.Proofs.Fast.Shift

attribute [local simp] CompactConstants.notThirtyOne notThirtyOneOfNat
attribute [local simp] CompactConstants.notZero CompactConstants.notZeroStruct

open EvmSemantics
open EvmSemantics.EVM
open Challenge.Modexp.Submission.Proofs
open Challenge.Modexp.Submission.Proofs.Fast
open Challenge.Modexp.Submission.Proofs.Bytecode
open Challenge.Modexp.Submission.Proofs.Bytecode.ShiftPCs

@[simp] private theorem compactLoopPC2749 : Artifact.submissionArtifact.instructionPC 2791 = 3664 := by rfl
@[simp] private theorem compactLoopPC2750 : Artifact.submissionArtifact.instructionPC 2792 = 3666 := by rfl
@[simp] private theorem compactLoopPC2751 : Artifact.submissionArtifact.instructionPC 2793 = 3667 := by rfl
@[simp] private theorem compactLoopPC2752 : Artifact.submissionArtifact.instructionPC 2794 = 3670 := by rfl
@[simp] private theorem compactLoopPC2753 : Artifact.submissionArtifact.instructionPC 2795 = 3671 := by rfl
@[simp] private theorem compactLoopPC2754 : Artifact.submissionArtifact.instructionPC 2796 = 3674 := by rfl
@[simp] private theorem compactLoopPC2755 : Artifact.submissionArtifact.instructionPC 2797 = 3675 := by rfl
@[simp] private theorem compactLoopPC2756 : Artifact.submissionArtifact.instructionPC 2798 = 3678 := by rfl
@[simp] private theorem compactLoopPC2758 : Artifact.submissionArtifact.instructionPC 2803 = 3685 := by rfl
@[simp] private theorem compactLoopPC2759 : Artifact.submissionArtifact.instructionPC 2804 = 3686 := by rfl
@[simp] private theorem compactLoopPC2760 : Artifact.submissionArtifact.instructionPC 2805 = 3687 := by rfl
@[simp] private theorem compactLoopPC2761 : Artifact.submissionArtifact.instructionPC 2806 = 3688 := by rfl
@[simp] private theorem compactLoopPC2762 : Artifact.submissionArtifact.instructionPC 2807 = 3689 := by rfl
@[simp] private theorem compactLoopPC2763 : Artifact.submissionArtifact.instructionPC 2808 = 3690 := by rfl
@[simp] private theorem compactLoopPC2764 : Artifact.submissionArtifact.instructionPC 2809 = 3691 := by rfl
@[simp] private theorem compactLoopPC2765 : Artifact.submissionArtifact.instructionPC 2810 = 3692 := by rfl
@[simp] private theorem compactLoopPC2766 : Artifact.submissionArtifact.instructionPC 2811 = 3693 := by rfl
@[simp] private theorem compactLoopPC2767 : Artifact.submissionArtifact.instructionPC 2812 = 3694 := by rfl
@[simp] private theorem compactLoopPC2768 : Artifact.submissionArtifact.instructionPC 2813 = 3695 := by rfl
@[simp] private theorem compactLoopPC2769 : Artifact.submissionArtifact.instructionPC 2814 = 3696 := by rfl
@[simp] private theorem compactLoopPC2770 : Artifact.submissionArtifact.instructionPC 2815 = 3697 := by rfl
@[simp] private theorem compactLoopPC2771 : Artifact.submissionArtifact.instructionPC 2816 = 3698 := by rfl
@[simp] private theorem compactLoopPC2772 : Artifact.submissionArtifact.instructionPC 2817 = 3699 := by rfl
@[simp] private theorem compactLoopPC2773 : Artifact.submissionArtifact.instructionPC 2818 = 3700 := by rfl
@[simp] private theorem compactLoopPC2774 : Artifact.submissionArtifact.instructionPC 2819 = 3701 := by rfl
@[simp] private theorem compactLoopPC2775 : Artifact.submissionArtifact.instructionPC 2820 = 3702 := by rfl
@[simp] private theorem compactLoopPC2776 : Artifact.submissionArtifact.instructionPC 2821 = 3703 := by rfl
@[simp] private theorem compactLoopPC2777 : Artifact.submissionArtifact.instructionPC 2822 = 3704 := by rfl
@[simp] private theorem compactLoopPC2778 : Artifact.submissionArtifact.instructionPC 2823 = 3705 := by rfl
@[simp] private theorem compactLoopPC2779 : Artifact.submissionArtifact.instructionPC 2824 = 3706 := by rfl
@[simp] private theorem compactLoopPC2780 : Artifact.submissionArtifact.instructionPC 2825 = 3707 := by rfl
@[simp] private theorem compactLoopPC2781 : Artifact.submissionArtifact.instructionPC 2826 = 3708 := by rfl
@[simp] private theorem compactLoopPC2782 : Artifact.submissionArtifact.instructionPC 2827 = 3709 := by rfl
@[simp] private theorem compactLoopPC2783 : Artifact.submissionArtifact.instructionPC 2828 = 3710 := by rfl
@[simp] private theorem compactLoopPC2784 : Artifact.submissionArtifact.instructionPC 2829 = 3711 := by rfl
@[simp] private theorem compactLoopPC2785 : Artifact.submissionArtifact.instructionPC 2830 = 3712 := by rfl
@[simp] private theorem compactLoopPC2786 : Artifact.submissionArtifact.instructionPC 2831 = 3713 := by rfl
@[simp] private theorem compactLoopPC2787 : Artifact.submissionArtifact.instructionPC 2832 = 3714 := by rfl
@[simp] private theorem compactLoopPC2788 : Artifact.submissionArtifact.instructionPC 2833 = 3715 := by rfl
@[simp] private theorem compactLoopPC2789 : Artifact.submissionArtifact.instructionPC 2834 = 3716 := by rfl
@[simp] private theorem compactLoopPC2790 : Artifact.submissionArtifact.instructionPC 2835 = 3717 := by rfl
@[simp] private theorem compactLoopPC2791 : Artifact.submissionArtifact.instructionPC 2836 = 3718 := by rfl
@[simp] private theorem compactLoopPC2792 : Artifact.submissionArtifact.instructionPC 2837 = 3719 := by rfl
@[simp] private theorem compactLoopPC2793 : Artifact.submissionArtifact.instructionPC 2838 = 3720 := by rfl
@[simp] private theorem compactLoopPC2794 : Artifact.submissionArtifact.instructionPC 2839 = 3721 := by rfl
@[simp] private theorem compactLoopPC2795 : Artifact.submissionArtifact.instructionPC 2840 = 3722 := by rfl
@[simp] private theorem compactLoopPC2797 : Artifact.submissionArtifact.instructionPC 2959 = 3843 := by rfl
@[simp] private theorem compactLoopPC2798 : Artifact.submissionArtifact.instructionPC 2960 = 3844 := by rfl
@[simp] private theorem compactLoopPC2799 : Artifact.submissionArtifact.instructionPC 2961 = 3845 := by rfl
@[simp] private theorem compactLoopPC2800 : Artifact.submissionArtifact.instructionPC 2962 = 3848 := by rfl
@[simp] private theorem compactLoopPC2803 : Artifact.submissionArtifact.instructionPC 2965 = 3851 := by rfl

/-- `blk3013` with steps to go: fall into the body. -/
theorem run_shiftHead_go (s : State) (mem : ByteArray) (n bsize esize msize k : Nat)
    (hk : k ≠ 0) (hk32 : k ≤ 32)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hrun : s.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock blk3013
      (shiftLoopState s mem n bsize esize msize k) =
      some (shiftBodyState s mem n bsize esize msize k) := by
  have hkmod : k % 115792089237316195423570985008687907853269984665640564039457584007913129639936
      = k := Nat.mod_eq_of_lt (by omega)
  simp (config := { maxSteps := 200000 })
    [blk3013, opAt, pushAt, wfOp,
      Challenge.EvmProof.Stepper.runLocatedBlock,
      Challenge.EvmProof.Stepper.runLocated,
      Challenge.EvmProof.Stepper.runInstr,
      shiftLoopState, shiftBodyState, kState, pcShiftLoop, pcShiftBody,
      outer, Exp.outer, hcode, hrun, hk, hkmod, UInt256.isZero, UInt256.isTrue,
      Challenge.EvmProof.Word.literal_eq_ofNat,
      Challenge.EvmProof.Word.word_toNat_ofNat,
      Challenge.EvmProof.Word.succ_ofNat_mod,
      Challenge.EvmProof.Word.ofNat_add_mod, jumpDest5366]

/-- `blk3013` with no steps to go: jump to `SHIFT_DONE`. -/
theorem run_shiftHead_done (s : State) (mem : ByteArray) (n bsize esize msize : Nat)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hrun : s.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock blk3013
      (shiftLoopState s mem n bsize esize msize 0) =
      some (shiftDoneState s mem n bsize esize msize) := by
  simp (config := { maxSteps := 200000 })
    [blk3013, opAt, pushAt, wfOp,
      Challenge.EvmProof.Stepper.runLocatedBlock,
      Challenge.EvmProof.Stepper.runLocated,
      Challenge.EvmProof.Stepper.runInstr,
      shiftLoopState, shiftDoneState, kState, pcShiftLoop, pcShiftDone,
      outer, Exp.outer, hcode, hrun, jumpDest5366, UInt256.isZero, UInt256.isTrue,
      Challenge.EvmProof.Word.literal_eq_ofNat,
      Challenge.EvmProof.Word.word_toNat_ofNat,
      Challenge.EvmProof.Word.succ_ofNat_mod,
      Challenge.EvmProof.Word.ofNat_add_mod]

/-- `blk3018`: `MCOPY(TN, BASE, s32)` and `t[0] := 0`. -/
theorem run_shiftBody (s : State) (mem : ByteArray) (n bsize esize msize k : Nat)
    (hn : 2 ≤ n) (hn32 : n ≤ 32) (hact : 298 ≤ s.activeWords.toNat)
    (htl : MachineState.readWord mem 9440 = UInt256.ofNat (8224 + 32 * n))
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hrun : s.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock blk3018
      (shiftBodyState s mem n bsize esize msize k) =
      some (estimateState s mem n bsize esize msize k) := by
  have hmod : (32 * n) %
      115792089237316195423570985008687907853269984665640564039457584007913129639936
      = 32 * n := Exp.mod_word_self (Nat.lt_of_le_of_lt (show 32 * n ≤ 1024 by omega) (by norm_num))
  have hfix2 : UInt256.ofNat (MachineState.activeWordsAfter
      (MachineState.activeWordsAfter s.activeWords.toNat 8224 (32 * n)) 2048
      (32 * n)) = s.activeWords :=
    Exp.activeWords_fix2 s 8224 (32 * n) 2048 (32 * n) (by omega) (by omega) (by omega)
      (by omega) hact
  have hfixTL : UInt256.ofNat (MachineState.activeWordsAfter s.activeWords.toNat 9440 32) =
      s.activeWords := Monpro.activeWords_fix s _ 32 (by decide) (by omega) (by omega)
  have hfixT0 : UInt256.ofNat (MachineState.activeWordsAfter s.activeWords.toNat
      (8224 + 32 * n) 32) = s.activeWords :=
    Monpro.activeWords_fix s _ 32 (by decide) (by omega) (by omega)
  have htl' : MachineState.readWord
      (MachineState.writeBytes mem (MachineState.readPadded mem 2048 (32 * n)) 8224) 9440 =
      UInt256.ofNat (8224 + 32 * n) := by
    rw [show MachineState.writeBytes mem (MachineState.readPadded mem 2048 (32 * n)) 8224 =
      Exp.mcopyMem mem 8224 2048 (32 * n) from rfl]
    rw [Exp.readWord_mcopyMem_disjoint mem 8224 2048 (32 * n) 9440 (Or.inr (by omega))]
    exact htl
  have hmodTL : (8224 + 32 * n) %
      115792089237316195423570985008687907853269984665640564039457584007913129639936
      = 8224 + 32 * n := Nat.mod_eq_of_lt (by omega)
  simp (config := { maxSteps := 400000 })
    [blk3018, opAt, pushAt, wfOp,
      Challenge.EvmProof.Stepper.runLocatedBlock,
      Challenge.EvmProof.Stepper.runLocated,
      Challenge.EvmProof.Stepper.runInstr,
      shiftBodyState, estimateState, kState, pcShiftBody, pcEstimate, uMem,
      Exp.mcopyMem, Exp.storeWord, outer, Exp.outer, hcode, hrun, hmod, hfix2, hfixTL,
      hfixT0, htl', hmodTL, Exp.push0_word,
      State.activeWordsAfterUInt256, State.activeWordsAfterUInt256_2,
      Challenge.EvmProof.Word.literal_eq_ofNat,
      Challenge.EvmProof.Word.word_toNat_ofNat,
      Challenge.EvmProof.Word.succ_ofNat_mod,
      Challenge.EvmProof.Word.ofNat_add_mod]

/-- Generic word identity; the quotient clamp itself is unchanged. -/
private theorem saturation_gt_eq_lt (a b : UInt256) : UInt256.gt a b = UInt256.lt b a := by
  rfl

private theorem ofNat_zero_lt_eq_double_isZero (x : UInt256) :
    UInt256.lt (UInt256.ofNat 0) x = UInt256.isZero (UInt256.isZero x) :=
  Monpro.zero_lt_eq_double_isZero x

private theorem addMod_comm (a b m : UInt256) :
    UInt256.addMod a b m = UInt256.addMod b a m := by
  simp only [UInt256.addMod, Nat.add_comm]

@[simp] private theorem newEstimatePC2960 : Artifact.submissionArtifact.instructionPC 2765 = 3631 := by rfl
@[simp] private theorem newEstimatePC2961 : Artifact.submissionArtifact.instructionPC 2766 = 3632 := by rfl
@[simp] private theorem newEstimatePC2962 : Artifact.submissionArtifact.instructionPC 2767 = 3633 := by rfl
@[simp] private theorem newEstimatePC2963 : Artifact.submissionArtifact.instructionPC 2768 = 3634 := by rfl
@[simp] private theorem newEstimatePC2964 : Artifact.submissionArtifact.instructionPC 2769 = 3637 := by rfl
@[simp] private theorem newEstimatePC2965 : Artifact.submissionArtifact.instructionPC 2770 = 3638 := by rfl
@[simp] private theorem newEstimatePC2966 : Artifact.submissionArtifact.instructionPC 2771 = 3639 := by rfl
@[simp] private theorem newEstimatePC2967 : Artifact.submissionArtifact.instructionPC 2772 = 3641 := by rfl
@[simp] private theorem newEstimatePCk2750 : Artifact.submissionArtifact.instructionPC 2773 = 3642 := by rfl
@[simp] private theorem newEstimatePCk2751 : Artifact.submissionArtifact.instructionPC 2774 = 3644 := by rfl
@[simp] private theorem newEstimatePCk2752 : Artifact.submissionArtifact.instructionPC 2775 = 3645 := by rfl
@[simp] private theorem newEstimatePCk2753 : Artifact.submissionArtifact.instructionPC 2776 = 3646 := by rfl
@[simp] private theorem newEstimatePCk2754 : Artifact.submissionArtifact.instructionPC 2777 = 3648 := by rfl
@[simp] private theorem newEstimatePCk2755 : Artifact.submissionArtifact.instructionPC 2778 = 3649 := by rfl
@[simp] private theorem newEstimatePCk2756 : Artifact.submissionArtifact.instructionPC 2779 = 3650 := by rfl
@[simp] private theorem newEstimatePCk2757 : Artifact.submissionArtifact.instructionPC 2780 = 3651 := by rfl
@[simp] private theorem newEstimatePCk2758 : Artifact.submissionArtifact.instructionPC 2781 = 3652 := by rfl

/-- `blk3026`: quotient estimate with a branchless saturation mask. -/
theorem run_estimate (s : State) (mem : ByteArray) (n bsize esize msize k : Nat)
    (hact : 296 ≤ s.activeWords.toNat)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hrun : s.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock blk3026
      (estimateState s mem n bsize esize msize k) =
      some (macSetupState s mem n bsize esize msize k) := by
  have hA : UInt256.ofNat (MachineState.activeWordsAfter s.activeWords.toNat 2048 32) =
      s.activeWords := Monpro.activeWords_fix s _ 32 (by decide) (by omega) hact
  have hB : UInt256.ofNat (MachineState.activeWordsAfter s.activeWords.toNat 6144 32) =
      s.activeWords := Monpro.activeWords_fix s _ 32 (by decide) (by omega) hact
  have hC : UInt256.ofNat (MachineState.activeWordsAfter s.activeWords.toNat 6208 32) =
      s.activeWords := Monpro.activeWords_fix s _ 32 (by decide) (by omega) hact
  have hD : UInt256.ofNat (MachineState.activeWordsAfter s.activeWords.toNat 2080 32) =
      s.activeWords := Monpro.activeWords_fix s _ 32 (by decide) (by omega) hact
  have hE : UInt256.ofNat (MachineState.activeWordsAfter s.activeWords.toNat 6176 32) =
      s.activeWords := Monpro.activeWords_fix s _ 32 (by decide) (by omega) hact
  have hF : UInt256.ofNat (MachineState.activeWordsAfter s.activeWords.toNat 6240 32) =
      s.activeWords := Monpro.activeWords_fix s _ 32 (by decide) (by omega) hact
  have hG : UInt256.ofNat (MachineState.activeWordsAfter s.activeWords.toNat 6272 32) =
      s.activeWords := Monpro.activeWords_fix s _ 32 (by decide) (by omega) hact
  have hH : UInt256.ofNat (MachineState.activeWordsAfter s.activeWords.toNat 0 32) =
      s.activeWords := Monpro.activeWords_fix s _ 32 (by decide) (by omega) hact
  have hI : UInt256.ofNat (MachineState.activeWordsAfter s.activeWords.toNat 32 32) =
      s.activeWords := Monpro.activeWords_fix s _ 32 (by decide) (by omega) hact
  simp (config := { maxSteps := 600000 })
    [blk3026, opAt, pushAt, wfOp,
      Challenge.EvmProof.Stepper.runLocatedBlock,
      Challenge.EvmProof.Stepper.runLocated,
      Challenge.EvmProof.Stepper.runInstr,
      estimateState, macSetupState, kState, pcEstimate, pcMacSetup, qhatOf,
      PRE_L, PRE_DODD, PRE_X, PRE_BMOD, PRE_DINV,
      outer, Exp.outer, hcode, hrun, hA, hB, hC, hD, hE, hF, hG, hH, hI, Exp.push0_word, ofNat_zero_lt_eq_double_isZero,
      State.activeWordsAfterUInt256,
      Challenge.EvmProof.Word.literal_eq_ofNat,
      Challenge.EvmProof.Word.word_toNat_ofNat,
      Challenge.EvmProof.Word.succ_ofNat_mod,
      Challenge.EvmProof.Word.ofNat_add_mod, List.exchange, saturation_gt_eq_lt, addMod_comm]

/-- `blk3069`: the limb-pass frame `[paj, ptj, 0, q]`. -/
theorem run_macSetup (s : State) (mem : ByteArray) (n bsize esize msize k : Nat)
    (hn : 1 ≤ n) (hn32 : n ≤ 32) (hact : 296 ≤ s.activeWords.toNat)
    (htl : MachineState.readWord (uMem mem n) 9440 = UInt256.ofNat (8224 + 32 * n))
    (hml : MachineState.readWord (uMem mem n) 9408 = UInt256.ofNat (32 * n - 32))
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hrun : s.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock blk3069
      (macSetupState s mem n bsize esize msize k) =
      some (macDispatchState s (uMem mem n) (qhatOf (uMem mem n)) n bsize esize msize k) := by
  have hTL : UInt256.ofNat (MachineState.activeWordsAfter s.activeWords.toNat 9440 32) =
      s.activeWords := Monpro.activeWords_fix s _ 32 (by decide) (by omega) hact
  have hML : UInt256.ofNat (MachineState.activeWordsAfter s.activeWords.toNat 9408 32) =
      s.activeWords := Monpro.activeWords_fix s _ 32 (by decide) (by omega) hact
  have hpa : UInt256.ofNat (5120 + (32 * n - 32)) = UInt256.ofNat (NEG + 32 * n - 32) := by
    unfold NEG; congr 1; omega
  simp (config := { maxSteps := 300000 })
    [blk3069, opAt, pushAt, wfOp,
      Challenge.EvmProof.Stepper.runLocatedBlock,
      Challenge.EvmProof.Stepper.runLocated,
      Challenge.EvmProof.Stepper.runInstr,
      macSetupState, macDispatchState, macLoopState, pcMacSetup, pcMacLoop, Monpro.l1Step,
      outer, Exp.outer, hcode, hrun, htl, hml, hTL, hML, Exp.push0_word, hpa,
      State.activeWordsAfterUInt256,
      Challenge.EvmProof.Word.literal_eq_ofNat,
      Challenge.EvmProof.Word.word_toNat_ofNat,
      Challenge.EvmProof.Word.succ_ofNat_mod,
      Challenge.EvmProof.Word.ofNat_add_mod]
  all_goals (try (congr 1; unfold NEG; omega))

/-- `blk3077b` with limbs to go: back to the loop head. -/
theorem run_macTail_go (s : State) (mm : ByteArray) (pa pt c q : UInt256)
    (n bsize esize msize k : Nat) (hgt : 8224 < pt.toNat)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hrun : s.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock blk3077b
      { s with pc := UInt256.ofNat pcMacTail
               stack := pa :: pt :: UInt256.ofNat 115792089237316195423570985008687907853269984665640564039457584007913129639904 :: c :: q :: UInt256.ofNat k :: outer n bsize esize msize
               memory := mm } =
      some { s with pc := UInt256.ofNat pcMacLoop
                    stack := pa :: pt :: UInt256.ofNat 115792089237316195423570985008687907853269984665640564039457584007913129639904 :: c :: q :: UInt256.ofNat k :: outer n bsize esize msize
                    memory := mm } := by
  simp (config := { maxSteps := 200000 })
    [blk3077b, opAt, pushAt, wfOp,
      Challenge.EvmProof.Stepper.runLocatedBlock,
      Challenge.EvmProof.Stepper.runLocated,
      Challenge.EvmProof.Stepper.runInstr,
      pcMacTail, pcMacLoop, outer, Exp.outer, hcode, hrun, hgt, jumpDest4933,
      UInt256.gt, UInt256.isTrue,
      Challenge.EvmProof.Word.literal_eq_ofNat,
      Challenge.EvmProof.Word.word_toNat_ofNat,
      Challenge.EvmProof.Word.succ_ofNat_mod,
      Challenge.EvmProof.Word.ofNat_add_mod, Nat.mod_eq_of_lt]

/-- `blk3077b` after the last limb: fall through into the middle block. -/
theorem run_macTail_exit (s : State) (mm : ByteArray) (pa pt c q : UInt256)
    (n bsize esize msize k : Nat) (hpt : pt.toNat = 8224)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hrun : s.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock blk3077b
      { s with pc := UInt256.ofNat pcMacTail
               stack := pa :: pt :: UInt256.ofNat 115792089237316195423570985008687907853269984665640564039457584007913129639904 :: c :: q :: UInt256.ofNat k :: outer n bsize esize msize
               memory := mm } =
      some { s with pc := UInt256.ofNat pcMid
                    stack := pa :: pt :: UInt256.ofNat 115792089237316195423570985008687907853269984665640564039457584007913129639904 :: c :: q :: UInt256.ofNat k :: outer n bsize esize msize
                    memory := mm } := by
  simp (config := { maxSteps := 200000 })
    [blk3077b, opAt, pushAt, wfOp,
      Challenge.EvmProof.Stepper.runLocatedBlock,
      Challenge.EvmProof.Stepper.runLocated,
      Challenge.EvmProof.Stepper.runInstr,
      pcMacTail, pcMid, outer, Exp.outer, hcode, hrun, hpt, jumpDest4933,
      UInt256.gt, UInt256.isTrue,
      Challenge.EvmProof.Word.literal_eq_ofNat,
      Challenge.EvmProof.Word.word_toNat_ofNat,
      Challenge.EvmProof.Word.succ_ofNat_mod,
      Challenge.EvmProof.Word.ofNat_add_mod, Nat.mod_eq_of_lt]

end Challenge.Modexp.Submission.Proofs.Fast.Shift
