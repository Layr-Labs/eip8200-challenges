import Challenge.Modexp.Submission.Proofs.Fast.ShiftBlocks
import Challenge.Modexp.Submission.Proofs.Fast.ShiftStates
import Challenge.Modexp.Submission.Proofs.Fast.CompactConstants
import Challenge.Modexp.Submission.Proofs.Bytecode.ShiftPCs

set_option warningAsError false
set_option maxRecDepth 40000
set_option maxHeartbeats 8000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace Challenge.Modexp.Submission.Proofs.Fast.ShiftCell1
open EvmSemantics EvmSemantics.EVM
open Challenge.Modexp.Submission.Proofs
open Challenge.Modexp.Submission.Proofs.Fast Shift
open Challenge.Modexp.Submission.Proofs.Bytecode
open Challenge.Modexp.Submission.Proofs.Bytecode.ShiftPCs
private theorem notThirtyOneOfNat : UInt256.lnot (UInt256.ofNat 31) = UInt256.ofNat
    115792089237316195423570985008687907853269984665640564039457584007913129639904 := by
  decide
attribute [local simp] CompactConstants.notThirtyOne notThirtyOneOfNat
attribute [local simp] CompactConstants.notZero CompactConstants.notZeroStruct

@[simp] private theorem compactLoopPC2749 : Artifact.submissionArtifact.instructionPC 2791 = 3664 := by rfl
@[simp] private theorem compactLoopPC2750 : Artifact.submissionArtifact.instructionPC 2792 = 3666 := by rfl
@[simp] private theorem compactLoopPC2751 : Artifact.submissionArtifact.instructionPC 2793 = 3667 := by rfl
@[simp] private theorem compactLoopPC2752 : Artifact.submissionArtifact.instructionPC 2794 = 3670 := by rfl
@[simp] private theorem compactLoopPC2753 : Artifact.submissionArtifact.instructionPC 2795 = 3671 := by rfl
@[simp] private theorem compactLoopPC2754 : Artifact.submissionArtifact.instructionPC 2796 = 3674 := by rfl
@[simp] private theorem compactLoopPC2755 : Artifact.submissionArtifact.instructionPC 2797 = 3675 := by rfl
@[simp] private theorem compactLoopPC2756 : Artifact.submissionArtifact.instructionPC 2798 = 3678 := by rfl
@[simp] private theorem compactLoopPC2758 : Artifact.submissionArtifact.instructionPC 2842 = 3724 := by rfl
@[simp] private theorem compactLoopPC2759 : Artifact.submissionArtifact.instructionPC 2843 = 3725 := by rfl
@[simp] private theorem compactLoopPC2760 : Artifact.submissionArtifact.instructionPC 2844 = 3726 := by rfl
@[simp] private theorem compactLoopPC2761 : Artifact.submissionArtifact.instructionPC 2845 = 3727 := by rfl
@[simp] private theorem compactLoopPC2762 : Artifact.submissionArtifact.instructionPC 2846 = 3728 := by rfl
@[simp] private theorem compactLoopPC2763 : Artifact.submissionArtifact.instructionPC 2847 = 3729 := by rfl
@[simp] private theorem compactLoopPC2764 : Artifact.submissionArtifact.instructionPC 2848 = 3730 := by rfl
@[simp] private theorem compactLoopPC2765 : Artifact.submissionArtifact.instructionPC 2849 = 3731 := by rfl
@[simp] private theorem compactLoopPC2766 : Artifact.submissionArtifact.instructionPC 2850 = 3732 := by rfl
@[simp] private theorem compactLoopPC2767 : Artifact.submissionArtifact.instructionPC 2851 = 3733 := by rfl
@[simp] private theorem compactLoopPC2768 : Artifact.submissionArtifact.instructionPC 2852 = 3734 := by rfl
@[simp] private theorem compactLoopPC2769 : Artifact.submissionArtifact.instructionPC 2853 = 3735 := by rfl
@[simp] private theorem compactLoopPC2770 : Artifact.submissionArtifact.instructionPC 2854 = 3736 := by rfl
@[simp] private theorem compactLoopPC2771 : Artifact.submissionArtifact.instructionPC 2855 = 3737 := by rfl
@[simp] private theorem compactLoopPC2772 : Artifact.submissionArtifact.instructionPC 2856 = 3738 := by rfl
@[simp] private theorem compactLoopPC2773 : Artifact.submissionArtifact.instructionPC 2857 = 3739 := by rfl
@[simp] private theorem compactLoopPC2774 : Artifact.submissionArtifact.instructionPC 2858 = 3740 := by rfl
@[simp] private theorem compactLoopPC2775 : Artifact.submissionArtifact.instructionPC 2859 = 3741 := by rfl
@[simp] private theorem compactLoopPC2776 : Artifact.submissionArtifact.instructionPC 2860 = 3742 := by rfl
@[simp] private theorem compactLoopPC2777 : Artifact.submissionArtifact.instructionPC 2861 = 3743 := by rfl
@[simp] private theorem compactLoopPC2778 : Artifact.submissionArtifact.instructionPC 2862 = 3744 := by rfl
@[simp] private theorem compactLoopPC2779 : Artifact.submissionArtifact.instructionPC 2863 = 3745 := by rfl
@[simp] private theorem compactLoopPC2780 : Artifact.submissionArtifact.instructionPC 2864 = 3746 := by rfl
@[simp] private theorem compactLoopPC2781 : Artifact.submissionArtifact.instructionPC 2865 = 3747 := by rfl
@[simp] private theorem compactLoopPC2782 : Artifact.submissionArtifact.instructionPC 2866 = 3748 := by rfl
@[simp] private theorem compactLoopPC2783 : Artifact.submissionArtifact.instructionPC 2867 = 3749 := by rfl
@[simp] private theorem compactLoopPC2784 : Artifact.submissionArtifact.instructionPC 2868 = 3750 := by rfl
@[simp] private theorem compactLoopPC2785 : Artifact.submissionArtifact.instructionPC 2869 = 3751 := by rfl
@[simp] private theorem compactLoopPC2786 : Artifact.submissionArtifact.instructionPC 2870 = 3752 := by rfl
@[simp] private theorem compactLoopPC2787 : Artifact.submissionArtifact.instructionPC 2871 = 3753 := by rfl
@[simp] private theorem compactLoopPC2788 : Artifact.submissionArtifact.instructionPC 2872 = 3754 := by rfl
@[simp] private theorem compactLoopPC2789 : Artifact.submissionArtifact.instructionPC 2873 = 3755 := by rfl
@[simp] private theorem compactLoopPC2790 : Artifact.submissionArtifact.instructionPC 2874 = 3756 := by rfl
@[simp] private theorem compactLoopPC2791 : Artifact.submissionArtifact.instructionPC 2875 = 3757 := by rfl
@[simp] private theorem compactLoopPC2792 : Artifact.submissionArtifact.instructionPC 2876 = 3758 := by rfl
@[simp] private theorem compactLoopPC2793 : Artifact.submissionArtifact.instructionPC 2877 = 3759 := by rfl
@[simp] private theorem compactLoopPC2794 : Artifact.submissionArtifact.instructionPC 2878 = 3760 := by rfl
@[simp] private theorem compactLoopPC2795 : Artifact.submissionArtifact.instructionPC 2879 = 3761 := by rfl
@[simp] private theorem compactLoopPC2797 : Artifact.submissionArtifact.instructionPC 2959 = 3843 := by rfl
@[simp] private theorem compactLoopPC2798 : Artifact.submissionArtifact.instructionPC 2960 = 3844 := by rfl
@[simp] private theorem compactLoopPC2799 : Artifact.submissionArtifact.instructionPC 2961 = 3845 := by rfl
@[simp] private theorem compactLoopPC2800 : Artifact.submissionArtifact.instructionPC 2962 = 3848 := by rfl
@[simp] private theorem compactLoopPC2803 : Artifact.submissionArtifact.instructionPC 2965 = 3851 := by rfl

def cellPath :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2841 .JUMPDEST,
   opAt 2842 (.Dup ⟨0, by decide⟩),
   opAt 2843 .MLOAD,
   pushAt 2844 0 0,
   opAt 2845 .NOT,
   opAt 2846 (.Dup ⟨6, by decide⟩),
   opAt 2847 (.Dup ⟨2, by decide⟩),
   opAt 2848 .MUL,
   opAt 2849 (.Swap ⟨1, by decide⟩),
   opAt 2850 (.Dup ⟨7, by decide⟩),
   opAt 2851 .MULMOD,
   opAt 2852 (.Dup ⟨1, by decide⟩),
   opAt 2853 (.Dup ⟨1, by decide⟩),
   opAt 2854 .LT,
   opAt 2855 .SUB,
   opAt 2856 (.Dup ⟨5, by decide⟩),
   opAt 2857 (.Dup ⟨2, by decide⟩),
   opAt 2858 .ADD,
   opAt 2859 (.Dup ⟨0, by decide⟩),
   opAt 2860 (.Swap ⟨6, by decide⟩),
   opAt 2861 .GT,
   opAt 2862 .SUB,
   opAt 2863 .SUB,
   opAt 2864 (.Dup ⟨4, by decide⟩),
   opAt 2865 (.Dup ⟨3, by decide⟩),
   opAt 2866 .MLOAD,
   opAt 2867 .ADD,
   opAt 2868 (.Dup ⟨0, by decide⟩),
   opAt 2869 (.Swap ⟨5, by decide⟩),
   opAt 2870 .GT,
   opAt 2871 .ADD,
   opAt 2872 (.Swap ⟨3, by decide⟩),
   opAt 2873 (.Dup ⟨2, by decide⟩),
   opAt 2874 (.Dup ⟨4, by decide⟩),
   opAt 2875 .ADD,
   opAt 2876 (.Swap ⟨2, by decide⟩),
   opAt 2877 .MSTORE,
   opAt 2878 (.Dup ⟨2, by decide⟩),
   opAt 2879 .ADD]

@[simp] private theorem cellStartPC : Artifact.submissionArtifact.instructionPC 2841 = 3723 := by rfl

theorem run_cell1 (s : State) (um : ByteArray) (q pa pt pa' pt' : UInt256)
    (n bsize esize msize k j : Nat)
    (hrun : s.halt = .Running)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hact : 296 ≤ s.activeWords.toNat)
    (hn32 : n ≤ 32) (hj : j < n)
    (hpa : pa.toNat = NEG + 32 * (n - 1 - j)) (hpt : pt.toNat = 8256 + 32 * (n - 1 - j))
    (hpa' : UInt256.ofNat 115792089237316195423570985008687907853269984665640564039457584007913129639904 + pa = pa')
    (hpt' : UInt256.ofNat 115792089237316195423570985008687907853269984665640564039457584007913129639904 + pt = pt') :
    Challenge.EvmProof.Stepper.runLocatedBlock cellPath
      { s with pc := UInt256.ofNat 3723
               stack := pa :: pt :: UInt256.ofNat 115792089237316195423570985008687907853269984665640564039457584007913129639904 :: (Monpro.l1Step um q NEG n j).carry :: q :: UInt256.ofNat k ::
                 outer n bsize esize msize
               memory := (Monpro.l1Step um q NEG n j).memory } =
      some { s with pc := UInt256.ofNat 3762
                    stack := pa' :: pt' :: UInt256.ofNat 115792089237316195423570985008687907853269984665640564039457584007913129639904 :: (Monpro.l1Step um q NEG n (j + 1)).carry :: q ::
                      UInt256.ofNat k :: outer n bsize esize msize
                    memory := (Monpro.l1Step um q NEG n (j + 1)).memory } := by
  have hactA : UInt256.ofNat (MachineState.activeWordsAfter s.activeWords.toNat
      (NEG + 32 * (n - 1 - j)) 32) = s.activeWords :=
    Monpro.activeWords_fix s _ 32 (by decide) (by unfold NEG; omega) hact
  have hactT : UInt256.ofNat (MachineState.activeWordsAfter s.activeWords.toNat
      (8256 + 32 * (n - 1 - j)) 32) = s.activeWords :=
    Monpro.activeWords_fix s _ 32 (by decide) (by omega) hact
  simp (config := { maxSteps := 800000 })
    [cellPath, opAt, pushAt, wfOp,
      Challenge.EvmProof.Stepper.runLocatedBlock,
      Challenge.EvmProof.Stepper.runLocated,
      Challenge.EvmProof.Stepper.runInstr,
      pcMacLoop, Monpro.l1Step, Monpro.macSum, Monpro.macCarry, Monpro.mulHi,
      Monpro.maxWord_literal, outer, Exp.outer,
      hrun, hcode, negK_literal, hpa, hpt, hpa', hpt', hactA, hactT,
      UInt256.gt, UInt256.isTrue,
      State.activeWordsAfterUInt256,
      Challenge.EvmProof.Word.succ_ofNat_mod,
      Challenge.EvmProof.Word.ofNat_add_mod,
      Challenge.EvmProof.Word.word_toNat_ofNat, Nat.mod_eq_of_lt,
      List.exchange]
  first
  | rfl
  | exact ⟨by rw [Monpro.MacAlt.macSumNat], Monpro.MacAlt.macCarryFix _ _ _ _⟩


#print axioms run_cell1
end Challenge.Modexp.Submission.Proofs.Fast.ShiftCell1
