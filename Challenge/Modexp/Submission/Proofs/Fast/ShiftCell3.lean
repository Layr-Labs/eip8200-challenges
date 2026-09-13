import Challenge.Modexp.Submission.Proofs.Fast.ShiftBlocks
import Challenge.Modexp.Submission.Proofs.Fast.ShiftStates
import Challenge.Modexp.Submission.Proofs.Fast.CompactConstants
import Challenge.Modexp.Submission.Proofs.Bytecode.ShiftPCs

set_option warningAsError false
set_option maxRecDepth 40000
set_option maxHeartbeats 8000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace Challenge.Modexp.Submission.Proofs.Fast.ShiftCell3
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

@[simp] private theorem compactLoopPC2749 : Artifact.submissionArtifact.instructionPC 2768 = 3701 := by rfl
@[simp] private theorem compactLoopPC2750 : Artifact.submissionArtifact.instructionPC 2769 = 3703 := by rfl
@[simp] private theorem compactLoopPC2751 : Artifact.submissionArtifact.instructionPC 2770 = 3704 := by rfl
@[simp] private theorem compactLoopPC2752 : Artifact.submissionArtifact.instructionPC 2771 = 3707 := by rfl
@[simp] private theorem compactLoopPC2753 : Artifact.submissionArtifact.instructionPC 2772 = 3708 := by rfl
@[simp] private theorem compactLoopPC2754 : Artifact.submissionArtifact.instructionPC 2773 = 3711 := by rfl
@[simp] private theorem compactLoopPC2755 : Artifact.submissionArtifact.instructionPC 2774 = 3712 := by rfl
@[simp] private theorem compactLoopPC2756 : Artifact.submissionArtifact.instructionPC 2775 = 3715 := by rfl
@[simp] private theorem compactLoopPC2758 : Artifact.submissionArtifact.instructionPC 2897 = 3839 := by rfl
@[simp] private theorem compactLoopPC2759 : Artifact.submissionArtifact.instructionPC 2898 = 3840 := by rfl
@[simp] private theorem compactLoopPC2760 : Artifact.submissionArtifact.instructionPC 2899 = 3841 := by rfl
@[simp] private theorem compactLoopPC2761 : Artifact.submissionArtifact.instructionPC 2900 = 3842 := by rfl
@[simp] private theorem compactLoopPC2762 : Artifact.submissionArtifact.instructionPC 2901 = 3843 := by rfl
@[simp] private theorem compactLoopPC2763 : Artifact.submissionArtifact.instructionPC 2902 = 3844 := by rfl
@[simp] private theorem compactLoopPC2764 : Artifact.submissionArtifact.instructionPC 2903 = 3845 := by rfl
@[simp] private theorem compactLoopPC2765 : Artifact.submissionArtifact.instructionPC 2904 = 3846 := by rfl
@[simp] private theorem compactLoopPC2766 : Artifact.submissionArtifact.instructionPC 2905 = 3847 := by rfl
@[simp] private theorem compactLoopPC2767 : Artifact.submissionArtifact.instructionPC 2906 = 3848 := by rfl
@[simp] private theorem compactLoopPC2768 : Artifact.submissionArtifact.instructionPC 2907 = 3849 := by rfl
@[simp] private theorem compactLoopPC2769 : Artifact.submissionArtifact.instructionPC 2908 = 3850 := by rfl
@[simp] private theorem compactLoopPC2770 : Artifact.submissionArtifact.instructionPC 2909 = 3851 := by rfl
@[simp] private theorem compactLoopPC2771 : Artifact.submissionArtifact.instructionPC 2910 = 3852 := by rfl
@[simp] private theorem compactLoopPC2772 : Artifact.submissionArtifact.instructionPC 2911 = 3853 := by rfl
@[simp] private theorem compactLoopPC2773 : Artifact.submissionArtifact.instructionPC 2912 = 3854 := by rfl
@[simp] private theorem compactLoopPC2774 : Artifact.submissionArtifact.instructionPC 2913 = 3855 := by rfl
@[simp] private theorem compactLoopPC2775 : Artifact.submissionArtifact.instructionPC 2914 = 3856 := by rfl
@[simp] private theorem compactLoopPC2776 : Artifact.submissionArtifact.instructionPC 2915 = 3857 := by rfl
@[simp] private theorem compactLoopPC2777 : Artifact.submissionArtifact.instructionPC 2916 = 3858 := by rfl
@[simp] private theorem compactLoopPC2778 : Artifact.submissionArtifact.instructionPC 2917 = 3859 := by rfl
@[simp] private theorem compactLoopPC2779 : Artifact.submissionArtifact.instructionPC 2918 = 3860 := by rfl
@[simp] private theorem compactLoopPC2780 : Artifact.submissionArtifact.instructionPC 2919 = 3861 := by rfl
@[simp] private theorem compactLoopPC2781 : Artifact.submissionArtifact.instructionPC 2920 = 3862 := by rfl
@[simp] private theorem compactLoopPC2782 : Artifact.submissionArtifact.instructionPC 2921 = 3863 := by rfl
@[simp] private theorem compactLoopPC2783 : Artifact.submissionArtifact.instructionPC 2922 = 3864 := by rfl
@[simp] private theorem compactLoopPC2784 : Artifact.submissionArtifact.instructionPC 2923 = 3865 := by rfl
@[simp] private theorem compactLoopPC2785 : Artifact.submissionArtifact.instructionPC 2924 = 3866 := by rfl
@[simp] private theorem compactLoopPC2786 : Artifact.submissionArtifact.instructionPC 2925 = 3867 := by rfl
@[simp] private theorem compactLoopPC2787 : Artifact.submissionArtifact.instructionPC 2926 = 3868 := by rfl
@[simp] private theorem compactLoopPC2788 : Artifact.submissionArtifact.instructionPC 2927 = 3869 := by rfl
@[simp] private theorem compactLoopPC2789 : Artifact.submissionArtifact.instructionPC 2928 = 3870 := by rfl
@[simp] private theorem compactLoopPC2790 : Artifact.submissionArtifact.instructionPC 2929 = 3871 := by rfl
@[simp] private theorem compactLoopPC2791 : Artifact.submissionArtifact.instructionPC 2930 = 3872 := by rfl
@[simp] private theorem compactLoopPC2792 : Artifact.submissionArtifact.instructionPC 2931 = 3873 := by rfl
@[simp] private theorem compactLoopPC2793 : Artifact.submissionArtifact.instructionPC 2932 = 3874 := by rfl
@[simp] private theorem compactLoopPC2794 : Artifact.submissionArtifact.instructionPC 2933 = 3875 := by rfl
@[simp] private theorem compactLoopPC2795 : Artifact.submissionArtifact.instructionPC 2934 = 3876 := by rfl
@[simp] private theorem compactLoopPC2797 : Artifact.submissionArtifact.instructionPC 2936 = 3880 := by rfl
@[simp] private theorem compactLoopPC2798 : Artifact.submissionArtifact.instructionPC 2937 = 3881 := by rfl
@[simp] private theorem compactLoopPC2799 : Artifact.submissionArtifact.instructionPC 2938 = 3882 := by rfl
@[simp] private theorem compactLoopPC2800 : Artifact.submissionArtifact.instructionPC 2939 = 3885 := by rfl
@[simp] private theorem compactLoopPC2803 : Artifact.submissionArtifact.instructionPC 2942 = 3888 := by rfl

def cellPath :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2896 .JUMPDEST,
   opAt 2897 (.Dup ⟨0, by decide⟩),
   opAt 2898 .MLOAD,
   pushAt 2899 0 0,
   opAt 2900 .NOT,
   opAt 2901 (.Dup ⟨6, by decide⟩),
   opAt 2902 (.Dup ⟨2, by decide⟩),
   opAt 2903 .MUL,
   opAt 2904 (.Swap ⟨1, by decide⟩),
   opAt 2905 (.Dup ⟨7, by decide⟩),
   opAt 2906 .MULMOD,
   opAt 2907 (.Dup ⟨1, by decide⟩),
   opAt 2908 (.Dup ⟨1, by decide⟩),
   opAt 2909 .LT,
   opAt 2910 .SUB,
   opAt 2911 (.Dup ⟨5, by decide⟩),
   opAt 2912 (.Dup ⟨2, by decide⟩),
   opAt 2913 .ADD,
   opAt 2914 (.Dup ⟨0, by decide⟩),
   opAt 2915 (.Swap ⟨6, by decide⟩),
   opAt 2916 .GT,
   opAt 2917 .SUB,
   opAt 2918 .SUB,
   opAt 2919 (.Dup ⟨4, by decide⟩),
   opAt 2920 (.Dup ⟨3, by decide⟩),
   opAt 2921 .MLOAD,
   opAt 2922 .ADD,
   opAt 2923 (.Dup ⟨0, by decide⟩),
   opAt 2924 (.Swap ⟨5, by decide⟩),
   opAt 2925 .GT,
   opAt 2926 .ADD,
   opAt 2927 (.Swap ⟨3, by decide⟩),
   opAt 2928 (.Dup ⟨2, by decide⟩),
   opAt 2929 (.Dup ⟨4, by decide⟩),
   opAt 2930 .ADD,
   opAt 2931 (.Swap ⟨2, by decide⟩),
   opAt 2932 .MSTORE,
   opAt 2933 (.Dup ⟨2, by decide⟩),
   opAt 2934 .ADD]

@[simp] private theorem cellStartPC : Artifact.submissionArtifact.instructionPC 2896 = 3838 := by rfl

theorem run_cell3 (s : State) (um : ByteArray) (q pa pt pa' pt' : UInt256)
    (n bsize esize msize k j : Nat)
    (hrun : s.halt = .Running)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hact : 88 ≤ s.activeWords.toNat)
    (hn32 : n ≤ 8) (hj : j < n)
    (hpa : pa.toNat = NEG + 32 * (n - 1 - j)) (hpt : pt.toNat = 2112 + 32 * (n - 1 - j))
    (hpa' : UInt256.ofNat 115792089237316195423570985008687907853269984665640564039457584007913129639904 + pa = pa')
    (hpt' : UInt256.ofNat 115792089237316195423570985008687907853269984665640564039457584007913129639904 + pt = pt') :
    Challenge.EvmProof.Stepper.runLocatedBlock cellPath
      { s with pc := UInt256.ofNat 3838
               stack := pa :: pt :: UInt256.ofNat 115792089237316195423570985008687907853269984665640564039457584007913129639904 :: (Monpro.l1Step um q NEG n j).carry :: q :: UInt256.ofNat k ::
                 outer n bsize esize msize
               memory := (Monpro.l1Step um q NEG n j).memory } =
      some { s with pc := UInt256.ofNat 3877
                    stack := pa' :: pt' :: UInt256.ofNat 115792089237316195423570985008687907853269984665640564039457584007913129639904 :: (Monpro.l1Step um q NEG n (j + 1)).carry :: q ::
                      UInt256.ofNat k :: outer n bsize esize msize
                    memory := (Monpro.l1Step um q NEG n (j + 1)).memory } := by
  have hactA : UInt256.ofNat (MachineState.activeWordsAfter s.activeWords.toNat
      (NEG + 32 * (n - 1 - j)) 32) = s.activeWords :=
    Monpro.activeWords_fix s _ 32 (by decide) (by unfold NEG; omega) hact
  have hactT : UInt256.ofNat (MachineState.activeWordsAfter s.activeWords.toNat
      (2112 + 32 * (n - 1 - j)) 32) = s.activeWords :=
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


#print axioms run_cell3
end Challenge.Modexp.Submission.Proofs.Fast.ShiftCell3
