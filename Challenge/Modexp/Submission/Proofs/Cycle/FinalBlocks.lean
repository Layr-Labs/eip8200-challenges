import Challenge.Modexp.Submission.Proofs.Cycle.Execution.UnpackFinal
import Challenge.Modexp.Submission.Proofs.Cycle.Execution.Canonicalsub
import Challenge.Modexp.Submission.Proofs.Cycle.Execution.PackFinal
import Challenge.Modexp.Submission.Proofs.Cycle.Execution.CanonicalCompare0
import Challenge.Modexp.Submission.Proofs.Cycle.Execution.CanonicalCompare1
import Challenge.Modexp.Submission.Proofs.Cycle.Execution.CanonicalCompare2
import Challenge.Modexp.Submission.Proofs.Cycle.Execution.CanonicalCompare3
import Challenge.Modexp.Submission.Proofs.Cycle.Execution.CanonicalCompare4
import Challenge.Modexp.Submission.Proofs.Cycle.Execution.CanonicalCompare5
import Challenge.Modexp.Submission.Proofs.Cycle.Execution.CanonicalCompare6
import Challenge.Modexp.Submission.Proofs.Cycle.Execution.CanonicalCompare7
import Challenge.Modexp.Submission.Proofs.Cycle.Execution.CanonicalCompare8
import Challenge.Modexp.Submission.Proofs.Cycle.Execution.CanonicalCompare9
import Challenge.Modexp.Submission.Proofs.Cycle.Execution.CanonicalCompare10
import Challenge.Modexp.Submission.Proofs.Cycle.Execution.CanonicalCompare11
import Challenge.Modexp.Submission.Proofs.Cycle.Execution.CanonicalCompare12
import Challenge.Modexp.Submission.Proofs.Cycle.Execution.CanonicalCompare13
import Challenge.Modexp.Submission.Proofs.Cycle.Execution.CanonicalCompare14
import Challenge.Modexp.Submission.Proofs.Cycle.Execution.CanonicalCompare15
import Challenge.Modexp.Submission.Proofs.Cycle.Execution.CanonicalCompare16
import Challenge.Modexp.Submission.Proofs.Cycle.Execution.CanonicalCompare17
import Challenge.Modexp.Submission.Proofs.Cycle.Artifact
import Challenge.Modexp.Submission.Proofs.CRT.CRTControlBase
set_option warningAsError true
set_option maxRecDepth 50000
set_option maxHeartbeats 12000000
namespace CycleSubmission.FinalBlocks
open EvmSemantics EvmSemantics.EVM YulEvmCompiler
open CycleSubmission.Execution HistoricalSearch.CRTControl Challenge.EvmProof
open Challenge.Modexp.Submission.Proofs.Bytecode
open WindowTwentyOneBinding WindowTwentyOneSlice
def unpackFinalBlock : Block Artifact.artifact .Osaka 8110 unpackFinalProgram :=
  WindowTwentyOneSlice.block Artifact.wellFormed 6705 55 8110 unpackFinalProgram
    (by change 6705+55 ≤ Artifact.instructions.length
        exact Nat.le_trans (by decide : 6705+55 ≤ 9188)
          (Nat.le_of_eq Artifact.instructionCount.symm))
    (by rw [PCFast.instructionPC_eq_byteLength]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)
def canonicalsubBlock : Block Artifact.artifact .Osaka 10857 canonicalsubProgram :=
  WindowTwentyOneSlice.block Artifact.wellFormed 8965 5 10857 canonicalsubProgram
    (by change 8965+5 ≤ Artifact.instructions.length
        exact Nat.le_trans (by decide : 8965+5 ≤ 9188)
          (Nat.le_of_eq Artifact.instructionCount.symm))
    (by rw [PCFast.instructionPC_eq_byteLength]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)
def packFinalBlock : Block Artifact.artifact .Osaka 10867 packFinalProgram :=
  WindowTwentyOneSlice.block Artifact.wellFormed 8971 87 10867 packFinalProgram
    (by change 8971+87 ≤ Artifact.instructions.length
        exact Nat.le_trans (by decide : 8971+87 ≤ 9188)
          (Nat.le_of_eq Artifact.instructionCount.symm))
    (by rw [PCFast.instructionPC_eq_byteLength]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)
def canonicalCompare0Block : Block Artifact.artifact .Osaka 10692 canonicalCompare0Program :=
  WindowTwentyOneSlice.block Artifact.wellFormed 8858 5 10692 canonicalCompare0Program
    (by change 8858+5 ≤ Artifact.instructions.length
        exact Nat.le_trans (by decide : 8858+5 ≤ 9188)
          (Nat.le_of_eq Artifact.instructionCount.symm))
    (by rw [PCFast.instructionPC_eq_byteLength]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)
def canonicalCompare0JumpBlock : Block Artifact.artifact .Osaka 10699 jumpiProgram :=
  WindowTwentyOneSlice.block Artifact.wellFormed 8863 1 10699 jumpiProgram
    (by change 8863+1 ≤ Artifact.instructions.length
        exact Nat.le_trans (by decide : 8863+1 ≤ 9188)
          (Nat.le_of_eq Artifact.instructionCount.symm))
    (by rw [PCFast.instructionPC_eq_byteLength]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)
def canonicalCompare1Block : Block Artifact.artifact .Osaka 10700 canonicalCompare1Program :=
  WindowTwentyOneSlice.block Artifact.wellFormed 8864 4 10700 canonicalCompare1Program
    (by change 8864+4 ≤ Artifact.instructions.length
        exact Nat.le_trans (by decide : 8864+4 ≤ 9188)
          (Nat.le_of_eq Artifact.instructionCount.symm))
    (by rw [PCFast.instructionPC_eq_byteLength]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)
def canonicalCompare1JumpBlock : Block Artifact.artifact .Osaka 10706 jumpiProgram :=
  WindowTwentyOneSlice.block Artifact.wellFormed 8868 1 10706 jumpiProgram
    (by change 8868+1 ≤ Artifact.instructions.length
        exact Nat.le_trans (by decide : 8868+1 ≤ 9188)
          (Nat.le_of_eq Artifact.instructionCount.symm))
    (by rw [PCFast.instructionPC_eq_byteLength]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)
def canonicalCompare2Block : Block Artifact.artifact .Osaka 10707 canonicalCompare2Program :=
  WindowTwentyOneSlice.block Artifact.wellFormed 8869 5 10707 canonicalCompare2Program
    (by change 8869+5 ≤ Artifact.instructions.length
        exact Nat.le_trans (by decide : 8869+5 ≤ 9188)
          (Nat.le_of_eq Artifact.instructionCount.symm))
    (by rw [PCFast.instructionPC_eq_byteLength]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)
def canonicalCompare2JumpBlock : Block Artifact.artifact .Osaka 10715 jumpiProgram :=
  WindowTwentyOneSlice.block Artifact.wellFormed 8874 1 10715 jumpiProgram
    (by change 8874+1 ≤ Artifact.instructions.length
        exact Nat.le_trans (by decide : 8874+1 ≤ 9188)
          (Nat.le_of_eq Artifact.instructionCount.symm))
    (by rw [PCFast.instructionPC_eq_byteLength]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)
def canonicalCompare3Block : Block Artifact.artifact .Osaka 10716 canonicalCompare3Program :=
  WindowTwentyOneSlice.block Artifact.wellFormed 8875 5 10716 canonicalCompare3Program
    (by change 8875+5 ≤ Artifact.instructions.length
        exact Nat.le_trans (by decide : 8875+5 ≤ 9188)
          (Nat.le_of_eq Artifact.instructionCount.symm))
    (by rw [PCFast.instructionPC_eq_byteLength]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)
def canonicalCompare3JumpBlock : Block Artifact.artifact .Osaka 10724 jumpiProgram :=
  WindowTwentyOneSlice.block Artifact.wellFormed 8880 1 10724 jumpiProgram
    (by change 8880+1 ≤ Artifact.instructions.length
        exact Nat.le_trans (by decide : 8880+1 ≤ 9188)
          (Nat.le_of_eq Artifact.instructionCount.symm))
    (by rw [PCFast.instructionPC_eq_byteLength]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)
def canonicalCompare4Block : Block Artifact.artifact .Osaka 10725 canonicalCompare4Program :=
  WindowTwentyOneSlice.block Artifact.wellFormed 8881 5 10725 canonicalCompare4Program
    (by change 8881+5 ≤ Artifact.instructions.length
        exact Nat.le_trans (by decide : 8881+5 ≤ 9188)
          (Nat.le_of_eq Artifact.instructionCount.symm))
    (by rw [PCFast.instructionPC_eq_byteLength]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)
def canonicalCompare4JumpBlock : Block Artifact.artifact .Osaka 10733 jumpiProgram :=
  WindowTwentyOneSlice.block Artifact.wellFormed 8886 1 10733 jumpiProgram
    (by change 8886+1 ≤ Artifact.instructions.length
        exact Nat.le_trans (by decide : 8886+1 ≤ 9188)
          (Nat.le_of_eq Artifact.instructionCount.symm))
    (by rw [PCFast.instructionPC_eq_byteLength]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)
def canonicalCompare5Block : Block Artifact.artifact .Osaka 10734 canonicalCompare5Program :=
  WindowTwentyOneSlice.block Artifact.wellFormed 8887 5 10734 canonicalCompare5Program
    (by change 8887+5 ≤ Artifact.instructions.length
        exact Nat.le_trans (by decide : 8887+5 ≤ 9188)
          (Nat.le_of_eq Artifact.instructionCount.symm))
    (by rw [PCFast.instructionPC_eq_byteLength]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)
def canonicalCompare5JumpBlock : Block Artifact.artifact .Osaka 10742 jumpiProgram :=
  WindowTwentyOneSlice.block Artifact.wellFormed 8892 1 10742 jumpiProgram
    (by change 8892+1 ≤ Artifact.instructions.length
        exact Nat.le_trans (by decide : 8892+1 ≤ 9188)
          (Nat.le_of_eq Artifact.instructionCount.symm))
    (by rw [PCFast.instructionPC_eq_byteLength]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)
def canonicalCompare6Block : Block Artifact.artifact .Osaka 10743 canonicalCompare6Program :=
  WindowTwentyOneSlice.block Artifact.wellFormed 8893 5 10743 canonicalCompare6Program
    (by change 8893+5 ≤ Artifact.instructions.length
        exact Nat.le_trans (by decide : 8893+5 ≤ 9188)
          (Nat.le_of_eq Artifact.instructionCount.symm))
    (by rw [PCFast.instructionPC_eq_byteLength]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)
def canonicalCompare6JumpBlock : Block Artifact.artifact .Osaka 10751 jumpiProgram :=
  WindowTwentyOneSlice.block Artifact.wellFormed 8898 1 10751 jumpiProgram
    (by change 8898+1 ≤ Artifact.instructions.length
        exact Nat.le_trans (by decide : 8898+1 ≤ 9188)
          (Nat.le_of_eq Artifact.instructionCount.symm))
    (by rw [PCFast.instructionPC_eq_byteLength]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)
def canonicalCompare7Block : Block Artifact.artifact .Osaka 10752 canonicalCompare7Program :=
  WindowTwentyOneSlice.block Artifact.wellFormed 8899 5 10752 canonicalCompare7Program
    (by change 8899+5 ≤ Artifact.instructions.length
        exact Nat.le_trans (by decide : 8899+5 ≤ 9188)
          (Nat.le_of_eq Artifact.instructionCount.symm))
    (by rw [PCFast.instructionPC_eq_byteLength]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)
def canonicalCompare7JumpBlock : Block Artifact.artifact .Osaka 10760 jumpiProgram :=
  WindowTwentyOneSlice.block Artifact.wellFormed 8904 1 10760 jumpiProgram
    (by change 8904+1 ≤ Artifact.instructions.length
        exact Nat.le_trans (by decide : 8904+1 ≤ 9188)
          (Nat.le_of_eq Artifact.instructionCount.symm))
    (by rw [PCFast.instructionPC_eq_byteLength]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)
def canonicalCompare8Block : Block Artifact.artifact .Osaka 10761 canonicalCompare8Program :=
  WindowTwentyOneSlice.block Artifact.wellFormed 8905 5 10761 canonicalCompare8Program
    (by change 8905+5 ≤ Artifact.instructions.length
        exact Nat.le_trans (by decide : 8905+5 ≤ 9188)
          (Nat.le_of_eq Artifact.instructionCount.symm))
    (by rw [PCFast.instructionPC_eq_byteLength]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)
def canonicalCompare8JumpBlock : Block Artifact.artifact .Osaka 10769 jumpiProgram :=
  WindowTwentyOneSlice.block Artifact.wellFormed 8910 1 10769 jumpiProgram
    (by change 8910+1 ≤ Artifact.instructions.length
        exact Nat.le_trans (by decide : 8910+1 ≤ 9188)
          (Nat.le_of_eq Artifact.instructionCount.symm))
    (by rw [PCFast.instructionPC_eq_byteLength]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)
def canonicalCompare9Block : Block Artifact.artifact .Osaka 10770 canonicalCompare9Program :=
  WindowTwentyOneSlice.block Artifact.wellFormed 8911 5 10770 canonicalCompare9Program
    (by change 8911+5 ≤ Artifact.instructions.length
        exact Nat.le_trans (by decide : 8911+5 ≤ 9188)
          (Nat.le_of_eq Artifact.instructionCount.symm))
    (by rw [PCFast.instructionPC_eq_byteLength]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)
def canonicalCompare9JumpBlock : Block Artifact.artifact .Osaka 10778 jumpiProgram :=
  WindowTwentyOneSlice.block Artifact.wellFormed 8916 1 10778 jumpiProgram
    (by change 8916+1 ≤ Artifact.instructions.length
        exact Nat.le_trans (by decide : 8916+1 ≤ 9188)
          (Nat.le_of_eq Artifact.instructionCount.symm))
    (by rw [PCFast.instructionPC_eq_byteLength]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)
def canonicalCompare10Block : Block Artifact.artifact .Osaka 10779 canonicalCompare10Program :=
  WindowTwentyOneSlice.block Artifact.wellFormed 8917 5 10779 canonicalCompare10Program
    (by change 8917+5 ≤ Artifact.instructions.length
        exact Nat.le_trans (by decide : 8917+5 ≤ 9188)
          (Nat.le_of_eq Artifact.instructionCount.symm))
    (by rw [PCFast.instructionPC_eq_byteLength]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)
def canonicalCompare10JumpBlock : Block Artifact.artifact .Osaka 10787 jumpiProgram :=
  WindowTwentyOneSlice.block Artifact.wellFormed 8922 1 10787 jumpiProgram
    (by change 8922+1 ≤ Artifact.instructions.length
        exact Nat.le_trans (by decide : 8922+1 ≤ 9188)
          (Nat.le_of_eq Artifact.instructionCount.symm))
    (by rw [PCFast.instructionPC_eq_byteLength]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)
def canonicalCompare11Block : Block Artifact.artifact .Osaka 10788 canonicalCompare11Program :=
  WindowTwentyOneSlice.block Artifact.wellFormed 8923 5 10788 canonicalCompare11Program
    (by change 8923+5 ≤ Artifact.instructions.length
        exact Nat.le_trans (by decide : 8923+5 ≤ 9188)
          (Nat.le_of_eq Artifact.instructionCount.symm))
    (by rw [PCFast.instructionPC_eq_byteLength]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)
def canonicalCompare11JumpBlock : Block Artifact.artifact .Osaka 10796 jumpiProgram :=
  WindowTwentyOneSlice.block Artifact.wellFormed 8928 1 10796 jumpiProgram
    (by change 8928+1 ≤ Artifact.instructions.length
        exact Nat.le_trans (by decide : 8928+1 ≤ 9188)
          (Nat.le_of_eq Artifact.instructionCount.symm))
    (by rw [PCFast.instructionPC_eq_byteLength]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)
def canonicalCompare12Block : Block Artifact.artifact .Osaka 10797 canonicalCompare12Program :=
  WindowTwentyOneSlice.block Artifact.wellFormed 8929 4 10797 canonicalCompare12Program
    (by change 8929+4 ≤ Artifact.instructions.length
        exact Nat.le_trans (by decide : 8929+4 ≤ 9188)
          (Nat.le_of_eq Artifact.instructionCount.symm))
    (by rw [PCFast.instructionPC_eq_byteLength]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)
def canonicalCompare12JumpBlock : Block Artifact.artifact .Osaka 10803 jumpiProgram :=
  WindowTwentyOneSlice.block Artifact.wellFormed 8933 1 10803 jumpiProgram
    (by change 8933+1 ≤ Artifact.instructions.length
        exact Nat.le_trans (by decide : 8933+1 ≤ 9188)
          (Nat.le_of_eq Artifact.instructionCount.symm))
    (by rw [PCFast.instructionPC_eq_byteLength]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)
def canonicalCompare13Block : Block Artifact.artifact .Osaka 10804 canonicalCompare13Program :=
  WindowTwentyOneSlice.block Artifact.wellFormed 8934 4 10804 canonicalCompare13Program
    (by change 8934+4 ≤ Artifact.instructions.length
        exact Nat.le_trans (by decide : 8934+4 ≤ 9188)
          (Nat.le_of_eq Artifact.instructionCount.symm))
    (by rw [PCFast.instructionPC_eq_byteLength]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)
def canonicalCompare13JumpBlock : Block Artifact.artifact .Osaka 10810 jumpiProgram :=
  WindowTwentyOneSlice.block Artifact.wellFormed 8938 1 10810 jumpiProgram
    (by change 8938+1 ≤ Artifact.instructions.length
        exact Nat.le_trans (by decide : 8938+1 ≤ 9188)
          (Nat.le_of_eq Artifact.instructionCount.symm))
    (by rw [PCFast.instructionPC_eq_byteLength]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)
def canonicalCompare14Block : Block Artifact.artifact .Osaka 10811 canonicalCompare14Program :=
  WindowTwentyOneSlice.block Artifact.wellFormed 8939 5 10811 canonicalCompare14Program
    (by change 8939+5 ≤ Artifact.instructions.length
        exact Nat.le_trans (by decide : 8939+5 ≤ 9188)
          (Nat.le_of_eq Artifact.instructionCount.symm))
    (by rw [PCFast.instructionPC_eq_byteLength]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)
def canonicalCompare14JumpBlock : Block Artifact.artifact .Osaka 10820 jumpiProgram :=
  WindowTwentyOneSlice.block Artifact.wellFormed 8944 1 10820 jumpiProgram
    (by change 8944+1 ≤ Artifact.instructions.length
        exact Nat.le_trans (by decide : 8944+1 ≤ 9188)
          (Nat.le_of_eq Artifact.instructionCount.symm))
    (by rw [PCFast.instructionPC_eq_byteLength]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)
def canonicalCompare15Block : Block Artifact.artifact .Osaka 10821 canonicalCompare15Program :=
  WindowTwentyOneSlice.block Artifact.wellFormed 8945 5 10821 canonicalCompare15Program
    (by change 8945+5 ≤ Artifact.instructions.length
        exact Nat.le_trans (by decide : 8945+5 ≤ 9188)
          (Nat.le_of_eq Artifact.instructionCount.symm))
    (by rw [PCFast.instructionPC_eq_byteLength]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)
def canonicalCompare15JumpBlock : Block Artifact.artifact .Osaka 10830 jumpiProgram :=
  WindowTwentyOneSlice.block Artifact.wellFormed 8950 1 10830 jumpiProgram
    (by change 8950+1 ≤ Artifact.instructions.length
        exact Nat.le_trans (by decide : 8950+1 ≤ 9188)
          (Nat.le_of_eq Artifact.instructionCount.symm))
    (by rw [PCFast.instructionPC_eq_byteLength]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)
def canonicalCompare16Block : Block Artifact.artifact .Osaka 10831 canonicalCompare16Program :=
  WindowTwentyOneSlice.block Artifact.wellFormed 8951 6 10831 canonicalCompare16Program
    (by change 8951+6 ≤ Artifact.instructions.length
        exact Nat.le_trans (by decide : 8951+6 ≤ 9188)
          (Nat.le_of_eq Artifact.instructionCount.symm))
    (by rw [PCFast.instructionPC_eq_byteLength]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)
def canonicalCompare16JumpBlock : Block Artifact.artifact .Osaka 10843 jumpiProgram :=
  WindowTwentyOneSlice.block Artifact.wellFormed 8957 1 10843 jumpiProgram
    (by change 8957+1 ≤ Artifact.instructions.length
        exact Nat.le_trans (by decide : 8957+1 ≤ 9188)
          (Nat.le_of_eq Artifact.instructionCount.symm))
    (by rw [PCFast.instructionPC_eq_byteLength]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)
def canonicalCompare17Block : Block Artifact.artifact .Osaka 10844 canonicalCompare17Program :=
  WindowTwentyOneSlice.block Artifact.wellFormed 8958 6 10844 canonicalCompare17Program
    (by change 8958+6 ≤ Artifact.instructions.length
        exact Nat.le_trans (by decide : 8958+6 ≤ 9188)
          (Nat.le_of_eq Artifact.instructionCount.symm))
    (by rw [PCFast.instructionPC_eq_byteLength]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)
def canonicalCompare17JumpBlock : Block Artifact.artifact .Osaka 10856 jumpiProgram :=
  WindowTwentyOneSlice.block Artifact.wellFormed 8964 1 10856 jumpiProgram
    (by change 8964+1 ≤ Artifact.instructions.length
        exact Nat.le_trans (by decide : 8964+1 ≤ 9188)
          (Nat.le_of_eq Artifact.instructionCount.symm))
    (by rw [PCFast.instructionPC_eq_byteLength]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)
def canonicalJumpBlock : Block Artifact.artifact .Osaka 10866 jumpProgram :=
  WindowTwentyOneSlice.block Artifact.wellFormed 8970 1 10866 jumpProgram
    (by change 8970+1 ≤ Artifact.instructions.length
        exact Nat.le_trans (by decide : 8970+1 ≤ 9188)
          (Nat.le_of_eq Artifact.instructionCount.symm))
    (by rw [PCFast.instructionPC_eq_byteLength]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)
theorem validJump10857 : Decode.isValidJumpDest Artifact.bytecode 10857 = true := by
  have h := ProgramArtifact.isValidJumpDest_index Artifact.artifact 8965
    (show Artifact.instructions[8965]? = some (.op .JUMPDEST) by rfl)
  have hp : Artifact.artifact.instructionPC 8965 = 10857 := by
    rw [PCFast.instructionPC_eq_byteLength]; rfl
  rw [hp] at h
  exact h
theorem validJump10867 : Decode.isValidJumpDest Artifact.bytecode 10867 = true := by
  have h := ProgramArtifact.isValidJumpDest_index Artifact.artifact 8971
    (show Artifact.instructions[8971]? = some (.op .JUMPDEST) by rfl)
  have hp : Artifact.artifact.instructionPC 8971 = 10867 := by
    rw [PCFast.instructionPC_eq_byteLength]; rfl
  rw [hp] at h
  exact h
theorem validJump11014 : Decode.isValidJumpDest Artifact.bytecode 11014 = true := by
  have h := ProgramArtifact.isValidJumpDest_index Artifact.artifact 9066
    (show Artifact.instructions[9066]? = some (.op .JUMPDEST) by rfl)
  have hp : Artifact.artifact.instructionPC 9066 = 11014 := by
    rw [PCFast.instructionPC_eq_byteLength]; rfl
  rw [hp] at h
  exact h
end CycleSubmission.FinalBlocks
