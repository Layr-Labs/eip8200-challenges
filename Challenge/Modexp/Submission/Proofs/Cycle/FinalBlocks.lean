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
  WindowTwentyOneSlice.block Artifact.wellFormed 6700 55 8110 unpackFinalProgram
    (by change 6700+55 ≤ Artifact.instructions.length
        exact Nat.le_trans (by decide : 6700+55 ≤ 9183)
          (Nat.le_of_eq Artifact.instructionCount.symm))
    (by rw [PCFast.instructionPC_eq_byteLength]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)
def canonicalsubBlock : Block Artifact.artifact .Osaka 10857 canonicalsubProgram :=
  WindowTwentyOneSlice.block Artifact.wellFormed 8960 5 10857 canonicalsubProgram
    (by change 8960+5 ≤ Artifact.instructions.length
        exact Nat.le_trans (by decide : 8960+5 ≤ 9183)
          (Nat.le_of_eq Artifact.instructionCount.symm))
    (by rw [PCFast.instructionPC_eq_byteLength]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)
def packFinalBlock : Block Artifact.artifact .Osaka 10867 packFinalProgram :=
  WindowTwentyOneSlice.block Artifact.wellFormed 8966 87 10867 packFinalProgram
    (by change 8966+87 ≤ Artifact.instructions.length
        exact Nat.le_trans (by decide : 8966+87 ≤ 9183)
          (Nat.le_of_eq Artifact.instructionCount.symm))
    (by rw [PCFast.instructionPC_eq_byteLength]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)
def canonicalCompare0Block : Block Artifact.artifact .Osaka 10692 canonicalCompare0Program :=
  WindowTwentyOneSlice.block Artifact.wellFormed 8853 5 10692 canonicalCompare0Program
    (by change 8853+5 ≤ Artifact.instructions.length
        exact Nat.le_trans (by decide : 8853+5 ≤ 9183)
          (Nat.le_of_eq Artifact.instructionCount.symm))
    (by rw [PCFast.instructionPC_eq_byteLength]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)
def canonicalCompare0JumpBlock : Block Artifact.artifact .Osaka 10699 jumpiProgram :=
  WindowTwentyOneSlice.block Artifact.wellFormed 8858 1 10699 jumpiProgram
    (by change 8858+1 ≤ Artifact.instructions.length
        exact Nat.le_trans (by decide : 8858+1 ≤ 9183)
          (Nat.le_of_eq Artifact.instructionCount.symm))
    (by rw [PCFast.instructionPC_eq_byteLength]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)
def canonicalCompare1Block : Block Artifact.artifact .Osaka 10700 canonicalCompare1Program :=
  WindowTwentyOneSlice.block Artifact.wellFormed 8859 4 10700 canonicalCompare1Program
    (by change 8859+4 ≤ Artifact.instructions.length
        exact Nat.le_trans (by decide : 8859+4 ≤ 9183)
          (Nat.le_of_eq Artifact.instructionCount.symm))
    (by rw [PCFast.instructionPC_eq_byteLength]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)
def canonicalCompare1JumpBlock : Block Artifact.artifact .Osaka 10706 jumpiProgram :=
  WindowTwentyOneSlice.block Artifact.wellFormed 8863 1 10706 jumpiProgram
    (by change 8863+1 ≤ Artifact.instructions.length
        exact Nat.le_trans (by decide : 8863+1 ≤ 9183)
          (Nat.le_of_eq Artifact.instructionCount.symm))
    (by rw [PCFast.instructionPC_eq_byteLength]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)
def canonicalCompare2Block : Block Artifact.artifact .Osaka 10707 canonicalCompare2Program :=
  WindowTwentyOneSlice.block Artifact.wellFormed 8864 5 10707 canonicalCompare2Program
    (by change 8864+5 ≤ Artifact.instructions.length
        exact Nat.le_trans (by decide : 8864+5 ≤ 9183)
          (Nat.le_of_eq Artifact.instructionCount.symm))
    (by rw [PCFast.instructionPC_eq_byteLength]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)
def canonicalCompare2JumpBlock : Block Artifact.artifact .Osaka 10715 jumpiProgram :=
  WindowTwentyOneSlice.block Artifact.wellFormed 8869 1 10715 jumpiProgram
    (by change 8869+1 ≤ Artifact.instructions.length
        exact Nat.le_trans (by decide : 8869+1 ≤ 9183)
          (Nat.le_of_eq Artifact.instructionCount.symm))
    (by rw [PCFast.instructionPC_eq_byteLength]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)
def canonicalCompare3Block : Block Artifact.artifact .Osaka 10716 canonicalCompare3Program :=
  WindowTwentyOneSlice.block Artifact.wellFormed 8870 5 10716 canonicalCompare3Program
    (by change 8870+5 ≤ Artifact.instructions.length
        exact Nat.le_trans (by decide : 8870+5 ≤ 9183)
          (Nat.le_of_eq Artifact.instructionCount.symm))
    (by rw [PCFast.instructionPC_eq_byteLength]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)
def canonicalCompare3JumpBlock : Block Artifact.artifact .Osaka 10724 jumpiProgram :=
  WindowTwentyOneSlice.block Artifact.wellFormed 8875 1 10724 jumpiProgram
    (by change 8875+1 ≤ Artifact.instructions.length
        exact Nat.le_trans (by decide : 8875+1 ≤ 9183)
          (Nat.le_of_eq Artifact.instructionCount.symm))
    (by rw [PCFast.instructionPC_eq_byteLength]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)
def canonicalCompare4Block : Block Artifact.artifact .Osaka 10725 canonicalCompare4Program :=
  WindowTwentyOneSlice.block Artifact.wellFormed 8876 5 10725 canonicalCompare4Program
    (by change 8876+5 ≤ Artifact.instructions.length
        exact Nat.le_trans (by decide : 8876+5 ≤ 9183)
          (Nat.le_of_eq Artifact.instructionCount.symm))
    (by rw [PCFast.instructionPC_eq_byteLength]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)
def canonicalCompare4JumpBlock : Block Artifact.artifact .Osaka 10733 jumpiProgram :=
  WindowTwentyOneSlice.block Artifact.wellFormed 8881 1 10733 jumpiProgram
    (by change 8881+1 ≤ Artifact.instructions.length
        exact Nat.le_trans (by decide : 8881+1 ≤ 9183)
          (Nat.le_of_eq Artifact.instructionCount.symm))
    (by rw [PCFast.instructionPC_eq_byteLength]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)
def canonicalCompare5Block : Block Artifact.artifact .Osaka 10734 canonicalCompare5Program :=
  WindowTwentyOneSlice.block Artifact.wellFormed 8882 5 10734 canonicalCompare5Program
    (by change 8882+5 ≤ Artifact.instructions.length
        exact Nat.le_trans (by decide : 8882+5 ≤ 9183)
          (Nat.le_of_eq Artifact.instructionCount.symm))
    (by rw [PCFast.instructionPC_eq_byteLength]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)
def canonicalCompare5JumpBlock : Block Artifact.artifact .Osaka 10742 jumpiProgram :=
  WindowTwentyOneSlice.block Artifact.wellFormed 8887 1 10742 jumpiProgram
    (by change 8887+1 ≤ Artifact.instructions.length
        exact Nat.le_trans (by decide : 8887+1 ≤ 9183)
          (Nat.le_of_eq Artifact.instructionCount.symm))
    (by rw [PCFast.instructionPC_eq_byteLength]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)
def canonicalCompare6Block : Block Artifact.artifact .Osaka 10743 canonicalCompare6Program :=
  WindowTwentyOneSlice.block Artifact.wellFormed 8888 5 10743 canonicalCompare6Program
    (by change 8888+5 ≤ Artifact.instructions.length
        exact Nat.le_trans (by decide : 8888+5 ≤ 9183)
          (Nat.le_of_eq Artifact.instructionCount.symm))
    (by rw [PCFast.instructionPC_eq_byteLength]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)
def canonicalCompare6JumpBlock : Block Artifact.artifact .Osaka 10751 jumpiProgram :=
  WindowTwentyOneSlice.block Artifact.wellFormed 8893 1 10751 jumpiProgram
    (by change 8893+1 ≤ Artifact.instructions.length
        exact Nat.le_trans (by decide : 8893+1 ≤ 9183)
          (Nat.le_of_eq Artifact.instructionCount.symm))
    (by rw [PCFast.instructionPC_eq_byteLength]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)
def canonicalCompare7Block : Block Artifact.artifact .Osaka 10752 canonicalCompare7Program :=
  WindowTwentyOneSlice.block Artifact.wellFormed 8894 5 10752 canonicalCompare7Program
    (by change 8894+5 ≤ Artifact.instructions.length
        exact Nat.le_trans (by decide : 8894+5 ≤ 9183)
          (Nat.le_of_eq Artifact.instructionCount.symm))
    (by rw [PCFast.instructionPC_eq_byteLength]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)
def canonicalCompare7JumpBlock : Block Artifact.artifact .Osaka 10760 jumpiProgram :=
  WindowTwentyOneSlice.block Artifact.wellFormed 8899 1 10760 jumpiProgram
    (by change 8899+1 ≤ Artifact.instructions.length
        exact Nat.le_trans (by decide : 8899+1 ≤ 9183)
          (Nat.le_of_eq Artifact.instructionCount.symm))
    (by rw [PCFast.instructionPC_eq_byteLength]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)
def canonicalCompare8Block : Block Artifact.artifact .Osaka 10761 canonicalCompare8Program :=
  WindowTwentyOneSlice.block Artifact.wellFormed 8900 5 10761 canonicalCompare8Program
    (by change 8900+5 ≤ Artifact.instructions.length
        exact Nat.le_trans (by decide : 8900+5 ≤ 9183)
          (Nat.le_of_eq Artifact.instructionCount.symm))
    (by rw [PCFast.instructionPC_eq_byteLength]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)
def canonicalCompare8JumpBlock : Block Artifact.artifact .Osaka 10769 jumpiProgram :=
  WindowTwentyOneSlice.block Artifact.wellFormed 8905 1 10769 jumpiProgram
    (by change 8905+1 ≤ Artifact.instructions.length
        exact Nat.le_trans (by decide : 8905+1 ≤ 9183)
          (Nat.le_of_eq Artifact.instructionCount.symm))
    (by rw [PCFast.instructionPC_eq_byteLength]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)
def canonicalCompare9Block : Block Artifact.artifact .Osaka 10770 canonicalCompare9Program :=
  WindowTwentyOneSlice.block Artifact.wellFormed 8906 5 10770 canonicalCompare9Program
    (by change 8906+5 ≤ Artifact.instructions.length
        exact Nat.le_trans (by decide : 8906+5 ≤ 9183)
          (Nat.le_of_eq Artifact.instructionCount.symm))
    (by rw [PCFast.instructionPC_eq_byteLength]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)
def canonicalCompare9JumpBlock : Block Artifact.artifact .Osaka 10778 jumpiProgram :=
  WindowTwentyOneSlice.block Artifact.wellFormed 8911 1 10778 jumpiProgram
    (by change 8911+1 ≤ Artifact.instructions.length
        exact Nat.le_trans (by decide : 8911+1 ≤ 9183)
          (Nat.le_of_eq Artifact.instructionCount.symm))
    (by rw [PCFast.instructionPC_eq_byteLength]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)
def canonicalCompare10Block : Block Artifact.artifact .Osaka 10779 canonicalCompare10Program :=
  WindowTwentyOneSlice.block Artifact.wellFormed 8912 5 10779 canonicalCompare10Program
    (by change 8912+5 ≤ Artifact.instructions.length
        exact Nat.le_trans (by decide : 8912+5 ≤ 9183)
          (Nat.le_of_eq Artifact.instructionCount.symm))
    (by rw [PCFast.instructionPC_eq_byteLength]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)
def canonicalCompare10JumpBlock : Block Artifact.artifact .Osaka 10787 jumpiProgram :=
  WindowTwentyOneSlice.block Artifact.wellFormed 8917 1 10787 jumpiProgram
    (by change 8917+1 ≤ Artifact.instructions.length
        exact Nat.le_trans (by decide : 8917+1 ≤ 9183)
          (Nat.le_of_eq Artifact.instructionCount.symm))
    (by rw [PCFast.instructionPC_eq_byteLength]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)
def canonicalCompare11Block : Block Artifact.artifact .Osaka 10788 canonicalCompare11Program :=
  WindowTwentyOneSlice.block Artifact.wellFormed 8918 5 10788 canonicalCompare11Program
    (by change 8918+5 ≤ Artifact.instructions.length
        exact Nat.le_trans (by decide : 8918+5 ≤ 9183)
          (Nat.le_of_eq Artifact.instructionCount.symm))
    (by rw [PCFast.instructionPC_eq_byteLength]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)
def canonicalCompare11JumpBlock : Block Artifact.artifact .Osaka 10796 jumpiProgram :=
  WindowTwentyOneSlice.block Artifact.wellFormed 8923 1 10796 jumpiProgram
    (by change 8923+1 ≤ Artifact.instructions.length
        exact Nat.le_trans (by decide : 8923+1 ≤ 9183)
          (Nat.le_of_eq Artifact.instructionCount.symm))
    (by rw [PCFast.instructionPC_eq_byteLength]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)
def canonicalCompare12Block : Block Artifact.artifact .Osaka 10797 canonicalCompare12Program :=
  WindowTwentyOneSlice.block Artifact.wellFormed 8924 4 10797 canonicalCompare12Program
    (by change 8924+4 ≤ Artifact.instructions.length
        exact Nat.le_trans (by decide : 8924+4 ≤ 9183)
          (Nat.le_of_eq Artifact.instructionCount.symm))
    (by rw [PCFast.instructionPC_eq_byteLength]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)
def canonicalCompare12JumpBlock : Block Artifact.artifact .Osaka 10803 jumpiProgram :=
  WindowTwentyOneSlice.block Artifact.wellFormed 8928 1 10803 jumpiProgram
    (by change 8928+1 ≤ Artifact.instructions.length
        exact Nat.le_trans (by decide : 8928+1 ≤ 9183)
          (Nat.le_of_eq Artifact.instructionCount.symm))
    (by rw [PCFast.instructionPC_eq_byteLength]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)
def canonicalCompare13Block : Block Artifact.artifact .Osaka 10804 canonicalCompare13Program :=
  WindowTwentyOneSlice.block Artifact.wellFormed 8929 4 10804 canonicalCompare13Program
    (by change 8929+4 ≤ Artifact.instructions.length
        exact Nat.le_trans (by decide : 8929+4 ≤ 9183)
          (Nat.le_of_eq Artifact.instructionCount.symm))
    (by rw [PCFast.instructionPC_eq_byteLength]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)
def canonicalCompare13JumpBlock : Block Artifact.artifact .Osaka 10810 jumpiProgram :=
  WindowTwentyOneSlice.block Artifact.wellFormed 8933 1 10810 jumpiProgram
    (by change 8933+1 ≤ Artifact.instructions.length
        exact Nat.le_trans (by decide : 8933+1 ≤ 9183)
          (Nat.le_of_eq Artifact.instructionCount.symm))
    (by rw [PCFast.instructionPC_eq_byteLength]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)
def canonicalCompare14Block : Block Artifact.artifact .Osaka 10811 canonicalCompare14Program :=
  WindowTwentyOneSlice.block Artifact.wellFormed 8934 5 10811 canonicalCompare14Program
    (by change 8934+5 ≤ Artifact.instructions.length
        exact Nat.le_trans (by decide : 8934+5 ≤ 9183)
          (Nat.le_of_eq Artifact.instructionCount.symm))
    (by rw [PCFast.instructionPC_eq_byteLength]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)
def canonicalCompare14JumpBlock : Block Artifact.artifact .Osaka 10820 jumpiProgram :=
  WindowTwentyOneSlice.block Artifact.wellFormed 8939 1 10820 jumpiProgram
    (by change 8939+1 ≤ Artifact.instructions.length
        exact Nat.le_trans (by decide : 8939+1 ≤ 9183)
          (Nat.le_of_eq Artifact.instructionCount.symm))
    (by rw [PCFast.instructionPC_eq_byteLength]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)
def canonicalCompare15Block : Block Artifact.artifact .Osaka 10821 canonicalCompare15Program :=
  WindowTwentyOneSlice.block Artifact.wellFormed 8940 5 10821 canonicalCompare15Program
    (by change 8940+5 ≤ Artifact.instructions.length
        exact Nat.le_trans (by decide : 8940+5 ≤ 9183)
          (Nat.le_of_eq Artifact.instructionCount.symm))
    (by rw [PCFast.instructionPC_eq_byteLength]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)
def canonicalCompare15JumpBlock : Block Artifact.artifact .Osaka 10830 jumpiProgram :=
  WindowTwentyOneSlice.block Artifact.wellFormed 8945 1 10830 jumpiProgram
    (by change 8945+1 ≤ Artifact.instructions.length
        exact Nat.le_trans (by decide : 8945+1 ≤ 9183)
          (Nat.le_of_eq Artifact.instructionCount.symm))
    (by rw [PCFast.instructionPC_eq_byteLength]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)
def canonicalCompare16Block : Block Artifact.artifact .Osaka 10831 canonicalCompare16Program :=
  WindowTwentyOneSlice.block Artifact.wellFormed 8946 6 10831 canonicalCompare16Program
    (by change 8946+6 ≤ Artifact.instructions.length
        exact Nat.le_trans (by decide : 8946+6 ≤ 9183)
          (Nat.le_of_eq Artifact.instructionCount.symm))
    (by rw [PCFast.instructionPC_eq_byteLength]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)
def canonicalCompare16JumpBlock : Block Artifact.artifact .Osaka 10843 jumpiProgram :=
  WindowTwentyOneSlice.block Artifact.wellFormed 8952 1 10843 jumpiProgram
    (by change 8952+1 ≤ Artifact.instructions.length
        exact Nat.le_trans (by decide : 8952+1 ≤ 9183)
          (Nat.le_of_eq Artifact.instructionCount.symm))
    (by rw [PCFast.instructionPC_eq_byteLength]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)
def canonicalCompare17Block : Block Artifact.artifact .Osaka 10844 canonicalCompare17Program :=
  WindowTwentyOneSlice.block Artifact.wellFormed 8953 6 10844 canonicalCompare17Program
    (by change 8953+6 ≤ Artifact.instructions.length
        exact Nat.le_trans (by decide : 8953+6 ≤ 9183)
          (Nat.le_of_eq Artifact.instructionCount.symm))
    (by rw [PCFast.instructionPC_eq_byteLength]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)
def canonicalCompare17JumpBlock : Block Artifact.artifact .Osaka 10856 jumpiProgram :=
  WindowTwentyOneSlice.block Artifact.wellFormed 8959 1 10856 jumpiProgram
    (by change 8959+1 ≤ Artifact.instructions.length
        exact Nat.le_trans (by decide : 8959+1 ≤ 9183)
          (Nat.le_of_eq Artifact.instructionCount.symm))
    (by rw [PCFast.instructionPC_eq_byteLength]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)
def canonicalJumpBlock : Block Artifact.artifact .Osaka 10866 jumpProgram :=
  WindowTwentyOneSlice.block Artifact.wellFormed 8965 1 10866 jumpProgram
    (by change 8965+1 ≤ Artifact.instructions.length
        exact Nat.le_trans (by decide : 8965+1 ≤ 9183)
          (Nat.le_of_eq Artifact.instructionCount.symm))
    (by rw [PCFast.instructionPC_eq_byteLength]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)
theorem validJump10857 : Decode.isValidJumpDest Artifact.bytecode 10857 = true := by
  have h := ProgramArtifact.isValidJumpDest_index Artifact.artifact 8960
    (show Artifact.instructions[8960]? = some (.op .JUMPDEST) by rfl)
  have hp : Artifact.artifact.instructionPC 8960 = 10857 := by
    rw [PCFast.instructionPC_eq_byteLength]; rfl
  rw [hp] at h
  exact h
theorem validJump10867 : Decode.isValidJumpDest Artifact.bytecode 10867 = true := by
  have h := ProgramArtifact.isValidJumpDest_index Artifact.artifact 8966
    (show Artifact.instructions[8966]? = some (.op .JUMPDEST) by rfl)
  have hp : Artifact.artifact.instructionPC 8966 = 10867 := by
    rw [PCFast.instructionPC_eq_byteLength]; rfl
  rw [hp] at h
  exact h
theorem validJump11014 : Decode.isValidJumpDest Artifact.bytecode 11014 = true := by
  have h := ProgramArtifact.isValidJumpDest_index Artifact.artifact 9061
    (show Artifact.instructions[9061]? = some (.op .JUMPDEST) by rfl)
  have hp : Artifact.artifact.instructionPC 9061 = 11014 := by
    rw [PCFast.instructionPC_eq_byteLength]; rfl
  rw [hp] at h
  exact h
end CycleSubmission.FinalBlocks
