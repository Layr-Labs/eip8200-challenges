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
  WindowTwentyOneSlice.block Artifact.wellFormed 6701 55 8110 unpackFinalProgram
    (by change 6701+55 ≤ Artifact.instructions.length
        exact Nat.le_trans (by decide : 6701+55 ≤ 9184)
          (Nat.le_of_eq Artifact.instructionCount.symm))
    (by rw [PCFast.instructionPC_eq_byteLength]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)
def canonicalsubBlock : Block Artifact.artifact .Osaka 10857 canonicalsubProgram :=
  WindowTwentyOneSlice.block Artifact.wellFormed 8961 5 10857 canonicalsubProgram
    (by change 8961+5 ≤ Artifact.instructions.length
        exact Nat.le_trans (by decide : 8961+5 ≤ 9184)
          (Nat.le_of_eq Artifact.instructionCount.symm))
    (by rw [PCFast.instructionPC_eq_byteLength]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)
def packFinalBlock : Block Artifact.artifact .Osaka 10867 packFinalProgram :=
  WindowTwentyOneSlice.block Artifact.wellFormed 8967 87 10867 packFinalProgram
    (by change 8967+87 ≤ Artifact.instructions.length
        exact Nat.le_trans (by decide : 8967+87 ≤ 9184)
          (Nat.le_of_eq Artifact.instructionCount.symm))
    (by rw [PCFast.instructionPC_eq_byteLength]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)
def canonicalCompare0Block : Block Artifact.artifact .Osaka 10692 canonicalCompare0Program :=
  WindowTwentyOneSlice.block Artifact.wellFormed 8854 5 10692 canonicalCompare0Program
    (by change 8854+5 ≤ Artifact.instructions.length
        exact Nat.le_trans (by decide : 8854+5 ≤ 9184)
          (Nat.le_of_eq Artifact.instructionCount.symm))
    (by rw [PCFast.instructionPC_eq_byteLength]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)
def canonicalCompare0JumpBlock : Block Artifact.artifact .Osaka 10699 jumpiProgram :=
  WindowTwentyOneSlice.block Artifact.wellFormed 8859 1 10699 jumpiProgram
    (by change 8859+1 ≤ Artifact.instructions.length
        exact Nat.le_trans (by decide : 8859+1 ≤ 9184)
          (Nat.le_of_eq Artifact.instructionCount.symm))
    (by rw [PCFast.instructionPC_eq_byteLength]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)
def canonicalCompare1Block : Block Artifact.artifact .Osaka 10700 canonicalCompare1Program :=
  WindowTwentyOneSlice.block Artifact.wellFormed 8860 4 10700 canonicalCompare1Program
    (by change 8860+4 ≤ Artifact.instructions.length
        exact Nat.le_trans (by decide : 8860+4 ≤ 9184)
          (Nat.le_of_eq Artifact.instructionCount.symm))
    (by rw [PCFast.instructionPC_eq_byteLength]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)
def canonicalCompare1JumpBlock : Block Artifact.artifact .Osaka 10706 jumpiProgram :=
  WindowTwentyOneSlice.block Artifact.wellFormed 8864 1 10706 jumpiProgram
    (by change 8864+1 ≤ Artifact.instructions.length
        exact Nat.le_trans (by decide : 8864+1 ≤ 9184)
          (Nat.le_of_eq Artifact.instructionCount.symm))
    (by rw [PCFast.instructionPC_eq_byteLength]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)
def canonicalCompare2Block : Block Artifact.artifact .Osaka 10707 canonicalCompare2Program :=
  WindowTwentyOneSlice.block Artifact.wellFormed 8865 5 10707 canonicalCompare2Program
    (by change 8865+5 ≤ Artifact.instructions.length
        exact Nat.le_trans (by decide : 8865+5 ≤ 9184)
          (Nat.le_of_eq Artifact.instructionCount.symm))
    (by rw [PCFast.instructionPC_eq_byteLength]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)
def canonicalCompare2JumpBlock : Block Artifact.artifact .Osaka 10715 jumpiProgram :=
  WindowTwentyOneSlice.block Artifact.wellFormed 8870 1 10715 jumpiProgram
    (by change 8870+1 ≤ Artifact.instructions.length
        exact Nat.le_trans (by decide : 8870+1 ≤ 9184)
          (Nat.le_of_eq Artifact.instructionCount.symm))
    (by rw [PCFast.instructionPC_eq_byteLength]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)
def canonicalCompare3Block : Block Artifact.artifact .Osaka 10716 canonicalCompare3Program :=
  WindowTwentyOneSlice.block Artifact.wellFormed 8871 5 10716 canonicalCompare3Program
    (by change 8871+5 ≤ Artifact.instructions.length
        exact Nat.le_trans (by decide : 8871+5 ≤ 9184)
          (Nat.le_of_eq Artifact.instructionCount.symm))
    (by rw [PCFast.instructionPC_eq_byteLength]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)
def canonicalCompare3JumpBlock : Block Artifact.artifact .Osaka 10724 jumpiProgram :=
  WindowTwentyOneSlice.block Artifact.wellFormed 8876 1 10724 jumpiProgram
    (by change 8876+1 ≤ Artifact.instructions.length
        exact Nat.le_trans (by decide : 8876+1 ≤ 9184)
          (Nat.le_of_eq Artifact.instructionCount.symm))
    (by rw [PCFast.instructionPC_eq_byteLength]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)
def canonicalCompare4Block : Block Artifact.artifact .Osaka 10725 canonicalCompare4Program :=
  WindowTwentyOneSlice.block Artifact.wellFormed 8877 5 10725 canonicalCompare4Program
    (by change 8877+5 ≤ Artifact.instructions.length
        exact Nat.le_trans (by decide : 8877+5 ≤ 9184)
          (Nat.le_of_eq Artifact.instructionCount.symm))
    (by rw [PCFast.instructionPC_eq_byteLength]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)
def canonicalCompare4JumpBlock : Block Artifact.artifact .Osaka 10733 jumpiProgram :=
  WindowTwentyOneSlice.block Artifact.wellFormed 8882 1 10733 jumpiProgram
    (by change 8882+1 ≤ Artifact.instructions.length
        exact Nat.le_trans (by decide : 8882+1 ≤ 9184)
          (Nat.le_of_eq Artifact.instructionCount.symm))
    (by rw [PCFast.instructionPC_eq_byteLength]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)
def canonicalCompare5Block : Block Artifact.artifact .Osaka 10734 canonicalCompare5Program :=
  WindowTwentyOneSlice.block Artifact.wellFormed 8883 5 10734 canonicalCompare5Program
    (by change 8883+5 ≤ Artifact.instructions.length
        exact Nat.le_trans (by decide : 8883+5 ≤ 9184)
          (Nat.le_of_eq Artifact.instructionCount.symm))
    (by rw [PCFast.instructionPC_eq_byteLength]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)
def canonicalCompare5JumpBlock : Block Artifact.artifact .Osaka 10742 jumpiProgram :=
  WindowTwentyOneSlice.block Artifact.wellFormed 8888 1 10742 jumpiProgram
    (by change 8888+1 ≤ Artifact.instructions.length
        exact Nat.le_trans (by decide : 8888+1 ≤ 9184)
          (Nat.le_of_eq Artifact.instructionCount.symm))
    (by rw [PCFast.instructionPC_eq_byteLength]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)
def canonicalCompare6Block : Block Artifact.artifact .Osaka 10743 canonicalCompare6Program :=
  WindowTwentyOneSlice.block Artifact.wellFormed 8889 5 10743 canonicalCompare6Program
    (by change 8889+5 ≤ Artifact.instructions.length
        exact Nat.le_trans (by decide : 8889+5 ≤ 9184)
          (Nat.le_of_eq Artifact.instructionCount.symm))
    (by rw [PCFast.instructionPC_eq_byteLength]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)
def canonicalCompare6JumpBlock : Block Artifact.artifact .Osaka 10751 jumpiProgram :=
  WindowTwentyOneSlice.block Artifact.wellFormed 8894 1 10751 jumpiProgram
    (by change 8894+1 ≤ Artifact.instructions.length
        exact Nat.le_trans (by decide : 8894+1 ≤ 9184)
          (Nat.le_of_eq Artifact.instructionCount.symm))
    (by rw [PCFast.instructionPC_eq_byteLength]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)
def canonicalCompare7Block : Block Artifact.artifact .Osaka 10752 canonicalCompare7Program :=
  WindowTwentyOneSlice.block Artifact.wellFormed 8895 5 10752 canonicalCompare7Program
    (by change 8895+5 ≤ Artifact.instructions.length
        exact Nat.le_trans (by decide : 8895+5 ≤ 9184)
          (Nat.le_of_eq Artifact.instructionCount.symm))
    (by rw [PCFast.instructionPC_eq_byteLength]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)
def canonicalCompare7JumpBlock : Block Artifact.artifact .Osaka 10760 jumpiProgram :=
  WindowTwentyOneSlice.block Artifact.wellFormed 8900 1 10760 jumpiProgram
    (by change 8900+1 ≤ Artifact.instructions.length
        exact Nat.le_trans (by decide : 8900+1 ≤ 9184)
          (Nat.le_of_eq Artifact.instructionCount.symm))
    (by rw [PCFast.instructionPC_eq_byteLength]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)
def canonicalCompare8Block : Block Artifact.artifact .Osaka 10761 canonicalCompare8Program :=
  WindowTwentyOneSlice.block Artifact.wellFormed 8901 5 10761 canonicalCompare8Program
    (by change 8901+5 ≤ Artifact.instructions.length
        exact Nat.le_trans (by decide : 8901+5 ≤ 9184)
          (Nat.le_of_eq Artifact.instructionCount.symm))
    (by rw [PCFast.instructionPC_eq_byteLength]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)
def canonicalCompare8JumpBlock : Block Artifact.artifact .Osaka 10769 jumpiProgram :=
  WindowTwentyOneSlice.block Artifact.wellFormed 8906 1 10769 jumpiProgram
    (by change 8906+1 ≤ Artifact.instructions.length
        exact Nat.le_trans (by decide : 8906+1 ≤ 9184)
          (Nat.le_of_eq Artifact.instructionCount.symm))
    (by rw [PCFast.instructionPC_eq_byteLength]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)
def canonicalCompare9Block : Block Artifact.artifact .Osaka 10770 canonicalCompare9Program :=
  WindowTwentyOneSlice.block Artifact.wellFormed 8907 5 10770 canonicalCompare9Program
    (by change 8907+5 ≤ Artifact.instructions.length
        exact Nat.le_trans (by decide : 8907+5 ≤ 9184)
          (Nat.le_of_eq Artifact.instructionCount.symm))
    (by rw [PCFast.instructionPC_eq_byteLength]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)
def canonicalCompare9JumpBlock : Block Artifact.artifact .Osaka 10778 jumpiProgram :=
  WindowTwentyOneSlice.block Artifact.wellFormed 8912 1 10778 jumpiProgram
    (by change 8912+1 ≤ Artifact.instructions.length
        exact Nat.le_trans (by decide : 8912+1 ≤ 9184)
          (Nat.le_of_eq Artifact.instructionCount.symm))
    (by rw [PCFast.instructionPC_eq_byteLength]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)
def canonicalCompare10Block : Block Artifact.artifact .Osaka 10779 canonicalCompare10Program :=
  WindowTwentyOneSlice.block Artifact.wellFormed 8913 5 10779 canonicalCompare10Program
    (by change 8913+5 ≤ Artifact.instructions.length
        exact Nat.le_trans (by decide : 8913+5 ≤ 9184)
          (Nat.le_of_eq Artifact.instructionCount.symm))
    (by rw [PCFast.instructionPC_eq_byteLength]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)
def canonicalCompare10JumpBlock : Block Artifact.artifact .Osaka 10787 jumpiProgram :=
  WindowTwentyOneSlice.block Artifact.wellFormed 8918 1 10787 jumpiProgram
    (by change 8918+1 ≤ Artifact.instructions.length
        exact Nat.le_trans (by decide : 8918+1 ≤ 9184)
          (Nat.le_of_eq Artifact.instructionCount.symm))
    (by rw [PCFast.instructionPC_eq_byteLength]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)
def canonicalCompare11Block : Block Artifact.artifact .Osaka 10788 canonicalCompare11Program :=
  WindowTwentyOneSlice.block Artifact.wellFormed 8919 5 10788 canonicalCompare11Program
    (by change 8919+5 ≤ Artifact.instructions.length
        exact Nat.le_trans (by decide : 8919+5 ≤ 9184)
          (Nat.le_of_eq Artifact.instructionCount.symm))
    (by rw [PCFast.instructionPC_eq_byteLength]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)
def canonicalCompare11JumpBlock : Block Artifact.artifact .Osaka 10796 jumpiProgram :=
  WindowTwentyOneSlice.block Artifact.wellFormed 8924 1 10796 jumpiProgram
    (by change 8924+1 ≤ Artifact.instructions.length
        exact Nat.le_trans (by decide : 8924+1 ≤ 9184)
          (Nat.le_of_eq Artifact.instructionCount.symm))
    (by rw [PCFast.instructionPC_eq_byteLength]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)
def canonicalCompare12Block : Block Artifact.artifact .Osaka 10797 canonicalCompare12Program :=
  WindowTwentyOneSlice.block Artifact.wellFormed 8925 4 10797 canonicalCompare12Program
    (by change 8925+4 ≤ Artifact.instructions.length
        exact Nat.le_trans (by decide : 8925+4 ≤ 9184)
          (Nat.le_of_eq Artifact.instructionCount.symm))
    (by rw [PCFast.instructionPC_eq_byteLength]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)
def canonicalCompare12JumpBlock : Block Artifact.artifact .Osaka 10803 jumpiProgram :=
  WindowTwentyOneSlice.block Artifact.wellFormed 8929 1 10803 jumpiProgram
    (by change 8929+1 ≤ Artifact.instructions.length
        exact Nat.le_trans (by decide : 8929+1 ≤ 9184)
          (Nat.le_of_eq Artifact.instructionCount.symm))
    (by rw [PCFast.instructionPC_eq_byteLength]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)
def canonicalCompare13Block : Block Artifact.artifact .Osaka 10804 canonicalCompare13Program :=
  WindowTwentyOneSlice.block Artifact.wellFormed 8930 4 10804 canonicalCompare13Program
    (by change 8930+4 ≤ Artifact.instructions.length
        exact Nat.le_trans (by decide : 8930+4 ≤ 9184)
          (Nat.le_of_eq Artifact.instructionCount.symm))
    (by rw [PCFast.instructionPC_eq_byteLength]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)
def canonicalCompare13JumpBlock : Block Artifact.artifact .Osaka 10810 jumpiProgram :=
  WindowTwentyOneSlice.block Artifact.wellFormed 8934 1 10810 jumpiProgram
    (by change 8934+1 ≤ Artifact.instructions.length
        exact Nat.le_trans (by decide : 8934+1 ≤ 9184)
          (Nat.le_of_eq Artifact.instructionCount.symm))
    (by rw [PCFast.instructionPC_eq_byteLength]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)
def canonicalCompare14Block : Block Artifact.artifact .Osaka 10811 canonicalCompare14Program :=
  WindowTwentyOneSlice.block Artifact.wellFormed 8935 5 10811 canonicalCompare14Program
    (by change 8935+5 ≤ Artifact.instructions.length
        exact Nat.le_trans (by decide : 8935+5 ≤ 9184)
          (Nat.le_of_eq Artifact.instructionCount.symm))
    (by rw [PCFast.instructionPC_eq_byteLength]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)
def canonicalCompare14JumpBlock : Block Artifact.artifact .Osaka 10820 jumpiProgram :=
  WindowTwentyOneSlice.block Artifact.wellFormed 8940 1 10820 jumpiProgram
    (by change 8940+1 ≤ Artifact.instructions.length
        exact Nat.le_trans (by decide : 8940+1 ≤ 9184)
          (Nat.le_of_eq Artifact.instructionCount.symm))
    (by rw [PCFast.instructionPC_eq_byteLength]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)
def canonicalCompare15Block : Block Artifact.artifact .Osaka 10821 canonicalCompare15Program :=
  WindowTwentyOneSlice.block Artifact.wellFormed 8941 5 10821 canonicalCompare15Program
    (by change 8941+5 ≤ Artifact.instructions.length
        exact Nat.le_trans (by decide : 8941+5 ≤ 9184)
          (Nat.le_of_eq Artifact.instructionCount.symm))
    (by rw [PCFast.instructionPC_eq_byteLength]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)
def canonicalCompare15JumpBlock : Block Artifact.artifact .Osaka 10830 jumpiProgram :=
  WindowTwentyOneSlice.block Artifact.wellFormed 8946 1 10830 jumpiProgram
    (by change 8946+1 ≤ Artifact.instructions.length
        exact Nat.le_trans (by decide : 8946+1 ≤ 9184)
          (Nat.le_of_eq Artifact.instructionCount.symm))
    (by rw [PCFast.instructionPC_eq_byteLength]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)
def canonicalCompare16Block : Block Artifact.artifact .Osaka 10831 canonicalCompare16Program :=
  WindowTwentyOneSlice.block Artifact.wellFormed 8947 6 10831 canonicalCompare16Program
    (by change 8947+6 ≤ Artifact.instructions.length
        exact Nat.le_trans (by decide : 8947+6 ≤ 9184)
          (Nat.le_of_eq Artifact.instructionCount.symm))
    (by rw [PCFast.instructionPC_eq_byteLength]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)
def canonicalCompare16JumpBlock : Block Artifact.artifact .Osaka 10843 jumpiProgram :=
  WindowTwentyOneSlice.block Artifact.wellFormed 8953 1 10843 jumpiProgram
    (by change 8953+1 ≤ Artifact.instructions.length
        exact Nat.le_trans (by decide : 8953+1 ≤ 9184)
          (Nat.le_of_eq Artifact.instructionCount.symm))
    (by rw [PCFast.instructionPC_eq_byteLength]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)
def canonicalCompare17Block : Block Artifact.artifact .Osaka 10844 canonicalCompare17Program :=
  WindowTwentyOneSlice.block Artifact.wellFormed 8954 6 10844 canonicalCompare17Program
    (by change 8954+6 ≤ Artifact.instructions.length
        exact Nat.le_trans (by decide : 8954+6 ≤ 9184)
          (Nat.le_of_eq Artifact.instructionCount.symm))
    (by rw [PCFast.instructionPC_eq_byteLength]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)
def canonicalCompare17JumpBlock : Block Artifact.artifact .Osaka 10856 jumpiProgram :=
  WindowTwentyOneSlice.block Artifact.wellFormed 8960 1 10856 jumpiProgram
    (by change 8960+1 ≤ Artifact.instructions.length
        exact Nat.le_trans (by decide : 8960+1 ≤ 9184)
          (Nat.le_of_eq Artifact.instructionCount.symm))
    (by rw [PCFast.instructionPC_eq_byteLength]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)
def canonicalJumpBlock : Block Artifact.artifact .Osaka 10866 jumpProgram :=
  WindowTwentyOneSlice.block Artifact.wellFormed 8966 1 10866 jumpProgram
    (by change 8966+1 ≤ Artifact.instructions.length
        exact Nat.le_trans (by decide : 8966+1 ≤ 9184)
          (Nat.le_of_eq Artifact.instructionCount.symm))
    (by rw [PCFast.instructionPC_eq_byteLength]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)
theorem validJump10857 : Decode.isValidJumpDest Artifact.bytecode 10857 = true := by
  have h := ProgramArtifact.isValidJumpDest_index Artifact.artifact 8961
    (show Artifact.instructions[8961]? = some (.op .JUMPDEST) by rfl)
  have hp : Artifact.artifact.instructionPC 8961 = 10857 := by
    rw [PCFast.instructionPC_eq_byteLength]; rfl
  rw [hp] at h
  exact h
theorem validJump10867 : Decode.isValidJumpDest Artifact.bytecode 10867 = true := by
  have h := ProgramArtifact.isValidJumpDest_index Artifact.artifact 8967
    (show Artifact.instructions[8967]? = some (.op .JUMPDEST) by rfl)
  have hp : Artifact.artifact.instructionPC 8967 = 10867 := by
    rw [PCFast.instructionPC_eq_byteLength]; rfl
  rw [hp] at h
  exact h
theorem validJump11014 : Decode.isValidJumpDest Artifact.bytecode 11014 = true := by
  have h := ProgramArtifact.isValidJumpDest_index Artifact.artifact 9062
    (show Artifact.instructions[9062]? = some (.op .JUMPDEST) by rfl)
  have hp : Artifact.artifact.instructionPC 9062 = 11014 := by
    rw [PCFast.instructionPC_eq_byteLength]; rfl
  rw [hp] at h
  exact h
end CycleSubmission.FinalBlocks
