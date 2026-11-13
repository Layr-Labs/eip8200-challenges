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
def unpackFinalBlock : Block Artifact.artifact .Osaka 7526 unpackFinalProgram :=
  WindowTwentyOneSlice.block CycleSubmission.Artifact.wellFormed 5812 54 7526 unpackFinalProgram
    (by change 5812 + 54 ≤ CycleSubmission.Artifact.instructions.length; rw [CycleSubmission.Artifact.instructionCount]; decide)
    (by rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)
def canonicalsubBlock : Block Artifact.artifact .Osaka 10202 canonicalsubProgram :=
  WindowTwentyOneSlice.block CycleSubmission.Artifact.wellFormed 8011 5 10202 canonicalsubProgram
    (by change 8011 + 5 ≤ CycleSubmission.Artifact.instructions.length; rw [CycleSubmission.Artifact.instructionCount]; decide)
    (by rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)
def packFinalBlock : Block Artifact.artifact .Osaka 10212 packFinalProgram :=
  WindowTwentyOneSlice.block CycleSubmission.Artifact.wellFormed 8017 82 10212 packFinalProgram
    (by change 8017 + 82 ≤ CycleSubmission.Artifact.instructions.length; rw [CycleSubmission.Artifact.instructionCount]; decide)
    (by rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)
def canonicalCompare0Block : Block Artifact.artifact .Osaka 10041 canonicalCompare0Program :=
  WindowTwentyOneSlice.block CycleSubmission.Artifact.wellFormed 7906 4 10041 canonicalCompare0Program
    (by change 7906 + 4 ≤ CycleSubmission.Artifact.instructions.length; rw [CycleSubmission.Artifact.instructionCount]; decide)
    (by rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)
def canonicalCompare0JumpBlock : Block Artifact.artifact .Osaka 10047 jumpiProgram :=
  WindowTwentyOneSlice.block CycleSubmission.Artifact.wellFormed 7910 1 10047 jumpiProgram
    (by change 7910 + 1 ≤ CycleSubmission.Artifact.instructions.length; rw [CycleSubmission.Artifact.instructionCount]; decide)
    (by rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)
def canonicalCompare1Block : Block Artifact.artifact .Osaka 10048 canonicalCompare1Program :=
  WindowTwentyOneSlice.block CycleSubmission.Artifact.wellFormed 7911 4 10048 canonicalCompare1Program
    (by change 7911 + 4 ≤ CycleSubmission.Artifact.instructions.length; rw [CycleSubmission.Artifact.instructionCount]; decide)
    (by rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)
def canonicalCompare1JumpBlock : Block Artifact.artifact .Osaka 10054 jumpiProgram :=
  WindowTwentyOneSlice.block CycleSubmission.Artifact.wellFormed 7915 1 10054 jumpiProgram
    (by change 7915 + 1 ≤ CycleSubmission.Artifact.instructions.length; rw [CycleSubmission.Artifact.instructionCount]; decide)
    (by rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)
def canonicalCompare2Block : Block Artifact.artifact .Osaka 10055 canonicalCompare2Program :=
  WindowTwentyOneSlice.block CycleSubmission.Artifact.wellFormed 7916 5 10055 canonicalCompare2Program
    (by change 7916 + 5 ≤ CycleSubmission.Artifact.instructions.length; rw [CycleSubmission.Artifact.instructionCount]; decide)
    (by rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)
def canonicalCompare2JumpBlock : Block Artifact.artifact .Osaka 10063 jumpiProgram :=
  WindowTwentyOneSlice.block CycleSubmission.Artifact.wellFormed 7921 1 10063 jumpiProgram
    (by change 7921 + 1 ≤ CycleSubmission.Artifact.instructions.length; rw [CycleSubmission.Artifact.instructionCount]; decide)
    (by rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)
def canonicalCompare3Block : Block Artifact.artifact .Osaka 10064 canonicalCompare3Program :=
  WindowTwentyOneSlice.block CycleSubmission.Artifact.wellFormed 7922 5 10064 canonicalCompare3Program
    (by change 7922 + 5 ≤ CycleSubmission.Artifact.instructions.length; rw [CycleSubmission.Artifact.instructionCount]; decide)
    (by rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)
def canonicalCompare3JumpBlock : Block Artifact.artifact .Osaka 10072 jumpiProgram :=
  WindowTwentyOneSlice.block CycleSubmission.Artifact.wellFormed 7927 1 10072 jumpiProgram
    (by change 7927 + 1 ≤ CycleSubmission.Artifact.instructions.length; rw [CycleSubmission.Artifact.instructionCount]; decide)
    (by rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)
def canonicalCompare4Block : Block Artifact.artifact .Osaka 10073 canonicalCompare4Program :=
  WindowTwentyOneSlice.block CycleSubmission.Artifact.wellFormed 7928 5 10073 canonicalCompare4Program
    (by change 7928 + 5 ≤ CycleSubmission.Artifact.instructions.length; rw [CycleSubmission.Artifact.instructionCount]; decide)
    (by rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)
def canonicalCompare4JumpBlock : Block Artifact.artifact .Osaka 10081 jumpiProgram :=
  WindowTwentyOneSlice.block CycleSubmission.Artifact.wellFormed 7933 1 10081 jumpiProgram
    (by change 7933 + 1 ≤ CycleSubmission.Artifact.instructions.length; rw [CycleSubmission.Artifact.instructionCount]; decide)
    (by rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)
def canonicalCompare5Block : Block Artifact.artifact .Osaka 10082 canonicalCompare5Program :=
  WindowTwentyOneSlice.block CycleSubmission.Artifact.wellFormed 7934 5 10082 canonicalCompare5Program
    (by change 7934 + 5 ≤ CycleSubmission.Artifact.instructions.length; rw [CycleSubmission.Artifact.instructionCount]; decide)
    (by rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)
def canonicalCompare5JumpBlock : Block Artifact.artifact .Osaka 10090 jumpiProgram :=
  WindowTwentyOneSlice.block CycleSubmission.Artifact.wellFormed 7939 1 10090 jumpiProgram
    (by change 7939 + 1 ≤ CycleSubmission.Artifact.instructions.length; rw [CycleSubmission.Artifact.instructionCount]; decide)
    (by rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)
def canonicalCompare6Block : Block Artifact.artifact .Osaka 10091 canonicalCompare6Program :=
  WindowTwentyOneSlice.block CycleSubmission.Artifact.wellFormed 7940 5 10091 canonicalCompare6Program
    (by change 7940 + 5 ≤ CycleSubmission.Artifact.instructions.length; rw [CycleSubmission.Artifact.instructionCount]; decide)
    (by rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)
def canonicalCompare6JumpBlock : Block Artifact.artifact .Osaka 10099 jumpiProgram :=
  WindowTwentyOneSlice.block CycleSubmission.Artifact.wellFormed 7945 1 10099 jumpiProgram
    (by change 7945 + 1 ≤ CycleSubmission.Artifact.instructions.length; rw [CycleSubmission.Artifact.instructionCount]; decide)
    (by rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)
def canonicalCompare7Block : Block Artifact.artifact .Osaka 10100 canonicalCompare7Program :=
  WindowTwentyOneSlice.block CycleSubmission.Artifact.wellFormed 7946 5 10100 canonicalCompare7Program
    (by change 7946 + 5 ≤ CycleSubmission.Artifact.instructions.length; rw [CycleSubmission.Artifact.instructionCount]; decide)
    (by rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)
def canonicalCompare7JumpBlock : Block Artifact.artifact .Osaka 10108 jumpiProgram :=
  WindowTwentyOneSlice.block CycleSubmission.Artifact.wellFormed 7951 1 10108 jumpiProgram
    (by change 7951 + 1 ≤ CycleSubmission.Artifact.instructions.length; rw [CycleSubmission.Artifact.instructionCount]; decide)
    (by rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)
def canonicalCompare8Block : Block Artifact.artifact .Osaka 10109 canonicalCompare8Program :=
  WindowTwentyOneSlice.block CycleSubmission.Artifact.wellFormed 7952 5 10109 canonicalCompare8Program
    (by change 7952 + 5 ≤ CycleSubmission.Artifact.instructions.length; rw [CycleSubmission.Artifact.instructionCount]; decide)
    (by rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)
def canonicalCompare8JumpBlock : Block Artifact.artifact .Osaka 10117 jumpiProgram :=
  WindowTwentyOneSlice.block CycleSubmission.Artifact.wellFormed 7957 1 10117 jumpiProgram
    (by change 7957 + 1 ≤ CycleSubmission.Artifact.instructions.length; rw [CycleSubmission.Artifact.instructionCount]; decide)
    (by rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)
def canonicalCompare9Block : Block Artifact.artifact .Osaka 10118 canonicalCompare9Program :=
  WindowTwentyOneSlice.block CycleSubmission.Artifact.wellFormed 7958 5 10118 canonicalCompare9Program
    (by change 7958 + 5 ≤ CycleSubmission.Artifact.instructions.length; rw [CycleSubmission.Artifact.instructionCount]; decide)
    (by rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)
def canonicalCompare9JumpBlock : Block Artifact.artifact .Osaka 10126 jumpiProgram :=
  WindowTwentyOneSlice.block CycleSubmission.Artifact.wellFormed 7963 1 10126 jumpiProgram
    (by change 7963 + 1 ≤ CycleSubmission.Artifact.instructions.length; rw [CycleSubmission.Artifact.instructionCount]; decide)
    (by rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)
def canonicalCompare10Block : Block Artifact.artifact .Osaka 10127 canonicalCompare10Program :=
  WindowTwentyOneSlice.block CycleSubmission.Artifact.wellFormed 7964 5 10127 canonicalCompare10Program
    (by change 7964 + 5 ≤ CycleSubmission.Artifact.instructions.length; rw [CycleSubmission.Artifact.instructionCount]; decide)
    (by rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)
def canonicalCompare10JumpBlock : Block Artifact.artifact .Osaka 10135 jumpiProgram :=
  WindowTwentyOneSlice.block CycleSubmission.Artifact.wellFormed 7969 1 10135 jumpiProgram
    (by change 7969 + 1 ≤ CycleSubmission.Artifact.instructions.length; rw [CycleSubmission.Artifact.instructionCount]; decide)
    (by rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)
def canonicalCompare11Block : Block Artifact.artifact .Osaka 10136 canonicalCompare11Program :=
  WindowTwentyOneSlice.block CycleSubmission.Artifact.wellFormed 7970 5 10136 canonicalCompare11Program
    (by change 7970 + 5 ≤ CycleSubmission.Artifact.instructions.length; rw [CycleSubmission.Artifact.instructionCount]; decide)
    (by rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)
def canonicalCompare11JumpBlock : Block Artifact.artifact .Osaka 10144 jumpiProgram :=
  WindowTwentyOneSlice.block CycleSubmission.Artifact.wellFormed 7975 1 10144 jumpiProgram
    (by change 7975 + 1 ≤ CycleSubmission.Artifact.instructions.length; rw [CycleSubmission.Artifact.instructionCount]; decide)
    (by rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)
def canonicalCompare12Block : Block Artifact.artifact .Osaka 10145 canonicalCompare12Program :=
  WindowTwentyOneSlice.block CycleSubmission.Artifact.wellFormed 7976 4 10145 canonicalCompare12Program
    (by change 7976 + 4 ≤ CycleSubmission.Artifact.instructions.length; rw [CycleSubmission.Artifact.instructionCount]; decide)
    (by rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)
def canonicalCompare12JumpBlock : Block Artifact.artifact .Osaka 10151 jumpiProgram :=
  WindowTwentyOneSlice.block CycleSubmission.Artifact.wellFormed 7980 1 10151 jumpiProgram
    (by change 7980 + 1 ≤ CycleSubmission.Artifact.instructions.length; rw [CycleSubmission.Artifact.instructionCount]; decide)
    (by rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)
def canonicalCompare13Block : Block Artifact.artifact .Osaka 10152 canonicalCompare13Program :=
  WindowTwentyOneSlice.block CycleSubmission.Artifact.wellFormed 7981 4 10152 canonicalCompare13Program
    (by change 7981 + 4 ≤ CycleSubmission.Artifact.instructions.length; rw [CycleSubmission.Artifact.instructionCount]; decide)
    (by rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)
def canonicalCompare13JumpBlock : Block Artifact.artifact .Osaka 10158 jumpiProgram :=
  WindowTwentyOneSlice.block CycleSubmission.Artifact.wellFormed 7985 1 10158 jumpiProgram
    (by change 7985 + 1 ≤ CycleSubmission.Artifact.instructions.length; rw [CycleSubmission.Artifact.instructionCount]; decide)
    (by rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)
def canonicalCompare14Block : Block Artifact.artifact .Osaka 10159 canonicalCompare14Program :=
  WindowTwentyOneSlice.block CycleSubmission.Artifact.wellFormed 7986 5 10159 canonicalCompare14Program
    (by change 7986 + 5 ≤ CycleSubmission.Artifact.instructions.length; rw [CycleSubmission.Artifact.instructionCount]; decide)
    (by rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)
def canonicalCompare14JumpBlock : Block Artifact.artifact .Osaka 10168 jumpiProgram :=
  WindowTwentyOneSlice.block CycleSubmission.Artifact.wellFormed 7991 1 10168 jumpiProgram
    (by change 7991 + 1 ≤ CycleSubmission.Artifact.instructions.length; rw [CycleSubmission.Artifact.instructionCount]; decide)
    (by rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)
def canonicalCompare15Block : Block Artifact.artifact .Osaka 10169 canonicalCompare15Program :=
  WindowTwentyOneSlice.block CycleSubmission.Artifact.wellFormed 7992 5 10169 canonicalCompare15Program
    (by change 7992 + 5 ≤ CycleSubmission.Artifact.instructions.length; rw [CycleSubmission.Artifact.instructionCount]; decide)
    (by rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)
def canonicalCompare15JumpBlock : Block Artifact.artifact .Osaka 10178 jumpiProgram :=
  WindowTwentyOneSlice.block CycleSubmission.Artifact.wellFormed 7997 1 10178 jumpiProgram
    (by change 7997 + 1 ≤ CycleSubmission.Artifact.instructions.length; rw [CycleSubmission.Artifact.instructionCount]; decide)
    (by rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)
def canonicalCompare16Block : Block Artifact.artifact .Osaka 10179 canonicalCompare16Program :=
  WindowTwentyOneSlice.block CycleSubmission.Artifact.wellFormed 7998 6 10179 canonicalCompare16Program
    (by change 7998 + 6 ≤ CycleSubmission.Artifact.instructions.length; rw [CycleSubmission.Artifact.instructionCount]; decide)
    (by rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)
def canonicalCompare16JumpBlock : Block Artifact.artifact .Osaka 10191 jumpiProgram :=
  WindowTwentyOneSlice.block CycleSubmission.Artifact.wellFormed 8004 1 10191 jumpiProgram
    (by change 8004 + 1 ≤ CycleSubmission.Artifact.instructions.length; rw [CycleSubmission.Artifact.instructionCount]; decide)
    (by rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)
def canonicalCompare17Block : Block Artifact.artifact .Osaka 10192 canonicalCompare17Program :=
  WindowTwentyOneSlice.block CycleSubmission.Artifact.wellFormed 8005 6 10192 canonicalCompare17Program
    (by change 8005 + 6 ≤ CycleSubmission.Artifact.instructions.length; rw [CycleSubmission.Artifact.instructionCount]; decide)
    (by rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)
def canonicalJumpBlock : Block Artifact.artifact .Osaka 10211 jumpProgram :=
  WindowTwentyOneSlice.block CycleSubmission.Artifact.wellFormed 8016 1 10211 jumpProgram
    (by change 8016 + 1 ≤ CycleSubmission.Artifact.instructions.length; rw [CycleSubmission.Artifact.instructionCount]; decide)
    (by rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)
theorem validJump10857 : Decode.isValidJumpDest Artifact.bytecode 10202 = true := by
  have h := ProgramArtifact.isValidJumpDest_index Artifact.artifact 8011
    (show Artifact.instructions[8011]? = some (.op .JUMPDEST) by rfl)
  have hp : Artifact.artifact.instructionPC 8011 = 10202 := by
    rw [PCFast.instructionPC_eq_byteLength]; rfl
  rw [hp] at h
  exact h
theorem validJump10867 : Decode.isValidJumpDest Artifact.bytecode 10212 = true := by
  have h := ProgramArtifact.isValidJumpDest_index Artifact.artifact 8017
    (show Artifact.instructions[8017]? = some (.op .JUMPDEST) by rfl)
  have hp : Artifact.artifact.instructionPC 8017 = 10212 := by
    rw [PCFast.instructionPC_eq_byteLength]; rfl
  rw [hp] at h
  exact h
theorem validJump11014 : Decode.isValidJumpDest Artifact.bytecode 10349 = true := by
  have h := ProgramArtifact.isValidJumpDest_index Artifact.artifact 8105
    (show Artifact.instructions[8105]? = some (.op .JUMPDEST) by rfl)
  have hp : Artifact.artifact.instructionPC 8105 = 10349 := by
    rw [PCFast.instructionPC_eq_byteLength]; rfl
  rw [hp] at h
  exact h
end CycleSubmission.FinalBlocks
