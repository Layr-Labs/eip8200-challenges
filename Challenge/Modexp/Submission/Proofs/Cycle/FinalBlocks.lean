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
def unpackFinalBlock : Block Artifact.artifact .Osaka 7678 unpackFinalProgram :=
  WindowTwentyOneSlice.block CycleSubmission.Artifact.wellFormed 5809 54 7678 unpackFinalProgram
    (by change 5809 + 54 ≤ CycleSubmission.Artifact.instructions.length; rw [CycleSubmission.Artifact.instructionCount]; decide)
    (by rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)
def canonicalsubBlock : Block Artifact.artifact .Osaka 10354 canonicalsubProgram :=
  WindowTwentyOneSlice.block CycleSubmission.Artifact.wellFormed 8008 5 10354 canonicalsubProgram
    (by change 8008 + 5 ≤ CycleSubmission.Artifact.instructions.length; rw [CycleSubmission.Artifact.instructionCount]; decide)
    (by rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)
def packFinalBlock : Block Artifact.artifact .Osaka 10364 packFinalProgram :=
  WindowTwentyOneSlice.block CycleSubmission.Artifact.wellFormed 8014 82 10364 packFinalProgram
    (by change 8014 + 82 ≤ CycleSubmission.Artifact.instructions.length; rw [CycleSubmission.Artifact.instructionCount]; decide)
    (by rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)
def canonicalCompare0Block : Block Artifact.artifact .Osaka 10193 canonicalCompare0Program :=
  WindowTwentyOneSlice.block CycleSubmission.Artifact.wellFormed 7903 4 10193 canonicalCompare0Program
    (by change 7903 + 4 ≤ CycleSubmission.Artifact.instructions.length; rw [CycleSubmission.Artifact.instructionCount]; decide)
    (by rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)
def canonicalCompare0JumpBlock : Block Artifact.artifact .Osaka 10199 jumpiProgram :=
  WindowTwentyOneSlice.block CycleSubmission.Artifact.wellFormed 7907 1 10199 jumpiProgram
    (by change 7907 + 1 ≤ CycleSubmission.Artifact.instructions.length; rw [CycleSubmission.Artifact.instructionCount]; decide)
    (by rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)
def canonicalCompare1Block : Block Artifact.artifact .Osaka 10200 canonicalCompare1Program :=
  WindowTwentyOneSlice.block CycleSubmission.Artifact.wellFormed 7908 4 10200 canonicalCompare1Program
    (by change 7908 + 4 ≤ CycleSubmission.Artifact.instructions.length; rw [CycleSubmission.Artifact.instructionCount]; decide)
    (by rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)
def canonicalCompare1JumpBlock : Block Artifact.artifact .Osaka 10206 jumpiProgram :=
  WindowTwentyOneSlice.block CycleSubmission.Artifact.wellFormed 7912 1 10206 jumpiProgram
    (by change 7912 + 1 ≤ CycleSubmission.Artifact.instructions.length; rw [CycleSubmission.Artifact.instructionCount]; decide)
    (by rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)
def canonicalCompare2Block : Block Artifact.artifact .Osaka 10207 canonicalCompare2Program :=
  WindowTwentyOneSlice.block CycleSubmission.Artifact.wellFormed 7913 5 10207 canonicalCompare2Program
    (by change 7913 + 5 ≤ CycleSubmission.Artifact.instructions.length; rw [CycleSubmission.Artifact.instructionCount]; decide)
    (by rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)
def canonicalCompare2JumpBlock : Block Artifact.artifact .Osaka 10215 jumpiProgram :=
  WindowTwentyOneSlice.block CycleSubmission.Artifact.wellFormed 7918 1 10215 jumpiProgram
    (by change 7918 + 1 ≤ CycleSubmission.Artifact.instructions.length; rw [CycleSubmission.Artifact.instructionCount]; decide)
    (by rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)
def canonicalCompare3Block : Block Artifact.artifact .Osaka 10216 canonicalCompare3Program :=
  WindowTwentyOneSlice.block CycleSubmission.Artifact.wellFormed 7919 5 10216 canonicalCompare3Program
    (by change 7919 + 5 ≤ CycleSubmission.Artifact.instructions.length; rw [CycleSubmission.Artifact.instructionCount]; decide)
    (by rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)
def canonicalCompare3JumpBlock : Block Artifact.artifact .Osaka 10224 jumpiProgram :=
  WindowTwentyOneSlice.block CycleSubmission.Artifact.wellFormed 7924 1 10224 jumpiProgram
    (by change 7924 + 1 ≤ CycleSubmission.Artifact.instructions.length; rw [CycleSubmission.Artifact.instructionCount]; decide)
    (by rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)
def canonicalCompare4Block : Block Artifact.artifact .Osaka 10225 canonicalCompare4Program :=
  WindowTwentyOneSlice.block CycleSubmission.Artifact.wellFormed 7925 5 10225 canonicalCompare4Program
    (by change 7925 + 5 ≤ CycleSubmission.Artifact.instructions.length; rw [CycleSubmission.Artifact.instructionCount]; decide)
    (by rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)
def canonicalCompare4JumpBlock : Block Artifact.artifact .Osaka 10233 jumpiProgram :=
  WindowTwentyOneSlice.block CycleSubmission.Artifact.wellFormed 7930 1 10233 jumpiProgram
    (by change 7930 + 1 ≤ CycleSubmission.Artifact.instructions.length; rw [CycleSubmission.Artifact.instructionCount]; decide)
    (by rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)
def canonicalCompare5Block : Block Artifact.artifact .Osaka 10234 canonicalCompare5Program :=
  WindowTwentyOneSlice.block CycleSubmission.Artifact.wellFormed 7931 5 10234 canonicalCompare5Program
    (by change 7931 + 5 ≤ CycleSubmission.Artifact.instructions.length; rw [CycleSubmission.Artifact.instructionCount]; decide)
    (by rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)
def canonicalCompare5JumpBlock : Block Artifact.artifact .Osaka 10242 jumpiProgram :=
  WindowTwentyOneSlice.block CycleSubmission.Artifact.wellFormed 7936 1 10242 jumpiProgram
    (by change 7936 + 1 ≤ CycleSubmission.Artifact.instructions.length; rw [CycleSubmission.Artifact.instructionCount]; decide)
    (by rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)
def canonicalCompare6Block : Block Artifact.artifact .Osaka 10243 canonicalCompare6Program :=
  WindowTwentyOneSlice.block CycleSubmission.Artifact.wellFormed 7937 5 10243 canonicalCompare6Program
    (by change 7937 + 5 ≤ CycleSubmission.Artifact.instructions.length; rw [CycleSubmission.Artifact.instructionCount]; decide)
    (by rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)
def canonicalCompare6JumpBlock : Block Artifact.artifact .Osaka 10251 jumpiProgram :=
  WindowTwentyOneSlice.block CycleSubmission.Artifact.wellFormed 7942 1 10251 jumpiProgram
    (by change 7942 + 1 ≤ CycleSubmission.Artifact.instructions.length; rw [CycleSubmission.Artifact.instructionCount]; decide)
    (by rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)
def canonicalCompare7Block : Block Artifact.artifact .Osaka 10252 canonicalCompare7Program :=
  WindowTwentyOneSlice.block CycleSubmission.Artifact.wellFormed 7943 5 10252 canonicalCompare7Program
    (by change 7943 + 5 ≤ CycleSubmission.Artifact.instructions.length; rw [CycleSubmission.Artifact.instructionCount]; decide)
    (by rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)
def canonicalCompare7JumpBlock : Block Artifact.artifact .Osaka 10260 jumpiProgram :=
  WindowTwentyOneSlice.block CycleSubmission.Artifact.wellFormed 7948 1 10260 jumpiProgram
    (by change 7948 + 1 ≤ CycleSubmission.Artifact.instructions.length; rw [CycleSubmission.Artifact.instructionCount]; decide)
    (by rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)
def canonicalCompare8Block : Block Artifact.artifact .Osaka 10261 canonicalCompare8Program :=
  WindowTwentyOneSlice.block CycleSubmission.Artifact.wellFormed 7949 5 10261 canonicalCompare8Program
    (by change 7949 + 5 ≤ CycleSubmission.Artifact.instructions.length; rw [CycleSubmission.Artifact.instructionCount]; decide)
    (by rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)
def canonicalCompare8JumpBlock : Block Artifact.artifact .Osaka 10269 jumpiProgram :=
  WindowTwentyOneSlice.block CycleSubmission.Artifact.wellFormed 7954 1 10269 jumpiProgram
    (by change 7954 + 1 ≤ CycleSubmission.Artifact.instructions.length; rw [CycleSubmission.Artifact.instructionCount]; decide)
    (by rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)
def canonicalCompare9Block : Block Artifact.artifact .Osaka 10270 canonicalCompare9Program :=
  WindowTwentyOneSlice.block CycleSubmission.Artifact.wellFormed 7955 5 10270 canonicalCompare9Program
    (by change 7955 + 5 ≤ CycleSubmission.Artifact.instructions.length; rw [CycleSubmission.Artifact.instructionCount]; decide)
    (by rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)
def canonicalCompare9JumpBlock : Block Artifact.artifact .Osaka 10278 jumpiProgram :=
  WindowTwentyOneSlice.block CycleSubmission.Artifact.wellFormed 7960 1 10278 jumpiProgram
    (by change 7960 + 1 ≤ CycleSubmission.Artifact.instructions.length; rw [CycleSubmission.Artifact.instructionCount]; decide)
    (by rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)
def canonicalCompare10Block : Block Artifact.artifact .Osaka 10279 canonicalCompare10Program :=
  WindowTwentyOneSlice.block CycleSubmission.Artifact.wellFormed 7961 5 10279 canonicalCompare10Program
    (by change 7961 + 5 ≤ CycleSubmission.Artifact.instructions.length; rw [CycleSubmission.Artifact.instructionCount]; decide)
    (by rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)
def canonicalCompare10JumpBlock : Block Artifact.artifact .Osaka 10287 jumpiProgram :=
  WindowTwentyOneSlice.block CycleSubmission.Artifact.wellFormed 7966 1 10287 jumpiProgram
    (by change 7966 + 1 ≤ CycleSubmission.Artifact.instructions.length; rw [CycleSubmission.Artifact.instructionCount]; decide)
    (by rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)
def canonicalCompare11Block : Block Artifact.artifact .Osaka 10288 canonicalCompare11Program :=
  WindowTwentyOneSlice.block CycleSubmission.Artifact.wellFormed 7967 5 10288 canonicalCompare11Program
    (by change 7967 + 5 ≤ CycleSubmission.Artifact.instructions.length; rw [CycleSubmission.Artifact.instructionCount]; decide)
    (by rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)
def canonicalCompare11JumpBlock : Block Artifact.artifact .Osaka 10296 jumpiProgram :=
  WindowTwentyOneSlice.block CycleSubmission.Artifact.wellFormed 7972 1 10296 jumpiProgram
    (by change 7972 + 1 ≤ CycleSubmission.Artifact.instructions.length; rw [CycleSubmission.Artifact.instructionCount]; decide)
    (by rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)
def canonicalCompare12Block : Block Artifact.artifact .Osaka 10297 canonicalCompare12Program :=
  WindowTwentyOneSlice.block CycleSubmission.Artifact.wellFormed 7973 4 10297 canonicalCompare12Program
    (by change 7973 + 4 ≤ CycleSubmission.Artifact.instructions.length; rw [CycleSubmission.Artifact.instructionCount]; decide)
    (by rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)
def canonicalCompare12JumpBlock : Block Artifact.artifact .Osaka 10303 jumpiProgram :=
  WindowTwentyOneSlice.block CycleSubmission.Artifact.wellFormed 7977 1 10303 jumpiProgram
    (by change 7977 + 1 ≤ CycleSubmission.Artifact.instructions.length; rw [CycleSubmission.Artifact.instructionCount]; decide)
    (by rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)
def canonicalCompare13Block : Block Artifact.artifact .Osaka 10304 canonicalCompare13Program :=
  WindowTwentyOneSlice.block CycleSubmission.Artifact.wellFormed 7978 4 10304 canonicalCompare13Program
    (by change 7978 + 4 ≤ CycleSubmission.Artifact.instructions.length; rw [CycleSubmission.Artifact.instructionCount]; decide)
    (by rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)
def canonicalCompare13JumpBlock : Block Artifact.artifact .Osaka 10310 jumpiProgram :=
  WindowTwentyOneSlice.block CycleSubmission.Artifact.wellFormed 7982 1 10310 jumpiProgram
    (by change 7982 + 1 ≤ CycleSubmission.Artifact.instructions.length; rw [CycleSubmission.Artifact.instructionCount]; decide)
    (by rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)
def canonicalCompare14Block : Block Artifact.artifact .Osaka 10311 canonicalCompare14Program :=
  WindowTwentyOneSlice.block CycleSubmission.Artifact.wellFormed 7983 5 10311 canonicalCompare14Program
    (by change 7983 + 5 ≤ CycleSubmission.Artifact.instructions.length; rw [CycleSubmission.Artifact.instructionCount]; decide)
    (by rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)
def canonicalCompare14JumpBlock : Block Artifact.artifact .Osaka 10320 jumpiProgram :=
  WindowTwentyOneSlice.block CycleSubmission.Artifact.wellFormed 7988 1 10320 jumpiProgram
    (by change 7988 + 1 ≤ CycleSubmission.Artifact.instructions.length; rw [CycleSubmission.Artifact.instructionCount]; decide)
    (by rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)
def canonicalCompare15Block : Block Artifact.artifact .Osaka 10321 canonicalCompare15Program :=
  WindowTwentyOneSlice.block CycleSubmission.Artifact.wellFormed 7989 5 10321 canonicalCompare15Program
    (by change 7989 + 5 ≤ CycleSubmission.Artifact.instructions.length; rw [CycleSubmission.Artifact.instructionCount]; decide)
    (by rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)
def canonicalCompare15JumpBlock : Block Artifact.artifact .Osaka 10330 jumpiProgram :=
  WindowTwentyOneSlice.block CycleSubmission.Artifact.wellFormed 7994 1 10330 jumpiProgram
    (by change 7994 + 1 ≤ CycleSubmission.Artifact.instructions.length; rw [CycleSubmission.Artifact.instructionCount]; decide)
    (by rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)
def canonicalCompare16Block : Block Artifact.artifact .Osaka 10331 canonicalCompare16Program :=
  WindowTwentyOneSlice.block CycleSubmission.Artifact.wellFormed 7995 6 10331 canonicalCompare16Program
    (by change 7995 + 6 ≤ CycleSubmission.Artifact.instructions.length; rw [CycleSubmission.Artifact.instructionCount]; decide)
    (by rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)
def canonicalCompare16JumpBlock : Block Artifact.artifact .Osaka 10343 jumpiProgram :=
  WindowTwentyOneSlice.block CycleSubmission.Artifact.wellFormed 8001 1 10343 jumpiProgram
    (by change 8001 + 1 ≤ CycleSubmission.Artifact.instructions.length; rw [CycleSubmission.Artifact.instructionCount]; decide)
    (by rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)
def canonicalCompare17Block : Block Artifact.artifact .Osaka 10344 canonicalCompare17Program :=
  WindowTwentyOneSlice.block CycleSubmission.Artifact.wellFormed 8002 6 10344 canonicalCompare17Program
    (by change 8002 + 6 ≤ CycleSubmission.Artifact.instructions.length; rw [CycleSubmission.Artifact.instructionCount]; decide)
    (by rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)
def canonicalJumpBlock : Block Artifact.artifact .Osaka 10363 jumpProgram :=
  WindowTwentyOneSlice.block CycleSubmission.Artifact.wellFormed 8013 1 10363 jumpProgram
    (by change 8013 + 1 ≤ CycleSubmission.Artifact.instructions.length; rw [CycleSubmission.Artifact.instructionCount]; decide)
    (by rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)
theorem validJump10857 : Decode.isValidJumpDest Artifact.bytecode 10354 = true := by
  have h := ProgramArtifact.isValidJumpDest_index Artifact.artifact 8008
    (show Artifact.instructions[8008]? = some (.op .JUMPDEST) by rfl)
  have hp : Artifact.artifact.instructionPC 8008 = 10354 := by
    rw [PCFast.instructionPC_eq_byteLength]; rfl
  rw [hp] at h
  exact h
theorem validJump10867 : Decode.isValidJumpDest Artifact.bytecode 10364 = true := by
  have h := ProgramArtifact.isValidJumpDest_index Artifact.artifact 8014
    (show Artifact.instructions[8014]? = some (.op .JUMPDEST) by rfl)
  have hp : Artifact.artifact.instructionPC 8014 = 10364 := by
    rw [PCFast.instructionPC_eq_byteLength]; rfl
  rw [hp] at h
  exact h
theorem validJump11014 : Decode.isValidJumpDest Artifact.bytecode 10501 = true := by
  have h := ProgramArtifact.isValidJumpDest_index Artifact.artifact 8102
    (show Artifact.instructions[8102]? = some (.op .JUMPDEST) by rfl)
  have hp : Artifact.artifact.instructionPC 8102 = 10501 := by
    rw [PCFast.instructionPC_eq_byteLength]; rfl
  rw [hp] at h
  exact h
end CycleSubmission.FinalBlocks
