import Challenge.Modexp.Submission.Proofs.Bytecode.Artifact
import Challenge.Modexp.Submission.Proofs.Bytecode.WindowTwentyOneSlice

set_option maxRecDepth 40000
set_option maxHeartbeats 4000000
namespace Challenge.Modexp.Submission.Proofs.Fast.ShiftUnrollBindings
open EvmSemantics EvmSemantics.EVM YulEvmCompiler
open Challenge.Modexp.Submission.Proofs.Bytecode WindowNibbleKernel WindowTwentyOneBinding

def cellProgram : List Instr :=
  [.op .JUMPDEST,
   .push 2 832,
   .op (.Dup ⟨1, by decide⟩),
   .op .SUB,
   .op .MLOAD,
   .op (.Dup ⟨2, by decide⟩),
   .op (.Dup ⟨6, by decide⟩),
   .op (.Dup ⟨2, by decide⟩),
   .op .MUL,
   .op (.Swap ⟨1, by decide⟩),
   .op (.Dup ⟨7, by decide⟩),
   .op .MULMOD,
   .op (.Dup ⟨1, by decide⟩),
   .op (.Dup ⟨1, by decide⟩),
   .op .LT,
   .op .SUB,
   .op (.Dup ⟨5, by decide⟩),
   .op (.Dup ⟨2, by decide⟩),
   .op .ADD,
   .op (.Dup ⟨0, by decide⟩),
   .op (.Swap ⟨6, by decide⟩),
   .op .GT,
   .op .SUB,
   .op .SUB,
   .op (.Dup ⟨4, by decide⟩),
   .op (.Dup ⟨2, by decide⟩),
   .op .MLOAD,
   .op .ADD,
   .op (.Dup ⟨0, by decide⟩),
   .op (.Swap ⟨5, by decide⟩),
   .op .GT,
   .op .ADD,
   .op (.Swap ⟨3, by decide⟩),
   .op (.Dup ⟨1, by decide⟩),
   .op .MSTORE,
   .op (.Dup ⟨2, by decide⟩),
   .op .ADD]

def cacheProgram : List Instr :=
  [.op (.Dup { idx := 0 }),
   .push 0 0,
   .op .SUB,
   .push 1 3,
   .op .AND,
   .push 1 39,
   .op .MUL,
   .push 2 3158,
   .op .ADD,
   .push 2 1698,
   .op .MSTORE]

def dispatchProgram : List Instr :=
  [.push 2 1698,
   .op .MLOAD,
   .op .JUMP]

def cell0 : Block Artifact.submissionArtifact .Osaka 3158 cellProgram :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 2347 37 3158 cellProgram
    (by decide) (by rfl) (by rfl) (by decide)

def cell1 : Block Artifact.submissionArtifact .Osaka 3197 cellProgram :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 2384 37 3197 cellProgram
    (by decide) (by rfl) (by rfl) (by decide)

def cell2 : Block Artifact.submissionArtifact .Osaka 3236 cellProgram :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 2421 37 3236 cellProgram
    (by decide) (by rfl) (by rfl) (by decide)

def cell3 : Block Artifact.submissionArtifact .Osaka 3275 cellProgram :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 2458 37 3275 cellProgram
    (by decide) (by rfl) (by rfl) (by decide)

def cache : Block Artifact.submissionArtifact .Osaka 2995 cacheProgram :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 2233 11 2995 cacheProgram
    (by decide) (by rfl) (by rfl) (by decide)

def dispatch : Block Artifact.submissionArtifact .Osaka 3153 dispatchProgram :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 2344 3 3153 dispatchProgram
    (by decide) (by rfl) (by rfl) (by decide)

theorem jump3684 : Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3158 = true :=
  Artifact.isValidJumpDest_index 2347 (by rfl)

theorem jump3723 : Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3197 = true :=
  Artifact.isValidJumpDest_index 2384 (by rfl)

theorem jump3762 : Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3236 = true :=
  Artifact.isValidJumpDest_index 2421 (by rfl)

theorem jump3801 : Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3275 = true :=
  Artifact.isValidJumpDest_index 2458 (by rfl)

#print axioms cell0
#print axioms cache
#print axioms jump3801
end Challenge.Modexp.Submission.Proofs.Fast.ShiftUnrollBindings
