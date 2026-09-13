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
   .push 2 3167,
   .op .ADD,
   .push 2 1698,
   .op .MSTORE]

def dispatchProgram : List Instr :=
  [.push 2 1698,
   .op .MLOAD,
   .op .JUMP]

def cell0 : Block Artifact.submissionArtifact .Osaka 3167 cellProgram :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 2330 37 3167 cellProgram
    (by decide) (by rfl) (by rfl) (by decide)

def cell1 : Block Artifact.submissionArtifact .Osaka 3206 cellProgram :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 2367 37 3206 cellProgram
    (by decide) (by rfl) (by rfl) (by decide)

def cell2 : Block Artifact.submissionArtifact .Osaka 3245 cellProgram :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 2404 37 3245 cellProgram
    (by decide) (by rfl) (by rfl) (by decide)

def cell3 : Block Artifact.submissionArtifact .Osaka 3284 cellProgram :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 2441 37 3284 cellProgram
    (by decide) (by rfl) (by rfl) (by decide)

def cache : Block Artifact.submissionArtifact .Osaka 3031 cacheProgram :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 2236 11 3031 cacheProgram
    (by decide) (by rfl) (by rfl) (by decide)

def dispatch : Block Artifact.submissionArtifact .Osaka 3162 dispatchProgram :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 2327 3 3162 dispatchProgram
    (by decide) (by rfl) (by rfl) (by decide)

theorem jump3684 : Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3167 = true :=
  Artifact.isValidJumpDest_index 2330 (by rfl)

theorem jump3723 : Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3206 = true :=
  Artifact.isValidJumpDest_index 2367 (by rfl)

theorem jump3762 : Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3245 = true :=
  Artifact.isValidJumpDest_index 2404 (by rfl)

theorem jump3801 : Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3284 = true :=
  Artifact.isValidJumpDest_index 2441 (by rfl)

#print axioms cell0
#print axioms cache
#print axioms jump3801
end Challenge.Modexp.Submission.Proofs.Fast.ShiftUnrollBindings
