import Challenge.Modexp.Submission.Proofs.Bytecode.Artifact
import Challenge.Modexp.Submission.Proofs.Bytecode.WindowTwentyOneSlice

set_option maxRecDepth 40000
set_option maxHeartbeats 4000000
namespace Challenge.Modexp.Submission.Proofs.Fast.ShiftUnrollBindings
open EvmSemantics EvmSemantics.EVM YulEvmCompiler
open Challenge.Modexp.Submission.Proofs.Bytecode WindowNibbleKernel WindowTwentyOneBinding

def cellProgram : List Instr :=
  [.op .JUMPDEST,
   .op (.Dup { idx := 0 }),
   .op .MLOAD,
   .push 0 0,
   .op .NOT,
   .op (.Dup { idx := 6 }),
   .op (.Dup { idx := 2 }),
   .op .MUL,
   .op (.Swap { idx := 1 }),
   .op (.Dup { idx := 7 }),
   .op .MULMOD,
   .op (.Dup { idx := 1 }),
   .op (.Dup { idx := 1 }),
   .op .LT,
   .op .SUB,
   .op (.Dup { idx := 5 }),
   .op (.Dup { idx := 2 }),
   .op .ADD,
   .op (.Dup { idx := 0 }),
   .op (.Swap { idx := 6 }),
   .op .GT,
   .op .SUB,
   .op .SUB,
   .op (.Dup { idx := 4 }),
   .op (.Dup { idx := 3 }),
   .op .MLOAD,
   .op .ADD,
   .op (.Dup { idx := 0 }),
   .op (.Swap { idx := 5 }),
   .op .GT,
   .op .ADD,
   .op (.Swap { idx := 3 }),
   .op (.Dup { idx := 2 }),
   .op (.Dup { idx := 4 }),
   .op .ADD,
   .op (.Swap { idx := 2 }),
   .op .MSTORE,
   .op (.Dup { idx := 2 }),
   .op .ADD]

def cacheProgram : List Instr :=
  [.op (.Dup { idx := 0 }),
   .push 0 0,
   .op .SUB,
   .push 1 3,
   .op .AND,
   .push 1 39,
   .op .MUL,
   .push 2 3684,
   .op .ADD,
   .push 2 6304,
   .op .MSTORE]

def dispatchProgram : List Instr :=
  [.push 2 6304,
   .op .MLOAD,
   .op .JUMP]

def cell0 : Block Artifact.submissionArtifact .Osaka 3684 cellProgram :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 2802 39 3684 cellProgram
    (by decide) (by rfl) (by rfl) (by decide)

def cell1 : Block Artifact.submissionArtifact .Osaka 3723 cellProgram :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 2841 39 3723 cellProgram
    (by decide) (by rfl) (by rfl) (by decide)

def cell2 : Block Artifact.submissionArtifact .Osaka 3762 cellProgram :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 2880 39 3762 cellProgram
    (by decide) (by rfl) (by rfl) (by decide)

def cell3 : Block Artifact.submissionArtifact .Osaka 3801 cellProgram :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 2919 39 3801 cellProgram
    (by decide) (by rfl) (by rfl) (by decide)

def cache : Block Artifact.submissionArtifact .Osaka 3543 cacheProgram :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 2707 11 3543 cacheProgram
    (by decide) (by rfl) (by rfl) (by decide)

def dispatch : Block Artifact.submissionArtifact .Osaka 3679 dispatchProgram :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 2799 3 3679 dispatchProgram
    (by decide) (by rfl) (by rfl) (by decide)

theorem jump3684 : Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3684 = true :=
  Artifact.isValidJumpDest_index 2802 (by rfl)

theorem jump3723 : Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3723 = true :=
  Artifact.isValidJumpDest_index 2841 (by rfl)

theorem jump3762 : Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3762 = true :=
  Artifact.isValidJumpDest_index 2880 (by rfl)

theorem jump3801 : Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3801 = true :=
  Artifact.isValidJumpDest_index 2919 (by rfl)

#print axioms cell0
#print axioms cache
#print axioms jump3801
end Challenge.Modexp.Submission.Proofs.Fast.ShiftUnrollBindings
