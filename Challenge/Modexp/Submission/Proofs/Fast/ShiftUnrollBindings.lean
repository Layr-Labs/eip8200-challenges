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
   .push 2 3766,
   .op .ADD,
   .push 2 1696,
   .op .MSTORE]

def dispatchProgram : List Instr :=
  [.push 2 1696,
   .op .MLOAD,
   .op .JUMP]

def cell0 : Block Artifact.submissionArtifact .Osaka 3766 cellProgram :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 2840 39 3766 cellProgram
    (by decide) (by rfl) (by rfl) (by decide)

def cell1 : Block Artifact.submissionArtifact .Osaka 3805 cellProgram :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 2879 39 3805 cellProgram
    (by decide) (by rfl) (by rfl) (by decide)

def cell2 : Block Artifact.submissionArtifact .Osaka 3844 cellProgram :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 2918 39 3844 cellProgram
    (by decide) (by rfl) (by rfl) (by decide)

def cell3 : Block Artifact.submissionArtifact .Osaka 3883 cellProgram :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 2957 39 3883 cellProgram
    (by decide) (by rfl) (by rfl) (by decide)

def cache : Block Artifact.submissionArtifact .Osaka 3625 cacheProgram :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 2745 11 3625 cacheProgram
    (by decide) (by rfl) (by rfl) (by decide)

def dispatch : Block Artifact.submissionArtifact .Osaka 3761 dispatchProgram :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 2837 3 3761 dispatchProgram
    (by decide) (by rfl) (by rfl) (by decide)

theorem jump3684 : Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3766 = true :=
  Artifact.isValidJumpDest_index 2840 (by rfl)

theorem jump3723 : Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3805 = true :=
  Artifact.isValidJumpDest_index 2879 (by rfl)

theorem jump3762 : Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3844 = true :=
  Artifact.isValidJumpDest_index 2918 (by rfl)

theorem jump3801 : Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3883 = true :=
  Artifact.isValidJumpDest_index 2957 (by rfl)

#print axioms cell0
#print axioms cache
#print axioms jump3801
end Challenge.Modexp.Submission.Proofs.Fast.ShiftUnrollBindings
