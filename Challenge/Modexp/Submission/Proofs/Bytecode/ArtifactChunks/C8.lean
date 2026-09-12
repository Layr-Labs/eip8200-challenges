import Challenge.Modexp.Submission.Proofs.Bytecode.ArtifactChunks.C7

set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 8000000

namespace Challenge.Modexp.Submission.Proofs.Bytecode.ArtifactChunks

open EvmSemantics EvmSemantics.EVM YulEvmCompiler
open Challenge.EvmProof

def instructions8 : List Instr :=
[
 .op .SUB,
 .op (.Swap { idx := 2 }),
 .op .GT,
 .op .OR,
 .op (.Swap { idx := 0 }),
 .push 2 3104,
 .op .MSTORE,
 .push 2 4160,
 .op .MLOAD,
 .push 0 0,
 .op .MLOAD,
 .op (.Dup { idx := 1 }),
 .op (.Dup { idx := 1 }),
 .op .GT,
 .op (.Swap { idx := 1 }),
 .op .SUB,
 .op (.Dup { idx := 2 }),
 .op (.Dup { idx := 1 }),
 .op .SUB,
 .op (.Swap { idx := 2 }),
 .op .GT,
 .op .OR,
 .op (.Swap { idx := 0 }),
 .push 2 3072,
 .op .MSTORE,
 .op .ISZERO,
 .push 2 4128,
 .op .MLOAD,
 .op .OR,
 .push 2 1087,
 .op .NOT,
 .push 2 5176,
 .op .JUMP,
 .op .JUMPDEST,
 .push 2 4160,
 .push 2 5248,
 .op .MLOAD,
 .op (.Swap { idx := 1 }),
 .op .MCOPY,
 .op .JUMP,
 .op .JUMPDEST,
 .op .MUL,
 .push 2 4160,
 .op .ADD,
 .push 2 5248,
 .op .MLOAD,
 .op (.Swap { idx := 1 }),
 .op .MCOPY,
 .op .JUMP,
 .op .JUMPDEST,
 .push 0 0,
 .op .CALLDATALOAD,
 .push 1 32,
 .op .CALLDATALOAD,
 .push 1 64,
 .op .CALLDATALOAD,
 .push 1 32,
 .op (.Dup { idx := 3 }),
 .op .GT,
 .op (.Dup { idx := 2 }),
 .push 1 32,
 .op .XOR,
 .op .OR,
 .op (.Dup { idx := 1 }),
 .push 1 32,
 .op .XOR,
 .op .OR,
 .push 2 5237,
 .op .JUMPI,
 .op (.Dup { idx := 2 }),
 .push 1 96,
 .op .ADD,
 .op (.Dup { idx := 2 }),
 .op (.Dup { idx := 1 }),
 .op .ADD,
 .push 2 1186,
 .op (.Dup { idx := 1 }),
 .op (.Dup { idx := 3 }),
 .push 1 96,
 .op (.Dup { idx := 6 }),
 .op (.Dup { idx := 8 }),
 .op (.Dup { idx := 10 }),
 .push 2 4841,
 .op .JUMP,
 .op .JUMPDEST,
 .op .POP,
 .op .POP,
 .op .POP,
 .push 2 1121,
 .op .JUMP
]

theorem count8 : instructions8.length = 90 := by
  decide

theorem assemble8 : assemble instructions8 = Challenge.Modexp.submissionSpan8 := by
  apply ByteArray.ext
  simp (config := { maxSteps := 600000 })
    [assemble, assembleBytes, instructions8, Challenge.Modexp.submissionSpan8,
      Instr.bytes, natToBE]
  repeat' apply And.intro
  all_goals decide

theorem wellFormed8 :
    instructions8.all (fun i => decide (Stepper.WellFormed .Osaka i)) = true := by
  simp (config := { maxSteps := 600000 })
    [instructions8, Stepper.WellFormed, YulEvmCompiler.plainOp]
  repeat' apply And.intro
  all_goals decide

end Challenge.Modexp.Submission.Proofs.Bytecode.ArtifactChunks
