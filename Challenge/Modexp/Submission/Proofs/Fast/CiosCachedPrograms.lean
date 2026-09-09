import Challenge.Modexp.Submission.Proofs.Bytecode.WindowNibbleDefs

set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000

namespace Challenge.Modexp.Submission.Proofs.Fast.CiosCached

open EvmSemantics EvmSemantics.EVM YulEvmCompiler
open Challenge.Modexp.Submission.Proofs.Bytecode
open Challenge.Modexp.Submission.Proofs.Fast
open WindowNibbleKernel

def l1Program : List Instr :=
  [.op (.Dup ⟨0, by decide⟩),
   .op .MLOAD,
   .op (.Dup ⟨10, by decide⟩),
   .op (.Dup ⟨5, by decide⟩),
   .op (.Dup ⟨2, by decide⟩),
   .op .MUL,
   .op (.Swap ⟨1, by decide⟩),
   .op (.Dup ⟨6, by decide⟩),
   .op .MULMOD,
   .op (.Dup ⟨1, by decide⟩),
   .op (.Dup ⟨1, by decide⟩),
   .op .LT,
   .op .SUB,
   .op (.Dup ⟨4, by decide⟩),
   .op (.Dup ⟨2, by decide⟩),
   .op .ADD,
   .op (.Dup ⟨0, by decide⟩),
   .op (.Swap ⟨5, by decide⟩),
   .op .GT,
   .op .SUB,
   .op .SUB,
   .op (.Dup ⟨3, by decide⟩),
   .op (.Dup ⟨3, by decide⟩),
   .op .MLOAD,
   .op .ADD,
   .op (.Dup ⟨0, by decide⟩),
   .op (.Swap ⟨4, by decide⟩),
   .op .GT,
   .op .ADD,
   .op (.Swap ⟨2, by decide⟩),
   .op (.Dup ⟨2, by decide⟩),
   .op (.Dup ⟨10, by decide⟩),
   .op .ADD,
   .op (.Swap ⟨2, by decide⟩),
   .op .MSTORE,
   .op (.Dup ⟨8, by decide⟩),
   .op .ADD]

/-- Only the final L1 copy retains its soon-discarded pointers. -/
def l1LastProgram : List Instr :=
  [.op (.Dup ⟨0, by decide⟩),
   .op .MLOAD,
   .op (.Dup ⟨10, by decide⟩),
   .op (.Dup ⟨5, by decide⟩),
   .op (.Dup ⟨2, by decide⟩),
   .op .MUL,
   .op (.Swap ⟨1, by decide⟩),
   .op (.Dup ⟨6, by decide⟩),
   .op .MULMOD,
   .op (.Dup ⟨1, by decide⟩),
   .op (.Dup ⟨1, by decide⟩),
   .op .LT,
   .op .SUB,
   .op (.Dup ⟨4, by decide⟩),
   .op (.Dup ⟨2, by decide⟩),
   .op .ADD,
   .op (.Dup ⟨0, by decide⟩),
   .op (.Swap ⟨5, by decide⟩),
   .op .GT,
   .op .SUB,
   .op .SUB,
   .op (.Dup ⟨3, by decide⟩),
   .op (.Dup ⟨3, by decide⟩),
   .op .MLOAD,
   .op .ADD,
   .op (.Dup ⟨0, by decide⟩),
   .op (.Swap ⟨4, by decide⟩),
   .op .GT,
   .op .ADD,
   .op (.Swap ⟨2, by decide⟩),
   .op (.Dup ⟨2, by decide⟩),
   .op .MSTORE]

def l2Program (p : Nat) : List Instr :=
  [.op (.Dup ⟨0, by decide⟩),
   .op .MLOAD,
   .op (.Dup ⟨11, by decide⟩),
   .op (.Dup ⟨5, by decide⟩),
   .op (.Dup ⟨2, by decide⟩),
   .op .MUL,
   .op (.Swap ⟨1, by decide⟩),
   .op (.Dup ⟨6, by decide⟩),
   .op .MULMOD,
   .op (.Dup ⟨1, by decide⟩),
   .op (.Dup ⟨1, by decide⟩),
   .op .LT,
   .op .SUB,
   .op (.Dup ⟨4, by decide⟩),
   .op (.Dup ⟨2, by decide⟩),
   .op .ADD,
   .op (.Dup ⟨0, by decide⟩),
   .op (.Swap ⟨5, by decide⟩),
   .op .GT,
   .op .SUB,
   .op .SUB,
   .op (.Dup ⟨3, by decide⟩),
   .op (.Dup ⟨3, by decide⟩),
   .op .MLOAD,
   .op .ADD,
   .op (.Dup ⟨0, by decide⟩),
   .op (.Swap ⟨4, by decide⟩),
   .op .GT,
   .op .ADD,
   .op (.Swap ⟨2, by decide⟩),
   .push 2 (UInt256.ofNat (8288 + p)),
   .op .MSTORE,
   .op .POP,
   .op (.Dup ⟨8, by decide⟩),
   .op .ADD] ++
  if p = 0 then
    [.op (.Dup ⟨8, by decide⟩), .op .JUMPDEST, .op .JUMPDEST]
  else
    [.push 2 (UInt256.ofNat (p - 32))]

/-- The final L2 cell stores at the fixed terminal address.  The following
two instructions in `tailProgram` discard the pointer words, so this
same-width tail leaves them unchanged. -/
def l2LastProgram : List Instr :=
  (l2Program 0).take 30 ++
    [.push 8 (UInt256.ofNat 8288), .op .MSTORE]

def entryProgram : List Instr :=
  [.op .JUMPDEST,
   .push 32 115792089237316195423570985008687907853269984665640564039457584007913129639904,
   .op (.Swap ⟨1, by decide⟩),
   .push 32 115792089237316195423570985008687907853269984665640564039457584007913129639935,
   .op (.Swap ⟨2, by decide⟩),
   .op (.Swap ⟨1, by decide⟩),
   .push 2 9344,
   .op .MLOAD,
   .push 1 128,
   .op .EQ,
   .op (.Swap ⟨1, by decide⟩),
   .op (.Swap ⟨0, by decide⟩),
   .push 2 9344,
   .op .MLOAD,
   .op (.Dup ⟨0, by decide⟩),
   .push 1 64,
   .op .ADD,
   .op .CALLDATASIZE,
   .push 2 8192,
   .op .CALLDATACOPY,
   .op (.Dup ⟨0, by decide⟩),
   .op (.Dup ⟨3, by decide⟩),
   .op .ADD,
   .push 1 32,
   .op (.Swap ⟨0, by decide⟩),
   .op .SUB,
   .push 1 32,
   .op (.Dup ⟨4, by decide⟩),
   .op .SUB,
   .op (.Swap ⟨3, by decide⟩),
   .op .POP,
   .op (.Swap ⟨1, by decide⟩),
   .op .ADD,
   .op (.Swap ⟨0, by decide⟩),
   .push 1 32,
   .op (.Dup ⟨2, by decide⟩),
   .op .SUB,
   .op (.Swap ⟨1, by decide⟩),
   .op .POP]

def outProgram : List Instr :=
  [.op .JUMPDEST,
   .op (.Dup ⟨0, by decide⟩),
   .op .MLOAD,
   .push 0 0,
   .push 2 9440,
   .op .MLOAD,
   .op (.Dup ⟨4, by decide⟩)]

def midProgram : List Instr :=
  [.op .POP,
   .op .POP,
   .op (.Dup ⟨0, by decide⟩),
   .push 7 8224,
   .op .MLOAD,
   .op .ADD,
   .op (.Dup ⟨0, by decide⟩),
   .push 2 8224,
   .op .MSTORE,
   .op .LT,
   .push 2 8192,
   .op .MSTORE,
   .push 2 9440,
   .op .MLOAD,
   .op .MLOAD,
   .push 2 9376,
   .op .MLOAD,
   .op .MUL,
   .op (.Dup ⟨0, by decide⟩),
   .push 2 9408,
   .op .MLOAD,
   .op .MLOAD,
   .op (.Dup ⟨1, by decide⟩),
   .op (.Dup ⟨1, by decide⟩),
   .op .MUL,
   .op (.Swap ⟨1, by decide⟩),
   .op (.Dup ⟨10, by decide⟩),
   .op (.Swap ⟨1, by decide⟩),
   .op .MULMOD,
   .op (.Dup ⟨1, by decide⟩),
   .op (.Dup ⟨10, by decide⟩),
   .op .ADD,
   .op (.Dup ⟨1, by decide⟩),
   .op .GT,
   .op .ADD,
   .op .SUB,
   .push 6 9440,
   .op .MLOAD,
   .op (.Dup ⟨8, by decide⟩),
   .op .ADD,
   .push 6 9408,
   .op .MLOAD,
   .op (.Dup ⟨9, by decide⟩),
   .op .ADD]

def tailProgram : List Instr :=
  [.op .POP,
   .op .POP,
   .op (.Swap ⟨1, by decide⟩),
   .op .POP,
   .op .POP,
   .op (.Dup ⟨0, by decide⟩),
   .push 3 8224,
   .op .MLOAD,
   .op .ADD,
   .op (.Dup ⟨0, by decide⟩),
   .push 2 8256,
   .op .MSTORE,
   .op .LT,
   .push 2 8192,
   .op .MLOAD,
   .op .ADD,
   .push 2 8224,
   .op .MSTORE,
   .op (.Dup ⟨4, by decide⟩),
   .op .ADD,
   .op (.Dup ⟨2, by decide⟩),
   .op (.Dup ⟨1, by decide⟩),
   .op .GT,
   .push 2 4595,
   .op .JUMPI,
   .op .POP,
   .op .POP,
   .op .POP,
   .op .POP,
   .op .POP,
   .op .POP,
   .push 2 2304,
   .op .JUMP]

def l1DispatchProgram : List Instr :=
  [.op (.Dup ⟨7, by decide⟩),
   .push 3 4758,
   .op .JUMPI]

def l2DispatchProgram : List Instr :=
  [.op (.Dup ⟨8, by decide⟩),
   .push 3 5141,
   .op .JUMPI]

def joinProgram : List Instr :=
  [.op .JUMPDEST]

end Challenge.Modexp.Submission.Proofs.Fast.CiosCached
