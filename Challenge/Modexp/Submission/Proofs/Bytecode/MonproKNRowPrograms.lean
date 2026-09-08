import Challenge.Modexp.Submission.Proofs.Bytecode.MonproKNCache

set_option warningAsError true

namespace Challenge.Modexp.Submission.Proofs.Bytecode.MonproKNRowPrograms

open EvmSemantics EvmSemantics.EVM YulEvmCompiler

/-- Exact raw252f bytes 1939..1981: 34 instructions. -/
def entryProgram : List Instr :=
  [.op .JUMPDEST,
   .push 1 31,
   .op .NOT,
   .op (.Swap ⟨1, by decide⟩),
   .push 0 0,
   .op .NOT,
   .op (.Swap ⟨2, by decide⟩),
   .op (.Swap ⟨1, by decide⟩),
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
   .op (.Swap ⟨0, by decide⟩),
   .op .POP,
   .push 1 32,
   .op (.Dup ⟨2, by decide⟩),
   .op .SUB,
   .op (.Swap ⟨1, by decide⟩),
   .op .POP]

/-- Exact raw252f bytes 1982..2002: 10 instructions. -/
def outProgram : List Instr :=
  [.op .JUMPDEST,
   .op (.Dup ⟨0, by decide⟩),
   .op .MLOAD,
   .push 0 0,
   .push 4 9440,
   .op .MLOAD,
   .op (.Dup ⟨4, by decide⟩),
   .push 7 9344,
   .op .MLOAD,
   .op .ADD]

/-- Exact raw252f bytes 2003..2007: 3 instructions. -/
def stubProgram : List Instr :=
  [.op .JUMPDEST,
   .push 2 4070,
   .op .JUMP]

/-- Exact raw252f bytes 2008..2076: 51 instructions. -/
def midProgram : List Instr :=
  [.op .JUMPDEST,
   .op .POP,
   .op .POP,
   .op (.Dup ⟨0, by decide⟩),
   .push 2 8224,
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
   .op (.Dup ⟨9, by decide⟩),
   .op (.Swap ⟨1, by decide⟩),
   .op .MULMOD,
   .op (.Dup ⟨1, by decide⟩),
   .op (.Dup ⟨1, by decide⟩),
   .op .LT,
   .op (.Dup ⟨2, by decide⟩),
   .op .ADD,
   .op (.Swap ⟨0, by decide⟩),
   .op .SUB,
   .op (.Swap ⟨0, by decide⟩),
   .push 0 0,
   .op .LT,
   .op .ADD,
   .push 2 9440,
   .op .MLOAD,
   .push 1 32,
   .op (.Swap ⟨0, by decide⟩),
   .op .SUB,
   .push 2 9408,
   .op .MLOAD,
   .push 1 32,
   .op (.Swap ⟨0, by decide⟩),
   .op .SUB]

/-- Exact raw252f bytes 2435..2470: 26 instructions. -/
def tailProgram : List Instr :=
  [.op .POP,
   .op .POP,
   .op (.Swap ⟨1, by decide⟩),
   .op .POP,
   .op .POP,
   .op .JUMPDEST,
   .op (.Dup ⟨0, by decide⟩),
   .push 2 8224,
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
   .op (.Dup ⟨3, by decide⟩),
   .op .ADD,
   .op (.Dup ⟨2, by decide⟩),
   .op (.Dup ⟨1, by decide⟩),
   .op .GT,
   .push 2 1982,
   .op .JUMPI]

/-- Exact raw252f bytes 2471..2479: 7 instructions. -/
def exitProgram : List Instr :=
  [.op .POP,
   .op .POP,
   .op .POP,
   .op .POP,
   .op .POP,
   .push 2 2655,
   .op .JUMP]


end Challenge.Modexp.Submission.Proofs.Bytecode.MonproKNRowPrograms
