import Challenge.Modexp.Submission.Proofs.Bytecode.WindowNibbleDefs

set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000

/-!
# Instruction sequences of the immediate-address cached CIOS kernel

The fully unrolled rows cache the actual operand base and keep no limb cursor.
Accumulator addresses use PUSH2. Modulus addresses use PUSH1 or PUSH0.
The first eight-limb cell uses the existing zero row-head carry.
-/

namespace Challenge.Modexp.Submission.Proofs.Fast.CiosCached

open EvmSemantics EvmSemantics.EVM YulEvmCompiler
open Challenge.Modexp.Submission.Proofs.Bytecode
open Challenge.Modexp.Submission.Proofs.Fast
open WindowNibbleKernel

/-- Pointer-free product and incoming-carry schedule. -/
def macProductProgram : List Instr :=
  [.op (.Dup ⟨3, by decide⟩),
   .op (.Dup ⟨2, by decide⟩),
   .op .MUL,
   .op (.Swap ⟨1, by decide⟩),
   .op (.Dup ⟨4, by decide⟩),
   .op .MULMOD,
   .op (.Dup ⟨1, by decide⟩),
   .op (.Dup ⟨1, by decide⟩),
   .op .LT,
   .op .SUB,
   .op (.Dup ⟨2, by decide⟩),
   .op (.Dup ⟨2, by decide⟩),
   .op .ADD,
   .op (.Dup ⟨0, by decide⟩),
   .op (.Swap ⟨3, by decide⟩),
   .op .GT,
   .op .SUB,
   .op .SUB]

/-- The first cell starts with carry zero. No other cell uses this schedule. -/
def macZeroProductProgram : List Instr :=
  [.op (.Dup ⟨3, by decide⟩),
   .op (.Dup ⟨2, by decide⟩),
   .op .MUL,
   .op (.Swap ⟨1, by decide⟩),
   .op (.Dup ⟨4, by decide⟩),
   .op .MULMOD,
   .op (.Dup ⟨1, by decide⟩),
   .op (.Dup ⟨1, by decide⟩),
   .op .LT,
   .op .SUB,
   .op (.Dup ⟨1, by decide⟩),
   .op .ADD,
   .op (.Swap ⟨0, by decide⟩),
   .op (.Swap ⟨1, by decide⟩),
   .op .SUB]

/-- Store the accumulated word before finishing the outgoing carry. -/
def macFinishProgram (tl ts : UInt256) : List Instr :=
  [.op (.Swap ⟨0, by decide⟩), .op (.Dup ⟨0, by decide⟩),
   .push 2 tl, .op .MLOAD, .op .ADD, .op (.Dup ⟨0, by decide⟩),
   .push 2 ts, .op .MSTORE, .op .LT, .op .ADD]


/-- Combine both carry tests while storing the low word before the final carry. -/
def macFusedPostProgram (tl ts : UInt256) : List Instr :=
  [.op (.Dup ⟨0, by decide⟩),
   .op (.Dup ⟨2, by decide⟩),
   .op .GT,
   .op .SUB,
   .op (.Dup ⟨1, by decide⟩),
   .op (.Dup ⟨3, by decide⟩),
   .op .ADD,
   .push 3 tl,
   .op .MLOAD,
   .op (.Dup ⟨1, by decide⟩),
   .op .ADD,
   .op (.Dup ⟨0, by decide⟩),
   .push 2 ts,
   .op .MSTORE,
   .op (.Dup ⟨1, by decide⟩),
   .op .GT,
   .op (.Swap ⟨3, by decide⟩),
   .op .GT,
   .op .SUB,
   .op .SUB,
   .op .ADD]

def macFusedProgram (tl ts : UInt256) : List Instr :=
  macProductProgram.take 6 ++ macFusedPostProgram tl ts

/-- Load at the cached base plus an immediate byte offset. -/
def l1LoadProgram (off : UInt256) : List Instr :=
  [.push 1 off, .op (.Dup ⟨4, by decide⟩), .op .ADD,
   .op .MLOAD, .op (.Dup ⟨8, by decide⟩)]

def l1Program (off t : UInt256) : List Instr :=
  l1LoadProgram off ++ macFusedProgram t t

def l1FirstProgram (off t : UInt256) : List Instr :=
  (l1LoadProgram off ++ macZeroProductProgram) ++ macFinishProgram t t

def l1LastProgram (t : UInt256) : List Instr :=
  [.op (.Dup ⟨3, by decide⟩), .op .MLOAD, .op (.Dup ⟨8, by decide⟩)] ++
    macFusedProgram t t

/-- The width is one for positive modulus offsets, zero for the final cell. -/
def l2Program (w : Fin 33) (x tl ts : UInt256) : List Instr :=
  [.push w x, .op .MLOAD, .op (.Dup ⟨9, by decide⟩)] ++
    macFusedProgram tl ts

def entryProgram : List Instr :=
  [
   .op .JUMPDEST,
   .push 1 31,
   .op .NOT,
   .push 2 2784,
   .op .MLOAD,
   .push 1 128,
   .op .EQ,
   .push 1 152,
   .op .MUL,
   .push 2 4200,
   .op .ADD,
   .op (.Dup ⟨0, by decide⟩),
   .push 3 314,
   .op .ADD,
   .op (.Swap ⟨3, by decide⟩),
   .push 0 0,
   .op .NOT,
   .op (.Swap ⟨3, by decide⟩),
   .push 2 2784,
   .op .MLOAD,
   .op (.Dup ⟨0, by decide⟩),
   .push 5 64,
   .op .ADD,
   .op .CALLDATASIZE,
   .push 2 2048,
   .op .CALLDATACOPY,
   .op (.Dup ⟨2, by decide⟩),
   .op (.Dup ⟨5, by decide⟩),
   .op .ADD,
   .op (.Swap ⟨2, by decide⟩),
   .op .ADD,
   .op (.Dup ⟨4, by decide⟩),
   .op .ADD]

def outProgram : List Instr :=
  [.op .JUMPDEST, .op (.Dup ⟨0, by decide⟩), .op .MLOAD]

def midProgram : List Instr :=
  [.op (.Dup ⟨0, by decide⟩),
   .push 2 2080,
   .op .MLOAD,
   .op .ADD,
   .op (.Dup ⟨0, by decide⟩),
   .push 2 2080,
   .op .MSTORE,
   .op .LT,
   .push 2 2048,
   .op .MSTORE,
   .push 2 2880,
   .op .MLOAD,
   .op .MLOAD,
   .op (.Dup ⟨0, by decide⟩),
   .push 2 2816,
   .op .MLOAD,
   .op .MUL,
   .op (.Swap ⟨0, by decide⟩),
   .push 2 2848,
   .op .MLOAD,
   .op .MLOAD,
   .op (.Dup ⟨2, by decide⟩),
   .op (.Dup ⟨10, by decide⟩),
   .op (.Swap ⟨1, by decide⟩),
   .op .MULMOD,
   .op (.Dup ⟨1, by decide⟩),
   .op .ADD,
   .op (.Dup ⟨0, by decide⟩),
   .op (.Swap ⟨1, by decide⟩),
   .op .GT,
   .op .ADD]

def tailProgram : List Instr :=
  [.op (.Swap ⟨1, by decide⟩),
   .op .POP,
   .op .POP,
   .op (.Dup ⟨0, by decide⟩),
   .push 2 2080,
   .op .MLOAD,
   .op .ADD,
   .op (.Dup ⟨0, by decide⟩),
   .push 2 2112,
   .op .MSTORE,
   .op .LT,
   .push 2 2048,
   .op .MLOAD,
   .op .ADD,
   .push 2 2080,
   .op .MSTORE,
   .op (.Dup ⟨4, by decide⟩),
   .op .ADD,
   .op (.Dup ⟨2, by decide⟩),
   .op (.Dup ⟨1, by decide⟩),
   .op .GT,
   .push 2 4169,
   .op .JUMPI,
   .op .POP,
   .op .POP,
   .op .POP,
   .op .POP,
   .op .POP,
   .op .POP,
   .op .POP,
   .push 2 4898,
   .op .JUMP]

def l1DispatchProgram : List Instr :=
  [.op (.Dup ⟨5, by decide⟩), .op .JUMP]

def l2DispatchProgram : List Instr :=
  [.op (.Dup ⟨9, by decide⟩), .op .JUMP]

def joinProgram : List Instr :=
  [.op .JUMPDEST]

end Challenge.Modexp.Submission.Proofs.Fast.CiosCached
