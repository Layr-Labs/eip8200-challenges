import Challenge.Modexp.Submission.Proofs.Bytecode.WindowNibbleDefs

set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000

/-!
# Instruction sequences of the immediate-address cached CIOS kernel

The fully unrolled four- and eight-limb rows keep only the `a` cursor, the
running carry and the row multiplier on the stack.  Every `t` and modulus limb
address is a compile-time `PUSH2` immediate, so the first loop no longer
maintains a `t` pointer and the second loop maintains no pointer at all.
-/

namespace Challenge.Modexp.Submission.Proofs.Fast.CiosCached

open EvmSemantics EvmSemantics.EVM YulEvmCompiler
open Challenge.Modexp.Submission.Proofs.Bytecode
open Challenge.Modexp.Submission.Proofs.Fast
open WindowNibbleKernel

/-- One first-loop MAC without its cursor update.  Entered with
`[pa, carry, bi, ...]`; `t` is the address of the accumulator limb. -/
def l1Body (t : UInt256) : List Instr :=
  [.op (.Dup ⟨0, by decide⟩),
   .op .MLOAD,
   .op (.Dup ⟨9, by decide⟩),
   .op (.Dup ⟨4, by decide⟩),
   .op (.Dup ⟨2, by decide⟩),
   .op .MUL,
   .op (.Swap ⟨1, by decide⟩),
   .op (.Dup ⟨5, by decide⟩),
   .op .MULMOD,
   .op (.Dup ⟨1, by decide⟩),
   .op (.Dup ⟨1, by decide⟩),
   .op .LT,
   .op .SUB,
   .op (.Dup ⟨3, by decide⟩),
   .op (.Dup ⟨2, by decide⟩),
   .op .ADD,
   .op (.Dup ⟨0, by decide⟩),
   .op (.Swap ⟨4, by decide⟩),
   .op .GT,
   .op .SUB,
   .op .SUB,
   .op (.Dup ⟨2, by decide⟩),
   .push 2 t,
   .op .MLOAD,
   .op .ADD,
   .op (.Dup ⟨0, by decide⟩),
   .op (.Swap ⟨3, by decide⟩),
   .op .GT,
   .op .ADD,
   .op (.Swap ⟨1, by decide⟩),
   .push 2 t,
   .op .MSTORE]

/-- A first-loop MAC that then moves the `a` cursor one limb down. -/
def l1Program (t : UInt256) : List Instr :=
  l1Body t ++ [.op (.Dup ⟨7, by decide⟩), .op .ADD]

/-- The final first-loop MAC discards the exhausted `a` cursor. -/
def l1LastProgram (t : UInt256) : List Instr :=
  l1Body t ++ [.op .POP]

/-- One second-loop MAC.  Entered with `[carry, mu, bi, ...]`; `x` is the
address of the modulus limb, `tl` the accumulator limb read and `ts` the
(one limb higher) accumulator limb written. -/
def l2Program (x tl ts : UInt256) : List Instr :=
  [.push 2 x,
   .op .MLOAD,
   .op (.Dup ⟨9, by decide⟩),
   .op (.Dup ⟨3, by decide⟩),
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
   .op .SUB,
   .op (.Dup ⟨1, by decide⟩),
   .push 2 tl,
   .op .MLOAD,
   .op .ADD,
   .op (.Dup ⟨0, by decide⟩),
   .op (.Swap ⟨2, by decide⟩),
   .op .GT,
   .op .ADD,
   .op (.Swap ⟨0, by decide⟩),
   .push 2 ts,
   .op .MSTORE]

def entryProgram : List Instr :=
  [.op .JUMPDEST,
   .push 32 115792089237316195423570985008687907853269984665640564039457584007913129639935,
   .op (.Swap ⟨1, by decide⟩),
   .push 32 115792089237316195423570985008687907853269984665640564039457584007913129639904,
   .op .JUMPDEST,
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

/-- Row head: load `b_i`, seed the carry and the `a` cursor. -/
def outProgram : List Instr :=
  [.op .JUMPDEST,
   .op (.Dup ⟨0, by decide⟩),
   .op .MLOAD,
   .push 0 0,
   .op (.Dup ⟨3, by decide⟩)]

/-- `t[n] += C`, `t[n+1] := carry`, then `mu` and the first reduction carry. -/
def midProgram : List Instr :=
  [.op (.Dup ⟨0, by decide⟩),
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
   .op (.Dup ⟨10, by decide⟩),
   .op (.Swap ⟨1, by decide⟩),
   .op .MULMOD,
   .op (.Dup ⟨1, by decide⟩),
   .op (.Dup ⟨10, by decide⟩),
   .op .ADD,
   .op (.Dup ⟨1, by decide⟩),
   .op .GT,
   .op .ADD,
   .op .SUB]

/-- Row tail: drop `mu` and `b_i`, finish the shift, advance the row pointer
and either loop or fall into the exit. -/
def tailProgram : List Instr :=
  [.op (.Swap ⟨1, by decide⟩),
   .op .POP,
   .op .POP,
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
  [.op (.Dup ⟨6, by decide⟩),
   .push 2 4757,
   .op .JUMPI]

def l2DispatchProgram : List Instr :=
  [.op (.Dup ⟨6, by decide⟩),
   .push 2 5112,
   .op .JUMPI]

def joinProgram : List Instr :=
  [.op .JUMPDEST]

end Challenge.Modexp.Submission.Proofs.Fast.CiosCached
