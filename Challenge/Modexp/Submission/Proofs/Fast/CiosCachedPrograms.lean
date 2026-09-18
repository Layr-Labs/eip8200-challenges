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

/-- Combine both carry tests while storing the low word before the final carry.
Ported from terrapinelf's promoted submission 8c2efe8b (commit c8f510f); same 26 bytes
as `macProductProgram`'s tail plus `macFinishProgram`, one instruction fewer, -3 gas. -/
def macFusedPostProgram (tl ts : UInt256) : List Instr :=
  [.op (.Dup ⟨0, by decide⟩),
   .op (.Dup ⟨2, by decide⟩),
   .op .GT,
   .op .SUB,
   .op (.Dup ⟨1, by decide⟩),
   .op (.Dup ⟨3, by decide⟩),
   .op .ADD,
   .push 2 tl,
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

/-- `macFusedPostProgram` with the incoming-carry `DUP4` **and the `ADD` that consumes it** both
deleted: same byte length, two gas cheaper, and equivalent *only* on a frame whose incoming carry
is already zero.  The `DUP4` reproduces the cell's incoming carry `c` and the `ADD` adds it to the
low product word, so dropping the pair is sound exactly where `c = 0` — the row-head cell of a
conversion chain, never a cell fed by a predecessor.  The two freed bytes are absorbed by widening
the load's `PUSH2` to a `PUSH4` of the same value, so the cell still occupies 36 bytes and no pc
after it moves. -/
def macFusedPostZeroProgram (tl ts : UInt256) : List Instr :=
  [.op (.Dup ⟨0, by decide⟩),
   .op (.Dup ⟨2, by decide⟩),
   .op .GT,
   .op .SUB,
   .op (.Dup ⟨1, by decide⟩),
   .push 4 tl,
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

/-- `macFusedProgram` on a known-zero incoming carry. -/
def macFusedZeroProgram (tl ts : UInt256) : List Instr :=
  macProductProgram.take 6 ++ macFusedPostZeroProgram tl ts

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
   .push 2 2688,
   .op .MLOAD,
   .push 1 128,
   .op .EQ,
   .push 1 153,
   .op .MUL,
   .push 2 3380,
   .op .ADD,
   .op (.Dup ⟨0, by decide⟩),
   .push 3 416,
   .op .ADD,
   .op (.Swap ⟨3, by decide⟩),
   .push 0 0,
   .op .NOT,
   .op (.Swap ⟨3, by decide⟩),
   .push 2 2688,
   .op .MLOAD,
   .op (.Dup ⟨0, by decide⟩),
   .push 5 64,
   .op .ADD,
   .op .CALLDATASIZE,
   .push 2 2048,
   .op .CALLDATACOPY,
   .op (.Dup ⟨0, by decide⟩),
   .op (.Dup ⟨3, by decide⟩),
   .op .ADD,
   .op (.Dup ⟨5, by decide⟩),
   .op .ADD,
   .op (.Swap ⟨2, by decide⟩),
   .op (.Dup ⟨5, by decide⟩),
   .op .ADD,
   .op (.Swap ⟨2, by decide⟩),
   .op (.Swap ⟨0, by decide⟩),
   .op .POP]

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
   .push 2 2784,
   .op .MLOAD,
   .op .MLOAD,
   .op (.Dup ⟨0, by decide⟩),
   .push 2 2720,
   .op .MLOAD,
   .op .MUL,
   .op (.Swap ⟨0, by decide⟩),
   .push 2 2752,
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
   .op (.Dup ⟨2, by decide⟩),
   .op .JUMPI,
   .op .POP,
   .op .POP,
   .op .POP,
   .op .POP,
   .op .POP,
   .op .POP,
   .op .POP]

def l1DispatchProgram : List Instr :=
  [.op (.Dup ⟨5, by decide⟩), .op .JUMP]

def l2DispatchProgram : List Instr :=
  [.op (.Dup ⟨9, by decide⟩), .op .JUMP]

/-- The private four-limb ladder copy's own tail.  Where the shared ladder ended in
`DUP10 JUMP` through the stack-held continuation -- a jump that on the eight-limb path
went to the very next pc and cost 11 gas for nothing -- the copy ends in an explicit
`PUSH2 0x0ee8 JUMP`, so the shared ladder no longer has to carry a continuation at all. -/
def l2ExitProgram : List Instr :=
  [.push 2 3939, .op .JUMP]

def joinProgram : List Instr :=
  [.op .JUMPDEST]

end Challenge.Modexp.Submission.Proofs.Fast.CiosCached
