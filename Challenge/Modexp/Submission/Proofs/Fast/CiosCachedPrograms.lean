import Challenge.Modexp.Submission.Proofs.Prepared.StackArgs
import Challenge.Modexp.Submission.Proofs.Bytecode.WindowNibbleDefs
open CycleSubmission.SharedStackArgs
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
def macProductProgram : List Instr :=
  [.op (.Dup dA3),
   .op (.Dup dA2),
   .op .MUL,
   .op (.Swap sA1),
   .op (.Dup dA4),
   .op .MULMOD,
   .op (.Dup dA1),
   .op (.Dup dA1),
   .op .LT,
   .op .SUB,
   .op (.Dup dA2),
   .op (.Dup dA2),
   .op .ADD,
   .op (.Dup dA0),
   .op (.Swap sA3),
   .op .GT,
   .op .SUB,
   .op .SUB]
def macZeroProductProgram : List Instr :=
  [.op (.Dup dA3),
   .op (.Dup dA2),
   .op .MUL,
   .op (.Swap sA1),
   .op (.Dup dA4),
   .op .MULMOD,
   .op (.Dup dA1),
   .op (.Dup dA1),
   .op .LT,
   .op .SUB,
   .op (.Dup dA1),
   .op .ADD,
   .op (.Swap sA0),
   .op (.Swap sA1),
   .op .SUB]
def macFinishProgram (tl ts : UInt256) : List Instr :=
  [.op (.Swap sA0),.op (.Dup dA0),
   .push 2 tl,.op .MLOAD,.op .ADD,.op (.Dup dA0),
   .push 2 ts,.op .MSTORE,.op .LT,.op .ADD]
def macFusedPostProgram (tl ts : UInt256) : List Instr :=
  [.op (.Dup dA0),
   .op (.Dup dA2),
   .op .GT,
   .op .SUB,
   .op (.Dup dA1),
   .op (.Dup dA3),
   .op .ADD,
   .push 2 tl,
   .op .MLOAD,
   .op (.Dup dA1),
   .op .ADD,
   .op (.Dup dA0),
   .push 2 ts,
   .op .MSTORE,
   .op (.Dup dA1),
   .op .GT,
   .op (.Swap sA3),
   .op .GT,
   .op .SUB,
   .op .SUB,
   .op .ADD]
def macFusedProgram (tl ts : UInt256) : List Instr :=
  macProductProgram.take 6++macFusedPostProgram tl ts
def macFusedPostProgramW3 (tl ts : UInt256) : List Instr :=
  [.op (.Dup dA0),
   .op (.Dup dA2),
   .op .GT,
   .op .SUB,
   .op (.Dup dA1),
   .op (.Dup dA3),
   .op .ADD,
   .push 3 tl,
   .op .MLOAD,
   .op (.Dup dA1),
   .op .ADD,
   .op (.Dup dA0),
   .push 2 ts,
   .op .MSTORE,
   .op (.Dup dA1),
   .op .GT,
   .op (.Swap sA3),
   .op .GT,
   .op .SUB,
   .op .SUB,
   .op .ADD]
def macFusedProgramW3 (tl ts : UInt256) : List Instr :=
  macProductProgram.take 6++macFusedPostProgramW3 tl ts
def macFusedPostZeroProgram (tl ts : UInt256) : List Instr :=
  [.op (.Dup dA0),
   .op (.Dup dA2),
   .op .GT,
   .op .SUB,
   .op (.Dup dA1),
   .op .JUMPDEST,
   .op .JUMPDEST,
   .push 2 tl,
   .op .MLOAD,
   .op (.Dup dA1),
   .op .ADD,
   .op (.Dup dA0),
   .push 2 ts,
   .op .MSTORE,
   .op (.Swap sA0),
   .op .JUMPDEST,
   .op .JUMPDEST,
   .op .GT,
   .op .SUB,
   .op .SUB,
   .op .ADD]
def macFusedZeroProgram (tl ts : UInt256) : List Instr :=
  macProductProgram.take 6++macFusedPostZeroProgram tl ts
/-! ## Block-0 schedule on a known-zero carry *and* a known-zero accumulator word

The M9 conversion's eight-limb row head reads the top accumulator word right after the shift
zeroed it and runs on the literal zero carry.  With `t = c = 0` the cell only has to store
`x * y` and leave `mulHi x y`: `DUP2 PUSH2 ts MSTORE` stores the low word, and
`DUP1 DUP3 GT PUSH2 0 SUB ADD SUB` forms `(0 - (mm < lo) + mm) - lo`.  The zero carry is popped
before the product (see `M9Mac.rideTopProgram`); ten `JUMPDEST`s keep the block's bytes and
instruction count. -/
def topProductProgram : List Instr :=
  [.op (.Dup dA2),.op (.Dup dA2),.op .MUL,
   .op (.Swap sA1),.op (.Dup dA3),.op .MULMOD]
def topStoreProgram (ts : UInt256) : List Instr :=
  [.op (.Dup dA1),.push 2 ts,.op .MSTORE]
def topCarryProgram : List Instr :=
  [.op (.Dup dA0),.op (.Dup dA2),.op .GT,
   .push 2 (UInt256.ofNat 0),.op .SUB,.op .ADD,.op .SUB]
def topFillProgram : List Instr := List.replicate 10 (.op .JUMPDEST)
def macTopZeroProgram (ts : UInt256) : List Instr :=
  ((topProductProgram++topStoreProgram ts)++topCarryProgram)++topFillProgram
def l1LoadProgram (off : UInt256) : List Instr :=
  [.push 1 off,.op (.Dup dA4),.op .ADD,
   .op .MLOAD,.op (.Dup dA8)]
def l1Program (off t : UInt256) : List Instr :=
  l1LoadProgram off++macFusedProgram t t
def l1FirstProgram (off t : UInt256) : List Instr :=
  (l1LoadProgram off++macZeroProductProgram)++macFinishProgram t t
def l1LastProgram (t : UInt256) : List Instr :=
  [.op (.Dup dA3),.op .MLOAD,.op (.Dup dA8)] ++
    macFusedProgram t t
def l2Program (w : Fin 33) (x tl ts : UInt256) : List Instr :=
  [.push w x,.op .MLOAD,.op (.Dup dA9)] ++
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
   .push 2 3369,
   .op .ADD,
   .op (.Dup dA0),
   .push 2 416,
   .op .ADD,
   .op (.Swap sA3),
   .push 0 0,
   .op .NOT,
   .op (.Swap sA3),
   .push 2 2688,
   .op .MLOAD,
   .op (.Dup dA0),
   .push 1 64,
   .op .ADD,
   .op .CALLDATASIZE,
   .push 2 2048,
   .op .CALLDATACOPY,
   .op (.Dup dA0),
   .op (.Dup dA3),
   .op .ADD,
   .op (.Dup dA5),
   .op .ADD,
   .op (.Swap sA2),
   .op (.Dup dA5),
   .op .ADD,
   .op (.Swap sA2),
   .op (.Swap sA0),
   .op .POP]
def outProgram : List Instr :=
  [.op .JUMPDEST,.op (.Dup dA0),.op .MLOAD]
def midProgram : List Instr :=
  [.op (.Dup dA0),
   .push 2 2080,
   .op .MLOAD,
   .op .ADD,
   .op (.Dup dA0),
   .push 2 2080,
   .op .MSTORE,
   .op .LT,
   .push 2 2048,
   .op .MSTORE,
   .push 2 2784,
   .op .MLOAD,
   .op .MLOAD,
   .op (.Dup dA0),
   .push 2 2720,
   .op .MLOAD,
   .op .MUL,
   .op (.Swap sA0),
   .push 2 2752,
   .op .MLOAD,
   .op .MLOAD,
   .op (.Dup dA2),
   .op (.Dup dA10),
   .op (.Swap sA1),
   .op .MULMOD,
   .op (.Dup dA1),
   .op .ADD,
   .op (.Dup dA0),
   .op (.Swap sA1),
   .op .GT,
   .op .ADD]
def tailProgram : List Instr :=
  [.op (.Swap sA1),
   .op .POP,
   .op .POP,
   .op (.Dup dA0),
   .push 2 2080,
   .op .MLOAD,
   .op .ADD,
   .op (.Dup dA0),
   .push 2 2112,
   .op .MSTORE,
   .op .LT,
   .push 2 2048,
   .op .MLOAD,
   .op .ADD,
   .push 2 2080,
   .op .MSTORE,
   .op (.Dup dA4),
   .op .ADD,
   .op (.Dup dA2),
   .op (.Dup dA1),
   .op .GT,
   .op (.Dup dA2),
   .op .JUMPI,
   .op .POP,
   .op .POP,
   .op .POP,
   .op .POP,
   .op .POP,
   .op .POP,
   .op .POP]
def l1DispatchProgram : List Instr :=
  [.op (.Dup dA5),.op .JUMP]
def l2DispatchProgram : List Instr :=
  [.op (.Dup dA9),.op .JUMP]
def l2ExitProgram : List Instr :=
  [.push 2 3816,.op .JUMP]
def joinProgram : List Instr :=
  [.op .JUMPDEST]
end Challenge.Modexp.Submission.Proofs.Fast.CiosCached
