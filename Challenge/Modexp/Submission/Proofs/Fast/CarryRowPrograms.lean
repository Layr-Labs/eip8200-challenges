import Challenge.Modexp.Submission.Proofs.Fast.CiosCachedPrograms
import Challenge.Modexp.Submission.Proofs.Fast.CiosReadonlyPrograms

set_option warningAsError true
namespace Challenge.Modexp.Submission.Proofs.Fast.CarryRowPrograms
open EvmSemantics YulEvmCompiler
open Challenge.Modexp.Submission.Proofs.Fast.CiosCached

def middleStore : List Instr :=
  [.op (.Dup ⟨0, by decide⟩), .push 2 2080, .op .MLOAD, .op .ADD,
   .op (.Dup ⟨0, by decide⟩), .push 2 2080, .op .MSTORE, .op .LT,
   .op (.Swap ⟨0, by decide⟩), .op .POP]

def middle : List Instr := middleStore ++ CiosReadonly.cachedProduct

/-- `middleStore` with the first `PUSH2 0x820` widened to `PUSH4`.  The widening
absorbs the two bytes freed by deleting the block's trailing `DUP10 JUMP`, so every
program counter outside 3639-3667 is unchanged.  The pushed VALUE and the gas are
identical; only `Instr.bytes.length` differs, which moves the block's interior pcs
by +2 and makes the block end at 3668 instead of 3666. -/
def middleStoreWide : List Instr :=
  [.op (.Dup ⟨0, by decide⟩), .push 4 2080, .op .MLOAD, .op .ADD,
   .op (.Dup ⟨0, by decide⟩), .push 2 2080, .op .MSTORE, .op .LT,
   .op (.Swap ⟨0, by decide⟩), .op .POP]

def middleWide : List Instr := middleStoreWide ++ CiosReadonly.cachedProduct

/-- The middle block with its leading `JUMPDEST` (pc 4555, the empty-chain entry).
This narrow form is the one the private ladder copy carries at 5283; the shared
ladder at 3639 uses `middleBlockWide`. -/
def middleBlock : List Instr := [.op .JUMPDEST] ++ middle

/-- The middle block at 3639, whose first store address is a `PUSH4`. -/
def middleBlockWide : List Instr := [.op .JUMPDEST] ++ middleWide

/-- `mu` is already consumed by the last copy; the first address is a `PUSH4` so that the
bytes of the removed `SWAP1 POP` are kept. -/
def tailStore : List Instr :=
  [.op (.Dup ⟨0, by decide⟩),
   .push 2 2080, .op .MLOAD, .op .ADD, .op (.Dup ⟨0, by decide⟩),
   .push 2 2112, .op .MSTORE, .op .LT, .op .ADD, .push 2 2080, .op .MSTORE]

def tail : List Instr := tailStore ++ (CiosCached.tailProgram.drop 16).take 7

end Challenge.Modexp.Submission.Proofs.Fast.CarryRowPrograms
