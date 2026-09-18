import Challenge.Modexp.Submission.Proofs.Fast.CiosCachedPrograms
import Challenge.Modexp.Submission.Proofs.Fast.CiosReadonlyPrograms

set_option warningAsError true
namespace Challenge.Modexp.Submission.Proofs.Fast.CarryRowPrograms
open EvmSemantics YulEvmCompiler
open Challenge.Modexp.Submission.Proofs.Fast.CiosCached

/-- The row head's carry merge on the slot channel (E1 at 3770 on the shared ladder, E3
at 5408 in the private four-limb ladder copy; the two sites are byte-identical):
`DUP1 DUP10 ADD SWAP9 POP DUP9 LT SWAP1 POP`.  On
`[c, bi, pbi, pa, pb, flag, neg, ones, cy, …]` it installs `cy + c` into the cell,
emits the overflow `lt (cy + c) c` in place of `c` and consumes `bi`; the scratch word
`mem[2080]` that the previous image read and rewrote here is untouched. -/
def middleStore : List Instr :=
  [.op (.Dup ⟨0, by decide⟩), .op (.Dup ⟨9, by decide⟩), .op .ADD,
   .op (.Swap ⟨8, by decide⟩), .op .POP, .op (.Dup ⟨8, by decide⟩),
   .op .LT, .op (.Swap ⟨0, by decide⟩), .op .POP]

def middle : List Instr := middleStore ++ CiosReadonly.cachedProduct

/-- The middle block with its leading `JUMPDEST` (3769 on the shared ladder, 5407 in the
private four-limb ladder copy; the copy adds its own `PUSH2 0x0f63 JUMP` behind it). -/
def middleBlock : List Instr := [.op .JUMPDEST] ++ middle

/-- The row writeback on the slot channel (E2 at 4039):
`DUP1 DUP10 ADD DUP1 PUSH2 0x840 MSTORE LT ADD SWAP7 POP`.  On
`[c, f, pbi, pa, pb, flag, neg, ones, cy, …]` it stores `cy + c` at 2112 and installs
`f + lt (cy + c) c` (the row's carry out) into the cell; `mu` is already consumed by
the last copy. -/
def tailStore : List Instr :=
  [.op (.Dup ⟨0, by decide⟩), .op (.Dup ⟨9, by decide⟩), .op .ADD, .op (.Dup ⟨0, by decide⟩),
   .push 2 2112, .op .MSTORE, .op .LT, .op .ADD, .op (.Swap ⟨6, by decide⟩), .op .POP]

def tail : List Instr := tailStore ++ (CiosCached.tailProgram.drop 16).take 7

end Challenge.Modexp.Submission.Proofs.Fast.CarryRowPrograms
