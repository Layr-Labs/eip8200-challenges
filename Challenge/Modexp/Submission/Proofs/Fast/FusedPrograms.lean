import Challenge.Modexp.Submission.Proofs.Fast.R8ZeroFirstRow
import Challenge.Modexp.Submission.Proofs.Fast.CarryRowPrograms
import Challenge.Modexp.Submission.Proofs.Fast.SquareRow

set_option warningAsError true
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000

/-!
# Fused R8-square programs.

Straight-line copies of existing kernel programs with indirect jumps replaced
by `POP` fall-throughs.  Each definition is instruction-identical to a span of
the submitted bytecode (verified by the `FusedBlocks` location certificates);
only the program counter flow changes.
-/

namespace Challenge.Modexp.Submission.Proofs.Fast.FusedPrograms

open EvmSemantics EvmSemantics.EVM YulEvmCompiler
open Challenge.Modexp.Submission.Proofs.Fast

/-- Prologue terminal: duplicate the join target, then pop it (fall through). -/
def quotientDupPOP : List Instr :=
  [.op (.Dup ⟨9, by decide⟩), .op .POP]

/-- Full prologue with a `POP` fall-through instead of the join jump. -/
def prologuePOPProgram (next : UInt256) : List Instr :=
  (((R8ZeroFirstRow.diagonalProgram next ++ R8ZeroFirstRow.cellsProgram 6) ++
    R8ZeroFirstRow.cellAB (UInt256.ofNat (SquareModel.aAddr 8 7))) ++
    R8ZeroFirstRow.finishStore) ++
    ((R8ZeroFirstRow.quotientA ++ R8ZeroFirstRow.quotientB) ++ quotientDupPOP)

/-- Row-check head (`DUP5 ADD DUP3`) with the check replaced by `POP`. -/
def headPOPProgram : List Instr :=
  [.op (.Dup ⟨4, by decide⟩), .op .ADD, .op (.Dup ⟨2, by decide⟩), .op .POP]

/-- Dispatch arithmetic with the indirect cell jump replaced by `POP`. -/
def b4POPProgram : List Instr :=
  [.push 1 37, .op (.Dup ⟨6, by decide⟩), .op .ADD, .op (.Swap ⟨5, by decide⟩),
   .op .POP]

/-- Rejoin: push the row-8 cell and jump to the original code. -/
def rejoinProgram : List Instr :=
  [.push 2 3639, .op .JUMP]

end Challenge.Modexp.Submission.Proofs.Fast.FusedPrograms
