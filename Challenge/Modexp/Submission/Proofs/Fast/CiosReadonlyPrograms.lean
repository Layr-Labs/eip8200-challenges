import Challenge.Modexp.Submission.Proofs.Fast.CiosNoDummyCarry
import Challenge.Modexp.Submission.Proofs.Fast.CiosReadonlyComponents

set_option warningAsError true

namespace Challenge.Modexp.Submission.Proofs.Fast.CiosReadonly
open YulEvmCompiler

def fullEntryProgram : List Instr :=
  [.op .JUMPDEST] ++ entryPrelude ++ CiosCached.entryProgram.drop 1

def fullMidProgram : List Instr :=
  CiosCached.midProgram.take 10 ++ cachedProduct

/-- The fourteen discards, then four `JUMPDEST`s (formerly `PUSH2 4804 POP`) falling
through to the CSUB guard at 4804. -/
def fullExitProgram : List Instr :=
  ((CiosCached.tailProgram.drop 23).take 7 ++ dropCache) ++
    [.op .JUMPDEST, .op .JUMPDEST, .op .JUMPDEST, .op .JUMPDEST]


/-- First operand and accumulator pointers remain cached across every row. -/
def commonFirstLoad : List Instr :=
  [.op (.Dup ⟨14, by decide⟩), .op .MLOAD, .op (.Dup ⟨7, by decide⟩)]

/-- The first-limb tail with the carry-in `0` folded away (the J/#1392 fusion applied to
the multiply rows): `hi' = lt(mm, lo) - mm`, `s = t + lo` is stored at `t[n-1]`, and the
carry out is `(gt(lo, s) - hi') - lo`. -/
def commonFusedLoad : List Instr :=
  [.op (.Dup ⟨1, by decide⟩), .op (.Dup ⟨1, by decide⟩), .op .LT, .op .SUB,
   .op (.Dup ⟨1, by decide⟩), .op (.Dup ⟨13, by decide⟩), .op .MLOAD, .op .ADD]

def commonFusedStore : List Instr :=
  [.op (.Dup ⟨0, by decide⟩), .op (.Dup ⟨14, by decide⟩), .op .MSTORE,
   .op (.Dup ⟨2, by decide⟩), .op .GT, .op .SUB, .op .SUB]

def commonFirstProgram : List Instr :=
  (commonFirstLoad ++ CiosNoDummyCarry.multiplyProgram) ++
    (commonFusedLoad ++ commonFusedStore)

end Challenge.Modexp.Submission.Proofs.Fast.CiosReadonly
