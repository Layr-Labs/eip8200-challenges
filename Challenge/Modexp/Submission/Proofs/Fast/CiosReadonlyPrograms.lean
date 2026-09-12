import Challenge.Modexp.Submission.Proofs.Fast.CiosNoDummyCarry
import Challenge.Modexp.Submission.Proofs.Fast.CiosReadonlyComponents

set_option warningAsError true

namespace Challenge.Modexp.Submission.Proofs.Fast.CiosReadonly
open YulEvmCompiler

def fullEntryProgram : List Instr :=
  [.op .JUMPDEST] ++ entryPrelude ++ CiosCached.entryProgram.drop 1

def fullMidProgram : List Instr :=
  CiosCached.midProgram.take 10 ++ cachedProduct

def fullExitProgram : List Instr :=
  ((CiosCached.tailProgram.drop 23).take 7 ++ dropCache) ++
    (CiosCached.tailProgram.drop 30)


/-- First operand and accumulator pointers remain cached across every row. -/
def commonFirstLoad : List Instr :=
  [.op (.Dup ⟨14, by decide⟩), .op .MLOAD, .op (.Dup ⟨7, by decide⟩)]

def commonFinishLoad : List Instr :=
  [.op (.Swap ⟨0, by decide⟩), .op (.Dup ⟨0, by decide⟩),
   .op (.Dup ⟨13, by decide⟩), .op .MLOAD, .op .ADD]

def commonFinishStore : List Instr :=
  [.op (.Dup ⟨0, by decide⟩), .op (.Dup ⟨14, by decide⟩),
   .op .MSTORE, .op .LT, .op .ADD]

def commonFirstProgram : List Instr :=
  (commonFirstLoad ++ CiosNoDummyCarry.productProgram) ++
    (commonFinishLoad ++ commonFinishStore)

end Challenge.Modexp.Submission.Proofs.Fast.CiosReadonly
