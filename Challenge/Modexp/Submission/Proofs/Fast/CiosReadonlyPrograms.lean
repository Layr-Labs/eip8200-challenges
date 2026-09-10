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

end Challenge.Modexp.Submission.Proofs.Fast.CiosReadonly
