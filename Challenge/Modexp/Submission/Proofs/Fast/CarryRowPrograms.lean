import Challenge.Modexp.Submission.Proofs.Fast.CiosCachedPrograms
import Challenge.Modexp.Submission.Proofs.Fast.CiosReadonlyPrograms

set_option warningAsError true
namespace Challenge.Modexp.Submission.Proofs.Fast.CarryRowPrograms
open EvmSemantics YulEvmCompiler
open Challenge.Modexp.Submission.Proofs.Fast.CiosCached

def middleStore : List Instr :=
  [.op (.Dup ⟨0, by decide⟩), .push 4 8224, .op .MLOAD, .op .ADD,
   .op (.Dup ⟨0, by decide⟩), .push 2 8224, .op .MSTORE, .op .LT,
   .op (.Swap ⟨0, by decide⟩), .op .POP]

def middle : List Instr := middleStore ++ CiosReadonly.cachedProduct

def tailStore : List Instr :=
  [.op (.Swap ⟨0, by decide⟩), .op .POP, .op (.Dup ⟨0, by decide⟩),
   .push 7 8224, .op .MLOAD, .op .ADD, .op (.Dup ⟨0, by decide⟩),
   .push 2 8256, .op .MSTORE, .op .LT, .op .ADD, .push 2 8224, .op .MSTORE]

def tail : List Instr := tailStore ++ (CiosCached.tailProgram.drop 16).take 7

end Challenge.Modexp.Submission.Proofs.Fast.CarryRowPrograms
