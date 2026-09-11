import Challenge.Modexp.Submission.Proofs.Fast.CiosReadonlyComponentsPart01

set_option warningAsError true
set_option linter.unusedSimpArgs false

namespace Challenge.Modexp.Submission.Proofs.Fast.CiosReadonly

open EvmSemantics EvmSemantics.EVM YulEvmCompiler
open Challenge.Modexp.Submission.Proofs.Bytecode
open Challenge.Modexp.Submission.Proofs.Fast
open WindowNibbleKernel CiosCachedMacCore CiosCached CiosCachedMidDefs
open Monpro
open CiosEndAroundCarry

def entryPrelude : List Instr :=
  [.push 1 64, .op .MLOAD, .push 1 96, .op .MLOAD, .push 2 9440, .op .MLOAD,
   .push 2 9408, .op .MLOAD, .op .MLOAD, .push 2 9376, .op .MLOAD,
   .push 1 32, .op .MLOAD, .push 2 9408, .op .MLOAD,
   .op (.Dup ⟨7, by decide⟩), .op .ADD,
   .op (.Swap ⟨7, by decide⟩), .op (.Swap ⟨0, by decide⟩), .op (.Swap ⟨6, by decide⟩)]

end Challenge.Modexp.Submission.Proofs.Fast.CiosReadonly
