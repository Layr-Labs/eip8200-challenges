import Challenge.Modexp.Submission.Proofs.Fast.CiosReadonlyComponentsPart17

set_option warningAsError true
set_option linter.unusedSimpArgs false

namespace Challenge.Modexp.Submission.Proofs.Fast.CiosReadonly

open EvmSemantics EvmSemantics.EVM YulEvmCompiler
open Challenge.Modexp.Submission.Proofs.Bytecode
open Challenge.Modexp.Submission.Proofs.Fast
open WindowNibbleKernel CiosCachedMacCore CiosCached CiosCachedMidDefs
open Monpro
open CiosEndAroundCarry

structure ReadonlyCache (mem : ByteArray) (n : Nat) (tl inv m0 : UInt256) : Prop where
  lowAddress : tl = UInt256.ofNat (8224 + 32*n)
  inverse : inv = MachineState.readWord mem 9376
  modulusLow : m0 = MachineState.readWord mem (32*n-32)

end Challenge.Modexp.Submission.Proofs.Fast.CiosReadonly
