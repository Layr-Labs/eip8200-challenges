import Challenge.Modexp.Submission.Proofs.Fast.CiosReadonlyComponentsPart18

set_option warningAsError true
set_option linter.unusedSimpArgs false

namespace Challenge.Modexp.Submission.Proofs.Fast.CiosReadonly

open EvmSemantics EvmSemantics.EVM YulEvmCompiler
open Challenge.Modexp.Submission.Proofs.Bytecode
open Challenge.Modexp.Submission.Proofs.Fast
open WindowNibbleKernel CiosCachedMacCore CiosCached CiosCachedMidDefs
open Monpro
open CiosEndAroundCarry

theorem ReadonlyCache.of_preserved {mem mem' : ByteArray} {n : Nat}
    {tl inv m0 : UInt256} (h : ReadonlyCache mem n tl inv m0)
    (hinv : MachineState.readWord mem' 9376 = MachineState.readWord mem 9376)
    (hm0 : MachineState.readWord mem' (32*n-32) = MachineState.readWord mem (32*n-32)) :
    ReadonlyCache mem' n tl inv m0 :=
  ⟨h.lowAddress, h.inverse.trans hinv.symm, h.modulusLow.trans hm0.symm⟩

end Challenge.Modexp.Submission.Proofs.Fast.CiosReadonly
