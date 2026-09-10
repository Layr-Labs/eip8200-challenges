import Challenge.Modexp.Submission.Proofs.Fast.CiosReadonlyComponentsPart21

set_option warningAsError true
set_option linter.unusedSimpArgs false

namespace Challenge.Modexp.Submission.Proofs.Fast.CiosReadonly

open EvmSemantics EvmSemantics.EVM YulEvmCompiler
open Challenge.Modexp.Submission.Proofs.Bytecode
open Challenge.Modexp.Submission.Proofs.Fast
open WindowNibbleKernel CiosCachedMacCore CiosCached CiosCachedMidDefs
open Monpro
open CiosEndAroundCarry

theorem ReadonlyCache.middle {mem : ByteArray} {n : Nat} {tl inv m0 : UInt256}
    (h : ReadonlyCache mem n tl inv m0) (hn : n ≤ 32) (c : UInt256) :
    ReadonlyCache (midMem mem c) n tl inv m0 :=
  h.of_preserved
    (CiosCachedMidMemory.read_mid mem c 9376 (Or.inr (by decide)))
    (CiosCachedMidMemory.read_mid mem c (32*n-32) (Or.inl (by omega)))

end Challenge.Modexp.Submission.Proofs.Fast.CiosReadonly
