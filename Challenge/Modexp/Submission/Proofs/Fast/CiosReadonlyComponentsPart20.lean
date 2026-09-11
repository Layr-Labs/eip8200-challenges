import Challenge.Modexp.Submission.Proofs.Fast.CiosReadonlyComponentsPart19

set_option warningAsError true
set_option linter.unusedSimpArgs false

namespace Challenge.Modexp.Submission.Proofs.Fast.CiosReadonly

open EvmSemantics EvmSemantics.EVM YulEvmCompiler
open Challenge.Modexp.Submission.Proofs.Bytecode
open Challenge.Modexp.Submission.Proofs.Fast
open WindowNibbleKernel CiosCachedMacCore CiosCached CiosCachedMidDefs
open Monpro
open CiosEndAroundCarry

theorem ReadonlyCache.l1 {mem : ByteArray} {n : Nat} {tl inv m0 : UInt256}
    (h : ReadonlyCache mem n tl inv m0) (hn : n ≤ 32) (bi : UInt256) (pa j : Nat) :
    ReadonlyCache (l1Step mem bi pa n j).memory n tl inv m0 :=
  h.of_preserved
    (readWord_l1Step mem bi pa n 9376 j hn (Or.inr (by decide)))
    (readWord_l1Step mem bi pa n (32*n-32) j hn (Or.inl (by omega)))

end Challenge.Modexp.Submission.Proofs.Fast.CiosReadonly
