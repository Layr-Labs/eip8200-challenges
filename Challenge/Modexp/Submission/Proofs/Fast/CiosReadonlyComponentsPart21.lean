import Challenge.Modexp.Submission.Proofs.Fast.CiosReadonlyComponentsPart20

set_option warningAsError true
set_option linter.unusedSimpArgs false

namespace Challenge.Modexp.Submission.Proofs.Fast.CiosReadonly

open EvmSemantics EvmSemantics.EVM YulEvmCompiler
open Challenge.Modexp.Submission.Proofs.Bytecode
open Challenge.Modexp.Submission.Proofs.Fast
open WindowNibbleKernel CiosCachedMacCore CiosCached CiosCachedMidDefs
open Monpro
open CiosEndAroundCarry

theorem ReadonlyCache.l2 {mem : ByteArray} {n : Nat} {tl inv m0 : UInt256}
    (h : ReadonlyCache mem n tl inv m0) (hn : n ≤ 32) (mu c0 : UInt256) (k : Nat) :
    ReadonlyCache (l2Step mem mu c0 n k).memory n tl inv m0 :=
  h.of_preserved
    (readWord_l2Step mem mu c0 n 9376 k hn (Or.inr (by decide)))
    (readWord_l2Step mem mu c0 n (32*n-32) k hn (Or.inl (by omega)))

end Challenge.Modexp.Submission.Proofs.Fast.CiosReadonly
