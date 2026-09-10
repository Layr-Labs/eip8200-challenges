import Challenge.Modexp.Submission.Proofs.Fast.CiosReadonlyComponentsPart22

set_option warningAsError true
set_option linter.unusedSimpArgs false

namespace Challenge.Modexp.Submission.Proofs.Fast.CiosReadonly

open EvmSemantics EvmSemantics.EVM YulEvmCompiler
open Challenge.Modexp.Submission.Proofs.Bytecode
open Challenge.Modexp.Submission.Proofs.Fast
open WindowNibbleKernel CiosCachedMacCore CiosCached CiosCachedMidDefs
open Monpro
open CiosEndAroundCarry

theorem ReadonlyCache.rows {mem : ByteArray} {n : Nat} {tl inv m0 : UInt256}
    (h : ReadonlyCache mem n tl inv m0) (hn : n ≤ 32) (pa pb i : Nat) :
    ReadonlyCache (rowsMem mem pa pb n i) n tl inv m0 :=
  h.of_preserved
    (readWord_rowsMem mem pa pb n 9376 hn (Or.inr (by decide)) i)
    (readWord_rowsMem mem pa pb n (32*n-32) hn (Or.inl (by omega)) i)

end Challenge.Modexp.Submission.Proofs.Fast.CiosReadonly
