import Challenge.Modexp.Submission.Proofs.Fast.CiosReadonlyComponentsPart23

set_option warningAsError true
set_option linter.unusedSimpArgs false

namespace Challenge.Modexp.Submission.Proofs.Fast.CiosReadonly

open EvmSemantics EvmSemantics.EVM YulEvmCompiler
open Challenge.Modexp.Submission.Proofs.Bytecode
open Challenge.Modexp.Submission.Proofs.Fast
open WindowNibbleKernel CiosCachedMacCore CiosCached CiosCachedMidDefs
open Monpro
open CiosEndAroundCarry

theorem ReadonlyCache.zeroed {mem : ByteArray} {n : Nat} {tl inv m0 : UInt256}
    (h : ReadonlyCache mem n tl inv m0) (hn : n ≤ 32) (s : State) :
    ReadonlyCache (mpZeroed s mem n) n tl inv m0 :=
  h.of_preserved
    (readWord_mpZeroed s mem n 9376 hn (Or.inr (by decide)))
    (readWord_mpZeroed s mem n (32*n-32) hn (Or.inl (by omega)))

end Challenge.Modexp.Submission.Proofs.Fast.CiosReadonly
