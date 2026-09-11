import Challenge.Modexp.Submission.Proofs.Fast.CsubCorePart48

set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false

namespace Challenge.Modexp.Submission.Proofs.Fast.Csub

attribute [local simp]
  CompactConstants.notThirtyOne CompactConstants.not1087

open EvmSemantics
open EvmSemantics.EVM
open YulEvmCompiler
open Challenge.Modexp.Submission.Proofs.Bytecode
open Challenge.Modexp.Submission.Proofs
open Challenge.Modexp.Submission.Proofs.Fast

theorem fastRepresents_amStep (memory : ByteArray) (pa pb n ptr cnt v : Nat)
    (hn : 1 ≤ n)
    (hdisj : ptr + 32 * cnt ≤ 8256 ∨ 8256 + 32 * n ≤ ptr)
    (hrep : Model.FastRepresents memory ptr cnt v) (j : Nat) (hj : j ≤ n) :
    Model.FastRepresents (amStep memory pa pb n j).memory ptr cnt v := by
  refine (Model.fastRepresents_congr ?_ v).2 hrep
  intro i hi
  exact amStep_readWord_disjoint memory pa pb n _ hn (by omega) j hj

end Challenge.Modexp.Submission.Proofs.Fast.Csub
