import Challenge.Ripemd160.Submission.Local20261028.RoundSchedule
set_option warningAsError true
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.Local20261028.RoundComposition
open EvmSemantics EvmSemantics.EVM YulEvmCompiler Challenge.EvmProof
open Paired144WordRound StackRoundTrace
theorem boundary21 (s : State) (h4 : UInt256) (q right : WordLane) (rho : List UInt256)
    (hstack : rho.length ≤ 900) (hrun : s.halt = .Running) (hactive : 34 ≤ s.activeWords.toNat) :
    runInstrSeq (templates 21) (state s h4 right rho 21 q) =
      some (state s h4 right rho 22 (StaggerModeSeven.step 21 (CoreModel.message s.memory 21) q)) := by
  have he : StaggerModeSeven.step 21 (CoreModel.message s.memory 21) q = CorePaired21.eval s.memory q := by
    unfold StaggerModeSeven.step
    rw [if_neg (by decide : ¬StaggerModeSeven.enabled 21)]
    unfold StaggerTerminal75.step
    rw [if_neg (by decide : ¬(21=75 ∨ 21=76))]
    rfl
  rw [he]
  simp only [state, pcs, shapes, templates, Nat.reduceSub]
  have hk20 : StaggerModeSeven.physicalKey 20 = StaggerAlgorithm.physicalKey 20 := by
    unfold StaggerModeSeven.physicalKey
    rw [if_neg (by decide : ¬StaggerModeSeven.enabled 20)]
  rw [hk20]
  have hk21 : StaggerModeSeven.physicalKey 21 = StaggerAlgorithm.physicalKey 21 := by
    unfold StaggerModeSeven.physicalKey
    rw [if_neg (by decide : ¬StaggerModeSeven.enabled 21)]
  rw [hk21]
  exact CorePaired21.run s h4 q right rho hstack hrun hactive
#print axioms boundary21
end Challenge.Ripemd160.Submission.Proofs.Bytecode.Local20261028.RoundComposition
