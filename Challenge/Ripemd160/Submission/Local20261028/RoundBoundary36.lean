import Challenge.Ripemd160.Submission.Local20261028.RoundSchedule
set_option warningAsError true
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.Local20261028.RoundComposition
open EvmSemantics EvmSemantics.EVM YulEvmCompiler Challenge.EvmProof
open Paired144WordRound StackRoundTrace
theorem boundary36 (s : State) (h4 : UInt256) (q right : WordLane) (rho : List UInt256)
    (hstack : rho.length ≤ 900) (hrun : s.halt = .Running) (hactive : 34 ≤ s.activeWords.toNat) :
    runInstrSeq (templates 36) (state s h4 right rho 36 q) =
      some (state s h4 right rho 37 (StaggerModeSeven.step 36 (CoreModel.message s.memory 36) q)) := by
  have he : StaggerModeSeven.step 36 (CoreModel.message s.memory 36) q = CorePaired36.eval s.memory q := by
    unfold StaggerModeSeven.step
    rw [if_neg (by decide : ¬StaggerModeSeven.enabled 36)]
    unfold StaggerTerminal75.step
    rw [if_neg (by decide : ¬(36=75 ∨ 36=76))]
    rfl
  rw [he]
  simp only [state, pcs, shapes, templates, Nat.reduceSub]
  have hk35 : StaggerModeSeven.physicalKey 35 = StaggerAlgorithm.physicalKey 35 := by
    unfold StaggerModeSeven.physicalKey
    rw [if_neg (by decide : ¬StaggerModeSeven.enabled 35)]
  rw [hk35]
  have hk36 : StaggerModeSeven.physicalKey 36 = StaggerAlgorithm.physicalKey 36 := by
    unfold StaggerModeSeven.physicalKey
    rw [if_neg (by decide : ¬StaggerModeSeven.enabled 36)]
  rw [hk36]
  exact CorePaired36.run s h4 q right rho hstack hrun hactive
#print axioms boundary36
end Challenge.Ripemd160.Submission.Proofs.Bytecode.Local20261028.RoundComposition
