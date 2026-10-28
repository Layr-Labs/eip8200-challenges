import Challenge.Ripemd160.Submission.Local20261028.RoundSchedule
set_option warningAsError true
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.Local20261028.RoundComposition
open EvmSemantics EvmSemantics.EVM YulEvmCompiler Challenge.EvmProof
open Paired144WordRound StackRoundTrace
theorem boundary24 (s : State) (h4 : UInt256) (q right : WordLane) (rho : List UInt256)
    (hstack : rho.length ≤ 900) (hrun : s.halt = .Running) (hactive : 34 ≤ s.activeWords.toNat) :
    runInstrSeq (templates 24) (state s h4 right rho 24 q) =
      some (state s h4 right rho 25 (StaggerModeSeven.step 24 (CoreModel.message s.memory 24) q)) := by
  have he : StaggerModeSeven.step 24 (CoreModel.message s.memory 24) q = CorePaired24.eval s.memory q := by
    unfold StaggerModeSeven.step
    rw [if_neg (by decide : ¬StaggerModeSeven.enabled 24)]
    unfold StaggerTerminal75.step
    rw [if_neg (by decide : ¬(24=75 ∨ 24=76))]
    rfl
  rw [he]
  simp only [state, pcs, shapes, templates, Nat.reduceSub]
  have hk23 : StaggerModeSeven.physicalKey 23 = StaggerAlgorithm.physicalKey 23 := by
    unfold StaggerModeSeven.physicalKey
    rw [if_neg (by decide : ¬StaggerModeSeven.enabled 23)]
  rw [hk23]
  have hk24 : StaggerModeSeven.physicalKey 24 = StaggerAlgorithm.physicalKey 24 := by
    unfold StaggerModeSeven.physicalKey
    rw [if_neg (by decide : ¬StaggerModeSeven.enabled 24)]
  rw [hk24]
  exact CorePaired24.run s h4 q right rho hstack hrun hactive
#print axioms boundary24
end Challenge.Ripemd160.Submission.Proofs.Bytecode.Local20261028.RoundComposition
