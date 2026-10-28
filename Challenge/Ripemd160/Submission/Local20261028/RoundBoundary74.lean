import Challenge.Ripemd160.Submission.Local20261028.RoundSchedule
set_option warningAsError true
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.Local20261028.RoundComposition
open EvmSemantics EvmSemantics.EVM YulEvmCompiler Challenge.EvmProof
open Paired144WordRound StackRoundTrace
theorem boundary74 (s : State) (h4 : UInt256) (q right : WordLane) (rho : List UInt256)
    (hstack : rho.length ≤ 900) (hrun : s.halt = .Running) (hactive : 34 ≤ s.activeWords.toNat) :
    runInstrSeq (templates 74) (state s h4 right rho 74 q) =
      some (state s h4 right rho 75 (StaggerModeSeven.step 74 (CoreModel.message s.memory 74) q)) := by
  have he : StaggerModeSeven.step 74 (CoreModel.message s.memory 74) q = CorePaired74.eval s.memory q := by
    unfold StaggerModeSeven.step
    rw [if_neg (by decide : ¬StaggerModeSeven.enabled 74)]
    unfold StaggerTerminal75.step
    rw [if_neg (by decide : ¬(74=75 ∨ 74=76))]
    rfl
  rw [he]
  simp only [state, pcs, shapes, templates, Nat.reduceSub]
  have hk73 : StaggerModeSeven.physicalKey 73 = StaggerAlgorithm.physicalKey 73 := by
    unfold StaggerModeSeven.physicalKey
    rw [if_neg (by decide : ¬StaggerModeSeven.enabled 73)]
  rw [hk73]
  have hk74 : StaggerModeSeven.physicalKey 74 = StaggerAlgorithm.physicalKey 74 := by
    unfold StaggerModeSeven.physicalKey
    rw [if_neg (by decide : ¬StaggerModeSeven.enabled 74)]
  rw [hk74]
  exact CorePaired74.run s h4 q right rho hstack hrun hactive
#print axioms boundary74
end Challenge.Ripemd160.Submission.Proofs.Bytecode.Local20261028.RoundComposition
