import Challenge.Ripemd160.Submission.Local20261028.RoundSchedule
set_option warningAsError true
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.Local20261028.RoundComposition
open EvmSemantics EvmSemantics.EVM YulEvmCompiler Challenge.EvmProof
open Paired144WordRound StackRoundTrace
theorem boundary12 (s : State) (h4 : UInt256) (q right : WordLane) (rho : List UInt256)
    (hstack : rho.length ≤ 900) (hrun : s.halt = .Running) (hactive : 34 ≤ s.activeWords.toNat) :
    runInstrSeq (templates 12) (state s h4 right rho 12 q) =
      some (state s h4 right rho 13 (StaggerModeSeven.step 12 (CoreModel.message s.memory 12) q)) := by
  have he : StaggerModeSeven.step 12 (CoreModel.message s.memory 12) q = CorePaired12.eval s.memory q := by
    unfold StaggerModeSeven.step
    rw [if_neg (by decide : ¬StaggerModeSeven.enabled 12)]
    unfold StaggerTerminal75.step
    rw [if_neg (by decide : ¬(12=75 ∨ 12=76))]
    rfl
  rw [he]
  simp only [state, pcs, shapes, templates, Nat.reduceSub]
  have hk11 : StaggerModeSeven.physicalKey 11 = StaggerAlgorithm.physicalKey 11 := by
    unfold StaggerModeSeven.physicalKey
    rw [if_neg (by decide : ¬StaggerModeSeven.enabled 11)]
  rw [hk11]
  have hk12 : StaggerModeSeven.physicalKey 12 = StaggerAlgorithm.physicalKey 12 := by
    unfold StaggerModeSeven.physicalKey
    rw [if_neg (by decide : ¬StaggerModeSeven.enabled 12)]
  rw [hk12]
  exact CorePaired12.run s h4 q right rho hstack hrun hactive
#print axioms boundary12
end Challenge.Ripemd160.Submission.Proofs.Bytecode.Local20261028.RoundComposition
