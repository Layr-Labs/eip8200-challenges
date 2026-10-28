import Challenge.Ripemd160.Submission.Local20261028.RoundSchedule
set_option warningAsError true
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.Local20261028.RoundComposition
open EvmSemantics EvmSemantics.EVM YulEvmCompiler Challenge.EvmProof
open Paired144WordRound StackRoundTrace
theorem boundary76 (s : State) (h4 : UInt256) (q right : WordLane) (rho : List UInt256)
    (hstack : rho.length ≤ 900) (hrun : s.halt = .Running) (hactive : 34 ≤ s.activeWords.toNat) :
    runInstrSeq (templates 76) (state s h4 right rho 76 q) =
      some (state s h4 right rho 77 (StaggerModeSeven.step 76 (CoreModel.message s.memory 76) q)) := by
  have he : StaggerModeSeven.step 76 (CoreModel.message s.memory 76) q = CorePaired76.eval s.memory q := by
    unfold StaggerModeSeven.step
    rw [if_neg (by decide : ¬StaggerModeSeven.enabled 76)]
    rfl
  rw [he]
  simp only [state, pcs, shapes, templates, Nat.reduceSub]
  have hk75 : StaggerModeSeven.physicalKey 75 = StaggerAlgorithm.physicalKey 75 := by
    unfold StaggerModeSeven.physicalKey
    rw [if_neg (by decide : ¬StaggerModeSeven.enabled 75)]
  rw [hk75]
  have hk76 : StaggerModeSeven.physicalKey 76 = StaggerAlgorithm.physicalKey 76 := by
    unfold StaggerModeSeven.physicalKey
    rw [if_neg (by decide : ¬StaggerModeSeven.enabled 76)]
  rw [hk76]
  exact CorePaired76.run s h4 q right rho hstack hrun hactive
#print axioms boundary76
end Challenge.Ripemd160.Submission.Proofs.Bytecode.Local20261028.RoundComposition
