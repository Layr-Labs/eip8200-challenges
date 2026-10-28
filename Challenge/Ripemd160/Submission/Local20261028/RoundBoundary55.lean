import Challenge.Ripemd160.Submission.Local20261028.RoundSchedule
set_option warningAsError true
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.Local20261028.RoundComposition
open EvmSemantics EvmSemantics.EVM YulEvmCompiler Challenge.EvmProof
open Paired144WordRound StackRoundTrace
theorem boundary55 (s : State) (h4 : UInt256) (q right : WordLane) (rho : List UInt256)
    (hstack : rho.length ≤ 900) (hrun : s.halt = .Running) (hactive : 34 ≤ s.activeWords.toNat) :
    runInstrSeq (templates 55) (state s h4 right rho 55 q) =
      some (state s h4 right rho 56 (StaggerModeSeven.step 55 (CoreModel.message s.memory 55) q)) := by
  have he : StaggerModeSeven.step 55 (CoreModel.message s.memory 55) q = CorePaired55.eval s.memory q := by
    unfold StaggerModeSeven.step
    rw [if_neg (by decide : ¬StaggerModeSeven.enabled 55)]
    unfold StaggerTerminal75.step
    rw [if_neg (by decide : ¬(55=75 ∨ 55=76))]
    rfl
  rw [he]
  simp only [state, pcs, shapes, templates, Nat.reduceSub]
  have hk54 : StaggerModeSeven.physicalKey 54 = StaggerAlgorithm.physicalKey 54 := by
    unfold StaggerModeSeven.physicalKey
    rw [if_neg (by decide : ¬StaggerModeSeven.enabled 54)]
  rw [hk54]
  have hk55 : StaggerModeSeven.physicalKey 55 = StaggerAlgorithm.physicalKey 55 := by
    unfold StaggerModeSeven.physicalKey
    rw [if_neg (by decide : ¬StaggerModeSeven.enabled 55)]
  rw [hk55]
  exact CorePaired55.run s h4 q right rho hstack hrun hactive
#print axioms boundary55
end Challenge.Ripemd160.Submission.Proofs.Bytecode.Local20261028.RoundComposition
