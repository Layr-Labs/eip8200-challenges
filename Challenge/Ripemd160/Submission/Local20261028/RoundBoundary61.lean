import Challenge.Ripemd160.Submission.Local20261028.RoundSchedule
set_option warningAsError true
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.Local20261028.RoundComposition
open EvmSemantics EvmSemantics.EVM YulEvmCompiler Challenge.EvmProof
open Paired144WordRound StackRoundTrace
theorem boundary61 (s : State) (h4 : UInt256) (q right : WordLane) (rho : List UInt256)
    (hstack : rho.length ≤ 900) (hrun : s.halt = .Running) (hactive : 34 ≤ s.activeWords.toNat) :
    runInstrSeq (templates 61) (state s h4 right rho 61 q) =
      some (state s h4 right rho 62 (StaggerModeSeven.step 61 (CoreModel.message s.memory 61) q)) := by
  have he : StaggerModeSeven.step 61 (CoreModel.message s.memory 61) q = CorePaired61.eval s.memory q := by
    unfold StaggerModeSeven.step
    rw [if_neg (by decide : ¬StaggerModeSeven.enabled 61)]
    unfold StaggerTerminal75.step
    rw [if_neg (by decide : ¬(61=75 ∨ 61=76))]
    rfl
  rw [he]
  simp only [state, pcs, shapes, templates, Nat.reduceSub]
  have hk60 : StaggerModeSeven.physicalKey 60 = StaggerAlgorithm.physicalKey 60 := by
    unfold StaggerModeSeven.physicalKey
    rw [if_neg (by decide : ¬StaggerModeSeven.enabled 60)]
  rw [hk60]
  have hk61 : StaggerModeSeven.physicalKey 61 = StaggerAlgorithm.physicalKey 61 := by
    unfold StaggerModeSeven.physicalKey
    rw [if_neg (by decide : ¬StaggerModeSeven.enabled 61)]
  rw [hk61]
  exact CorePaired61.run s h4 q right rho hstack hrun hactive
#print axioms boundary61
end Challenge.Ripemd160.Submission.Proofs.Bytecode.Local20261028.RoundComposition
