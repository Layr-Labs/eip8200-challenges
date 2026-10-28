import Challenge.Ripemd160.Submission.Local20261028.RoundSchedule
set_option warningAsError true
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.Local20261028.RoundComposition
open EvmSemantics EvmSemantics.EVM YulEvmCompiler Challenge.EvmProof
open Paired144WordRound StackRoundTrace
theorem boundary25 (s : State) (h4 : UInt256) (q right : WordLane) (rho : List UInt256)
    (hstack : rho.length ≤ 900) (hrun : s.halt = .Running) (hactive : 34 ≤ s.activeWords.toNat) :
    runInstrSeq (templates 25) (state s h4 right rho 25 q) =
      some (state s h4 right rho 26 (StaggerModeSeven.step 25 (CoreModel.message s.memory 25) q)) := by
  have he : StaggerModeSeven.step 25 (CoreModel.message s.memory 25) q = CorePaired25.eval s.memory q := by
    unfold StaggerModeSeven.step
    rw [if_neg (by decide : ¬StaggerModeSeven.enabled 25)]
    unfold StaggerTerminal75.step
    rw [if_neg (by decide : ¬(25=75 ∨ 25=76))]
    rfl
  rw [he]
  simp only [state, pcs, shapes, templates, Nat.reduceSub]
  have hk24 : StaggerModeSeven.physicalKey 24 = StaggerAlgorithm.physicalKey 24 := by
    unfold StaggerModeSeven.physicalKey
    rw [if_neg (by decide : ¬StaggerModeSeven.enabled 24)]
  rw [hk24]
  have hk25 : StaggerModeSeven.physicalKey 25 = StaggerAlgorithm.physicalKey 25 := by
    unfold StaggerModeSeven.physicalKey
    rw [if_neg (by decide : ¬StaggerModeSeven.enabled 25)]
  rw [hk25]
  exact CorePaired25.run s h4 q right rho hstack hrun hactive
#print axioms boundary25
end Challenge.Ripemd160.Submission.Proofs.Bytecode.Local20261028.RoundComposition
