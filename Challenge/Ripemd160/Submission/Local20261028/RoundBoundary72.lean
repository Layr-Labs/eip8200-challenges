import Challenge.Ripemd160.Submission.Local20261028.RoundSchedule
set_option warningAsError true
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.Local20261028.RoundComposition
open EvmSemantics EvmSemantics.EVM YulEvmCompiler Challenge.EvmProof
open Paired144WordRound StackRoundTrace
theorem boundary72 (s : State) (h4 : UInt256) (q right : WordLane) (rho : List UInt256)
    (hstack : rho.length ≤ 900) (hrun : s.halt = .Running) (hactive : 34 ≤ s.activeWords.toNat) :
    runInstrSeq (templates 72) (state s h4 right rho 72 q) =
      some (state s h4 right rho 73 (StaggerModeSeven.step 72 (CoreModel.message s.memory 72) q)) := by
  have he : StaggerModeSeven.step 72 (CoreModel.message s.memory 72) q = CorePaired72.eval s.memory q := by
    unfold StaggerModeSeven.step
    rw [if_neg (by decide : ¬StaggerModeSeven.enabled 72)]
    unfold StaggerTerminal75.step
    rw [if_neg (by decide : ¬(72=75 ∨ 72=76))]
    rfl
  rw [he]
  simp only [state, pcs, shapes, templates, Nat.reduceSub]
  have hk71 : StaggerModeSeven.physicalKey 71 = StaggerAlgorithm.physicalKey 71 := by
    unfold StaggerModeSeven.physicalKey
    rw [if_neg (by decide : ¬StaggerModeSeven.enabled 71)]
  rw [hk71]
  have hk72 : StaggerModeSeven.physicalKey 72 = StaggerAlgorithm.physicalKey 72 := by
    unfold StaggerModeSeven.physicalKey
    rw [if_neg (by decide : ¬StaggerModeSeven.enabled 72)]
  rw [hk72]
  exact CorePaired72.run s h4 q right rho hstack hrun hactive
#print axioms boundary72
end Challenge.Ripemd160.Submission.Proofs.Bytecode.Local20261028.RoundComposition
