import Challenge.Ripemd160.Submission.Local20261028.RoundSchedule
set_option warningAsError true
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.Local20261028.RoundComposition
open EvmSemantics EvmSemantics.EVM YulEvmCompiler Challenge.EvmProof
open Paired144WordRound StackRoundTrace
theorem boundary14 (s : State) (h4 : UInt256) (q right : WordLane) (rho : List UInt256)
    (hstack : rho.length ≤ 900) (hrun : s.halt = .Running) (hactive : 34 ≤ s.activeWords.toNat) :
    runInstrSeq (templates 14) (state s h4 right rho 14 q) =
      some (state s h4 right rho 15 (StaggerModeSeven.step 14 (CoreModel.message s.memory 14) q)) := by
  have he : StaggerModeSeven.step 14 (CoreModel.message s.memory 14) q = CorePaired14.eval s.memory q := by
    unfold StaggerModeSeven.step
    rw [if_neg (by decide : ¬StaggerModeSeven.enabled 14)]
    unfold StaggerTerminal75.step
    rw [if_neg (by decide : ¬(14=75 ∨ 14=76))]
    rfl
  rw [he]
  simp only [state, pcs, shapes, templates, Nat.reduceSub]
  have hk13 : StaggerModeSeven.physicalKey 13 = StaggerAlgorithm.physicalKey 13 := by
    unfold StaggerModeSeven.physicalKey
    rw [if_neg (by decide : ¬StaggerModeSeven.enabled 13)]
  rw [hk13]
  have hk14 : StaggerModeSeven.physicalKey 14 = StaggerAlgorithm.physicalKey 14 := by
    unfold StaggerModeSeven.physicalKey
    rw [if_neg (by decide : ¬StaggerModeSeven.enabled 14)]
  rw [hk14]
  exact CorePaired14.run s h4 q right rho hstack hrun hactive
#print axioms boundary14
end Challenge.Ripemd160.Submission.Proofs.Bytecode.Local20261028.RoundComposition
