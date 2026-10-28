import Challenge.Ripemd160.Submission.Local20261028.RoundSchedule
set_option warningAsError true
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.Local20261028.RoundComposition
open EvmSemantics EvmSemantics.EVM YulEvmCompiler Challenge.EvmProof
open Paired144WordRound StackRoundTrace
theorem boundary67 (s : State) (h4 : UInt256) (q right : WordLane) (rho : List UInt256)
    (hstack : rho.length ≤ 900) (hrun : s.halt = .Running) (hactive : 34 ≤ s.activeWords.toNat) :
    runInstrSeq (templates 67) (state s h4 right rho 67 q) =
      some (state s h4 right rho 68 (StaggerModeSeven.step 67 (CoreModel.message s.memory 67) q)) := by
  have he : StaggerModeSeven.step 67 (CoreModel.message s.memory 67) q = CorePaired67.eval s.memory q := by
    unfold StaggerModeSeven.step
    rw [if_neg (by decide : ¬StaggerModeSeven.enabled 67)]
    unfold StaggerTerminal75.step
    rw [if_neg (by decide : ¬(67=75 ∨ 67=76))]
    rfl
  rw [he]
  simp only [state, pcs, shapes, templates, Nat.reduceSub]
  have hk66 : StaggerModeSeven.physicalKey 66 = StaggerAlgorithm.physicalKey 66 := by
    unfold StaggerModeSeven.physicalKey
    rw [if_neg (by decide : ¬StaggerModeSeven.enabled 66)]
  rw [hk66]
  have hk67 : StaggerModeSeven.physicalKey 67 = StaggerAlgorithm.physicalKey 67 := by
    unfold StaggerModeSeven.physicalKey
    rw [if_neg (by decide : ¬StaggerModeSeven.enabled 67)]
  rw [hk67]
  exact CorePaired67.run s h4 q right rho hstack hrun hactive
#print axioms boundary67
end Challenge.Ripemd160.Submission.Proofs.Bytecode.Local20261028.RoundComposition
