import Challenge.Ripemd160.Submission.Local20261028.RoundSchedule
set_option warningAsError true
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.Local20261028.RoundComposition
open EvmSemantics EvmSemantics.EVM YulEvmCompiler Challenge.EvmProof
open Paired144WordRound StackRoundTrace
theorem boundary22 (s : State) (h4 : UInt256) (q right : WordLane) (rho : List UInt256)
    (hstack : rho.length ≤ 900) (hrun : s.halt = .Running) (hactive : 34 ≤ s.activeWords.toNat) :
    runInstrSeq (templates 22) (state s h4 right rho 22 q) =
      some (state s h4 right rho 23 (StaggerModeSeven.step 22 (CoreModel.message s.memory 22) q)) := by
  have he : StaggerModeSeven.step 22 (CoreModel.message s.memory 22) q = CorePaired22.eval s.memory q := by
    unfold StaggerModeSeven.step
    rw [if_neg (by decide : ¬StaggerModeSeven.enabled 22)]
    unfold StaggerTerminal75.step
    rw [if_neg (by decide : ¬(22=75 ∨ 22=76))]
    rfl
  rw [he]
  simp only [state, pcs, shapes, templates, Nat.reduceSub]
  have hk21 : StaggerModeSeven.physicalKey 21 = StaggerAlgorithm.physicalKey 21 := by
    unfold StaggerModeSeven.physicalKey
    rw [if_neg (by decide : ¬StaggerModeSeven.enabled 21)]
  rw [hk21]
  have hk22 : StaggerModeSeven.physicalKey 22 = StaggerAlgorithm.physicalKey 22 := by
    unfold StaggerModeSeven.physicalKey
    rw [if_neg (by decide : ¬StaggerModeSeven.enabled 22)]
  rw [hk22]
  exact CorePaired22.run s h4 q right rho hstack hrun hactive
#print axioms boundary22
end Challenge.Ripemd160.Submission.Proofs.Bytecode.Local20261028.RoundComposition
