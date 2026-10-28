import Challenge.Ripemd160.Submission.Local20261028.RoundSchedule
set_option warningAsError true
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.Local20261028.RoundComposition
open EvmSemantics EvmSemantics.EVM YulEvmCompiler Challenge.EvmProof
open Paired144WordRound StackRoundTrace
theorem boundary18 (s : State) (h4 : UInt256) (q right : WordLane) (rho : List UInt256)
    (hstack : rho.length ≤ 900) (hrun : s.halt = .Running) (hactive : 34 ≤ s.activeWords.toNat) :
    runInstrSeq (templates 18) (state s h4 right rho 18 q) =
      some (state s h4 right rho 19 (StaggerModeSeven.step 18 (CoreModel.message s.memory 18) q)) := by
  have he : StaggerModeSeven.step 18 (CoreModel.message s.memory 18) q = CorePaired18.eval s.memory q := by
    unfold StaggerModeSeven.step
    rw [if_neg (by decide : ¬StaggerModeSeven.enabled 18)]
    unfold StaggerTerminal75.step
    rw [if_neg (by decide : ¬(18=75 ∨ 18=76))]
    rfl
  rw [he]
  simp only [state, pcs, shapes, templates, Nat.reduceSub]
  have hk17 : StaggerModeSeven.physicalKey 17 = StaggerAlgorithm.physicalKey 17 := by
    unfold StaggerModeSeven.physicalKey
    rw [if_neg (by decide : ¬StaggerModeSeven.enabled 17)]
  rw [hk17]
  have hk18 : StaggerModeSeven.physicalKey 18 = StaggerAlgorithm.physicalKey 18 := by
    unfold StaggerModeSeven.physicalKey
    rw [if_neg (by decide : ¬StaggerModeSeven.enabled 18)]
  rw [hk18]
  exact CorePaired18.run s h4 q right rho hstack hrun hactive
#print axioms boundary18
end Challenge.Ripemd160.Submission.Proofs.Bytecode.Local20261028.RoundComposition
