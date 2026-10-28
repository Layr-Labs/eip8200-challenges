import Challenge.Ripemd160.Submission.Local20261028.RoundSchedule
set_option warningAsError true
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.Local20261028.RoundComposition
open EvmSemantics EvmSemantics.EVM YulEvmCompiler Challenge.EvmProof
open Paired144WordRound StackRoundTrace
theorem boundary49 (s : State) (h4 : UInt256) (q right : WordLane) (rho : List UInt256)
    (hstack : rho.length ≤ 900) (hrun : s.halt = .Running) (hactive : 34 ≤ s.activeWords.toNat) :
    runInstrSeq (templates 49) (state s h4 right rho 49 q) =
      some (state s h4 right rho 50 (StaggerModeSeven.step 49 (CoreModel.message s.memory 49) q)) := by
  have he : StaggerModeSeven.step 49 (CoreModel.message s.memory 49) q = CorePaired49.eval s.memory q := by
    unfold StaggerModeSeven.step
    rw [if_neg (by decide : ¬StaggerModeSeven.enabled 49)]
    unfold StaggerTerminal75.step
    rw [if_neg (by decide : ¬(49=75 ∨ 49=76))]
    rfl
  rw [he]
  simp only [state, pcs, shapes, templates, Nat.reduceSub]
  have hk48 : StaggerModeSeven.physicalKey 48 = StaggerAlgorithm.physicalKey 48 := by
    unfold StaggerModeSeven.physicalKey
    rw [if_neg (by decide : ¬StaggerModeSeven.enabled 48)]
  rw [hk48]
  have hk49 : StaggerModeSeven.physicalKey 49 = StaggerAlgorithm.physicalKey 49 := by
    unfold StaggerModeSeven.physicalKey
    rw [if_neg (by decide : ¬StaggerModeSeven.enabled 49)]
  rw [hk49]
  exact CorePaired49.run s h4 q right rho hstack hrun hactive
#print axioms boundary49
end Challenge.Ripemd160.Submission.Proofs.Bytecode.Local20261028.RoundComposition
