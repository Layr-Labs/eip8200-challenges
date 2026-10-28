import Challenge.Ripemd160.Submission.Local20261028.RoundSchedule
set_option warningAsError true
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.Local20261028.RoundComposition
open EvmSemantics EvmSemantics.EVM YulEvmCompiler Challenge.EvmProof
open Paired144WordRound StackRoundTrace
theorem boundary9 (s : State) (h4 : UInt256) (q right : WordLane) (rho : List UInt256)
    (hstack : rho.length ≤ 900) (hrun : s.halt = .Running) (hactive : 34 ≤ s.activeWords.toNat) :
    runInstrSeq (templates 9) (state s h4 right rho 9 q) =
      some (state s h4 right rho 10 (StaggerModeSeven.step 9 (CoreModel.message s.memory 9) q)) := by
  have he : StaggerModeSeven.step 9 (CoreModel.message s.memory 9) q = CorePaired9.eval s.memory q := by
    unfold StaggerModeSeven.step
    rw [if_neg (by decide : ¬StaggerModeSeven.enabled 9)]
    unfold StaggerTerminal75.step
    rw [if_neg (by decide : ¬(9=75 ∨ 9=76))]
    rfl
  rw [he]
  simp only [state, pcs, shapes, templates, Nat.reduceSub]
  have hk8 : StaggerModeSeven.physicalKey 8 = StaggerAlgorithm.physicalKey 8 := by
    unfold StaggerModeSeven.physicalKey
    rw [if_neg (by decide : ¬StaggerModeSeven.enabled 8)]
  rw [hk8]
  have hk9 : StaggerModeSeven.physicalKey 9 = StaggerAlgorithm.physicalKey 9 := by
    unfold StaggerModeSeven.physicalKey
    rw [if_neg (by decide : ¬StaggerModeSeven.enabled 9)]
  rw [hk9]
  exact CorePaired9.run s h4 q right rho hstack hrun hactive
#print axioms boundary9
end Challenge.Ripemd160.Submission.Proofs.Bytecode.Local20261028.RoundComposition
