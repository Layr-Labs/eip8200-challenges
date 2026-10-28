import Challenge.Ripemd160.Submission.Local20261028.RoundSchedule
set_option warningAsError true
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.Local20261028.RoundComposition
open EvmSemantics EvmSemantics.EVM YulEvmCompiler Challenge.EvmProof
open Paired144WordRound StackRoundTrace
theorem boundary8 (s : State) (h4 : UInt256) (q right : WordLane) (rho : List UInt256)
    (hstack : rho.length ≤ 900) (hrun : s.halt = .Running) (hactive : 34 ≤ s.activeWords.toNat) :
    runInstrSeq (templates 8) (state s h4 right rho 8 q) =
      some (state s h4 right rho 9 (StaggerModeSeven.step 8 (CoreModel.message s.memory 8) q)) := by
  have he : StaggerModeSeven.step 8 (CoreModel.message s.memory 8) q = CorePaired8.eval s.memory q := by
    unfold StaggerModeSeven.step
    rw [if_neg (by decide : ¬StaggerModeSeven.enabled 8)]
    unfold StaggerTerminal75.step
    rw [if_neg (by decide : ¬(8=75 ∨ 8=76))]
    rfl
  rw [he]
  simp only [state, pcs, shapes, templates, Nat.reduceSub]
  have hk7 : StaggerModeSeven.physicalKey 7 = StaggerAlgorithm.physicalKey 7 := by
    unfold StaggerModeSeven.physicalKey
    rw [if_neg (by decide : ¬StaggerModeSeven.enabled 7)]
  rw [hk7]
  have hk8 : StaggerModeSeven.physicalKey 8 = StaggerAlgorithm.physicalKey 8 := by
    unfold StaggerModeSeven.physicalKey
    rw [if_neg (by decide : ¬StaggerModeSeven.enabled 8)]
  rw [hk8]
  exact CorePaired8.run s h4 q right rho hstack hrun hactive
#print axioms boundary8
end Challenge.Ripemd160.Submission.Proofs.Bytecode.Local20261028.RoundComposition
