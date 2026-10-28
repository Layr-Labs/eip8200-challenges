import Challenge.Ripemd160.Submission.Local20261028.RoundSchedule
set_option warningAsError true
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.Local20261028.RoundComposition
open EvmSemantics EvmSemantics.EVM YulEvmCompiler Challenge.EvmProof
open Paired144WordRound StackRoundTrace
theorem boundary70 (s : State) (h4 : UInt256) (q right : WordLane) (rho : List UInt256)
    (hstack : rho.length ≤ 900) (hrun : s.halt = .Running) (hactive : 34 ≤ s.activeWords.toNat) :
    runInstrSeq (templates 70) (state s h4 right rho 70 q) =
      some (state s h4 right rho 71 (StaggerModeSeven.step 70 (CoreModel.message s.memory 70) q)) := by
  have he : StaggerModeSeven.step 70 (CoreModel.message s.memory 70) q = CorePaired70.eval s.memory q := by
    unfold StaggerModeSeven.step
    rw [if_neg (by decide : ¬StaggerModeSeven.enabled 70)]
    unfold StaggerTerminal75.step
    rw [if_neg (by decide : ¬(70=75 ∨ 70=76))]
    rfl
  rw [he]
  simp only [state, pcs, shapes, templates, Nat.reduceSub]
  have hk69 : StaggerModeSeven.physicalKey 69 = StaggerAlgorithm.physicalKey 69 := by
    unfold StaggerModeSeven.physicalKey
    rw [if_neg (by decide : ¬StaggerModeSeven.enabled 69)]
  rw [hk69]
  have hk70 : StaggerModeSeven.physicalKey 70 = StaggerAlgorithm.physicalKey 70 := by
    unfold StaggerModeSeven.physicalKey
    rw [if_neg (by decide : ¬StaggerModeSeven.enabled 70)]
  rw [hk70]
  exact CorePaired70.run s h4 q right rho hstack hrun hactive
#print axioms boundary70
end Challenge.Ripemd160.Submission.Proofs.Bytecode.Local20261028.RoundComposition
