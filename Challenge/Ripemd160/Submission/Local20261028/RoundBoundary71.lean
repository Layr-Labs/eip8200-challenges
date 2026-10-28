import Challenge.Ripemd160.Submission.Local20261028.RoundSchedule
set_option warningAsError true
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.Local20261028.RoundComposition
open EvmSemantics EvmSemantics.EVM YulEvmCompiler Challenge.EvmProof
open Paired144WordRound StackRoundTrace
theorem boundary71 (s : State) (h4 : UInt256) (q right : WordLane) (rho : List UInt256)
    (hstack : rho.length ≤ 900) (hrun : s.halt = .Running) (hactive : 34 ≤ s.activeWords.toNat) :
    runInstrSeq (templates 71) (state s h4 right rho 71 q) =
      some (state s h4 right rho 72 (StaggerModeSeven.step 71 (CoreModel.message s.memory 71) q)) := by
  have he : StaggerModeSeven.step 71 (CoreModel.message s.memory 71) q = CorePaired71.eval s.memory q := by
    unfold StaggerModeSeven.step
    rw [if_neg (by decide : ¬StaggerModeSeven.enabled 71)]
    unfold StaggerTerminal75.step
    rw [if_neg (by decide : ¬(71=75 ∨ 71=76))]
    rfl
  rw [he]
  simp only [state, pcs, shapes, templates, Nat.reduceSub]
  have hk70 : StaggerModeSeven.physicalKey 70 = StaggerAlgorithm.physicalKey 70 := by
    unfold StaggerModeSeven.physicalKey
    rw [if_neg (by decide : ¬StaggerModeSeven.enabled 70)]
  rw [hk70]
  have hk71 : StaggerModeSeven.physicalKey 71 = StaggerAlgorithm.physicalKey 71 := by
    unfold StaggerModeSeven.physicalKey
    rw [if_neg (by decide : ¬StaggerModeSeven.enabled 71)]
  rw [hk71]
  exact CorePaired71.run s h4 q right rho hstack hrun hactive
#print axioms boundary71
end Challenge.Ripemd160.Submission.Proofs.Bytecode.Local20261028.RoundComposition
