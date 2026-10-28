import Challenge.Ripemd160.Submission.Local20261028.RoundSchedule
set_option warningAsError true
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.Local20261028.RoundComposition
open EvmSemantics EvmSemantics.EVM YulEvmCompiler Challenge.EvmProof
open Paired144WordRound StackRoundTrace
theorem boundary27 (s : State) (h4 : UInt256) (q right : WordLane) (rho : List UInt256)
    (hstack : rho.length ≤ 900) (hrun : s.halt = .Running) (hactive : 34 ≤ s.activeWords.toNat) :
    runInstrSeq (templates 27) (state s h4 right rho 27 q) =
      some (state s h4 right rho 28 (StaggerModeSeven.step 27 (CoreModel.message s.memory 27) q)) := by
  have he : StaggerModeSeven.step 27 (CoreModel.message s.memory 27) q = CorePaired27.eval s.memory q := by
    unfold StaggerModeSeven.step
    rw [if_neg (by decide : ¬StaggerModeSeven.enabled 27)]
    unfold StaggerTerminal75.step
    rw [if_neg (by decide : ¬(27=75 ∨ 27=76))]
    rfl
  rw [he]
  simp only [state, pcs, shapes, templates, Nat.reduceSub]
  have hk26 : StaggerModeSeven.physicalKey 26 = StaggerAlgorithm.physicalKey 26 := by
    unfold StaggerModeSeven.physicalKey
    rw [if_neg (by decide : ¬StaggerModeSeven.enabled 26)]
  rw [hk26]
  have hk27 : StaggerModeSeven.physicalKey 27 = StaggerAlgorithm.physicalKey 27 := by
    unfold StaggerModeSeven.physicalKey
    rw [if_neg (by decide : ¬StaggerModeSeven.enabled 27)]
  rw [hk27]
  exact CorePaired27.run s h4 q right rho hstack hrun hactive
#print axioms boundary27
end Challenge.Ripemd160.Submission.Proofs.Bytecode.Local20261028.RoundComposition
