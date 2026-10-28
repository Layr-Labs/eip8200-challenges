import Challenge.Ripemd160.Submission.Local20261028.RoundSchedule
set_option warningAsError true
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.Local20261028.RoundComposition
open EvmSemantics EvmSemantics.EVM YulEvmCompiler Challenge.EvmProof
open Paired144WordRound StackRoundTrace
theorem boundary20 (s : State) (h4 : UInt256) (q right : WordLane) (rho : List UInt256)
    (hstack : rho.length ≤ 900) (hrun : s.halt = .Running) (hactive : 34 ≤ s.activeWords.toNat) :
    runInstrSeq (templates 20) (state s h4 right rho 20 q) =
      some (state s h4 right rho 21 (StaggerModeSeven.step 20 (CoreModel.message s.memory 20) q)) := by
  have he : StaggerModeSeven.step 20 (CoreModel.message s.memory 20) q = CorePaired20.eval s.memory q := by
    unfold StaggerModeSeven.step
    rw [if_neg (by decide : ¬StaggerModeSeven.enabled 20)]
    unfold StaggerTerminal75.step
    rw [if_neg (by decide : ¬(20=75 ∨ 20=76))]
    rfl
  rw [he]
  simp only [state, pcs, shapes, templates, Nat.reduceSub]
  have hk19 : StaggerModeSeven.physicalKey 19 = StaggerAlgorithm.physicalKey 19 := by
    unfold StaggerModeSeven.physicalKey
    rw [if_neg (by decide : ¬StaggerModeSeven.enabled 19)]
  rw [hk19]
  have hk20 : StaggerModeSeven.physicalKey 20 = StaggerAlgorithm.physicalKey 20 := by
    unfold StaggerModeSeven.physicalKey
    rw [if_neg (by decide : ¬StaggerModeSeven.enabled 20)]
  rw [hk20]
  exact CorePaired20.run s h4 q right rho hstack hrun hactive
#print axioms boundary20
end Challenge.Ripemd160.Submission.Proofs.Bytecode.Local20261028.RoundComposition
