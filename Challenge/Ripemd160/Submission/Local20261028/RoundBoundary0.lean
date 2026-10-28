import Challenge.Ripemd160.Submission.Local20261028.RoundSchedule
set_option warningAsError true
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.Local20261028.RoundComposition
open EvmSemantics EvmSemantics.EVM YulEvmCompiler Challenge.EvmProof
open Paired144WordRound StackRoundTrace
theorem boundary0 (s : State) (h4 : UInt256) (q right : WordLane) (rho : List UInt256)
    (hstack : rho.length ≤ 900) (hrun : s.halt = .Running) (hactive : 34 ≤ s.activeWords.toNat) :
    runInstrSeq (templates 0) (state s h4 right rho 0 q) =
      some (state s h4 right rho 1 (StaggerModeSeven.step 0 (CoreModel.message s.memory 0) q)) := by
  have he : StaggerModeSeven.step 0 (CoreModel.message s.memory 0) q = CorePaired0.eval s.memory q := by
    unfold StaggerModeSeven.step
    rw [if_neg (by decide : ¬StaggerModeSeven.enabled 0)]
    unfold StaggerTerminal75.step
    rw [if_neg (by decide : ¬(0=75 ∨ 0=76))]
    rfl
  rw [he]
  simp only [state, pcs, shapes, templates, Nat.reduceSub]
  have hk0 : StaggerModeSeven.physicalKey 0 = StaggerAlgorithm.physicalKey 0 := by
    unfold StaggerModeSeven.physicalKey
    rw [if_neg (by decide : ¬StaggerModeSeven.enabled 0)]
  rw [hk0]
  exact CorePaired0.run s h4 q right rho hstack hrun hactive
#print axioms boundary0
end Challenge.Ripemd160.Submission.Proofs.Bytecode.Local20261028.RoundComposition
