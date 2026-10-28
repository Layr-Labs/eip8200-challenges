import Challenge.Ripemd160.Submission.Local20261028.RoundSchedule
set_option warningAsError true
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.Local20261028.RoundComposition
open EvmSemantics EvmSemantics.EVM YulEvmCompiler Challenge.EvmProof
open Paired144WordRound StackRoundTrace
theorem boundary3 (s : State) (h4 : UInt256) (q right : WordLane) (rho : List UInt256)
    (hstack : rho.length ≤ 900) (hrun : s.halt = .Running) (hactive : 34 ≤ s.activeWords.toNat) :
    runInstrSeq (templates 3) (state s h4 right rho 3 q) =
      some (state s h4 right rho 4 (StaggerModeSeven.step 3 (CoreModel.message s.memory 3) q)) := by
  have he : StaggerModeSeven.step 3 (CoreModel.message s.memory 3) q = CorePaired3.eval s.memory q := by
    unfold StaggerModeSeven.step
    rw [if_neg (by decide : ¬StaggerModeSeven.enabled 3)]
    unfold StaggerTerminal75.step
    rw [if_neg (by decide : ¬(3=75 ∨ 3=76))]
    rfl
  rw [he]
  simp only [state, pcs, shapes, templates, Nat.reduceSub]
  have hk2 : StaggerModeSeven.physicalKey 2 = StaggerAlgorithm.physicalKey 2 := by
    unfold StaggerModeSeven.physicalKey
    rw [if_neg (by decide : ¬StaggerModeSeven.enabled 2)]
  rw [hk2]
  have hk3 : StaggerModeSeven.physicalKey 3 = StaggerAlgorithm.physicalKey 3 := by
    unfold StaggerModeSeven.physicalKey
    rw [if_neg (by decide : ¬StaggerModeSeven.enabled 3)]
  rw [hk3]
  exact CorePaired3.run s h4 q right rho hstack hrun hactive
#print axioms boundary3
end Challenge.Ripemd160.Submission.Proofs.Bytecode.Local20261028.RoundComposition
