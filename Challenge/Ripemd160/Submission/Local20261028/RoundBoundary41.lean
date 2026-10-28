import Challenge.Ripemd160.Submission.Local20261028.RoundSchedule
set_option warningAsError true
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.Local20261028.RoundComposition
open EvmSemantics EvmSemantics.EVM YulEvmCompiler Challenge.EvmProof
open Paired144WordRound StackRoundTrace
theorem boundary41 (s : State) (h4 : UInt256) (q right : WordLane) (rho : List UInt256)
    (hstack : rho.length ≤ 900) (hrun : s.halt = .Running) (hactive : 34 ≤ s.activeWords.toNat) :
    runInstrSeq (templates 41) (state s h4 right rho 41 q) =
      some (state s h4 right rho 42 (StaggerModeSeven.step 41 (CoreModel.message s.memory 41) q)) := by
  have he : StaggerModeSeven.step 41 (CoreModel.message s.memory 41) q = CorePaired41.eval s.memory q := by
    unfold StaggerModeSeven.step
    rw [if_neg (by decide : ¬StaggerModeSeven.enabled 41)]
    unfold StaggerTerminal75.step
    rw [if_neg (by decide : ¬(41=75 ∨ 41=76))]
    rfl
  rw [he]
  simp only [state, pcs, shapes, templates, Nat.reduceSub]
  have hk40 : StaggerModeSeven.physicalKey 40 = StaggerAlgorithm.physicalKey 40 := by
    unfold StaggerModeSeven.physicalKey
    rw [if_neg (by decide : ¬StaggerModeSeven.enabled 40)]
  rw [hk40]
  have hk41 : StaggerModeSeven.physicalKey 41 = StaggerAlgorithm.physicalKey 41 := by
    unfold StaggerModeSeven.physicalKey
    rw [if_neg (by decide : ¬StaggerModeSeven.enabled 41)]
  rw [hk41]
  exact CorePaired41.run s h4 q right rho hstack hrun hactive
#print axioms boundary41
end Challenge.Ripemd160.Submission.Proofs.Bytecode.Local20261028.RoundComposition
