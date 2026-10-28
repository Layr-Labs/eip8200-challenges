import Challenge.Ripemd160.Submission.Local20261028.RoundSchedule
set_option warningAsError true
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.Local20261028.RoundComposition
open EvmSemantics EvmSemantics.EVM YulEvmCompiler Challenge.EvmProof
open Paired144WordRound StackRoundTrace
theorem boundary31 (s : State) (h4 : UInt256) (q right : WordLane) (rho : List UInt256)
    (hstack : rho.length ≤ 900) (hrun : s.halt = .Running) (hactive : 34 ≤ s.activeWords.toNat) :
    runInstrSeq (templates 31) (state s h4 right rho 31 q) =
      some (state s h4 right rho 32 (StaggerModeSeven.step 31 (CoreModel.message s.memory 31) q)) := by
  have he : StaggerModeSeven.step 31 (CoreModel.message s.memory 31) q = CorePaired31.eval s.memory q := by
    unfold StaggerModeSeven.step
    rw [if_neg (by decide : ¬StaggerModeSeven.enabled 31)]
    unfold StaggerTerminal75.step
    rw [if_neg (by decide : ¬(31=75 ∨ 31=76))]
    rfl
  rw [he]
  simp only [state, pcs, shapes, templates, Nat.reduceSub]
  have hk30 : StaggerModeSeven.physicalKey 30 = StaggerAlgorithm.physicalKey 30 := by
    unfold StaggerModeSeven.physicalKey
    rw [if_neg (by decide : ¬StaggerModeSeven.enabled 30)]
  rw [hk30]
  have hk31 : StaggerModeSeven.physicalKey 31 = StaggerAlgorithm.physicalKey 31 := by
    unfold StaggerModeSeven.physicalKey
    rw [if_neg (by decide : ¬StaggerModeSeven.enabled 31)]
  rw [hk31]
  exact CorePaired31.run s h4 q right rho hstack hrun hactive
#print axioms boundary31
end Challenge.Ripemd160.Submission.Proofs.Bytecode.Local20261028.RoundComposition
