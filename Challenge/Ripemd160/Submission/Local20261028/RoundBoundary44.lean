import Challenge.Ripemd160.Submission.Local20261028.RoundSchedule
set_option warningAsError true
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.Local20261028.RoundComposition
open EvmSemantics EvmSemantics.EVM YulEvmCompiler Challenge.EvmProof
open Paired144WordRound StackRoundTrace
theorem boundary44 (s : State) (h4 : UInt256) (q right : WordLane) (rho : List UInt256)
    (hstack : rho.length ≤ 900) (hrun : s.halt = .Running) (hactive : 34 ≤ s.activeWords.toNat) :
    runInstrSeq (templates 44) (state s h4 right rho 44 q) =
      some (state s h4 right rho 45 (StaggerModeSeven.step 44 (CoreModel.message s.memory 44) q)) := by
  have he : StaggerModeSeven.step 44 (CoreModel.message s.memory 44) q = CorePaired44.eval s.memory q := by
    unfold StaggerModeSeven.step
    rw [if_neg (by decide : ¬StaggerModeSeven.enabled 44)]
    unfold StaggerTerminal75.step
    rw [if_neg (by decide : ¬(44=75 ∨ 44=76))]
    rfl
  rw [he]
  simp only [state, pcs, shapes, templates, Nat.reduceSub]
  have hk43 : StaggerModeSeven.physicalKey 43 = StaggerAlgorithm.physicalKey 43 := by
    unfold StaggerModeSeven.physicalKey
    rw [if_neg (by decide : ¬StaggerModeSeven.enabled 43)]
  rw [hk43]
  have hk44 : StaggerModeSeven.physicalKey 44 = StaggerAlgorithm.physicalKey 44 := by
    unfold StaggerModeSeven.physicalKey
    rw [if_neg (by decide : ¬StaggerModeSeven.enabled 44)]
  rw [hk44]
  exact CorePaired44.run s h4 q right rho hstack hrun hactive
#print axioms boundary44
end Challenge.Ripemd160.Submission.Proofs.Bytecode.Local20261028.RoundComposition
