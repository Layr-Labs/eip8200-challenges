import Challenge.Ripemd160.Submission.Local20261028.RoundSchedule
set_option warningAsError true
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.Local20261028.RoundComposition
open EvmSemantics EvmSemantics.EVM YulEvmCompiler Challenge.EvmProof
open Paired144WordRound StackRoundTrace
theorem boundary26 (s : State) (h4 : UInt256) (q right : WordLane) (rho : List UInt256)
    (hstack : rho.length ≤ 900) (hrun : s.halt = .Running) (hactive : 34 ≤ s.activeWords.toNat) :
    runInstrSeq (templates 26) (state s h4 right rho 26 q) =
      some (state s h4 right rho 27 (StaggerModeSeven.step 26 (CoreModel.message s.memory 26) q)) := by
  have he : StaggerModeSeven.step 26 (CoreModel.message s.memory 26) q = CorePaired26.eval s.memory q := by
    unfold StaggerModeSeven.step
    rw [if_neg (by decide : ¬StaggerModeSeven.enabled 26)]
    unfold StaggerTerminal75.step
    rw [if_neg (by decide : ¬(26=75 ∨ 26=76))]
    rfl
  rw [he]
  simp only [state, pcs, shapes, templates, Nat.reduceSub]
  have hk25 : StaggerModeSeven.physicalKey 25 = StaggerAlgorithm.physicalKey 25 := by
    unfold StaggerModeSeven.physicalKey
    rw [if_neg (by decide : ¬StaggerModeSeven.enabled 25)]
  rw [hk25]
  have hk26 : StaggerModeSeven.physicalKey 26 = StaggerAlgorithm.physicalKey 26 := by
    unfold StaggerModeSeven.physicalKey
    rw [if_neg (by decide : ¬StaggerModeSeven.enabled 26)]
  rw [hk26]
  exact CorePaired26.run s h4 q right rho hstack hrun hactive
#print axioms boundary26
end Challenge.Ripemd160.Submission.Proofs.Bytecode.Local20261028.RoundComposition
