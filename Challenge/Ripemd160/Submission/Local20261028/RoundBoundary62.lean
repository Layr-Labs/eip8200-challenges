import Challenge.Ripemd160.Submission.Local20261028.RoundSchedule
set_option warningAsError true
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.Local20261028.RoundComposition
open EvmSemantics EvmSemantics.EVM YulEvmCompiler Challenge.EvmProof
open Paired144WordRound StackRoundTrace
theorem boundary62 (s : State) (h4 : UInt256) (q right : WordLane) (rho : List UInt256)
    (hstack : rho.length ≤ 900) (hrun : s.halt = .Running) (hactive : 34 ≤ s.activeWords.toNat) :
    runInstrSeq (templates 62) (state s h4 right rho 62 q) =
      some (state s h4 right rho 63 (StaggerModeSeven.step 62 (CoreModel.message s.memory 62) q)) := by
  have he : StaggerModeSeven.step 62 (CoreModel.message s.memory 62) q = CorePaired62.eval s.memory q := by
    unfold StaggerModeSeven.step
    rw [if_neg (by decide : ¬StaggerModeSeven.enabled 62)]
    unfold StaggerTerminal75.step
    rw [if_neg (by decide : ¬(62=75 ∨ 62=76))]
    rfl
  rw [he]
  simp only [state, pcs, shapes, templates, Nat.reduceSub]
  have hk61 : StaggerModeSeven.physicalKey 61 = StaggerAlgorithm.physicalKey 61 := by
    unfold StaggerModeSeven.physicalKey
    rw [if_neg (by decide : ¬StaggerModeSeven.enabled 61)]
  rw [hk61]
  have hk62 : StaggerModeSeven.physicalKey 62 = StaggerAlgorithm.physicalKey 62 := by
    unfold StaggerModeSeven.physicalKey
    rw [if_neg (by decide : ¬StaggerModeSeven.enabled 62)]
  rw [hk62]
  exact CorePaired62.run s h4 q right rho hstack hrun hactive
#print axioms boundary62
end Challenge.Ripemd160.Submission.Proofs.Bytecode.Local20261028.RoundComposition
