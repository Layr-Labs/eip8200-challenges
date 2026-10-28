import Challenge.Ripemd160.Submission.Local20261028.RoundSchedule
set_option warningAsError true
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.Local20261028.RoundComposition
open EvmSemantics EvmSemantics.EVM YulEvmCompiler Challenge.EvmProof
open Paired144WordRound StackRoundTrace
theorem boundary52 (s : State) (h4 : UInt256) (q right : WordLane) (rho : List UInt256)
    (hstack : rho.length ≤ 900) (hrun : s.halt = .Running) (hactive : 34 ≤ s.activeWords.toNat) :
    runInstrSeq (templates 52) (state s h4 right rho 52 q) =
      some (state s h4 right rho 53 (StaggerModeSeven.step 52 (CoreModel.message s.memory 52) q)) := by
  have he : StaggerModeSeven.step 52 (CoreModel.message s.memory 52) q = CorePaired52.eval s.memory q := by
    unfold StaggerModeSeven.step
    rw [if_neg (by decide : ¬StaggerModeSeven.enabled 52)]
    unfold StaggerTerminal75.step
    rw [if_neg (by decide : ¬(52=75 ∨ 52=76))]
    rfl
  rw [he]
  simp only [state, pcs, shapes, templates, Nat.reduceSub]
  have hk51 : StaggerModeSeven.physicalKey 51 = StaggerAlgorithm.physicalKey 51 := by
    unfold StaggerModeSeven.physicalKey
    rw [if_neg (by decide : ¬StaggerModeSeven.enabled 51)]
  rw [hk51]
  have hk52 : StaggerModeSeven.physicalKey 52 = StaggerAlgorithm.physicalKey 52 := by
    unfold StaggerModeSeven.physicalKey
    rw [if_neg (by decide : ¬StaggerModeSeven.enabled 52)]
  rw [hk52]
  exact CorePaired52.run s h4 q right rho hstack hrun hactive
#print axioms boundary52
end Challenge.Ripemd160.Submission.Proofs.Bytecode.Local20261028.RoundComposition
