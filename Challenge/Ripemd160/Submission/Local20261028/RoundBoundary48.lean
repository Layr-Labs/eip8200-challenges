import Challenge.Ripemd160.Submission.Local20261028.RoundSchedule
set_option warningAsError true
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.Local20261028.RoundComposition
open EvmSemantics EvmSemantics.EVM YulEvmCompiler Challenge.EvmProof
open Paired144WordRound StackRoundTrace
theorem boundary48 (s : State) (h4 : UInt256) (q right : WordLane) (rho : List UInt256)
    (hstack : rho.length ≤ 900) (hrun : s.halt = .Running) (hactive : 34 ≤ s.activeWords.toNat) :
    runInstrSeq (templates 48) (state s h4 right rho 48 q) =
      some (state s h4 right rho 49 (StaggerModeSeven.step 48 (CoreModel.message s.memory 48) q)) := by
  have he : StaggerModeSeven.step 48 (CoreModel.message s.memory 48) q = CorePaired48.eval s.memory q := by
    unfold StaggerModeSeven.step
    rw [if_neg (by decide : ¬StaggerModeSeven.enabled 48)]
    unfold StaggerTerminal75.step
    rw [if_neg (by decide : ¬(48=75 ∨ 48=76))]
    rfl
  rw [he]
  simp only [state, pcs, shapes, templates, Nat.reduceSub]
  have hk48 : StaggerModeSeven.physicalKey 48 = StaggerAlgorithm.physicalKey 48 := by
    unfold StaggerModeSeven.physicalKey
    rw [if_neg (by decide : ¬StaggerModeSeven.enabled 48)]
  rw [hk48]
  exact CorePaired48.run s h4 q right rho hstack hrun hactive
#print axioms boundary48
end Challenge.Ripemd160.Submission.Proofs.Bytecode.Local20261028.RoundComposition
