import Challenge.Ripemd160.Submission.Local20261028.RoundSchedule
set_option warningAsError true
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.Local20261028.RoundComposition
open EvmSemantics EvmSemantics.EVM YulEvmCompiler Challenge.EvmProof
open Paired144WordRound StackRoundTrace
theorem boundary65 (s : State) (h4 : UInt256) (q right : WordLane) (rho : List UInt256)
    (hstack : rho.length ≤ 900) (hrun : s.halt = .Running) (hactive : 34 ≤ s.activeWords.toNat) :
    runInstrSeq (templates 65) (state s h4 right rho 65 q) =
      some (state s h4 right rho 66 (StaggerModeSeven.step 65 (CoreModel.message s.memory 65) q)) := by
  have he : StaggerModeSeven.step 65 (CoreModel.message s.memory 65) q = CorePaired65.eval s.memory q := by
    unfold StaggerModeSeven.step
    rw [if_neg (by decide : ¬StaggerModeSeven.enabled 65)]
    unfold StaggerTerminal75.step
    rw [if_neg (by decide : ¬(65=75 ∨ 65=76))]
    rfl
  rw [he]
  simp only [state, pcs, shapes, templates, Nat.reduceSub]
  have hk64 : StaggerModeSeven.physicalKey 64 = StaggerAlgorithm.physicalKey 64 := by
    unfold StaggerModeSeven.physicalKey
    rw [if_neg (by decide : ¬StaggerModeSeven.enabled 64)]
  rw [hk64]
  have hk65 : StaggerModeSeven.physicalKey 65 = StaggerAlgorithm.physicalKey 65 := by
    unfold StaggerModeSeven.physicalKey
    rw [if_neg (by decide : ¬StaggerModeSeven.enabled 65)]
  rw [hk65]
  exact CorePaired65.run s h4 q right rho hstack hrun hactive
#print axioms boundary65
end Challenge.Ripemd160.Submission.Proofs.Bytecode.Local20261028.RoundComposition
