import Challenge.Ripemd160.Submission.Local20261028.RoundSchedule
set_option warningAsError true
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.Local20261028.RoundComposition
open EvmSemantics EvmSemantics.EVM YulEvmCompiler Challenge.EvmProof
open Paired144WordRound StackRoundTrace
theorem boundary16 (s : State) (h4 : UInt256) (q right : WordLane) (rho : List UInt256)
    (hstack : rho.length ≤ 900) (hrun : s.halt = .Running) (hactive : 34 ≤ s.activeWords.toNat) :
    runInstrSeq (templates 16) (state s h4 right rho 16 q) =
      some (state s h4 right rho 17 (StaggerModeSeven.step 16 (CoreModel.message s.memory 16) q)) := by
  have he : StaggerModeSeven.step 16 (CoreModel.message s.memory 16) q = CorePaired16.eval s.memory q := by
    unfold StaggerModeSeven.step
    rw [if_neg (by decide : ¬StaggerModeSeven.enabled 16)]
    unfold StaggerTerminal75.step
    rw [if_neg (by decide : ¬(16=75 ∨ 16=76))]
    rfl
  rw [he]
  simp only [state, pcs, shapes, templates, Nat.reduceSub]
  have hk15 : StaggerModeSeven.physicalKey 15 = StaggerAlgorithm.physicalKey 15 := by
    unfold StaggerModeSeven.physicalKey
    rw [if_neg (by decide : ¬StaggerModeSeven.enabled 15)]
  rw [hk15]
  have hk16 : StaggerModeSeven.physicalKey 16 = StaggerAlgorithm.physicalKey 16 := by
    unfold StaggerModeSeven.physicalKey
    rw [if_neg (by decide : ¬StaggerModeSeven.enabled 16)]
  rw [hk16]
  exact CorePaired16.run s h4 q right rho hstack hrun hactive
#print axioms boundary16
end Challenge.Ripemd160.Submission.Proofs.Bytecode.Local20261028.RoundComposition
