import Challenge.Ripemd160.Submission.Local20261028.RoundSchedule
set_option warningAsError true
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.Local20261028.RoundComposition
open EvmSemantics EvmSemantics.EVM YulEvmCompiler Challenge.EvmProof
open Paired144WordRound StackRoundTrace
theorem boundary60 (s : State) (h4 : UInt256) (q right : WordLane) (rho : List UInt256)
    (hstack : rho.length ≤ 900) (hrun : s.halt = .Running) (hactive : 34 ≤ s.activeWords.toNat) :
    runInstrSeq (templates 60) (state s h4 right rho 60 q) =
      some (state s h4 right rho 61 (StaggerModeSeven.step 60 (CoreModel.message s.memory 60) q)) := by
  have he : StaggerModeSeven.step 60 (CoreModel.message s.memory 60) q = CorePaired60.eval s.memory q := by
    unfold StaggerModeSeven.step
    rw [if_neg (by decide : ¬StaggerModeSeven.enabled 60)]
    unfold StaggerTerminal75.step
    rw [if_neg (by decide : ¬(60=75 ∨ 60=76))]
    rfl
  rw [he]
  simp only [state, pcs, shapes, templates, Nat.reduceSub]
  have hk59 : StaggerModeSeven.physicalKey 59 = StaggerAlgorithm.physicalKey 59 := by
    unfold StaggerModeSeven.physicalKey
    rw [if_neg (by decide : ¬StaggerModeSeven.enabled 59)]
  rw [hk59]
  have hk60 : StaggerModeSeven.physicalKey 60 = StaggerAlgorithm.physicalKey 60 := by
    unfold StaggerModeSeven.physicalKey
    rw [if_neg (by decide : ¬StaggerModeSeven.enabled 60)]
  rw [hk60]
  exact CorePaired60.run s h4 q right rho hstack hrun hactive
#print axioms boundary60
end Challenge.Ripemd160.Submission.Proofs.Bytecode.Local20261028.RoundComposition
