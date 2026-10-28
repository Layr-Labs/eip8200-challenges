import Challenge.Ripemd160.Submission.Local20261028.RoundSchedule
set_option warningAsError true
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.Local20261028.RoundComposition
open EvmSemantics EvmSemantics.EVM YulEvmCompiler Challenge.EvmProof
open Paired144WordRound StackRoundTrace
theorem boundary73 (s : State) (h4 : UInt256) (q right : WordLane) (rho : List UInt256)
    (hstack : rho.length ≤ 900) (hrun : s.halt = .Running) (hactive : 34 ≤ s.activeWords.toNat) :
    runInstrSeq (templates 73) (state s h4 right rho 73 q) =
      some (state s h4 right rho 74 (StaggerModeSeven.step 73 (CoreModel.message s.memory 73) q)) := by
  have he : StaggerModeSeven.step 73 (CoreModel.message s.memory 73) q = CorePaired73.eval s.memory q := by
    unfold StaggerModeSeven.step
    rw [if_neg (by decide : ¬StaggerModeSeven.enabled 73)]
    unfold StaggerTerminal75.step
    rw [if_neg (by decide : ¬(73=75 ∨ 73=76))]
    rfl
  rw [he]
  simp only [state, pcs, shapes, templates, Nat.reduceSub]
  have hk72 : StaggerModeSeven.physicalKey 72 = StaggerAlgorithm.physicalKey 72 := by
    unfold StaggerModeSeven.physicalKey
    rw [if_neg (by decide : ¬StaggerModeSeven.enabled 72)]
  rw [hk72]
  have hk73 : StaggerModeSeven.physicalKey 73 = StaggerAlgorithm.physicalKey 73 := by
    unfold StaggerModeSeven.physicalKey
    rw [if_neg (by decide : ¬StaggerModeSeven.enabled 73)]
  rw [hk73]
  exact CorePaired73.run s h4 q right rho hstack hrun hactive
#print axioms boundary73
end Challenge.Ripemd160.Submission.Proofs.Bytecode.Local20261028.RoundComposition
