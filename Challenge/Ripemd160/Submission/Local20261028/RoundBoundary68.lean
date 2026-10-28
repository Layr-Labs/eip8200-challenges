import Challenge.Ripemd160.Submission.Local20261028.RoundSchedule
set_option warningAsError true
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.Local20261028.RoundComposition
open EvmSemantics EvmSemantics.EVM YulEvmCompiler Challenge.EvmProof
open Paired144WordRound StackRoundTrace
theorem boundary68 (s : State) (h4 : UInt256) (q right : WordLane) (rho : List UInt256)
    (hstack : rho.length ≤ 900) (hrun : s.halt = .Running) (hactive : 34 ≤ s.activeWords.toNat) :
    runInstrSeq (templates 68) (state s h4 right rho 68 q) =
      some (state s h4 right rho 69 (StaggerModeSeven.step 68 (CoreModel.message s.memory 68) q)) := by
  have he : StaggerModeSeven.step 68 (CoreModel.message s.memory 68) q = CorePaired68.eval s.memory q := by
    unfold StaggerModeSeven.step
    rw [if_neg (by decide : ¬StaggerModeSeven.enabled 68)]
    unfold StaggerTerminal75.step
    rw [if_neg (by decide : ¬(68=75 ∨ 68=76))]
    rfl
  rw [he]
  simp only [state, pcs, shapes, templates, Nat.reduceSub]
  have hk67 : StaggerModeSeven.physicalKey 67 = StaggerAlgorithm.physicalKey 67 := by
    unfold StaggerModeSeven.physicalKey
    rw [if_neg (by decide : ¬StaggerModeSeven.enabled 67)]
  rw [hk67]
  have hk68 : StaggerModeSeven.physicalKey 68 = StaggerAlgorithm.physicalKey 68 := by
    unfold StaggerModeSeven.physicalKey
    rw [if_neg (by decide : ¬StaggerModeSeven.enabled 68)]
  rw [hk68]
  exact CorePaired68.run s h4 q right rho hstack hrun hactive
#print axioms boundary68
end Challenge.Ripemd160.Submission.Proofs.Bytecode.Local20261028.RoundComposition
