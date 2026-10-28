import Challenge.Ripemd160.Submission.Local20261028.RoundSchedule
set_option warningAsError true
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.Local20261028.RoundComposition
open EvmSemantics EvmSemantics.EVM YulEvmCompiler Challenge.EvmProof
open Paired144WordRound StackRoundTrace
theorem boundary57 (s : State) (h4 : UInt256) (q right : WordLane) (rho : List UInt256)
    (hstack : rho.length ≤ 900) (hrun : s.halt = .Running) (hactive : 34 ≤ s.activeWords.toNat) :
    runInstrSeq (templates 57) (state s h4 right rho 57 q) =
      some (state s h4 right rho 58 (StaggerModeSeven.step 57 (CoreModel.message s.memory 57) q)) := by
  have he : StaggerModeSeven.step 57 (CoreModel.message s.memory 57) q = CorePaired57.eval s.memory q := by
    unfold StaggerModeSeven.step
    rw [if_neg (by decide : ¬StaggerModeSeven.enabled 57)]
    unfold StaggerTerminal75.step
    rw [if_neg (by decide : ¬(57=75 ∨ 57=76))]
    rfl
  rw [he]
  simp only [state, pcs, shapes, templates, Nat.reduceSub]
  have hk56 : StaggerModeSeven.physicalKey 56 = StaggerAlgorithm.physicalKey 56 := by
    unfold StaggerModeSeven.physicalKey
    rw [if_neg (by decide : ¬StaggerModeSeven.enabled 56)]
  rw [hk56]
  have hk57 : StaggerModeSeven.physicalKey 57 = StaggerAlgorithm.physicalKey 57 := by
    unfold StaggerModeSeven.physicalKey
    rw [if_neg (by decide : ¬StaggerModeSeven.enabled 57)]
  rw [hk57]
  exact CorePaired57.run s h4 q right rho hstack hrun hactive
#print axioms boundary57
end Challenge.Ripemd160.Submission.Proofs.Bytecode.Local20261028.RoundComposition
