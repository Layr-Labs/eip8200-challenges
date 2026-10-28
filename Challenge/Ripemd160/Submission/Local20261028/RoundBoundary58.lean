import Challenge.Ripemd160.Submission.Local20261028.RoundSchedule
set_option warningAsError true
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.Local20261028.RoundComposition
open EvmSemantics EvmSemantics.EVM YulEvmCompiler Challenge.EvmProof
open Paired144WordRound StackRoundTrace
theorem boundary58 (s : State) (h4 : UInt256) (q right : WordLane) (rho : List UInt256)
    (hstack : rho.length ≤ 900) (hrun : s.halt = .Running) (hactive : 34 ≤ s.activeWords.toNat) :
    runInstrSeq (templates 58) (state s h4 right rho 58 q) =
      some (state s h4 right rho 59 (StaggerModeSeven.step 58 (CoreModel.message s.memory 58) q)) := by
  have he : StaggerModeSeven.step 58 (CoreModel.message s.memory 58) q = CorePaired58.eval s.memory q := by
    unfold StaggerModeSeven.step
    rw [if_neg (by decide : ¬StaggerModeSeven.enabled 58)]
    unfold StaggerTerminal75.step
    rw [if_neg (by decide : ¬(58=75 ∨ 58=76))]
    rfl
  rw [he]
  simp only [state, pcs, shapes, templates, Nat.reduceSub]
  have hk57 : StaggerModeSeven.physicalKey 57 = StaggerAlgorithm.physicalKey 57 := by
    unfold StaggerModeSeven.physicalKey
    rw [if_neg (by decide : ¬StaggerModeSeven.enabled 57)]
  rw [hk57]
  have hk58 : StaggerModeSeven.physicalKey 58 = StaggerAlgorithm.physicalKey 58 := by
    unfold StaggerModeSeven.physicalKey
    rw [if_neg (by decide : ¬StaggerModeSeven.enabled 58)]
  rw [hk58]
  exact CorePaired58.run s h4 q right rho hstack hrun hactive
#print axioms boundary58
end Challenge.Ripemd160.Submission.Proofs.Bytecode.Local20261028.RoundComposition
