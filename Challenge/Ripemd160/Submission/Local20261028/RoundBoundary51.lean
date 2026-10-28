import Challenge.Ripemd160.Submission.Local20261028.RoundSchedule
set_option warningAsError true
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.Local20261028.RoundComposition
open EvmSemantics EvmSemantics.EVM YulEvmCompiler Challenge.EvmProof
open Paired144WordRound StackRoundTrace
theorem boundary51 (s : State) (h4 : UInt256) (q right : WordLane) (rho : List UInt256)
    (hstack : rho.length ≤ 900) (hrun : s.halt = .Running) (hactive : 34 ≤ s.activeWords.toNat) :
    runInstrSeq (templates 51) (state s h4 right rho 51 q) =
      some (state s h4 right rho 52 (StaggerModeSeven.step 51 (CoreModel.message s.memory 51) q)) := by
  have he : StaggerModeSeven.step 51 (CoreModel.message s.memory 51) q = CorePaired51.eval s.memory q := by
    unfold StaggerModeSeven.step
    rw [if_neg (by decide : ¬StaggerModeSeven.enabled 51)]
    unfold StaggerTerminal75.step
    rw [if_neg (by decide : ¬(51=75 ∨ 51=76))]
    rfl
  rw [he]
  simp only [state, pcs, shapes, templates, Nat.reduceSub]
  have hk50 : StaggerModeSeven.physicalKey 50 = StaggerAlgorithm.physicalKey 50 := by
    unfold StaggerModeSeven.physicalKey
    rw [if_neg (by decide : ¬StaggerModeSeven.enabled 50)]
  rw [hk50]
  have hk51 : StaggerModeSeven.physicalKey 51 = StaggerAlgorithm.physicalKey 51 := by
    unfold StaggerModeSeven.physicalKey
    rw [if_neg (by decide : ¬StaggerModeSeven.enabled 51)]
  rw [hk51]
  exact CorePaired51.run s h4 q right rho hstack hrun hactive
#print axioms boundary51
end Challenge.Ripemd160.Submission.Proofs.Bytecode.Local20261028.RoundComposition
