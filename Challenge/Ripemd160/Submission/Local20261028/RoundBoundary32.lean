import Challenge.Ripemd160.Submission.Local20261028.RoundSchedule
set_option warningAsError true
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.Local20261028.RoundComposition
open EvmSemantics EvmSemantics.EVM YulEvmCompiler Challenge.EvmProof
open Paired144WordRound StackRoundTrace
theorem boundary32 (s : State) (h4 : UInt256) (q right : WordLane) (rho : List UInt256)
    (hstack : rho.length ≤ 900) (hrun : s.halt = .Running) (hactive : 34 ≤ s.activeWords.toNat) :
    runInstrSeq (templates 32) (state s h4 right rho 32 q) =
      some (state s h4 right rho 33 (StaggerModeSeven.step 32 (CoreModel.message s.memory 32) q)) := by
  have he : StaggerModeSeven.step 32 (CoreModel.message s.memory 32) q = CorePaired32.eval s.memory q := by
    unfold StaggerModeSeven.step
    rw [if_neg (by decide : ¬StaggerModeSeven.enabled 32)]
    unfold StaggerTerminal75.step
    rw [if_neg (by decide : ¬(32=75 ∨ 32=76))]
    rfl
  rw [he]
  simp only [state, pcs, shapes, templates, Nat.reduceSub]
  have hk31 : StaggerModeSeven.physicalKey 31 = StaggerAlgorithm.physicalKey 31 := by
    unfold StaggerModeSeven.physicalKey
    rw [if_neg (by decide : ¬StaggerModeSeven.enabled 31)]
  rw [hk31]
  have hk32 : StaggerModeSeven.physicalKey 32 = StaggerAlgorithm.physicalKey 32 := by
    unfold StaggerModeSeven.physicalKey
    rw [if_neg (by decide : ¬StaggerModeSeven.enabled 32)]
  rw [hk32]
  exact CorePaired32.run s h4 q right rho hstack hrun hactive
#print axioms boundary32
end Challenge.Ripemd160.Submission.Proofs.Bytecode.Local20261028.RoundComposition
