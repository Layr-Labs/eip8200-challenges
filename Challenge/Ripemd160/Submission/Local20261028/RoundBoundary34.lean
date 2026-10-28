import Challenge.Ripemd160.Submission.Local20261028.RoundSchedule
set_option warningAsError true
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.Local20261028.RoundComposition
open EvmSemantics EvmSemantics.EVM YulEvmCompiler Challenge.EvmProof
open Paired144WordRound StackRoundTrace
theorem boundary34 (s : State) (h4 : UInt256) (q right : WordLane) (rho : List UInt256)
    (hstack : rho.length ≤ 900) (hrun : s.halt = .Running) (hactive : 34 ≤ s.activeWords.toNat) :
    runInstrSeq (templates 34) (state s h4 right rho 34 q) =
      some (state s h4 right rho 35 (StaggerModeSeven.step 34 (CoreModel.message s.memory 34) q)) := by
  have he : StaggerModeSeven.step 34 (CoreModel.message s.memory 34) q = CorePaired34.eval s.memory q := by
    unfold StaggerModeSeven.step
    rw [if_neg (by decide : ¬StaggerModeSeven.enabled 34)]
    unfold StaggerTerminal75.step
    rw [if_neg (by decide : ¬(34=75 ∨ 34=76))]
    rfl
  rw [he]
  simp only [state, pcs, shapes, templates, Nat.reduceSub]
  have hk33 : StaggerModeSeven.physicalKey 33 = StaggerAlgorithm.physicalKey 33 := by
    unfold StaggerModeSeven.physicalKey
    rw [if_neg (by decide : ¬StaggerModeSeven.enabled 33)]
  rw [hk33]
  have hk34 : StaggerModeSeven.physicalKey 34 = StaggerAlgorithm.physicalKey 34 := by
    unfold StaggerModeSeven.physicalKey
    rw [if_neg (by decide : ¬StaggerModeSeven.enabled 34)]
  rw [hk34]
  exact CorePaired34.run s h4 q right rho hstack hrun hactive
#print axioms boundary34
end Challenge.Ripemd160.Submission.Proofs.Bytecode.Local20261028.RoundComposition
