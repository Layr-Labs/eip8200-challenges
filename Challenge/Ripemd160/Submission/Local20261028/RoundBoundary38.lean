import Challenge.Ripemd160.Submission.Local20261028.RoundSchedule
set_option warningAsError true
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.Local20261028.RoundComposition
open EvmSemantics EvmSemantics.EVM YulEvmCompiler Challenge.EvmProof
open Paired144WordRound StackRoundTrace
theorem boundary38 (s : State) (h4 : UInt256) (q right : WordLane) (rho : List UInt256)
    (hstack : rho.length ≤ 900) (hrun : s.halt = .Running) (hactive : 34 ≤ s.activeWords.toNat) :
    runInstrSeq (templates 38) (state s h4 right rho 38 q) =
      some (state s h4 right rho 39 (StaggerModeSeven.step 38 (CoreModel.message s.memory 38) q)) := by
  have he : StaggerModeSeven.step 38 (CoreModel.message s.memory 38) q = CorePaired38.eval s.memory q := by
    unfold StaggerModeSeven.step
    rw [if_neg (by decide : ¬StaggerModeSeven.enabled 38)]
    unfold StaggerTerminal75.step
    rw [if_neg (by decide : ¬(38=75 ∨ 38=76))]
    rfl
  rw [he]
  simp only [state, pcs, shapes, templates, Nat.reduceSub]
  have hk37 : StaggerModeSeven.physicalKey 37 = StaggerAlgorithm.physicalKey 37 := by
    unfold StaggerModeSeven.physicalKey
    rw [if_neg (by decide : ¬StaggerModeSeven.enabled 37)]
  rw [hk37]
  have hk38 : StaggerModeSeven.physicalKey 38 = StaggerAlgorithm.physicalKey 38 := by
    unfold StaggerModeSeven.physicalKey
    rw [if_neg (by decide : ¬StaggerModeSeven.enabled 38)]
  rw [hk38]
  exact CorePaired38.run s h4 q right rho hstack hrun hactive
#print axioms boundary38
end Challenge.Ripemd160.Submission.Proofs.Bytecode.Local20261028.RoundComposition
