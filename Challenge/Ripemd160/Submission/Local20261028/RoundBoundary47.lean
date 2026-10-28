import Challenge.Ripemd160.Submission.Local20261028.RoundSchedule
set_option warningAsError true
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.Local20261028.RoundComposition
open EvmSemantics EvmSemantics.EVM YulEvmCompiler Challenge.EvmProof
open Paired144WordRound StackRoundTrace
theorem boundary47 (s : State) (h4 : UInt256) (q right : WordLane) (rho : List UInt256)
    (hstack : rho.length ≤ 900) (hrun : s.halt = .Running) (hactive : 34 ≤ s.activeWords.toNat) :
    runInstrSeq (templates 47) (state s h4 right rho 47 q) =
      some (state s h4 right rho 48 (StaggerModeSeven.step 47 (CoreModel.message s.memory 47) q)) := by
  have he : StaggerModeSeven.step 47 (CoreModel.message s.memory 47) q = CorePaired47.eval s.memory q := by
    rfl
  rw [he]
  simp only [state, pcs, shapes, templates, Nat.reduceSub]
  exact CorePaired47.run s h4 q right rho hstack hrun hactive
#print axioms boundary47
end Challenge.Ripemd160.Submission.Proofs.Bytecode.Local20261028.RoundComposition
