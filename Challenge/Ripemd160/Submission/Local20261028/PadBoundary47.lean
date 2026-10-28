import Challenge.Ripemd160.Submission.Local20261028.PadSchedule
set_option warningAsError true
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.Local20261028.PadComposition
open EvmSemantics EvmSemantics.EVM YulEvmCompiler Challenge.EvmProof
open Paired144WordRound StackRoundTrace
theorem boundary47 (s : State) (len h4 : UInt256) (q right : WordLane) (rho : List UInt256)
    (hstack : rho.length ≤ 900) (hrun : s.halt = .Running) (hactive : 34 ≤ s.activeWords.toNat)
    (hcal : UInt256.ofNat s.executionEnv.calldata.size = len)
    (hmem : MachineState.readWord s.memory 0 = PadValues.load len 162) :
    runInstrSeq (templates 47) (state s len h4 right rho 47 q) =
      some (state s len h4 right rho 48 (StaggerModeSeven.step 47 (PadModel.message len 47) q)) := by
  have he : StaggerModeSeven.step 47 (PadModel.message len 47) q = PadCore47.eval len q := by
    rfl
  rw [he]
  simp only [state, pcs, shapes, templates, Nat.reduceSub]
  exact PadCore47.run s len h4 q right rho hstack hrun hactive hcal hmem
#print axioms boundary47
end Challenge.Ripemd160.Submission.Proofs.Bytecode.Local20261028.PadComposition
