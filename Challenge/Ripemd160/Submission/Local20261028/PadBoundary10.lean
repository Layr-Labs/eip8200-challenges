import Challenge.Ripemd160.Submission.Local20261028.PadSchedule
set_option warningAsError true
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.Local20261028.PadComposition
open EvmSemantics EvmSemantics.EVM YulEvmCompiler Challenge.EvmProof
open Paired144WordRound StackRoundTrace
theorem boundary10 (s : State) (len h4 : UInt256) (q right : WordLane) (rho : List UInt256)
    (hstack : rho.length ≤ 900) (hrun : s.halt = .Running) (hactive : 34 ≤ s.activeWords.toNat)
    (hcal : UInt256.ofNat s.executionEnv.calldata.size = len)
    (hmem : MachineState.readWord s.memory 0 = PadValues.load len 162) :
    runInstrSeq (templates 10) (state s len h4 right rho 10 q) =
      some (state s len h4 right rho 11 (StaggerModeSeven.step 10 (PadModel.message len 10) q)) := by
  have he : StaggerModeSeven.step 10 (PadModel.message len 10) q = PadCore10.eval len q := by
    unfold StaggerModeSeven.step
    rw [if_neg (by decide : ¬StaggerModeSeven.enabled 10)]
    unfold StaggerTerminal75.step
    rw [if_neg (by decide : ¬(10=75 ∨ 10=76))]
    rfl
  rw [he]
  simp only [state, pcs, shapes, templates, Nat.reduceSub]
  have hk9 : StaggerModeSeven.physicalKey 9 = StaggerAlgorithm.physicalKey 9 := by
    unfold StaggerModeSeven.physicalKey
    rw [if_neg (by decide : ¬StaggerModeSeven.enabled 9)]
  rw [hk9]
  have hk10 : StaggerModeSeven.physicalKey 10 = StaggerAlgorithm.physicalKey 10 := by
    unfold StaggerModeSeven.physicalKey
    rw [if_neg (by decide : ¬StaggerModeSeven.enabled 10)]
  rw [hk10]
  exact PadCore10.run s len h4 q right rho hstack hrun hactive hcal hmem
#print axioms boundary10
end Challenge.Ripemd160.Submission.Proofs.Bytecode.Local20261028.PadComposition
