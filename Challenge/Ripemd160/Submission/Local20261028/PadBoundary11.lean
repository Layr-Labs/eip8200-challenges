import Challenge.Ripemd160.Submission.Local20261028.PadSchedule
set_option warningAsError true
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.Local20261028.PadComposition
open EvmSemantics EvmSemantics.EVM YulEvmCompiler Challenge.EvmProof
open Paired144WordRound StackRoundTrace
theorem boundary11 (s : State) (len h4 : UInt256) (q right : WordLane) (rho : List UInt256)
    (hstack : rho.length ≤ 900) (hrun : s.halt = .Running) (hactive : 34 ≤ s.activeWords.toNat)
    (hcal : UInt256.ofNat s.executionEnv.calldata.size = len)
    (hmem : MachineState.readWord s.memory 0 = PadValues.load len 162) :
    runInstrSeq (templates 11) (state s len h4 right rho 11 q) =
      some (state s len h4 right rho 12 (StaggerModeSeven.step 11 (PadModel.message len 11) q)) := by
  have he : StaggerModeSeven.step 11 (PadModel.message len 11) q = PadCore11.eval len q := by
    unfold StaggerModeSeven.step
    rw [if_neg (by decide : ¬StaggerModeSeven.enabled 11)]
    unfold StaggerTerminal75.step
    rw [if_neg (by decide : ¬(11=75 ∨ 11=76))]
    rfl
  rw [he]
  simp only [state, pcs, shapes, templates, Nat.reduceSub]
  have hk10 : StaggerModeSeven.physicalKey 10 = StaggerAlgorithm.physicalKey 10 := by
    unfold StaggerModeSeven.physicalKey
    rw [if_neg (by decide : ¬StaggerModeSeven.enabled 10)]
  rw [hk10]
  have hk11 : StaggerModeSeven.physicalKey 11 = StaggerAlgorithm.physicalKey 11 := by
    unfold StaggerModeSeven.physicalKey
    rw [if_neg (by decide : ¬StaggerModeSeven.enabled 11)]
  rw [hk11]
  exact PadCore11.run s len h4 q right rho hstack hrun hactive hcal hmem
#print axioms boundary11
end Challenge.Ripemd160.Submission.Proofs.Bytecode.Local20261028.PadComposition
