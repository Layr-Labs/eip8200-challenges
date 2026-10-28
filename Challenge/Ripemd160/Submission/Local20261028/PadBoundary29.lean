import Challenge.Ripemd160.Submission.Local20261028.PadSchedule
set_option warningAsError true
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.Local20261028.PadComposition
open EvmSemantics EvmSemantics.EVM YulEvmCompiler Challenge.EvmProof
open Paired144WordRound StackRoundTrace
theorem boundary29 (s : State) (len h4 : UInt256) (q right : WordLane) (rho : List UInt256)
    (hstack : rho.length ≤ 900) (hrun : s.halt = .Running) (hactive : 34 ≤ s.activeWords.toNat)
    (hcal : UInt256.ofNat s.executionEnv.calldata.size = len)
    (hmem : MachineState.readWord s.memory 0 = PadValues.load len 162) :
    runInstrSeq (templates 29) (state s len h4 right rho 29 q) =
      some (state s len h4 right rho 30 (StaggerModeSeven.step 29 (PadModel.message len 29) q)) := by
  have he : StaggerModeSeven.step 29 (PadModel.message len 29) q = PadCore29.eval len q := by
    unfold StaggerModeSeven.step
    rw [if_neg (by decide : ¬StaggerModeSeven.enabled 29)]
    unfold StaggerTerminal75.step
    rw [if_neg (by decide : ¬(29=75 ∨ 29=76))]
    rfl
  rw [he]
  simp only [state, pcs, shapes, templates, Nat.reduceSub]
  have hk28 : StaggerModeSeven.physicalKey 28 = StaggerAlgorithm.physicalKey 28 := by
    unfold StaggerModeSeven.physicalKey
    rw [if_neg (by decide : ¬StaggerModeSeven.enabled 28)]
  rw [hk28]
  have hk29 : StaggerModeSeven.physicalKey 29 = StaggerAlgorithm.physicalKey 29 := by
    unfold StaggerModeSeven.physicalKey
    rw [if_neg (by decide : ¬StaggerModeSeven.enabled 29)]
  rw [hk29]
  exact PadCore29.run s len h4 q right rho hstack hrun hactive hcal hmem
#print axioms boundary29
end Challenge.Ripemd160.Submission.Proofs.Bytecode.Local20261028.PadComposition
