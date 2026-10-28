import Challenge.Ripemd160.Submission.Local20261028.PadSchedule
set_option warningAsError true
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.Local20261028.PadComposition
open EvmSemantics EvmSemantics.EVM YulEvmCompiler Challenge.EvmProof
open Paired144WordRound StackRoundTrace
theorem boundary36 (s : State) (len h4 : UInt256) (q right : WordLane) (rho : List UInt256)
    (hstack : rho.length ≤ 900) (hrun : s.halt = .Running) (hactive : 34 ≤ s.activeWords.toNat)
    (hcal : UInt256.ofNat s.executionEnv.calldata.size = len)
    (hmem : MachineState.readWord s.memory 0 = PadValues.load len 162) :
    runInstrSeq (templates 36) (state s len h4 right rho 36 q) =
      some (state s len h4 right rho 37 (StaggerModeSeven.step 36 (PadModel.message len 36) q)) := by
  have he : StaggerModeSeven.step 36 (PadModel.message len 36) q = PadCore36.eval len q := by
    unfold StaggerModeSeven.step
    rw [if_neg (by decide : ¬StaggerModeSeven.enabled 36)]
    unfold StaggerTerminal75.step
    rw [if_neg (by decide : ¬(36=75 ∨ 36=76))]
    rfl
  rw [he]
  simp only [state, pcs, shapes, templates, Nat.reduceSub]
  have hk35 : StaggerModeSeven.physicalKey 35 = StaggerAlgorithm.physicalKey 35 := by
    unfold StaggerModeSeven.physicalKey
    rw [if_neg (by decide : ¬StaggerModeSeven.enabled 35)]
  rw [hk35]
  have hk36 : StaggerModeSeven.physicalKey 36 = StaggerAlgorithm.physicalKey 36 := by
    unfold StaggerModeSeven.physicalKey
    rw [if_neg (by decide : ¬StaggerModeSeven.enabled 36)]
  rw [hk36]
  exact PadCore36.run s len h4 q right rho hstack hrun hactive hcal hmem
#print axioms boundary36
end Challenge.Ripemd160.Submission.Proofs.Bytecode.Local20261028.PadComposition
