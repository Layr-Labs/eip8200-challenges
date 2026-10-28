import Challenge.Ripemd160.Submission.Local20261028.PadSchedule
set_option warningAsError true
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.Local20261028.PadComposition
open EvmSemantics EvmSemantics.EVM YulEvmCompiler Challenge.EvmProof
open Paired144WordRound StackRoundTrace
theorem boundary6 (s : State) (len h4 : UInt256) (q right : WordLane) (rho : List UInt256)
    (hstack : rho.length ≤ 900) (hrun : s.halt = .Running) (hactive : 34 ≤ s.activeWords.toNat)
    (hcal : UInt256.ofNat s.executionEnv.calldata.size = len)
    (hmem : MachineState.readWord s.memory 0 = PadValues.load len 162) :
    runInstrSeq (templates 6) (state s len h4 right rho 6 q) =
      some (state s len h4 right rho 7 (StaggerModeSeven.step 6 (PadModel.message len 6) q)) := by
  have he : StaggerModeSeven.step 6 (PadModel.message len 6) q = PadCore6.eval len q := by
    unfold StaggerModeSeven.step
    rw [if_neg (by decide : ¬StaggerModeSeven.enabled 6)]
    unfold StaggerTerminal75.step
    rw [if_neg (by decide : ¬(6=75 ∨ 6=76))]
    rfl
  rw [he]
  simp only [state, pcs, shapes, templates, Nat.reduceSub]
  have hk5 : StaggerModeSeven.physicalKey 5 = StaggerAlgorithm.physicalKey 5 := by
    unfold StaggerModeSeven.physicalKey
    rw [if_neg (by decide : ¬StaggerModeSeven.enabled 5)]
  rw [hk5]
  have hk6 : StaggerModeSeven.physicalKey 6 = StaggerAlgorithm.physicalKey 6 := by
    unfold StaggerModeSeven.physicalKey
    rw [if_neg (by decide : ¬StaggerModeSeven.enabled 6)]
  rw [hk6]
  exact PadCore6.run s len h4 q right rho hstack hrun hactive hcal hmem
#print axioms boundary6
end Challenge.Ripemd160.Submission.Proofs.Bytecode.Local20261028.PadComposition
