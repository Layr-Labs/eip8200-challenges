import Challenge.Ripemd160.Submission.Local20261028.PadSchedule
set_option warningAsError true
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.Local20261028.PadComposition
open EvmSemantics EvmSemantics.EVM YulEvmCompiler Challenge.EvmProof
open Paired144WordRound StackRoundTrace
theorem boundary7 (s : State) (len h4 : UInt256) (q right : WordLane) (rho : List UInt256)
    (hstack : rho.length ≤ 900) (hrun : s.halt = .Running) (hactive : 34 ≤ s.activeWords.toNat)
    (hcal : UInt256.ofNat s.executionEnv.calldata.size = len)
    (hmem : MachineState.readWord s.memory 0 = PadValues.load len 162) :
    runInstrSeq (templates 7) (state s len h4 right rho 7 q) =
      some (state s len h4 right rho 8 (StaggerModeSeven.step 7 (PadModel.message len 7) q)) := by
  have he : StaggerModeSeven.step 7 (PadModel.message len 7) q = PadCore7.eval len q := by
    unfold StaggerModeSeven.step
    rw [if_neg (by decide : ¬StaggerModeSeven.enabled 7)]
    unfold StaggerTerminal75.step
    rw [if_neg (by decide : ¬(7=75 ∨ 7=76))]
    rfl
  rw [he]
  simp only [state, pcs, shapes, templates, Nat.reduceSub]
  have hk6 : StaggerModeSeven.physicalKey 6 = StaggerAlgorithm.physicalKey 6 := by
    unfold StaggerModeSeven.physicalKey
    rw [if_neg (by decide : ¬StaggerModeSeven.enabled 6)]
  rw [hk6]
  have hk7 : StaggerModeSeven.physicalKey 7 = StaggerAlgorithm.physicalKey 7 := by
    unfold StaggerModeSeven.physicalKey
    rw [if_neg (by decide : ¬StaggerModeSeven.enabled 7)]
  rw [hk7]
  exact PadCore7.run s len h4 q right rho hstack hrun hactive hcal hmem
#print axioms boundary7
end Challenge.Ripemd160.Submission.Proofs.Bytecode.Local20261028.PadComposition
