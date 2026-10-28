import Challenge.Ripemd160.Submission.Local20261028.PadSchedule
set_option warningAsError true
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.Local20261028.PadComposition
open EvmSemantics EvmSemantics.EVM YulEvmCompiler Challenge.EvmProof
open Paired144WordRound StackRoundTrace
theorem boundary61 (s : State) (len h4 : UInt256) (q right : WordLane) (rho : List UInt256)
    (hstack : rho.length ≤ 900) (hrun : s.halt = .Running) (hactive : 34 ≤ s.activeWords.toNat)
    (hcal : UInt256.ofNat s.executionEnv.calldata.size = len)
    (hmem : MachineState.readWord s.memory 0 = PadValues.load len 162) :
    runInstrSeq (templates 61) (state s len h4 right rho 61 q) =
      some (state s len h4 right rho 62 (StaggerModeSeven.step 61 (PadModel.message len 61) q)) := by
  have he : StaggerModeSeven.step 61 (PadModel.message len 61) q = PadCore61.eval len q := by
    unfold StaggerModeSeven.step
    rw [if_neg (by decide : ¬StaggerModeSeven.enabled 61)]
    unfold StaggerTerminal75.step
    rw [if_neg (by decide : ¬(61=75 ∨ 61=76))]
    rfl
  rw [he]
  simp only [state, pcs, shapes, templates, Nat.reduceSub]
  have hk60 : StaggerModeSeven.physicalKey 60 = StaggerAlgorithm.physicalKey 60 := by
    unfold StaggerModeSeven.physicalKey
    rw [if_neg (by decide : ¬StaggerModeSeven.enabled 60)]
  rw [hk60]
  have hk61 : StaggerModeSeven.physicalKey 61 = StaggerAlgorithm.physicalKey 61 := by
    unfold StaggerModeSeven.physicalKey
    rw [if_neg (by decide : ¬StaggerModeSeven.enabled 61)]
  rw [hk61]
  exact PadCore61.run s len h4 q right rho hstack hrun hactive hcal hmem
#print axioms boundary61
end Challenge.Ripemd160.Submission.Proofs.Bytecode.Local20261028.PadComposition
