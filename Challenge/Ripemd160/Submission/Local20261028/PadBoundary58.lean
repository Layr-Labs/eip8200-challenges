import Challenge.Ripemd160.Submission.Local20261028.PadSchedule
set_option warningAsError true
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.Local20261028.PadComposition
open EvmSemantics EvmSemantics.EVM YulEvmCompiler Challenge.EvmProof
open Paired144WordRound StackRoundTrace
theorem boundary58 (s : State) (len h4 : UInt256) (q right : WordLane) (rho : List UInt256)
    (hstack : rho.length ≤ 900) (hrun : s.halt = .Running) (hactive : 34 ≤ s.activeWords.toNat)
    (hcal : UInt256.ofNat s.executionEnv.calldata.size = len)
    (hmem : MachineState.readWord s.memory 0 = PadValues.load len 162) :
    runInstrSeq (templates 58) (state s len h4 right rho 58 q) =
      some (state s len h4 right rho 59 (StaggerModeSeven.step 58 (PadModel.message len 58) q)) := by
  have he : StaggerModeSeven.step 58 (PadModel.message len 58) q = PadCore58.eval len q := by
    unfold StaggerModeSeven.step
    rw [if_neg (by decide : ¬StaggerModeSeven.enabled 58)]
    unfold StaggerTerminal75.step
    rw [if_neg (by decide : ¬(58=75 ∨ 58=76))]
    rfl
  rw [he]
  simp only [state, pcs, shapes, templates, Nat.reduceSub]
  have hk57 : StaggerModeSeven.physicalKey 57 = StaggerAlgorithm.physicalKey 57 := by
    unfold StaggerModeSeven.physicalKey
    rw [if_neg (by decide : ¬StaggerModeSeven.enabled 57)]
  rw [hk57]
  have hk58 : StaggerModeSeven.physicalKey 58 = StaggerAlgorithm.physicalKey 58 := by
    unfold StaggerModeSeven.physicalKey
    rw [if_neg (by decide : ¬StaggerModeSeven.enabled 58)]
  rw [hk58]
  exact PadCore58.run s len h4 q right rho hstack hrun hactive hcal hmem
#print axioms boundary58
end Challenge.Ripemd160.Submission.Proofs.Bytecode.Local20261028.PadComposition
