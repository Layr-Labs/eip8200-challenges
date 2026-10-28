import Challenge.Ripemd160.Submission.Local20261028.PadSchedule
set_option warningAsError true
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.Local20261028.PadComposition
open EvmSemantics EvmSemantics.EVM YulEvmCompiler Challenge.EvmProof
open Paired144WordRound StackRoundTrace
theorem boundary28 (s : State) (len h4 : UInt256) (q right : WordLane) (rho : List UInt256)
    (hstack : rho.length ≤ 900) (hrun : s.halt = .Running) (hactive : 34 ≤ s.activeWords.toNat)
    (hcal : UInt256.ofNat s.executionEnv.calldata.size = len)
    (hmem : MachineState.readWord s.memory 0 = PadValues.load len 162) :
    runInstrSeq (templates 28) (state s len h4 right rho 28 q) =
      some (state s len h4 right rho 29 (StaggerModeSeven.step 28 (PadModel.message len 28) q)) := by
  have he : StaggerModeSeven.step 28 (PadModel.message len 28) q = PadCore28.eval len q := by
    unfold StaggerModeSeven.step
    rw [if_neg (by decide : ¬StaggerModeSeven.enabled 28)]
    unfold StaggerTerminal75.step
    rw [if_neg (by decide : ¬(28=75 ∨ 28=76))]
    rfl
  rw [he]
  simp only [state, pcs, shapes, templates, Nat.reduceSub]
  have hk27 : StaggerModeSeven.physicalKey 27 = StaggerAlgorithm.physicalKey 27 := by
    unfold StaggerModeSeven.physicalKey
    rw [if_neg (by decide : ¬StaggerModeSeven.enabled 27)]
  rw [hk27]
  have hk28 : StaggerModeSeven.physicalKey 28 = StaggerAlgorithm.physicalKey 28 := by
    unfold StaggerModeSeven.physicalKey
    rw [if_neg (by decide : ¬StaggerModeSeven.enabled 28)]
  rw [hk28]
  exact PadCore28.run s len h4 q right rho hstack hrun hactive hcal hmem
#print axioms boundary28
end Challenge.Ripemd160.Submission.Proofs.Bytecode.Local20261028.PadComposition
