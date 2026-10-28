import Challenge.Ripemd160.Submission.Local20261028.PadSchedule
set_option warningAsError true
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.Local20261028.PadComposition
open EvmSemantics EvmSemantics.EVM YulEvmCompiler Challenge.EvmProof
open Paired144WordRound StackRoundTrace
theorem boundary31 (s : State) (len h4 : UInt256) (q right : WordLane) (rho : List UInt256)
    (hstack : rho.length ≤ 900) (hrun : s.halt = .Running) (hactive : 34 ≤ s.activeWords.toNat)
    (hcal : UInt256.ofNat s.executionEnv.calldata.size = len)
    (hmem : MachineState.readWord s.memory 0 = PadValues.load len 162) :
    runInstrSeq (templates 31) (state s len h4 right rho 31 q) =
      some (state s len h4 right rho 32 (StaggerModeSeven.step 31 (PadModel.message len 31) q)) := by
  have he : StaggerModeSeven.step 31 (PadModel.message len 31) q = PadCore31.eval len q := by
    unfold StaggerModeSeven.step
    rw [if_neg (by decide : ¬StaggerModeSeven.enabled 31)]
    unfold StaggerTerminal75.step
    rw [if_neg (by decide : ¬(31=75 ∨ 31=76))]
    rfl
  rw [he]
  simp only [state, pcs, shapes, templates, Nat.reduceSub]
  have hk30 : StaggerModeSeven.physicalKey 30 = StaggerAlgorithm.physicalKey 30 := by
    unfold StaggerModeSeven.physicalKey
    rw [if_neg (by decide : ¬StaggerModeSeven.enabled 30)]
  rw [hk30]
  have hk31 : StaggerModeSeven.physicalKey 31 = StaggerAlgorithm.physicalKey 31 := by
    unfold StaggerModeSeven.physicalKey
    rw [if_neg (by decide : ¬StaggerModeSeven.enabled 31)]
  rw [hk31]
  exact PadCore31.run s len h4 q right rho hstack hrun hactive hcal hmem
#print axioms boundary31
end Challenge.Ripemd160.Submission.Proofs.Bytecode.Local20261028.PadComposition
