import Challenge.Ripemd160.Submission.Local20261028.PadSchedule
set_option warningAsError true
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.Local20261028.PadComposition
open EvmSemantics EvmSemantics.EVM YulEvmCompiler Challenge.EvmProof
open Paired144WordRound StackRoundTrace
theorem boundary30 (s : State) (len h4 : UInt256) (q right : WordLane) (rho : List UInt256)
    (hstack : rho.length ≤ 900) (hrun : s.halt = .Running) (hactive : 34 ≤ s.activeWords.toNat)
    (hcal : UInt256.ofNat s.executionEnv.calldata.size = len)
    (hmem : MachineState.readWord s.memory 0 = PadValues.load len 162) :
    runInstrSeq (templates 30) (state s len h4 right rho 30 q) =
      some (state s len h4 right rho 31 (StaggerModeSeven.step 30 (PadModel.message len 30) q)) := by
  have he : StaggerModeSeven.step 30 (PadModel.message len 30) q = PadCore30.eval len q := by
    unfold StaggerModeSeven.step
    rw [if_neg (by decide : ¬StaggerModeSeven.enabled 30)]
    unfold StaggerTerminal75.step
    rw [if_neg (by decide : ¬(30=75 ∨ 30=76))]
    rfl
  rw [he]
  simp only [state, pcs, shapes, templates, Nat.reduceSub]
  have hk29 : StaggerModeSeven.physicalKey 29 = StaggerAlgorithm.physicalKey 29 := by
    unfold StaggerModeSeven.physicalKey
    rw [if_neg (by decide : ¬StaggerModeSeven.enabled 29)]
  rw [hk29]
  have hk30 : StaggerModeSeven.physicalKey 30 = StaggerAlgorithm.physicalKey 30 := by
    unfold StaggerModeSeven.physicalKey
    rw [if_neg (by decide : ¬StaggerModeSeven.enabled 30)]
  rw [hk30]
  exact PadCore30.run s len h4 q right rho hstack hrun hactive hcal hmem
#print axioms boundary30
end Challenge.Ripemd160.Submission.Proofs.Bytecode.Local20261028.PadComposition
