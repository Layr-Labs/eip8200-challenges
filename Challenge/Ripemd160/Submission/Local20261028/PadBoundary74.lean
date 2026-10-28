import Challenge.Ripemd160.Submission.Local20261028.PadSchedule
set_option warningAsError true
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.Local20261028.PadComposition
open EvmSemantics EvmSemantics.EVM YulEvmCompiler Challenge.EvmProof
open Paired144WordRound StackRoundTrace
theorem boundary74 (s : State) (len h4 : UInt256) (q right : WordLane) (rho : List UInt256)
    (hstack : rho.length ≤ 900) (hrun : s.halt = .Running) (hactive : 34 ≤ s.activeWords.toNat)
    (hcal : UInt256.ofNat s.executionEnv.calldata.size = len)
    (hmem : MachineState.readWord s.memory 0 = PadValues.load len 162) :
    runInstrSeq (templates 74) (state s len h4 right rho 74 q) =
      some (state s len h4 right rho 75 (StaggerModeSeven.step 74 (PadModel.message len 74) q)) := by
  have he : StaggerModeSeven.step 74 (PadModel.message len 74) q = PadCore74.eval len q := by
    unfold StaggerModeSeven.step
    rw [if_neg (by decide : ¬StaggerModeSeven.enabled 74)]
    unfold StaggerTerminal75.step
    rw [if_neg (by decide : ¬(74=75 ∨ 74=76))]
    rfl
  rw [he]
  simp only [state, pcs, shapes, templates, Nat.reduceSub]
  have hk73 : StaggerModeSeven.physicalKey 73 = StaggerAlgorithm.physicalKey 73 := by
    unfold StaggerModeSeven.physicalKey
    rw [if_neg (by decide : ¬StaggerModeSeven.enabled 73)]
  rw [hk73]
  have hk74 : StaggerModeSeven.physicalKey 74 = StaggerAlgorithm.physicalKey 74 := by
    unfold StaggerModeSeven.physicalKey
    rw [if_neg (by decide : ¬StaggerModeSeven.enabled 74)]
  rw [hk74]
  exact PadCore74.run s len h4 q right rho hstack hrun hactive hcal hmem
#print axioms boundary74
end Challenge.Ripemd160.Submission.Proofs.Bytecode.Local20261028.PadComposition
