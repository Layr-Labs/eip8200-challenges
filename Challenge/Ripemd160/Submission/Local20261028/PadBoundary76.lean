import Challenge.Ripemd160.Submission.Local20261028.PadSchedule
set_option warningAsError true
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.Local20261028.PadComposition
open EvmSemantics EvmSemantics.EVM YulEvmCompiler Challenge.EvmProof
open Paired144WordRound StackRoundTrace
theorem boundary76 (s : State) (len h4 : UInt256) (q right : WordLane) (rho : List UInt256)
    (hstack : rho.length ≤ 900) (hrun : s.halt = .Running) (hactive : 34 ≤ s.activeWords.toNat)
    (hcal : UInt256.ofNat s.executionEnv.calldata.size = len)
    (hmem : MachineState.readWord s.memory 0 = PadValues.load len 162) :
    runInstrSeq (templates 76) (state s len h4 right rho 76 q) =
      some (state s len h4 right rho 77 (StaggerModeSeven.step 76 (PadModel.message len 76) q)) := by
  have he : StaggerModeSeven.step 76 (PadModel.message len 76) q = PadCore76.eval len q := by
    unfold StaggerModeSeven.step
    rw [if_neg (by decide : ¬StaggerModeSeven.enabled 76)]
    rfl
  rw [he]
  simp only [state, pcs, shapes, templates, Nat.reduceSub]
  have hk75 : StaggerModeSeven.physicalKey 75 = StaggerAlgorithm.physicalKey 75 := by
    unfold StaggerModeSeven.physicalKey
    rw [if_neg (by decide : ¬StaggerModeSeven.enabled 75)]
  rw [hk75]
  have hk76 : StaggerModeSeven.physicalKey 76 = StaggerAlgorithm.physicalKey 76 := by
    unfold StaggerModeSeven.physicalKey
    rw [if_neg (by decide : ¬StaggerModeSeven.enabled 76)]
  rw [hk76]
  exact PadCore76.run s len h4 q right rho hstack hrun hactive hcal hmem
#print axioms boundary76
end Challenge.Ripemd160.Submission.Proofs.Bytecode.Local20261028.PadComposition
