import Challenge.Ripemd160.Submission.Local20261028.PadSchedule
set_option warningAsError true
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.Local20261028.PadComposition
open EvmSemantics EvmSemantics.EVM YulEvmCompiler Challenge.EvmProof
open Paired144WordRound StackRoundTrace
theorem boundary8 (s : State) (len h4 : UInt256) (q right : WordLane) (rho : List UInt256)
    (hstack : rho.length ≤ 900) (hrun : s.halt = .Running) (hactive : 34 ≤ s.activeWords.toNat)
    (hcal : UInt256.ofNat s.executionEnv.calldata.size = len)
    (hmem : MachineState.readWord s.memory 0 = PadValues.load len 162) :
    runInstrSeq (templates 8) (state s len h4 right rho 8 q) =
      some (state s len h4 right rho 9 (StaggerModeSeven.step 8 (PadModel.message len 8) q)) := by
  have he : StaggerModeSeven.step 8 (PadModel.message len 8) q = PadCore8.eval len q := by
    unfold StaggerModeSeven.step
    rw [if_neg (by decide : ¬StaggerModeSeven.enabled 8)]
    unfold StaggerTerminal75.step
    rw [if_neg (by decide : ¬(8=75 ∨ 8=76))]
    rfl
  rw [he]
  simp only [state, pcs, shapes, templates, Nat.reduceSub]
  have hk7 : StaggerModeSeven.physicalKey 7 = StaggerAlgorithm.physicalKey 7 := by
    unfold StaggerModeSeven.physicalKey
    rw [if_neg (by decide : ¬StaggerModeSeven.enabled 7)]
  rw [hk7]
  have hk8 : StaggerModeSeven.physicalKey 8 = StaggerAlgorithm.physicalKey 8 := by
    unfold StaggerModeSeven.physicalKey
    rw [if_neg (by decide : ¬StaggerModeSeven.enabled 8)]
  rw [hk8]
  exact PadCore8.run s len h4 q right rho hstack hrun hactive hcal hmem
#print axioms boundary8
end Challenge.Ripemd160.Submission.Proofs.Bytecode.Local20261028.PadComposition
