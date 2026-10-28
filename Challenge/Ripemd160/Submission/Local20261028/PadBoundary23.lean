import Challenge.Ripemd160.Submission.Local20261028.PadSchedule
set_option warningAsError true
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.Local20261028.PadComposition
open EvmSemantics EvmSemantics.EVM YulEvmCompiler Challenge.EvmProof
open Paired144WordRound StackRoundTrace
theorem boundary23 (s : State) (len h4 : UInt256) (q right : WordLane) (rho : List UInt256)
    (hstack : rho.length ≤ 900) (hrun : s.halt = .Running) (hactive : 34 ≤ s.activeWords.toNat)
    (hcal : UInt256.ofNat s.executionEnv.calldata.size = len)
    (hmem : MachineState.readWord s.memory 0 = PadValues.load len 162) :
    runInstrSeq (templates 23) (state s len h4 right rho 23 q) =
      some (state s len h4 right rho 24 (StaggerModeSeven.step 23 (PadModel.message len 23) q)) := by
  have he : StaggerModeSeven.step 23 (PadModel.message len 23) q = PadCore23.eval len q := by
    unfold StaggerModeSeven.step
    rw [if_neg (by decide : ¬StaggerModeSeven.enabled 23)]
    unfold StaggerTerminal75.step
    rw [if_neg (by decide : ¬(23=75 ∨ 23=76))]
    rfl
  rw [he]
  simp only [state, pcs, shapes, templates, Nat.reduceSub]
  have hk22 : StaggerModeSeven.physicalKey 22 = StaggerAlgorithm.physicalKey 22 := by
    unfold StaggerModeSeven.physicalKey
    rw [if_neg (by decide : ¬StaggerModeSeven.enabled 22)]
  rw [hk22]
  have hk23 : StaggerModeSeven.physicalKey 23 = StaggerAlgorithm.physicalKey 23 := by
    unfold StaggerModeSeven.physicalKey
    rw [if_neg (by decide : ¬StaggerModeSeven.enabled 23)]
  rw [hk23]
  exact PadCore23.run s len h4 q right rho hstack hrun hactive hcal hmem
#print axioms boundary23
end Challenge.Ripemd160.Submission.Proofs.Bytecode.Local20261028.PadComposition
