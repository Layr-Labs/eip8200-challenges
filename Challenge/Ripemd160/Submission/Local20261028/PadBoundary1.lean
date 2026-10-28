import Challenge.Ripemd160.Submission.Local20261028.PadSchedule
set_option warningAsError true
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.Local20261028.PadComposition
open EvmSemantics EvmSemantics.EVM YulEvmCompiler Challenge.EvmProof
open Paired144WordRound StackRoundTrace
theorem boundary1 (s : State) (len h4 : UInt256) (q right : WordLane) (rho : List UInt256)
    (hstack : rho.length ≤ 900) (hrun : s.halt = .Running) (hactive : 34 ≤ s.activeWords.toNat)
    (hcal : UInt256.ofNat s.executionEnv.calldata.size = len)
    (hmem : MachineState.readWord s.memory 0 = PadValues.load len 162) :
    runInstrSeq (templates 1) (state s len h4 right rho 1 q) =
      some (state s len h4 right rho 2 (StaggerModeSeven.step 1 (PadModel.message len 1) q)) := by
  have he : StaggerModeSeven.step 1 (PadModel.message len 1) q = PadCore1.eval len q := by
    unfold StaggerModeSeven.step
    rw [if_neg (by decide : ¬StaggerModeSeven.enabled 1)]
    unfold StaggerTerminal75.step
    rw [if_neg (by decide : ¬(1=75 ∨ 1=76))]
    rfl
  rw [he]
  simp only [state, pcs, shapes, templates, Nat.reduceSub]
  have hk0 : StaggerModeSeven.physicalKey 0 = StaggerAlgorithm.physicalKey 0 := by
    unfold StaggerModeSeven.physicalKey
    rw [if_neg (by decide : ¬StaggerModeSeven.enabled 0)]
  rw [hk0]
  have hk1 : StaggerModeSeven.physicalKey 1 = StaggerAlgorithm.physicalKey 1 := by
    unfold StaggerModeSeven.physicalKey
    rw [if_neg (by decide : ¬StaggerModeSeven.enabled 1)]
  rw [hk1]
  exact PadCore1.run s len h4 q right rho hstack hrun hactive hcal hmem
#print axioms boundary1
end Challenge.Ripemd160.Submission.Proofs.Bytecode.Local20261028.PadComposition
