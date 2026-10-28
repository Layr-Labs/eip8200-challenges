import Challenge.Ripemd160.Submission.Local20261028.PadSchedule
set_option warningAsError true
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.Local20261028.PadComposition
open EvmSemantics EvmSemantics.EVM YulEvmCompiler Challenge.EvmProof
open Paired144WordRound StackRoundTrace
theorem boundary66 (s : State) (len h4 : UInt256) (q right : WordLane) (rho : List UInt256)
    (hstack : rho.length ≤ 900) (hrun : s.halt = .Running) (hactive : 34 ≤ s.activeWords.toNat)
    (hcal : UInt256.ofNat s.executionEnv.calldata.size = len)
    (hmem : MachineState.readWord s.memory 0 = PadValues.load len 162) :
    runInstrSeq (templates 66) (state s len h4 right rho 66 q) =
      some (state s len h4 right rho 67 (StaggerModeSeven.step 66 (PadModel.message len 66) q)) := by
  have he : StaggerModeSeven.step 66 (PadModel.message len 66) q = PadCore66.eval len q := by
    unfold StaggerModeSeven.step
    rw [if_neg (by decide : ¬StaggerModeSeven.enabled 66)]
    unfold StaggerTerminal75.step
    rw [if_neg (by decide : ¬(66=75 ∨ 66=76))]
    rfl
  rw [he]
  simp only [state, pcs, shapes, templates, Nat.reduceSub]
  have hk65 : StaggerModeSeven.physicalKey 65 = StaggerAlgorithm.physicalKey 65 := by
    unfold StaggerModeSeven.physicalKey
    rw [if_neg (by decide : ¬StaggerModeSeven.enabled 65)]
  rw [hk65]
  have hk66 : StaggerModeSeven.physicalKey 66 = StaggerAlgorithm.physicalKey 66 := by
    unfold StaggerModeSeven.physicalKey
    rw [if_neg (by decide : ¬StaggerModeSeven.enabled 66)]
  rw [hk66]
  exact PadCore66.run s len h4 q right rho hstack hrun hactive hcal hmem
#print axioms boundary66
end Challenge.Ripemd160.Submission.Proofs.Bytecode.Local20261028.PadComposition
