import Challenge.Ripemd160.Submission.Local20261028.PadSchedule
set_option warningAsError true
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.Local20261028.PadComposition
open EvmSemantics EvmSemantics.EVM YulEvmCompiler Challenge.EvmProof
open Paired144WordRound StackRoundTrace
theorem boundary33 (s : State) (len h4 : UInt256) (q right : WordLane) (rho : List UInt256)
    (hstack : rho.length ≤ 900) (hrun : s.halt = .Running) (hactive : 34 ≤ s.activeWords.toNat)
    (hcal : UInt256.ofNat s.executionEnv.calldata.size = len)
    (hmem : MachineState.readWord s.memory 0 = PadValues.load len 162) :
    runInstrSeq (templates 33) (state s len h4 right rho 33 q) =
      some (state s len h4 right rho 34 (StaggerModeSeven.step 33 (PadModel.message len 33) q)) := by
  have he : StaggerModeSeven.step 33 (PadModel.message len 33) q = PadCore33.eval len q := by
    unfold StaggerModeSeven.step
    rw [if_neg (by decide : ¬StaggerModeSeven.enabled 33)]
    unfold StaggerTerminal75.step
    rw [if_neg (by decide : ¬(33=75 ∨ 33=76))]
    rfl
  rw [he]
  simp only [state, pcs, shapes, templates, Nat.reduceSub]
  have hk32 : StaggerModeSeven.physicalKey 32 = StaggerAlgorithm.physicalKey 32 := by
    unfold StaggerModeSeven.physicalKey
    rw [if_neg (by decide : ¬StaggerModeSeven.enabled 32)]
  rw [hk32]
  have hk33 : StaggerModeSeven.physicalKey 33 = StaggerAlgorithm.physicalKey 33 := by
    unfold StaggerModeSeven.physicalKey
    rw [if_neg (by decide : ¬StaggerModeSeven.enabled 33)]
  rw [hk33]
  exact PadCore33.run s len h4 q right rho hstack hrun hactive hcal hmem
#print axioms boundary33
end Challenge.Ripemd160.Submission.Proofs.Bytecode.Local20261028.PadComposition
