import Challenge.Ripemd160.Submission.Local20261028.PadSchedule
set_option warningAsError true
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.Local20261028.PadComposition
open EvmSemantics EvmSemantics.EVM YulEvmCompiler Challenge.EvmProof
open Paired144WordRound StackRoundTrace
theorem boundary9 (s : State) (len h4 : UInt256) (q right : WordLane) (rho : List UInt256)
    (hstack : rho.length ≤ 900) (hrun : s.halt = .Running) (hactive : 34 ≤ s.activeWords.toNat)
    (hcal : UInt256.ofNat s.executionEnv.calldata.size = len)
    (hmem : MachineState.readWord s.memory 0 = PadValues.load len 162) :
    runInstrSeq (templates 9) (state s len h4 right rho 9 q) =
      some (state s len h4 right rho 10 (StaggerModeSeven.step 9 (PadModel.message len 9) q)) := by
  have he : StaggerModeSeven.step 9 (PadModel.message len 9) q = PadCore9.eval len q := by
    unfold StaggerModeSeven.step
    rw [if_neg (by decide : ¬StaggerModeSeven.enabled 9)]
    unfold StaggerTerminal75.step
    rw [if_neg (by decide : ¬(9=75 ∨ 9=76))]
    rfl
  rw [he]
  simp only [state, pcs, shapes, templates, Nat.reduceSub]
  have hk8 : StaggerModeSeven.physicalKey 8 = StaggerAlgorithm.physicalKey 8 := by
    unfold StaggerModeSeven.physicalKey
    rw [if_neg (by decide : ¬StaggerModeSeven.enabled 8)]
  rw [hk8]
  have hk9 : StaggerModeSeven.physicalKey 9 = StaggerAlgorithm.physicalKey 9 := by
    unfold StaggerModeSeven.physicalKey
    rw [if_neg (by decide : ¬StaggerModeSeven.enabled 9)]
  rw [hk9]
  exact PadCore9.run s len h4 q right rho hstack hrun hactive hcal hmem
#print axioms boundary9
end Challenge.Ripemd160.Submission.Proofs.Bytecode.Local20261028.PadComposition
