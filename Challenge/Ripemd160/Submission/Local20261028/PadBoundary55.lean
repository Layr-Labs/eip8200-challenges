import Challenge.Ripemd160.Submission.Local20261028.PadSchedule
set_option warningAsError true
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.Local20261028.PadComposition
open EvmSemantics EvmSemantics.EVM YulEvmCompiler Challenge.EvmProof
open Paired144WordRound StackRoundTrace
theorem boundary55 (s : State) (len h4 : UInt256) (q right : WordLane) (rho : List UInt256)
    (hstack : rho.length ≤ 900) (hrun : s.halt = .Running) (hactive : 34 ≤ s.activeWords.toNat)
    (hcal : UInt256.ofNat s.executionEnv.calldata.size = len)
    (hmem : MachineState.readWord s.memory 0 = PadValues.load len 162) :
    runInstrSeq (templates 55) (state s len h4 right rho 55 q) =
      some (state s len h4 right rho 56 (StaggerModeSeven.step 55 (PadModel.message len 55) q)) := by
  have he : StaggerModeSeven.step 55 (PadModel.message len 55) q = PadCore55.eval len q := by
    unfold StaggerModeSeven.step
    rw [if_neg (by decide : ¬StaggerModeSeven.enabled 55)]
    unfold StaggerTerminal75.step
    rw [if_neg (by decide : ¬(55=75 ∨ 55=76))]
    rfl
  rw [he]
  simp only [state, pcs, shapes, templates, Nat.reduceSub]
  have hk54 : StaggerModeSeven.physicalKey 54 = StaggerAlgorithm.physicalKey 54 := by
    unfold StaggerModeSeven.physicalKey
    rw [if_neg (by decide : ¬StaggerModeSeven.enabled 54)]
  rw [hk54]
  have hk55 : StaggerModeSeven.physicalKey 55 = StaggerAlgorithm.physicalKey 55 := by
    unfold StaggerModeSeven.physicalKey
    rw [if_neg (by decide : ¬StaggerModeSeven.enabled 55)]
  rw [hk55]
  exact PadCore55.run s len h4 q right rho hstack hrun hactive hcal hmem
#print axioms boundary55
end Challenge.Ripemd160.Submission.Proofs.Bytecode.Local20261028.PadComposition
