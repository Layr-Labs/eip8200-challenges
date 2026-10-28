import Challenge.Ripemd160.Submission.Local20261028.PadSchedule
set_option warningAsError true
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.Local20261028.PadComposition
open EvmSemantics EvmSemantics.EVM YulEvmCompiler Challenge.EvmProof
open Paired144WordRound StackRoundTrace
theorem boundary43 (s : State) (len h4 : UInt256) (q right : WordLane) (rho : List UInt256)
    (hstack : rho.length ≤ 900) (hrun : s.halt = .Running) (hactive : 34 ≤ s.activeWords.toNat)
    (hcal : UInt256.ofNat s.executionEnv.calldata.size = len)
    (hmem : MachineState.readWord s.memory 0 = PadValues.load len 162) :
    runInstrSeq (templates 43) (state s len h4 right rho 43 q) =
      some (state s len h4 right rho 44 (StaggerModeSeven.step 43 (PadModel.message len 43) q)) := by
  have he : StaggerModeSeven.step 43 (PadModel.message len 43) q = PadCore43.eval len q := by
    unfold StaggerModeSeven.step
    rw [if_neg (by decide : ¬StaggerModeSeven.enabled 43)]
    unfold StaggerTerminal75.step
    rw [if_neg (by decide : ¬(43=75 ∨ 43=76))]
    rfl
  rw [he]
  simp only [state, pcs, shapes, templates, Nat.reduceSub]
  have hk42 : StaggerModeSeven.physicalKey 42 = StaggerAlgorithm.physicalKey 42 := by
    unfold StaggerModeSeven.physicalKey
    rw [if_neg (by decide : ¬StaggerModeSeven.enabled 42)]
  rw [hk42]
  have hk43 : StaggerModeSeven.physicalKey 43 = StaggerAlgorithm.physicalKey 43 := by
    unfold StaggerModeSeven.physicalKey
    rw [if_neg (by decide : ¬StaggerModeSeven.enabled 43)]
  rw [hk43]
  exact PadCore43.run s len h4 q right rho hstack hrun hactive hcal hmem
#print axioms boundary43
end Challenge.Ripemd160.Submission.Proofs.Bytecode.Local20261028.PadComposition
