import Challenge.Ripemd160.Submission.Local20261028.PadSchedule
set_option warningAsError true
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.Local20261028.PadComposition
open EvmSemantics EvmSemantics.EVM YulEvmCompiler Challenge.EvmProof
open Paired144WordRound StackRoundTrace
theorem boundary42 (s : State) (len h4 : UInt256) (q right : WordLane) (rho : List UInt256)
    (hstack : rho.length ≤ 900) (hrun : s.halt = .Running) (hactive : 34 ≤ s.activeWords.toNat)
    (hcal : UInt256.ofNat s.executionEnv.calldata.size = len)
    (hmem : MachineState.readWord s.memory 0 = PadValues.load len 162) :
    runInstrSeq (templates 42) (state s len h4 right rho 42 q) =
      some (state s len h4 right rho 43 (StaggerModeSeven.step 42 (PadModel.message len 42) q)) := by
  have he : StaggerModeSeven.step 42 (PadModel.message len 42) q = PadCore42.eval len q := by
    unfold StaggerModeSeven.step
    rw [if_neg (by decide : ¬StaggerModeSeven.enabled 42)]
    unfold StaggerTerminal75.step
    rw [if_neg (by decide : ¬(42=75 ∨ 42=76))]
    rfl
  rw [he]
  simp only [state, pcs, shapes, templates, Nat.reduceSub]
  have hk41 : StaggerModeSeven.physicalKey 41 = StaggerAlgorithm.physicalKey 41 := by
    unfold StaggerModeSeven.physicalKey
    rw [if_neg (by decide : ¬StaggerModeSeven.enabled 41)]
  rw [hk41]
  have hk42 : StaggerModeSeven.physicalKey 42 = StaggerAlgorithm.physicalKey 42 := by
    unfold StaggerModeSeven.physicalKey
    rw [if_neg (by decide : ¬StaggerModeSeven.enabled 42)]
  rw [hk42]
  exact PadCore42.run s len h4 q right rho hstack hrun hactive hcal hmem
#print axioms boundary42
end Challenge.Ripemd160.Submission.Proofs.Bytecode.Local20261028.PadComposition
