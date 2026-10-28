import Challenge.Ripemd160.Submission.Local20261028.PadSchedule
set_option warningAsError true
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.Local20261028.PadComposition
open EvmSemantics EvmSemantics.EVM YulEvmCompiler Challenge.EvmProof
open Paired144WordRound StackRoundTrace
theorem boundary16 (s : State) (len h4 : UInt256) (q right : WordLane) (rho : List UInt256)
    (hstack : rho.length ≤ 900) (hrun : s.halt = .Running) (hactive : 34 ≤ s.activeWords.toNat)
    (hcal : UInt256.ofNat s.executionEnv.calldata.size = len)
    (hmem : MachineState.readWord s.memory 0 = PadValues.load len 162) :
    runInstrSeq (templates 16) (state s len h4 right rho 16 q) =
      some (state s len h4 right rho 17 (StaggerModeSeven.step 16 (PadModel.message len 16) q)) := by
  have he : StaggerModeSeven.step 16 (PadModel.message len 16) q = PadCore16.eval len q := by
    unfold StaggerModeSeven.step
    rw [if_neg (by decide : ¬StaggerModeSeven.enabled 16)]
    unfold StaggerTerminal75.step
    rw [if_neg (by decide : ¬(16=75 ∨ 16=76))]
    rfl
  rw [he]
  simp only [state, pcs, shapes, templates, Nat.reduceSub]
  have hk15 : StaggerModeSeven.physicalKey 15 = StaggerAlgorithm.physicalKey 15 := by
    unfold StaggerModeSeven.physicalKey
    rw [if_neg (by decide : ¬StaggerModeSeven.enabled 15)]
  rw [hk15]
  have hk16 : StaggerModeSeven.physicalKey 16 = StaggerAlgorithm.physicalKey 16 := by
    unfold StaggerModeSeven.physicalKey
    rw [if_neg (by decide : ¬StaggerModeSeven.enabled 16)]
  rw [hk16]
  exact PadCore16.run s len h4 q right rho hstack hrun hactive hcal hmem
#print axioms boundary16
end Challenge.Ripemd160.Submission.Proofs.Bytecode.Local20261028.PadComposition
