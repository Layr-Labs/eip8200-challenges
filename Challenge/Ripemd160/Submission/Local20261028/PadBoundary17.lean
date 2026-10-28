import Challenge.Ripemd160.Submission.Local20261028.PadSchedule
set_option warningAsError true
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.Local20261028.PadComposition
open EvmSemantics EvmSemantics.EVM YulEvmCompiler Challenge.EvmProof
open Paired144WordRound StackRoundTrace
theorem boundary17 (s : State) (len h4 : UInt256) (q right : WordLane) (rho : List UInt256)
    (hstack : rho.length ≤ 900) (hrun : s.halt = .Running) (hactive : 34 ≤ s.activeWords.toNat)
    (hcal : UInt256.ofNat s.executionEnv.calldata.size = len)
    (hmem : MachineState.readWord s.memory 0 = PadValues.load len 162) :
    runInstrSeq (templates 17) (state s len h4 right rho 17 q) =
      some (state s len h4 right rho 18 (StaggerModeSeven.step 17 (PadModel.message len 17) q)) := by
  have he : StaggerModeSeven.step 17 (PadModel.message len 17) q = PadCore17.eval len q := by
    unfold StaggerModeSeven.step
    rw [if_neg (by decide : ¬StaggerModeSeven.enabled 17)]
    unfold StaggerTerminal75.step
    rw [if_neg (by decide : ¬(17=75 ∨ 17=76))]
    rfl
  rw [he]
  simp only [state, pcs, shapes, templates, Nat.reduceSub]
  have hk16 : StaggerModeSeven.physicalKey 16 = StaggerAlgorithm.physicalKey 16 := by
    unfold StaggerModeSeven.physicalKey
    rw [if_neg (by decide : ¬StaggerModeSeven.enabled 16)]
  rw [hk16]
  have hk17 : StaggerModeSeven.physicalKey 17 = StaggerAlgorithm.physicalKey 17 := by
    unfold StaggerModeSeven.physicalKey
    rw [if_neg (by decide : ¬StaggerModeSeven.enabled 17)]
  rw [hk17]
  exact PadCore17.run s len h4 q right rho hstack hrun hactive hcal hmem
#print axioms boundary17
end Challenge.Ripemd160.Submission.Proofs.Bytecode.Local20261028.PadComposition
