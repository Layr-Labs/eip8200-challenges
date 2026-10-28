import Challenge.Ripemd160.Submission.Local20261028.PadSchedule
set_option warningAsError true
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.Local20261028.PadComposition
open EvmSemantics EvmSemantics.EVM YulEvmCompiler Challenge.EvmProof
open Paired144WordRound StackRoundTrace
theorem boundary69 (s : State) (len h4 : UInt256) (q right : WordLane) (rho : List UInt256)
    (hstack : rho.length ≤ 900) (hrun : s.halt = .Running) (hactive : 34 ≤ s.activeWords.toNat)
    (hcal : UInt256.ofNat s.executionEnv.calldata.size = len)
    (hmem : MachineState.readWord s.memory 0 = PadValues.load len 162) :
    runInstrSeq (templates 69) (state s len h4 right rho 69 q) =
      some (state s len h4 right rho 70 (StaggerModeSeven.step 69 (PadModel.message len 69) q)) := by
  have he : StaggerModeSeven.step 69 (PadModel.message len 69) q = PadCore69.eval len q := by
    unfold StaggerModeSeven.step
    rw [if_neg (by decide : ¬StaggerModeSeven.enabled 69)]
    unfold StaggerTerminal75.step
    rw [if_neg (by decide : ¬(69=75 ∨ 69=76))]
    rfl
  rw [he]
  simp only [state, pcs, shapes, templates, Nat.reduceSub]
  have hk68 : StaggerModeSeven.physicalKey 68 = StaggerAlgorithm.physicalKey 68 := by
    unfold StaggerModeSeven.physicalKey
    rw [if_neg (by decide : ¬StaggerModeSeven.enabled 68)]
  rw [hk68]
  have hk69 : StaggerModeSeven.physicalKey 69 = StaggerAlgorithm.physicalKey 69 := by
    unfold StaggerModeSeven.physicalKey
    rw [if_neg (by decide : ¬StaggerModeSeven.enabled 69)]
  rw [hk69]
  exact PadCore69.run s len h4 q right rho hstack hrun hactive hcal hmem
#print axioms boundary69
end Challenge.Ripemd160.Submission.Proofs.Bytecode.Local20261028.PadComposition
