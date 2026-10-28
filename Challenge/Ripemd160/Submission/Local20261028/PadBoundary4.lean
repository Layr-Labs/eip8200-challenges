import Challenge.Ripemd160.Submission.Local20261028.PadSchedule
set_option warningAsError true
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.Local20261028.PadComposition
open EvmSemantics EvmSemantics.EVM YulEvmCompiler Challenge.EvmProof
open Paired144WordRound StackRoundTrace
theorem boundary4 (s : State) (len h4 : UInt256) (q right : WordLane) (rho : List UInt256)
    (hstack : rho.length ≤ 900) (hrun : s.halt = .Running) (hactive : 34 ≤ s.activeWords.toNat)
    (hcal : UInt256.ofNat s.executionEnv.calldata.size = len)
    (hmem : MachineState.readWord s.memory 0 = PadValues.load len 162) :
    runInstrSeq (templates 4) (state s len h4 right rho 4 q) =
      some (state s len h4 right rho 5 (StaggerModeSeven.step 4 (PadModel.message len 4) q)) := by
  have he : StaggerModeSeven.step 4 (PadModel.message len 4) q = PadCore4.eval len q := by
    unfold StaggerModeSeven.step
    rw [if_neg (by decide : ¬StaggerModeSeven.enabled 4)]
    unfold StaggerTerminal75.step
    rw [if_neg (by decide : ¬(4=75 ∨ 4=76))]
    rfl
  rw [he]
  simp only [state, pcs, shapes, templates, Nat.reduceSub]
  have hk3 : StaggerModeSeven.physicalKey 3 = StaggerAlgorithm.physicalKey 3 := by
    unfold StaggerModeSeven.physicalKey
    rw [if_neg (by decide : ¬StaggerModeSeven.enabled 3)]
  rw [hk3]
  have hk4 : StaggerModeSeven.physicalKey 4 = StaggerAlgorithm.physicalKey 4 := by
    unfold StaggerModeSeven.physicalKey
    rw [if_neg (by decide : ¬StaggerModeSeven.enabled 4)]
  rw [hk4]
  exact PadCore4.run s len h4 q right rho hstack hrun hactive hcal hmem
#print axioms boundary4
end Challenge.Ripemd160.Submission.Proofs.Bytecode.Local20261028.PadComposition
