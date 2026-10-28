import Challenge.Ripemd160.Submission.Local20261028.PadSchedule
set_option warningAsError true
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.Local20261028.PadComposition
open EvmSemantics EvmSemantics.EVM YulEvmCompiler Challenge.EvmProof
open Paired144WordRound StackRoundTrace
theorem boundary39 (s : State) (len h4 : UInt256) (q right : WordLane) (rho : List UInt256)
    (hstack : rho.length ≤ 900) (hrun : s.halt = .Running) (hactive : 34 ≤ s.activeWords.toNat)
    (hcal : UInt256.ofNat s.executionEnv.calldata.size = len)
    (hmem : MachineState.readWord s.memory 0 = PadValues.load len 162) :
    runInstrSeq (templates 39) (state s len h4 right rho 39 q) =
      some (state s len h4 right rho 40 (StaggerModeSeven.step 39 (PadModel.message len 39) q)) := by
  have he : StaggerModeSeven.step 39 (PadModel.message len 39) q = PadCore39.eval len q := by
    unfold StaggerModeSeven.step
    rw [if_neg (by decide : ¬StaggerModeSeven.enabled 39)]
    unfold StaggerTerminal75.step
    rw [if_neg (by decide : ¬(39=75 ∨ 39=76))]
    rfl
  rw [he]
  simp only [state, pcs, shapes, templates, Nat.reduceSub]
  have hk38 : StaggerModeSeven.physicalKey 38 = StaggerAlgorithm.physicalKey 38 := by
    unfold StaggerModeSeven.physicalKey
    rw [if_neg (by decide : ¬StaggerModeSeven.enabled 38)]
  rw [hk38]
  have hk39 : StaggerModeSeven.physicalKey 39 = StaggerAlgorithm.physicalKey 39 := by
    unfold StaggerModeSeven.physicalKey
    rw [if_neg (by decide : ¬StaggerModeSeven.enabled 39)]
  rw [hk39]
  exact PadCore39.run s len h4 q right rho hstack hrun hactive hcal hmem
#print axioms boundary39
end Challenge.Ripemd160.Submission.Proofs.Bytecode.Local20261028.PadComposition
