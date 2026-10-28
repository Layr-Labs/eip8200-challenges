import Challenge.Ripemd160.Submission.Local20261028.PadSchedule
set_option warningAsError true
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.Local20261028.PadComposition
open EvmSemantics EvmSemantics.EVM YulEvmCompiler Challenge.EvmProof
open Paired144WordRound StackRoundTrace
theorem boundary51 (s : State) (len h4 : UInt256) (q right : WordLane) (rho : List UInt256)
    (hstack : rho.length ≤ 900) (hrun : s.halt = .Running) (hactive : 34 ≤ s.activeWords.toNat)
    (hcal : UInt256.ofNat s.executionEnv.calldata.size = len)
    (hmem : MachineState.readWord s.memory 0 = PadValues.load len 162) :
    runInstrSeq (templates 51) (state s len h4 right rho 51 q) =
      some (state s len h4 right rho 52 (StaggerModeSeven.step 51 (PadModel.message len 51) q)) := by
  have he : StaggerModeSeven.step 51 (PadModel.message len 51) q = PadCore51.eval len q := by
    unfold StaggerModeSeven.step
    rw [if_neg (by decide : ¬StaggerModeSeven.enabled 51)]
    unfold StaggerTerminal75.step
    rw [if_neg (by decide : ¬(51=75 ∨ 51=76))]
    rfl
  rw [he]
  simp only [state, pcs, shapes, templates, Nat.reduceSub]
  have hk50 : StaggerModeSeven.physicalKey 50 = StaggerAlgorithm.physicalKey 50 := by
    unfold StaggerModeSeven.physicalKey
    rw [if_neg (by decide : ¬StaggerModeSeven.enabled 50)]
  rw [hk50]
  have hk51 : StaggerModeSeven.physicalKey 51 = StaggerAlgorithm.physicalKey 51 := by
    unfold StaggerModeSeven.physicalKey
    rw [if_neg (by decide : ¬StaggerModeSeven.enabled 51)]
  rw [hk51]
  exact PadCore51.run s len h4 q right rho hstack hrun hactive hcal hmem
#print axioms boundary51
end Challenge.Ripemd160.Submission.Proofs.Bytecode.Local20261028.PadComposition
