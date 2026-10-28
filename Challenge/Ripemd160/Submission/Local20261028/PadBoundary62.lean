import Challenge.Ripemd160.Submission.Local20261028.PadSchedule
set_option warningAsError true
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.Local20261028.PadComposition
open EvmSemantics EvmSemantics.EVM YulEvmCompiler Challenge.EvmProof
open Paired144WordRound StackRoundTrace
theorem boundary62 (s : State) (len h4 : UInt256) (q right : WordLane) (rho : List UInt256)
    (hstack : rho.length ≤ 900) (hrun : s.halt = .Running) (hactive : 34 ≤ s.activeWords.toNat)
    (hcal : UInt256.ofNat s.executionEnv.calldata.size = len)
    (hmem : MachineState.readWord s.memory 0 = PadValues.load len 162) :
    runInstrSeq (templates 62) (state s len h4 right rho 62 q) =
      some (state s len h4 right rho 63 (StaggerModeSeven.step 62 (PadModel.message len 62) q)) := by
  have he : StaggerModeSeven.step 62 (PadModel.message len 62) q = PadCore62.eval len q := by
    unfold StaggerModeSeven.step
    rw [if_neg (by decide : ¬StaggerModeSeven.enabled 62)]
    unfold StaggerTerminal75.step
    rw [if_neg (by decide : ¬(62=75 ∨ 62=76))]
    rfl
  rw [he]
  simp only [state, pcs, shapes, templates, Nat.reduceSub]
  have hk61 : StaggerModeSeven.physicalKey 61 = StaggerAlgorithm.physicalKey 61 := by
    unfold StaggerModeSeven.physicalKey
    rw [if_neg (by decide : ¬StaggerModeSeven.enabled 61)]
  rw [hk61]
  have hk62 : StaggerModeSeven.physicalKey 62 = StaggerAlgorithm.physicalKey 62 := by
    unfold StaggerModeSeven.physicalKey
    rw [if_neg (by decide : ¬StaggerModeSeven.enabled 62)]
  rw [hk62]
  exact PadCore62.run s len h4 q right rho hstack hrun hactive hcal hmem
#print axioms boundary62
end Challenge.Ripemd160.Submission.Proofs.Bytecode.Local20261028.PadComposition
