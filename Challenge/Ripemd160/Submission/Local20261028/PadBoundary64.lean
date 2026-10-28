import Challenge.Ripemd160.Submission.Local20261028.PadSchedule
set_option warningAsError true
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.Local20261028.PadComposition
open EvmSemantics EvmSemantics.EVM YulEvmCompiler Challenge.EvmProof
open Paired144WordRound StackRoundTrace
theorem boundary64 (s : State) (len h4 : UInt256) (q right : WordLane) (rho : List UInt256)
    (hstack : rho.length ≤ 900) (hrun : s.halt = .Running) (hactive : 34 ≤ s.activeWords.toNat)
    (hcal : UInt256.ofNat s.executionEnv.calldata.size = len)
    (hmem : MachineState.readWord s.memory 0 = PadValues.load len 162) :
    runInstrSeq (templates 64) (state s len h4 right rho 64 q) =
      some (state s len h4 right rho 65 (StaggerModeSeven.step 64 (PadModel.message len 64) q)) := by
  have he : StaggerModeSeven.step 64 (PadModel.message len 64) q = PadCore64.eval len q := by
    unfold StaggerModeSeven.step
    rw [if_neg (by decide : ¬StaggerModeSeven.enabled 64)]
    unfold StaggerTerminal75.step
    rw [if_neg (by decide : ¬(64=75 ∨ 64=76))]
    rfl
  rw [he]
  simp only [state, pcs, shapes, templates, Nat.reduceSub]
  have hk63 : StaggerModeSeven.physicalKey 63 = StaggerAlgorithm.physicalKey 63 := by
    unfold StaggerModeSeven.physicalKey
    rw [if_neg (by decide : ¬StaggerModeSeven.enabled 63)]
  rw [hk63]
  have hk64 : StaggerModeSeven.physicalKey 64 = StaggerAlgorithm.physicalKey 64 := by
    unfold StaggerModeSeven.physicalKey
    rw [if_neg (by decide : ¬StaggerModeSeven.enabled 64)]
  rw [hk64]
  exact PadCore64.run s len h4 q right rho hstack hrun hactive hcal hmem
#print axioms boundary64
end Challenge.Ripemd160.Submission.Proofs.Bytecode.Local20261028.PadComposition
