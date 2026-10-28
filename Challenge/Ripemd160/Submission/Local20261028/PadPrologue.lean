import Challenge.Ripemd160.Submission.Local20261028.PadCoreRight0
import Challenge.Ripemd160.Submission.Local20261028.PadCoreRight1
import Challenge.Ripemd160.Submission.Local20261028.PadCorePack
import Challenge.Ripemd160.Submission.Local20261028.PadComposition
set_option warningAsError true
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.Local20261028.PadPrologue
open EvmSemantics EvmSemantics.EVM Challenge.EvmProof Paired144WordRound
open StackRoundTrace PadCommon
def template := (PadRawRight0.template ++ PadRawRight1.template) ++ PadRawPack.template
theorem run (s : State) (len : UInt256) (h : WordLane) (off limit : UInt256) (rho : List UInt256)
    (hs : rho.length ≤ 894) (hr : s.halt = .Running) (ha : 34 ≤ s.activeWords.toNat)
    (hcal : UInt256.ofNat s.executionEnv.calldata.size = len)
    (hmem : MachineState.readWord s.memory 0 = PadValues.load len 162)
    (hvalid : Decode.isValidJumpDest s.executionEnv.code 4601 = true) :
    runInstrSeq template
      {s with pc := UInt256.ofNat 89, stack := stack len h.e [.factor,.lower,.cache 140,.cache 350,.cache 310,.cache 190,.e] h h (UInt256.ofNat 1352829926) (PadCorePack.suffix h off limit rho)} =
      some (PadComposition.state s len h.e h (PadCorePack.suffix h off limit rho) 0
        (PadModel.pair h (PadModel.prologue len h))) := by
  have hlen : (PadCorePack.suffix h off limit rho).length ≤ 900 := by
    simp only [PadCorePack.suffix, List.length_append, List.length_cons, List.length_nil]
    omega
  have h0 := PadCoreRight0.run s len h.e h h (PadCorePack.suffix h off limit rho) hlen
    rfl rfl rfl rfl rfl hr ha hcal hmem
  have h1 := PadCoreRight1.run s len h.e (PadModel.right0 len h) h
    (PadCorePack.suffix h off limit rho) hlen rfl rfl hr ha hcal hmem hvalid
  have h01 := DenseScheduleTrace.runInstrSeq_append_running h0 hr h1
  have h2 := PadCorePack.run s len h (PadModel.right1 len (PadModel.right0 len h))
    off limit rho (by omega) hr ha hcal hmem
  have ht := DenseScheduleTrace.runInstrSeq_append_running h01 hr h2
  have hk : StaggerModeSeven.physicalKey 0 = StaggerAlgorithm.physicalKey 0 := by
    unfold StaggerModeSeven.physicalKey
    rw [if_neg (by decide : ¬ StaggerModeSeven.enabled 0)]
  simpa only [template, PadComposition.state, PadComposition.pcs,
    PadComposition.shapes, Nat.reduceSub, hk, PadModel.prologue] using ht
#print axioms run
end Challenge.Ripemd160.Submission.Proofs.Bytecode.Local20261028.PadPrologue
