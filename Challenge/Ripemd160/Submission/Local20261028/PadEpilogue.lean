import Challenge.Ripemd160.Submission.Local20261028.PadCoreUnpack
import Challenge.Ripemd160.Submission.Local20261028.PadCoreLeft77
import Challenge.Ripemd160.Submission.Local20261028.PadCoreLeft78
import Challenge.Ripemd160.Submission.Local20261028.PadCoreLeft79
import Challenge.Ripemd160.Submission.Local20261028.PadComposition
set_option warningAsError true
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.Local20261028.PadEpilogue
open EvmSemantics EvmSemantics.EVM Challenge.EvmProof Paired144WordRound
open StackRoundTrace PadCommon
def template := ((PadRawUnpack.template ++ PadRawLeft77.template) ++ PadRawLeft78.template) ++ PadRawLeft79.template
def result (s : State) (len h4 : UInt256) (q : WordLane) (rho : List UInt256) : State :=
  {s with pc := UInt256.ofNat 8033, stack := stack len h4 [.b,.c,.d,.a,.dr,.ar,.cachedMessage 360,.pair,.upper,.er,.cr,.literal 23,.e,.br,.factor,.lower,.cache 140,.cache 350,.cache 310,.cache 190,.cache 500] (PadCoreLeft79.epilogueRaw len q) q (UInt256.ofNat 2840853838) rho}
theorem run (s : State) (len h4 : UInt256) (q right : WordLane) (rho : List UInt256)
    (hs : rho.length ≤ 900) (hr : s.halt = .Running) (ha : 34 ≤ s.activeWords.toNat) :
    runInstrSeq template (PadComposition.state s len h4 right rho 77 q) =
      some (result s len h4 q rho) := by
  have h0 := PadCoreUnpack.run s len h4 q right rho hs hr ha
  have h1 := PadCoreLeft77.run s len h4 (PadModel.left q) q rho rfl hs hr ha
  have h01 := DenseScheduleTrace.runInstrSeq_append_running h0 hr h1
  have h2 := PadCoreLeft78.run s len h4 (PadModel.left77 len (PadModel.left q)) q rho
    rfl rfl rfl hs hr ha
  have h012 := DenseScheduleTrace.runInstrSeq_append_running h01 hr h2
  have h3 := PadCoreLeft79.run s len h4 (PadModel.left78 len (PadModel.left77 len (PadModel.left q)))
    q rho rfl hs hr ha
  have ht := DenseScheduleTrace.runInstrSeq_append_running h012 hr h3
  have hk : StaggerModeSeven.physicalKey 76 = StaggerAlgorithm.physicalKey 76 := by
    unfold StaggerModeSeven.physicalKey
    rw [if_neg (by decide : ¬ StaggerModeSeven.enabled 76)]
  simpa only [template, result, PadComposition.state, PadComposition.pcs,
    PadComposition.shapes, Nat.reduceSub, hk, PadCoreLeft79.epilogueRaw] using ht
#print axioms run
end Challenge.Ripemd160.Submission.Proofs.Bytecode.Local20261028.PadEpilogue
