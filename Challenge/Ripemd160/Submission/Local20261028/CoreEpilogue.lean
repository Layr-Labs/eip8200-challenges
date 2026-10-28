import Challenge.Ripemd160.Submission.Local20261028.CoreUnpack
import Challenge.Ripemd160.Submission.Local20261028.CoreLeft77
import Challenge.Ripemd160.Submission.Local20261028.CoreLeft78
import Challenge.Ripemd160.Submission.Local20261028.CoreLeft79
import Challenge.Ripemd160.Submission.Local20261028.RoundComposition
set_option warningAsError true
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.Local20261028.CoreEpilogue
open EvmSemantics EvmSemantics.EVM Challenge.EvmProof Paired144WordRound
open StackRoundTrace CoreCommon
def template := ((RawUnpack.template ++ RawLeft77.template) ++ RawLeft78.template) ++ RawLeft79.template
def result (s : State) (h4 : UInt256) (q : WordLane) (rho : List UInt256) : State :=
  {s with pc := UInt256.ofNat 4523, stack := stack s.memory h4 [.b,.c,.d,.a,.dr,.ar,.cachedMessage 360,.pair,.upper,.er,.cr,.literal 23,.e,.br,.factor,.lower,.cache 140,.cache 350,.cache 310,.cache 190,.cache 500] (CoreLeft79.epilogueRaw s.memory q) q (UInt256.ofNat 2840853838) rho}
theorem run (s : State) (h4 : UInt256) (q right : WordLane) (rho : List UInt256)
    (hs : rho.length ≤ 900) (hr : s.halt = .Running) (ha : 34 ≤ s.activeWords.toNat) :
    runInstrSeq template (RoundComposition.state s h4 right rho 77 q) =
      some (result s h4 q rho) := by
  have h0 := CoreUnpack.run s h4 q right rho hs hr ha
  have h1 := CoreLeft77.run s h4 (CoreModel.left q) q rho rfl hs hr ha
  have h01 := DenseScheduleTrace.runInstrSeq_append_running h0 hr h1
  have h2 := CoreLeft78.run s h4 (CoreModel.left77 s.memory (CoreModel.left q)) q rho
    rfl rfl rfl hs hr ha
  have h012 := DenseScheduleTrace.runInstrSeq_append_running h01 hr h2
  have h3 := CoreLeft79.run s h4 (CoreModel.left78 s.memory (CoreModel.left77 s.memory (CoreModel.left q)))
    q rho rfl hs hr ha
  have ht := DenseScheduleTrace.runInstrSeq_append_running h012 hr h3
  have hk : StaggerModeSeven.physicalKey 76 = StaggerAlgorithm.physicalKey 76 := by
    unfold StaggerModeSeven.physicalKey
    rw [if_neg (by decide : ¬ StaggerModeSeven.enabled 76)]
  simpa only [template, result, RoundComposition.state, RoundComposition.pcs,
    RoundComposition.shapes, Nat.reduceSub, hk, CoreLeft79.epilogueRaw] using ht
#print axioms run
end Challenge.Ripemd160.Submission.Proofs.Bytecode.Local20261028.CoreEpilogue
