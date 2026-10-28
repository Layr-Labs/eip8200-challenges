import Challenge.Ripemd160.Submission.Local20261028.CoreRight0
import Challenge.Ripemd160.Submission.Local20261028.CoreRight1
import Challenge.Ripemd160.Submission.Local20261028.CorePack
import Challenge.Ripemd160.Submission.Local20261028.RoundComposition
set_option warningAsError true
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.Local20261028.CorePrologue
open EvmSemantics EvmSemantics.EVM Challenge.EvmProof Paired144WordRound
open StackRoundTrace CoreCommon
def template := (RawRight0.template ++ RawRight1.template) ++ RawPack.template
theorem run (s : State) (h : WordLane) (off limit : UInt256) (rho : List UInt256)
    (hs : rho.length ≤ 894) (hr : s.halt = .Running) (ha : 34 ≤ s.activeWords.toNat) :
    runInstrSeq template
      {s with pc := UInt256.ofNat 824, stack := stack s.memory h.e [.factor,.lower,.cache 140,.cache 350,.cache 310,.cache 190,.e] h h (UInt256.ofNat 1352829926) (CorePack.suffix h off limit rho)} =
      some (RoundComposition.state s h.e h (CorePack.suffix h off limit rho) 0
        (CoreModel.pair h (CoreModel.prologue s.memory h))) := by
  have hlen : (CorePack.suffix h off limit rho).length ≤ 900 := by
    simp only [CorePack.suffix, List.length_append, List.length_cons, List.length_nil]
    omega
  have h0 := CoreRight0.run s h.e h h (CorePack.suffix h off limit rho) hlen
    rfl rfl rfl rfl rfl hr ha
  have h1 := CoreRight1.run s h.e (CoreModel.right0 s.memory h) h
    (CorePack.suffix h off limit rho) hlen rfl rfl hr ha
  have h01 := DenseScheduleTrace.runInstrSeq_append_running h0 hr h1
  have h2 := CorePack.run s h (CoreModel.right1 s.memory (CoreModel.right0 s.memory h))
    off limit rho (by omega) hr ha
  have ht := DenseScheduleTrace.runInstrSeq_append_running h01 hr h2
  have hk : StaggerModeSeven.physicalKey 0 = StaggerAlgorithm.physicalKey 0 := by
    unfold StaggerModeSeven.physicalKey
    rw [if_neg (by decide : ¬ StaggerModeSeven.enabled 0)]
  simpa only [template, RoundComposition.state, RoundComposition.pcs,
    RoundComposition.shapes, Nat.reduceSub, hk, CoreModel.prologue] using ht
#print axioms run
end Challenge.Ripemd160.Submission.Proofs.Bytecode.Local20261028.CorePrologue
