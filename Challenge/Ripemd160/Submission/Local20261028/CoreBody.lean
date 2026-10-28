import Challenge.Ripemd160.Submission.Local20261028.CorePrologue
import Challenge.Ripemd160.Submission.Local20261028.CoreEpilogue
import Challenge.Ripemd160.Submission.Local20261028.CoreTail
import Challenge.Ripemd160.Submission.Proofs.Bytecode.StaggerPersistentFrame
set_option warningAsError true
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.Local20261028.CoreBody
open EvmSemantics EvmSemantics.EVM Challenge.EvmProof Paired144WordRound
open StackRoundTrace CoreCommon CoreFunctional
def template := ((CorePrologue.template ++ RoundComposition.block 77) ++ CoreEpilogue.template) ++ CoreTail.template
theorem initial_eq (h : Compression.HashState) :
    initial h = (⟨Word.ofUInt32 h.h0, Word.ofUInt32 h.h1, Word.ofUInt32 h.h2,
      Word.ofUInt32 h.h3, Word.ofUInt32 h.h4⟩ : WordLane) := by
  simp only [StaggerRepresentation.word_ofUInt32]
  rfl
theorem entry_eq (s : State) (h : Compression.HashState) (off limit : UInt256) (rho : List UInt256) :
    StaggerPersistentFrame.frame h off limit rho =
      stack s.memory (initial h).e [.factor,.lower,.cache 140,.cache 350,.cache 310,.cache 190,.e]
        (initial h) (initial h) (UInt256.ofNat 1352829926) (CorePack.suffix (initial h) off limit rho) := by
  rw [initial_eq]
  rfl
theorem tail_eq (s : State) (h : Compression.HashState) (q : WordLane)
    (off limit : UInt256) (rho : List UInt256) :
    CoreEpilogue.result s (initial h).e q (CorePack.suffix (initial h) off limit rho) =
      {s with pc := UInt256.ofNat 4523, stack := ScheduledTailRaw.stack0 (ScheduledTailFrame.bind h (CoreTail.tailInput s.memory h (CoreLeft79.epilogueRaw s.memory q) q off limit)) rho} := by
  rw [initial_eq]
  rfl
theorem run (s : State) (h : Compression.HashState) (off limit : UInt256) (rho : List UInt256)
    (hs : rho.length ≤ 894) (hr : s.halt = .Running) (ha : 34 ≤ s.activeWords.toNat) :
    runInstrSeq template
      {s with pc := UInt256.ofNat 824, stack := StaggerPersistentFrame.frame h off limit rho} =
      some {s with pc := UInt256.ofNat 4578, stack := Word.ofUInt32 h.h2 :: StaggerPersistentFrame.frame (result s.memory h) off limit rho} := by
  have hlen : (CorePack.suffix (initial h) off limit rho).length ≤ 900 := by
    simp only [CorePack.suffix, List.length_append, List.length_cons, List.length_nil]
    omega
  have hp := CorePrologue.run s (initial h) off limit rho hs hr ha
  rw [← entry_eq] at hp
  have hm := RoundComposition.run_block s (initial h).e
    (CoreModel.pair (initial h) (CoreModel.prologue s.memory (initial h)))
    (initial h) (CorePack.suffix (initial h) off limit rho) hlen hr ha 77 (by decide)
  have hpm := DenseScheduleTrace.runInstrSeq_append_running hp hr hm
  have he := CoreEpilogue.run s (initial h).e (CoreModel.paired s.memory (initial h))
    (initial h) (CorePack.suffix (initial h) off limit rho) hlen hr ha
  have hpme := DenseScheduleTrace.runInstrSeq_append_running hpm hr he
  rw [tail_eq] at hpme
  have ht := CoreTail.run s h (CoreModel.paired s.memory (initial h))
    (CoreModel.paired s.memory (initial h)) off limit rho (by omega) hr
  exact DenseScheduleTrace.runInstrSeq_append_running hpme hr ht

theorem exact_bytes :
    (Challenge.Ripemd160.Benchmark.bytecode.data.toList.drop 824).take (4578-824) =
      PcEncoding.assembleBytes template := by
  rw [RipemdSubmissionTables20261028.CandidateBytes.exact_list]
  change (RipemdSubmissionTables20261028.CandidateBytes.bytes.drop (768+56)).take (4578-824) = _
  rw [← List.drop_drop, RipemdSubmissionTables20261028.CandidateBytes.drop12]
  decide +kernel

theorem run_spec (s : State) (h : Compression.HashState) (off limit : UInt256) (rho : List UInt256)
    (bs : ByteArray) (blockOff : Nat)
    (hs : rho.length ≤ 894) (hr : s.halt = .Running) (ha : 34 ≤ s.activeWords.toNat)
    (hm : CoreMessage.Ready s.memory (fun i => (CompressionCorrect.schedule bs blockOff)[i]!)) :
    ∃ h' : Compression.HashState,
      runInstrSeq template
        {s with pc := UInt256.ofNat 824, stack := StaggerPersistentFrame.frame h off limit rho} =
        some {s with pc := UInt256.ofNat 4578, stack := Word.ofUInt32 h.h2 :: StaggerPersistentFrame.frame h' off limit rho} ∧
      CompressionCorrect.hashArray h' = Crypto.Ripemd160.compressBlock (CompressionCorrect.hashArray h) bs blockOff :=
  ⟨result s.memory h, run s h off limit rho hs hr ha,
    result_compressBlock s.memory bs blockOff h hm⟩
#print axioms run
#print axioms exact_bytes
#print axioms run_spec
end Challenge.Ripemd160.Submission.Proofs.Bytecode.Local20261028.CoreBody
