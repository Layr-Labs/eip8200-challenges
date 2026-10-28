import Challenge.Ripemd160.Submission.Local20261028.CoreLeft79
import Challenge.Ripemd160.Submission.Local20261028.CoreFunctional
import Challenge.Ripemd160.Submission.Local20261028.CandidateBytes
import Challenge.Ripemd160.Submission.Proofs.Bytecode.PcEncoding
import Challenge.Ripemd160.Submission.Proofs.Bytecode.ScheduledTailFrame
set_option warningAsError true
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.Local20261028.CoreTail
open EvmSemantics EvmSemantics.EVM Challenge.EvmProof Paired144WordRound
open CoreFunctional StackRoundTrace
abbrev template := ScheduledTailRaw.template
theorem exact_bytes :
    (Challenge.Ripemd160.Benchmark.bytecode.data.toList.drop 4523).take 55 =
      PcEncoding.assembleBytes template := by
  rw [RipemdSubmissionTables20261028.CandidateBytes.exact_list]
  change (RipemdSubmissionTables20261028.CandidateBytes.bytes.drop (4480+43)).take 55 = _
  rw [← List.drop_drop, RipemdSubmissionTables20261028.CandidateBytes.drop70]
  decide +kernel
#print axioms exact_bytes
def tailInput (memory : ByteArray) (h : Compression.HashState) (l r : WordLane)
    (off limit : UInt256) : ScheduledTailRaw.Input :=
  {ld := l.d, lb := l.b, le := l.e, la := l.a, k := UInt256.ofNat 2840853838,
   lc := l.c, re := r.e, rc := r.c, ra := r.a, rd := r.d, rb := r.b,
   factor := factorPlusWord, lower := UInt256.ofNat 4294967295,
   cache140 := fusedModulusWord 5 7, cache190 := fusedCoefficientWord 0 2,
   cache310 := fusedCoefficientWord 0 3, cache350 := fusedModulusWord 8 5,
   literal72 := CoreModel.load memory 360, literal28 := UInt256.ofNat 28,
   h4 := Word.ofUInt32 h.h4, h1 := Word.ofUInt32 h.h1, h2 := Word.ofUInt32 h.h2,
   h3 := Word.ofUInt32 h.h3, h0 := Word.ofUInt32 h.h0, off := off, limit := limit}

theorem combine_eq (memory : ByteArray) (h : Compression.HashState) (q r : WordLane)
    (off limit : UInt256) :
    ScheduledTailFrame.combine h (tailInput memory h (CoreLeft79.epilogueRaw memory q) r off limit) =
      combine h (CoreModel.epilogue memory q) r := by
  simp only [ScheduledTailFrame.combine, tailInput, combine,
    PairedCompressionBridge.combineLanes, Paired80Compression.unpackLeft,
    StaggerFinalMemory.unpackRight, ScheduledTailFrame.high,
    StaggerFinalMemory.high32, Paired80Compression.low32, Word.toUInt32,
    CoreLeft79.epilogueRaw, CoreModel.epilogue, CoreLeft79.left79Raw_a, CoreLeft79.left79Raw_b, CoreLeft79.left79Raw_c, CoreLeft79.left79Raw_e, CoreLeft79.left79Raw_d_shift]
  congr 1 <;> apply UInt32.eq_of_toBitVec_eq <;>
    simp only [UInt32.toBitVec_add] <;> ac_rfl

theorem run (s : State) (h : Compression.HashState) (q r : WordLane)
    (off limit : UInt256) (rho : List UInt256) (hs : rho.length ≤ 980) (hr : s.halt = .Running) :
    runInstrSeq template
      {s with pc := UInt256.ofNat 4523, stack := ScheduledTailRaw.stack0 (ScheduledTailFrame.bind h
        (tailInput s.memory h (CoreLeft79.epilogueRaw s.memory q) r off limit)) rho} =
      some {s with pc := UInt256.ofNat 4578, stack := Word.ofUInt32 h.h2 ::
        ScheduledTailFrame.frame (combine h (CoreModel.epilogue s.memory q) r) off limit rho} := by
  have ht := ScheduledTailFrame.run_tail s (UInt256.ofNat 4523) h
    (tailInput s.memory h (CoreLeft79.epilogueRaw s.memory q) r off limit) rho hs hr
  have hend : pcAfter (UInt256.ofNat 4523) template = UInt256.ofNat 4578 := by decide +kernel
  rw [hend, combine_eq] at ht
  exact ht
#print axioms combine_eq
#print axioms run
end Challenge.Ripemd160.Submission.Proofs.Bytecode.Local20261028.CoreTail
