import Challenge.Ripemd160.Submission.Local20261028.PadCoreLeft79
import Challenge.Ripemd160.Submission.Local20261028.PadFunctional
import Challenge.Ripemd160.Submission.Local20261028.PadOutput
set_option warningAsError true
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.Local20261028.PadTail
open EvmSemantics EvmSemantics.EVM Challenge.EvmProof Paired144WordRound
open PadFunctional StackRoundTrace
def tailInput (len : UInt256) (h : Compression.HashState) (l r : WordLane)
    (off limit : UInt256) : ScheduledTailRaw.Input :=
  {ld := l.d, lb := l.b, le := l.e, la := l.a, k := UInt256.ofNat 2840853838,
   lc := l.c, re := r.e, rc := r.c, ra := r.a, rd := r.d, rb := r.b,
   factor := factorPlusWord, lower := UInt256.ofNat 4294967295,
   cache140 := fusedModulusWord 5 7, cache190 := fusedCoefficientWord 0 2,
   cache310 := fusedCoefficientWord 0 3, cache350 := fusedModulusWord 8 5,
   literal72 := PadValues.load len 360, literal28 := UInt256.ofNat 28,
   h4 := Word.ofUInt32 h.h4, h1 := Word.ofUInt32 h.h1, h2 := Word.ofUInt32 h.h2,
   h3 := Word.ofUInt32 h.h3, h0 := Word.ofUInt32 h.h0, off := off, limit := limit}

theorem combine_eq (len : UInt256) (h : Compression.HashState) (q r : WordLane)
    (off limit : UInt256) :
    ScheduledTailFrame.combine h (tailInput len h (PadCoreLeft79.epilogueRaw len q) r off limit) =
      combine h (PadModel.epilogue len q) r := by
  simp only [ScheduledTailFrame.combine, tailInput, combine, PersistentStaggerFunctional.combine,
    PairedCompressionBridge.combineLanes, Paired80Compression.unpackLeft,
    StaggerFinalMemory.unpackRight, ScheduledTailFrame.high,
    StaggerFinalMemory.high32, Paired80Compression.low32, Word.toUInt32,
    PadCoreLeft79.epilogueRaw, PadModel.epilogue, PadCoreLeft79.left79Raw_a, PadCoreLeft79.left79Raw_b, PadCoreLeft79.left79Raw_c, PadCoreLeft79.left79Raw_e, PadCoreLeft79.left79Raw_d_shift]
  congr 1 <;> apply UInt32.eq_of_toBitVec_eq <;>
    simp only [UInt32.toBitVec_add] <;> ac_rfl

#print axioms combine_eq
end Challenge.Ripemd160.Submission.Proofs.Bytecode.Local20261028.PadTail
