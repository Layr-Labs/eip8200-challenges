import Challenge.Ripemd160.Submission.Proofs.Bytecode.PersistentStaggerFunctional
import Challenge.Ripemd160.Submission.Proofs.Bytecode.ScheduledTailFrame
import Challenge.Ripemd160.Submission.Proofs.Bytecode.StaggerPersistentFrame
set_option warningAsError true
set_option maxRecDepth 30000
set_option maxHeartbeats 3000000
namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.ScheduledTailBridge
open EvmSemantics EvmSemantics.EVM Challenge.EvmProof Paired144WordRound
open PersistentStaggerFunctional

def tailInput (_memory : ByteArray) (h : Compression.HashState) (l r : WordLane)
    (off limit : UInt256) : ScheduledTailRaw.Input :=
  {ld := l.d, lb := l.b, le := l.e, la := l.a, k := UInt256.ofNat 2840853838,
   lc := l.c, re := r.e, rc := r.c, ra := r.a, rd := r.d, rb := r.b,
   factor := factorWord, lower := UInt256.ofNat 4294967295,
   cache140 := compactMaskWord, cache190 := coefficientWord 0 2,
   cache310 := coefficientWord 0 3, cache350 := coefficientWord 3 0,
   literal72 := UInt256.ofNat 72, literal28 := UInt256.ofNat 28,
   h4 := Word.ofUInt32 h.h4, h1 := Word.ofUInt32 h.h1, h2 := Word.ofUInt32 h.h2,
   h3 := Word.ofUInt32 h.h3, h0 := Word.ofUInt32 h.h0, off := off, limit := limit}

theorem combine_eq (memory : ByteArray) (h : Compression.HashState) (l r : WordLane)
    (off limit : UInt256) :
    ScheduledTailFrame.combine h (tailInput memory h l r off limit) = combine h l r := by
  simp only [ScheduledTailFrame.combine, tailInput, combine,
    PairedCompressionBridge.combineLanes, Paired80Compression.unpackLeft,
    StaggerFinalMemory.unpackRight, ScheduledTailFrame.high,
    StaggerFinalMemory.high32, Paired80Compression.low32, Word.toUInt32]
  congr 1 <;> apply UInt32.eq_of_toBitVec_eq <;>
    simp only [UInt32.toBitVec_add] <;> ac_rfl

def fromCurrent (q : StaggerPersistentTailRaw.Input) : ScheduledTailRaw.Input :=
  {ld := q.ld, lb := q.lb, le := q.le, la := q.la, k := q.k, lc := q.lc, re := q.re, rc := q.rc, ra := q.ra, rd := q.rd, rb := q.rb, factor := q.factor, lower := q.lower, cache140 := q.cache140, cache190 := q.cache190, cache310 := q.cache310, cache350 := q.cache350, literal72 := q.literal72, literal28 := q.literal28, h4 := q.h4, h1 := q.h1, h2 := q.h2, h3 := q.h3, h0 := q.h0, off := q.off, limit := q.limit}

theorem stack0_current (q : StaggerPersistentTailRaw.Input) (rho : List UInt256) :
    ScheduledTailRaw.stack0 (fromCurrent q) rho = StaggerPersistentTailRaw.stack0 q rho := rfl

theorem bind_current (h : Compression.HashState) (q : StaggerPersistentTailRaw.Input) :
    ScheduledTailFrame.bind h (fromCurrent q) = fromCurrent (StaggerPersistentFrame.bind h q) := rfl

theorem combine_current (h : Compression.HashState) (q : StaggerPersistentTailRaw.Input) :
    ScheduledTailFrame.combine h (fromCurrent q) = StaggerPersistentFrame.combine h q := rfl

theorem run_current (s : State) (pc : UInt256) (h : Compression.HashState)
    (q : StaggerPersistentTailRaw.Input) (rho : List UInt256)
    (hstack : rho.length ≤ 980) (hrun : s.halt = .Running) :
    StackRoundTrace.runInstrSeq ScheduledTailRaw.template
      {s with pc := pc, stack := StaggerPersistentTailRaw.stack0 (StaggerPersistentFrame.bind h q) rho} =
      some {s with
        pc := StackRoundTrace.pcAfter pc ScheduledTailRaw.template
        stack := StaggerPersistentFrame.frame (StaggerPersistentFrame.combine h q) q.off q.limit rho} := by
  have g := ScheduledTailFrame.run_tail s pc h (fromCurrent q) rho hstack hrun
  rw [bind_current, stack0_current, combine_current] at g
  exact g

#print axioms combine_eq
#print axioms stack0_current
#print axioms combine_current
#print axioms run_current
end Challenge.Ripemd160.Submission.Proofs.Bytecode.ScheduledTailBridge
