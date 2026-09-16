import Challenge.Ripemd160.Submission.Proofs.Bytecode.RawExpressionAC
import Challenge.Ripemd160.Submission.Proofs.Bytecode.StackRoundTrace
import Challenge.Ripemd160.Submission.Proofs.Bytecode.Word
import Challenge.Ripemd160.Submission.Proofs.Bytecode.DenseScheduleTrace
set_option warningAsError true
set_option maxRecDepth 30000
set_option maxHeartbeats 3000000
set_option linter.unusedSimpArgs false
namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.ScheduledTailRaw
open EvmSemantics EvmSemantics.EVM YulEvmCompiler Challenge.EvmProof
open StackRoundTrace
private theorem neutral_hadd (a b : UInt256) : a + b = UInt256.add a b := rfl
structure Input where
  ld : UInt256
  lb : UInt256
  le : UInt256
  la : UInt256
  k : UInt256
  lc : UInt256
  re : UInt256
  rc : UInt256
  ra : UInt256
  rd : UInt256
  rb : UInt256
  factor : UInt256
  lower : UInt256
  cache140 : UInt256
  cache350 : UInt256
  cache310 : UInt256
  cache190 : UInt256
  literal72 : UInt256
  literal28 : UInt256
  h4 : UInt256
  h1 : UInt256
  h2 : UInt256
  h3 : UInt256
  h0 : UInt256
  off : UInt256
  limit : UInt256

def stack0 (q : Input) (rho : List UInt256) : List UInt256 := [ q.lb,
    q.le,
    q.la,
    q.ld,
    q.literal72,
    q.k,
    q.lc,
    q.re,
    q.rc,
    q.ra,
    q.rd,
    q.rb,
    q.factor,
    q.lower,
    q.cache140,
    q.cache350,
    q.cache310,
    q.cache190,
    q.h4,
    q.h3,
    q.h2,
    q.h1,
    q.h0,
    q.off,
    q.limit ] ++ rho

def chunk0 : List Instr := [ .op (.Swap ⟨7, by decide⟩),
    .push ⟨1, by decide⟩ (UInt256.ofNat 172),
    .op .SHR,
    .op (.Swap ⟨8, by decide⟩),
    .push ⟨1, by decide⟩ (UInt256.ofNat 172),
    .op .SHR,
    .op .ADD,
    .op (.Swap ⟨9, by decide⟩),
    .push ⟨1, by decide⟩ (UInt256.ofNat 172) ]

def stack1 (q : Input) (rho : List UInt256) : List UInt256 := [ (UInt256.ofNat 172),
    q.rb,
    q.la,
    q.ld,
    q.literal72,
    q.k,
    q.lc,
    q.re,
    q.lb,
    (UInt256.shiftRight q.rc (UInt256.ofNat 172)),
    q.rd,
    (UInt256.add (UInt256.shiftRight q.ra (UInt256.ofNat 172)) q.le),
    q.factor,
    q.lower,
    q.cache140,
    q.cache350,
    q.cache310,
    q.cache190,
    q.h4,
    q.h3,
    q.h2,
    q.h1,
    q.h0,
    q.off,
    q.limit ] ++ rho
theorem run_chunk0 (s : State) (pc : UInt256) (q : Input) (rho : List UInt256)
    (hstack : rho.length ≤ 980) (hrun : s.halt = .Running) :
    runInstrSeq chunk0 {s with pc := pc, stack := stack0 q rho} =
      some {s with pc := pcAfter pc chunk0, stack := stack1 q rho} := by
  have hcap (n : Nat) (hn : n ≤ 43) : rho.length + n < 1024 := by omega
  simp (discharger := omega) [chunk0, stack0, stack1, runInstrSeq,
    DataStepper.runInstr, UInt256.succ, pcAfter, Instr.size, hrun, hcap,
    Nat.add_assoc, List.getElem?_cons_zero, List.exchange,
    Word.word_toNat_ofNat, Word.literal_eq_ofNat]
  all_goals simp only [neutral_hadd, RawExpressionAC.add_comm, RawExpressionAC.add_left_comm, RawExpressionAC.add_assoc]
  all_goals repeat first | apply And.intro | exact True.intro | rfl
#print axioms run_chunk0

def chunk1 : List Instr := [ .op .SHR,
    .op .ADD,
    .op (.Swap ⟨7, by decide⟩),
    .push ⟨1, by decide⟩ (UInt256.ofNat 172),
    .op .SHR,
    .op (.Swap ⟨4, by decide⟩),
    .push ⟨1, by decide⟩ (UInt256.ofNat 172),
    .op .SHR,
    .op .ADD,
    .op (.Swap ⟨1, by decide⟩),
    .op .POP,
    .op (.Swap ⟨15, by decide⟩) ]

def stack2 (q : Input) (rho : List UInt256) : List UInt256 := [ q.h2, (UInt256.add (UInt256.shiftRight q.re (UInt256.ofNat 172)) q.ld), q.lc, (UInt256.shiftRight q.rd (UInt256.ofNat 172)), q.lb, (UInt256.shiftRight q.rc (UInt256.ofNat 172)), (UInt256.add (UInt256.shiftRight q.rb (UInt256.ofNat 172)) q.la), (UInt256.add (UInt256.shiftRight q.ra (UInt256.ofNat 172)) q.le), q.factor, q.lower, q.cache140, q.cache350, q.cache310, q.cache190, q.h4, q.h3, q.literal72, q.h1, q.h0, q.off, q.limit ] ++ rho
theorem run_chunk1 (s : State) (pc : UInt256) (q : Input) (rho : List UInt256)
    (hstack : rho.length ≤ 980) (hrun : s.halt = .Running) :
    runInstrSeq chunk1 {s with pc := pc, stack := stack1 q rho} =
      some {s with pc := pcAfter pc chunk1, stack := stack2 q rho} := by
  have hcap (n : Nat) (hn : n ≤ 43) : rho.length + n < 1024 := by omega
  simp (discharger := omega) [chunk1, stack1, stack2, runInstrSeq,
    DataStepper.runInstr, UInt256.succ, pcAfter, Instr.size, hrun, hcap,
    Nat.add_assoc, List.getElem?_cons_zero, List.exchange,
    Word.word_toNat_ofNat, Word.literal_eq_ofNat]
  all_goals simp only [neutral_hadd, RawExpressionAC.add_comm, RawExpressionAC.add_left_comm, RawExpressionAC.add_assoc]
  all_goals repeat first | apply And.intro | exact True.intro | rfl
#print axioms run_chunk1

def chunk2 : List Instr := [ .op .ADD,
    .op (.Dup ⟨8, by decide⟩),
    .op .AND,
    .op (.Swap ⟨15, by decide⟩),
    .op .ADD,
    .op .ADD,
    .op (.Dup ⟨6, by decide⟩),
    .op .AND,
    .op (.Swap ⟨14, by decide⟩),
    .op .ADD,
    .op .ADD ]

def stack3 (q : Input) (rho : List UInt256) : List UInt256 := [ (UInt256.add (UInt256.add q.h0 q.lb) (UInt256.shiftRight q.rc (UInt256.ofNat 172))), (UInt256.add (UInt256.shiftRight q.rb (UInt256.ofNat 172)) q.la), (UInt256.add (UInt256.shiftRight q.ra (UInt256.ofNat 172)) q.le), q.factor, q.lower, q.cache140, q.cache350, q.cache310, q.cache190, q.h4, q.h3, q.literal72, (UInt256.land q.lower (UInt256.add q.h2 (UInt256.add (UInt256.shiftRight q.re (UInt256.ofNat 172)) q.ld))), (UInt256.land q.lower (UInt256.add (UInt256.add q.h1 q.lc) (UInt256.shiftRight q.rd (UInt256.ofNat 172)))), q.off, q.limit ] ++ rho
theorem run_chunk2 (s : State) (pc : UInt256) (q : Input) (rho : List UInt256)
    (hstack : rho.length ≤ 980) (hrun : s.halt = .Running) :
    runInstrSeq chunk2 {s with pc := pc, stack := stack2 q rho} =
      some {s with pc := pcAfter pc chunk2, stack := stack3 q rho} := by
  have hcap (n : Nat) (hn : n ≤ 43) : rho.length + n < 1024 := by omega
  simp (discharger := omega) [chunk2, stack2, stack3, runInstrSeq,
    DataStepper.runInstr, UInt256.succ, pcAfter, Instr.size, hrun, hcap,
    Nat.add_assoc, List.getElem?_cons_zero, List.exchange,
    Word.word_toNat_ofNat, Word.literal_eq_ofNat]
  all_goals simp only [neutral_hadd, RawExpressionAC.add_comm, RawExpressionAC.add_left_comm, RawExpressionAC.add_assoc]
  all_goals repeat first | apply And.intro | exact True.intro | rfl
#print axioms run_chunk2

def chunk3 : List Instr := [ .op (.Dup ⟨4, by decide⟩),
    .op .AND,
    .op (.Swap ⟨8, by decide⟩),
    .op .ADD,
    .op (.Dup ⟨3, by decide⟩),
    .op .AND,
    .op (.Swap ⟨8, by decide⟩),
    .op .ADD,
    .op (.Dup ⟨2, by decide⟩),
    .op .AND,
    .op (.Swap ⟨8, by decide⟩),
    .op .POP ]

def stack4 (q : Input) (rho : List UInt256) : List UInt256 := [ q.factor, q.lower, q.cache140, q.cache350, q.cache310, q.cache190, (UInt256.land q.lower (UInt256.add (UInt256.add q.h0 q.lb) (UInt256.shiftRight q.rc (UInt256.ofNat 172)))), (UInt256.land q.lower (UInt256.add q.h4 (UInt256.add (UInt256.shiftRight q.rb (UInt256.ofNat 172)) q.la))), (UInt256.land q.lower (UInt256.add q.h3 (UInt256.add (UInt256.shiftRight q.ra (UInt256.ofNat 172)) q.le))), (UInt256.land q.lower (UInt256.add q.h2 (UInt256.add (UInt256.shiftRight q.re (UInt256.ofNat 172)) q.ld))), (UInt256.land q.lower (UInt256.add (UInt256.add q.h1 q.lc) (UInt256.shiftRight q.rd (UInt256.ofNat 172)))), q.off, q.limit ] ++ rho
theorem run_chunk3 (s : State) (pc : UInt256) (q : Input) (rho : List UInt256)
    (hstack : rho.length ≤ 980) (hrun : s.halt = .Running) :
    runInstrSeq chunk3 {s with pc := pc, stack := stack3 q rho} =
      some {s with pc := pcAfter pc chunk3, stack := stack4 q rho} := by
  have hcap (n : Nat) (hn : n ≤ 43) : rho.length + n < 1024 := by omega
  simp (discharger := omega) [chunk3, stack3, stack4, runInstrSeq,
    DataStepper.runInstr, UInt256.succ, pcAfter, Instr.size, hrun, hcap,
    Nat.add_assoc, List.getElem?_cons_zero, List.exchange,
    Word.word_toNat_ofNat, Word.literal_eq_ofNat]
  all_goals simp only [neutral_hadd, RawExpressionAC.add_comm, RawExpressionAC.add_left_comm, RawExpressionAC.add_assoc]
  all_goals repeat first | apply And.intro | exact True.intro | rfl
#print axioms run_chunk3

def template : List Instr := chunk0 ++ chunk1 ++ chunk2 ++ chunk3
theorem run_template (s : State) (pc : UInt256) (q : Input) (rho : List UInt256)
    (hstack : rho.length ≤ 980) (hrun : s.halt = .Running) :
    runInstrSeq template {s with pc := pc, stack := stack0 q rho} =
      some {s with pc := pcAfter pc template, stack := stack4 q rho} := by
  have h0 := run_chunk0 s (pc) q rho hstack hrun
  have h1 := run_chunk1 s (pcAfter (pc) chunk0) q rho hstack hrun
  have h2 := run_chunk2 s (pcAfter (pcAfter (pc) chunk0) chunk1) q rho hstack hrun
  have h3 := run_chunk3 s (pcAfter (pcAfter (pcAfter (pc) chunk0) chunk1) chunk2) q rho hstack hrun
  have hsum1 := DenseScheduleTrace.runInstrSeq_append_running h0 (by exact hrun) h1
  have hsum2 := DenseScheduleTrace.runInstrSeq_append_running hsum1 (by exact hrun) h2
  have hsum3 := DenseScheduleTrace.runInstrSeq_append_running hsum2 (by exact hrun) h3
  simpa only [template, DenseScheduleTrace.pcAfter_append] using hsum3
#print axioms run_template
end Challenge.Ripemd160.Submission.Proofs.Bytecode.ScheduledTailRaw
