import Challenge.Ripemd160.Submission.Proofs.Bytecode.StackRoundTrace
import Challenge.Ripemd160.Submission.Proofs.Bytecode.Word
import Challenge.Ripemd160.Submission.Proofs.Bytecode.DenseScheduleTrace
set_option warningAsError true
set_option maxRecDepth 30000
set_option maxHeartbeats 3000000
set_option linter.unusedSimpArgs false
namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.StaggerPersistentTailRaw
open EvmSemantics EvmSemantics.EVM YulEvmCompiler Challenge.EvmProof
open StackRoundTrace
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
  cache190 : UInt256
  cache310 : UInt256
  cache350 : UInt256
  late342 : UInt256
  late252 : UInt256
  h4 : UInt256
  h1 : UInt256
  h2 : UInt256
  h3 : UInt256
  h0 : UInt256
  off : UInt256
  limit : UInt256

def stack0 (q : Input) (rho : List UInt256) : List UInt256 := [ q.ld, q.lb, q.le, q.la, q.late252, q.late342, q.k, q.lc, q.re, q.rc, q.ra, q.rd, q.rb, q.factor, q.lower, q.cache140, q.cache190, q.cache310, q.cache350, q.h4, q.h1, q.h2, q.h3, q.h0, q.off, q.limit ] ++ rho

def chunk0 : List Instr := [ .op (.Swap ⟨8, by decide⟩),
    .push ⟨1, by decide⟩ (UInt256.ofNat 144),
    .op .SHR,
    .op .ADD,
    .op (.Swap ⟨8, by decide⟩),
    .push ⟨1, by decide⟩ (UInt256.ofNat 144),
    .op .SHR,
    .op .ADD,
    .op (.Swap ⟨12, by decide⟩),
    .op .POP ]

def stack1 (q : Input) (rho : List UInt256) : List UInt256 := [ q.la, q.late252, q.late342, q.k, q.lc, q.re, q.ld, (UInt256.add (UInt256.shiftRight q.rc (UInt256.ofNat 144)) q.lb), q.rd, q.rb, q.factor, q.lower, (UInt256.add (UInt256.shiftRight q.ra (UInt256.ofNat 144)) q.le), q.cache190, q.cache310, q.cache350, q.h4, q.h1, q.h2, q.h3, q.h0, q.off, q.limit ] ++ rho
theorem run_chunk0 (s : State) (pc : UInt256) (q : Input) (rho : List UInt256)
    (hstack : rho.length ≤ 980) (hrun : s.halt = .Running) :
    runInstrSeq chunk0 {s with pc := pc, stack := stack0 q rho} =
      some {s with pc := pcAfter pc chunk0, stack := stack1 q rho} := by
  have hcap (n : Nat) (hn : n ≤ 43) : rho.length + n < 1024 := by omega
  simp (discharger := omega) [chunk0, stack0, stack1, runInstrSeq,
    Stepper.runInstr, UInt256.succ, pcAfter, Instr.size, hrun, hcap,
    Nat.add_assoc, List.getElem?_cons_zero, List.exchange,
    Word.word_toNat_ofNat, Word.literal_eq_ofNat]
  all_goals repeat first | apply And.intro | rfl
#print axioms run_chunk0

def chunk1 : List Instr := [ .op (.Swap ⟨9, by decide⟩),
    .op .POP,
    .op .POP,
    .op .POP,
    .op (.Swap ⟨4, by decide⟩),
    .push ⟨1, by decide⟩ (UInt256.ofNat 144),
    .op .SHR,
    .op .ADD,
    .op (.Swap ⟨10, by decide⟩),
    .op .POP ]

def stack2 (q : Input) (rho : List UInt256) : List UInt256 := [ q.re, q.ld, (UInt256.add (UInt256.shiftRight q.rc (UInt256.ofNat 144)) q.lb), q.k, q.rb, q.la, q.lower, (UInt256.add (UInt256.shiftRight q.ra (UInt256.ofNat 144)) q.le), q.cache190, q.cache310, (UInt256.add (UInt256.shiftRight q.rd (UInt256.ofNat 144)) q.lc), q.h4, q.h1, q.h2, q.h3, q.h0, q.off, q.limit ] ++ rho
theorem run_chunk1 (s : State) (pc : UInt256) (q : Input) (rho : List UInt256)
    (hstack : rho.length ≤ 980) (hrun : s.halt = .Running) :
    runInstrSeq chunk1 {s with pc := pc, stack := stack1 q rho} =
      some {s with pc := pcAfter pc chunk1, stack := stack2 q rho} := by
  have hcap (n : Nat) (hn : n ≤ 43) : rho.length + n < 1024 := by omega
  simp (discharger := omega) [chunk1, stack1, stack2, runInstrSeq,
    Stepper.runInstr, UInt256.succ, pcAfter, Instr.size, hrun, hcap,
    Nat.add_assoc, List.getElem?_cons_zero, List.exchange,
    Word.word_toNat_ofNat, Word.literal_eq_ofNat]
  all_goals repeat first | apply And.intro | rfl
#print axioms run_chunk1

def chunk2 : List Instr := [ .push ⟨1, by decide⟩ (UInt256.ofNat 144),
    .op .SHR,
    .op .ADD,
    .op (.Swap ⟨6, by decide⟩),
    .op .POP,
    .op (.Swap ⟨6, by decide⟩),
    .op .POP,
    .op .POP,
    .push ⟨1, by decide⟩ (UInt256.ofNat 144),
    .op .SHR,
    .op .ADD ]

def stack3 (q : Input) (rho : List UInt256) : List UInt256 := [ (UInt256.add (UInt256.shiftRight q.rb (UInt256.ofNat 144)) q.la), q.lower, (UInt256.add (UInt256.shiftRight q.ra (UInt256.ofNat 144)) q.le), (UInt256.add (UInt256.shiftRight q.re (UInt256.ofNat 144)) q.ld), (UInt256.add (UInt256.shiftRight q.rc (UInt256.ofNat 144)) q.lb), (UInt256.add (UInt256.shiftRight q.rd (UInt256.ofNat 144)) q.lc), q.h4, q.h1, q.h2, q.h3, q.h0, q.off, q.limit ] ++ rho
theorem run_chunk2 (s : State) (pc : UInt256) (q : Input) (rho : List UInt256)
    (hstack : rho.length ≤ 980) (hrun : s.halt = .Running) :
    runInstrSeq chunk2 {s with pc := pc, stack := stack2 q rho} =
      some {s with pc := pcAfter pc chunk2, stack := stack3 q rho} := by
  have hcap (n : Nat) (hn : n ≤ 43) : rho.length + n < 1024 := by omega
  simp (discharger := omega) [chunk2, stack2, stack3, runInstrSeq,
    Stepper.runInstr, UInt256.succ, pcAfter, Instr.size, hrun, hcap,
    Nat.add_assoc, List.getElem?_cons_zero, List.exchange,
    Word.word_toNat_ofNat, Word.literal_eq_ofNat]
  all_goals repeat first | apply And.intro | rfl
#print axioms run_chunk2

def chunk3 : List Instr := [ .op (.Swap ⟨0, by decide⟩),
    .op (.Swap ⟨5, by decide⟩),
    .op .ADD,
    .op (.Dup ⟨5, by decide⟩),
    .op .AND,
    .op (.Swap ⟨7, by decide⟩),
    .op .ADD,
    .op (.Dup ⟨4, by decide⟩),
    .op .AND,
    .op (.Swap ⟨5, by decide⟩) ]

def stack4 (q : Input) (rho : List UInt256) : List UInt256 := [ q.h2, (UInt256.add (UInt256.shiftRight q.re (UInt256.ofNat 144)) q.ld), (UInt256.add (UInt256.shiftRight q.rc (UInt256.ofNat 144)) q.lb), (UInt256.add (UInt256.shiftRight q.rd (UInt256.ofNat 144)) q.lc), q.lower, q.h1, (UInt256.land q.lower (UInt256.add q.h3 (UInt256.add (UInt256.shiftRight q.ra (UInt256.ofNat 144)) q.le))), (UInt256.land q.lower (UInt256.add q.h4 (UInt256.add (UInt256.shiftRight q.rb (UInt256.ofNat 144)) q.la))), q.h0, q.off, q.limit ] ++ rho
theorem run_chunk3 (s : State) (pc : UInt256) (q : Input) (rho : List UInt256)
    (hstack : rho.length ≤ 980) (hrun : s.halt = .Running) :
    runInstrSeq chunk3 {s with pc := pc, stack := stack3 q rho} =
      some {s with pc := pcAfter pc chunk3, stack := stack4 q rho} := by
  have hcap (n : Nat) (hn : n ≤ 43) : rho.length + n < 1024 := by omega
  simp (discharger := omega) [chunk3, stack3, stack4, runInstrSeq,
    Stepper.runInstr, UInt256.succ, pcAfter, Instr.size, hrun, hcap,
    Nat.add_assoc, List.getElem?_cons_zero, List.exchange,
    Word.word_toNat_ofNat, Word.literal_eq_ofNat]
  all_goals repeat first | apply And.intro | rfl
#print axioms run_chunk3

def chunk4 : List Instr := [ .op .ADD,
    .op (.Swap ⟨6, by decide⟩),
    .op .ADD,
    .op (.Dup ⟨2, by decide⟩),
    .op .AND,
    .op (.Swap ⟨5, by decide⟩),
    .op (.Dup ⟨2, by decide⟩),
    .op .AND,
    .op (.Swap ⟨2, by decide⟩),
    .op .ADD,
    .op .AND ]

def stack5 (q : Input) (rho : List UInt256) : List UInt256 := [ (UInt256.land (UInt256.add q.h1 (UInt256.add (UInt256.shiftRight q.rd (UInt256.ofNat 144)) q.lc)) q.lower), (UInt256.land q.lower (UInt256.add q.h2 (UInt256.add (UInt256.shiftRight q.re (UInt256.ofNat 144)) q.ld))), (UInt256.land q.lower (UInt256.add q.h3 (UInt256.add (UInt256.shiftRight q.ra (UInt256.ofNat 144)) q.le))), (UInt256.land q.lower (UInt256.add q.h4 (UInt256.add (UInt256.shiftRight q.rb (UInt256.ofNat 144)) q.la))), (UInt256.land q.lower (UInt256.add q.h0 (UInt256.add (UInt256.shiftRight q.rc (UInt256.ofNat 144)) q.lb))), q.off, q.limit ] ++ rho
theorem run_chunk4 (s : State) (pc : UInt256) (q : Input) (rho : List UInt256)
    (hstack : rho.length ≤ 980) (hrun : s.halt = .Running) :
    runInstrSeq chunk4 {s with pc := pc, stack := stack4 q rho} =
      some {s with pc := pcAfter pc chunk4, stack := stack5 q rho} := by
  have hcap (n : Nat) (hn : n ≤ 43) : rho.length + n < 1024 := by omega
  simp (discharger := omega) [chunk4, stack4, stack5, runInstrSeq,
    Stepper.runInstr, UInt256.succ, pcAfter, Instr.size, hrun, hcap,
    Nat.add_assoc, List.getElem?_cons_zero, List.exchange,
    Word.word_toNat_ofNat, Word.literal_eq_ofNat]
  all_goals repeat first | apply And.intro | rfl
#print axioms run_chunk4

def template : List Instr := chunk0 ++ chunk1 ++ chunk2 ++ chunk3 ++ chunk4
theorem run_template (s : State) (pc : UInt256) (q : Input) (rho : List UInt256)
    (hstack : rho.length ≤ 980) (hrun : s.halt = .Running) :
    runInstrSeq template {s with pc := pc, stack := stack0 q rho} =
      some {s with pc := pcAfter pc template, stack := stack5 q rho} := by
  have h0 := run_chunk0 s (pc) q rho hstack hrun
  have h1 := run_chunk1 s (pcAfter (pc) chunk0) q rho hstack hrun
  have h2 := run_chunk2 s (pcAfter (pcAfter (pc) chunk0) chunk1) q rho hstack hrun
  have h3 := run_chunk3 s (pcAfter (pcAfter (pcAfter (pc) chunk0) chunk1) chunk2) q rho hstack hrun
  have h4 := run_chunk4 s (pcAfter (pcAfter (pcAfter (pcAfter (pc) chunk0) chunk1) chunk2) chunk3) q rho hstack hrun
  have hsum1 := DenseScheduleTrace.runInstrSeq_append_running h0 (by exact hrun) h1
  have hsum2 := DenseScheduleTrace.runInstrSeq_append_running hsum1 (by exact hrun) h2
  have hsum3 := DenseScheduleTrace.runInstrSeq_append_running hsum2 (by exact hrun) h3
  have hsum4 := DenseScheduleTrace.runInstrSeq_append_running hsum3 (by exact hrun) h4
  simpa only [template, DenseScheduleTrace.pcAfter_append] using hsum4
#print axioms run_template
end Challenge.Ripemd160.Submission.Proofs.Bytecode.StaggerPersistentTailRaw
