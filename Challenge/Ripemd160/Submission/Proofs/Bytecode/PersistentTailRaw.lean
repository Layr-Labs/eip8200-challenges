import Challenge.Ripemd160.Submission.Proofs.Bytecode.StackRoundTrace
import Challenge.Ripemd160.Submission.Proofs.Bytecode.Word
set_option warningAsError true
set_option maxRecDepth 30000
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.PersistentTailRaw
open EvmSemantics EvmSemantics.EVM YulEvmCompiler Challenge.EvmProof
open StackRoundTrace
structure Input where
  a : UInt256
  b : UInt256
  c : UInt256
  d : UInt256
  e : UInt256
  factor : UInt256
  pair : UInt256
  upper : UInt256
  lower : UInt256
  k0 : UInt256
  k1 : UInt256
  k2 : UInt256
  k3 : UInt256
  k4 : UInt256
  k5 : UInt256
  h0 : UInt256
  h1 : UInt256
  h2 : UInt256
  h3 : UInt256
  h4 : UInt256
  off : UInt256
  limit : UInt256

def stack0 (q : Input) (rho : List UInt256) : List UInt256 := [q.d, q.b, q.c, q.a, q.e, q.factor, q.pair, q.upper, q.lower, q.k0, q.k1, q.k2, q.k3, q.k4, q.k5, q.h0, q.h1, q.h2, q.h3, q.h4, q.off, q.limit] ++ rho

def chunk0 : List Instr := [
  .op (.Swap ⟨5, by decide⟩),
  .op .POP,
  .op (.Swap ⟨5, by decide⟩),
  .op .POP,
  .op (.Swap ⟨2, by decide⟩),
  .op .POP,
  .op (.Swap ⟨5, by decide⟩),
  .op .POP,
  .op (.Swap ⟨5, by decide⟩),
  .op .POP,
  .op (.Dup ⟨10, by decide⟩) ]
def stack1 (q : Input) (rho : List UInt256) : List UInt256 := [q.h0, q.c, q.d, q.b, q.lower, q.a, q.e, q.k2, q.k3, q.k4, q.k5, q.h0, q.h1, q.h2, q.h3, q.h4, q.off, q.limit] ++ rho
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

def chunk1 : List Instr := [
  .op (.Dup ⟨12, by decide⟩),
  .op (.Dup ⟨2, by decide⟩),
  .op (.Dup ⟨4, by decide⟩),
  .push ⟨1, by decide⟩ (UInt256.ofNat 144),
  .op .SHR,
  .op .ADD,
  .op .ADD,
  .op (.Dup ⟨5, by decide⟩),
  .op .AND,
  .op (.Swap ⟨11, by decide⟩),
  .op .POP ]
def stack2 (q : Input) (rho : List UInt256) : List UInt256 := [q.h0, q.c, q.d, q.b, q.lower, q.a, q.e, q.k2, q.k3, q.k4, q.k5, (UInt256.land q.lower (UInt256.add (UInt256.add (UInt256.shiftRight q.d (UInt256.ofNat 144)) q.c) q.h1)), q.h1, q.h2, q.h3, q.h4, q.off, q.limit] ++ rho
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

def chunk2 : List Instr := [
  .op (.Dup ⟨13, by decide⟩),
  .op (.Dup ⟨3, by decide⟩),
  .op (.Dup ⟨8, by decide⟩),
  .push ⟨1, by decide⟩ (UInt256.ofNat 144),
  .op .SHR,
  .op .ADD,
  .op .ADD,
  .op (.Dup ⟨5, by decide⟩),
  .op .AND,
  .op (.Swap ⟨12, by decide⟩),
  .op .POP ]
def stack3 (q : Input) (rho : List UInt256) : List UInt256 := [q.h0, q.c, q.d, q.b, q.lower, q.a, q.e, q.k2, q.k3, q.k4, q.k5, (UInt256.land q.lower (UInt256.add (UInt256.add (UInt256.shiftRight q.d (UInt256.ofNat 144)) q.c) q.h1)), (UInt256.land q.lower (UInt256.add (UInt256.add (UInt256.shiftRight q.e (UInt256.ofNat 144)) q.d) q.h2)), q.h2, q.h3, q.h4, q.off, q.limit] ++ rho
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

def chunk3 : List Instr := [
  .op (.Dup ⟨14, by decide⟩),
  .op (.Dup ⟨7, by decide⟩),
  .op (.Dup ⟨7, by decide⟩),
  .push ⟨1, by decide⟩ (UInt256.ofNat 144),
  .op .SHR,
  .op .ADD,
  .op .ADD,
  .op (.Dup ⟨5, by decide⟩),
  .op .AND,
  .op (.Swap ⟨13, by decide⟩),
  .op .POP ]
def stack4 (q : Input) (rho : List UInt256) : List UInt256 := [q.h0, q.c, q.d, q.b, q.lower, q.a, q.e, q.k2, q.k3, q.k4, q.k5, (UInt256.land q.lower (UInt256.add (UInt256.add (UInt256.shiftRight q.d (UInt256.ofNat 144)) q.c) q.h1)), (UInt256.land q.lower (UInt256.add (UInt256.add (UInt256.shiftRight q.e (UInt256.ofNat 144)) q.d) q.h2)), (UInt256.land q.lower (UInt256.add (UInt256.add (UInt256.shiftRight q.a (UInt256.ofNat 144)) q.e) q.h3)), q.h3, q.h4, q.off, q.limit] ++ rho
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

def chunk4 : List Instr := [
  .op (.Dup ⟨15, by decide⟩),
  .op (.Dup ⟨6, by decide⟩),
  .op (.Dup ⟨5, by decide⟩),
  .push ⟨1, by decide⟩ (UInt256.ofNat 144),
  .op .SHR,
  .op .ADD,
  .op .ADD,
  .op (.Dup ⟨5, by decide⟩),
  .op .AND,
  .op (.Swap ⟨14, by decide⟩),
  .op .POP ]
def stack5 (q : Input) (rho : List UInt256) : List UInt256 := [q.h0, q.c, q.d, q.b, q.lower, q.a, q.e, q.k2, q.k3, q.k4, q.k5, (UInt256.land q.lower (UInt256.add (UInt256.add (UInt256.shiftRight q.d (UInt256.ofNat 144)) q.c) q.h1)), (UInt256.land q.lower (UInt256.add (UInt256.add (UInt256.shiftRight q.e (UInt256.ofNat 144)) q.d) q.h2)), (UInt256.land q.lower (UInt256.add (UInt256.add (UInt256.shiftRight q.a (UInt256.ofNat 144)) q.e) q.h3)), (UInt256.land q.lower (UInt256.add (UInt256.add (UInt256.shiftRight q.b (UInt256.ofNat 144)) q.a) q.h4)), q.h4, q.off, q.limit] ++ rho
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

def chunk5 : List Instr := [
  .op (.Dup ⟨3, by decide⟩),
  .op (.Dup ⟨2, by decide⟩),
  .push ⟨1, by decide⟩ (UInt256.ofNat 144),
  .op .SHR,
  .op .ADD,
  .op .ADD,
  .op (.Dup ⟨4, by decide⟩),
  .op .AND,
  .op (.Swap ⟨14, by decide⟩),
  .op .POP ]
def stack6 (q : Input) (rho : List UInt256) : List UInt256 := [q.c, q.d, q.b, q.lower, q.a, q.e, q.k2, q.k3, q.k4, q.k5, (UInt256.land q.lower (UInt256.add (UInt256.add (UInt256.shiftRight q.d (UInt256.ofNat 144)) q.c) q.h1)), (UInt256.land q.lower (UInt256.add (UInt256.add (UInt256.shiftRight q.e (UInt256.ofNat 144)) q.d) q.h2)), (UInt256.land q.lower (UInt256.add (UInt256.add (UInt256.shiftRight q.a (UInt256.ofNat 144)) q.e) q.h3)), (UInt256.land q.lower (UInt256.add (UInt256.add (UInt256.shiftRight q.b (UInt256.ofNat 144)) q.a) q.h4)), (UInt256.land q.lower (UInt256.add (UInt256.add (UInt256.shiftRight q.c (UInt256.ofNat 144)) q.b) q.h0)), q.off, q.limit] ++ rho
theorem run_chunk5 (s : State) (pc : UInt256) (q : Input) (rho : List UInt256)
    (hstack : rho.length ≤ 980) (hrun : s.halt = .Running) :
    runInstrSeq chunk5 {s with pc := pc, stack := stack5 q rho} =
      some {s with pc := pcAfter pc chunk5, stack := stack6 q rho} := by
  have hcap (n : Nat) (hn : n ≤ 43) : rho.length + n < 1024 := by omega
  simp (discharger := omega) [chunk5, stack5, stack6, runInstrSeq,
    Stepper.runInstr, UInt256.succ, pcAfter, Instr.size, hrun, hcap,
    Nat.add_assoc, List.getElem?_cons_zero, List.exchange,
    Word.word_toNat_ofNat, Word.literal_eq_ofNat]
  all_goals repeat first | apply And.intro | rfl
#print axioms run_chunk5

def chunk6 : List Instr := [
  .op .POP,
  .op .POP,
  .op .POP,
  .op .POP,
  .op .POP,
  .op .POP,
  .op .POP,
  .op .POP,
  .op .POP,
  .op .POP ]
def stack7 (q : Input) (rho : List UInt256) : List UInt256 := [(UInt256.land q.lower (UInt256.add (UInt256.add (UInt256.shiftRight q.d (UInt256.ofNat 144)) q.c) q.h1)), (UInt256.land q.lower (UInt256.add (UInt256.add (UInt256.shiftRight q.e (UInt256.ofNat 144)) q.d) q.h2)), (UInt256.land q.lower (UInt256.add (UInt256.add (UInt256.shiftRight q.a (UInt256.ofNat 144)) q.e) q.h3)), (UInt256.land q.lower (UInt256.add (UInt256.add (UInt256.shiftRight q.b (UInt256.ofNat 144)) q.a) q.h4)), (UInt256.land q.lower (UInt256.add (UInt256.add (UInt256.shiftRight q.c (UInt256.ofNat 144)) q.b) q.h0)), q.off, q.limit] ++ rho
theorem run_chunk6 (s : State) (pc : UInt256) (q : Input) (rho : List UInt256)
    (hstack : rho.length ≤ 980) (hrun : s.halt = .Running) :
    runInstrSeq chunk6 {s with pc := pc, stack := stack6 q rho} =
      some {s with pc := pcAfter pc chunk6, stack := stack7 q rho} := by
  have hcap (n : Nat) (hn : n ≤ 43) : rho.length + n < 1024 := by omega
  simp (discharger := omega) [chunk6, stack6, stack7, runInstrSeq,
    Stepper.runInstr, UInt256.succ, pcAfter, Instr.size, hrun, hcap,
    Nat.add_assoc, List.getElem?_cons_zero, List.exchange,
    Word.word_toNat_ofNat, Word.literal_eq_ofNat]
  all_goals repeat first | apply And.intro | rfl
#print axioms run_chunk6
private theorem pcAfter_append (pc : UInt256) (first second : List Instr) :
    pcAfter pc (first ++ second) = pcAfter (pcAfter pc first) second := by
  induction first generalizing pc with
  | nil => rfl
  | cons instruction rest ih =>
      simp only [List.cons_append, pcAfter]
      exact ih (pc := pc + UInt256.ofNat instruction.size)

private theorem runInstrSeq_append_running
    {first second : List Instr} {s middle result : State}
    (hfirst : runInstrSeq first s = some middle)
    (hmiddle : middle.halt = .Running)
    (hsecond : runInstrSeq second middle = some result) :
    runInstrSeq (first ++ second) s = some result := by
  induction first generalizing s middle with
  | nil =>
      simp only [List.nil_append, runInstrSeq] at hfirst ⊢
      cases hfirst
      exact hsecond
  | cons instruction rest ih =>
      cases hrun : Challenge.EvmProof.Stepper.runInstr instruction s with
      | none =>
          simp [runInstrSeq, hrun] at hfirst
      | some next =>
          cases rest with
          | nil =>
              have hnext : next = middle := by
                simpa [runInstrSeq, hrun] using hfirst
              subst middle
              cases second with
              | nil =>
                  simpa [runInstrSeq, hrun] using hsecond
              | cons nextInstruction secondRest =>
                  simpa [runInstrSeq, hrun, hmiddle] using hsecond
          | cons nextInstruction restTail =>
              cases hhalt : next.halt with
              | Running =>
                  have htail :
                      runInstrSeq (nextInstruction :: restTail) next = some middle := by
                    simpa [runInstrSeq, hrun, hhalt] using hfirst
                  have hjoined := ih (s := next) (middle := middle)
                    htail hmiddle hsecond
                  simpa [runInstrSeq, hrun, hhalt] using hjoined
              | Success =>
                  simp [runInstrSeq, hrun, hhalt] at hfirst
              | Returned =>
                  simp [runInstrSeq, hrun, hhalt] at hfirst
              | Reverted =>
                  simp [runInstrSeq, hrun, hhalt] at hfirst
              | Exception error =>
                  simp [runInstrSeq, hrun, hhalt] at hfirst


def template : List Instr := chunk0 ++ chunk1 ++ chunk2 ++ chunk3 ++ chunk4 ++ chunk5 ++ chunk6

theorem run_template (s : State) (pc : UInt256) (q : Input) (rho : List UInt256)
    (hstack : rho.length ≤ 980) (hrun : s.halt = .Running) :
    runInstrSeq template {s with pc := pc, stack := stack0 q rho} =
      some {s with pc := pcAfter pc template, stack := stack7 q rho} := by
  have h0 := run_chunk0 (s) (pc) q rho hstack hrun
  have h1 := run_chunk1 ({s with pc := pcAfter (pc) chunk0, stack := stack1 q rho}) (pcAfter (pc) chunk0) q rho hstack hrun
  have j1 := runInstrSeq_append_running h0 hrun h1
  have h2 := run_chunk2 ({s with pc := pcAfter (pcAfter (pc) chunk0) chunk1, stack := stack2 q rho}) (pcAfter (pcAfter (pc) chunk0) chunk1) q rho hstack hrun
  have j2 := runInstrSeq_append_running j1 hrun h2
  have h3 := run_chunk3 ({s with pc := pcAfter (pcAfter (pcAfter (pc) chunk0) chunk1) chunk2, stack := stack3 q rho}) (pcAfter (pcAfter (pcAfter (pc) chunk0) chunk1) chunk2) q rho hstack hrun
  have j3 := runInstrSeq_append_running j2 hrun h3
  have h4 := run_chunk4 ({s with pc := pcAfter (pcAfter (pcAfter (pcAfter (pc) chunk0) chunk1) chunk2) chunk3, stack := stack4 q rho}) (pcAfter (pcAfter (pcAfter (pcAfter (pc) chunk0) chunk1) chunk2) chunk3) q rho hstack hrun
  have j4 := runInstrSeq_append_running j3 hrun h4
  have h5 := run_chunk5 ({s with pc := pcAfter (pcAfter (pcAfter (pcAfter (pcAfter (pc) chunk0) chunk1) chunk2) chunk3) chunk4, stack := stack5 q rho}) (pcAfter (pcAfter (pcAfter (pcAfter (pcAfter (pc) chunk0) chunk1) chunk2) chunk3) chunk4) q rho hstack hrun
  have j5 := runInstrSeq_append_running j4 hrun h5
  have h6 := run_chunk6 ({s with pc := pcAfter (pcAfter (pcAfter (pcAfter (pcAfter (pcAfter (pc) chunk0) chunk1) chunk2) chunk3) chunk4) chunk5, stack := stack6 q rho}) (pcAfter (pcAfter (pcAfter (pcAfter (pcAfter (pcAfter (pc) chunk0) chunk1) chunk2) chunk3) chunk4) chunk5) q rho hstack hrun
  have j6 := runInstrSeq_append_running j5 hrun h6
  simpa only [template, pcAfter_append] using j6
#print axioms run_template
end Challenge.Ripemd160.Submission.Proofs.Bytecode.PersistentTailRaw
