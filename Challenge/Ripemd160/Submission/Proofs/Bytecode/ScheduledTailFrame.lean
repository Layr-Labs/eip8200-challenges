import Challenge.Ripemd160.Submission.Proofs.Bytecode.ScheduledTailRaw
import Challenge.Ripemd160.Submission.Proofs.Bytecode.Compression
import Challenge.Ripemd160.Submission.Proofs.Bytecode.Paired144WordRound
set_option warningAsError true
set_option linter.unusedSimpArgs false
namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.ScheduledTailFrame
open EvmSemantics EvmSemantics.EVM YulEvmCompiler Challenge.EvmProof
open Challenge.EvmProof.Word StackRoundTrace

def frame (h : Compression.HashState) (off limit : UInt256) (rho : List UInt256) : List UInt256 :=
  [Paired144WordRound.factorPlusWord, UInt256.ofNat 4294967295, Paired144WordRound.fusedModulusWord 5 7,
   Paired144WordRound.fusedModulusWord 8 5, Paired144WordRound.fusedCoefficientWord 0 3,
   Paired144WordRound.fusedCoefficientWord 0 2,
   ofUInt32 h.h4, ofUInt32 h.h3, ofUInt32 h.h2, ofUInt32 h.h1, ofUInt32 h.h0, off, limit] ++ rho

def coreRest (h : Compression.HashState) (off limit : UInt256) (rho : List UInt256) : List UInt256 :=
  [ofUInt32 h.h3, ofUInt32 h.h2, ofUInt32 h.h1, ofUInt32 h.h0, off, limit] ++ rho

def bind (h : Compression.HashState) (q : ScheduledTailRaw.Input) : ScheduledTailRaw.Input :=
  {q with
    h0 := ofUInt32 h.h0
    h1 := ofUInt32 h.h1
    h2 := ofUInt32 h.h2
    h3 := ofUInt32 h.h3
    h4 := ofUInt32 h.h4
    lower := UInt256.ofNat 0xffffffff
    factor := Paired144WordRound.factorPlusWord
    cache140 := Paired144WordRound.fusedModulusWord 5 7
    cache350 := Paired144WordRound.fusedModulusWord 8 5
    cache310 := Paired144WordRound.fusedCoefficientWord 0 3
    cache190 := Paired144WordRound.fusedCoefficientWord 0 2}
def high (x : UInt256) : UInt32 := toUInt32 (UInt256.shiftRight x (UInt256.ofNat 144))
def combine (h : Compression.HashState) (q : ScheduledTailRaw.Input) : Compression.HashState :=
  {h0 := h.h1 + toUInt32 q.lc + high q.rd,
   h1 := h.h2 + toUInt32 (Paired144WordRound.wordShift q.ld 23) + high q.re,
   h2 := h.h3 + toUInt32 q.le + high q.ra,
   h3 := h.h4 + toUInt32 q.la + high q.rb,
   h4 := h.h0 + toUInt32 q.lb + high q.rc}

private theorem lower_left (x : UInt256) :
    UInt256.land (UInt256.ofNat 0xffffffff) x = mask32 x := by
  apply word_ext
  change (((UInt256.ofNat 0xffffffff).val &&& x.val).val) =
    ((x.val &&& (UInt256.ofNat 0xffffffff).val).val)
  simp only [Fin.and_val]
  change (UInt256.ofNat 0xffffffff).toNat &&& x.toNat = x.toNat &&& (UInt256.ofNat 0xffffffff).toNat
  exact Nat.and_comm _ _

private theorem lower_right (x : UInt256) :
    UInt256.land x (UInt256.ofNat 0xffffffff) = mask32 x := rfl

private theorem raw_toUInt32_add (x y : UInt256) :
    toUInt32 (UInt256.add x y) = toUInt32 x + toUInt32 y := by
  change toUInt32 (x + y) = _
  exact toUInt32_add x y

theorem tail_result (h : Compression.HashState) (q : ScheduledTailRaw.Input)
    (rho : List UInt256) :
    ScheduledTailRaw.stack4 (bind h q) rho = ofUInt32 h.h2 :: frame (combine h q) q.off q.limit rho := by
  simp only [ScheduledTailRaw.stack4, bind, frame, combine, high, Paired144WordRound.wordShift,
    lower_left, lower_right, mask32_eq_ofUInt32, raw_toUInt32_add, toUInt32_ofUInt32,
    List.cons_append, List.nil_append,
    List.cons.injEq, and_true, true_and]
  repeat' apply And.intro
  all_goals congr 1
  all_goals apply UInt32.eq_of_toBitVec_eq
  all_goals simp only [UInt32.toBitVec_add]
  all_goals ac_rfl

/-- The resident tail now stops at the block exit (4537), before the `h3`/`h2` placement. -/
theorem run_tail (s : State) (pc : UInt256) (h : Compression.HashState)
    (q : ScheduledTailRaw.Input) (rho : List UInt256)
    (hstack : rho.length ≤ 980) (hrun : s.halt = .Running) :
    runInstrSeq ScheduledTailRaw.template
      {s with pc := pc, stack := ScheduledTailRaw.stack0 (bind h q) rho} =
      some {s with
        pc := pcAfter pc ScheduledTailRaw.template
        stack := ScheduledTailRaw.stack3a (bind h q) rho} :=
  ScheduledTailRaw.run_template s pc (bind h q) rho hstack hrun

/-- The tail copy each loop target runs after the exit: the last eight tail instructions and a
`POP` of the old `h2` word, which leaves the frame with the continuation still in its slot. -/
def copyTemplate : List Instr := ScheduledTailRaw.chunk3b ++ [.op .POP]

theorem run_copy (s : State) (pc : UInt256) (h : Compression.HashState)
    (q : ScheduledTailRaw.Input) (rho : List UInt256)
    (hstack : rho.length ≤ 980) (hrun : s.halt = .Running) :
    runInstrSeq copyTemplate
      {s with pc := pc, stack := ScheduledTailRaw.stack3a (bind h q) rho} =
      some {s with
        pc := pcAfter pc copyTemplate
        stack := frame (combine h q) q.off q.limit rho} := by
  have h1 := ScheduledTailRaw.run_chunk3b s pc (bind h q) rho hstack hrun
  rw [tail_result] at h1
  have hlen : (ofUInt32 h.h2 :: frame (combine h q) q.off q.limit rho).length < 1024 := by
    simp only [frame, List.cons_append, List.nil_append, List.length_cons, List.length_append]
    omega
  have h2 : runInstrSeq [.op .POP]
      {s with pc := pcAfter pc ScheduledTailRaw.chunk3b, stack := ofUInt32 h.h2 :: frame (combine h q) q.off q.limit rho} =
      some {s with pc := pcAfter (pcAfter pc ScheduledTailRaw.chunk3b) [.op .POP], stack := frame (combine h q) q.off q.limit rho} := by
    simp only [runInstrSeq, DataStepper.runInstr, if_pos hlen, hrun]
    rfl
  have h12 := DenseScheduleTrace.runInstrSeq_append_running h1 (by exact hrun) h2
  simpa only [copyTemplate, DenseScheduleTrace.pcAfter_append] using h12

/-! The new digest epilogue at 4733 stores the exit stack's words directly: the `h4`, `h1` and `h0`
words are already masked, and the `h3` and `h2` sums are stored unmasked because only their low 32
bits survive the later, lower stores. -/

theorem exit_h4 (h : Compression.HashState) (q : ScheduledTailRaw.Input) :
    UInt256.land (bind h q).lower (UInt256.add (bind h q).h0 (UInt256.add (bind h q).lb
      (UInt256.shiftRight (bind h q).rc (UInt256.ofNat 144)))) = ofUInt32 (combine h q).h4 := by
  simp only [bind, combine, high, lower_left, mask32_eq_ofUInt32, raw_toUInt32_add, toUInt32_ofUInt32]
  congr 1
  apply UInt32.eq_of_toBitVec_eq
  simp only [UInt32.toBitVec_add]
  ac_rfl

theorem exit_h1 (h : Compression.HashState) (q : ScheduledTailRaw.Input) :
    UInt256.land (bind h q).lower (UInt256.add (bind h q).h2 (UInt256.add
      (UInt256.shiftRight (UInt256.mul (bind h q).ld (bind h q).factor) (UInt256.ofNat 23))
      (UInt256.shiftRight (bind h q).re (UInt256.ofNat 144)))) = ofUInt32 (combine h q).h1 := by
  simp only [bind, combine, high, Paired144WordRound.wordShift, lower_left, mask32_eq_ofUInt32,
    raw_toUInt32_add, toUInt32_ofUInt32]
  congr 1
  apply UInt32.eq_of_toBitVec_eq
  simp only [UInt32.toBitVec_add]
  ac_rfl

theorem exit_h0 (h : Compression.HashState) (q : ScheduledTailRaw.Input) :
    UInt256.land (bind h q).lower (UInt256.add (bind h q).h1 (UInt256.add
      (UInt256.shiftRight (bind h q).rd (UInt256.ofNat 144)) (bind h q).lc)) =
      ofUInt32 (combine h q).h0 := by
  simp only [bind, combine, high, lower_left, mask32_eq_ofUInt32, raw_toUInt32_add, toUInt32_ofUInt32]
  congr 1
  apply UInt32.eq_of_toBitVec_eq
  simp only [UInt32.toBitVec_add]
  ac_rfl

theorem exit_h3 (h : Compression.HashState) (q : ScheduledTailRaw.Input) :
    toUInt32 (UInt256.add (UInt256.add (bind h q).h4 (bind h q).la)
      (UInt256.shiftRight (bind h q).rb (UInt256.ofNat 144))) = (combine h q).h3 := by
  simp only [bind, combine, high, raw_toUInt32_add, toUInt32_ofUInt32]

theorem exit_h2 (h : Compression.HashState) (q : ScheduledTailRaw.Input) :
    toUInt32 (UInt256.add (bind h q).h3 (UInt256.add (bind h q).le
      (UInt256.shiftRight (bind h q).ra (UInt256.ofNat 144)))) = (combine h q).h2 := by
  simp only [bind, combine, high, raw_toUInt32_add, toUInt32_ofUInt32]
  ac_rfl

#print axioms tail_result
#print axioms run_tail
#print axioms run_copy
#print axioms exit_h4
#print axioms exit_h3
#print axioms exit_h2
end Challenge.Ripemd160.Submission.Proofs.Bytecode.ScheduledTailFrame
