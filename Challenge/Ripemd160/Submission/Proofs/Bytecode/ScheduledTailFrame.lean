import Challenge.Ripemd160.Submission.Proofs.Bytecode.ScheduledTailRaw
import Challenge.Ripemd160.Submission.Proofs.Bytecode.Compression
set_option warningAsError true
set_option linter.unusedSimpArgs false
namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.ScheduledTailFrame
open EvmSemantics EvmSemantics.EVM YulEvmCompiler Challenge.EvmProof
open Challenge.EvmProof.Word StackRoundTrace

def frame (h : Compression.HashState) (off limit : UInt256) (rho : List UInt256) : List UInt256 :=
  [ofUInt32 h.h0, ofUInt32 h.h1, ofUInt32 h.h2, ofUInt32 h.h3, ofUInt32 h.h4, off, limit] ++ rho

def coreRest (h : Compression.HashState) (off limit : UInt256) (rho : List UInt256) : List UInt256 :=
  [ofUInt32 h.h1, ofUInt32 h.h2, ofUInt32 h.h3, ofUInt32 h.h0, off, limit] ++ rho

def bind (h : Compression.HashState) (q : ScheduledTailRaw.Input) : ScheduledTailRaw.Input :=
  {q with
    h0 := ofUInt32 h.h0
    h1 := ofUInt32 h.h1
    h2 := ofUInt32 h.h2
    h3 := ofUInt32 h.h3
    h4 := ofUInt32 h.h4
    lower := UInt256.ofNat 0xffffffff}
def high (x : UInt256) : UInt32 := toUInt32 (UInt256.shiftRight x (UInt256.ofNat 144))
def combine (h : Compression.HashState) (q : ScheduledTailRaw.Input) : Compression.HashState :=
  {h0 := h.h1 + toUInt32 q.lc + high q.rd,
   h1 := h.h2 + toUInt32 q.ld + high q.re,
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
    ScheduledTailRaw.stack5 (bind h q) rho = frame (combine h q) q.off q.limit rho := by
  simp only [ScheduledTailRaw.stack5, bind, frame, combine, high,
    lower_left, lower_right, mask32_eq_ofUInt32, raw_toUInt32_add, toUInt32_ofUInt32,
    List.cons_append, List.nil_append,
    List.cons.injEq, and_true, true_and]
  repeat' apply And.intro
  all_goals congr 1
  all_goals apply UInt32.eq_of_toBitVec_eq
  all_goals simp only [UInt32.toBitVec_add]
  all_goals ac_rfl

theorem run_tail (s : State) (pc : UInt256) (h : Compression.HashState)
    (q : ScheduledTailRaw.Input) (rho : List UInt256)
    (hstack : rho.length ≤ 980) (hrun : s.halt = .Running) :
    runInstrSeq ScheduledTailRaw.template
      {s with pc := pc, stack := ScheduledTailRaw.stack0 (bind h q) rho} =
      some {s with
        pc := pcAfter pc ScheduledTailRaw.template
        stack := frame (combine h q) q.off q.limit rho} := by
  simpa only [tail_result] using ScheduledTailRaw.run_template s pc (bind h q) rho hstack hrun
#print axioms tail_result
#print axioms run_tail
end Challenge.Ripemd160.Submission.Proofs.Bytecode.ScheduledTailFrame
