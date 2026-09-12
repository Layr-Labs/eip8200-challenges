import Challenge.Ripemd160.Submission.Proofs.Bytecode.PersistentTailRaw
import Challenge.Ripemd160.Submission.Proofs.Bytecode.Compression
set_option warningAsError true
namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.PersistentFrame
open EvmSemantics EvmSemantics.EVM YulEvmCompiler Challenge.EvmProof
open Challenge.EvmProof.Word StackRoundTrace

def frame (h : Compression.HashState) (off limit : UInt256)
    (rho : List UInt256) : List UInt256 :=
  [ofUInt32 h.h0, ofUInt32 h.h1, ofUInt32 h.h2, ofUInt32 h.h3,
    ofUInt32 h.h4, off, limit] ++ rho

def bind (h : Compression.HashState) (q : PersistentTailRaw.Input) :
    PersistentTailRaw.Input :=
  {q with
    h0 := ofUInt32 h.h0
    h1 := ofUInt32 h.h1
    h2 := ofUInt32 h.h2
    h3 := ofUInt32 h.h3
    h4 := ofUInt32 h.h4
    lower := UInt256.ofNat 0xffffffff}

def high (x : UInt256) : UInt32 := toUInt32 (UInt256.shiftRight x (UInt256.ofNat 144))

def combine (h : Compression.HashState) (q : PersistentTailRaw.Input) :
    Compression.HashState :=
  {h0 := h.h1 + toUInt32 q.c + high q.d,
   h1 := h.h2 + toUInt32 q.d + high q.e,
   h2 := h.h3 + toUInt32 q.e + high q.a,
   h3 := h.h4 + toUInt32 q.a + high q.b,
   h4 := h.h0 + toUInt32 q.b + high q.c}

private theorem lower_left (x : UInt256) :
    UInt256.land (UInt256.ofNat 0xffffffff) x = mask32 x := by
  apply word_ext
  change (((UInt256.ofNat 0xffffffff).val &&& x.val).val) =
    ((x.val &&& (UInt256.ofNat 0xffffffff).val).val)
  simp only [Fin.and_val]
  change (UInt256.ofNat 0xffffffff).toNat &&& x.toNat =
    x.toNat &&& (UInt256.ofNat 0xffffffff).toNat
  exact Nat.and_comm _ _

theorem masked_add (h : UInt32) (left right : UInt256) :
    UInt256.land (UInt256.ofNat 0xffffffff)
      (UInt256.add (UInt256.add right left) (ofUInt32 h)) =
      ofUInt32 (h + toUInt32 left + toUInt32 right) := by
  rw [lower_left, mask32_eq_ofUInt32]
  change ofUInt32 (toUInt32 ((right + left) + ofUInt32 h)) = _
  simp only [toUInt32_add, toUInt32_ofUInt32]
  congr 1
  apply UInt32.eq_of_toBitVec_eq
  simp only [UInt32.toBitVec_add]
  ac_rfl

theorem tail_result (h : Compression.HashState) (q : PersistentTailRaw.Input)
    (rho : List UInt256) :
    PersistentTailRaw.stack7 (bind h q) rho =
      frame (combine h q) q.off q.limit rho := by
  simp only [PersistentTailRaw.stack7, bind, frame, combine, high, masked_add]

theorem run_tail (s : State) (pc : UInt256) (h : Compression.HashState)
    (q : PersistentTailRaw.Input) (rho : List UInt256)
    (hstack : rho.length ≤ 980) (hrun : s.halt = .Running) :
    runInstrSeq PersistentTailRaw.template
      {s with pc := pc, stack := PersistentTailRaw.stack0 (bind h q) rho} =
      some {s with
        pc := pcAfter pc PersistentTailRaw.template
        stack := frame (combine h q) q.off q.limit rho} := by
  simpa only [tail_result] using PersistentTailRaw.run_template s pc (bind h q) rho hstack hrun

#print axioms masked_add
#print axioms tail_result
#print axioms run_tail
end Challenge.Ripemd160.Submission.Proofs.Bytecode.PersistentFrame
