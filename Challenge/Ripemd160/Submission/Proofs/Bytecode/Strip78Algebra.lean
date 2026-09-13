import Challenge.Ripemd160.Submission.Proofs.Bytecode.GapCarry
import Challenge.Ripemd160.Submission.Proofs.Bytecode.TerminalRound

set_option warningAsError true
set_option linter.unusedSimpArgs false
set_option maxRecDepth 10000
set_option maxHeartbeats 4000000
namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.Strip78Algebra
open EvmSemantics PairedLaneUInt256Bridge PairedLaneCore PairedLaneScaledRotate
open PairedHelperBooleanTrace PairedAllInlineCoreTrace
open PairedStartupTrace (pairWord lowerWord upperWord)

theorem bits_mask (x : UInt256) : bits (UInt256.land pairWord x) = normalize (bits x) := by
  rw [bits_land, normalize_eq_and, BitVec.and_comm]
  rfl

theorem clean_gap (x : BitVec 256) (hx : normalize x = x) : x.getLsbD 64 = false := by
  rw [← hx, normalize_eq_and, BitVec.getLsbD_and]
  have h : pairMask.getLsbD 64 = false := by decide
  simp only [h, Bool.and_false]

theorem scaled78_add_gap (a b e f : BitVec 32) :
    (pack e f + ((scaleHigh (pack a b) 6 * PairedLaneProduct.factor) >>> 27)).getLsbD 64 = false := by
  rw [← BitVec.testBit_toNat, BitVec.toNat_add, pack_toNat, toNat_shift,
    scaleHigh_product_toNat a b 6 (by decide)]
  have ha := a.isLt
  have hb := b.isLt
  have he := e.isLt
  have hf := f.isLt
  rw [Nat.testBit_eq_decide_div_mod_eq]
  simp only [Nat.reducePow] at *
  apply decide_eq_false_iff_not.mpr
  omega

def maskedBD (q : Frame) : Frame :=
  {q with b := UInt256.land pairWord q.b, d := UInt256.land pairWord q.d}

theorem inline4_mask (q : Frame) (hc : UInt256.land pairWord q.c = q.c)
    (hlower : q.lower = lowerWord) :
    UInt256.land pairWord (inline4Boolean q) = inline4Boolean (maskedBD q) := by
  apply bits_injective
  have hc' := congrArg bits hc
  simp only [bits_land] at hc'
  simp only [inline4Boolean, maskedBD, hlower, bits_land, bits_xor, bits_lor, bits_lnot]
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  have hcl := congrArg (fun x : BitVec 256 => x.getLsbD i) hc'
  have hlp : bits pairWord &&& bits lowerWord = bits lowerWord := by decide
  have hl := congrArg (fun x : BitVec 256 => x.getLsbD i) hlp
  simp only [BitVec.getLsbD_and] at hcl hl
  simp only [BitVec.getLsbD_xor, BitVec.getLsbD_and, BitVec.getLsbD_or,
    BitVec.getLsbD_not, hi, decide_true, Bool.true_and]
  have hbool : ∀ p l b c d : Bool, (p && c) = c → (p && l) = l →
      (p && ((l && (d || !c)) ^^ (d ^^ (c ^^ b)))) =
      ((l && ((p && d) || !c)) ^^ ((p && d) ^^ (c ^^ (p && b)))) := by decide
  exact hbool _ _ _ _ _ hcl hl

theorem inline4_gap (q : Frame) (hb : (bits q.b).getLsbD 64 = false)
    (hc : (bits q.c).getLsbD 64 = false) (hd : (bits q.d).getLsbD 64 = false)
    (hlower : q.lower = lowerWord) :
    (bits (inline4Boolean q)).getLsbD 64 = false := by
  have hl : (bits lowerWord).getLsbD 64 = false := by decide
  simp only [inline4Boolean, bits_xor, bits_land, bits_lor, bits_lnot,
    BitVec.getLsbD_xor, BitVec.getLsbD_and, BitVec.getLsbD_or,
    BitVec.getLsbD_not, hlower, hl, hb, hc, hd]
  rfl

theorem mask_add_gap (x y : UInt256)
    (hy : y.toNat % 2 ^ 128 < 2 ^ 63) (hx : (bits x).getLsbD 64 = false) :
    UInt256.land pairWord (UInt256.add x y) =
      UInt256.land pairWord (UInt256.add (UInt256.land pairWord x) y) := by
  apply bits_injective
  simp only [bits_mask, bits_add]
  exact GapCarry.normalize_add_gap (bits x) (bits y) hy hx

theorem inlineSum_masked (q : Frame) (hpair : q.pair = pairWord)
    (hlower : q.lower = lowerWord) (hc : UInt256.land pairWord q.c = q.c)
    (hb : (bits q.b).getLsbD 64 = false) (hd : (bits q.d).getLsbD 64 = false)
    (hsmall : (UInt256.add q.k (UInt256.add q.message0 q.a)).toNat % 2 ^ 128 < 2 ^ 63) :
    inlineSum q (inline4Boolean q) = inlineSum (maskedBD q) (inline4Boolean (maskedBD q)) := by
  have hc' : (bits q.c).getLsbD 64 = false := by
    apply clean_gap
    rw [← bits_mask, hc]
  have hgap := inline4_gap q hb hc' hd hlower
  have hadd : ∀ v : UInt256,
      UInt256.add q.k (UInt256.add q.message0 (UInt256.add v q.a)) =
      UInt256.add v (UInt256.add q.k (UInt256.add q.message0 q.a)) := by
    intro v
    apply bits_injective
    simp only [bits_add]
    ac_rfl
  have h := mask_add_gap (inline4Boolean q) (UInt256.add q.k (UInt256.add q.message0 q.a)) hsmall hgap
  rw [inline4_mask q hc hlower] at h
  simpa only [inlineSum, maskedBD, hpair, hadd] using h

theorem resultMemory_mask_ce (memory : ByteArray) (q : PairedTailTrace.Frame)
    (hlower : q.lower = lowerWord) :
    PairedTailTrace.resultMemory memory
      {q with c := UInt256.land pairWord q.c, e := UInt256.land pairWord q.e} =
      PairedTailTrace.resultMemory memory q := by
  simp only [PairedTailTrace.resultMemory, PairedTailTrace.result0, PairedTailTrace.result1,
    PairedTailTrace.result2, PairedTailTrace.result3, PairedTailTrace.result4,
    hlower, PairedTailTrace.tail_combine_normalized,
    TerminalMask.toUInt32_pair, TerminalMask.toUInt32_pair_shr]

theorem resultMemory_masked (memory : ByteArray) (q : Frame)
    (hpair : q.pair = pairWord) (hlower : q.lower = lowerWord)
    (hc : UInt256.land pairWord q.c = q.c)
    (hb : (bits q.b).getLsbD 64 = false) (hd : (bits q.d).getLsbD 64 = false)
    (hsmall : (UInt256.add q.k (UInt256.add (PairedAllInlineCoreTrace.inline79Frame memory q).message0 q.a)).toNat % 2 ^ 128 < 2 ^ 63) :
    PairedTailTrace.resultMemory memory (TerminalRound.modifiedFrame memory q) =
      PairedTailTrace.resultMemory memory (TerminalRound.modifiedFrame memory (maskedBD q)) := by
  have hs := inlineSum_masked (PairedAllInlineCoreTrace.inline79Frame memory q) hpair hlower hc hb hd hsmall
  have ht : TerminalRound.modifiedT (PairedAllInlineCoreTrace.inline79Frame memory q) (inline4Boolean q) =
      TerminalRound.modifiedT (PairedAllInlineCoreTrace.inline79Frame memory (maskedBD q)) (inline4Boolean (maskedBD q)) := by
    unfold TerminalRound.modifiedT scaledRotation
    rw [show inlineSum (PairedAllInlineCoreTrace.inline79Frame memory q) (inline4Boolean q) =
        inlineSum (PairedAllInlineCoreTrace.inline79Frame memory (maskedBD q)) (inline4Boolean (maskedBD q)) from hs]
    rfl
  have hframe : TerminalRound.modifiedFrame memory (maskedBD q) =
      {TerminalRound.modifiedFrame memory q with
        c := UInt256.land pairWord q.b, e := UInt256.land pairWord q.d} := by
    unfold TerminalRound.modifiedFrame
    rw [ht]
    rfl
  rw [hframe]
  exact (resultMemory_mask_ce memory (TerminalRound.modifiedFrame memory q) hlower).symm

#print axioms resultMemory_masked
#print axioms scaled78_add_gap
#print axioms inlineSum_masked
end Challenge.Ripemd160.Submission.Proofs.Bytecode.Strip78Algebra
