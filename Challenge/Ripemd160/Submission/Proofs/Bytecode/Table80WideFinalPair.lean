import Challenge.Ripemd160.Submission.Proofs.Bytecode.Table80TerminalTranspose
import Challenge.Ripemd160.Submission.Proofs.Bytecode.Paired80FinalPair
set_option warningAsError true
set_option maxHeartbeats 4000000
namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.Table80WideFinalPair
open Paired80Core Paired80Product Paired80Boolean Paired80RoundSemantic Paired80ScaledRotate
open Paired80Terminal Paired80FinalPair Table80TerminalTranspose Paired80Carry

def wide78 (message k : BitVec 256) (q : Lane 256) : Lane 256 :=
  ⟨q.e, ((scaleHigh (pairedSum 4 q.a q.b q.c q.d message k) 6 * wideFactor) >>> 27) + q.e,
    q.b, (q.c * wideFactor) >>> 22, q.d⟩

def terminal79 (message k : BitVec 256) (q : Lane 256) : Lane 256 :=
  ⟨q.e, (pairedSum 4 q.a q.b q.c q.d message k * wideFactor) >>> 101,
    q.b, (q.c * wideFactor) >>> 22, q.d⟩

def repair (q : Lane 256) : Lane 256 :=
  {q with b := pack (high q.b + low q.a) (low q.b + high q.a)}

theorem eq112_bit (x y : BitVec 256) (h : Paired80Message.Eq112 x y)
    (i : Nat) (hi : i < 112) : x.getLsbD i = y.getLsbD i := by
  have ht : x.setWidth 112 = y.setWidth 112 := by
    apply BitVec.eq_of_toNat_eq
    simpa only [BitVec.toNat_setWidth, Paired80Message.Eq112] using h
  have hg := congrArg (fun (z : BitVec 112) => z.getLsbD i) ht
  simpa only [BitVec.getLsbD_setWidth, hi, decide_true, Bool.true_and] using hg

theorem normalized_shift_add (x e : BitVec 256) (n : Nat) (hn : n ≤ 43) :
    normalize (((x * wideFactor) >>> n) + e) =
      normalize (((x * factor) >>> n) + e) :=
  Paired80Message.normalize_congr _ _ (Paired80Message.add_right _ _ _ (eq112_wide_shift x n hn))

theorem maskBD_wide78 (message k : BitVec 256) (q : Lane 256) :
    maskBD (wide78 message k q) = pairedStep 4 5 11 message k q := by
  simp only [maskBD, wide78, pairedStep, pairedT, rawRotate,
    show (5 : Nat) ≠ 11 by decide, if_false, show ¬ (11 : Nat) < 5 by decide,
    Nat.reduceSub, ← normalize_eq_and]
  rw [normalized_shift_add _ _ 27 (by decide), normalize_wide_shift _ 22 (by decide)]

theorem repair_rotation (x e : BitVec 256)
    (hx : normalize x = x) (he : normalize e = e) :
    pack (high ((x * wideFactor) >>> 101) + low e)
        (low ((x * wideFactor) >>> 101) + high e) =
      normalize (rawRotate x 6 11 + e) := by
  have hxp : x = pack (low x) (high x) := hx.symm
  have hep : e = pack (low e) (high e) := he.symm
  conv_lhs => rw [hxp, hep]
  conv_rhs => rw [hxp, hep]
  rw [terminal_high, terminal_low, low_pack, high_pack]
  rw [normalize_add_pack _ _ _ (rawRotate_gap _ _ 6 11 (by decide) (by decide) (by decide) (by decide)),
    low_rawRotate _ _ 6 11 (by decide) (by decide) (by decide) (by decide),
    high_rawRotate _ _ 6 11 (by decide) (by decide) (by decide) (by decide)]

theorem normalize_terminal79 (q : Lane 256) (message k : BitVec 256)
    (hc : normalize q.c = q.c) (he : normalize q.e = q.e)
    (hb : q.b.getLsbD 48 = false) (hd : q.d.getLsbD 48 = false)
    (hs : (k + (message + q.a)).toNat % 2 ^ 80 < 2 ^ 47) :
    normalizeLane (repair (terminal79 message k q)) =
      pairedStep 4 6 11 message k (maskBD q) := by
  have hsum := sum4_maskBD q message k hc hb hd hs
  have hn : normalize (pairedSum 4 q.a (normalize q.b) q.c (normalize q.d) message k) =
      pairedSum 4 q.a (normalize q.b) q.c (normalize q.d) message k := by
    simp only [pairedSum, ← normalize_eq_and, normalize_idem]
  simp only [normalizeLane, repair, terminal79, pairedStep, maskBD, pairedT,
    normalize_pack, ← normalize_eq_and]
  rw [he, hsum, repair_rotation _ _ hn he, normalize_wide_shift _ 22 (by decide)]

theorem last_two_normalized (l q : Lane 32) (message78 message79 : BitVec 256)
    (wl79 wr79 kl78 kr78 kl79 kr79 : BitVec 32)
    (hm79 : Paired80Message.Eq112 message79 (pack wl79 wr79)) :
    normalizeLane (repair (terminal79 message79 (pack kl79 kr79)
      (wide78 message78 (pack kl78 kr78) (packLane l q)))) =
      pairedStep 4 6 11 message79 (pack kl79 kr79)
        (pairedStep 4 5 11 message78 (pack kl78 kr78) (packLane l q)) := by
  let t := wide78 message78 (pack kl78 kr78) (packLane l q)
  have hsum : normalize (pairedSum 4 (packLane l q).a (packLane l q).b
      (packLane l q).c (packLane l q).d message78 (pack kl78 kr78)) =
      pairedSum 4 (packLane l q).a (packLane l q).b
      (packLane l q).c (packLane l q).d message78 (pack kl78 kr78) := by
    simp only [pairedSum, ← normalize_eq_and, normalize_idem]
  have hb : t.b.getLsbD 48 = false := by
    change (((scaleHigh _ 6 * wideFactor) >>> 27) + pack l.e q.e).getLsbD 48 = false
    rw [eq112_bit _ _ (Paired80Message.add_right _ _ _
      (eq112_wide_shift _ 27 (by decide))) 48 (by decide)]
    rw [← hsum]
    change ((((scaleHigh (pack _ _) 6) * factor) >>> 27) + pack l.e q.e).getLsbD 48 = false
    rw [BitVec.add_comm]
    exact scaled78_add_gap _ _ _ _
  have hd : t.d.getLsbD 48 = false := by
    change (((pack l.c q.c) * wideFactor) >>> 22).getLsbD 48 = false
    rw [BitVec.getLsbD_ushiftRight, wide_bit _ _ (by decide)]
    exact c10_gap l.c q.c
  have hc : normalize t.c = t.c := normalize_pack l.b q.b
  have he : normalize t.e = t.e := normalize_pack l.d q.d
  have hs : (pack kl79 kr79 + (message79 + t.a)).toNat % 2 ^ 80 < 2 ^ 47 :=
    three_small _ _ _ (clean_low _ (normalize_pack _ _))
      (message_low message79 wl79 wr79 hm79) (clean_low _ (normalize_pack l.e q.e))
  rw [normalize_terminal79 t message79 (pack kl79 kr79) hc he hb hd hs]
  rw [maskBD_wide78]

#print axioms maskBD_wide78
#print axioms repair_rotation
#print axioms normalize_terminal79
#print axioms last_two_normalized
end Challenge.Ripemd160.Submission.Proofs.Bytecode.Table80WideFinalPair
