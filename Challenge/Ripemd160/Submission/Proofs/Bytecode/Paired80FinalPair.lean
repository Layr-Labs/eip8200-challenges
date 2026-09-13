import Challenge.Ripemd160.Submission.Proofs.Bytecode.Paired80Terminal
import Challenge.Ripemd160.Submission.Proofs.Bytecode.Paired80RoundSemantic
import Challenge.Ripemd160.Submission.Proofs.Bytecode.Paired80MaskedNot
set_option warningAsError true
namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.Paired80FinalPair
open Paired80Core Paired80Product Paired80Boolean Paired80RoundSemantic Paired80ScaledRotate
open Paired80Terminal

def rawStep (r s : Nat) (message k : BitVec 256) (q : Lane 256) : Lane 256 :=
  ⟨q.e, rawRotate (pairedSum 4 q.a q.b q.c q.d message k) r s + q.e,
    q.b, (q.c * factor) >>> 22, q.d⟩

def normalizeLane (q : Lane 256) : Lane 256 :=
  ⟨normalize q.a, normalize q.b, normalize q.c, normalize q.d, normalize q.e⟩

def maskBD (q : Lane 256) : Lane 256 :=
  {q with b := normalize q.b, d := normalize q.d}

theorem maskBD_rawStep (r s : Nat) (message k : BitVec 256) (q : Lane 256) :
    maskBD (rawStep r s message k q) = pairedStep 4 r s message k q := by
  simp only [maskBD, rawStep, pairedStep, pairedT, normalize_eq_and]

theorem inline4_eq (b c d : BitVec 256) : inline4 b c d = pairedF 4 b c d := by
  simp only [inline4, pairedF, f]
  rw [Paired80MaskedNot.lower_masked_not]
  ac_rfl

theorem sum4_maskBD (q : Lane 256) (message k : BitVec 256)
    (hc : normalize q.c = q.c) (hb : q.b.getLsbD 48 = false) (hd : q.d.getLsbD 48 = false)
    (hs : (k + (message + q.a)).toNat % 2 ^ 80 < 2 ^ 47) :
    pairedSum 4 q.a q.b q.c q.d message k =
      pairedSum 4 q.a (normalize q.b) q.c (normalize q.d) message k := by
  have h := terminal_sum_masked q.b q.c q.d (k + (message + q.a)) hc hb hd hs
  rw [inline4_eq, inline4_eq] at h
  simp only [pairedSum, ← normalize_eq_and]
  convert h using 1 <;> congr 1 <;> ac_rfl

theorem normalize_raw79_maskBD (q : Lane 256) (message k : BitVec 256)
    (hc : normalize q.c = q.c) (he : normalize q.e = q.e)
    (hb : q.b.getLsbD 48 = false) (hd : q.d.getLsbD 48 = false)
    (hs : (k + (message + q.a)).toNat % 2 ^ 80 < 2 ^ 47) :
    normalizeLane (rawStep 6 11 message k q) = pairedStep 4 6 11 message k (maskBD q) := by
  have hsum := sum4_maskBD q message k hc hb hd hs
  simp only [normalizeLane, rawStep, pairedStep, pairedT, maskBD]
  rw [hsum, he]
  simp only [normalize_eq_and]

/-- Both unmasked terminal rounds have the same normalized output as two
canonical rounds, with arbitrary high table bits in each message. -/
theorem last_two_normalized (l q : Lane 32) (message78 message79 : BitVec 256)
    (wl79 wr79 kl78 kr78 kl79 kr79 : BitVec 32)
    (hm79 : Paired80Message.Eq112 message79 (pack wl79 wr79)) :
    normalizeLane (rawStep 6 11 message79 (pack kl79 kr79)
      (rawStep 5 11 message78 (pack kl78 kr78) (packLane l q))) =
      pairedStep 4 6 11 message79 (pack kl79 kr79)
        (pairedStep 4 5 11 message78 (pack kl78 kr78) (packLane l q)) := by
  let t := rawStep 5 11 message78 (pack kl78 kr78) (packLane l q)
  have hsum : normalize (pairedSum 4 (packLane l q).a (packLane l q).b
      (packLane l q).c (packLane l q).d message78 (pack kl78 kr78)) =
      pairedSum 4 (packLane l q).a (packLane l q).b
      (packLane l q).c (packLane l q).d message78 (pack kl78 kr78) := by
    simp only [pairedSum, ← normalize_eq_and, normalize_idem]
  have hb : t.b.getLsbD 48 = false := by
    change (rawRotate _ 5 11 + pack l.e q.e).getLsbD 48 = false
    rw [← hsum]
    change (rawRotate (pack _ _) 5 11 + pack l.e q.e).getLsbD 48 = false
    simp only [rawRotate, show (5 : Nat) ≠ 11 by decide, if_false,
      show ¬ (11 : Nat) < 5 by decide]
    rw [BitVec.add_comm]
    exact scaled78_add_gap _ _ _ _
  have hd : t.d.getLsbD 48 = false := c10_gap l.c q.c
  have hc : normalize t.c = t.c := normalize_pack l.b q.b
  have he : normalize t.e = t.e := normalize_pack l.d q.d
  have hs : (pack kl79 kr79 + (message79 + t.a)).toNat % 2 ^ 80 < 2 ^ 47 :=
    three_small _ _ _ (clean_low _ (normalize_pack _ _))
      (message_low message79 wl79 wr79 hm79) (clean_low _ (normalize_pack l.e q.e))
  rw [normalize_raw79_maskBD t message79 (pack kl79 kr79) hc he hb hd hs]
  rw [show maskBD t = pairedStep 4 5 11 message78 (pack kl78 kr78) (packLane l q) from
    maskBD_rawStep 5 11 message78 (pack kl78 kr78) (packLane l q)]

#print axioms maskBD_rawStep
#print axioms sum4_maskBD
#print axioms normalize_raw79_maskBD
#print axioms last_two_normalized
end Challenge.Ripemd160.Submission.Proofs.Bytecode.Paired80FinalPair
