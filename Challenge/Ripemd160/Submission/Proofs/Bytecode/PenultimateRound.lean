import Challenge.Ripemd160.Submission.Proofs.Bytecode.PenultimateCarry
import Challenge.Ripemd160.Submission.Proofs.Bytecode.TerminalRound

set_option warningAsError true
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 600000
set_option maxRecDepth 50000

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.PenultimateRound
open EvmSemantics
open PenultimateCarry
open Challenge.Ripemd160.Submission.Proofs.Bytecode
open PairedLaneCore PairedLaneProduct PairedLaneScaledRotate PairedLaneUInt256Bridge
open PairedHelperBooleanTrace PairedAllInlineCoreTrace

def Normal (x : UInt256) : Prop := normalize (bits x) = bits x

theorem normal_gap (x : UInt256) (hx : Normal x) : (bits x).getLsbD 64 = false := by
  rw [← hx]
  exact normalize_gap _

theorem pair_bits : bits _root_.Challenge.Ripemd160.Submission.Proofs.Bytecode.PairedStartupTrace.pairWord = pairMask := by decide

theorem lower_bits : bits _root_.Challenge.Ripemd160.Submission.Proofs.Bytecode.PairedStartupTrace.lowerWord = PairedLaneBoolean.lowerMask := by decide

theorem upper_bits : bits _root_.Challenge.Ripemd160.Submission.Proofs.Bytecode.PairedStartupTrace.upperWord = PairedLaneBoolean.upperMask := by decide

theorem normal_inlineSum (q : Frame) (v : UInt256) (hp : q.pair = _root_.Challenge.Ripemd160.Submission.Proofs.Bytecode.PairedStartupTrace.pairWord) :
    Normal (inlineSum q v) := by
  unfold Normal inlineSum
  simp only [hp, bits_land, pair_bits]
  rw [BitVec.and_comm pairMask, ← normalize_eq_and, normalize_idem]

def rawT78 (memory : ByteArray) (q : Frame) : UInt256 :=
  UInt256.add q.e (scaledRotation (PairedAllInlineCoreTrace.inline78Frame memory q) q.upper
    (UInt256.ofNat 63) (UInt256.ofNat 27) (inline4Boolean q))

theorem rawT78_gap (memory : ByteArray) (q : Frame)
    (hp : q.pair = _root_.Challenge.Ripemd160.Submission.Proofs.Bytecode.PairedStartupTrace.pairWord) (hu : q.upper = _root_.Challenge.Ripemd160.Submission.Proofs.Bytecode.PairedStartupTrace.upperWord)
    (hf : q.factor = PairedLaneWordRotate.factorWord) (he : Normal q.e) :
    (bits (rawT78 memory q)).getLsbD 64 = false := by
  let v := bits (inlineSum (PairedAllInlineCoreTrace.inline78Frame memory q) (inline4Boolean q))
  have hv : v = pack (low v) (high v) :=
    (normal_inlineSum (PairedAllInlineCoreTrace.inline78Frame memory q) (inline4Boolean q) hp).symm
  have hb : bits (scaledRotation (PairedAllInlineCoreTrace.inline78Frame memory q) q.upper
      (UInt256.ofNat 63) (UInt256.ofNat 27) (inline4Boolean q)) =
      (scaleHigh v 6 * factor) >>> 27 := by
    simp only [scaledRotation, bits_shr _ 27 (by decide), bits_mul, bits_add,
      bits_land, bits_ofNat, hu, upper_bits]
    rw [show bits (PairedAllInlineCoreTrace.inline78Frame memory q).factor = factor from congrArg bits hf]
    change (factor * ((63#256) * (PairedLaneBoolean.upperMask &&& v) + v)) >>> 27 = _
    unfold scaleHigh
    rw [BitVec.mul_comm factor]
    rfl
  unfold rawT78
  rw [bits_add, hb, hv, ← he]
  exact (by simpa only [BitVec.add_comm, normalize] using
    raw78_added_gap (low v) (high v) (low (bits q.e)) (high (bits q.e)))

theorem rawC10_gap (q : Frame) (hf : q.factor = PairedLaneWordRotate.factorWord)
    (hc : Normal q.c) : (bits (TerminalRound.modifiedC10 q)).getLsbD 64 = false := by
  unfold TerminalRound.modifiedC10
  rw [bits_shr _ 22 (by decide), bits_mul, hf]
  change ((factor * bits q.c) >>> 22).getLsbD 64 = false
  rw [BitVec.mul_comm factor, ← hc]
  exact raw_c10_gap _ _

theorem masked_three_add_eq (x y a m k : UInt256)
    (hx : (bits x).getLsbD 64 = false) (hy : (bits y).getLsbD 64 = false)
    (hxy : normalize (bits x) = normalize (bits y))
    (ha : Normal a) (hm : Normal m) (hk : Normal k) :
    UInt256.land _root_.Challenge.Ripemd160.Submission.Proofs.Bytecode.PairedStartupTrace.pairWord (UInt256.add k (UInt256.add m (UInt256.add x a))) =
      UInt256.land _root_.Challenge.Ripemd160.Submission.Proofs.Bytecode.PairedStartupTrace.pairWord (UInt256.add k (UInt256.add m (UInt256.add y a))) := by
  apply bits_injective
  simp only [bits_land, bits_add, pair_bits]
  rw [BitVec.and_comm pairMask, BitVec.and_comm pairMask, ← normalize_eq_and,
    ← normalize_eq_and]
  have h := normalize_three_add_congr (bits x) (bits y)
    (low (bits a)) (high (bits a)) (low (bits m)) (high (bits m))
    (low (bits k)) (high (bits k)) hx hy hxy
  change normalize (((bits x + normalize (bits a)) + normalize (bits m)) + normalize (bits k)) =
    normalize (((bits y + normalize (bits a)) + normalize (bits m)) + normalize (bits k)) at h
  rw [ha, hm, hk] at h
  convert h using 1 <;> congr 1 <;> ac_rfl

#print axioms normal_inlineSum
#print axioms rawT78_gap
#print axioms rawC10_gap
#print axioms masked_three_add_eq

def maskBD (q : Frame) : Frame :=
  {q with
    b := UInt256.land _root_.Challenge.Ripemd160.Submission.Proofs.Bytecode.PairedStartupTrace.pairWord q.b
    d := UInt256.land _root_.Challenge.Ripemd160.Submission.Proofs.Bytecode.PairedStartupTrace.pairWord q.d}

theorem maskBD_bits_b (q : Frame) : bits (maskBD q).b = normalize (bits q.b) := by
  simp only [maskBD, bits_land, pair_bits]
  rw [BitVec.and_comm, ← normalize_eq_and]

theorem maskBD_bits_d (q : Frame) : bits (maskBD q).d = normalize (bits q.d) := by
  simp only [maskBD, bits_land, pair_bits]
  rw [BitVec.and_comm, ← normalize_eq_and]

theorem inline4_bits (q : Frame) (hl : q.lower = _root_.Challenge.Ripemd160.Submission.Proofs.Bytecode.PairedStartupTrace.lowerWord) :
    bits (inline4Boolean q) = boolean4 (bits q.b) (bits q.c) (bits q.d) := by
  simp only [inline4Boolean, bits_xor, bits_land, bits_lor, bits_lnot, hl, lower_bits]
  rfl

theorem inline4_maskBD (q : Frame) (hl : q.lower = _root_.Challenge.Ripemd160.Submission.Proofs.Bytecode.PairedStartupTrace.lowerWord) :
    normalize (bits (inline4Boolean q)) = normalize (bits (inline4Boolean (maskBD q))) := by
  rw [inline4_bits q hl, inline4_bits (maskBD q) hl, maskBD_bits_b, maskBD_bits_d]
  exact boolean4_normalize_bd _ _ _

theorem inlineSum_maskBD (q : Frame) (hp : q.pair = _root_.Challenge.Ripemd160.Submission.Proofs.Bytecode.PairedStartupTrace.pairWord)
    (hl : q.lower = _root_.Challenge.Ripemd160.Submission.Proofs.Bytecode.PairedStartupTrace.lowerWord)
    (ha : Normal q.a) (hm : Normal q.message0) (hk : Normal q.k)
    (hb : (bits q.b).getLsbD 64 = false) (hc : (bits q.c).getLsbD 64 = false)
    (hd : (bits q.d).getLsbD 64 = false) :
    inlineSum q (inline4Boolean q) = inlineSum (maskBD q) (inline4Boolean (maskBD q)) := by
  have hg : (bits (inline4Boolean q)).getLsbD 64 = false := by
    rw [inline4_bits q hl]; exact boolean4_gap _ _ _ hb hc hd
  have hg' : (bits (inline4Boolean (maskBD q))).getLsbD 64 = false := by
    rw [inline4_bits (maskBD q) hl, maskBD_bits_b, maskBD_bits_d]
    exact boolean4_gap _ _ _ (normalize_gap _) hc (normalize_gap _)
  simpa only [inlineSum, maskBD, hp] using
    masked_three_add_eq (inline4Boolean q) (inline4Boolean (maskBD q))
      q.a q.message0 q.k hg hg' (inline4_maskBD q hl) ha hm hk

#print axioms maskBD_bits_b
#print axioms inline4_maskBD
#print axioms inlineSum_maskBD
end Challenge.Ripemd160.Submission.Proofs.Bytecode.PenultimateRound

