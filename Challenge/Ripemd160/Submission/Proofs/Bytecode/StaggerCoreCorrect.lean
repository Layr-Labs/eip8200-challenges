import Challenge.Ripemd160.Submission.Proofs.Bytecode.StaggerScalarLow54
import Challenge.Ripemd160.Submission.Proofs.Bytecode.StaggerRepresentation
import Challenge.Ripemd160.Submission.Proofs.Bytecode.StaggerMessage
set_option warningAsError true
set_option maxRecDepth 10000
set_option linter.unusedSimpArgs false
namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.StaggerCoreCorrect
open EvmSemantics EvmSemantics.EVM
open Paired144WordRound (packCrypto)
open Paired80Compression (low32 unpackLeft)
open Paired80CryptoBridge (CryptoLane cryptoStep)
open Paired80Algorithm (leftFold rightFold)
open StaggerCoreModel StaggerRepresentation
open StaggerScalarWord (embed unpackLeft_packCrypto)

/-! ### Unmasked right-lane prologue

`right0/1/2` no longer re-mask the rotated `.d` field (`maskD = false`).  The
prologue result is therefore only equal to `embed (rightFold words 3 q)` on the
low 32 bits of every field (`.b`/`.c` stay exactly clean).  After `pair` the
extra bits sit at positions `≥ 176`, above both packed lanes, and the packed
round only ever reads the low 176 bits of `.a/.d/.e`, so three packed rounds
already coincide with the clean trajectory. -/

section PrologueNear
open PairedLaneUInt256Bridge

/-- Agreement on the low 176 bits (both packed lanes and the spacer between them). -/
def Near (x y : UInt256) : Prop := (bits x).setWidth 176 = (bits y).setWidth 176

theorem near_refl (x : UInt256) : Near x x := rfl

theorem near_of_eq {x y : UInt256} (h : x = y) : Near x y := h ▸ near_refl x

theorem near_getLsbD {x y : UInt256} (h : Near x y) (i : Nat) (hi : i < 176) :
    (bits x).getLsbD i = (bits y).getLsbD i := by
  have hx := congrArg (fun z : BitVec 176 => z.getLsbD i) h
  simpa only [BitVec.getLsbD_setWidth, hi, decide_true, Bool.true_and] using hx

theorem near_of_getLsbD {x y : UInt256}
    (h : ∀ i, i < 176 → (bits x).getLsbD i = (bits y).getLsbD i) : Near x y := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_setWidth, hi, decide_true, Bool.true_and]
  exact h i (by omega)

theorem near_add {a a' b b' : UInt256} (ha : Near a a') (hb : Near b b') :
    Near (UInt256.add a b) (UInt256.add a' b') := by
  unfold Near at *
  rw [bits_add, bits_add, BitVec.setWidth_add _ _ (by decide),
    BitVec.setWidth_add _ _ (by decide), ha, hb]

theorem near_raw (mode : Nat) (sel b c : UInt256) {d d' : UInt256} (hd : Near d d') :
    Near (StaggerWord.raw mode sel b c d) (StaggerWord.raw mode sel b c d') := by
  apply near_of_getLsbD
  intro i hi
  have h := near_getLsbD hd i hi
  rcases Nat.lt_or_ge mode 8 with hm | hm
  · interval_cases mode <;>
      simp only [StaggerWord.raw, bits_xor, bits_lor, bits_land, bits_lnot,
        BitVec.getLsbD_xor, BitVec.getLsbD_or, BitVec.getLsbD_and, BitVec.getLsbD_not, h]
  · obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_le hm
    simp only [Nat.add_comm 8 n, StaggerWord.raw, bits_xor, bits_lor, bits_land, bits_lnot,
      BitVec.getLsbD_xor, BitVec.getLsbD_or, BitVec.getLsbD_and, BitVec.getLsbD_not, h]

theorem getLsbD_high {m : UInt256} {k : Nat} (hm : (bits m).toNat < 2 ^ k)
    (i : Nat) (hi : k ≤ i) : (bits m).getLsbD i = false :=
  Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hm (Nat.pow_le_pow_right (by decide) hi))

theorem pairWord_lt : (bits Paired144WordRound.pairWord).toNat < 2 ^ 176 := by
  rw [Paired144WordRound.pairWord, bits_word, Paired144Core.pairMask_value]
  decide

theorem compactMask_lt : (bits Paired144WordRound.compactMaskWord).toNat < 2 ^ 104 := by
  rw [Paired144WordRound.compactMaskWord, bits_ofNat, BitVec.toNat_ofNat]
  decide

theorem land_near {m : UInt256} (hm : (bits m).toNat < 2 ^ 176)
    {x y : UInt256} (h : Near x y) : UInt256.land x m = UInt256.land y m := by
  apply bits_injective
  rw [bits_land, bits_land]
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  rw [BitVec.getLsbD_and, BitVec.getLsbD_and]
  by_cases hi' : i < 176
  · rw [near_getLsbD h i hi']
  · rw [getLsbD_high hm i (by omega), Bool.and_false, Bool.and_false]

theorem compact_near {x y : UInt256} (h : Near x y) :
    Paired144WordRound.wordCompact x = Paired144WordRound.wordCompact y := by
  unfold Paired144WordRound.wordCompact
  apply bits_injective
  rw [bits_land, bits_land, bits_lor, bits_lor, bits_shr _ 72 (by decide),
    bits_shr _ 72 (by decide)]
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  rw [BitVec.getLsbD_and, BitVec.getLsbD_and, BitVec.getLsbD_or, BitVec.getLsbD_or,
    BitVec.getLsbD_ushiftRight, BitVec.getLsbD_ushiftRight]
  by_cases hi' : i < 104
  · rw [near_getLsbD h i (by omega), near_getLsbD h (72 + i) (by omega)]
  · rw [getLsbD_high compactMask_lt i (by omega), Bool.and_false, Bool.and_false]

theorem rotate_near (r s : Nat) {x y : UInt256} (h : Near x y) :
    Paired144WordRound.wordRotate x r s = Paired144WordRound.wordRotate y r s := by
  unfold Paired144WordRound.wordRotate
  simp only [compact_near h, land_near pairWord_lt h]

theorem t_near (mode r s : Nat) (message key : UInt256) (q q' : PairedLaneWordRound.WordLane)
    (ha : Near q.a q'.a) (hb : q.b = q'.b) (hc : q.c = q'.c) (hd : Near q.d q'.d)
    (he : Near q.e q'.e) :
    StaggerWord.t mode r s message key q = StaggerWord.t mode r s message key q' := by
  have hs : Near (StaggerWord.sum mode q.a q.b q.c q.d message key)
      (StaggerWord.sum mode q'.a q'.b q'.c q'.d message key) := by
    unfold StaggerWord.sum
    rw [hb, hc]
    exact near_add (near_add (near_add ha (near_raw mode _ _ _ hd)) (near_refl _)) (near_refl _)
  unfold StaggerWord.t
  rw [rotate_near r s hs]
  exact land_near pairWord_lt (near_add (near_refl _) he)

theorem step_congr (mode r s : Nat) (message key : UInt256) (q q' : PairedLaneWordRound.WordLane)
    (ht : StaggerWord.t mode r s message key q = StaggerWord.t mode r s message key q')
    (hb : q.b = q'.b) (hc : q.c = q'.c) (hd : q.d = q'.d) (he : q.e = q'.e) :
    StaggerWord.step mode r s message key q = StaggerWord.step mode r s message key q' := by
  unfold StaggerWord.step
  rw [ht, hb, hc, hd, he]

theorem step3_near (m0 r0 s0 m1 r1 s1 m2 r2 s2 : Nat) (x0 k0 x1 k1 x2 k2 : UInt256)
    (q q' : PairedLaneWordRound.WordLane)
    (ha : Near q.a q'.a) (hb : q.b = q'.b) (hc : q.c = q'.c) (hd : Near q.d q'.d)
    (he : Near q.e q'.e) :
    StaggerWord.step m2 r2 s2 x2 k2 (StaggerWord.step m1 r1 s1 x1 k1
        (StaggerWord.step m0 r0 s0 x0 k0 q)) =
      StaggerWord.step m2 r2 s2 x2 k2 (StaggerWord.step m1 r1 s1 x1 k1
        (StaggerWord.step m0 r0 s0 x0 k0 q')) := by
  have rot : ∀ {u v : UInt256}, u = v →
      UInt256.land (Paired144WordRound.wordShift u 28) Paired144WordRound.pairWord =
        UInt256.land (Paired144WordRound.wordShift v 28) Paired144WordRound.pairWord := by
    intro u v h
    rw [h]
  have t0 := t_near m0 r0 s0 x0 k0 q q' ha hb hc hd he
  have t1 := t_near m1 r1 s1 x1 k1 (StaggerWord.step m0 r0 s0 x0 k0 q)
    (StaggerWord.step m0 r0 s0 x0 k0 q') he t0 hb (near_of_eq (rot hc)) hd
  have t2 := t_near m2 r2 s2 x2 k2
    (StaggerWord.step m1 r1 s1 x1 k1 (StaggerWord.step m0 r0 s0 x0 k0 q))
    (StaggerWord.step m1 r1 s1 x1 k1 (StaggerWord.step m0 r0 s0 x0 k0 q'))
    hd t1 t0 (near_of_eq (rot hb)) (near_of_eq (rot hc))
  exact step_congr m2 r2 s2 x2 k2 _ _ t2 t1 t0 (rot hb) (rot hc)

theorem fold_near3 (msg : Nat → UInt256) (q q' : PairedLaneWordRound.WordLane)
    (ha : Near q.a q'.a) (hb : q.b = q'.b) (hc : q.c = q'.c) (hd : Near q.d q'.d)
    (he : Near q.e q'.e) :
    StaggerAlgorithm.fold msg 3 q = StaggerAlgorithm.fold msg 3 q' := by
  change StaggerAlgorithm.step 2 (msg 2) (StaggerAlgorithm.step 1 (msg 1)
      (StaggerAlgorithm.step 0 (msg 0) q)) =
    StaggerAlgorithm.step 2 (msg 2) (StaggerAlgorithm.step 1 (msg 1)
      (StaggerAlgorithm.step 0 (msg 0) q'))
  unfold StaggerAlgorithm.step
  exact step3_near _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ q q' ha hb hc hd he

theorem fold_congr (msg : Nat → UInt256) {q q' : PairedLaneWordRound.WordLane}
    (h : StaggerAlgorithm.fold msg 3 q = StaggerAlgorithm.fold msg 3 q') (k : Nat) :
    StaggerAlgorithm.fold msg (k + 3) q = StaggerAlgorithm.fold msg (k + 3) q' := by
  induction k with
  | zero => exact h
  | succ k ih =>
    rw [show k + 1 + 3 = (k + 3) + 1 by omega]
    exact congrArg (StaggerAlgorithm.step (k + 3) (msg (k + 3))) ih

theorem low_getLsbD {x y : UInt256} (h : Paired144Core.low (bits x) = Paired144Core.low (bits y))
    (j : Nat) (hj : j < 32) : (bits x).getLsbD j = (bits y).getLsbD j := by
  have hx := congrArg (fun z : BitVec 32 => z.getLsbD j) h
  simpa only [Paired144Core.low, BitVec.getLsbD_extractLsb', hj, decide_true, Bool.true_and,
    Nat.zero_add] using hx

theorem pairWord_near (l : UInt256) {x y : UInt256}
    (h : Paired144Core.low (bits x) = Paired144Core.low (bits y)) :
    Near (StaggerCoreModel.pairWord l x) (StaggerCoreModel.pairWord l y) := by
  apply near_of_getLsbD
  intro i hi
  rw [StaggerCoreModel.pairWord, StaggerCoreModel.pairWord, bits_lor, bits_lor,
    bits_shl _ 144 (by decide), bits_shl _ 144 (by decide), BitVec.getLsbD_or, BitVec.getLsbD_or,
    BitVec.getLsbD_shiftLeft, BitVec.getLsbD_shiftLeft]
  by_cases h144 : i < 144
  · simp [h144]
  · rw [low_getLsbD h (i - 144) (by omega)]

theorem low_of_unpackLeft {x y : PairedLaneWordRound.WordLane} (h : unpackLeft x = unpackLeft y) :
    Paired144Core.low (bits x.a) = Paired144Core.low (bits y.a) ∧
    Paired144Core.low (bits x.b) = Paired144Core.low (bits y.b) ∧
    Paired144Core.low (bits x.c) = Paired144Core.low (bits y.c) ∧
    Paired144Core.low (bits x.d) = Paired144Core.low (bits y.d) ∧
    Paired144Core.low (bits x.e) = Paired144Core.low (bits y.e) :=
  ⟨congrArg (fun z : CryptoLane => z.a.toBitVec) h, congrArg (fun z : CryptoLane => z.b.toBitVec) h,
    congrArg (fun z : CryptoLane => z.c.toBitVec) h, congrArg (fun z : CryptoLane => z.d.toBitVec) h,
    congrArg (fun z : CryptoLane => z.e.toBitVec) h⟩

theorem clean_low_eq {x y : UInt256} (hx : StaggerScalarWord.mask x = x)
    (hy : StaggerScalarWord.mask y = y)
    (h : Paired144Core.low (bits x) = Paired144Core.low (bits y)) : x = y := by
  rw [← hx, ← hy]
  apply bits_injective
  rw [StaggerScalarWord.bits_mask, StaggerScalarWord.bits_mask, StaggerScalar.mask_eq,
    StaggerScalar.mask_eq, h]

end PrologueNear

theorem prologue_unpack (memory : ByteArray) (words : Nat → UInt32) (q : CryptoLane)
    (hm : StaggerMessage.Ready memory words) :
    unpackLeft (prologue memory (embed q)) = rightFold words 3 q := by
  have hm0 : low32 (MachineState.readWord memory 90) = words 5 := hm.scalar 5 (by decide)
  have hm1 : low32 (MachineState.readWord memory 558) = words 14 := hm.scalar 31 (by decide)
  have hm2 : low32 (MachineState.readWord memory 630) = words 7 := hm.scalar 35 (by decide)
  have hpacked := StaggerScalarLow54.packCrypto_low54 q ⟨0,0,0,0,0⟩
  have h1 : StaggerScalarLow54.Low54
      (PairedLaneUInt256Bridge.bits (right0 memory (embed q)).c) := hpacked.2.1
  have h2 : StaggerScalarLow54.Low54
      (PairedLaneUInt256Bridge.bits (right1 memory (right0 memory (embed q))).c) :=
    StaggerScalarLow54.clean_low54 _
      (StaggerScalarWord.step_b_clean false 4 8 (MachineState.readWord memory 90)
        (UInt256.ofNat 1352829926) (embed q))
  have p0 := StaggerScalarLow54.project_step true false 4 8 (by decide) (by decide)
    (MachineState.readWord memory 90) (UInt256.ofNat 1352829926) (embed q) hpacked.2.2.1
  have p1 := StaggerScalarLow54.project_step true false 4 9 (by decide) (by decide)
    (MachineState.readWord memory 558) (UInt256.ofNat 1352829926) (right0 memory (embed q)) h1
  have p2 := StaggerScalarLow54.project_step true false 4 9 (by decide) (by decide)
    (MachineState.readWord memory 630) (UInt256.ofNat 1352829926)
      (right1 memory (right0 memory (embed q))) h2
  unfold prologue
  change unpackLeft (StaggerScalarWord.step true false 4 9 _ _ _) = _
  rw [p2]
  change cryptoStep _ _ _ _ (unpackLeft (StaggerScalarWord.step true false 4 9 _ _ _)) = _
  rw [p1]
  change cryptoStep _ _ _ _ (cryptoStep _ _ _ _ (unpackLeft (StaggerScalarWord.step true false 4 8 _ _ _))) = _
  rw [p0, hm0, hm1, hm2, show unpackLeft (embed q) = q from unpackLeft_packCrypto _ _]
  rfl

theorem paired_crypto (memory : ByteArray) (words : Nat → UInt32) (q : CryptoLane)
    (hm : StaggerMessage.Ready memory words) :
    paired memory (embed q) = packCrypto (leftFold words 77 q) (rightFold words 80 q) := by
  have hl := low_of_unpackLeft ((prologue_unpack memory words q hm).trans
    (unpackLeft_packCrypto (rightFold words 3 q) ⟨0,0,0,0,0⟩).symm)
  have hclean := StaggerScalarWord.embed_clean (rightFold words 3 q)
  have hb : (prologue memory (embed q)).b = (embed (rightFold words 3 q)).b :=
    clean_low_eq (x := (prologue memory (embed q)).b)
      (StaggerScalarWord.step_b_clean false 4 9 (MachineState.readWord memory 630)
        (UInt256.ofNat 1352829926) (right1 memory (right0 memory (embed q))))
      (clean_b _ hclean) hl.2.1
  have hc : (prologue memory (embed q)).c = (embed (rightFold words 3 q)).c :=
    clean_low_eq (x := (prologue memory (embed q)).c)
      (StaggerScalarWord.step_b_clean false 4 9 (MachineState.readWord memory 558)
        (UInt256.ofNat 1352829926) (right0 memory (embed q)))
      (clean_c _ hclean) hl.2.2.1
  have h3 : StaggerAlgorithm.fold (message memory) 3 (pair (embed q) (prologue memory (embed q))) =
      StaggerAlgorithm.fold (message memory) 3 (pair (embed q) (embed (rightFold words 3 q))) :=
    fold_near3 (message memory) _ _ (pairWord_near _ hl.1)
      (congrArg (StaggerCoreModel.pairWord _) hb) (congrArg (StaggerCoreModel.pairWord _) hc)
      (pairWord_near _ hl.2.2.2.1) (pairWord_near _ hl.2.2.2.2)
  have h77 : StaggerAlgorithm.fold (message memory) 77 (pair (embed q) (prologue memory (embed q))) =
      StaggerAlgorithm.fold (message memory) 77 (pair (embed q) (embed (rightFold words 3 q))) :=
    fold_congr (message memory) h3 74
  rw [paired, h77, pair_embed]
  exact StaggerAlgorithm.fold_crypto (message memory) words 77 (by decide) q q hm.paired

def leftFinish (words : Nat → UInt32) (q : CryptoLane) : CryptoLane :=
  cryptoStep 4 6 (words 13) Crypto.Ripemd160.K[4]!
    (cryptoStep 4 5 (words 15) Crypto.Ripemd160.K[4]!
      (cryptoStep 4 8 (words 6) Crypto.Ripemd160.K[4]! q))

theorem leftFinish_fold (words : Nat → UInt32) (q : CryptoLane) :
    leftFinish words (leftFold words 77 q) = leftFold words 80 q := by rfl

theorem epilogue_crypto (memory : ByteArray) (words : Nat → UInt32) (l r : CryptoLane)
    (hm : StaggerMessage.Ready memory words) :
    unpackLeft (epilogue memory (packCrypto l r)) = leftFinish words l := by
  have hm0 : low32 (MachineState.readWord memory 0) = words 6 := hm.scalar 0 (by decide)
  have hm1 : low32 (MachineState.readWord memory 144) = words 15 := hm.scalar 8 (by decide)
  have hm2 : low32 (MachineState.readWord memory 252) = words 13 := hm.scalar 14 (by decide)
  have hpacked := StaggerScalarLow54.packCrypto_low54 l r
  have h0 := hpacked.2.2.1
  have h1 : StaggerScalarLow54.Low54
      (PairedLaneUInt256Bridge.bits (left77 memory (packCrypto l r)).c) := hpacked.2.1
  have h2 : StaggerScalarLow54.Low54
      (PairedLaneUInt256Bridge.bits (left78 memory (left77 memory (packCrypto l r))).c) :=
    StaggerScalarLow54.clean_low54 _
      (StaggerScalarWord.step_b_clean false 4 8 (MachineState.readWord memory 0)
        (UInt256.ofNat 2840853838) (packCrypto l r))
  have p0 := StaggerScalarLow54.project_step true false 4 8 (by decide) (by decide)
    (MachineState.readWord memory 0) (UInt256.ofNat 2840853838) (packCrypto l r) h0
  have p1 := StaggerScalarLow54.project_step false false 4 5 (by decide) (by decide)
    (MachineState.readWord memory 144) (UInt256.ofNat 2840853838) (left77 memory (packCrypto l r)) h1
  have p2 := StaggerScalarLow54.project_step false false 4 6 (by decide) (by decide)
    (MachineState.readWord memory 252) (UInt256.ofNat 2840853838)
      (left78 memory (left77 memory (packCrypto l r))) h2
  unfold epilogue
  rw [left_packCrypto]
  change unpackLeft (StaggerScalarWord.step false false 4 6 _ _ _) = _
  rw [p2]
  change cryptoStep _ _ _ _ (unpackLeft (StaggerScalarWord.step false false 4 5 _ _ _)) = _
  rw [p1]
  change cryptoStep _ _ _ _ (cryptoStep _ _ _ _ (unpackLeft (StaggerScalarWord.step true false 4 8 _ _ _))) = _
  rw [p0, hm0, hm1, hm2, show unpackLeft (packCrypto l r) = l from unpackLeft_packCrypto _ _]
  rfl

#print axioms prologue_unpack
#print axioms fold_near3
#print axioms paired_crypto
#print axioms epilogue_crypto
end Challenge.Ripemd160.Submission.Proofs.Bytecode.StaggerCoreCorrect
