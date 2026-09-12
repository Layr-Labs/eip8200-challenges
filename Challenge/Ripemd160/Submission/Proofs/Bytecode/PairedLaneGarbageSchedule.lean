import Challenge.Ripemd160.Submission.Proofs.Bytecode.PairedLaneGarbage
import Challenge.Ripemd160.Submission.Proofs.Bytecode.PairedHelperBooleanTrace
import Challenge.Ripemd160.Submission.Proofs.Bytecode.PairedAllInlineCoreTrace
import Challenge.Ripemd160.Submission.Proofs.Bytecode.PairedScheduleLift
import Challenge.Ripemd160.Submission.Proofs.Bytecode.PairedMask32Cache
import Challenge.Ripemd160.Submission.Proofs.Bytecode.PairedLaneWordGroupTwoHoist

set_option warningAsError true

/-!
The schedule may leave spacer garbage in its cells.

`NormalizedScheduleReady` states the two reads of each message cell
exactly. The extraction masks that make it exact are redundant at
runtime, so this module states the weaker predicate the unmasked
schedule satisfies and rebuilds `algorithmMessage` from it in the
additive form `PairedLaneGarbage` consumes.

Both conjuncts have to be stated, not derived one from the other: the
`208 + 32 i` read is not a store at all, it is a misaligned re-read of
the same bytes (its high half is the cell's low half, its low half is
the top of the next cell), so garbage in one cell shows up in two
different bit positions.
-/
namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.PairedHelperBooleanTrace

open EvmSemantics EvmSemantics.EVM
open PairedLaneCore PairedLaneUInt256Bridge

/-- `lor` of two disjoint halves is addition.

`Nat.two_pow_add_eq_or_of_lt` is the same bridge the compiler package
uses for byte assembly; here the split is at bit 128. -/
theorem lor_high_low (high low : Nat) (hhigh : high < 2 ^ 128)
    (hlow : low < 2 ^ 128) :
    UInt256.lor (UInt256.ofNat (high * 2 ^ 128)) (UInt256.ofNat low) =
      UInt256.ofNat (high * 2 ^ 128 + low) := by
  have hpow : 2 ^ 128 * 2 ^ 128 = 2 ^ 256 := by
    rw [← Nat.pow_add]
  have hstep : (high + 1) * 2 ^ 128 = high * 2 ^ 128 + 2 ^ 128 := by
    rw [Nat.succ_mul]
  have hbound : (high + 1) * 2 ^ 128 ≤ 2 ^ 256 := by
    calc (high + 1) * 2 ^ 128 ≤ 2 ^ 128 * 2 ^ 128 :=
          Nat.mul_le_mul_right _ (Nat.succ_le_of_lt hhigh)
      _ = 2 ^ 256 := hpow
  have hsum : high * 2 ^ 128 + low < 2 ^ 256 := by
    calc high * 2 ^ 128 + low < high * 2 ^ 128 + 2 ^ 128 :=
          Nat.add_lt_add_left hlow _
      _ = (high + 1) * 2 ^ 128 := hstep.symm
      _ ≤ 2 ^ 256 := hbound
  have hmul : high * 2 ^ 128 < 2 ^ 256 :=
    Nat.lt_of_le_of_lt (Nat.le_add_right _ low) hsum
  have hlow256 : low < 2 ^ 256 :=
    Nat.lt_of_lt_of_le hlow (Nat.pow_le_pow_right (by decide) (by decide))
  apply bits_injective
  rw [bits_lor, bits_ofNat, bits_ofNat, bits_ofNat]
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_or, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hmul,
    Nat.mod_eq_of_lt hlow256, Nat.mod_eq_of_lt hsum]
  rw [Nat.mul_comm high (2 ^ 128)]
  exact (Nat.two_pow_add_eq_or_of_lt hlow high).symm

#print axioms lor_high_low

/-- The schedule cells as the unmasked prologue leaves them.

`g i` is whatever the extraction left above the word: a multiple of
`2 ^ 32` below `2 ^ 96`. `NormalizedScheduleReady` is the `g = 0`
instance, so nothing here special-cases which cells carry garbage - the
four unmasked sites are just the indices where `g i` happens to be
non-zero.

Both reads are stated because the second is not a store: it re-reads the
same bytes from 16 bytes lower, which lifts the cell's low 128 bits into
the high half. -/
def GarbageScheduleReady (memory : ByteArray) (words : Nat → UInt32)
    (g : Nat → Nat) : Prop :=
  (∀ i < 16, g i % 2 ^ 32 = 0 ∧ g i < 2 ^ 96) ∧
  (∀ i < 16, MachineState.readWord memory (32 * ScheduleLayout.perm i) =
    UInt256.ofNat ((words i).toNat + g i)) ∧
  (∀ i < 16, MachineState.readWord memory (32 * ScheduleLayout.perm i + 16) =
    UInt256.shiftLeft (UInt256.ofNat ((words i).toNat + g i))
      (UInt256.ofNat 128))

/-- The exact schedule is the zero-garbage instance. -/
theorem garbageScheduleReady_of_normalized (memory : ByteArray)
    (words : Nat → UInt32) (hready : NormalizedScheduleReady memory words) :
    GarbageScheduleReady memory words (fun _ => 0) := by
  refine ⟨fun i _ => ⟨rfl, Nat.two_pow_pos 96⟩, fun i hi => ?_, fun i hi => ?_⟩
  · simpa only [Nat.add_zero] using hready.1 i hi
  · simpa only [Nat.add_zero] using hready.2 i hi

#print axioms garbageScheduleReady_of_normalized

/-- Shifting a value that fits the low half into the high half. -/
theorem shl128_ofNat (x : Nat) (hx : x < 2 ^ 128) :
    UInt256.shiftLeft (UInt256.ofNat x) (UInt256.ofNat 128) =
      UInt256.ofNat (x * 2 ^ 128) := by
  have hpow : 2 ^ 128 * 2 ^ 128 = 2 ^ 256 := by rw [← Nat.pow_add]
  have hstep : (x + 1) * 2 ^ 128 = x * 2 ^ 128 + 2 ^ 128 := by rw [Nat.succ_mul]
  have hbound : (x + 1) * 2 ^ 128 ≤ 2 ^ 256 := by
    calc (x + 1) * 2 ^ 128 ≤ 2 ^ 128 * 2 ^ 128 :=
          Nat.mul_le_mul_right _ (Nat.succ_le_of_lt hx)
      _ = 2 ^ 256 := hpow
  have hmul : x * 2 ^ 128 < 2 ^ 256 := by
    calc x * 2 ^ 128 < x * 2 ^ 128 + 2 ^ 128 :=
          Nat.lt_add_of_pos_right (Nat.two_pow_pos 128)
      _ = (x + 1) * 2 ^ 128 := hstep.symm
      _ ≤ 2 ^ 256 := hbound
  have hx256 : x < 2 ^ 256 :=
    Nat.lt_of_lt_of_le hx (Nat.pow_le_pow_right (by decide) (by decide))
  apply bits_injective
  rw [bits_shl _ 128 (by decide), bits_ofNat, bits_ofNat]
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, Nat.shiftLeft_eq,
    Nat.mod_eq_of_lt hmul, Nat.mod_eq_of_lt hx256]

/-- `algorithmMessage` under a garbage-carrying schedule. -/
theorem algorithmMessage_of_garbage (memory : ByteArray) (words : Nat → UInt32)
    (g : Nat → Nat) (hready : GarbageScheduleReady memory words g)
    (i : Nat) (hi : i < 80) :
    algorithmMessage memory i =
      UInt256.ofNat
        (((words Crypto.Ripemd160.rP[i]!).toNat + g Crypto.Ripemd160.rP[i]!)
            * 2 ^ 128
          + ((words Crypto.Ripemd160.r[i]!).toNat
              + g Crypto.Ripemd160.r[i]!)) := by
  obtain ⟨hbound, hlow, hhigh⟩ := hready
  have hb := algorithmIndex_bounds ⟨i, hi⟩
  have hglo := hbound _ hb.1
  have hghi := hbound _ hb.2
  have hlt (c : Nat) (hc : g c < 2 ^ 96) (w : UInt32) :
      w.toNat + g c < 2 ^ 128 := by
    have hw : w.toNat < 2 ^ 32 := w.toNat_lt_size
    calc w.toNat + g c < 2 ^ 32 + 2 ^ 96 := Nat.add_lt_add hw hc
      _ < 2 ^ 128 := by decide
  unfold algorithmMessage
  rw [hhigh _ hb.2, hlow _ hb.1,
    shl128_ofNat _ (hlt _ hghi.2 _),
    lor_high_low _ _ (hlt _ hghi.2 _) (hlt _ hglo.2 _)]

#print axioms shl128_ofNat
#print axioms algorithmMessage_of_garbage

set_option maxRecDepth 8000 in
/-- The additive form the fold consumes: the low lane's garbage stays in
place and the high lane's garbage, a multiple of `2^32`, lands at `2^160`. -/
theorem algorithmMessage_of_garbage_add (memory : ByteArray) (words : Nat → UInt32)
    (g : Nat → Nat) (hready : GarbageScheduleReady memory words g)
    (i : Nat) (hi : i < 80) :
    algorithmMessage memory i =
      UInt256.add
        (packed32 (words Crypto.Ripemd160.r[i]!) (words Crypto.Ripemd160.rP[i]!))
        (UInt256.ofNat (g Crypto.Ripemd160.r[i]!
          + (g Crypto.Ripemd160.rP[i]! / 2 ^ 32) * 2 ^ 160)) := by
  have hb := algorithmIndex_bounds ⟨i, hi⟩
  have hlo := hready.1 Crypto.Ripemd160.r[i]! hb.1
  have hhi := hready.1 Crypto.Ripemd160.rP[i]! hb.2
  have hdiv : (g Crypto.Ripemd160.rP[i]! / 2 ^ 32) * 2 ^ 32 =
      g Crypto.Ripemd160.rP[i]! :=
    Nat.div_mul_cancel (Nat.dvd_of_mod_eq_zero hhi.1)
  have hwlo : (words Crypto.Ripemd160.r[i]!).toNat < 2 ^ 32 :=
    (words Crypto.Ripemd160.r[i]!).toNat_lt_size
  have hwhi : (words Crypto.Ripemd160.rP[i]!).toNat < 2 ^ 32 :=
    (words Crypto.Ripemd160.rP[i]!).toNat_lt_size
  rw [algorithmMessage_of_garbage memory words g hready i hi, packed32_eq_or,
    shl128_ofNat _ (by omega), lor_high_low _ _ (by omega) (by omega)]
  show _ = UInt256.ofNat _ + UInt256.ofNat _
  rw [Challenge.EvmProof.Word.ofNat_add_mod]
  have key : ∀ a b c d e P Q : Nat, e * Q = b →
      (a + b) * P + (c + d) = a * P + c + (d + e * (Q * P)) := by
    intro a b c d e P Q h
    subst h
    ring
  have h160 : (2 : Nat) ^ 160 = 2 ^ 32 * 2 ^ 128 := by rw [← Nat.pow_add]
  rw [h160]
  exact congrArg UInt256.ofNat (key _ _ _ _ _ _ _ hdiv)

#print axioms algorithmMessage_of_garbage_add

/-- The whole paired fold ignores per-round spacer garbage.

`garbageLow`/`garbageHigh` are indexed because each round selects a
different pair of schedule cells, so the garbage carried into round `i`
is whatever sits in the cells `r[i]` and `rP[i]`. -/
theorem pairedWordFold_crypto_garbage
    (group leftRotation rightRotation : Nat → Nat)
    (leftMessage rightMessage leftConstant rightConstant : Nat → UInt32)
    (garbageLow garbageHigh : Nat → Nat)
    (count : Nat) (left right : PairedLaneCryptoBridge.CryptoLane)
    (hrotation : ∀ i < count,
      0 < leftRotation i ∧ leftRotation i < 32 ∧
      0 < rightRotation i ∧ rightRotation i < 32)
    (hgarbage : ∀ i < count,
      garbageLow i % 2 ^ 32 = 0 ∧ garbageLow i < 2 ^ 96 ∧
      garbageHigh i < 2 ^ 64) :
    pairedWordFold group leftRotation rightRotation
      (fun i => UInt256.add (packed32 (leftMessage i) (rightMessage i))
        (UInt256.ofNat (garbageLow i + garbageHigh i * 2 ^ 160)))
      (fun i => packed32 (leftConstant i) (rightConstant i))
      count (PairedLaneWordRound.packCrypto left right) =
    PairedLaneWordRound.packCrypto
      (scalarLeftFold group leftRotation leftMessage leftConstant count left)
      (scalarRightFold group rightRotation rightMessage rightConstant count right) := by
  induction count with
  | zero => rfl
  | succ i ih =>
    have hi := ih (fun j hj => hrotation j (by omega))
      (fun j hj => hgarbage j (by omega))
    rw [pairedWordFold, hi]
    rcases hrotation i (by omega) with ⟨hl0, hl, hr0, hr⟩
    rcases hgarbage i (by omega) with ⟨hg32, hglow, hghigh⟩
    exact PairedLaneWordRound.wordStep_of_crypto_garbage
      (group i) (leftRotation i) (rightRotation i) hl0 hl hr0 hr
      (leftMessage i) (rightMessage i) (leftConstant i) (rightConstant i)
      (scalarLeftFold group leftRotation leftMessage leftConstant i left)
      (scalarRightFold group rightRotation rightMessage rightConstant i right)
      (garbageLow i) (garbageHigh i) hg32 hglow hghigh

#print axioms pairedWordFold_crypto_garbage

/-- `algorithmFold_crypto` with per-round spacer garbage in the message.

`pairedWordFold_congr` still does the rewrite: the message equality it
needs is literal, and the additive form supplies exactly that. -/
theorem algorithmFold_crypto_garbage (memory : ByteArray) (words : Nat → UInt32)
    (garbageLow garbageHigh : Nat → Nat)
    (count : Nat) (hcount : count ≤ 80)
    (left right : PairedLaneCryptoBridge.CryptoLane)
    (hgarbage : ∀ i < count,
      garbageLow i % 2 ^ 32 = 0 ∧ garbageLow i < 2 ^ 96 ∧
      garbageHigh i < 2 ^ 64)
    (hmessage : ∀ i < count, algorithmMessage memory i =
      UInt256.add
        (packed32 (words Crypto.Ripemd160.r[i]!) (words Crypto.Ripemd160.rP[i]!))
        (UInt256.ofNat (garbageLow i + garbageHigh i * 2 ^ 160))) :
    algorithmFold memory 0 count (PairedLaneWordRound.packCrypto left right) =
      PairedLaneWordRound.packCrypto
        (scalarLeftFold (fun i => i / 16) (fun i => Crypto.Ripemd160.s[i]!)
          (fun i => words Crypto.Ripemd160.r[i]!)
          (fun i => Crypto.Ripemd160.K[i / 16]!) count left)
        (scalarRightFold (fun i => i / 16) (fun i => Crypto.Ripemd160.sP[i]!)
          (fun i => words Crypto.Ripemd160.rP[i]!)
          (fun i => Crypto.Ripemd160.KP[i / 16]!) count right) := by
  simp only [algorithmFold, Nat.zero_add]
  have hconstant (i : Nat) (hi : i < count) :
      algorithmKey (i / 16) =
        packed32 Crypto.Ripemd160.K[i / 16]! Crypto.Ripemd160.KP[i / 16]! :=
    algorithmKey_packed ⟨i / 16, by omega⟩
  have hrotation (i : Nat) (hi : i < count) :
      0 < Crypto.Ripemd160.s[i]! ∧ Crypto.Ripemd160.s[i]! < 32 ∧
      0 < Crypto.Ripemd160.sP[i]! ∧ Crypto.Ripemd160.sP[i]! < 32 :=
    algorithmRotation_bounds ⟨i, by omega⟩
  have h0 := pairedWordFold_congr
    (fun i => i / 16) (fun i => Crypto.Ripemd160.s[i]!) (fun i => Crypto.Ripemd160.sP[i]!)
    (algorithmMessage memory) (fun i => algorithmKey (i / 16))
    (fun i => UInt256.add
      (packed32 (words Crypto.Ripemd160.r[i]!) (words Crypto.Ripemd160.rP[i]!))
      (UInt256.ofNat (garbageLow i + garbageHigh i * 2 ^ 160)))
    (fun i => packed32 Crypto.Ripemd160.K[i / 16]! Crypto.Ripemd160.KP[i / 16]!)
    count (PairedLaneWordRound.packCrypto left right) hmessage hconstant
  exact h0.trans (pairedWordFold_crypto_garbage
    (fun i => i / 16) (fun i => Crypto.Ripemd160.s[i]!) (fun i => Crypto.Ripemd160.sP[i]!)
    (fun i => words Crypto.Ripemd160.r[i]!) (fun i => words Crypto.Ripemd160.rP[i]!)
    (fun i => Crypto.Ripemd160.K[i / 16]!) (fun i => Crypto.Ripemd160.KP[i / 16]!)
    garbageLow garbageHigh count left right hrotation hgarbage)

#print axioms algorithmFold_crypto_garbage

end Challenge.Ripemd160.Submission.Proofs.Bytecode.PairedHelperBooleanTrace

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.PairedSynthCoreTrace

open EvmSemantics
open PairedLaneCore PairedLaneUInt256Bridge PairedHelperBooleanTrace
open PairedLaneWordGroupTwoHoist PairedLaneWordRound

/-- Group two's hoisted step also ignores the garbage: the equality with
`wordStep` is message-agnostic. -/
theorem rawWordStep2_of_crypto_garbage (r s : Nat)
    (hr0 : 0 < r) (hr : r < 32) (hs0 : 0 < s) (hs : s < 32)
    (wl wr kl kr : UInt32) (l q : PairedLaneCryptoBridge.CryptoLane)
    (low high : Nat) (hlow32 : low % 2 ^ 32 = 0) (hlow : low < 2 ^ 96)
    (hhigh : high < 2 ^ 64) :
    rawWordStep2 r s
        (UInt256.add (word (pack wl.toBitVec wr.toBitVec))
          (UInt256.ofNat (low + high * 2 ^ 160)))
        (adjustedK (word (pack kl.toBitVec kr.toBitVec))) (packCrypto l q) =
      packCrypto (PairedLaneCryptoBridge.cryptoStep 2 r wl kl l)
        (PairedLaneCryptoBridge.cryptoStep 2 s wr kr q) := by
  obtain ⟨hb, hc, hd⟩ := packCrypto_supported l q
  exact (rawWordStep2_eq_of_supported r s
    (UInt256.add (word (pack wl.toBitVec wr.toBitVec))
      (UInt256.ofNat (low + high * 2 ^ 160)))
    (word (pack kl.toBitVec kr.toBitVec)) (packCrypto l q) hb hc hd).trans
      (PairedLaneWordRound.wordStep_of_crypto_garbage 2 r s hr0 hr hs0 hs
        wl wr kl kr l q low high hlow32 hlow hhigh)

theorem hoistedWordStep_of_crypto_garbage (j r t : Nat)
    (hr0 : 0 < r) (hr : r < 32) (ht0 : 0 < t) (ht : t < 32)
    (ml mr kl kr : UInt32) (left right : PairedLaneCryptoBridge.CryptoLane)
    (low high : Nat) (hlow32 : low % 2 ^ 32 = 0) (hlow : low < 2 ^ 96)
    (hhigh : high < 2 ^ 64) :
    hoistedWordStep j r t
        (UInt256.add (packed32 ml mr) (UInt256.ofNat (low + high * 2 ^ 160)))
        (packed32 kl kr) (PairedLaneWordRound.packCrypto left right) =
      PairedLaneWordRound.packCrypto
        (PairedLaneCryptoBridge.cryptoStep j r ml kl left)
        (PairedLaneCryptoBridge.cryptoStep (4 - j) t mr kr right) := by
  by_cases hj : j = 2
  · subst j
    simp only [hoistedWordStep]
    exact rawWordStep2_of_crypto_garbage r t hr0 hr ht0 ht ml mr kl kr left right
      low high hlow32 hlow hhigh
  · simp only [hoistedWordStep, if_neg hj]
    exact PairedLaneWordRound.wordStep_of_crypto_garbage j r t hr0 hr ht0 ht
      ml mr kl kr left right low high hlow32 hlow hhigh

theorem hoistedWordFold_crypto_garbage
    (group leftRotation rightRotation : Nat → Nat)
    (leftMessage rightMessage leftConstant rightConstant : Nat → UInt32)
    (garbageLow garbageHigh : Nat → Nat)
    (count : Nat) (left right : PairedLaneCryptoBridge.CryptoLane)
    (hrotation : ∀ i < count,
      0 < leftRotation i ∧ leftRotation i < 32 ∧
      0 < rightRotation i ∧ rightRotation i < 32)
    (hgarbage : ∀ i < count,
      garbageLow i % 2 ^ 32 = 0 ∧ garbageLow i < 2 ^ 96 ∧
      garbageHigh i < 2 ^ 64) :
    hoistedWordFold group leftRotation rightRotation
        (fun i => UInt256.add (packed32 (leftMessage i) (rightMessage i))
          (UInt256.ofNat (garbageLow i + garbageHigh i * 2 ^ 160)))
        (fun i => packed32 (leftConstant i) (rightConstant i)) count
        (PairedLaneWordRound.packCrypto left right) =
      PairedLaneWordRound.packCrypto
        (scalarLeftFold group leftRotation leftMessage leftConstant count left)
        (scalarRightFold group rightRotation rightMessage rightConstant count right) := by
  induction count with
  | zero => rfl
  | succ i ih =>
    have hprev := ih (fun n hn => hrotation n (by omega))
      (fun n hn => hgarbage n (by omega))
    obtain ⟨hr0, hr, ht0, ht⟩ := hrotation i (by omega)
    obtain ⟨hg32, hglow, hghigh⟩ := hgarbage i (by omega)
    exact (congrArg
      (hoistedWordStep (group i) (leftRotation i) (rightRotation i)
        (UInt256.add (packed32 (leftMessage i) (rightMessage i))
          (UInt256.ofNat (garbageLow i + garbageHigh i * 2 ^ 160)))
        (packed32 (leftConstant i) (rightConstant i))) hprev).trans
      (hoistedWordStep_of_crypto_garbage (group i) (leftRotation i) (rightRotation i)
        hr0 hr ht0 ht (leftMessage i) (rightMessage i) (leftConstant i) (rightConstant i)
        (scalarLeftFold group leftRotation leftMessage leftConstant i left)
        (scalarRightFold group rightRotation rightMessage rightConstant i right)
        (garbageLow i) (garbageHigh i) hg32 hglow hghigh)

#print axioms rawWordStep2_of_crypto_garbage
#print axioms hoistedWordStep_of_crypto_garbage
#print axioms hoistedWordFold_crypto_garbage

/-- `hoistedAlgorithmFold_crypto` with per-round spacer garbage. -/
theorem hoistedAlgorithmFold_crypto_garbage (memory : ByteArray)
    (words : Nat → UInt32) (garbageLow garbageHigh : Nat → Nat)
    (count : Nat) (hcount : count ≤ 80)
    (left right : PairedLaneCryptoBridge.CryptoLane)
    (hgarbage : ∀ i < count,
      garbageLow i % 2 ^ 32 = 0 ∧ garbageLow i < 2 ^ 96 ∧
      garbageHigh i < 2 ^ 64)
    (hmessage : ∀ i < count, algorithmMessage memory i =
      UInt256.add
        (packed32 (words Crypto.Ripemd160.r[i]!) (words Crypto.Ripemd160.rP[i]!))
        (UInt256.ofNat (garbageLow i + garbageHigh i * 2 ^ 160))) :
    hoistedAlgorithmFold memory 0 count (PairedLaneWordRound.packCrypto left right) =
      PairedLaneWordRound.packCrypto
        (scalarLeftFold (fun i => i / 16) (fun i => Crypto.Ripemd160.s[i]!)
          (fun i => words Crypto.Ripemd160.r[i]!)
          (fun i => Crypto.Ripemd160.K[i / 16]!) count left)
        (scalarRightFold (fun i => i / 16) (fun i => Crypto.Ripemd160.sP[i]!)
          (fun i => words Crypto.Ripemd160.rP[i]!)
          (fun i => Crypto.Ripemd160.KP[i / 16]!) count right) := by
  simp only [hoistedAlgorithmFold, Nat.zero_add]
  have hconstant (i : Nat) (hi : i < count) :
      algorithmKey (i / 16) =
        packed32 Crypto.Ripemd160.K[i / 16]! Crypto.Ripemd160.KP[i / 16]! :=
    algorithmKey_packed ⟨i / 16, by omega⟩
  have hrotation (i : Nat) (hi : i < count) :
      0 < Crypto.Ripemd160.s[i]! ∧ Crypto.Ripemd160.s[i]! < 32 ∧
      0 < Crypto.Ripemd160.sP[i]! ∧ Crypto.Ripemd160.sP[i]! < 32 :=
    algorithmRotation_bounds ⟨i, by omega⟩
  have h0 := hoistedWordFold_congr
    (fun i => i / 16) (fun i => Crypto.Ripemd160.s[i]!) (fun i => Crypto.Ripemd160.sP[i]!)
    (algorithmMessage memory) (fun i => algorithmKey (i / 16))
    (fun i => UInt256.add
      (packed32 (words Crypto.Ripemd160.r[i]!) (words Crypto.Ripemd160.rP[i]!))
      (UInt256.ofNat (garbageLow i + garbageHigh i * 2 ^ 160)))
    (fun i => packed32 Crypto.Ripemd160.K[i / 16]! Crypto.Ripemd160.KP[i / 16]!)
    count (PairedLaneWordRound.packCrypto left right) hmessage hconstant
  exact h0.trans (hoistedWordFold_crypto_garbage
    (fun i => i / 16) (fun i => Crypto.Ripemd160.s[i]!) (fun i => Crypto.Ripemd160.sP[i]!)
    (fun i => words Crypto.Ripemd160.r[i]!) (fun i => words Crypto.Ripemd160.rP[i]!)
    (fun i => Crypto.Ripemd160.K[i / 16]!) (fun i => Crypto.Ripemd160.KP[i / 16]!)
    garbageLow garbageHigh count left right hrotation hgarbage)

#print axioms hoistedAlgorithmFold_crypto_garbage

end Challenge.Ripemd160.Submission.Proofs.Bytecode.PairedSynthCoreTrace

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.PairedAllInlineCoreTrace

open EvmSemantics EvmSemantics.EVM YulEvmCompiler
open StackRoundTrace PairedLaneUInt256Bridge PairedLaneWordBoolean
open PairedHelperBooleanTrace PairedLaneWordGroupTwoHoist
open PairedLaneCore PairedSynthCoreTrace PairedLaneWordRound

/-- The whole straight-line core, run against a schedule that carries
spacer garbage. Identical conclusion to `run_wholeCore_crypto`: the
garbage never reaches the result. -/
theorem run_wholeCore_crypto_garbage (s : State) (words : Nat → UInt32)
    (garbageLow garbageHigh : Nat → Nat)
    (left right : PairedLaneCryptoBridge.CryptoLane) (rho : List UInt256)
    (hstack : rho.length ≤ 1002) (hrun : s.halt = .Running)
    (hactive : 23 ≤ s.activeWords.toNat)
    (hgarbage : ∀ i < 80,
      garbageLow i % 2 ^ 32 = 0 ∧ garbageLow i < 2 ^ 96 ∧
      garbageHigh i < 2 ^ 64)
    (hmessage : ∀ i < 80, algorithmMessage s.memory i =
      UInt256.add
        (packed32 (words Crypto.Ripemd160.r[i]!) (words Crypto.Ripemd160.rP[i]!))
        (UInt256.ofNat (garbageLow i + garbageHigh i * 2 ^ 160))) :
    runInstrSeq wholeCoreChain.code
      {s with pc := UInt256.ofNat 727, stack := coreStack [.a, .b, .c, .d, .e, .factor, .pair, .upper, .lower] ⟨PairedLaneWordRound.packCrypto left right, 0⟩ rho} =
      some {s with pc := UInt256.ofNat 4729, stack := coreStack [.d, .b, .c, .a, .e, .factor, .pair, .upper, .lower] (coreCryptoResult words left right) rho} := by
  let f : CoreFrame := ⟨PairedLaneWordRound.packCrypto left right, 0⟩
  have h0 := wholeCoreChain_eval s.memory f
  have h1 := PairedSynthCoreTrace.hoistedAlgorithmFold_crypto_garbage s.memory words
    garbageLow garbageHigh 80 (by decide) left right hgarbage hmessage
  have he : wholeCoreChain.eval s.memory f = coreCryptoResult words left right :=
    h0.trans (congrArg (fun q => CoreFrame.mk q (algorithmKey 4)) h1)
  exact (run_wholeCoreChain s f rho hstack hrun hactive).trans
    (congrArg (fun q => some {s with pc := UInt256.ofNat 4729, stack := coreStack [.d, .b, .c, .a, .e, .factor, .pair, .upper, .lower] q rho}) he)

#print axioms run_wholeCore_crypto_garbage

end Challenge.Ripemd160.Submission.Proofs.Bytecode.PairedAllInlineCoreTrace


namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.PairedMask32Cache

open EvmSemantics EvmSemantics.EVM YulEvmCompiler Challenge.EvmProof
open StackRoundTrace DenseScheduleTemplate PairedScheduleMemory

end Challenge.Ripemd160.Submission.Proofs.Bytecode.PairedMask32Cache
