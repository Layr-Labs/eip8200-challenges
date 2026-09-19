import Challenge.Ripemd160.Submission.Proofs.Bytecode.StaggerCoreModel
import Challenge.EvmProof.Word
set_option warningAsError true
set_option maxRecDepth 10000
namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.StaggerMessage
open EvmSemantics EvmSemantics.EVM Challenge.EvmProof PairedLaneUInt256Bridge Paired144Core
open Paired80Compression
open StaggerCoreModel (message)

structure Ready (memory : ByteArray) (words : Nat → UInt32) : Prop where
  paired : StaggerAlgorithm.MessageReady (message memory) words 77
  scalar : ∀ j, j < 61 → low32 (MachineState.readWord memory (18 * j)) = words StaggerTableLayout.slots[j]!

/-- No compact-rotation round reads schedule word 2 (the only word with 64 dead bits) in its
lower half. -/
theorem compact_not_two (i : Fin 77) :
    Paired144WordRound.usesCompact Crypto.Ripemd160.s[i.val]! Crypto.Ripemd160.sP[i.val + 3]! →
      Crypto.Ripemd160.r[i.val]! ≠ 2 := by
  have h : ∀ j : Fin 77,
      Paired144WordRound.usesCompact Crypto.Ripemd160.s[j.val]! Crypto.Ripemd160.sP[j.val + 3]! →
        Crypto.Ripemd160.r[j.val]! ≠ 2 := by decide
  exact h i

/-- The loader stores words 1 and 2 without their mask, the pad-only block word 14: `g k`
extra 32-bit words sit above each scalar word, at most two, fewer than `2 ^ 35` unless `k = 2`,
at most one unless `k = 2` or `k = 14`, none for the other words except word 15, which may
carry fewer than `2 ^ 23` (the pad-only block leaves at most three dead bits above its
unmasked bit length). -/
theorem ready_junk (memory : ByteArray) (words : Nat → UInt256) (scalar : Nat → UInt32)
    (g : Nat → Nat)
    (hwords : ∀ k, k < 16 → (words k).toNat = (scalar k).toNat + g k * 2 ^ 32)
    (hg : ∀ k, k < 16 → g k < 2 ^ 64) (hg35 : ∀ k, k < 16 → k ≠ 2 → g k < 2 ^ 35)
    (hg32 : ∀ k, k < 16 → k ≠ 2 → k ≠ 14 → g k < 2 ^ 32)
    (hclean : ∀ k, k < 16 → ¬ StaggerAlgorithm.Dirty k → g k < 2 ^ 23 ∧ (k ≠ 15 → g k = 0)) :
    Ready (StaggerTableLayout.resultMemory memory words) scalar := by
  have hs (k : Nat) : (scalar k).toNat < 2 ^ 32 := (scalar k).toBitVec.isLt
  have hb (k : Nat) (hk : k < 16) : (words k).toNat < 2 ^ 112 := by
    rw [hwords k hk]
    have := hs k; have := hg k hk
    omega
  constructor
  · intro i hi
    have hl := (Paired80Algorithm.index_bounds ⟨i, by omega⟩).1
    have hr := (Paired80Algorithm.index_bounds ⟨i+3, by omega⟩).2
    have hc := compact_not_two ⟨i, hi⟩
    apply Or.inl
    refine ⟨g Crypto.Ripemd160.r[i]!, g Crypto.Ripemd160.rP[i + 3]!,
      ⟨hg _ hl, hg _ hr, fun hu => hg35 _ hl (hc hu),
        hclean _ hl, hclean _ hr, hg32 _ hl⟩, ?_⟩
    apply BitVec.eq_of_toNat_eq
    rw [bits_toNat, BitVec.toNat_add, pack_toNat, StaggerRound.junk, BitVec.toNat_ofNat]
    by_cases hi76 : i = 76
    · subst i
      have hgl : g Crypto.Ripemd160.r[76]! = 0 := by
        exact ((hclean Crypto.Ripemd160.r[76]! (by decide) (by decide)).2 (by decide))
      have hgr : g Crypto.Ripemd160.rP[79]! = 0 := by
        exact ((hclean Crypto.Ripemd160.rP[79]! (by decide) (by decide)).2 (by decide))
      have hword :
          MachineState.readWord (StaggerTableLayout.resultMemory memory words)
              (18 * StaggerTableLayout.pairIndices[76]!) =
            word (pack (scalar Crypto.Ripemd160.r[76]!).toBitVec
              (scalar Crypto.Ripemd160.rP[79]!).toBitVec) := by
        apply Word.word_ext
        rw [StaggerTableLayout.read_round_wide memory words 76 (by decide) hb]
        simp only [hwords Crypto.Ripemd160.r[76]! (by decide),
          hwords Crypto.Ripemd160.rP[79]! (by decide), hgl, hgr,
          Nat.zero_mul, Nat.add_zero]
        rw [← bits_toNat, bits_word, pack_toNat, UInt32.toNat_toBitVec]
      have hx :
          Paired144Core.normalize (bits
              (MachineState.readWord (StaggerTableLayout.resultMemory memory words)
                (18 * StaggerTableLayout.pairIndices[76]!))) =
            pack (scalar Crypto.Ripemd160.r[76]!).toBitVec
              (scalar Crypto.Ripemd160.rP[79]!).toBitVec := by
        rw [hword, bits_word, normalize_pack]
      have hmasked :
          (UInt256.land
              (MachineState.readWord (StaggerTableLayout.resultMemory memory words)
                (18 * StaggerTableLayout.pairIndices[76]!))
              Paired144WordRound.pairWord).toNat =
            (scalar Crypto.Ripemd160.r[76]!).toBitVec.toNat +
              (scalar Crypto.Ripemd160.rP[79]!).toBitVec.toNat * 2 ^ 144 := by
        rw [← bits_toNat, bits_land, Paired144WordRound.pairWord, bits_word,
          ← normalize_eq_and, hx, pack_toNat]
      simp only [StaggerCoreModel.message, if_pos]
      rw [hmasked]
      have h1 := hs Crypto.Ripemd160.r[76]!; have h2 := hs Crypto.Ripemd160.rP[79]!
      have h3 := hg Crypto.Ripemd160.r[76]! (by decide)
      have h4 := hg Crypto.Ripemd160.rP[79]! (by decide)
      simp only [hgl, hgr, Nat.zero_mul, Nat.add_zero, UInt32.toNat_toBitVec] at *
      omega
    · simp only [StaggerCoreModel.message, if_neg hi76]
      change (MachineState.readWord (StaggerTableLayout.resultMemory memory words)
        (18 * StaggerTableLayout.pairIndices[i]!)).toNat = _
      rw [StaggerTableLayout.read_round_wide memory words i hi hb, hwords _ hl, hwords _ hr]
      have h1 := hs Crypto.Ripemd160.r[i]!; have h2 := hs Crypto.Ripemd160.rP[i + 3]!
      have h3 := hg _ hl; have h4 := hg _ hr
      simp only [UInt32.toNat_toBitVec] at *
      omega
  · intro j hj
    apply UInt32.toNat_inj.mp
    change (MachineState.readWord (StaggerTableLayout.resultMemory memory words) (18*j)).toNat % 2^32 = _
    rw [StaggerTableLayout.read_slot_low_wide memory words j hj hb,
      hwords _ (StaggerTableLayout.slots_lt j hj)]
    have := hs StaggerTableLayout.slots[j]!
    change _ = (scalar StaggerTableLayout.slots[j]!).toNat
    omega

theorem ready (memory : ByteArray) (words : Nat → UInt256) (scalar : Nat → UInt32)
    (hwords : ∀ k, k < 16 → words k = Word.ofUInt32 (scalar k)) :
    Ready (StaggerTableLayout.resultMemory memory words) scalar :=
  ready_junk memory words scalar (fun _ => 0)
    (fun k hk => by rw [hwords k hk, Word.ofUInt32_toNat]; omega)
    (fun _ _ => by norm_num) (fun _ _ _ => by norm_num) (fun _ _ _ _ => by norm_num)
    (fun _ _ _ => ⟨by norm_num, fun _ => rfl⟩)

/-- `Ready` depends on the table image only from byte 14 up, plus the low 32 bits of the
word at address 0.  `Ready.paired` reads at `18 * pairIndices[i]!` and `layout_valid` gives
`1 ≤ pairIndices[i]!`, so every round window starts at address 18; `Ready.scalar` at `j = 0`
reads address 0 but only through `low32`.  Both the normal-block table and the pad-only
table are repaired through this one lemma. -/
theorem ready_congr_high (m m' : ByteArray) (scalar : Nat → UInt32)
    (hbyte : ∀ j, 14 ≤ j → m'[j]?.getD 0 = m[j]?.getD 0)
    (hlo : (MachineState.readWord m' 0).toNat % 2 ^ 32
         = (MachineState.readWord m 0).toNat % 2 ^ 32)
    (h : Ready m scalar) : Ready m' scalar := by
  have hread : ∀ A, 14 ≤ A → MachineState.readWord m' A = MachineState.readWord m A := by
    intro A hA
    apply Word.word_ext
    rw [Bytes.readWord_toNat, Bytes.readWord_toNat]
    exact StaggerTableMemory.bytesToNatPadded_congrOffset _ _ _ _ _
      (fun i _ => hbyte (A + i) (by omega))
  constructor
  · intro i hi
    obtain ⟨hpos, -, -, -⟩ := StaggerTableLayout.layout_valid ⟨i, hi⟩
    change 1 ≤ StaggerTableLayout.pairIndices[i]! at hpos
    have heq : StaggerCoreModel.message m' i = StaggerCoreModel.message m i := by
      by_cases hi76 : i = 76
      · subst i
        simp only [StaggerCoreModel.message, if_pos]
        exact congrArg (fun x => UInt256.land x Paired144WordRound.pairWord)
          (hread _ (by omega))
      · simp only [StaggerCoreModel.message, if_neg hi76]
        exact hread _ (by omega)
    rw [heq]
    exact h.paired i hi
  · intro j hj
    by_cases hz : j = 0
    · subst hz
      have hprev := h.scalar 0 hj
      apply UInt32.toNat_inj.mp
      have hgoal := congrArg UInt32.toNat hprev
      change (MachineState.readWord m (18 * 0)).toNat % 2 ^ 32 = _ at hgoal
      change (MachineState.readWord m' (18 * 0)).toNat % 2 ^ 32 = _
      rw [show 18 * 0 = 0 from rfl] at hgoal ⊢
      rw [hlo]
      exact hgoal
    · rw [hread (18 * j) (by omega)]
      exact h.scalar j hj

/-- `Ready` survives overwriting the word at address 0, provided the new value agrees with
the old on its low 32 bits and the image agrees from byte 14 up.  `Ready.paired` reads only
at `18 * pairIndices[i]!` and `layout_valid` gives `1 ≤ pairIndices[i]!`, so every round
window starts at address 18; `Ready.scalar` at `j = 0` reads address 0 but only through
`low32`.  Both the normal-block and the pad-only table use this. -/
theorem ready_writeWord_zero (memory : ByteArray) (scalar : Nat → UInt32) (v : UInt256)
    (hlo : v.toNat % 2 ^ 32 = (MachineState.readWord memory 0).toNat % 2 ^ 32)
    (hbyte : ∀ j, 14 ≤ j →
      (PairedScheduleMemory.writeWord memory 0 v)[j]?.getD 0 = memory[j]?.getD 0)
    (h : Ready memory scalar) :
    Ready (PairedScheduleMemory.writeWord memory 0 v) scalar :=
  ready_congr_high memory _ scalar hbyte
    (by rw [PairedScheduleMemory.read_writeWord]; exact hlo) h

/-- The dual lane the removed mask at pc 873 leaves in slot 0 is invisible to `Ready`. -/
theorem ready_dual0 (memory : ByteArray) (words : Nat → UInt256) (scalar : Nat → UInt32)
    (hw : (words 6).toNat < 2 ^ 32)
    (h : Ready (StaggerTableLayout.resultMemory memory words) scalar) :
    Ready (StaggerTableLayout.resultMemory0 memory words) scalar := by
  rw [StaggerTableLayout.resultMemory0]
  refine ready_writeWord_zero _ scalar _ ?_ ?_ h
  · have := StaggerTableLayout.read_zero0_low memory words hw
    rw [StaggerTableLayout.read_zero0] at this
    exact this
  · intro j hj
    have := StaggerTableLayout.getD_resultMemory0 memory words hw j hj
    rwa [StaggerTableLayout.resultMemory0] at this

#print axioms ready_dual0
#print axioms ready_junk
#print axioms ready
end Challenge.Ripemd160.Submission.Proofs.Bytecode.StaggerMessage
