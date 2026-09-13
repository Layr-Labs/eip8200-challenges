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

/-- The loader stores words 1 and 2 without their mask: `g k` extra 32-bit words sit above
each scalar word, at most two, at most one unless `k = 2`, none for the other words except
word 15, which may carry fewer than `2 ^ 23` (the pad-only block leaves at most three dead bits
above its unmasked bit length). -/
theorem ready_junk (memory : ByteArray) (words : Nat → UInt256) (scalar : Nat → UInt32)
    (g : Nat → Nat)
    (hwords : ∀ k, k < 16 → (words k).toNat = (scalar k).toNat + g k * 2 ^ 32)
    (hg : ∀ k, k < 16 → g k < 2 ^ 64) (hg32 : ∀ k, k < 16 → k ≠ 2 → g k < 2 ^ 32)
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
    refine ⟨g Crypto.Ripemd160.r[i]!, g Crypto.Ripemd160.rP[i + 3]!,
      ⟨hg _ hl, hg _ hr, fun hu => hg32 _ hl (hc hu),
        hclean _ hl, hclean _ hr, hg32 _ hl⟩, ?_⟩
    apply BitVec.eq_of_toNat_eq
    rw [bits_toNat, BitVec.toNat_add, pack_toNat, StaggerRound.junk, BitVec.toNat_ofNat]
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
    (fun _ _ => by norm_num) (fun _ _ _ => by norm_num) (fun _ _ _ => ⟨by norm_num, fun _ => rfl⟩)

#print axioms ready_junk
#print axioms ready
end Challenge.Ripemd160.Submission.Proofs.Bytecode.StaggerMessage
