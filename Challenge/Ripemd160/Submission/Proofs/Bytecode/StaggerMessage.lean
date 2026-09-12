import Challenge.Ripemd160.Submission.Proofs.Bytecode.StaggerCoreModel
import Challenge.EvmProof.Word
set_option warningAsError true
namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.StaggerMessage
open EvmSemantics EvmSemantics.EVM Challenge.EvmProof PairedLaneUInt256Bridge Paired80Core
open Paired80Compression
open StaggerCoreModel (message)

structure Ready (memory : ByteArray) (words : Nat → UInt32) : Prop where
  paired : StaggerAlgorithm.MessageReady (message memory) words 77
  scalar : ∀ j, j < 61 → low32 (MachineState.readWord memory (10 * j)) = words StaggerTableLayout.slots[j]!

theorem ready (memory : ByteArray) (words : Nat → UInt256) (scalar : Nat → UInt32)
    (hwords : ∀ k, k < 16 → words k = Word.ofUInt32 (scalar k)) :
    Ready (StaggerTableLayout.resultMemory memory words) scalar := by
  have hb (k : Nat) (hk : k < 16) : (words k).toNat < 2 ^ 32 := by
    rw [hwords k hk, Word.ofUInt32_toNat]
    exact (scalar k).toBitVec.isLt
  constructor
  · intro i hi
    have hl := (Paired80Algorithm.index_bounds ⟨i, by omega⟩).1
    have hr := (Paired80Algorithm.index_bounds ⟨i+3, by omega⟩).2
    unfold Paired80Message.Eq112
    rw [bits_toNat, pack_toNat]
    change (MachineState.readWord (StaggerTableLayout.resultMemory memory words)
      (10 * StaggerTableLayout.pairIndices[i]!)).toNat % 2 ^ 112 =
      ((scalar Crypto.Ripemd160.r[i]!).toNat +
        (scalar Crypto.Ripemd160.rP[i+3]!).toNat * 2 ^ 80) % 2 ^ 112
    rw [StaggerTableLayout.read_round memory words i hi hb,
      hwords _ hl, hwords _ hr, Word.ofUInt32_toNat, Word.ofUInt32_toNat]
    symm
    apply Nat.mod_eq_of_lt
    have hl : (scalar Crypto.Ripemd160.r[i]!).toNat < 2 ^ 32 := (scalar _).toBitVec.isLt
    have hr : (scalar Crypto.Ripemd160.rP[i+3]!).toNat < 2 ^ 32 := (scalar _).toBitVec.isLt
    simp only [Nat.reducePow] at *
    omega
  · intro j hj
    apply UInt32.toNat_inj.mp
    change (MachineState.readWord (StaggerTableLayout.resultMemory memory words) (10*j)).toNat % 2^32 = _
    rw [StaggerTableLayout.read_slot_low memory words j hj hb,
      hwords _ (StaggerTableLayout.slots_lt j hj), Word.ofUInt32_toNat]

#print axioms ready
end Challenge.Ripemd160.Submission.Proofs.Bytecode.StaggerMessage
