import Challenge.Ripemd160.Submission.Proofs.Bytecode.PairTableLayout
import Challenge.Ripemd160.Submission.Proofs.Bytecode.Paired80FinalWord
import Challenge.EvmProof.Word
set_option warningAsError true
namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.Table80FinalBridge
open EvmSemantics Challenge.EvmProof PairedLaneUInt256Bridge Paired80Core
open Paired80WordRound Paired80Algorithm

def message (memory : ByteArray) (i : Nat) : UInt256 :=
  MachineState.readWord memory (10 * PairTableLayout.pairIndices[i]!)

theorem messageReady (memory : ByteArray) (words : Nat → UInt256)
    (scalar : Nat → UInt32)
    (hwords : ∀ k, k < 16 → words k = Word.ofUInt32 (scalar k)) :
    MessageReady (message (PairTableLayout.resultMemory memory words)) scalar 80 := by
  have hb (k : Nat) (hk : k < 16) : (words k).toNat < 2 ^ 32 := by
    rw [hwords k hk, Word.ofUInt32_toNat]
    exact (scalar k).toBitVec.isLt
  intro i hi
  obtain ⟨hl, hr⟩ := index_bounds ⟨i, hi⟩
  unfold Paired80Message.Eq112
  rw [bits_toNat, pack_toNat]
  change (MachineState.readWord (PairTableLayout.resultMemory memory words)
    (10 * PairTableLayout.pairIndices[i]!)).toNat % 2 ^ 112 =
    ((scalar Crypto.Ripemd160.r[i]!).toNat +
      (scalar Crypto.Ripemd160.rP[i]!).toNat * 2 ^ 80) % 2 ^ 112
  rw [PairTableLayout.read_round memory words i hi hb,
    hwords _ hl, hwords _ hr, Word.ofUInt32_toNat, Word.ofUInt32_toNat]
  symm
  apply Nat.mod_eq_of_lt
  have hl := (scalar Crypto.Ripemd160.r[i]!).toBitVec.isLt
  have hr := (scalar Crypto.Ripemd160.rP[i]!).toBitVec.isLt
  change (scalar Crypto.Ripemd160.r[i]!).toNat < 2 ^ 32 at hl
  change (scalar Crypto.Ripemd160.rP[i]!).toNat < 2 ^ 32 at hr
  simp only [Nat.reducePow] at *
  omega

#print axioms messageReady
end Challenge.Ripemd160.Submission.Proofs.Bytecode.Table80FinalBridge
