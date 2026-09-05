import Challenge.Ripemd160.Submission.Proofs.Bytecode.StackRound
import Challenge.Ripemd160.Submission.Proofs.Bytecode.CompressionCorrect

set_option warningAsError true
set_option maxHeartbeats 1000000

/-!
# Functional composition of the direct stack rounds

The round trace supplies the exact machine transition. This file relates the
two direct 80-round folds and their cross-combination to the pinned block
model. It does not assert a bytecode execution trace.
-/

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.StackCompression

open EvmSemantics
open Challenge.EvmProof.Word
open Compression

def leftStep (word : Nat → UInt32) (i : Nat) (x : EvmWorking) : EvmWorking :=
  StackRound.stackRound x (i / 16)
    (ofUInt32 (word (Crypto.Ripemd160.r[i]!)))
    (Crypto.Ripemd160.s[i]!) (ofUInt32 (Crypto.Ripemd160.K[i / 16]!))

def rightStep (word : Nat → UInt32) (i : Nat) (x : EvmWorking) : EvmWorking :=
  StackRound.stackRound x (4 - i / 16)
    (ofUInt32 (word (Crypto.Ripemd160.rP[i]!)))
    (Crypto.Ripemd160.sP[i]!) (ofUInt32 (Crypto.Ripemd160.KP[i / 16]!))

private theorem leftRotation (i : Nat) (hi : i < 80) :
    0 < Crypto.Ripemd160.s[i]! ∧ Crypto.Ripemd160.s[i]! < 32 := by
  interval_cases i <;> decide

private theorem rightRotation (i : Nat) (hi : i < 80) :
    0 < Crypto.Ripemd160.sP[i]! ∧ Crypto.Ripemd160.sP[i]! < 32 := by
  interval_cases i <;> decide

theorem leftStep_embed (word : Nat → UInt32) (i : Nat) (x : Working)
    (hi : i < 80) :
    leftStep word i (embed x) = embed (CompressionCorrect.leftStep word i x) := by
  unfold leftStep CompressionCorrect.leftStep
  exact StackRound.stackRound_embed x (i / 16) _ _ _ (by omega)
    (leftRotation i hi).1 (leftRotation i hi).2

theorem rightStep_embed (word : Nat → UInt32) (i : Nat) (x : Working)
    (hi : i < 80) :
    rightStep word i (embed x) = embed (CompressionCorrect.rightStep word i x) := by
  unfold rightStep CompressionCorrect.rightStep
  exact StackRound.stackRound_embed x (4 - i / 16) _ _ _ (by omega)
    (rightRotation i hi).1 (rightRotation i hi).2

def leftRounds (word : Nat → UInt32) : Nat → EvmWorking → EvmWorking
  | 0, x => x
  | i + 1, x => leftStep word i (leftRounds word i x)

def rightRounds (word : Nat → UInt32) : Nat → EvmWorking → EvmWorking
  | 0, x => x
  | i + 1, x => rightStep word i (rightRounds word i x)

theorem leftRounds_embed (word : Nat → UInt32) (count : Nat) (x : Working)
    (hc : count ≤ 80) :
    leftRounds word count (embed x) =
      embed (CompressionCorrect.leftRounds word count x) := by
  induction count with
  | zero => rfl
  | succ i ih =>
      rw [leftRounds, CompressionCorrect.leftRounds, ih (by omega)]
      exact leftStep_embed word i _ (by omega)

theorem rightRounds_embed (word : Nat → UInt32) (count : Nat) (x : Working)
    (hc : count ≤ 80) :
    rightRounds word count (embed x) =
      embed (CompressionCorrect.rightRounds word count x) := by
  induction count with
  | zero => rfl
  | succ i ih =>
      rw [rightRounds, CompressionCorrect.rightRounds, ih (by omega)]
      exact rightStep_embed word i _ (by omega)

def compress (word : Nat → UInt32) (h : EvmHashState) : EvmHashState :=
  evmCombine h
    (leftRounds word 80 (CompressionCorrect.evmWorkingOfHash h))
    (rightRounds word 80 (CompressionCorrect.evmWorkingOfHash h))

theorem compress_embed (word : Nat → UInt32) (h : HashState) :
    compress word (embedHash h) =
      embedHash (CompressionCorrect.compressModel word h) := by
  rw [compress, CompressionCorrect.compressModel,
    CompressionCorrect.evmWorkingOfHash_embed,
    leftRounds_embed _ 80 _ (by omega),
    rightRounds_embed _ 80 _ (by omega), evmCombine_embed]

theorem compress_eq_specBlock (bs : ByteArray) (blockOff : Nat) (h : HashState) :
    let out := compress (fun i => (CompressionCorrect.schedule bs blockOff)[i]!)
      (embedHash h)
    #[toUInt32 out.h0, toUInt32 out.h1, toUInt32 out.h2,
      toUInt32 out.h3, toUInt32 out.h4] =
      Crypto.Ripemd160.compressBlock (CompressionCorrect.hashArray h) bs blockOff := by
  dsimp only
  rw [compress_embed]
  simp only [embedHash, toUInt32_ofUInt32]
  exact CompressionCorrect.compressModel_eq_compressBlock bs blockOff h

end Challenge.Ripemd160.Submission.Proofs.Bytecode.StackCompression
