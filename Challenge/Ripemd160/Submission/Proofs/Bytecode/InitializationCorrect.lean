import Challenge.Ripemd160.Submission.Proofs.Bytecode.Main
import Challenge.Ripemd160.Submission.Proofs.Bytecode.Word
import Challenge.EvmProof.Memory
import Mathlib.Tactic.IntervalCases

set_option warningAsError true
set_option maxRecDepth 20000
set_option maxHeartbeats 2000000

/-!
# Functional correctness of the compact RIPEMD-160 initialization

The executable entry initializes only the five chaining words used by the
current compression path. This module exposes that exact memory invariant.
-/

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.InitializationCorrect

open EvmSemantics
open EvmSemantics.EVM
open Challenge.EvmProof.Word

def initializedMemory : ByteArray :=
  (Main.initializedState ByteArray.empty).memory

theorem initializedState_memory (input : ByteArray) :
    (Main.initializedState input).memory = initializedMemory := by
  rfl

@[simp] private theorem numeralToNat (a : Nat) :
    UInt256.toNat (OfNat.ofNat a : UInt256) = a % 2 ^ 256 := by
  exact Challenge.EvmProof.Word.word_toNat_ofNat a

@[simp] private theorem initBytes_size (n : Nat) :
    (Data.Bytes.natToBytesPadded n 32).size = 32 := by
  simp [Data.Bytes.natToBytesPadded, ByteArray.size]

@[simp] private theorem toNat544 : (544 : UInt256).toNat = 544 := by decide
@[simp] private theorem toNat576 : (576 : UInt256).toNat = 576 := by decide
@[simp] private theorem toNat608 : (608 : UInt256).toNat = 608 := by decide
@[simp] private theorem toNat640 : (640 : UInt256).toNat = 640 := by decide
@[simp] private theorem toNat672 : (672 : UInt256).toNat = 672 := by decide

def slotWord (memory : ByteArray) (base i : Nat) : UInt256 :=
  MachineState.readWord memory (base + 32 * i)

private theorem initialized_h (i : Nat) (hi : i < 5) :
    slotWord initializedMemory 0x220 i =
      ofUInt32 (Crypto.Ripemd160.H0[i]!) := by
  interval_cases i <;>
    unfold slotWord initializedMemory Main.initializedState <;>
    norm_num [Artifact.initStores, Main.applyInitStore,
      Challenge.EvmProof.Word.word_toNat_ofNat, numeralToNat]
  all_goals
    repeat'
      first
      | rw [Challenge.EvmProof.Memory.readWord_writeBytes_of_lt _ _ _
          (by exact Fin.isLt _)]
      | rw [Challenge.EvmProof.Memory.readWord_writeBytes_disjoint _ _ _ _
          (by simp only [initBytes_size]; omega)]
  all_goals (norm_num [Crypto.Ripemd160.H0, ofUInt32] ; decide)

theorem initializedState_hash (input : ByteArray) :
    ∀ i, i < 5 →
      slotWord (Main.initializedState input).memory 0x220 i =
        ofUInt32 (Crypto.Ripemd160.H0[i]!) := by
  rw [initializedState_memory]
  exact initialized_h

end Challenge.Ripemd160.Submission.Proofs.Bytecode.InitializationCorrect
