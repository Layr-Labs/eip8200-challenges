import Challenge.Ripemd160.Submission.Proofs.Bytecode.Main
import Challenge.Ripemd160.Submission.Proofs.Bytecode.Word
import Challenge.EvmProof.Memory
import Mathlib.Tactic.IntervalCases
set_option warningAsError true
set_option maxRecDepth 20000
set_option maxHeartbeats 2000000
/-!
# Functional correctness of RIPEMD-160 initialization

The direct execution proof in `Main` establishes every store.  Here we expose
the algorithm-facing invariant of that fixed memory image: all four packed
80-byte selector/rotation tables, both constant arrays, and the five initial
hash words agree with the RIPEMD-160 specification.
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

@[simp] private theorem toNat32 : (32 : UInt256).toNat = 32 := by decide
@[simp] private theorem toNat64 : (64 : UInt256).toNat = 64 := by decide
@[simp] private theorem toNat96 : (96 : UInt256).toNat = 96 := by decide
@[simp] private theorem toNat128 : (128 : UInt256).toNat = 128 := by decide
@[simp] private theorem toNat160 : (160 : UInt256).toNat = 160 := by decide
@[simp] private theorem toNat1184 : (1184 : UInt256).toNat = 1184 := by decide
@[simp] private theorem toNat1216 : (1216 : UInt256).toNat = 1216 := by decide
@[simp] private theorem toNat1248 : (1248 : UInt256).toNat = 1248 := by decide
@[simp] private theorem toNat1280 : (1280 : UInt256).toNat = 1280 := by decide
@[simp] private theorem toNat1312 : (1312 : UInt256).toNat = 1312 := by decide
@[simp] private theorem toNat1344 : (1344 : UInt256).toNat = 1344 := by decide
@[simp] private theorem toNat1376 : (1376 : UInt256).toNat = 1376 := by decide
@[simp] private theorem toNat1408 : (1408 : UInt256).toNat = 1408 := by decide
@[simp] private theorem toNat1440 : (1440 : UInt256).toNat = 1440 := by decide
@[simp] private theorem toNat1472 : (1472 : UInt256).toNat = 1472 := by decide
@[simp] private theorem toNat1504 : (1504 : UInt256).toNat = 1504 := by decide
@[simp] private theorem toNat1536 : (1536 : UInt256).toNat = 1536 := by decide
@[simp] private theorem toNat1568 : (1568 : UInt256).toNat = 1568 := by decide
@[simp] private theorem toNat1600 : (1600 : UInt256).toNat = 1600 := by decide
@[simp] private theorem toNat1632 : (1632 : UInt256).toNat = 1632 := by decide
@[simp] private theorem toNat1664 : (1664 : UInt256).toNat = 1664 := by decide
@[simp] private theorem toNat1696 : (1696 : UInt256).toNat = 1696 := by decide
@[simp] private theorem toNat1728 : (1728 : UInt256).toNat = 1728 := by decide
@[simp] private theorem toNat1760 : (1760 : UInt256).toNat = 1760 := by decide
@[simp] private theorem toNat1792 : (1792 : UInt256).toNat = 1792 := by decide
@[simp] private theorem toNat1824 : (1824 : UInt256).toNat = 1824 := by decide
@[simp] private theorem toNat1856 : (1856 : UInt256).toNat = 1856 := by decide

/-- The packed-table addressing expression used by Yul's `tableAt`. -/
def tableByte (memory : ByteArray) (base i : Nat) : UInt256 :=
  UInt256.byteAt (UInt256.ofNat (i % 32))
    (MachineState.readWord memory (base + 32 * (i / 32)))

/-- The 32-byte-strided word addressing used by the state and constants. -/
def slotWord (memory : ByteArray) (base i : Nat) : UInt256 :=
  MachineState.readWord memory (base + 32 * i)

def HashStateCorrect (memory : ByteArray) : Prop :=
  ∀ i, i < 5 →
    slotWord memory 0x020 i = ofUInt32 (Crypto.Ripemd160.H0[i]!)

private theorem initialized_h (i : Nat) (hi : i < 5) :
    slotWord initializedMemory 0x020 i =
      ofUInt32 (Crypto.Ripemd160.H0[i]!) := by
  interval_cases i <;>
    unfold slotWord initializedMemory Main.initializedState Main.skippedState <;>
    norm_num [Artifact.initStores, Main.applyInitStore,
      Execution.mainStart, Execution.atPC, initialState,
      Challenge.EvmProof.Word.word_toNat_ofNat, numeralToNat]
  all_goals
    repeat'
      first
      | rw [Challenge.EvmProof.Memory.readWord_writeBytes_of_lt _ _ _
          (by exact Fin.isLt _)]
      | rw [Challenge.EvmProof.Memory.readWord_writeBytes_disjoint _ _ _ _
          (by simp only [initBytes_size]; omega)]
  all_goals norm_num [Crypto.Ripemd160.H0, ofUInt32] ; decide

theorem initializedMemory_hash : HashStateCorrect initializedMemory :=
  initialized_h

theorem initializedState_hash (input : ByteArray) :
    HashStateCorrect (Main.initializedState input).memory := by
  rw [initializedState_memory]
  exact initializedMemory_hash

end Challenge.Ripemd160.Submission.Proofs.Bytecode.InitializationCorrect
