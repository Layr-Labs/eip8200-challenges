import Challenge.Ripemd160.Reference.Proofs.Bytecode.Main
import Challenge.Ripemd160.Reference.Proofs.Bytecode.Word
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

namespace Challenge.Ripemd160.Reference.Proofs.Bytecode.InitializationCorrect

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

def TablesCorrect (memory : ByteArray) : Prop :=
  (∀ i, i < 80 → tableByte memory 0x4a0 i = UInt256.ofNat (Crypto.Ripemd160.r[i]!)) ∧
  (∀ i, i < 80 → tableByte memory 0x500 i = UInt256.ofNat (Crypto.Ripemd160.rP[i]!)) ∧
  (∀ i, i < 80 → tableByte memory 0x560 i = UInt256.ofNat (Crypto.Ripemd160.s[i]!)) ∧
  (∀ i, i < 80 → tableByte memory 0x5c0 i = UInt256.ofNat (Crypto.Ripemd160.sP[i]!))

def ConstantsCorrect (memory : ByteArray) : Prop :=
  (∀ j, j < 5 → slotWord memory 0x620 j = ofUInt32 (Crypto.Ripemd160.K[j]!)) ∧
  (∀ j, j < 5 → slotWord memory 0x6c0 j = ofUInt32 (Crypto.Ripemd160.KP[j]!)) ∧
  (∀ i, i < 5 → slotWord memory 0x020 i = ofUInt32 (Crypto.Ripemd160.H0[i]!))

private theorem initialized_r (i : Nat) (hi : i < 80) :
    tableByte initializedMemory 0x4a0 i =
      UInt256.ofNat (Crypto.Ripemd160.r[i]!) := by
  interval_cases i <;>
    unfold tableByte initializedMemory Main.initializedState <;>
    norm_num [Artifact.initStores, Main.applyInitStore,
      Challenge.EvmProof.Word.word_toNat_ofNat, numeralToNat]
  all_goals
    repeat'
      first
      | rw [Challenge.EvmProof.Memory.readWord_writeBytes_of_lt _ _ _
          (by exact Fin.isLt _)]
      | rw [Challenge.EvmProof.Memory.readWord_writeBytes_disjoint _ _ _ _
          (by simp only [initBytes_size]; omega)]
  all_goals norm_num [Crypto.Ripemd160.r] ; decide

private theorem initialized_rP (i : Nat) (hi : i < 80) :
    tableByte initializedMemory 0x500 i =
      UInt256.ofNat (Crypto.Ripemd160.rP[i]!) := by
  interval_cases i <;>
    unfold tableByte initializedMemory Main.initializedState <;>
    norm_num [Artifact.initStores, Main.applyInitStore,
      Challenge.EvmProof.Word.word_toNat_ofNat, numeralToNat]
  all_goals
    repeat'
      first
      | rw [Challenge.EvmProof.Memory.readWord_writeBytes_of_lt _ _ _
          (by exact Fin.isLt _)]
      | rw [Challenge.EvmProof.Memory.readWord_writeBytes_disjoint _ _ _ _
          (by simp only [initBytes_size]; omega)]
  all_goals norm_num [Crypto.Ripemd160.rP] ; decide

private theorem initialized_s (i : Nat) (hi : i < 80) :
    tableByte initializedMemory 0x560 i =
      UInt256.ofNat (Crypto.Ripemd160.s[i]!) := by
  interval_cases i <;>
    unfold tableByte initializedMemory Main.initializedState <;>
    norm_num [Artifact.initStores, Main.applyInitStore,
      Challenge.EvmProof.Word.word_toNat_ofNat, numeralToNat]
  all_goals
    repeat'
      first
      | rw [Challenge.EvmProof.Memory.readWord_writeBytes_of_lt _ _ _
          (by exact Fin.isLt _)]
      | rw [Challenge.EvmProof.Memory.readWord_writeBytes_disjoint _ _ _ _
          (by simp only [initBytes_size]; omega)]
  all_goals norm_num [Crypto.Ripemd160.s] ; decide

private theorem initialized_sP (i : Nat) (hi : i < 80) :
    tableByte initializedMemory 0x5c0 i =
      UInt256.ofNat (Crypto.Ripemd160.sP[i]!) := by
  interval_cases i <;>
    unfold tableByte initializedMemory Main.initializedState <;>
    norm_num [Artifact.initStores, Main.applyInitStore,
      Challenge.EvmProof.Word.word_toNat_ofNat, numeralToNat]
  all_goals
    repeat'
      first
      | rw [Challenge.EvmProof.Memory.readWord_writeBytes_of_lt _ _ _
          (by exact Fin.isLt _)]
      | rw [Challenge.EvmProof.Memory.readWord_writeBytes_disjoint _ _ _ _
          (by simp only [initBytes_size]; omega)]
  all_goals norm_num [Crypto.Ripemd160.sP] ; decide

private theorem initialized_k (j : Nat) (hj : j < 5) :
    slotWord initializedMemory 0x620 j =
      ofUInt32 (Crypto.Ripemd160.K[j]!) := by
  interval_cases j <;>
    unfold slotWord initializedMemory Main.initializedState <;>
    norm_num [Artifact.initStores, Main.applyInitStore,
      Challenge.EvmProof.Word.word_toNat_ofNat, numeralToNat]
  all_goals
    repeat'
      first
      | rw [Challenge.EvmProof.Memory.readWord_writeBytes_of_lt _ _ 0
          (by norm_num)]
      | rw [Challenge.EvmProof.Memory.readWord_writeBytes_of_lt _ _ _
          (by exact Fin.isLt _)]
      | rw [Challenge.EvmProof.Memory.readWord_writeBytes_disjoint _ _ _ _
          (by simp only [initBytes_size]; omega)]
  all_goals (norm_num [Crypto.Ripemd160.K, ofUInt32] <;> decide)

private theorem initialized_kP (j : Nat) (hj : j < 5) :
    slotWord initializedMemory 0x6c0 j =
      ofUInt32 (Crypto.Ripemd160.KP[j]!) := by
  interval_cases j <;>
    unfold slotWord initializedMemory Main.initializedState <;>
    norm_num [Artifact.initStores, Main.applyInitStore,
      Challenge.EvmProof.Word.word_toNat_ofNat, numeralToNat]
  all_goals
    repeat'
      first
      | rw [Challenge.EvmProof.Memory.readWord_writeBytes_of_lt _ _ 0
          (by norm_num)]
      | rw [Challenge.EvmProof.Memory.readWord_writeBytes_of_lt _ _ _
          (by exact Fin.isLt _)]
      | rw [Challenge.EvmProof.Memory.readWord_writeBytes_disjoint _ _ _ _
          (by simp only [initBytes_size]; omega)]
  all_goals (norm_num [Crypto.Ripemd160.KP, ofUInt32] <;> decide)

private theorem initialized_h (i : Nat) (hi : i < 5) :
    slotWord initializedMemory 0x020 i =
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
  all_goals norm_num [Crypto.Ripemd160.H0, ofUInt32] ; decide

theorem initializedMemory_tables : TablesCorrect initializedMemory :=
  ⟨initialized_r, initialized_rP, initialized_s, initialized_sP⟩

theorem initializedMemory_constants : ConstantsCorrect initializedMemory :=
  ⟨initialized_k, initialized_kP, initialized_h⟩

theorem initializedState_tables (input : ByteArray) :
    TablesCorrect (Main.initializedState input).memory := by
  rw [initializedState_memory]
  exact initializedMemory_tables

theorem initializedState_constants (input : ByteArray) :
    ConstantsCorrect (Main.initializedState input).memory := by
  rw [initializedState_memory]
  exact initializedMemory_constants

end Challenge.Ripemd160.Reference.Proofs.Bytecode.InitializationCorrect
