import Challenge.Ripemd160.Reference.Proofs.Bytecode.Main
import Challenge.Ripemd160.Reference.Proofs.Bytecode.Word
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
  interval_cases i <;> native_decide

private theorem initialized_rP (i : Nat) (hi : i < 80) :
    tableByte initializedMemory 0x500 i =
      UInt256.ofNat (Crypto.Ripemd160.rP[i]!) := by
  interval_cases i <;> native_decide

private theorem initialized_s (i : Nat) (hi : i < 80) :
    tableByte initializedMemory 0x560 i =
      UInt256.ofNat (Crypto.Ripemd160.s[i]!) := by
  interval_cases i <;> native_decide

private theorem initialized_sP (i : Nat) (hi : i < 80) :
    tableByte initializedMemory 0x5c0 i =
      UInt256.ofNat (Crypto.Ripemd160.sP[i]!) := by
  interval_cases i <;> native_decide

private theorem initialized_k (j : Nat) (hj : j < 5) :
    slotWord initializedMemory 0x620 j =
      ofUInt32 (Crypto.Ripemd160.K[j]!) := by
  interval_cases j <;> native_decide

private theorem initialized_kP (j : Nat) (hj : j < 5) :
    slotWord initializedMemory 0x6c0 j =
      ofUInt32 (Crypto.Ripemd160.KP[j]!) := by
  interval_cases j <;> native_decide

private theorem initialized_h (i : Nat) (hi : i < 5) :
    slotWord initializedMemory 0x020 i =
      ofUInt32 (Crypto.Ripemd160.H0[i]!) := by
  interval_cases i <;> native_decide

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
