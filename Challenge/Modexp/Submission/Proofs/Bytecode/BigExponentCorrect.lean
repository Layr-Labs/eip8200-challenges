import Challenge.Modexp.Submission.Proofs.Bytecode.BitPrefix
import Challenge.Modexp.Submission.Proofs.Bytecode.BigComplete
import Challenge.Modexp.Submission.Proofs.Bytecode.ExpCore
import Challenge.Modexp.Submission.Proofs.Bytecode.WordCorrect
set_option warningAsError true
set_option maxRecDepth 20000
set_option maxHeartbeats 3000000
set_option linter.unusedSimpArgs false
/-! # Functional correctness of multi-limb exponentiation -/

namespace Challenge.Modexp.Submission.Proofs.Bytecode.BigExponentCorrect

open EvmSemantics
open EvmSemantics.EVM

open ExpCore

theorem exponentBit_toNat_le_one (byte : UInt256) (j : Nat) :
    (exponentBit byte j).toNat ≤ 1 := by
  rw [exponentBit, Challenge.EvmProof.Word.word_toNat_land,
    show (1 : UInt256).toNat = 1 by decide]
  exact Nat.and_le_right

theorem readWord_copyMemory_self (memory : ByteArray) (ptr count j : Nat)
    (hj : j < count) (hfit : ptr + 32 * count < 2 ^ 256) :
    MachineState.readWord
        (BigHelpers.copyMemory memory (UInt256.ofNat ptr)
          (UInt256.ofNat ptr) count) (ptr + 32 * j) =
      MachineState.readWord memory (ptr + 32 * j) := by
  induction count with
  | zero => omega
  | succ count ih =>
      rw [BigHelpers.copyMemory]
      by_cases hjlast : j = count
      · subst j
        rw [BigHelpers.clearOffset_toNat ptr count (by omega),
          Challenge.EvmProof.Memory.readWord_writeWord]
        by_cases hzero : count = 0
        · subst count
          rfl
        · exact BigHelpers.readWord_copyMemory_disjoint_region memory ptr ptr
            (ptr + 32 * count) count count 0 (by omega) (by omega)
            (by omega) (Or.inl (by omega))
      · rw [Challenge.EvmProof.Memory.readWord_writeBytes_disjoint]
        · exact ih (by omega) (by omega)
        · left
          rw [BigHelpers.clearOffset_toNat ptr count (by omega)]
          omega

theorem copyMemory_self_represents (memory : ByteArray) (ptr count value : Nat)
    (hfit : ptr + 32 * count < 2 ^ 256)
    (hrep : Limbs.Represents memory ptr count value) :
    Limbs.Represents
      (BigHelpers.copyMemory memory (UInt256.ofNat ptr) (UInt256.ofNat ptr)
        count) ptr count value := by
  refine ⟨hrep.1, ?_⟩
  rw [← hrep.2]
  unfold Limbs.memoryLimbs
  apply List.map_congr_left
  intro j hj
  exact congrArg UInt256.toNat
    (readWord_copyMemory_self memory ptr count j (by simpa using hj) hfit)

theorem exponentBit_toNat_eq (byte : UInt256) (j : Nat) (hj : j < 8) :
    (exponentBit byte j).toNat = BitPrefix.exponentBitNat byte j := by
  have h := congrArg UInt256.toNat (BitPrefix.exponentBit_eq byte j hj)
  have hbit := BitPrefix.exponentBitNat_zero_or_one byte j
  rw [Challenge.EvmProof.Word.word_toNat_ofNat,
    Nat.mod_eq_of_lt (by omega : BitPrefix.exponentBitNat byte j < 2 ^ 256)]
    at h
  exact h

theorem loadedExponentByte_lt (s : State) (expOff i : Nat) :
    (loadedExponentByte s expOff i).toNat < 256 := by
  unfold loadedExponentByte UInt256.byteAt
  rw [show (0 : UInt256).toNat = 0 by decide]
  rw [if_neg (by omega)]
  rw [Challenge.EvmProof.Word.word_toNat_ofNat]
  have hand :
      ((MachineState.readWord s.executionEnv.calldata (expOff + i)).toNat >>>
        (8 * (31 - 0))) &&& 255 ≤ 255 := Nat.and_le_right
  have hlt :
      ((MachineState.readWord s.executionEnv.calldata (expOff + i)).toNat >>>
        (8 * (31 - 0))) &&& 255 < 2 ^ 256 := by omega
  rw [Nat.mod_eq_of_lt hlt]
  omega

def exponentValueAfter (s : State) (modulus base expOff : Nat) :
    Nat → Nat → Nat
  | 0, acc => acc
  | i + 1, acc =>
      BitPrefix.natExpStep modulus (loadedExponentByte s expOff i)
        (exponentValueAfter s modulus base expOff i acc) base

theorem exponentValueAfter_lt (s : State) (modulus base expOff steps acc : Nat)
    (hmodulusPos : 0 < modulus) (hacc : acc < modulus) :
    exponentValueAfter s modulus base expOff steps acc < modulus := by
  induction steps with
  | zero => exact hacc
  | succ steps ih =>
      rw [exponentValueAfter, BitPrefix.natExpStep]
      exact Nat.mod_lt _ hmodulusPos


/-- `ExpCore`'s operational accumulator agrees with the reference's
`exponentValueAfter`: both compute `base ^ (exponent prefix) mod modulus`, one
by square-and-multiply with a `started` flag, the other by `acc^256 * base^byte`
per byte. -/
theorem accAfterBytes_eq_exponentValueAfter (s : State) (modulus base : Nat)
    (hmod : 0 < modulus) (hbase : base < modulus) (expOff : Nat)
    (hbytes : ∀ k, (ExpCore.byteAt s expOff k).toNat < 256) (i : Nat) :
    ExpCore.accAfterBytes s modulus base expOff 0 (base ^ 0 % modulus) i
      = exponentValueAfter s modulus base expOff i (base ^ 0 % modulus) := by
  have hspec := ExpCore.accAfterBytes_spec s modulus base hmod hbase expOff hbytes
  induction i with
  | zero => rfl
  | succ i ih =>
      rw [(hspec (i + 1)).1]
      show _ = BitPrefix.natExpStep modulus (loadedExponentByte s expOff i)
        (exponentValueAfter s modulus base expOff i (base ^ 0 % modulus)) base
      rw [← ih, (hspec i).1]
      unfold BitPrefix.natExpStep
      show base ^ (256 * ExpCore.expValueAfter s expOff i
        + (ExpCore.byteAt s expOff i).toNat) % modulus = _
      rw [pow_add, pow_mul']
      conv_rhs => rw [Nat.mul_mod, ← Nat.pow_mod, ← Nat.mul_mod]
      rfl

theorem exponentByteProgress_represents (s : State)
    (accumulatorWord : UInt256) (count b e m baseOff expOff : Nat)
    (rest : List UInt256) (steps acc base modulus : Nat) (_hsteps : steps ≤ e)
    (hcount : count ≤ 32) (hmodulusPos : 0 < modulus)
    (haccReduced : acc < modulus) (hbaseReduced : base < modulus)
    (hmodulusBound : modulus < Limbs.radix ^ count)
    (hacc : Limbs.Represents s.memory 2048 count acc)
    (hbase : Limbs.Represents s.memory 1024 count base)
    (hmodulus : Limbs.Represents s.memory 0 count modulus) :
    let progress := ExpCore.bytesState s accumulatorWord count b e m baseOff
      expOff rest 0 steps
    Limbs.Represents progress.memory 2048 count
        (ExpCore.accAfterBytes s modulus base expOff 0 acc steps) ∧
      Limbs.Represents progress.memory 1024 count base ∧
      Limbs.Represents progress.memory 0 count modulus := by
  obtain ⟨h1, h2, h3, _⟩ := ExpCore.bytesState_represents s accumulatorWord count
    b e m baseOff expOff rest 0 steps (by omega) hcount acc base modulus
    hmodulusPos hmodulusBound haccReduced hbaseReduced hacc hbase hmodulus
  exact ⟨h1, h2, h3⟩

theorem loadedExponentByte_header (input : ByteArray) (i : Nat)
    (hoff : Word.expOffset input + i < 2 ^ 256) :
    loadedExponentByte (Main.headerState input) (Word.expOffset input) i =
      BitPrefix.exponentByte input i := by
  unfold loadedExponentByte BitPrefix.exponentByte Word.byteWord
    Accessors.calldataByteValue
  rw [Challenge.EvmProof.Word.word_toNat_ofNat, Nat.mod_eq_of_lt hoff]
  rfl

theorem exponentValueAfter_executionEnv (s t : State)
    (modulus base expOff steps acc : Nat) (henv : s.executionEnv = t.executionEnv) :
    exponentValueAfter s modulus base expOff steps acc =
      exponentValueAfter t modulus base expOff steps acc := by
  induction steps with
  | zero => rfl
  | succ steps ih =>
      have hbyte : loadedExponentByte s expOff steps =
          loadedExponentByte t expOff steps := by
        unfold loadedExponentByte
        rw [henv]
      rw [exponentValueAfter, exponentValueAfter, ih, hbyte]

theorem exponentValueAfter_header_eq_natExpAfter (input : ByteArray)
    (modulus base steps acc : Nat)
    (hoff : Word.expOffset input + steps < 2 ^ 256) :
    exponentValueAfter (Main.headerState input) modulus base
        (Word.expOffset input) steps acc =
      BitPrefix.natExpAfter input modulus base steps acc := by
  induction steps with
  | zero => rfl
  | succ steps ih =>
      rw [exponentValueAfter, BitPrefix.natExpAfter, ih (by omega),
        loadedExponentByte_header input steps (by omega)]

theorem exponentValueAfter_header_eq (input : ByteArray)
    (modulus base acc : Nat) (hvalid : ValidInput input)
    (hacc : acc < modulus) :
    exponentValueAfter (Main.headerState input) modulus base
        (Word.expOffset input) (exponentSize input) acc =
      (acc ^ (256 ^ exponentSize input) *
        base ^ (Precompile.bytesToNatPadded input (Word.expOffset input)
          (exponentSize input))) % modulus := by
  have hoff : Word.expOffset input + exponentSize input < 2 ^ 256 := by
    rcases hvalid with ⟨_, hb, he, _⟩
    simp only [Word.expOffset]
    omega
  rw [exponentValueAfter_header_eq_natExpAfter input modulus base
    (exponentSize input) acc hoff]
  exact BitPrefix.natExpAfter_eq input modulus base acc
    (exponentSize input) hvalid (by omega) hacc

end Challenge.Modexp.Submission.Proofs.Bytecode.BigExponentCorrect
