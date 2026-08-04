import Challenge.Modexp.Reference.Proofs.Bytecode.BigComplete
import Challenge.Modexp.Reference.Proofs.Bytecode.WordCorrect
set_option warningAsError true
set_option maxRecDepth 20000
set_option maxHeartbeats 3000000
set_option linter.unusedSimpArgs false
/-! # Functional correctness of multi-limb exponentiation -/

namespace Challenge.Modexp.Reference.Proofs.Bytecode.BigExponentCorrect

open EvmSemantics
open EvmSemantics.EVM

open BigExponent

theorem exponentBit_toNat_le_one (byte : UInt256) (j : Nat) :
    (exponentBit byte j).toNat ≤ 1 := by
  rw [exponentBit, Challenge.EvmProof.Word.word_toNat_land,
    show (1 : UInt256).toNat = 1 by decide]
  exact Nat.and_le_right

theorem selectOffset_eq (ptr k : Nat) (hfit : ptr + 32 * k < 2 ^ 256) :
    (UInt256.ofNat ptr + selectOffset k).toNat = ptr + 32 * k := by
  rw [selectOffset]
  have hcomm : UInt256.ofNat ptr +
      UInt256.shiftLeft (UInt256.ofNat k) (UInt256.ofNat 5) =
      BigHelpers.clearOffset (UInt256.ofNat ptr) k := by
    simpa only [BigHelpers.clearOffset] using
      (Challenge.EvmProof.Word.word_add_comm (UInt256.ofNat ptr)
        (UInt256.shiftLeft (UInt256.ofNat k) (UInt256.ofNat 5)))
  rw [hcomm, BigHelpers.clearOffset_toNat ptr k hfit]

theorem selectMemory_zero (memory : ByteArray) (count : Nat)
    (hcount : count ≤ 32) :
    selectMemory memory (0 - UInt256.ofNat 0) count =
      BigHelpers.copyMemory memory (UInt256.ofNat 2048) (UInt256.ofNat 2048)
        count := by
  induction count with
  | zero => rfl
  | succ count ih =>
      rw [selectMemory, BigHelpers.copyMemory, ih (by omega)]
      simp only [selectedWord]
      have hz : (0 : UInt256) = UInt256.ofNat 0 := by decide
      rw [hz]
      rw [WordCorrect.select_zero]
      have h2048 : (2048 : UInt256) = UInt256.ofNat 2048 := by decide
      rw [h2048]
      rw [selectOffset_eq 2048 count (by omega),
        BigHelpers.clearOffset_toNat 2048 count (by omega)]

theorem selectMemory_one (memory : ByteArray) (count : Nat)
    (hcount : count ≤ 32) :
    selectMemory memory (0 - UInt256.ofNat 1) count =
      BigHelpers.copyMemory memory (UInt256.ofNat 2048) (UInt256.ofNat 3072)
        count := by
  induction count with
  | zero => rfl
  | succ count ih =>
      rw [selectMemory, BigHelpers.copyMemory, ih (by omega)]
      simp only [selectedWord]
      have hz : (0 : UInt256) = UInt256.ofNat 0 := by decide
      rw [hz]
      rw [WordCorrect.select_one]
      have h2048 : (2048 : UInt256) = UInt256.ofNat 2048 := by decide
      have h3072 : (3072 : UInt256) = UInt256.ofNat 3072 := by decide
      rw [h2048, h3072]
      rw [selectOffset_eq 3072 count (by omega),
        BigHelpers.clearOffset_toNat 3072 count (by omega),
        selectOffset_eq 2048 count (by omega),
        BigHelpers.clearOffset_toNat 2048 count (by omega)]

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

theorem selectMemory_represents (memory : ByteArray) (byte : UInt256)
    (j count square product : Nat) (hcount : count ≤ 32)
    (hsquare : Limbs.Represents memory 2048 count square)
    (hproduct : Limbs.Represents memory 3072 count product) :
    Limbs.Represents
      (selectMemory memory (selectMask byte j) count) 2048 count
      (if (exponentBit byte j).toNat = 0 then square else product) := by
  have hbit := exponentBit_toNat_le_one byte j
  have hword : UInt256.ofNat (exponentBit byte j).toNat =
      exponentBit byte j := WordCorrect.ofNat_toNat _
  interval_cases h : (exponentBit byte j).toNat
  · simp only [if_pos rfl]
    rw [selectMask, ← hword, selectMemory_zero memory count hcount]
    exact copyMemory_self_represents memory 2048 count square (by omega) hsquare
  · rw [selectMask, ← hword, selectMemory_one memory count hcount]
    exact BigHelpers.copyMemory_represents memory 2048 3072 count product
      hproduct (by omega) (by omega) (Or.inl (by omega))

end Challenge.Modexp.Reference.Proofs.Bytecode.BigExponentCorrect
