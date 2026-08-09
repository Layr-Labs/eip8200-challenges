import Challenge.Modexp.Submission.Proofs.Bytecode.BitPrefix
import Challenge.Modexp.Submission.Proofs.Bytecode.BigCorrect
set_option warningAsError true
set_option maxRecDepth 20000
set_option maxHeartbeats 3000000
set_option linter.unusedSimpArgs false
/-! # Functional correctness of multi-limb result serialization -/

namespace Challenge.Modexp.Submission.Proofs.Bytecode.BigSerializeCorrect

open EvmSemantics
open EvmSemantics.EVM

theorem getElem_eq_div_mod_ofDigits (radix : Nat) (digits : List Nat)
    (index : Nat) (hradix : 0 < radix) (hindex : index < digits.length)
    (hdigits : ∀ digit ∈ digits, digit < radix) :
    digits[index] = Nat.ofDigits radix digits / radix ^ index % radix := by
  rw [Nat.ofDigits_div_pow_eq_ofDigits_drop index hradix digits hdigits]
  rw [List.drop_eq_getElem_cons hindex]
  simp only [Nat.ofDigits_cons]
  rw [Nat.add_mul_mod_self_left,
    Nat.mod_eq_of_lt (hdigits digits[index] (List.getElem_mem hindex))]

theorem readLimb_of_represents {memory : ByteArray} {ptr count value index : Nat}
    (hrep : Limbs.Represents memory ptr count value) (hindex : index < count) :
    (MachineState.readWord memory (ptr + 32 * index)).toNat =
      value / Limbs.radix ^ index % Limbs.radix := by
  have hget := getElem_eq_div_mod_ofDigits Limbs.radix
    (Limbs.memoryLimbs memory ptr count) index Limbs.radix_pos
    (by simpa using hindex)
    (fun digit hdigit => Limbs.memoryLimb_lt memory ptr count hdigit)
  rw [Limbs.value_of_represents hrep] at hget
  simpa [Limbs.memoryLimbs] using hget

theorem serializerLimb_eq (m k : Nat) (hm : m < 2 ^ 256) (hk : k < m) :
    BigSerialize.serializerLimb m k =
      UInt256.ofNat (BigLoad.loadLimb m k) := by
  change BigLoad.loadLimbWord (UInt256.ofNat m) k = _
  exact BigLoadCorrect.loadLimbWord_ofNat m k hm hk

theorem serializerShift_eq (m k : Nat) (hm : m < 2 ^ 256) (hk : k < m) :
    BigSerialize.serializerShift m k =
      UInt256.ofNat (BigLoad.loadShift m k) := by
  change BigLoad.loadShiftWord (UInt256.ofNat m) k = _
  exact BigLoadCorrect.loadShiftWord_ofNat m k hm hk

theorem extractedLimbByte (value limb rem : Nat) (hrem : rem < 32) :
    ((value / Limbs.radix ^ limb % Limbs.radix) / 256 ^ rem) % 256 =
      value / 256 ^ (32 * limb + rem) % 256 := by
  have hradix : Limbs.radix = 256 ^ 32 := Limbs.radix_eq
  let head := value / 256 ^ (32 * limb)
  have hsplit : 256 ^ 32 = 256 ^ rem * 256 ^ (32 - rem) := by
    rw [← Nat.pow_add]
    congr 1
    omega
  have hdiv : value / 256 ^ (32 * limb) / 256 ^ rem =
      value / 256 ^ (32 * limb + rem) := by
    rw [Nat.div_div_eq_div_mul, ← Nat.pow_add]
  rw [hradix]
  rw [show (256 ^ 32) ^ limb = 256 ^ (32 * limb) by
    rw [Nat.pow_mul]]
  change ((head % 256 ^ 32) / 256 ^ rem) % 256 = _
  rw [hsplit, Nat.mod_mul_right_div_self]
  have hdvd : 256 ∣ 256 ^ (32 - rem) := by
    exact dvd_pow_self 256 (by omega)
  rw [Nat.mod_mod_of_dvd _ hdvd]
  exact congrArg (fun n => n % 256) hdiv

theorem serializedByte_correct (memory : ByteArray) (m k value : Nat)
    (hmBound : m ≤ 1024) (hk : k < m)
    (hrep : Limbs.Represents memory 2048 (Limbs.limbCount m) value) :
    (BigSerialize.serializedByte memory m k).toNat =
      value / 256 ^ (m - 1 - k) % 256 := by
  let reverse := m - 1 - k
  let limb := BigLoad.loadLimb m k
  let rem := BigLoad.loadReverse m k % 32
  have hm : m < 2 ^ 256 := by omega
  have hlimb : limb < Limbs.limbCount m := by
    simp only [limb, BigLoad.loadLimb, BigLoad.loadReverse, Limbs.limbCount]
    omega
  have hn : Limbs.limbCount m ≤ 32 := Limbs.limbCount_le_32 m hmBound
  have hrem : rem < 32 := by
    exact Nat.mod_lt _ (by omega)
  have haddr : (UInt256.ofNat 2048 +
      UInt256.shiftLeft (UInt256.ofNat limb) (UInt256.ofNat 5)).toNat =
      2048 + 32 * limb := BigHelpers.addOffset_toNat 2048 limb (by omega)
  have hword := readLimb_of_represents hrep hlimb
  have h2048 : (2048 : UInt256) = UInt256.ofNat 2048 := by decide
  have hshift : BigLoad.loadShift m k = 8 * rem := by
    simp [BigLoad.loadShift, rem]
  have hshiftLt : BigLoad.loadShift m k < 256 := by omega
  have hrecompose : 32 * (reverse / 32) + reverse % 32 = reverse := by
    have h := Nat.mod_add_div reverse 32
    omega
  unfold BigSerialize.serializedByte
  rw [serializerLimb_eq m k hm hk, serializerShift_eq m k hm hk, h2048,
    haddr, Challenge.EvmProof.Word.word_toNat_land,
    Challenge.EvmProof.Word.shiftRight_toNat _ hshiftLt,
    Challenge.EvmProof.Word.word_toNat_ofNat,
    Nat.mod_eq_of_lt (by norm_num : 255 < 2 ^ 256)]
  rw [show (255 : Nat) = 2 ^ 8 - 1 by norm_num,
    Nat.and_two_pow_sub_one_eq_mod, Nat.shiftRight_eq_div_pow]
  rw [hshift, show 2 ^ (8 * rem) = 256 ^ rem by
    rw [show (256 : Nat) = 2 ^ 8 by norm_num, Nat.pow_mul]]
  rw [hword]
  simpa [limb, rem, reverse, BigLoad.loadLimb, BigLoad.loadReverse,
    hrecompose] using
    extractedLimbByte value limb rem hrem

theorem serializeMemory_preserves_represents (memory : ByteArray)
    (m steps value : Nat) (hmBound : m ≤ 1024) (hsteps : steps ≤ m)
    (hrep : Limbs.Represents memory 2048 (Limbs.limbCount m) value) :
    Limbs.Represents (BigSerialize.serializeMemory memory m steps) 2048
      (Limbs.limbCount m) value := by
  induction steps with
  | zero => simpa [BigSerialize.serializeMemory] using hrep
  | succ steps ih =>
      let before := BigSerialize.serializeMemory memory m steps
      let byte := ByteArray.mk
        #[UInt8.ofNat ((BigSerialize.serializedByte before m steps).toNat % 256)]
      have hsteps' : steps ≤ m := by omega
      have hbefore := ih hsteps'
      have haddr : (6144 + UInt256.ofNat steps).toNat = 6144 + steps := by
        change (UInt256.ofNat 6144 + UInt256.ofNat steps).toNat = 6144 + steps
        rw [Challenge.EvmProof.Word.ofNat_add_ofNat (by omega),
          Challenge.EvmProof.Word.word_toNat_ofNat,
          Nat.mod_eq_of_lt (by omega)]
      have hmemory : BigSerialize.serializeMemory memory m (steps + 1) =
          MachineState.writeBytes before byte
            (6144 + UInt256.ofNat steps).toNat := by
        rfl
      refine ⟨hbefore.1, ?_⟩
      rw [← hbefore.2]
      rw [hmemory]
      unfold Limbs.memoryLimbs
      apply List.map_congr_left
      intro j hj
      have hj' : j < Limbs.limbCount m := by simpa using hj
      apply congrArg UInt256.toNat
      rw [Challenge.EvmProof.Memory.readWord_writeBytes_disjoint]
      left
      rw [haddr]
      have hn := Limbs.limbCount_le_32 m hmBound
      omega

theorem serializeMemory_outputByte (memory : ByteArray)
    (m steps k value : Nat) (hmBound : m ≤ 1024) (hsteps : steps ≤ m)
    (hk : k < steps)
    (hrep : Limbs.Represents memory 2048 (Limbs.limbCount m) value) :
    (BigSerialize.serializeMemory memory m steps)[6144 + k]?.getD 0 =
      UInt8.ofNat (value / 256 ^ (m - 1 - k) % 256) := by
  induction steps with
  | zero => omega
  | succ steps ih =>
      let before := BigSerialize.serializeMemory memory m steps
      let byte := ByteArray.mk
        #[UInt8.ofNat ((BigSerialize.serializedByte before m steps).toNat % 256)]
      have hsteps' : steps ≤ m := by omega
      have haddr : (6144 + UInt256.ofNat steps).toNat = 6144 + steps := by
        change (UInt256.ofNat 6144 + UInt256.ofNat steps).toNat = 6144 + steps
        rw [Challenge.EvmProof.Word.ofNat_add_ofNat (by omega),
          Challenge.EvmProof.Word.word_toNat_ofNat,
          Nat.mod_eq_of_lt (by omega)]
      have hmemory : BigSerialize.serializeMemory memory m (steps + 1) =
          MachineState.writeBytes before byte
            (6144 + UInt256.ofNat steps).toNat := by
        rfl
      rw [hmemory, MachineState.writeBytes_getElem?_getD, haddr]
      by_cases hlast : k = steps
      · subst k
        rw [if_pos (by
          constructor
          · omega
          · simp [byte, ByteArray.size])]
        have hbefore := serializeMemory_preserves_represents memory m steps
          value hmBound hsteps' hrep
        have hbyte := serializedByte_correct before m steps value hmBound
          (by omega) (by simpa [before] using hbefore)
        simp [byte, hbyte]
        rfl
      · rw [if_neg (by
          have : k < steps := by omega
          simp [byte, ByteArray.size]
          omega)]
        exact ih hsteps' (by omega)

theorem serializeMemory_readPadded (memory : ByteArray) (m value : Nat)
    (hmBound : m ≤ 1024)
    (hrep : Limbs.Represents memory 2048 (Limbs.limbCount m) value) :
    MachineState.readPadded (BigSerialize.serializeMemory memory m m) 6144 m =
      Precompile.natToBytes value m := by
  apply ByteArray.ext_getElem
  · rw [Challenge.EvmProof.Memory.readPadded_size, Precompile.natToBytes,
      YulEvmCompiler.BytesLemmas.natToBytesPadded_size]
  · intro k hleft hright
    have hk : k < m := by
      simpa [Precompile.natToBytes,
        YulEvmCompiler.BytesLemmas.natToBytesPadded_size] using hright
    rw [← Challenge.EvmProof.Memory.getD0_eq_getElem _ _ hleft,
      ← Challenge.EvmProof.Memory.getD0_eq_getElem _ _ hright,
      Challenge.EvmProof.Memory.readPadded_getElem?_getD,
      if_pos hk,
      serializeMemory_outputByte memory m m k value hmBound (by omega) hk hrep,
      Precompile.natToBytes,
      YulEvmCompiler.BytesLemmas.natToBytesPadded_getElem?_getD value m k hk]

theorem completedState_hReturn (input : ByteArray) (returnDest : UInt256)
    (rest : List UInt256) (hvalid : ValidInput input)
    (hbig : 32 < modulusSize input)
    (hmodulusPos : 0 < Word.modulusValue input) :
    (BigComplete.completedState (Main.headerState input) (baseSize input)
      (exponentSize input) (modulusSize input) 96 (Word.expOffset input)
      (Word.modulusOffset input) returnDest rest).hReturn = spec input := by
  let m := modulusSize input
  let result := Precompile.modPow (BitPrefix.baseNat input)
    (BitPrefix.exponentNat input) (Word.modulusValue input)
  let progress := BigComplete.exponentProgressState (Main.headerState input)
    (baseSize input) (exponentSize input) m 96 (Word.expOffset input)
    (Word.modulusOffset input) returnDest rest
  have hm : m ≤ 1024 := by simpa [m] using hvalid.2.2.2
  have hrep : Limbs.Represents progress.memory 2048
      (Limbs.limbCount m) result := by
    simpa [progress, m, result] using
      BigCorrect.exponentProgress_represents_result input returnDest rest
        hvalid hbig hmodulusPos
  have hserialized := serializeMemory_readPadded progress.memory m result hm hrep
  rw [spec, if_neg (by omega)]
  simpa [BigComplete.completedState, BigSerialize.bigReturned,
    BigSerialize.serializeProgress, progress, m, result,
    BitPrefix.baseNat, BitPrefix.exponentNat, Word.expOffset,
    Word.modulusOffset, Word.modulusValue] using hserialized

theorem completedState_result (input : ByteArray) (returnDest : UInt256)
    (rest : List UInt256) (hvalid : ValidInput input)
    (hbig : 32 < modulusSize input)
    (hmodulusPos : 0 < Word.modulusValue input) :
    (BigComplete.completedState (Main.headerState input) (baseSize input)
      (exponentSize input) (modulusSize input) 96 (Word.expOffset input)
      (Word.modulusOffset input) returnDest rest).toResult =
        .returned (spec input) := by
  rw [State.toResult_returned _ (by rfl),
    completedState_hReturn input returnDest rest hvalid hbig hmodulusPos]

end Challenge.Modexp.Submission.Proofs.Bytecode.BigSerializeCorrect
