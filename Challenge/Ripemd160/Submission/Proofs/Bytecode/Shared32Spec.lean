import Challenge.Ripemd160.Submission.Proofs.Bytecode.Shared32Table
import Challenge.Ripemd160.Submission.Proofs.Bytecode.PaddedBlockBridge
import Challenge.Ripemd160.Submission.Proofs.Bytecode.CompressionCorrect

set_option warningAsError true
set_option maxRecDepth 20000
set_option maxHeartbeats 3000000
set_option linter.unusedSimpArgs false

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.Shared32Spec
open EvmSemantics EvmSemantics.EVM Challenge.EvmProof
open Shared32Scratch Shared32Table

theorem readLE32_congr (a b : ByteArray) (x y : Nat)
    (h : ∀ i, i < 4 → a[x + i]?.getD 0 = b[y + i]?.getD 0) :
    Crypto.Ripemd160.readLE32 a x = Crypto.Ripemd160.readLE32 b y := by
  have hb (m : ByteArray) (j : Nat) :
      (if h : j < m.size then m[j].toUInt32 else 0) = (m[j]?.getD 0).toUInt32 := by
    by_cases hj : j < m.size <;> simp [hj]
  apply HashSpecBridge.readLE32_eq_of_byte
  intro i hi
  rw [hb, hb, h i hi]

theorem padded_lower (input : ByteArray) (j : Nat) (hj : j < input.size) :
    (Padding.paddedMessage input)[j]?.getD 0 = input[j]?.getD 0 := by
  simp only [Padding.paddedMessage, Memory.getElem?_getD_append, ByteArray.size_append]
  rw [if_pos (by omega), if_pos (by omega), if_pos hj]

theorem padded_upper (input : ByteArray) (h32 : input.size = 32)
    (j : Nat) (hj : j < 32) :
    (Padding.paddedMessage input)[32 + j]?.getD 0 =
      if j = 0 then 128 else if j = 25 then 1 else 0 := by
  have hz : Padding.zeroBytes input.size = ByteArray.mk (Array.replicate 23 0) := by
    rw [Padding.zeroBytes, Padding.zeroCount, h32]
    rfl
  have hf : Padding.lengthBytes input = ByteArray.mk #[0, 1, 0, 0, 0, 0, 0, 0] := by
    apply ByteArray.ext_getElem
    · rw [Padding.lengthBytes_size]; rfl
    · intro i ha hb
      have hi : i < 8 := hb
      rw [Padding.lengthByte input i hi, h32]
      interval_cases i <;> rfl
  rw [Padding.paddedMessage, hz, hf]
  simp only [Memory.getElem?_getD_append, ByteArray.size_append, h32,
    show (ByteArray.mk #[128]).size = 1 by rfl,
    show (ByteArray.mk (Array.replicate 23 0)).size = 23 by rfl]
  interval_cases j <;> norm_num <;> rfl

theorem copied_lower_read (input : ByteArray) (h32 : input.size = 32)
    (k : Nat) (hk : k < 8) :
    Crypto.Ripemd160.readLE32 (copiedMemory input) (1056 + 4 * k) =
      Crypto.Ripemd160.readLE32 (Padding.paddedMessage input) (4 * k) := by
  apply readLE32_congr
  intro i hi
  rw [padded_lower input _ (by omega)]
  simp only [copiedMemory, MachineState.writeBytes_getElem?_getD]
  rw [if_pos (by omega)]
  congr 2
  omega

theorem extracted_readLE32 (memory : ByteArray) (k : Nat) (hk : k < 16) :
    PairedScheduleData.extractedWord memory 1056 k =
      Word.ofUInt32 (Crypto.Ripemd160.readLE32 memory (1056 + 4 * k)) := by
  rw [PairedScheduleData.extractedWord_eq_expectedWord _ _ _ hk (by omega)]
  have hp : Schedule.loadOffsetWord (UInt256.ofNat 1056) k =
      UInt256.ofNat (1056 + 4 * k) := by
    apply Word.word_ext
    rw [PairedScheduleData.loadOffsetWord_toNat _ _ hk (by omega),
      Word.word_toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  change Word.mask32 (Schedule.readLEWord memory (Schedule.loadOffsetWord (UInt256.ofNat 1056) k)) = _
  rw [hp]
  exact PaddedBlockBridge.mask32_readLEWord_eq_readLE32 _ _ (by omega)

theorem upper_readLE32 (input : ByteArray) (h32 : input.size = 32)
    (k : Nat) (hk0 : 8 ≤ k) (hk1 : k < 16) :
    Crypto.Ripemd160.readLE32 (Padding.paddedMessage input) (4 * k) =
      UInt32.ofNat (highScalar k) := by
  let upper : ByteArray := ByteArray.mk #[128, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0]
  have hc : Crypto.Ripemd160.readLE32 (Padding.paddedMessage input) (4 * k) =
      Crypto.Ripemd160.readLE32 upper (4 * k - 32) := by
    apply readLE32_congr
    intro i hi
    have ha : 4 * k + i = 32 + (4 * k - 32 + i) := by omega
    rw [ha, padded_upper input h32 _ (by omega)]
    have hbyte (j : Nat) (hj : j < 32) :
        upper[j]?.getD 0 = if j = 0 then 128 else if j = 25 then 1 else 0 := by
      interval_cases j <;> rfl
    rw [hbyte _ (by omega)]
  rw [hc]
  interval_cases k <;>
    simp only [Crypto.Ripemd160.readLE32, Std.Legacy.Range.forIn_eq_forIn_range',
      Std.Legacy.Range.size, Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one,
      pure_bind, List.forIn_pure_yield_eq_foldl, Id.run_pure,
      List.range', List.foldl_cons, List.foldl_nil] <;>
      norm_num [upper, ByteArray.size, highScalar, ByteArray.getElem_eq_getElem_data] <;> rfl

theorem scalars_schedule (input : ByteArray) (h32 : input.size = 32)
    (k : Nat) (hk : k < 16) :
    scalars (copiedMemory input) k =
      (CompressionCorrect.schedule (Padding.paddedMessage input) 0)[k]! := by
  have hs : (CompressionCorrect.schedule (Padding.paddedMessage input) 0)[k]! =
      Crypto.Ripemd160.readLE32 (Padding.paddedMessage input) (4 * k) := by
    interval_cases k <;> simp [CompressionCorrect.schedule, List.range']
  rw [hs]
  by_cases hl : k < 8
  · rw [scalars, if_pos hl, extracted_readLE32 _ k hk,
      Word.ofUInt32_toNat, UInt32.ofNat_toNat, copied_lower_read input h32 k hl]
  · rw [scalars, if_neg hl, upper_readLE32 input h32 k (by omega) hk]

theorem scalars_schedule_all (input : ByteArray) (h32 : input.size = 32) :
    scalars (copiedMemory input) =
      fun k => (CompressionCorrect.schedule (Padding.paddedMessage input) 0)[k]! := by
  funext k
  by_cases hk : k < 16
  · exact scalars_schedule input h32 k hk
  · have hs : (CompressionCorrect.schedule (Padding.paddedMessage input) 0).size = 16 := by
      simp [CompressionCorrect.schedule, List.range']
    rw [getElem!_neg _ _ (by omega)]
    simp only [scalars, if_neg (by omega : ¬k < 8), highScalar,
      if_neg (by omega : k ≠ 8), if_neg (by omega : k ≠ 14)]
    rfl

theorem ready_spec (input : ByteArray) (h32 : input.size = 32) :
    StaggerMessage.Ready
      (StaggerTableLayout.resultMemory (copiedMemory input) (words (copiedMemory input)))
      (fun k => (CompressionCorrect.schedule (Padding.paddedMessage input) 0)[k]!) := by
  rw [← scalars_schedule_all input h32]
  exact table_ready _

#print axioms scalars_schedule
#print axioms ready_spec
end Challenge.Ripemd160.Submission.Proofs.Bytecode.Shared32Spec
