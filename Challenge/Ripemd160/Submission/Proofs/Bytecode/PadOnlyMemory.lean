import Challenge.Ripemd160.Submission.Proofs.Bytecode.PadOnlySchedule
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.PadOnlySchedule
open EvmSemantics EvmSemantics.EVM YulEvmCompiler Challenge.EvmProof
open StackRoundTrace StackRoundTemplate PairedHelperBooleanTrace
open DenseScheduleTemplate PairedScheduleMemory PairedMask32Cache
def padWords (n : UInt256) (i : Nat) : UInt256 :=
  if i = 0 then UInt256.ofNat 128 else
  if i = 14 then lowLength n else
  if i = 15 then highLength n else UInt256.ofNat 0

private theorem zeroBytes_getD (i : Nat) : zeroBytes[i]?.getD 0 = 0 := by
  change (Array.replicate 512 (0 : UInt8))[i]?.getD 0 = 0
  by_cases hi : i < 512
  · rw [getElem?_pos _ _ (by simpa using hi)]
    simp
  · rw [getElem?_neg _ _ (by simpa using hi)]
    rfl

private theorem zeroWord_getD (i : Nat) (hi : i < 32) :
    (Data.Bytes.natToBytesPadded (UInt256.ofNat 0).toNat 32)[i]?.getD 0 = 0 := by
  rw [YulEvmCompiler.BytesLemmas.natToBytesPadded_getElem?_getD _ _ _ hi]
  simp

private theorem zeroBytes_size : zeroBytes.size = 512 := by rfl

private theorem getD_resultMemory (memory : ByteArray) (n : UInt256) (i : Nat) :
    (resultMemory memory n)[i]?.getD 0 =
      if 480 ≤ i ∧ i < 512 then (Data.Bytes.natToBytesPadded (highLength n).toNat 32)[i - 480]?.getD 0
      else if 448 ≤ i ∧ i < 480 then (Data.Bytes.natToBytesPadded (lowLength n).toNat 32)[i - 448]?.getD 0
      else if i < 32 then (Data.Bytes.natToBytesPadded (UInt256.ofNat 128).toNat 32)[i]?.getD 0
      else if i < 512 then 0 else memory[i]?.getD 0 := by
  simp [resultMemory, writeWord, MachineState.writeBytes_getElem?_getD,
    YulEvmCompiler.BytesLemmas.natToBytesPadded_size, zeroBytes_size, zeroBytes_getD]

private theorem memory_pointwise (memory : ByteArray) (n : UInt256)
    (hs : SentinelCore.SentinelOK memory) (i : Nat) :
    (normalizedMemory memory (padWords n))[i]?.getD 0 =
      (resultMemory memory n)[i]?.getD 0 := by
  simp only [normalizedMemory, storeCells, cell, padWords,
    writeWord, MachineState.writeBytes_getElem?_getD,
    YulEvmCompiler.BytesLemmas.natToBytesPadded_size,
    getD_resultMemory]
  norm_num only
  simp only [ScheduleLayout.perm_eval_0, ScheduleLayout.perm_eval_1,
    ScheduleLayout.perm_eval_2, ScheduleLayout.perm_eval_3,
    ScheduleLayout.perm_eval_4, ScheduleLayout.perm_eval_5,
    ScheduleLayout.perm_eval_6, ScheduleLayout.perm_eval_7,
    ScheduleLayout.perm_eval_8, ScheduleLayout.perm_eval_9,
    ScheduleLayout.perm_eval_10, ScheduleLayout.perm_eval_11,
    ScheduleLayout.perm_eval_12, ScheduleLayout.perm_eval_13,
    ScheduleLayout.perm_eval_14, ScheduleLayout.perm_eval_15,
    ScheduleLayout.perm_eval_16]
  norm_num only
  simp only [ite_true, ite_false]
  have hcases : i < 32 ∨ (32 ≤ i ∧ i < 64) ∨ (64 ≤ i ∧ i < 96) ∨ (96 ≤ i ∧ i < 128) ∨ (128 ≤ i ∧ i < 160) ∨ (160 ≤ i ∧ i < 192) ∨ (192 ≤ i ∧ i < 224) ∨ (224 ≤ i ∧ i < 256) ∨ (256 ≤ i ∧ i < 288) ∨ (288 ≤ i ∧ i < 320) ∨ (320 ≤ i ∧ i < 352) ∨ (352 ≤ i ∧ i < 384) ∨ (384 ≤ i ∧ i < 416) ∨ (416 ≤ i ∧ i < 448) ∨ (448 ≤ i ∧ i < 480) ∨ (480 ≤ i ∧ i < 512) ∨ (512 ≤ i ∧ i < 544) ∨ 544 ≤ i := by omega
  rcases hcases with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11 | h12 | h13 | h14 | h15 | h16 | h17
  all_goals
    repeat first
      | rw [if_pos (by omega)]
      | rw [if_neg (by omega)]
  all_goals try rfl
  all_goals try exact zeroWord_getD _ (by omega)
  all_goals
    rw [zeroWord_getD _ (by omega)]
    have hz := hs.2 (i - 512) (by omega)
    simpa [Nat.add_sub_of_le (show 512 ≤ i by omega)] using hz.symm

#print axioms memory_pointwise




private theorem bytes_ext_getD (a b : ByteArray)
    (hsize : a.size = b.size) (hget : ∀ i : Nat, a[i]?.getD 0 = b[i]?.getD 0) : a = b := by
  apply ByteArray.ext
  apply Array.ext
  · exact hsize
  · intro i hi₁ hi₂
    have h := hget i
    rw [getElem?_pos _ i hi₁, getElem?_pos _ i hi₂] at h
    exact h

theorem memory_equiv (memory : ByteArray) (n : UInt256)
    (hs : SentinelCore.SentinelOK memory) :
    normalizedMemory memory (padWords n) = resultMemory memory n := by
  have hsz := hs.1
  have hnorm : (normalizedMemory memory (padWords n)).size = memory.size := by
    simp only [normalizedMemory, storeCells, writeWord_size]
    simp only [cell, ScheduleLayout.perm_eval_0, ScheduleLayout.perm_eval_1,
      ScheduleLayout.perm_eval_2, ScheduleLayout.perm_eval_3,
      ScheduleLayout.perm_eval_4, ScheduleLayout.perm_eval_5,
      ScheduleLayout.perm_eval_6, ScheduleLayout.perm_eval_7,
      ScheduleLayout.perm_eval_8, ScheduleLayout.perm_eval_9,
      ScheduleLayout.perm_eval_10, ScheduleLayout.perm_eval_11,
      ScheduleLayout.perm_eval_12, ScheduleLayout.perm_eval_13,
      ScheduleLayout.perm_eval_14, ScheduleLayout.perm_eval_15,
      ScheduleLayout.perm_eval_16]
    norm_num [max_assoc]
    omega
  have hresult : (resultMemory memory n).size = memory.size := by
    rw [resultMemory, writeWord_size, writeWord_size, writeWord_size,
      MachineState.writeBytes_size, zeroBytes_size]
    simp only [Nat.zero_add, if_false, show ¬ (512 : Nat) = 0 by decide]
    omega
  exact bytes_ext_getD _ _ (hnorm.trans hresult.symm) (memory_pointwise memory n hs)

#print axioms memory_equiv



end Challenge.Ripemd160.Submission.Proofs.Bytecode.PadOnlySchedule
