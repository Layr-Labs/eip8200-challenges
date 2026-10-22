import Challenge.Modexp.Submission.Proofs.CRT.CRTKernelExecution
import Challenge.Modexp.Submission.Proofs.CRT.CRTInputMemory
import Challenge.Modexp.Submission.Proofs.CRT.CRTMemoryCells
import Challenge.Modexp.Submission.Proofs.CRT.CRTWordPacking
set_option warningAsError true
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option maxRecDepth 40000
set_option maxHeartbeats 2000000
set_option exponentiation.threshold 4096

namespace HistoricalSearch.CRTAdapterMeaning
open EvmSemantics EvmSemantics.EVM
open HistoricalSearch.GeneratedColumns HistoricalSearch.CRTInputMemory
open HistoricalSearch.CRTMemoryCells HistoricalSearch.CRTWordPacking
open Challenge.EvmProof.Word Challenge.EvmProof.Memory

theorem land_comm (a b : UInt256) : UInt256.land a b = UInt256.land b a := by
  apply word_ext
  rw [word_toNat_land, word_toNat_land, Nat.and_comm]

theorem lor_comm (a b : UInt256) : UInt256.lor a b = UInt256.lor b a := by
  apply word_ext
  rw [word_toNat_lor, word_toNat_lor, Nat.or_comm]

theorem shift_zero (a : UInt256) : UInt256.shiftRight a (UInt256.ofNat 0) = a := by
  apply word_ext
  rw [shiftRight_toNat _ (by decide : 0 < 256), Nat.shiftRight_zero]

theorem read_store_disjoint (mem : ByteArray) (word : UInt256) (dst src : Nat)
    (hd : src+32 ≤ dst ∨ dst+32 ≤ src) :
    MachineState.readWord
      (MachineState.writeBytes mem (Data.Bytes.natToBytesPadded word.toNat 32) dst) src =
      MachineState.readWord mem src := by
  apply readWord_writeBytes_disjoint
  simpa only [YulEvmCompiler.BytesLemmas.natToBytesPadded_size] using hd

def inputWord (mem : ByteArray) (ptr i : Nat) : UInt256 :=
  if i < 8 then inputDigitWord mem ptr i
  else UInt256.shiftRight (MachineState.readWord mem ptr) (UInt256.ofNat 160)

def operandCells (words : Nat → UInt256) : List (Nat × UInt256) :=
  [(768,words 0), (800,words 1), (832,words 2), (864,words 3),
   (896,words 4), (928,words 5), (960,words 6), (992,words 7), (1024,words 8)]

def entryMemory (mem : ByteArray) (counter : UInt256) : ByteArray :=
  storeCells mem ((1728,counter)::operandCells (inputWord mem 2368))

def inputWords (mem : ByteArray) (ptr : Nat) : List UInt256 :=
  [inputWord mem ptr 0, inputWord mem ptr 1, inputWord mem ptr 2,
   inputWord mem ptr 3, inputWord mem ptr 4, inputWord mem ptr 5,
   inputWord mem ptr 6, inputWord mem ptr 7, inputWord mem ptr 8]

theorem entry_model (s : State)
    (pbi hd w3 ent m32 allones m128 m64 m0 tl m96 inv tn aprev counter ret : UInt256)
    (rest : List UInt256) :
    entryModel s pbi hd w3 ent m32 allones m128 m64 m0 tl m96 inv tn aprev counter ret rest =
      {s with
        pc := UInt256.ofNat 5859
        memory := entryMemory s.memory counter
        stack := [UInt256.ofNat (2^251-1)] ++ inputWords s.memory 0 ++
          [UInt256.ofNat (2^244-1), MachineState.readWord s.memory 2720,
           UInt256.ofNat 0, hd, w3, UInt256.ofNat 3643, m32, allones,
           m128, m64, m0, tl, m96, inv, tn, aprev, counter, ret] ++ rest} := by
  simp (disch := omega) only [entryModel, entryMemory, operandCells, inputWord, inputWords,
    inputDigitWord, loadOffset, loadShift, storeCells, writeCell,
    read_store_disjoint, land_comm, shift_zero, Nat.reduceMul, Nat.reduceAdd,
    Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub, Nat.reducePow, Nat.reduceLT,
    if_true, if_false, List.cons_append, List.nil_append]

theorem operandCells_map (words : Nat → UInt256) :
    operandCells words = (List.range 9).map (fun i => (768+32*i, words i)) := rfl

theorem operandCells_read (mem : ByteArray) (words : Nat → UInt256) (i : Nat) (hi : i < 9) :
    MachineState.readWord (storeCells mem (operandCells words)) (768+32*i) = words i := by
  rw [operandCells_map]
  apply storeCells_hit
  · exact List.mem_map.mpr ⟨i, List.mem_range.mpr hi, rfl⟩
  · intro c hc
    rcases List.mem_map.mp hc with ⟨j, hj, rfl⟩
    have hj' := List.mem_range.mp hj
    by_cases he : j = i
    · subst j
      exact Or.inl ⟨rfl, rfl⟩
    · right
      omega

theorem entry_operand (mem : ByteArray) (counter : UInt256) (i : Nat) (hi : i < 9) :
    MachineState.readWord (entryMemory mem counter) (768+32*i) = inputWord mem 2368 i := by
  unfold entryMemory
  rw [storeCells]
  exact operandCells_read _ _ i hi

theorem entry_counter (mem : ByteArray) (counter : UInt256) :
    MachineState.readWord (entryMemory mem counter) 1728 = counter := by
  unfold entryMemory
  rw [storeCells, readWord_storeCells]
  · exact readWord_writeWord mem 1728 counter
  · intro c hc
    rw [operandCells_map] at hc
    rcases List.mem_map.mp hc with ⟨j, hj, rfl⟩
    have hj' := List.mem_range.mp hj
    right
    omega

theorem inputWord_low {mem : ByteArray} {ptr A : Nat}
    (hrep : Challenge.Modexp.Submission.Proofs.Fast.Model.FastRepresents mem ptr 8 A)
    (i : Nat) (hi : i < 8) :
    (inputWord mem ptr i).toNat = A/2^(244*i)%2^244 := by
  rw [inputWord, if_pos hi]
  exact inputDigitWord_toNat hrep i hi

theorem inputWord_high {mem : ByteArray} {ptr A : Nat}
    (hrep : Challenge.Modexp.Submission.Proofs.Fast.Model.FastRepresents mem ptr 8 A) :
    (inputWord mem ptr 8).toNat = A/2^1952 := by
  rw [inputWord, if_neg (by decide : ¬8 < 8)]
  exact inputTopWord_toNat hrep

def rawDigits (mem : ByteArray) (i : Nat) : UInt256 := MachineState.readWord mem (1344+32*i)

def retainedInput (mem : ByteArray) (i : Nat) : UInt256 :=
  if i < 8 then retainedWord (rawDigits mem) i
  else UInt256.shiftRight (rawDigits mem 8) (UInt256.ofNat 96)

def retainedMemory (mem : ByteArray) : ByteArray :=
  storeCells mem ((1728,MachineState.readWord mem 1728 - UInt256.ofNat 1) ::
    operandCells (retainedInput mem))

def outputCells (d : Nat → UInt256) : List (Nat × UInt256) :=
  [(2336,outputWord d 0), (2304,outputWord d 1), (2272,outputWord d 2),
   (2240,outputWord d 3), (2208,outputWord d 4), (2176,outputWord d 5),
   (2144,outputWord d 6), (2112,outputWord d 7)]

def exitMemory (mem : ByteArray) : ByteArray := storeCells mem (outputCells (rawDigits mem))

def cachedTop (mem : ByteArray) : UInt256 :=
  UInt256.lor (UInt256.shiftLeft (MachineState.readWord mem 1024) (UInt256.ofNat 160))
    (UInt256.shiftRight (MachineState.readWord mem 992) (UInt256.ofNat 84))

theorem retain_model (s : State)
    (P n0 n1 n2 n3 n4 n5 n6 n7 n8 minv pbi hd w3 ent m32 allones m128 m64 m0 tl m96 inv tn aprev counter ret : UInt256)
    (rest : List UInt256) :
    retainModel s P n0 n1 n2 n3 n4 n5 n6 n7 n8 (UInt256.ofNat (2^244-1)) minv
      pbi hd w3 ent m32 allones m128 m64 m0 tl m96 inv tn aprev counter ret rest =
      {s with
        pc := UInt256.ofNat 8624
        memory := retainedMemory s.memory
        stack := [UInt256.ofNat 5858, P, n0, n1, n2, n3, n4, n5, n6, n7, n8,
          UInt256.ofNat (2^244-1), minv, pbi, hd, w3, ent, m32, allones, m128, m64,
          m0, tl, m96, inv, tn, aprev, counter, ret] ++ rest} := by
  simp (disch := omega) only [retainModel, retainedMemory, operandCells, retainedInput,
    retainedWord, rawDigits, storeCells, writeCell, read_store_disjoint,
    land_comm, lor_comm, Nat.reduceMul, Nat.reduceAdd, Nat.reducePow, Nat.reduceSub,
    Nat.reduceLT, if_true, if_false, List.cons_append, List.nil_append]

theorem exit_model (s : State)
    (P n0 n1 n2 n3 n4 n5 n6 n7 n8 mask minv pbi hd w3 ent m32 allones m128 m64 m0 tl m96 inv tn aprev counter ret : UInt256)
    (rest : List UInt256) :
    exitModel s P n0 n1 n2 n3 n4 n5 n6 n7 n8 mask minv
      pbi hd w3 ent m32 allones m128 m64 m0 tl m96 inv tn aprev counter ret rest =
      {s with
        pc := UInt256.ofNat 8976
        memory := exitMemory s.memory
        stack := [UInt256.ofNat 3942, pbi, hd, w3, ent, m32, allones, m128, m64,
          m0, tl, m96, inv, MachineState.readWord s.memory 1760, cachedTop s.memory,
          MachineState.readWord s.memory 1728, ret] ++ rest} := by
  simp (disch := omega) only [exitModel, exitMemory, outputCells, outputWord,
    rawDigits, cachedTop, storeCells, writeCell, read_store_disjoint,
    lor_comm, Nat.reduceMul, Nat.reduceAdd, Nat.reducePow, Nat.reduceSub,
    List.cons_append, List.nil_append]

theorem outputCells_map (d : Nat → UInt256) :
    outputCells d = (List.range 8).map (fun i => (2112+32*(7-i), outputWord d i)) := rfl

theorem outputCells_read (mem : ByteArray) (d : Nat → UInt256) (i : Nat) (hi : i < 8) :
    MachineState.readWord (storeCells mem (outputCells d)) (2112+32*(7-i)) = outputWord d i := by
  rw [outputCells_map]
  apply storeCells_hit
  · exact List.mem_map.mpr ⟨i, List.mem_range.mpr hi, rfl⟩
  · intro c hc
    rcases List.mem_map.mp hc with ⟨j, hj, rfl⟩
    have hj' := List.mem_range.mp hj
    by_cases he : j = i
    · subst j
      exact Or.inl ⟨rfl, rfl⟩
    · right
      omega

theorem exit_represents (mem : ByteArray)
    (hd : ∀ i < 9, (rawDigits mem i).toNat < 2^244) :
    Challenge.Modexp.Submission.Proofs.Fast.Model.FastRepresents
      (exitMemory mem) 2112 8 (value (rawDigits mem) % 2^2048) := by
  apply output_represents _ _ hd
  exact outputCells_read mem (rawDigits mem)

theorem retained_operand (mem : ByteArray) (i : Nat) (hi : i < 9) :
    MachineState.readWord (retainedMemory mem) (768+32*i) = retainedInput mem i := by
  unfold retainedMemory
  rw [storeCells]
  exact operandCells_read _ _ i hi

theorem retained_operand_low (mem : ByteArray) (i : Nat) (hi : i < 8)
    (hd : ∀ j < 9, (rawDigits mem j).toNat < 2^244) :
    (MachineState.readWord (retainedMemory mem) (768+32*i)).toNat =
      value (rawDigits mem) / 2^(244*i) % 2^244 := by
  rw [retained_operand mem i (by omega), retainedInput, if_pos hi]
  exact retainedWord_toNat (rawDigits mem) i hi hd

theorem retained_operand_high (mem : ByteArray)
    (hd : ∀ j < 9, (rawDigits mem j).toNat < 2^244) :
    (MachineState.readWord (retainedMemory mem) 1024).toNat =
      value (rawDigits mem) / 2^1952 := by
  rw [show 1024 = 768+32*8 by decide, retained_operand mem 8 (by decide),
    retainedInput, if_neg (by decide : ¬8 < 8)]
  exact retainedTop_toNat (rawDigits mem) hd

theorem operandCells_bounds (words : Nat → UInt256) (c : Nat × UInt256)
    (hc : c ∈ operandCells words) : 768 ≤ c.1 ∧ c.1+32 ≤ 1056 := by
  rw [operandCells_map] at hc
  rcases List.mem_map.mp hc with ⟨j, hj, rfl⟩
  have hj' := List.mem_range.mp hj
  constructor <;> omega

theorem entry_keep (mem : ByteArray) (counter : UInt256) (addr width : Nat)
    (h : addr+width ≤ 768 ∨ 1792 ≤ addr) :
    MachineState.readPadded (entryMemory mem counter) addr width =
      MachineState.readPadded mem addr width := by
  apply scratch_preserves_live _ _ _ addr width h
  intro c hc
  rcases List.mem_cons.mp hc with he | ht
  · subst c
    norm_num
  · have hb := operandCells_bounds _ _ ht
    constructor <;> omega

theorem retained_keep (mem : ByteArray) (addr width : Nat)
    (h : addr+width ≤ 768 ∨ 1792 ≤ addr) :
    MachineState.readPadded (retainedMemory mem) addr width =
      MachineState.readPadded mem addr width := by
  apply scratch_preserves_live _ _ _ addr width h
  intro c hc
  rcases List.mem_cons.mp hc with he | ht
  · subst c
    norm_num
  · have hb := operandCells_bounds _ _ ht
    constructor <;> omega

theorem exit_keep (mem : ByteArray) (addr width : Nat)
    (h : addr+width ≤ 2112 ∨ 2368 ≤ addr) :
    MachineState.readPadded (exitMemory mem) addr width =
      MachineState.readPadded mem addr width := by
  apply readPadded_storeCells
  intro c hc
  rw [outputCells_map] at hc
  rcases List.mem_map.mp hc with ⟨j, hj, rfl⟩
  have hj' := List.mem_range.mp hj
  omega

theorem retained_counter (mem : ByteArray) :
    MachineState.readWord (retainedMemory mem) 1728 =
      MachineState.readWord mem 1728 - UInt256.ofNat 1 := by
  unfold retainedMemory
  rw [storeCells, readWord_storeCells]
  · exact readWord_writeWord mem 1728 _
  · intro c hc
    have hb := operandCells_bounds _ _ hc
    right
    omega

theorem retained_counter_toNat (mem : ByteArray)
    (h : 0 < (MachineState.readWord mem 1728).toNat) :
    (MachineState.readWord (retainedMemory mem) 1728).toNat =
      (MachineState.readWord mem 1728).toNat - 1 := by
  rw [retained_counter, word_toNat_sub_cond]
  change (if (MachineState.readWord mem 1728).toNat < 1 then _ else _) = _
  rw [if_neg (by omega)]
  rfl

/-- The old tail caches the most significant word of the latest operand.
This proves its restoration from the retained mixed-radix representation. -/
theorem cachedTop_toNat (mem : ByteArray) (A : Nat) (hA : A < 2^2048)
    (h7 : (MachineState.readWord mem 992).toNat = A/2^1708%2^244)
    (h8 : (MachineState.readWord mem 1024).toNat = A/2^1952) :
    (cachedTop mem).toNat = A/2^1792 := by
  have hlo : (MachineState.readWord mem 992).toNat < 2^244 := by
    rw [h7]
    exact Nat.mod_lt _ (Nat.two_pow_pos 244)
  have hl : A/2^1708 = (MachineState.readWord mem 992).toNat +
      2^244*(MachineState.readWord mem 1024).toNat := by
    rw [h7, h8]
    have hh := Nat.mod_add_div (A/2^1708) (2^244)
    rw [Nat.div_div_eq_div_mul, ← Nat.pow_add] at hh
    exact hh.symm
  have hp := HistoricalSearch.MixedMontgomery.repackOr (2^244) 84 160 256
    (MachineState.readWord mem 992).toNat (MachineState.readWord mem 1024).toNat 0
    (by decide) (by norm_num) hlo (by decide)
  rw [Nat.mul_zero, Nat.add_zero, ← hl, Nat.div_div_eq_div_mul, ← Nat.pow_add] at hp
  have hq : A/2^1792 < (2:Nat)^256 := by
    apply (Nat.div_lt_iff_lt_mul (Nat.two_pow_pos 1792)).2
    simpa [← Nat.pow_add] using hA
  unfold cachedTop
  rw [word_toNat_lor,
    HistoricalSearch.CRTWordBridge.shiftLeft_toNat _ _ (by decide : 160 < 256),
    shiftRight_toNat _ (by decide : 84 < 256), Nat.or_comm, hp,
    Nat.mod_eq_of_lt hq]

#print axioms entry_model
#print axioms operandCells_read
#print axioms entry_operand
#print axioms entry_counter
#print axioms inputWord_low
#print axioms inputWord_high
#print axioms retain_model
#print axioms exit_model
#print axioms outputCells_read
#print axioms exit_represents
#print axioms retained_operand_low
#print axioms retained_operand_high
#print axioms entry_keep
#print axioms retained_keep
#print axioms exit_keep
#print axioms retained_counter_toNat
#print axioms cachedTop_toNat
end HistoricalSearch.CRTAdapterMeaning
