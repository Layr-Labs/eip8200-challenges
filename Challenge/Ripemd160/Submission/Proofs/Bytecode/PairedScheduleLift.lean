import Challenge.Ripemd160.Submission.Proofs.Bytecode.DenseScheduleLift
import Challenge.Ripemd160.Submission.Proofs.Bytecode.DenseScheduleTrace
import Challenge.Ripemd160.Submission.Proofs.Bytecode.DenseEndianMultiply
import Challenge.Ripemd160.Submission.Proofs.Bytecode.DenseScheduleMemory
import Challenge.EvmProof.Bytes
import Challenge.EvmProof.Memory

set_option warningAsError true

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.PairedScheduleOverlap

open EvmSemantics
open Challenge.EvmProof

/-- Two padded half-word reads decompose every 32-byte read, even past the
end of the byte array. No clean-memory or alignment assumption is needed. -/
theorem readWord_halves (memory : ByteArray) (offset : Nat) :
    (MachineState.readWord memory offset).toNat =
      EVM.Precompile.bytesToNatPadded memory offset 16 * 2 ^ 128 +
      EVM.Precompile.bytesToNatPadded memory (offset + 16) 16 := by
  rw [Bytes.readWord_toNat]
  simpa only [show 16 + 16 = 32 by decide,
    show 256 ^ 16 = 2 ^ 128 by decide] using
      Bytes.bytesToNatPadded_add memory offset 16 16

theorem halves_of_small (memory : ByteArray) (offset : Nat)
    (hsmall : (MachineState.readWord memory offset).toNat < 2 ^ 128) :
    EVM.Precompile.bytesToNatPadded memory offset 16 = 0 ∧
    EVM.Precompile.bytesToNatPadded memory (offset + 16) 16 =
      (MachineState.readWord memory offset).toNat := by
  have hsplit := readWord_halves memory offset
  norm_num at hsmall hsplit
  omega

/-- A normalized current cell followed by a normalized cell (or zero
sentinel) supports the overlapping upper-lane read used by the paired code. -/
theorem readWord_offset16 (memory : ByteArray) (offset : Nat)
    (current next : UInt256)
    (hcurrent : MachineState.readWord memory offset = current)
    (hnext : MachineState.readWord memory (offset + 32) = next)
    (hcurrent32 : current.toNat < 2 ^ 32)
    (hnext32 : next.toNat < 2 ^ 32) :
    MachineState.readWord memory (offset + 16) =
      UInt256.shiftLeft current (UInt256.ofNat 128) := by
  have hsmall1 : (MachineState.readWord memory offset).toNat < 2 ^ 128 := by
    rw [hcurrent]
    exact hcurrent32.trans (by decide)
  have hsmall2 : (MachineState.readWord memory (offset + 32)).toNat < 2 ^ 128 := by
    rw [hnext]
    exact hnext32.trans (by decide)
  have hleft := (halves_of_small memory offset hsmall1).2
  have hright := (halves_of_small memory (offset + 32) hsmall2).1
  rw [hcurrent] at hleft
  have hresult : current.toNat * 2 ^ 128 < 2 ^ 256 := by
    norm_num at hcurrent32 ⊢
    omega
  have hshift : UInt256.shiftLeft current (UInt256.ofNat 128) =
      UInt256.ofNat (current.toNat * 2 ^ 128) := by
    calc
      UInt256.shiftLeft current (UInt256.ofNat 128) =
          UInt256.shiftLeft (UInt256.ofNat current.toNat) (UInt256.ofNat 128) :=
        congrArg (fun value => UInt256.shiftLeft value (UInt256.ofNat 128))
          (Challenge.EvmProof.Word.word_eq_ofNat_toNat current)
      _ = _ := Challenge.EvmProof.Word.shiftLeft_ofNat current.val.isLt (by decide) hresult
  apply Challenge.EvmProof.Word.word_ext
  rw [hshift, Challenge.EvmProof.Word.word_toNat_ofNat, Nat.mod_eq_of_lt hresult,
    readWord_halves, hleft, show offset + 16 + 16 = offset + 32 by omega,
    hright, Nat.add_zero]

theorem read_schedule_upper (memory : ByteArray) (words : Nat → UInt256)
    (hread : ∀ i, i ≤ 16 → MachineState.readWord memory (192 + 32 * i) = words i)
    (hbound : ∀ i, i ≤ 16 → (words i).toNat < 2 ^ 32)
    (i : Nat) (hi : i < 16) :
    MachineState.readWord memory (208 + 32 * i) =
      UInt256.shiftLeft (words i) (UInt256.ofNat 128) := by
  have hnext : MachineState.readWord memory (192 + 32 * i + 32) = words (i + 1) := by
    convert hread (i + 1) (by omega) using 1
    congr 1
  have h := readWord_offset16 memory (192 + 32 * i) (words i) (words (i + 1))
    (hread i (by omega)) hnext (hbound i (by omega)) (hbound (i + 1) (by omega))
  convert h using 1
  congr 1
  omega

#print axioms readWord_halves
#print axioms halves_of_small
#print axioms readWord_offset16
#print axioms read_schedule_upper

end Challenge.Ripemd160.Submission.Proofs.Bytecode.PairedScheduleOverlap

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.PairedScheduleMemory

open EvmSemantics
open Challenge.EvmProof

def cell (i : Nat) : Nat := 192 + 32 * i

def writeWord (memory : ByteArray) (address : Nat) (value : UInt256) : ByteArray :=
  MachineState.writeBytes memory (Data.Bytes.natToBytesPadded value.toNat 32) address

def storeCells (memory : ByteArray) (words : Nat → UInt256) (first : Nat) :
    Nat → ByteArray
  | 0 => memory
  | n + 1 => writeWord (storeCells memory words first n) (cell (first + n)) (words (first + n))

/-- Match the emitted order: upper eight cells, lower eight, then the sentinel. -/
def normalizedMemory (memory : ByteArray) (words : Nat → UInt256) : ByteArray :=
  writeWord (storeCells (storeCells memory words 8 8) words 0 8) (cell 16) (UInt256.ofNat 0)

theorem read_writeWord (memory : ByteArray) (address : Nat) (value : UInt256) :
    MachineState.readWord (writeWord memory address value) address = value :=
  Memory.readWord_writeWord memory address value

theorem read_writeWord_disjoint (memory : ByteArray) (readStart writeStart : Nat)
    (value : UInt256)
    (hdisjoint : readStart + 32 ≤ writeStart ∨ writeStart + 32 ≤ readStart) :
    MachineState.readWord (writeWord memory writeStart value) readStart =
      MachineState.readWord memory readStart := by
  apply Memory.readWord_writeBytes_disjoint
  simpa only [YulEvmCompiler.BytesLemmas.natToBytesPadded_size] using hdisjoint

theorem read_storeCells (memory : ByteArray) (words : Nat → UInt256)
    (first n i : Nat) (hfirst : first ≤ i) (hi : i < first + n) :
    MachineState.readWord (storeCells memory words first n) (cell i) = words i := by
  induction n generalizing i with
  | zero => omega
  | succ n ih =>
    rw [storeCells]
    by_cases heq : i = first + n
    · subst i
      exact read_writeWord _ _ _
    · rw [read_writeWord_disjoint _ _ _ _ (Or.inl (by simp only [cell]; omega))]
      exact ih i hfirst (by omega)

theorem read_storeCells_outside (memory : ByteArray) (words : Nat → UInt256)
    (first n address : Nat)
    (houtside : address + 32 ≤ cell first ∨ cell (first + n) ≤ address) :
    MachineState.readWord (storeCells memory words first n) address =
      MachineState.readWord memory address := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [storeCells, read_writeWord_disjoint]
    · apply ih
      simp only [cell] at houtside ⊢
      omega
    · simp only [cell] at houtside ⊢
      omega

theorem getD_storeCells_outside (memory : ByteArray) (words : Nat → UInt256)
    (first n address : Nat)
    (houtside : address < cell first ∨ cell (first + n) ≤ address) :
    (storeCells memory words first n)[address]?.getD 0 = memory[address]?.getD 0 := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [storeCells]
    simp only [writeWord, MachineState.writeBytes_getElem?_getD,
      YulEvmCompiler.BytesLemmas.natToBytesPadded_size]
    rw [if_neg (by simp only [cell] at houtside ⊢; omega)]
    apply ih
    simp only [cell] at houtside ⊢
    omega

theorem read_normalized_cell (memory : ByteArray) (words : Nat → UInt256)
    (i : Nat) (hi : i ≤ 16) :
    MachineState.readWord (normalizedMemory memory words) (cell i) =
      if i = 16 then UInt256.ofNat 0 else words i := by
  by_cases heq : i = 16
  · subst i
    simp only [normalizedMemory, read_writeWord, ↓reduceIte]
  · rw [if_neg heq, normalizedMemory, read_writeWord_disjoint _ _ _ _
      (Or.inl (by simp only [cell]; omega))]
    by_cases hlow : i < 8
    · exact read_storeCells _ _ 0 8 i (by omega) (by omega)
    · rw [read_storeCells_outside _ _ 0 8 (cell i)
        (Or.inr (by simp only [cell]; omega))]
      exact read_storeCells _ _ 8 8 i (by omega) (by omega)

theorem read_normalized_upper (memory : ByteArray) (words : Nat → UInt256)
    (hbound : ∀ i, i < 16 → (words i).toNat < 2 ^ 32)
    (i : Nat) (hi : i < 16) :
    MachineState.readWord (normalizedMemory memory words) (208 + 32 * i) =
      UInt256.shiftLeft (words i) (UInt256.ofNat 128) := by
  have h := PairedScheduleOverlap.read_schedule_upper
    (normalizedMemory memory words) (fun j => if j = 16 then UInt256.ofNat 0 else words j)
    (fun j hj => read_normalized_cell memory words j hj)
    (by
      intro j hj
      by_cases heq : j = 16
      · simp only [heq, ↓reduceIte]
        decide
      · simp only [if_neg heq]
        exact hbound j (by omega))
    i hi
  simpa only [if_neg (show i ≠ 16 by omega)] using h

theorem read_normalized_outside (memory : ByteArray) (words : Nat → UInt256)
    (address : Nat) (houtside : address + 32 ≤ 192 ∨ 736 ≤ address) :
    MachineState.readWord (normalizedMemory memory words) address =
      MachineState.readWord memory address := by
  rw [normalizedMemory, read_writeWord_disjoint]
  · rw [read_storeCells_outside, read_storeCells_outside]
    · simp only [cell]
      omega
    · simp only [cell]
      omega
  · simp only [cell]
    omega

theorem getD_normalized_outside (memory : ByteArray) (words : Nat → UInt256)
    (address : Nat) (houtside : address < 192 ∨ 736 ≤ address) :
    (normalizedMemory memory words)[address]?.getD 0 = memory[address]?.getD 0 := by
  simp only [normalizedMemory, writeWord, MachineState.writeBytes_getElem?_getD,
    YulEvmCompiler.BytesLemmas.natToBytesPadded_size]
  rw [if_neg (by simp only [cell]; omega), getD_storeCells_outside,
    getD_storeCells_outside]
  · simp only [cell]
    omega
  · simp only [cell]
    omega

theorem readPadded_normalized_outside (memory : ByteArray) (words : Nat → UInt256)
    (address count : Nat) (houtside : address + count ≤ 192 ∨ 736 ≤ address) :
    MachineState.readPadded (normalizedMemory memory words) address count =
      MachineState.readPadded memory address count := by
  apply Memory.readPadded_congr
  intro j hj
  apply getD_normalized_outside
  omega

theorem read_normalized_hash (memory : ByteArray) (words : Nat → UInt256)
    (i : Nat) (hi : i < 5) :
    MachineState.readWord (normalizedMemory memory words) (32 + 32 * i) =
      MachineState.readWord memory (32 + 32 * i) := by
  apply read_normalized_outside
  left
  omega

#print axioms read_writeWord
#print axioms read_writeWord_disjoint
#print axioms read_storeCells
#print axioms read_storeCells_outside
#print axioms getD_storeCells_outside
#print axioms read_normalized_cell
#print axioms read_normalized_upper
#print axioms read_normalized_outside
#print axioms getD_normalized_outside
#print axioms readPadded_normalized_outside
#print axioms read_normalized_hash


theorem writeWord_size (memory : ByteArray) (address : Nat) (value : UInt256) :
    (writeWord memory address value).size = max memory.size (address + 32) := by
  simp only [writeWord, MachineState.writeBytes_size,
    YulEvmCompiler.BytesLemmas.natToBytesPadded_size,
    if_neg (by decide : (32 : Nat) ≠ 0)]

private theorem getD_eq_data (b : ByteArray) (j : Nat) (hj : j < b.data.size) :
    b[j]?.getD 0 = b.data[j] := by
  have h : j < b.size := hj
  rw [getElem?_pos b j h]
  rfl

/-- Writing a zero word over 32 bytes that are ALREADY zero, in memory that is
ALREADY long enough, changes nothing.  BOTH hypotheses are required: on a short
`ByteArray` `writeBytes` EXTENDS the array, so "reads as zero" alone is false. -/
theorem writeWord_zero_noop (memory : ByteArray) (address : Nat)
    (hsize : address + 32 ≤ memory.size)
    (hzero : ∀ i, i < 32 → memory[address + i]?.getD 0 = 0) :
    writeWord memory address (UInt256.ofNat 0) = memory := by
  have hbsize : (EvmSemantics.Data.Bytes.natToBytesPadded (UInt256.ofNat 0).toNat 32).size = 32 :=
    YulEvmCompiler.BytesLemmas.natToBytesPadded_size _ _
  apply ByteArray.ext
  apply Array.ext
  · show (EvmSemantics.MachineState.writeBytes memory _ address).size = memory.size
    rw [EvmSemantics.MachineState.writeBytes_size, hbsize]
    rw [if_neg (by omega)]
    omega
  · intro i hi₁ hi₂
    have h := EvmSemantics.MachineState.writeBytes_getElem?_getD memory
      (EvmSemantics.Data.Bytes.natToBytesPadded (UInt256.ofNat 0).toNat 32) address i
    rw [hbsize] at h
    rw [← getD_eq_data _ i hi₁, ← getD_eq_data _ i hi₂]
    show (EvmSemantics.MachineState.writeBytes memory _ address)[i]?.getD 0 = _
    by_cases hc : address ≤ i ∧ i < address + 32
    · rw [if_pos hc] at h
      have hk : i - address < 32 := by omega
      have hz := YulEvmCompiler.BytesLemmas.natToBytesPadded_getElem?_getD
        (UInt256.ofNat 0).toNat 32 (i - address) hk
      have hzero' := hzero (i - address) hk
      have hidx : address + (i - address) = i := by omega
      rw [hidx] at hzero'
      rw [h, hz, hzero']
      simp
    · rw [if_neg hc] at h
      exact h

theorem storeCells_size (memory : ByteArray) (words : Nat → UInt256)
    (first n : Nat) :
    (storeCells memory words first n).size =
      if n = 0 then memory.size else max memory.size (cell (first + n)) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [storeCells, writeWord_size, ih]
    simp only [Nat.succ_ne_zero, if_false]
    split <;> simp only [cell] <;> omega

theorem normalizedMemory_size (memory : ByteArray) (words : Nat → UInt256) :
    (normalizedMemory memory words).size = max memory.size 736 := by
  rw [normalizedMemory, writeWord_size, storeCells_size, storeCells_size]
  norm_num [cell]

theorem normalizedMemory_size_of_ge (memory : ByteArray) (words : Nat → UInt256)
    (hsize : 736 ≤ memory.size) :
    (normalizedMemory memory words).size = memory.size := by
  rw [normalizedMemory_size, Nat.max_eq_left hsize]

theorem active_cell (current i : Nat) :
    MachineState.activeWordsAfter current (cell i) 32 = max current (7 + i) := by
  simp only [MachineState.activeWordsAfter, if_neg (by decide : (32 : Nat) ≠ 0), cell]
  congr 1
  omega

theorem active_cell_preserved (current i : Nat)
    (hcurrent : 23 ≤ current) (hi : i ≤ 16) :
    MachineState.activeWordsAfter current (cell i) 32 = current := by
  rw [active_cell, Nat.max_eq_left (by omega)]

theorem active_wrapped_cell_preserved (current : UInt256) (i : Nat)
    (hcurrent : 23 ≤ current.toNat) (hi : i ≤ 16) :
    UInt256.ofNat (MachineState.activeWordsAfter current.toNat (cell i) 32) = current := by
  rw [active_cell_preserved current.toNat i hcurrent hi]
  exact (Challenge.EvmProof.Word.word_eq_ofNat_toNat current).symm

theorem active_load_ge23 (current offset : Nat) (hoffset : 736 ≤ offset) :
    23 ≤ MachineState.activeWordsAfter current offset 32 := by
  simp only [MachineState.activeWordsAfter, if_neg (by decide : (32 : Nat) ≠ 0)]
  apply Nat.le_trans ?_ (Nat.le_max_right _ _)
  omega

#print axioms writeWord_size
#print axioms storeCells_size
#print axioms normalizedMemory_size
#print axioms normalizedMemory_size_of_ge
#print axioms active_cell
#print axioms active_cell_preserved
#print axioms active_wrapped_cell_preserved
#print axioms active_load_ge23

end Challenge.Ripemd160.Submission.Proofs.Bytecode.PairedScheduleMemory

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.PairedScheduleData

open EvmSemantics
open Challenge.EvmProof
open DenseScheduleMemory PairedScheduleMemory

def reversedWord (value : UInt256) : UInt256 :=
  DenseScheduleTemplate.multipliedStage
    (DenseScheduleTemplate.multipliedStage value 8 DenseScheduleTemplate.mask8)
    16 DenseScheduleTemplate.mask16

theorem reversedWord_eq_packed (value : UInt256) :
    reversedWord value = DensePacked.packed value := by
  unfold reversedWord
  rw [DenseEndianMultiply.multipliedStage16_eq_packedStage,
    DenseEndianMultiply.multipliedStage8_eq_packedStage]
  simp only [DenseScheduleTemplate.packedStage, DensePacked.packed,
    DensePacked.shr, DensePacked.shl, DenseScheduleTemplate.mask8,
    DenseScheduleTemplate.mask16, DensePacked.mask8, DensePacked.mask16,
    Word.lor_comm]

theorem shr_zero (value : UInt256) : DensePacked.shr value 0 = value := by
  apply Challenge.EvmProof.Word.word_ext
  rw [show (DensePacked.shr value 0).toNat = value.toNat >>> 0 from
    Challenge.EvmProof.Word.shiftRight_toNat value (by decide)]
  exact Nat.shiftRight_zero

/-- Exact emitted extraction branches: j=0 has no redundant mask, j=7 no shift. -/
def chunk (value : UInt256) (j : Nat) : UInt256 :=
  let packed := reversedWord value
  if j = 0 then DensePacked.shr packed 224
  else if j = 7 then Challenge.EvmProof.Word.mask32 packed
  else Challenge.EvmProof.Word.mask32 (DensePacked.shr packed (32 * (7-j)))

theorem chunk_eq_le4 (value : UInt256) (j : Nat) (hj : j < 8) :
    chunk value j = Challenge.EvmProof.Word.mask32 (DensePacked.le4 value j) := by
  unfold chunk
  rw [reversedWord_eq_packed]
  by_cases h0 : j = 0
  · subst j
    rw [if_pos rfl]
    exact (DensePacked.mask32_shr224 _).symm.trans
      (by simpa only [Nat.sub_zero] using DensePacked.packed_extract value 0 (by decide))
  · rw [if_neg h0]
    by_cases h7 : j = 7
    · subst j
      rw [if_pos rfl]
      simpa only [Nat.sub_self, Nat.mul_zero, shr_zero] using
        DensePacked.packed_extract value 7 (by decide)
    · rw [if_neg h7]
      exact DensePacked.packed_extract value j hj

def extractedWord (memory : ByteArray) (p i : Nat) : UInt256 :=
  chunk (MachineState.readWord memory (p + 32 * (i / 8))) (i % 8)

def littleWord (memory : ByteArray) (p i : Nat) : UInt256 :=
  Challenge.EvmProof.Word.mask32 (DensePacked.le4
    (MachineState.readWord memory (p + 4 * i)) 0)

theorem extractedWord_eq_littleWord (memory : ByteArray) (p i : Nat) :
    extractedWord memory p i = littleWord memory p i := by
  unfold extractedWord littleWord
  rw [chunk_eq_le4 _ _ (Nat.mod_lt _ (by decide)),
    DensePacked.le4_readWord_offset _ _ _ (Nat.mod_lt _ (by decide))]
  have h := Nat.div_add_mod i 8
  have hp : p + 32 * (i / 8) + 4 * (i % 8) = p + 4 * i := by omega
  rw [hp]

theorem littleWord_bound (memory : ByteArray) (p i : Nat) :
    (littleWord memory p i).toNat < 2 ^ 32 := by
  rw [littleWord, Challenge.EvmProof.Word.mask32_eq_ofUInt32,
    Challenge.EvmProof.Word.ofUInt32_toNat]
  exact (Challenge.EvmProof.Word.toUInt32 _).toBitVec.isLt

theorem extractedWord_bound (memory : ByteArray) (p i : Nat) :
    (extractedWord memory p i).toNat < 2 ^ 32 := by
  rw [extractedWord_eq_littleWord]
  exact littleWord_bound memory p i

theorem loadOffsetWord_toNat (p i : Nat) (hi : i < 16)
    (hbound : p + 64 < 2 ^ 256) :
    (Schedule.loadOffsetWord (UInt256.ofNat p) i).toNat = p + 4 * i := by
  unfold Schedule.loadOffsetWord
  rw [Challenge.EvmProof.Word.shiftLeft_ofNat (by omega) (by decide)
    (by omega : i * 2 ^ 2 < 2 ^ 256)]
  rw [Challenge.EvmProof.Word.ofNat_add_ofNat (by omega),
    Challenge.EvmProof.Word.word_toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  omega

theorem extractedWord_eq_expectedWord (memory : ByteArray) (p i : Nat)
    (hi : i < 16) (hbound : p + 64 < 2 ^ 256) :
    extractedWord memory p i =
      ScheduleCorrect.expectedWord memory (UInt256.ofNat p) i := by
  rw [extractedWord_eq_littleWord]
  unfold littleWord ScheduleCorrect.expectedWord Schedule.readLEWord
  rw [loadOffsetWord_toNat p i hi hbound]
  rfl

theorem read_normalized_extracted (memory : ByteArray) (p i : Nat) (hi : i < 16) :
    MachineState.readWord (normalizedMemory memory (extractedWord memory p))
      (192 + 32 * i) = littleWord memory p i := by
  change MachineState.readWord (normalizedMemory memory (extractedWord memory p))
    (cell i) = littleWord memory p i
  rw [read_normalized_cell _ _ _ (by omega), if_neg (by omega)]
  exact extractedWord_eq_littleWord memory p i

theorem read_normalized_extracted_upper (memory : ByteArray) (p i : Nat) (hi : i < 16) :
    MachineState.readWord (normalizedMemory memory (extractedWord memory p))
      (208 + 32 * i) = UInt256.shiftLeft (littleWord memory p i) (UInt256.ofNat 128) := by
  rw [read_normalized_upper _ _ (fun j _ => extractedWord_bound memory p j) _ hi,
    extractedWord_eq_littleWord]

#print axioms reversedWord_eq_packed
#print axioms shr_zero
#print axioms chunk_eq_le4
#print axioms extractedWord_eq_littleWord
#print axioms littleWord_bound
#print axioms extractedWord_bound
#print axioms loadOffsetWord_toNat
#print axioms extractedWord_eq_expectedWord
#print axioms read_normalized_extracted
#print axioms read_normalized_extracted_upper

end Challenge.Ripemd160.Submission.Proofs.Bytecode.PairedScheduleData

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.PairedSchedulePrimitives

open EvmSemantics EvmSemantics.EVM
open YulEvmCompiler
open Challenge.EvmProof
open StackRoundTrace DenseScheduleTemplate
open PairedScheduleMemory

def storeTemplate (address : Nat) : List Instr :=
  [if address = 192 ∨ address = 224 then push1 (UInt256.ofNat address) else push2 (UInt256.ofNat address), op .MSTORE]

theorem run_storeTemplate (s : State) (pc value : UInt256) (address : Nat)
    (rest : List UInt256) (hstack : rest.length < 1022)
    (haddress : address < 2 ^ 256) (hrun : s.halt = .Running) :
    runInstrSeq (storeTemplate address) {s with pc := pc, stack := value :: rest} =
      some { s with
        pc := pcAfter pc (storeTemplate address)
        stack := rest
        memory := writeWord s.memory address value
        activeWords := UInt256.ofNat (MachineState.activeWordsAfter s.activeWords.toNat address 32)} := by
  have hcap1 : rest.length + 1 < 1024 := by omega
  have hcap : rest.length + 1 + 1 < 1024 := by omega
  have haddr : (UInt256.ofNat address).toNat = address := by
    rw [Challenge.EvmProof.Word.word_toNat_ofNat]
    exact Nat.mod_eq_of_lt haddress
  by_cases hsmall : address = 192 ∨ address = 224 <;>
    simp [storeTemplate, hsmall, push1, push2, op, writeWord, runInstrSeq,
    Challenge.EvmProof.Stepper.runInstr, pcAfter, hrun, hcap1, hcap,
    UInt256.succ, Instr.size,
    State.activeWordsAfterUInt256, haddr]
  all_goals rfl

def maskTemplate : List Instr :=
  [.push ⟨4, by decide⟩ (UInt256.ofNat 0xffffffff), op .AND]

theorem run_maskTemplate (s : State) (pc value : UInt256)
    (rest : List UInt256) (hstack : rest.length < 1022) (hrun : s.halt = .Running) :
    runInstrSeq maskTemplate {s with pc := pc, stack := value :: rest} =
      some { s with
        pc := pcAfter pc maskTemplate
        stack := Challenge.EvmProof.Word.mask32 value :: rest} := by
  have hcap1 : rest.length + 1 < 1024 := by omega
  have hcap : rest.length + 1 + 1 < 1024 := by omega
  simp [maskTemplate, op, runInstrSeq, Challenge.EvmProof.Stepper.runInstr,
    pcAfter, hrun, hcap1, hcap, UInt256.succ, Instr.size,
    Challenge.EvmProof.Word.mask32, Word.land_comm]
  exact ⟨rfl, rfl⟩

def duplicateShiftTemplate (shift : Nat) : List Instr :=
  [dup1, push1 (UInt256.ofNat shift), op .SHR]

theorem run_duplicateShiftTemplate (s : State) (pc value : UInt256) (shift : Nat)
    (rest : List UInt256) (hstack : rest.length < 1020) (hrun : s.halt = .Running) :
    runInstrSeq (duplicateShiftTemplate shift) {s with pc := pc, stack := value :: rest} =
      some { s with
        pc := pcAfter pc (duplicateShiftTemplate shift)
        stack := UInt256.shiftRight value (UInt256.ofNat shift) :: value :: rest} := by
  have hcap1 : rest.length + 1 < 1024 := by omega
  have hcap2 : rest.length + 1 + 1 < 1024 := by omega
  have hcap3 : rest.length + 1 + 1 + 1 < 1024 := by omega
  simp [duplicateShiftTemplate, dup1, push1, op, runInstrSeq,
    Challenge.EvmProof.Stepper.runInstr, pcAfter, hrun, hcap1, hcap2, hcap3,
    UInt256.succ, Instr.size]
  rfl

#print axioms run_storeTemplate
#print axioms run_maskTemplate
#print axioms run_duplicateShiftTemplate

end Challenge.Ripemd160.Submission.Proofs.Bytecode.PairedSchedulePrimitives

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.PairedScheduleStores

open EvmSemantics EvmSemantics.EVM
open YulEvmCompiler
open StackRoundTrace DenseScheduleTemplate PairedScheduleMemory PairedSchedulePrimitives

def firstTemplate (address : Nat) : List Instr :=
  duplicateShiftTemplate 224 ++ storeTemplate address

def middleTemplate (shift address : Nat) : List Instr :=
  duplicateShiftTemplate shift ++ (maskTemplate ++ storeTemplate address)

def lastTemplate (address : Nat) : List Instr :=
  maskTemplate ++ storeTemplate address

theorem run_firstTemplate (s : State) (pc value : UInt256) (address : Nat)
    (rest : List UInt256) (hstack : rest.length < 1020)
    (haddress : address < 2 ^ 256) (hrun : s.halt = .Running) :
    runInstrSeq (firstTemplate address) {s with pc := pc, stack := value :: rest} =
      some { s with
        pc := pcAfter pc (firstTemplate address)
        stack := value :: rest
        memory := writeWord s.memory address (UInt256.shiftRight value (UInt256.ofNat 224))
        activeWords := UInt256.ofNat (MachineState.activeWordsAfter s.activeWords.toNat address 32) } := by
  have h1 := run_duplicateShiftTemplate s pc value 224 rest hstack hrun
  have h2 := run_storeTemplate s (pcAfter pc (duplicateShiftTemplate 224))
    (UInt256.shiftRight value (UInt256.ofNat 224)) address (value :: rest)
    (by simp only [List.length_cons]; omega) haddress hrun
  unfold firstTemplate
  rw [DenseScheduleTrace.pcAfter_append]
  exact DenseScheduleTrace.runInstrSeq_append_running h1
    (by exact hrun) h2

theorem run_middleTemplate (s : State) (pc value : UInt256) (shift address : Nat)
    (rest : List UInt256) (hstack : rest.length < 1020)
    (haddress : address < 2 ^ 256) (hrun : s.halt = .Running) :
    runInstrSeq (middleTemplate shift address) {s with pc := pc, stack := value :: rest} =
      some { s with
        pc := pcAfter pc (middleTemplate shift address)
        stack := value :: rest
        memory := writeWord s.memory address (Challenge.EvmProof.Word.mask32
          (UInt256.shiftRight value (UInt256.ofNat shift)))
        activeWords := UInt256.ofNat (MachineState.activeWordsAfter s.activeWords.toNat address 32) } := by
  have h1 := run_duplicateShiftTemplate s pc value shift rest hstack hrun
  have h2 := run_maskTemplate s (pcAfter pc (duplicateShiftTemplate shift))
    (UInt256.shiftRight value (UInt256.ofNat shift)) (value :: rest)
    (by simp only [List.length_cons]; omega) hrun
  have h3 := run_storeTemplate s
    (pcAfter (pcAfter pc (duplicateShiftTemplate shift)) maskTemplate)
    (Challenge.EvmProof.Word.mask32 (UInt256.shiftRight value (UInt256.ofNat shift)))
    address (value :: rest) (by simp only [List.length_cons]; omega) haddress hrun
  have h23 := DenseScheduleTrace.runInstrSeq_append_running h2 (by exact hrun) h3
  unfold middleTemplate
  rw [DenseScheduleTrace.pcAfter_append, DenseScheduleTrace.pcAfter_append]
  exact DenseScheduleTrace.runInstrSeq_append_running h1 (by exact hrun) h23

theorem run_lastTemplate (s : State) (pc value : UInt256) (address : Nat)
    (rest : List UInt256) (hstack : rest.length < 1022)
    (haddress : address < 2 ^ 256) (hrun : s.halt = .Running) :
    runInstrSeq (lastTemplate address) {s with pc := pc, stack := value :: rest} =
      some { s with
        pc := pcAfter pc (lastTemplate address)
        stack := rest
        memory := writeWord s.memory address (Challenge.EvmProof.Word.mask32 value)
        activeWords := UInt256.ofNat (MachineState.activeWordsAfter s.activeWords.toNat address 32) } := by
  have h1 := run_maskTemplate s pc value rest hstack hrun
  have h2 := run_storeTemplate s (pcAfter pc maskTemplate)
    (Challenge.EvmProof.Word.mask32 value) address rest hstack haddress hrun
  unfold lastTemplate
  rw [DenseScheduleTrace.pcAfter_append]
  exact DenseScheduleTrace.runInstrSeq_append_running h1 (by exact hrun) h2

#print axioms run_firstTemplate
#print axioms run_middleTemplate
#print axioms run_lastTemplate

end Challenge.Ripemd160.Submission.Proofs.Bytecode.PairedScheduleStores

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.PairedScheduleHalves

open EvmSemantics EvmSemantics.EVM
open YulEvmCompiler
open StackRoundTrace DenseScheduleTemplate PairedScheduleMemory PairedScheduleStores

def chunkValue (value : UInt256) (j : Nat) : UInt256 :=
  if j = 0 then UInt256.shiftRight value (UInt256.ofNat 224)
  else if j = 7 then Challenge.EvmProof.Word.mask32 value
  else Challenge.EvmProof.Word.mask32
    (UInt256.shiftRight value (UInt256.ofNat (32 * (7 - j))))

def keepTemplate (first j : Nat) : List Instr :=
  if j = 0 then firstTemplate (cell (first + j))
  else middleTemplate (32 * (7 - j)) (cell (first + j))

def prefixTemplate (first : Nat) : Nat → List Instr
  | 0 => []
  | n + 1 => prefixTemplate first n ++ keepTemplate first n

def halfWords (value : UInt256) (first i : Nat) : UInt256 :=
  chunkValue value (i - first)

def halfTemplate (first : Nat) : List Instr :=
  prefixTemplate first 7 ++ lastTemplate (cell (first + 7))

theorem schedule_cell_lt (i : Nat) (hi : i ≤ 16) : cell i < 2 ^ 256 := by
  simp only [cell]
  norm_num
  omega

theorem run_keepTemplate (s : State) (pc value : UInt256)
    (first j : Nat) (rest : List UInt256)
    (hstack : rest.length < 1020) (hrun : s.halt = .Running)
    (hactive : 23 ≤ s.activeWords.toNat) (hslot : first + j ≤ 16) (hj : j < 7) :
    runInstrSeq (keepTemplate first j) {s with pc := pc, stack := value :: rest} =
      some { s with
        pc := pcAfter pc (keepTemplate first j)
        stack := value :: rest
        memory := writeWord s.memory (cell (first + j)) (chunkValue value j) } := by
  by_cases hzero : j = 0
  · have h := run_firstTemplate s pc value (cell (first + j)) rest hstack
      (schedule_cell_lt (first + j) hslot) hrun
    rw [active_wrapped_cell_preserved s.activeWords (first + j) hactive hslot] at h
    simpa only [keepTemplate, chunkValue, if_pos hzero] using h
  · have hseven : j ≠ 7 := by omega
    have h := run_middleTemplate s pc value (32 * (7 - j)) (cell (first + j))
      rest hstack (schedule_cell_lt (first + j) hslot) hrun
    rw [active_wrapped_cell_preserved s.activeWords (first + j) hactive hslot] at h
    simpa only [keepTemplate, chunkValue, if_neg hzero, if_neg hseven] using h

theorem run_prefixTemplate (s : State) (pc value : UInt256)
    (first n : Nat) (rest : List UInt256)
    (hstack : rest.length < 1020) (hrun : s.halt = .Running)
    (hactive : 23 ≤ s.activeWords.toNat) (hfirst : first + 8 ≤ 16) (hn : n ≤ 7) :
    runInstrSeq (prefixTemplate first n) {s with pc := pc, stack := value :: rest} =
      some { s with
        pc := pcAfter pc (prefixTemplate first n)
        stack := value :: rest
        memory := storeCells s.memory (halfWords value first) first n } := by
  induction n with
  | zero =>
    simp only [prefixTemplate, runInstrSeq, pcAfter, storeCells]
  | succ n ih =>
    have h1 := ih (by omega)
    have h2 := run_keepTemplate
      {s with memory := storeCells s.memory (halfWords value first) first n}
      (pcAfter pc (prefixTemplate first n)) value first n rest
      hstack hrun hactive (by omega) (by omega)
    have hjoin := DenseScheduleTrace.runInstrSeq_append_running h1 (by exact hrun) h2
    simpa only [prefixTemplate, DenseScheduleTrace.pcAfter_append, storeCells,
      halfWords, Nat.add_sub_cancel_left] using hjoin

theorem run_halfTemplate (s : State) (pc value : UInt256)
    (first : Nat) (rest : List UInt256)
    (hstack : rest.length < 1020) (hrun : s.halt = .Running)
    (hactive : 23 ≤ s.activeWords.toNat) (hfirst : first + 8 ≤ 16) :
    runInstrSeq (halfTemplate first) {s with pc := pc, stack := value :: rest} =
      some { s with
        pc := pcAfter pc (halfTemplate first)
        stack := rest
        memory := storeCells s.memory (halfWords value first) first 8 } := by
  have h1 := run_prefixTemplate s pc value first 7 rest hstack hrun hactive hfirst (by decide)
  have h2 := run_lastTemplate
    {s with memory := storeCells s.memory (halfWords value first) first 7}
    (pcAfter pc (prefixTemplate first 7)) value (cell (first + 7)) rest
    (by omega) (schedule_cell_lt (first + 7) (by omega)) hrun
  rw [active_wrapped_cell_preserved s.activeWords (first + 7) hactive (by omega)] at h2
  have hjoin := DenseScheduleTrace.runInstrSeq_append_running h1 (by exact hrun) h2
  simpa only [halfTemplate, DenseScheduleTrace.pcAfter_append, storeCells,
    halfWords, Nat.add_sub_cancel_left, chunkValue, show ¬(7 = 0) by decide,
    if_false, if_true] using hjoin

#print axioms schedule_cell_lt
#print axioms run_keepTemplate
#print axioms run_prefixTemplate
#print axioms run_halfTemplate

end Challenge.Ripemd160.Submission.Proofs.Bytecode.PairedScheduleHalves


namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.PairedScheduleCombined

open EvmSemantics EvmSemantics.EVM
open YulEvmCompiler
open StackRoundTrace DenseScheduleTemplate PairedScheduleMemory PairedScheduleHalves

def reversedHalfTemplate (first : Nat) : List Instr :=
  (endianStage8 ++ endianStage16) ++ halfTemplate first

theorem run_reversedHalfTemplate (s : State) (pc value : UInt256)
    (first : Nat) (rest : List UInt256)
    (hstack : rest.length < 1020) (hrun : s.halt = .Running)
    (hactive : 23 ≤ s.activeWords.toNat) (hfirst : first + 8 ≤ 16) :
    runInstrSeq (reversedHalfTemplate first) {s with pc := pc, stack := value :: rest} =
      some { s with
        pc := pcAfter pc (reversedHalfTemplate first)
        stack := rest
        memory := storeCells s.memory (halfWords (packedWord value) first) first 8 } := by
  have h1 := DenseScheduleTrace.runInstrSeq_endianStage s pc value 8 mask8
    rest hstack (Or.inl ⟨rfl, rfl⟩) hrun
  dsimp only [DenseScheduleTrace.stageState] at h1
  have h2 := DenseScheduleTrace.runInstrSeq_endianStage s
    (pcAfter pc (endianStage 8 mask8)) (packedStage value 8 mask8) 16 mask16
    rest hstack (Or.inr ⟨rfl, rfl⟩) hrun
  dsimp only [DenseScheduleTrace.stageState] at h2
  have h12 := DenseScheduleTrace.runInstrSeq_append_running
    (first := (endianStage 8 mask8)) (second := (endianStage 16 mask16)) h1 (by exact hrun) h2
  have h3 := run_halfTemplate s
    (pcAfter (pcAfter pc (endianStage 8 mask8)) (endianStage 16 mask16)) (packedWord value)
    first rest hstack hrun hactive hfirst
  have hjoin := DenseScheduleTrace.runInstrSeq_append_running
    (first := (endianStage 8 mask8) ++ (endianStage 16 mask16)) (second := halfTemplate first)
    h12 (by exact hrun) h3
  simpa only [reversedHalfTemplate, endianStage8, endianStage16, DenseScheduleTrace.pcAfter_append] using hjoin

def scheduleWords (s : State) (messageOffset : UInt256) (i : Nat) : UInt256 :=
  if i < 8 then halfWords (packedInput0 s messageOffset) 0 i
  else halfWords (packedInput1 s messageOffset) 8 i

theorem storeCells_congr (memory : ByteArray) (words other : Nat → UInt256)
    (first n : Nat)
    (heq : ∀ i, first ≤ i → i < first + n → words i = other i) :
    storeCells memory words first n = storeCells memory other first n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [storeCells]
    rw [ih (fun i hlow hhigh => heq i hlow (by omega)),
      heq (first + n) (by omega) (by omega)]

theorem store_upper_schedule (memory : ByteArray) (s : State) (messageOffset : UInt256) :
    storeCells memory (halfWords (packedInput1 s messageOffset) 8) 8 8 =
      storeCells memory (scheduleWords s messageOffset) 8 8 := by
  apply storeCells_congr
  intro i hlo _
  simp only [scheduleWords, if_neg (by omega : ¬i < 8)]

theorem store_lower_schedule (memory : ByteArray) (s : State) (messageOffset : UInt256) :
    storeCells memory (halfWords (packedInput0 s messageOffset) 0) 0 8 =
      storeCells memory (scheduleWords s messageOffset) 0 8 := by
  apply storeCells_congr
  intro i _ hhi
  simp only [scheduleWords, if_pos (by omega : i < 8)]

def sentinelTemplate : List Instr :=
  [.push ⟨0, by decide⟩ (UInt256.ofNat 0)] ++ PairedSchedulePrimitives.storeTemplate (cell 16)

theorem run_sentinelTemplate (s : State) (pc : UInt256) (rest : List UInt256)
    (hstack : rest.length < 1022) (hrun : s.halt = .Running)
    (hactive : 23 ≤ s.activeWords.toNat) :
    runInstrSeq sentinelTemplate {s with pc := pc, stack := rest} =
      some { s with
        pc := pcAfter pc sentinelTemplate
        stack := rest
        memory := writeWord s.memory (cell 16) (UInt256.ofNat 0) } := by
  have hcap : rest.length < 1024 := by omega
  have h1 : runInstrSeq [.push ⟨0, by decide⟩ (UInt256.ofNat 0)] {s with pc := pc, stack := rest} =
      some { s with
        pc := pcAfter pc [.push ⟨0, by decide⟩ (UInt256.ofNat 0)]
        stack := UInt256.ofNat 0 :: rest } := by
    simp [runInstrSeq, Challenge.EvmProof.Stepper.runInstr, pcAfter,
      hrun, hcap, UInt256.succ, Instr.size]
    exact ⟨rfl, rfl⟩
  have h2 := PairedSchedulePrimitives.run_storeTemplate s
    (pcAfter pc [.push ⟨0, by decide⟩ (UInt256.ofNat 0)]) (UInt256.ofNat 0) (cell 16) rest hstack
    (schedule_cell_lt 16 (by decide)) hrun
  rw [active_wrapped_cell_preserved s.activeWords 16 hactive (by decide)] at h2
  have hjoin := DenseScheduleTrace.runInstrSeq_append_running h1 (by exact hrun) h2
  simpa only [sentinelTemplate, DenseScheduleTrace.pcAfter_append] using hjoin

def fullTemplate : List Instr :=
  ((initialTemplate ++ reversedHalfTemplate 8) ++ reversedHalfTemplate 0) ++ sentinelTemplate

theorem run_fullTemplate (s : State) (pc messageOffset returnPC : UInt256)
    (rest : List UInt256) (hstack : rest.length < 1018) (hrun : s.halt = .Running)
    (hactive : 23 ≤ (loadedActiveWords s messageOffset).toNat) :
    runInstrSeq fullTemplate (scheduleEntry s pc messageOffset returnPC rest) =
      some { s with
        pc := pcAfter pc fullTemplate
        stack := returnPC :: rest
        memory := normalizedMemory s.memory (scheduleWords s messageOffset)
        activeWords := loadedActiveWords s messageOffset } := by
  have h1 := DenseScheduleTrace.runInstrSeq_initial s pc messageOffset returnPC rest hstack hrun
  have h2 := run_reversedHalfTemplate
    {s with activeWords := loadedActiveWords s messageOffset}
    (pcAfter pc initialTemplate) (inputWord1 s messageOffset) 8
    (inputWord0 s messageOffset :: returnPC :: rest)
    (by simp only [List.length_cons]; omega) hrun hactive (by decide)
  have h12 := DenseScheduleTrace.runInstrSeq_append_running h1 (by exact hrun) h2
  have h3 := run_reversedHalfTemplate
    { s with
      activeWords := loadedActiveWords s messageOffset
      memory := storeCells s.memory (halfWords (packedInput1 s messageOffset) 8) 8 8 }
    (pcAfter (pcAfter pc initialTemplate) (reversedHalfTemplate 8))
    (inputWord0 s messageOffset) 0 (returnPC :: rest)
    (by simp only [List.length_cons]; omega) hrun hactive (by decide)
  have h123 := DenseScheduleTrace.runInstrSeq_append_running h12 (by exact hrun) h3
  have h4 := run_sentinelTemplate
    { s with
      activeWords := loadedActiveWords s messageOffset
      memory := storeCells
        (storeCells s.memory (halfWords (packedInput1 s messageOffset) 8) 8 8)
        (halfWords (packedInput0 s messageOffset) 0) 0 8 }
    (pcAfter (pcAfter (pcAfter pc initialTemplate) (reversedHalfTemplate 8))
      (reversedHalfTemplate 0)) (returnPC :: rest)
    (by simp only [List.length_cons]; omega) hrun hactive
  have hjoin := DenseScheduleTrace.runInstrSeq_append_running h123 (by exact hrun) h4
  rw [store_upper_schedule, store_lower_schedule] at hjoin
  simpa only [fullTemplate, DenseScheduleTrace.pcAfter_append, normalizedMemory] using hjoin

#print axioms run_reversedHalfTemplate
#print axioms storeCells_congr
#print axioms store_upper_schedule
#print axioms store_lower_schedule
#print axioms run_sentinelTemplate
#print axioms run_fullTemplate

end Challenge.Ripemd160.Submission.Proofs.Bytecode.PairedScheduleCombined




namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.PairedScheduleContract

open EvmSemantics EvmSemantics.EVM
open YulEvmCompiler
open StackRoundTrace DenseScheduleTemplate PairedScheduleMemory PairedScheduleHalves
open PairedScheduleCombined

theorem pointer_add32_toNat (p : Nat) (hbound : p + 64 < 2 ^ 256) :
    (UInt256.ofNat p + UInt256.ofNat 32).toNat = p + 32 := by
  rw [Challenge.EvmProof.Word.ofNat_add_ofNat (by omega),
    Challenge.EvmProof.Word.word_toNat_ofNat, Nat.mod_eq_of_lt (by omega)]

theorem loaded_active_ge23 (s : State) (p : Nat)
    (hp : 736 ≤ p) (hbound : p + 64 < 2 ^ 256) :
    23 ≤ (loadedActiveWords s (UInt256.ofNat p)).toNat := by
  have hcur := (activeAfterWord s.activeWords (UInt256.ofNat p)).val.isLt
  have hnew : MachineState.activeWordsAfter
      (activeAfterWord s.activeWords (UInt256.ofNat p)).toNat (p + 32) 32 < 2 ^ 256 := by
    simp only [MachineState.activeWordsAfter, if_neg (by decide : (32 : Nat) ≠ 0)]
    apply Nat.max_lt.mpr
    constructor
    · exact hcur
    · omega
  change 23 ≤ (UInt256.ofNat (MachineState.activeWordsAfter
    (activeAfterWord s.activeWords (UInt256.ofNat p)).toNat
    (UInt256.ofNat p + UInt256.ofNat 32).toNat 32)).toNat
  rw [pointer_add32_toNat p hbound, Challenge.EvmProof.Word.word_toNat_ofNat,
    Nat.mod_eq_of_lt hnew]
  exact active_load_ge23 _ _ (by omega)

theorem packedWord_eq_reversedWord (value : UInt256) :
    packedWord value = PairedScheduleData.reversedWord value := by
  simp only [packedWord, PairedScheduleData.reversedWord,
    DenseEndianMultiply.multipliedStage16_eq_packedStage,
    DenseEndianMultiply.multipliedStage8_eq_packedStage]

theorem chunkValue_packed (value : UInt256) (j : Nat) :
    chunkValue (packedWord value) j = PairedScheduleData.chunk value j := by
  rw [packedWord_eq_reversedWord]
  rfl

theorem scheduleWords_eq_extracted (s : State) (p i : Nat)
    (hi : i < 16) (hbound : p + 64 < 2 ^ 256) :
    scheduleWords s (UInt256.ofNat p) i =
      PairedScheduleData.extractedWord s.memory p i := by
  have hp : (UInt256.ofNat p).toNat = p := by
    rw [Challenge.EvmProof.Word.word_toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  by_cases hlo : i < 8
  · simp only [scheduleWords, if_pos hlo, halfWords, Nat.sub_zero,
      packedInput0, inputWord0, hp, chunkValue_packed, PairedScheduleData.extractedWord,
      Nat.div_eq_of_lt hlo, Nat.mod_eq_of_lt hlo, Nat.mul_zero, Nat.add_zero]
  · have hdiv : i / 8 = 1 := by omega
    have hmod : i % 8 = i - 8 := by omega
    simp only [scheduleWords, if_neg hlo, halfWords,
      packedInput1, inputWord1, pointer_add32_toNat p hbound, chunkValue_packed,
      PairedScheduleData.extractedWord, hdiv, hmod, Nat.mul_one]

theorem normalizedMemory_congr (memory : ByteArray) (words other : Nat → UInt256)
    (heq : ∀ i, i < 16 → words i = other i) :
    normalizedMemory memory words = normalizedMemory memory other := by
  unfold normalizedMemory
  rw [storeCells_congr memory words other 8 8 (fun i _ hi => heq i (by omega)),
    storeCells_congr _ words other 0 8 (fun i _ hi => heq i (by omega))]

theorem run_fullTemplate_natural (s : State) (pc returnPC : UInt256)
    (p : Nat) (rest : List UInt256)
    (hstack : rest.length < 1018) (hrun : s.halt = .Running)
    (hp : 736 ≤ p) (hbound : p + 64 < 2 ^ 256) :
    runInstrSeq fullTemplate (scheduleEntry s pc (UInt256.ofNat p) returnPC rest) =
      some { s with
        pc := pcAfter pc fullTemplate
        stack := returnPC :: rest
        memory := normalizedMemory s.memory (PairedScheduleData.extractedWord s.memory p)
        activeWords := loadedActiveWords s (UInt256.ofNat p) } := by
  have h := run_fullTemplate s pc (UInt256.ofNat p) returnPC rest hstack hrun
    (loaded_active_ge23 s p hp hbound)
  rw [normalizedMemory_congr s.memory (scheduleWords s (UInt256.ofNat p))
    (PairedScheduleData.extractedWord s.memory p)
    (fun i hi => scheduleWords_eq_extracted s p i hi hbound)] at h
  exact h

theorem fullTemplate_length : fullTemplate.length = 152 := by
  norm_num [fullTemplate, initialTemplate, reversedHalfTemplate, endianStage8, endianStage16,
    endianStage, halfTemplate, prefixTemplate, keepTemplate, PairedScheduleStores.firstTemplate,
    PairedScheduleStores.middleTemplate, PairedScheduleStores.lastTemplate,
    PairedSchedulePrimitives.duplicateShiftTemplate, PairedSchedulePrimitives.maskTemplate,
    PairedSchedulePrimitives.storeTemplate, sentinelTemplate]

theorem fullTemplate_byteLength : (assembleBytes fullTemplate).length = 391 := by
  rw [DenseScheduleTemplate.assembleBytes_length]
  norm_num [fullTemplate, initialTemplate, reversedHalfTemplate, endianStage8, endianStage16,
    endianStage, endianMaskPush, endianFactorPush, endianFactor,
    halfTemplate, prefixTemplate, keepTemplate, PairedScheduleStores.firstTemplate,
    PairedScheduleStores.middleTemplate, PairedScheduleStores.lastTemplate,
    PairedSchedulePrimitives.duplicateShiftTemplate, PairedSchedulePrimitives.maskTemplate,
    PairedSchedulePrimitives.storeTemplate, sentinelTemplate, cell,
    op, push1, push2, push3, dup1, swap1]

theorem fullTemplate_staticGas : staticGas fullTemplate = 461 := by
  norm_num [staticGas, fullTemplate, initialTemplate, reversedHalfTemplate,
    endianStage8, endianStage16, endianStage, endianMaskPush, endianFactorPush, endianFactor,
    halfTemplate, prefixTemplate, keepTemplate, PairedScheduleStores.firstTemplate,
    PairedScheduleStores.middleTemplate, PairedScheduleStores.lastTemplate,
    PairedSchedulePrimitives.duplicateShiftTemplate, PairedSchedulePrimitives.maskTemplate,
    PairedSchedulePrimitives.storeTemplate, sentinelTemplate, cell,
    op, push1, push2, push3, dup1, swap1,
    Challenge.EvmProof.Meter.instrStaticCost, Gas.baseCost]

#print axioms pointer_add32_toNat
#print axioms loaded_active_ge23
#print axioms packedWord_eq_reversedWord
#print axioms chunkValue_packed
#print axioms scheduleWords_eq_extracted
#print axioms normalizedMemory_congr
#print axioms run_fullTemplate_natural
#print axioms fullTemplate_length
#print axioms fullTemplate_byteLength
#print axioms fullTemplate_staticGas

end Challenge.Ripemd160.Submission.Proofs.Bytecode.PairedScheduleContract



namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.PairedScheduleExact

open EvmSemantics EvmSemantics.EVM
open YulEvmCompiler
open DenseScheduleTemplate PairedScheduleMemory PairedScheduleHalves PairedScheduleCombined

/-- Exact instruction decoding of the frozen 5337-byte candidate's 393-byte
window beginning at physical PC464. This list is not generated from test inputs. -/
def frozenInstructions : List Instr :=
  [.op .JUMPDEST,
   .op (.Dup ⟨0, by decide⟩),
   .op .MLOAD,
   .op (.Swap ⟨0, by decide⟩),
   .push ⟨1, by decide⟩ (UInt256.ofNat 0x20),
   .op .ADD,
   .op .MLOAD,
   .op (.Dup ⟨0, by decide⟩),
   .op (.Dup ⟨0, by decide⟩),
   .push ⟨1, by decide⟩ (UInt256.ofNat 0x08),
   .op .SHR,
   .op .XOR,
   .push ⟨31, by decide⟩ (UInt256.ofNat 0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff),
   .op .AND,
   .push ⟨2, by decide⟩ (UInt256.ofNat 0x0101),
   .op .MUL,
   .op .XOR,
   .op (.Dup ⟨0, by decide⟩),
   .op (.Dup ⟨0, by decide⟩),
   .push ⟨1, by decide⟩ (UInt256.ofNat 0x10),
   .op .SHR,
   .op .XOR,
   .push ⟨30, by decide⟩ (UInt256.ofNat 0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff),
   .op .AND,
   .push ⟨3, by decide⟩ (UInt256.ofNat 0x010001),
   .op .MUL,
   .op .XOR,
   .op (.Dup ⟨0, by decide⟩),
   .push ⟨1, by decide⟩ (UInt256.ofNat 0xe0),
   .op .SHR,
   .push ⟨2, by decide⟩ (UInt256.ofNat 0x01c0),
   .op .MSTORE,
   .op (.Dup ⟨0, by decide⟩),
   .push ⟨1, by decide⟩ (UInt256.ofNat 0xc0),
   .op .SHR,
   .push ⟨4, by decide⟩ (UInt256.ofNat 0xffffffff),
   .op .AND,
   .push ⟨2, by decide⟩ (UInt256.ofNat 0x01e0),
   .op .MSTORE,
   .op (.Dup ⟨0, by decide⟩),
   .push ⟨1, by decide⟩ (UInt256.ofNat 0xa0),
   .op .SHR,
   .push ⟨4, by decide⟩ (UInt256.ofNat 0xffffffff),
   .op .AND,
   .push ⟨2, by decide⟩ (UInt256.ofNat 0x0200),
   .op .MSTORE,
   .op (.Dup ⟨0, by decide⟩),
   .push ⟨1, by decide⟩ (UInt256.ofNat 0x80),
   .op .SHR,
   .push ⟨4, by decide⟩ (UInt256.ofNat 0xffffffff),
   .op .AND,
   .push ⟨2, by decide⟩ (UInt256.ofNat 0x0220),
   .op .MSTORE,
   .op (.Dup ⟨0, by decide⟩),
   .push ⟨1, by decide⟩ (UInt256.ofNat 0x60),
   .op .SHR,
   .push ⟨4, by decide⟩ (UInt256.ofNat 0xffffffff),
   .op .AND,
   .push ⟨2, by decide⟩ (UInt256.ofNat 0x0240),
   .op .MSTORE,
   .op (.Dup ⟨0, by decide⟩),
   .push ⟨1, by decide⟩ (UInt256.ofNat 0x40),
   .op .SHR,
   .push ⟨4, by decide⟩ (UInt256.ofNat 0xffffffff),
   .op .AND,
   .push ⟨2, by decide⟩ (UInt256.ofNat 0x0260),
   .op .MSTORE,
   .op (.Dup ⟨0, by decide⟩),
   .push ⟨1, by decide⟩ (UInt256.ofNat 0x20),
   .op .SHR,
   .push ⟨4, by decide⟩ (UInt256.ofNat 0xffffffff),
   .op .AND,
   .push ⟨2, by decide⟩ (UInt256.ofNat 0x0280),
   .op .MSTORE,
   .push ⟨4, by decide⟩ (UInt256.ofNat 0xffffffff),
   .op .AND,
   .push ⟨2, by decide⟩ (UInt256.ofNat 0x02a0),
   .op .MSTORE,
   .op (.Dup ⟨0, by decide⟩),
   .op (.Dup ⟨0, by decide⟩),
   .push ⟨1, by decide⟩ (UInt256.ofNat 0x08),
   .op .SHR,
   .op .XOR,
   .push ⟨31, by decide⟩ (UInt256.ofNat 0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff),
   .op .AND,
   .push ⟨2, by decide⟩ (UInt256.ofNat 0x0101),
   .op .MUL,
   .op .XOR,
   .op (.Dup ⟨0, by decide⟩),
   .op (.Dup ⟨0, by decide⟩),
   .push ⟨1, by decide⟩ (UInt256.ofNat 0x10),
   .op .SHR,
   .op .XOR,
   .push ⟨30, by decide⟩ (UInt256.ofNat 0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff),
   .op .AND,
   .push ⟨3, by decide⟩ (UInt256.ofNat 0x010001),
   .op .MUL,
   .op .XOR,
   .op (.Dup ⟨0, by decide⟩),
   .push ⟨1, by decide⟩ (UInt256.ofNat 0xe0),
   .op .SHR,
   .push ⟨1, by decide⟩ (UInt256.ofNat 0x00c0),
   .op .MSTORE,
   .op (.Dup ⟨0, by decide⟩),
   .push ⟨1, by decide⟩ (UInt256.ofNat 0xc0),
   .op .SHR,
   .push ⟨4, by decide⟩ (UInt256.ofNat 0xffffffff),
   .op .AND,
   .push ⟨1, by decide⟩ (UInt256.ofNat 0x00e0),
   .op .MSTORE,
   .op (.Dup ⟨0, by decide⟩),
   .push ⟨1, by decide⟩ (UInt256.ofNat 0xa0),
   .op .SHR,
   .push ⟨4, by decide⟩ (UInt256.ofNat 0xffffffff),
   .op .AND,
   .push ⟨2, by decide⟩ (UInt256.ofNat 0x0100),
   .op .MSTORE,
   .op (.Dup ⟨0, by decide⟩),
   .push ⟨1, by decide⟩ (UInt256.ofNat 0x80),
   .op .SHR,
   .push ⟨4, by decide⟩ (UInt256.ofNat 0xffffffff),
   .op .AND,
   .push ⟨2, by decide⟩ (UInt256.ofNat 0x0120),
   .op .MSTORE,
   .op (.Dup ⟨0, by decide⟩),
   .push ⟨1, by decide⟩ (UInt256.ofNat 0x60),
   .op .SHR,
   .push ⟨4, by decide⟩ (UInt256.ofNat 0xffffffff),
   .op .AND,
   .push ⟨2, by decide⟩ (UInt256.ofNat 0x0140),
   .op .MSTORE,
   .op (.Dup ⟨0, by decide⟩),
   .push ⟨1, by decide⟩ (UInt256.ofNat 0x40),
   .op .SHR,
   .push ⟨4, by decide⟩ (UInt256.ofNat 0xffffffff),
   .op .AND,
   .push ⟨2, by decide⟩ (UInt256.ofNat 0x0160),
   .op .MSTORE,
   .op (.Dup ⟨0, by decide⟩),
   .push ⟨1, by decide⟩ (UInt256.ofNat 0x20),
   .op .SHR,
   .push ⟨4, by decide⟩ (UInt256.ofNat 0xffffffff),
   .op .AND,
   .push ⟨2, by decide⟩ (UInt256.ofNat 0x0180),
   .op .MSTORE,
   .push ⟨4, by decide⟩ (UInt256.ofNat 0xffffffff),
   .op .AND,
   .push ⟨2, by decide⟩ (UInt256.ofNat 0x01a0),
   .op .MSTORE,
   .push ⟨0, by decide⟩ (UInt256.ofNat 0),
   .push ⟨2, by decide⟩ (UInt256.ofNat 0x02c0),
   .op .MSTORE]

theorem fullTemplate_eq_frozenInstructions : fullTemplate = frozenInstructions := by
  norm_num [fullTemplate, frozenInstructions, initialTemplate, reversedHalfTemplate,
    endianStage8, endianStage16, endianStage, endianMaskPush, endianFactorPush,
    endianFactor, halfTemplate, prefixTemplate, keepTemplate, PairedScheduleStores.firstTemplate,
    PairedScheduleStores.middleTemplate, PairedScheduleStores.lastTemplate,
    PairedSchedulePrimitives.duplicateShiftTemplate, PairedSchedulePrimitives.maskTemplate,
    PairedSchedulePrimitives.storeTemplate, sentinelTemplate, cell,
    op, push1, push2, push3, dup1, swap1, mask8, mask16]

#print axioms fullTemplate_eq_frozenInstructions

end Challenge.Ripemd160.Submission.Proofs.Bytecode.PairedScheduleExact


namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.PairedScheduleLift

open EvmSemantics EvmSemantics.EVM
open YulEvmCompiler Challenge.EvmProof
open StackRoundTemplate StackRoundTrace DenseScheduleTemplate PairedScheduleMemory
open PairedScheduleCombined PairedScheduleContract PairedScheduleExact

theorem fullTemplate_advances :
    ∀ instruction ∈ fullTemplate, DenseScheduleLift.Advances instruction := by
  intro instruction hmem
  rw [fullTemplate_eq_frozenInstructions] at hmem
  simp only [frozenInstructions, List.mem_cons, List.not_mem_nil, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals first
    | exact Or.inl (Or.inl (StraightLine.push _ _))
    | exact Or.inl (Or.inl StraightLine.add)
    | exact Or.inl (Or.inl StraightLine.and)
    | exact Or.inl (Or.inl StraightLine.xor)
    | exact Or.inl (Or.inl StraightLine.shr)
    | exact Or.inl (Or.inl StraightLine.mload)
    | exact Or.inl (Or.inl (StraightLine.dup _))
    | exact Or.inl (Or.inl (StraightLine.swap _))
    | exact Or.inr (Or.inl rfl)
    | exact Or.inr (Or.inr rfl)
    | exact Or.inl (Or.inr (Or.inr rfl))

theorem runLocatedBlock_fullTemplate {artifact : ProgramArtifact} {fork : Fork}
    (site : GenericRoundSite artifact fork fullTemplate)
    (s : State) (returnPC : UInt256) (p : Nat) (rest : List UInt256)
    (hstack : rest.length < 1018) (hrun : s.halt = .Running)
    (hp : 736 ≤ p) (hbound : p + 64 < 2 ^ 256) :
    Stepper.runLocatedBlock site.path
      (scheduleEntry s site.startPC (UInt256.ofNat p) returnPC rest) =
      some { s with
        pc := site.endPC
        stack := returnPC :: rest
        memory := normalizedMemory s.memory (PairedScheduleData.extractedWord s.memory p)
        activeWords := loadedActiveWords s (UInt256.ofNat p) } := by
  have hend : site.endPC = pcAfter site.startPC fullTemplate := by
    have h := endPC_eq_pcAfter_sites site.sites site.startPC site.endPC
      site.head_eq site.end_eq site.contiguous
    rwa [site.instruction_eq] at h
  rw [DenseScheduleLift.runLocatedBlock_eq_raw site fullTemplate_advances
    (scheduleEntry s site.startPC (UInt256.ofNat p) returnPC rest) rfl]
  have h := run_fullTemplate_natural s site.startPC returnPC p rest hstack hrun hp hbound
  rw [← hend] at h
  exact h

def gasSteps_fullTemplate {artifact : ProgramArtifact} {fork : Fork}
    (site : GenericRoundSite artifact fork fullTemplate)
    (s : State) (returnPC : UInt256) (p : Nat) (rest : List UInt256)
    (hstack : rest.length < 1018) (hrun : s.halt = .Running)
    (hp : 736 ≤ p) (hbound : p + 64 < 2 ^ 256)
    (hcode : s.executionEnv.code = artifact.code) (hfork : s.fork = fork)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    GasSteps (scheduleEntry s site.startPC (UInt256.ofNat p) returnPC rest)
      { s with
        pc := site.endPC
        stack := returnPC :: rest
        memory := normalizedMemory s.memory (PairedScheduleData.extractedWord s.memory p)
        activeWords := loadedActiveWords s (UInt256.ofNat p) } := by
  apply Stepper.runLocatedBlock_sound artifact fork site.path
  · exact hcode
  · exact hfork
  · exact runLocatedBlock_fullTemplate site s returnPC p rest hstack hrun hp hbound
  · exact hrun
  · exact hnp

#print axioms fullTemplate_advances
#print axioms runLocatedBlock_fullTemplate
#print axioms gasSteps_fullTemplate

end Challenge.Ripemd160.Submission.Proofs.Bytecode.PairedScheduleLift
