import Challenge.Modexp.Submission.Proofs.CRT.CRTAdapterMeaning
import Challenge.Modexp.Submission.Proofs.CRT.MixedInput
set_option warningAsError true
set_option linter.unusedVariables false
set_option maxHeartbeats 3000000
set_option exponentiation.threshold 4096

namespace HistoricalSearch.CRTLoopArithmetic
open EvmSemantics EvmSemantics.EVM
open HistoricalSearch.ColumnMemory HistoricalSearch.ColumnSequence
open HistoricalSearch.CRTAdapterMeaning HistoricalSearch.CRTMemoryCells
open HistoricalSearch.MixedMontgomery
open Challenge.Modexp.Submission.Proofs.Fast
open Challenge.EvmProof.Memory

/-- Exact mixed-radix digits, with the short top limb. -/
structure Represents (mem : ByteArray) (A : Nat) : Prop where
  bounded : A < 2^2048
  low : ∀ i < 8, (aRead mem i).toNat = A / 2^(244*i) % 2^244
  high : (aRead mem 8).toNat = A / 2^1952

theorem entry_represents (mem : ByteArray) (counter : UInt256) (A : Nat)
    (ha : Model.FastRepresents mem 2368 8 A) :
    Represents (entryMemory mem counter) A := by
  refine ⟨?_, ?_, ?_⟩
  · exact Model.fastRepresents_lt ha
  · intro i hi
    rw [aRead, entry_operand mem counter i (by omega)]
    exact inputWord_low ha i hi
  · rw [aRead, entry_operand mem counter 8 (by decide)]
    exact inputWord_high ha

def checkedMemory (mem : ByteArray) : ByteArray :=
  writeCell mem (1760, UInt256.shiftRight (rawDigits mem 8) (UInt256.ofNat 192))

theorem checked_word (mem : ByteArray) (addr : Nat)
    (h : addr+32 ≤ 1760 ∨ 1792 ≤ addr) :
    MachineState.readWord (checkedMemory mem) addr = MachineState.readWord mem addr := by
  unfold checkedMemory writeCell
  exact read_store_disjoint _ _ _ _ h

theorem checked_digits (mem : ByteArray) (i : Nat) (hi : i < 9) :
    rawDigits (checkedMemory mem) i = rawDigits mem i := by
  unfold rawDigits
  exact checked_word mem _ (Or.inl (by omega))

theorem checked_value (mem : ByteArray) :
    CRTWordPacking.value (rawDigits (checkedMemory mem)) = CRTWordPacking.value (rawDigits mem) := by
  unfold CRTWordPacking.value weighted
  congr 1
  apply Finset.sum_congr rfl
  intro i hi
  dsimp only
  rw [checked_digits mem i (Finset.mem_range.mp hi)]

theorem checked_flag (mem : ByteArray)
    (hd : ∀ i < 9, (rawDigits mem i).toNat < 2^244) :
    (MachineState.readWord (checkedMemory mem) 1760).toNat =
      CRTWordPacking.value (rawDigits mem) / 2^2048 := by
  rw [checkedMemory, writeCell, readWord_writeWord]
  exact CRTWordPacking.overflow_toNat _ hd

theorem checked_preserves (mem : ByteArray) (A : Nat) (h : Represents mem A) :
    Represents (checkedMemory mem) A := by
  refine ⟨h.bounded, ?_, ?_⟩
  · intro i hi
    rw [aRead, checked_word mem _ (Or.inl (by omega))]
    exact h.low i hi
  · rw [aRead, checked_word mem _ (Or.inl (by decide))]
    exact h.high

theorem checked_keep (mem : ByteArray) (addr width : Nat)
    (h : addr+width ≤ 1760 ∨ 1792 ≤ addr) :
    MachineState.readPadded (checkedMemory mem) addr width = MachineState.readPadded mem addr width := by
  unfold checkedMemory writeCell
  apply readPadded_writeBytes_disjoint
  simpa only [YulEvmCompiler.BytesLemmas.natToBytesPadded_size] using h

variable (s : State) (minv : UInt256) (n : Nat → UInt256) (rest : List UInt256)

def result : State := states s minv n rest 17
def quotient : Nat := CRTWordPacking.value (rawDigits (result s minv n rest).memory)

theorem result_preserves (A : Nat) (ha : Represents s.memory A) :
    Represents (result s minv n rest).memory A := by
  refine ⟨ha.bounded, ?_, ?_⟩
  · intro i hi
    rw [result, a_preserved s minv n rest 17 (by decide) i (by omega)]
    exact ha.low i hi
  · rw [result, a_preserved s minv n rest 17 (by decide) 8 (by decide)]
    exact ha.high

/-- The actual seventeen sequential column models produce the Montgomery
square and a bounded raw quotient. No assumptions concern unwritten scratch. -/
theorem result_contract (A N : Nat) (ha : Represents s.memory A)
    (hN : N < 2^2048) (hpos : 0 < N) (hodd : Odd N)
    (hnlow : ∀ i < 8, (n i).toNat = N / 2^(244*i) % 2^244)
    (hnhigh : (n 8).toNat = N / 2^1952)
    (hinv : (N*minv.toNat+1) % 2^256 = 0) :
    (∀ i < 9, (rawDigits (result s minv n rest).memory i).toNat < 2^244) ∧
    quotient s minv n rest < 2^2048+N ∧
    normalize (2^2048) N (quotient s minv n rest) < 2^2048 ∧
    normalize (2^2048) N (quotient s minv n rest) % N = Model.montMul N (2^2048) A A := by
  have hA := MixedInput.value A (aRead s.memory) ha.bounded ha.low ha.high
  have hN' := MixedInput.value N n hN hnlow hnhigh
  have hn0 : (n 0).toNat = N % GeneratedArithmetic.radix := by
    simpa [GeneratedArithmetic.radix] using hnlow 0 (by decide)
  exact KernelArithmetic.contract s minv n rest A N hA.2.1 hN'.2.1 hA.2.2 hN'.2.2
    hA.1 hN'.1 hn0 hinv ha.bounded hpos hN hodd

/-- A non-overflow round can be fed directly back into the same column kernel. -/
theorem retained_represents (mem : ByteArray)
    (hd : ∀ i < 9, (rawDigits mem i).toNat < 2^244)
    (hq : CRTWordPacking.value (rawDigits mem) < 2^2048) :
    Represents (retainedMemory (checkedMemory mem)) (CRTWordPacking.value (rawDigits mem)) := by
  have hd' : ∀ i < 9, (rawDigits (checkedMemory mem) i).toNat < 2^244 := by
    intro i hi
    rw [checked_digits mem i hi]
    exact hd i hi
  refine ⟨hq, ?_, ?_⟩
  · intro i hi
    change (MachineState.readWord _ _).toNat = _
    rw [retained_operand_low _ i hi hd', checked_value]
  · change (MachineState.readWord _ 1024).toNat = _
    rw [retained_operand_high _ hd', checked_value]

theorem exit_representation (mem : ByteArray)
    (hd : ∀ i < 9, (rawDigits mem i).toNat < 2^244) :
    Model.FastRepresents (exitMemory (checkedMemory mem)) 2112 8
      (CRTWordPacking.value (rawDigits mem) % 2^2048) := by
  have hd' : ∀ i < 9, (rawDigits (checkedMemory mem) i).toNat < 2^244 := by
    intro i hi
    rw [checked_digits mem i hi]
    exact hd i hi
  simpa only [checked_value] using exit_represents (checkedMemory mem) hd'

#print axioms entry_represents
#print axioms checked_value
#print axioms checked_flag
#print axioms checked_preserves
#print axioms checked_keep
#print axioms result_preserves
#print axioms result_contract
#print axioms retained_represents
#print axioms exit_representation
end HistoricalSearch.CRTLoopArithmetic
