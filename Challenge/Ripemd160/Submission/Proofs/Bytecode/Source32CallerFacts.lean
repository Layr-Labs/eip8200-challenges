import Challenge.Ripemd160.Submission.Proofs.Bytecode.Source32Memory
import Challenge.Ripemd160.Submission.Proofs.Bytecode.PaddingTrace

set_option warningAsError true
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.Source32CallerFacts
open EvmSemantics EvmSemantics.EVM Challenge.EvmProof

/-- Memory inherited at the new source constructor before its two stores. -/
def constructorBase (input : ByteArray) : ByteArray :=
  (PaddingTrace.padCopied input).memory

def constructedMemory (input : ByteArray) : ByteArray :=
  Source32Memory.source32Memory (constructorBase input)

/-- Explicitly the ordinary padding model, independent of any new entry-state name. -/
def ordinaryMemory (input : ByteArray) : ByteArray :=
  if input.size % 64 = 0 then (PaddingTrace.padSkip input).memory
  else (PaddingTrace.padReturned input).memory

/-- A memory value model; the physical branch trace is a separate obligation. -/
def initializerMemory (input : ByteArray) : ByteArray :=
  if input.size = 32 then constructedMemory input else ordinaryMemory input

private theorem base_memory_empty (input : ByteArray) :
    (PaddingTrace.padLengthReady input).memory = ByteArray.empty := rfl

theorem constructorBase_eq (input : ByteArray) :
    constructorBase input = Padding.copiedMemory ByteArray.empty input := by
  dsimp only [constructorBase, PaddingTrace.padCopied]
  rw [Memory.readPadded_zero_size, base_memory_empty]
  rfl

theorem constructorBase_low_zero (input : ByteArray) (a : Nat)
    (ha : a < Padding.messageOffset) :
    (constructorBase input)[a]?.getD 0 = 0 := by
  rw [constructorBase_eq]
  unfold Padding.copiedMemory
  rw [MachineState.writeBytes_getElem?_getD, if_neg (by omega)]
  exact Memory.getElem?_getD_eq_zero_of_size_le ByteArray.empty a (Nat.zero_le a)

theorem constructorBase_zero_tail (input : ByteArray) :
    ∀ a, 88 ≤ a → a < 92 → (constructorBase input)[a]?.getD 0 = 0 := by
  intro a _ ha
  apply constructorBase_low_zero
  unfold Padding.messageOffset
  omega

theorem constructorBase_input_byte (input : ByteArray) (i : Nat) (hi : i < input.size) :
    (constructorBase input)[Padding.messageOffset + i]?.getD 0 = input[i]?.getD 0 := by
  rw [constructorBase_eq]
  unfold Padding.copiedMemory
  rw [MachineState.writeBytes_getElem?_getD, if_pos (by omega), Nat.add_sub_cancel_left]

private theorem returned_low_zero (input : ByteArray) (hfit : Challenge.Ripemd160.CalldataFits input)
    (a : Nat) (ha : a < Padding.messageOffset) :
    (PaddingTrace.padReturned input).memory[a]?.getD 0 = 0 := by
  have hlen := Padding.input_and_footer_fit input.size
  rw [PaddingTrace.padReturned_getD_window input hfit a (by omega)]
  simp only [Padding.paddedMemory, Padding.sentinelMemory, Padding.copiedMemory,
    MachineState.writeBytes_getElem?_getD]
  rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), base_memory_empty]
  exact Memory.getElem?_getD_eq_zero_of_size_le ByteArray.empty a (Nat.zero_le a)

theorem ordinary_low_zero (input : ByteArray) (hfit : Challenge.Ripemd160.CalldataFits input)
    (a : Nat) (ha : a < Padding.messageOffset) :
    (ordinaryMemory input)[a]?.getD 0 = 0 := by
  unfold ordinaryMemory
  split
  · exact constructorBase_low_zero input a ha
  · exact returned_low_zero input hfit a ha

private theorem readWord_zero_window (memory : ByteArray) (off : Nat)
    (hz : ∀ i, i < 32 → memory[off + i]?.getD 0 = 0) :
    MachineState.readWord memory off = UInt256.ofNat 0 := by
  have hr : MachineState.readPadded memory off 32 =
      MachineState.readPadded (Source32Memory.writeWord ByteArray.empty off (UInt256.ofNat 0)) off 32 := by
    apply Memory.readPadded_congr
    intro i hi
    rw [hz i hi]
    simp only [Source32Memory.writeWord, MachineState.writeBytes_getElem?_getD,
      YulEvmCompiler.BytesLemmas.natToBytesPadded_size]
    rw [if_pos (by omega), Nat.add_sub_cancel_left,
      YulEvmCompiler.BytesLemmas.natToBytesPadded_getElem?_getD _ _ _ hi]
    simp only [Word.word_toNat_ofNat, Nat.zero_mod, Nat.zero_div]
    decide
  calc
    MachineState.readWord memory off =
        MachineState.readWord (Source32Memory.writeWord ByteArray.empty off (UInt256.ofNat 0)) off := by
      unfold MachineState.readWord
      rw [hr]
    _ = UInt256.ofNat 0 := Memory.readWord_writeWord _ _ _

theorem ordinary_read32 (input : ByteArray) (hfit : Challenge.Ripemd160.CalldataFits input) :
    MachineState.readWord (ordinaryMemory input) 32 = UInt256.ofNat 0 := by
  apply readWord_zero_window
  intro i hi
  apply ordinary_low_zero input hfit
  unfold Padding.messageOffset
  omega

theorem constructed_read32 (input : ByteArray) :
    MachineState.readWord (constructedMemory input) 32 = UInt256.ofNat 128 :=
  Source32Memory.read32 _

theorem constructed_read60 (input : ByteArray) :
    MachineState.readWord (constructedMemory input) 60 = Source32Memory.source32Word :=
  Source32Memory.read60 _ (constructorBase_zero_tail input)

theorem constructed_frame88 (input : ByteArray) (a : Nat) (ha : 88 ≤ a) :
    (constructedMemory input)[a]?.getD 0 = (constructorBase input)[a]?.getD 0 :=
  Source32Memory.frame88 _ a ha

theorem constructed_input_byte (input : ByteArray) (i : Nat) (hi : i < input.size) :
    (constructedMemory input)[Padding.messageOffset + i]?.getD 0 = input[i]?.getD 0 := by
  rw [constructed_frame88 input _ (by unfold Padding.messageOffset; omega),
    constructorBase_input_byte input i hi]

theorem afterLower_read60 (input : ByteArray) (value : UInt256) :
    MachineState.readWord (Source32Memory.writeWord (constructedMemory input) 28 value) 60 =
      Source32Memory.source32Word := by
  rw [Source32Memory.write28_read60, constructed_read60]

theorem afterLower_frame88 (input : ByteArray) (value : UInt256) (a : Nat) (ha : 88 ≤ a) :
    (Source32Memory.writeWord (constructedMemory input) 28 value)[a]?.getD 0 =
      (constructorBase input)[a]?.getD 0 := by
  rw [Source32Memory.write28_frame60 _ value a (by omega), constructed_frame88 input a ha]

theorem afterLower_input_byte (input : ByteArray) (value : UInt256)
    (i : Nat) (hi : i < input.size) :
    (Source32Memory.writeWord (constructedMemory input) 28 value)[Padding.messageOffset + i]?.getD 0 =
      input[i]?.getD 0 := by
  rw [afterLower_frame88 input value _ (by unfold Padding.messageOffset; omega),
    constructorBase_input_byte input i hi]

theorem initializer_read32 (input : ByteArray) (hfit : Challenge.Ripemd160.CalldataFits input) :
    MachineState.readWord (initializerMemory input) 32 =
      if input.size = 32 then UInt256.ofNat 128 else UInt256.ofNat 0 := by
  unfold initializerMemory
  split
  · exact constructed_read32 input
  · exact ordinary_read32 input hfit

theorem initializer_flag_iff (input : ByteArray) (hfit : Challenge.Ripemd160.CalldataFits input) :
    UInt256.isTrue (MachineState.readWord (initializerMemory input) 32) ↔ input.size = 32 := by
  rw [initializer_read32 input hfit]
  by_cases h : input.size = 32
  · rw [if_pos h]
    exact ⟨fun _ => h, fun _ => by decide⟩
  · rw [if_neg h]
    exact iff_of_false (by decide) h

theorem sizeWord_eq32_iff (input : ByteArray) (hfit : Challenge.Ripemd160.CalldataFits input) :
    UInt256.ofNat input.size = UInt256.ofNat 32 ↔ input.size = 32 := by
  constructor
  · intro h
    have hn : input.size < 2 ^ 256 := lt_trans hfit (by norm_num)
    have he := congrArg UInt256.toNat h
    rw [Word.word_toNat_ofNat, Nat.mod_eq_of_lt hn, Word.word_toNat_ofNat] at he
    simpa using he
  · intro h
    rw [h]

#print axioms constructorBase_eq
#print axioms constructorBase_low_zero
#print axioms constructorBase_zero_tail
#print axioms constructorBase_input_byte
#print axioms ordinary_low_zero
#print axioms ordinary_read32
#print axioms constructed_read32
#print axioms constructed_read60
#print axioms constructed_frame88
#print axioms constructed_input_byte
#print axioms afterLower_read60
#print axioms afterLower_frame88
#print axioms afterLower_input_byte
#print axioms initializer_read32
#print axioms initializer_flag_iff
#print axioms sizeWord_eq32_iff
end Challenge.Ripemd160.Submission.Proofs.Bytecode.Source32CallerFacts
