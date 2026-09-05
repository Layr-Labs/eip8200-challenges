import Challenge.Ripemd160.Submission.Proofs.Bytecode.KnownInputData
import Challenge.EvmProof.Bytes
import Challenge.EvmProof.Memory
import Challenge.EvmProof.Word

set_option warningAsError true
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.PatternedInputData

open EvmSemantics
open EvmSemantics.EVM

/-- Byte `i` of the public 1000-byte patterned scorer vector. -/
def expectedByte (i : Nat) : UInt8 :=
  UInt8.ofNat ((i * 37 + i / 251 * 11 + 7) % 256)

/-- The public scoring input `Scorer.patterned 1000`. -/
def patternedInput : ByteArray :=
  ByteArray.ofFn fun i : Fin 1000 => expectedByte i.val

@[simp] theorem patternedInput_size : patternedInput.size = 1000 := by
  simp [patternedInput, ByteArray.size]

@[simp] theorem patternedInput_getElem (i : Nat) (hi : i < patternedInput.size) :
    patternedInput[i] = expectedByte i := by
  have hi' : i < 1000 := by
    simpa [patternedInput_size] using hi
  simp [patternedInput, ByteArray.getElem_eq_getElem_data, expectedByte] at hi ⊢
  have hfin : (⟨i, hi'⟩ : Fin 1000).val = i := rfl
  simpa [hfin] using Array.getElem_ofFn
    (fun j : Fin 1000 => UInt8.ofNat ((j.val * 37 + j.val / 251 * 11 + 7) % 256))
    i hi'

theorem expectedByte_lt (i : Nat) : (expectedByte i).toNat < 256 :=
  UInt8.toNat_lt _

theorem expectedByte_zero : expectedByte 0 = 7 := by decide

/-- High byte of the first word is `7`, not ASCII `a`. -/
theorem patterned_reference_ne :
    MachineState.readWord patternedInput 0 ≠ KnownInputData.fullWord := by
  intro h
  have hshift := Challenge.EvmProof.Bytes.shiftRight_readWord
    patternedInput 0 1 (by omega) (by omega)
  have hpat : UInt256.shiftRight (MachineState.readWord patternedInput 0)
      (UInt256.ofNat 248) = UInt256.ofNat 7 := by
    have hbyte :
        EVM.Precompile.bytesToNatPadded patternedInput 0 1 = 7 := by
      unfold EVM.Precompile.bytesToNatPadded
      have h0 : 0 < patternedInput.size := by
        rw [patternedInput_size]; omega
      simp [MachineState.readPadded, patternedInput_getElem 0 (by
        rw [patternedInput_size]; omega), expectedByte_zero,
        Data.Bytes.bytesToBigEndianNat, Challenge.EvmProof.Bytecode.toList_eq_data]
      decide
    rw [hshift, hbyte]
  have hfull : UInt256.shiftRight KnownInputData.fullWord (UInt256.ofNat 248) =
      UInt256.ofNat 0x61 := by decide
  have hne : UInt256.ofNat 7 ≠ UInt256.ofNat 0x61 := by decide
  exact hne (by rw [← hpat, h, hfull])

theorem patterned_ne_target : patternedInput ≠ KnownInputData.targetInput := by
  intro h
  have href : MachineState.readWord patternedInput 0 = KnownInputData.fullWord := by
    rw [h]
    simpa [KnownInputData.expectedWord] using
      KnownInputData.targetInput_readWord 0 (by decide)
  exact patterned_reference_ne href

end Challenge.Ripemd160.Submission.Proofs.Bytecode.PatternedInputData
