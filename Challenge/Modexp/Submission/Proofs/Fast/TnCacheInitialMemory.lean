import Challenge.Modexp.Submission.Proofs.Fast.TnCacheMemory
import Challenge.Modexp.Submission.Proofs.Fast.Monpro

set_option warningAsError true
set_option linter.unusedSimpArgs false

namespace Challenge.Modexp.Submission.Proofs.Fast.TnCacheInitialMemory
open EvmSemantics EvmSemantics.EVM
open Challenge.Modexp.Submission.Proofs.Fast Monpro TnCacheMemory

/-- The initial memory already contains the zero value of the cached word. -/
theorem lift_zeroed (s : State) (mem : ByteArray) (n : Nat) :
    lift (mpZeroed s mem n) (UInt256.ofNat 0) = mpZeroed s mem n := by
  have hz : (UInt256.ofNat 0).toNat = 0 := by decide
  apply ByteArray.ext_getElem
  · simp only [lift, mpZeroed, MachineState.writeBytes_size,
      Challenge.EvmProof.Memory.readPadded_size, hz,
      YulEvmCompiler.BytesLemmas.natToBytesPadded_size]
    split_ifs <;> omega
  · intro i hi hj
    rw [← Challenge.EvmProof.Memory.getD0_eq_getElem _ _ hi,
      ← Challenge.EvmProof.Memory.getD0_eq_getElem _ _ hj]
    simp only [lift, MachineState.writeBytes_getElem?_getD, hz,
      YulEvmCompiler.BytesLemmas.natToBytesPadded_size]
    split
    · next h =>
      rw [natToBytesPadded_zero_byte 32 (i-2080) (by omega)]
      simp only [mpZeroed, MachineState.writeBytes_getElem?_getD,
        Challenge.EvmProof.Memory.readPadded_size]
      rw [if_pos (by omega), Challenge.EvmProof.Memory.readPadded_getElem?_getD,
        if_pos (by omega), Challenge.EvmProof.Memory.getElem?_getD_eq_zero_of_size_le _ _ (by omega)]
    · rfl

#print axioms lift_zeroed
end Challenge.Modexp.Submission.Proofs.Fast.TnCacheInitialMemory
