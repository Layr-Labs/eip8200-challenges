import Challenge.Modexp.Submission.Proofs.Bytecode.WindowHitStates
import Challenge.Modexp.Submission.Proofs.Bytecode.WindowSpec

set_option warningAsError true

/-!
# Fixed-width hit result bridge

The execution trace returns a single table-sized word.  These lemmas identify
that memory slice with the MODEXP specification independently of the concrete
return-tail instructions.
-/

namespace Challenge.Modexp.Submission.Proofs.Bytecode.WindowHitResult

open EvmSemantics
open EvmSemantics.EVM
open WindowHitStates

theorem completedWord_toNat (input : ByteArray)
    (hmodulus : 0 < WindowSpec.modulusValue input) :
    (WindowMath.afterChunksWord input 128 (modulusWord input)
      (baseWord input) 8 (UInt256.ofNat 1)).toNat =
        WindowSpec.windowResult input := by
  rw [WindowMath.afterChunksWord_toNat input 128 (modulusWord input)
    (baseWord input) (UInt256.ofNat 1) 8 (by
      simpa only [modulusWord, Challenge.EvmProof.Bytes.readWord_toNat,
        WindowSpec.modulusValue] using hmodulus)]
  simp only [modulusWord, baseWord, Challenge.EvmProof.Bytes.readWord_toNat]
  change WindowMath.afterBytes input 128 (WindowSpec.modulusValue input)
    (WindowSpec.baseValue input) 32 1 = WindowSpec.windowResult input
  exact WindowMath.afterBytes_literal_one input 128
    (WindowSpec.modulusValue input) (WindowSpec.baseValue input) 31

theorem returnedState_result (input : ByteArray)
    (hmatch : WindowGuardLogic.Matches input)
    (hmodulus : 0 < WindowSpec.modulusValue input)
    (word : UInt256)
    (hword : word.toNat = WindowSpec.windowResult input) :
    (returnedState input word).toResult = .returned (spec input) := by
  rw [WindowSpec.spec_eq input hmatch hmodulus]
  change ExecutionResult.returned
      (MachineState.readPadded (normalOutputMemory input word) 0 32) =
    ExecutionResult.returned
      (Precompile.natToBytes (WindowSpec.windowResult input) 32)
  rw [show MachineState.readPadded (normalOutputMemory input word) 0 32 =
      Data.Bytes.natToBytesPadded word.toNat 32 by
    exact WindowTableMemory.readPadded_storeWord _ _ _]
  simp [hword, Precompile.natToBytes]

theorem zeroReturnedState_result (input : ByteArray)
    (hmatch : WindowGuardLogic.Matches input)
    (hmodulus : WindowSpec.modulusValue input = 0) :
    (zeroReturnedState input).toResult = .returned (spec input) := by
  rcases hmatch with ⟨hb, he, hm⟩
  have hzero : Precompile.bytesToNatPadded input 160 32 = 0 := hmodulus
  have hspec : spec input = Precompile.natToBytes 0 32 := by
    unfold spec
    rw [hb, he, hm]
    simp [hzero, Precompile.modPow]
  rw [hspec]
  change ExecutionResult.returned
      (MachineState.readPadded (outputMemory 0) 0 32) =
    ExecutionResult.returned (Precompile.natToBytes 0 32)
  rw [show MachineState.readPadded (outputMemory 0) 0 32 =
      Data.Bytes.natToBytesPadded (0 : UInt256).toNat 32 by
    exact WindowTableMemory.readPadded_storeWord _ _ _]
  simp only [Precompile.natToBytes]
  rfl

end Challenge.Modexp.Submission.Proofs.Bytecode.WindowHitResult
