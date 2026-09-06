import Challenge.Modexp.Submission.Proofs.Bytecode.WindowHitStates
import Challenge.Modexp.Submission.Proofs.Bytecode.WindowByteKernel

set_option warningAsError true

/-!
# Fixed-width loop byte model

This module connects the reusable artifact-independent byte kernel to the
four concrete semantic loop boundaries.  The remaining artifact obligation
is deliberately separate: each 80-instruction slice must be identified with
`byteProgram count` at its generated instruction indices.
-/

namespace Challenge.Modexp.Submission.Proofs.Bytecode.WindowHitByteModel

open EvmSemantics
open EvmSemantics.EVM
open WindowControlDefs
open WindowHitStates
open WindowNibbleKernel
open WindowByteKernel

theorem wordState_eq_kernel (input : ByteArray) (pointer count pc : Nat)
    (accumulator : UInt256) :
    wordState input pointer count pc accumulator =
      wordKernelState (Dispatch.wordEntryState input) (UInt256.ofNat pc)
        (baseWord input) (modulusWord input)
        (MachineState.readWord input pointer) (UInt256.ofNat pointer)
        (byteAccumulator input pointer count accumulator) (routeStack input) := by
  rfl

theorem run_wordByte_model (input : ByteArray) (pointer count startPC endPC : Nat)
    (accumulator : UInt256) (hcount : count < 4)
    (hpc : advancePC (byteAdvance count) (UInt256.ofNat startPC) =
      UInt256.ofNat endPC) :
    runInstructions (byteProgram count)
      (wordState input pointer count startPC accumulator) =
    some (wordState input pointer (count + 1) endPC accumulator) := by
  rw [wordState_eq_kernel]
  rw [run_byte (hindex := hcount) (hrest := by simp [routeStack])]
  rw [hpc]
  rw [wordState_eq_kernel]
  rfl

theorem run_byte0_model (input : ByteArray) (pointer : Nat)
    (accumulator : UInt256) :
    runInstructions (byteProgram 0)
      (wordState input pointer 0 3208 accumulator) =
    some (wordState input pointer 1 3292 accumulator) :=
  run_wordByte_model input pointer 0 3208 3292 accumulator (by decide) (by decide)

theorem run_byte1_model (input : ByteArray) (pointer : Nat)
    (accumulator : UInt256) :
    runInstructions (byteProgram 1)
      (wordState input pointer 1 3292 accumulator) =
    some (wordState input pointer 2 3377 accumulator) :=
  run_wordByte_model input pointer 1 3292 3377 accumulator (by decide) (by decide)

theorem run_byte2_model (input : ByteArray) (pointer : Nat)
    (accumulator : UInt256) :
    runInstructions (byteProgram 2)
      (wordState input pointer 2 3377 accumulator) =
    some (wordState input pointer 3 3462 accumulator) :=
  run_wordByte_model input pointer 2 3377 3462 accumulator (by decide) (by decide)

theorem run_byte3_model (input : ByteArray) (pointer : Nat)
    (accumulator : UInt256) :
    runInstructions (byteProgram 3)
      (wordState input pointer 3 3462 accumulator) =
    some (wordState input pointer 4 3547 accumulator) :=
  run_wordByte_model input pointer 3 3462 3547 accumulator (by decide) (by decide)

end Challenge.Modexp.Submission.Proofs.Bytecode.WindowHitByteModel
