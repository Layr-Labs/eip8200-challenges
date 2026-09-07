import Challenge.Modexp.Submission.Proofs.Bytecode.WindowHitByteGas
import Challenge.Modexp.Submission.Proofs.Bytecode.WindowHitLoopAdvance

set_option warningAsError true

/-!
# One fixed-width word-loop iteration

This adapter is the only place that specializes the artifact-independent
four-byte certificate to the submission's concrete loop boundary states.
-/

namespace Challenge.Modexp.Submission.Proofs.Bytecode.WindowHitWordStep

open EvmSemantics
open EvmSemantics.EVM
open WindowControlDefs
open WindowHitStates

def gasSteps_fourBytes (input : ByteArray) (pointer : Nat)
    (accumulator : UInt256) :
    Challenge.EvmProof.GasSteps
      (wordState input pointer 0 3208 accumulator)
      (wordState input pointer 4 3547 accumulator) := by
  have h := WindowHitByteGas.gasSteps_fourBytes
    (Dispatch.wordEntryState input) (baseWord input) (modulusWord input)
    (MachineState.readWord input pointer) (UInt256.ofNat pointer) accumulator
    (routeStack input) (by simp [routeStack]) rfl rfl
    deployAddress_not_precompile
  have htemplate : { Dispatch.wordEntryState input with halt := .Running } =
      Dispatch.wordEntryState input := by rfl
  rw [htemplate] at h
  simpa only [wordState, WindowByteKernel.wordKernelState, byteAccumulator,
    WindowMath.chunkWordStep, tableMemory] using h

def gasSteps_word (input : ByteArray) (pointer : Nat)
    (accumulator : UInt256) (hpointer : pointer < 160) :
    Challenge.EvmProof.GasSteps
      (wordState input pointer 0 3208 accumulator)
      (loopState input (pointer + 4)
        (WindowMath.chunkWordStep (modulusWord input) (baseWord input)
          accumulator (MachineState.readWord input pointer))) :=
  (gasSteps_fourBytes input pointer accumulator).trans
    (WindowHitLoopAdvance.gasSteps_loopAdvance input pointer accumulator hpointer)

end Challenge.Modexp.Submission.Proofs.Bytecode.WindowHitWordStep
