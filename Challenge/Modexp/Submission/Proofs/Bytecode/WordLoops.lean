import Challenge.Modexp.Submission.Proofs.Bytecode.WordBitSel
import Challenge.Modexp.Submission.Proofs.Bytecode.Unroll0
import Challenge.Modexp.Submission.Proofs.Bytecode.Unroll1
import Challenge.Modexp.Submission.Proofs.Bytecode.Unroll2
import Challenge.Modexp.Submission.Proofs.Bytecode.Unroll3
import Challenge.Modexp.Submission.Proofs.Bytecode.Unroll4
import Challenge.Modexp.Submission.Proofs.Bytecode.Unroll5
import Challenge.Modexp.Submission.Proofs.Bytecode.Unroll6
import Challenge.Modexp.Submission.Proofs.Bytecode.Unroll7
set_option warningAsError true
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000
/-!
# One-word MODEXP loop composition

This module closes the two nested exponent loops and composes their exact
`GasSteps` certificates from the small execution segments proved in `Word`.
Keeping this composition separate also lets later correctness and gas-cost
proofs reuse the cached straight-line certificates.
-/

namespace Challenge.Modexp.Submission.Proofs.Bytecode.WordLoops

open EvmSemantics
open EvmSemantics.EVM
open Word

attribute [local simp] Challenge.EvmProof.Word.ofNat_add_mod
  Challenge.EvmProof.Word.succ_ofNat_mod

def gasSteps_expEnter (input : ByteArray) (i : Nat) (acc base : UInt256)
    (hvalid : ValidInput input) (hi : i < exponentSize input) :
    Challenge.EvmProof.GasSteps (expLoopState input i acc base)
      (bitLoopState input i 0 (byteWord input (expOffset input + i))
        (UInt256.ofNat (expOffset input + i)) acc base) :=
  (Challenge.EvmProof.Stepper.runLocatedBlock_sound
      Artifact.submissionArtifact .Osaka expGuardPath rfl rfl
        (run_expGuard input i acc base hvalid hi) rfl
        deployAddress_not_precompile).trans
    (Challenge.EvmProof.Stepper.runLocatedBlock_sound
      Artifact.submissionArtifact .Osaka expLoadPath rfl rfl
        (run_expLoad input i acc base hvalid hi) rfl
        deployAddress_not_precompile)

def gasSteps_bitCopy0 (input : ByteArray) (outer : Nat)
    (byte offset acc base : UInt256) :
    Challenge.EvmProof.GasSteps
      (bitUnrollState input outer 0 byte offset acc base)
      (bitUnrollState input outer 1 byte offset
        (bitStepSel input byte 0 acc base) base) :=
  Unroll0.gasSteps_bitCopy0_sym
    (bitLoopState input outer 0 byte offset acc base) (bitTail input)
    (base - UInt256.ofNat 1) (UInt256.ofNat 0) byte offset (UInt256.ofNat outer)
    acc base (UInt256.ofNat (modulusValue input))
    (bitFrame input outer byte offset acc base) (by simp [bitTail, callerRest])

def gasSteps_bitCopy1 (input : ByteArray) (outer : Nat)
    (byte offset acc base : UInt256) :
    Challenge.EvmProof.GasSteps
      (bitUnrollState input outer 1 byte offset acc base)
      (bitUnrollState input outer 2 byte offset
        (bitStepSel input byte 1 acc base) base) :=
  Unroll1.gasSteps_bitCopy1_sym
    (bitLoopState input outer 0 byte offset acc base) (bitTail input)
    (base - UInt256.ofNat 1) (UInt256.ofNat 0) byte offset (UInt256.ofNat outer)
    acc base (UInt256.ofNat (modulusValue input))
    (bitFrame input outer byte offset acc base) (by simp [bitTail, callerRest])

def gasSteps_bitCopy2 (input : ByteArray) (outer : Nat)
    (byte offset acc base : UInt256) :
    Challenge.EvmProof.GasSteps
      (bitUnrollState input outer 2 byte offset acc base)
      (bitUnrollState input outer 3 byte offset
        (bitStepSel input byte 2 acc base) base) :=
  Unroll2.gasSteps_bitCopy2_sym
    (bitLoopState input outer 0 byte offset acc base) (bitTail input)
    (base - UInt256.ofNat 1) (UInt256.ofNat 0) byte offset (UInt256.ofNat outer)
    acc base (UInt256.ofNat (modulusValue input))
    (bitFrame input outer byte offset acc base) (by simp [bitTail, callerRest])

def gasSteps_bitCopy3 (input : ByteArray) (outer : Nat)
    (byte offset acc base : UInt256) :
    Challenge.EvmProof.GasSteps
      (bitUnrollState input outer 3 byte offset acc base)
      (bitUnrollState input outer 4 byte offset
        (bitStepSel input byte 3 acc base) base) :=
  Unroll3.gasSteps_bitCopy3_sym
    (bitLoopState input outer 0 byte offset acc base) (bitTail input)
    (base - UInt256.ofNat 1) (UInt256.ofNat 0) byte offset (UInt256.ofNat outer)
    acc base (UInt256.ofNat (modulusValue input))
    (bitFrame input outer byte offset acc base) (by simp [bitTail, callerRest])

def gasSteps_bitCopy4 (input : ByteArray) (outer : Nat)
    (byte offset acc base : UInt256) :
    Challenge.EvmProof.GasSteps
      (bitUnrollState input outer 4 byte offset acc base)
      (bitUnrollState input outer 5 byte offset
        (bitStepSel input byte 4 acc base) base) :=
  Unroll4.gasSteps_bitCopy4_sym
    (bitLoopState input outer 0 byte offset acc base) (bitTail input)
    (base - UInt256.ofNat 1) (UInt256.ofNat 0) byte offset (UInt256.ofNat outer)
    acc base (UInt256.ofNat (modulusValue input))
    (bitFrame input outer byte offset acc base) (by simp [bitTail, callerRest])

def gasSteps_bitCopy5 (input : ByteArray) (outer : Nat)
    (byte offset acc base : UInt256) :
    Challenge.EvmProof.GasSteps
      (bitUnrollState input outer 5 byte offset acc base)
      (bitUnrollState input outer 6 byte offset
        (bitStepSel input byte 5 acc base) base) :=
  Unroll5.gasSteps_bitCopy5_sym
    (bitLoopState input outer 0 byte offset acc base) (bitTail input)
    (base - UInt256.ofNat 1) (UInt256.ofNat 0) byte offset (UInt256.ofNat outer)
    acc base (UInt256.ofNat (modulusValue input))
    (bitFrame input outer byte offset acc base) (by simp [bitTail, callerRest])

def gasSteps_bitCopy6 (input : ByteArray) (outer : Nat)
    (byte offset acc base : UInt256) :
    Challenge.EvmProof.GasSteps
      (bitUnrollState input outer 6 byte offset acc base)
      (bitUnrollState input outer 7 byte offset
        (bitStepSel input byte 6 acc base) base) :=
  Unroll6.gasSteps_bitCopy6_sym
    (bitLoopState input outer 0 byte offset acc base) (bitTail input)
    (base - UInt256.ofNat 1) (UInt256.ofNat 0) byte offset (UInt256.ofNat outer)
    acc base (UInt256.ofNat (modulusValue input))
    (bitFrame input outer byte offset acc base) (by simp [bitTail, callerRest])

def gasSteps_bitCopy7 (input : ByteArray) (outer : Nat)
    (byte offset acc base : UInt256) :
    Challenge.EvmProof.GasSteps
      (bitUnrollState input outer 7 byte offset acc base)
      (bitUnrollState input outer 8 byte offset
        (bitStepSel input byte 7 acc base) base) :=
  Unroll7.gasSteps_bitCopy7_sym
    (bitLoopState input outer 0 byte offset acc base) (bitTail input)
    (base - UInt256.ofNat 1) (UInt256.ofNat 0) byte offset (UInt256.ofNat outer)
    acc base (UInt256.ofNat (modulusValue input))
    (bitFrame input outer byte offset acc base) (by simp [bitTail, callerRest])

def bitAfter (input : ByteArray) (byte : UInt256) (base : UInt256) :
    Nat → UInt256 → UInt256
  | 0, acc => acc
  | j + 1, acc => bitStepSel input byte j (bitAfter input byte base j acc) base

def gasSteps_bitLoop (input : ByteArray) (outer : Nat)
    (byte offset acc base : UInt256) :
    Challenge.EvmProof.GasSteps
      (bitLoopState input outer 0 byte offset acc base)
      (bitUnrollState input outer 8 byte offset
        (bitAfter input byte base 8 acc) base) :=
  (gasSteps_bitEntry input outer byte offset acc base).trans <|
  (gasSteps_bitHead input outer byte offset acc base).trans <|
  (gasSteps_bitCopy0 input outer byte offset
    (bitAfter input byte base 0 acc) base).trans <|
  (gasSteps_bitCopy1 input outer byte offset
    (bitAfter input byte base 1 acc) base).trans <|
  (gasSteps_bitCopy2 input outer byte offset
    (bitAfter input byte base 2 acc) base).trans <|
  (gasSteps_bitCopy3 input outer byte offset
    (bitAfter input byte base 3 acc) base).trans <|
  (gasSteps_bitCopy4 input outer byte offset
    (bitAfter input byte base 4 acc) base).trans <|
  (gasSteps_bitCopy5 input outer byte offset
    (bitAfter input byte base 5 acc) base).trans <|
  (gasSteps_bitCopy6 input outer byte offset
    (bitAfter input byte base 6 acc) base).trans <|
  gasSteps_bitCopy7 input outer byte offset
    (bitAfter input byte base 7 acc) base

def gasSteps_bitFinish (input : ByteArray) (outer : Nat)
    (byte offset acc base : UInt256) (hvalid : ValidInput input)
    (houter : outer < exponentSize input) :
    Challenge.EvmProof.GasSteps
      (bitUnrollState input outer 8 byte offset acc base)
      (expLoopState input (outer + 1) acc base) :=
  (gasSteps_bitExit input outer byte offset acc base).trans
    (Challenge.EvmProof.Stepper.runLocatedBlock_sound
      Artifact.submissionArtifact .Osaka bitFinishTailPath rfl rfl
        (run_bitFinishTail input outer byte offset acc base hvalid houter) rfl
        deployAddress_not_precompile)

def expStep (input : ByteArray) (i : Nat) (acc base : UInt256) : UInt256 :=
  bitAfter input (byteWord input (expOffset input + i)) base 8 acc

def expAfter (input : ByteArray) (base : UInt256) : Nat → UInt256 → UInt256
  | 0, acc => acc
  | i + 1, acc => expStep input i (expAfter input base i acc) base

def gasSteps_expIteration (input : ByteArray) (i : Nat) (acc base : UInt256)
    (hvalid : ValidInput input) (hi : i < exponentSize input) :
    Challenge.EvmProof.GasSteps (expLoopState input i acc base)
      (expLoopState input (i + 1) (expStep input i acc base) base) := by
  let byte := byteWord input (expOffset input + i)
  let offset := UInt256.ofNat (expOffset input + i)
  exact (gasSteps_expEnter input i acc base hvalid hi).trans <|
    (gasSteps_bitLoop input i byte offset acc base).trans
      (gasSteps_bitFinish input i byte offset (bitAfter input byte base 8 acc)
        base hvalid hi)

def gasSteps_expLoop (input : ByteArray) (acc base : UInt256)
    (hvalid : ValidInput input) :
    Challenge.EvmProof.GasSteps (expLoopState input 0 acc base)
      (expLoopState input (exponentSize input)
        (expAfter input base (exponentSize input) acc) base) := by
  exact Challenge.EvmProof.GasSteps.iterateBounded (I := fun i =>
      expLoopState input i (expAfter input base i acc) base) (exponentSize input)
    (fun i hi => gasSteps_expIteration input i
      (expAfter input base i acc) base hvalid hi)

end Challenge.Modexp.Submission.Proofs.Bytecode.WordLoops
