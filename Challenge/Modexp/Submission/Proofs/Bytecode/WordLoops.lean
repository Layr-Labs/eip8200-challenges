import Challenge.Modexp.Submission.Proofs.Bytecode.WordLoopFinish
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

def gasSteps_bitIteration (input : ByteArray) (outer j : Nat)
    (byte offset acc base : UInt256) (hj : j < 8) :
    Challenge.EvmProof.GasSteps
      (bitLoopState input outer j byte offset acc base)
      (bitLoopState input outer (j + 1) byte offset
        (bitStep input byte j acc base) base) :=
  (Challenge.EvmProof.Stepper.runLocatedBlock_sound
      Artifact.submissionArtifact .Osaka bitGuardPath rfl rfl
        (run_bitGuard input outer j byte offset acc base hj) rfl
        deployAddress_not_precompile).trans <|
    (Challenge.EvmProof.Stepper.runLocatedBlock_sound
      Artifact.submissionArtifact .Osaka bitDecodePath rfl rfl
        (run_bitDecode input outer j byte offset acc base hj) rfl
        deployAddress_not_precompile).trans <|
    (Challenge.EvmProof.Stepper.runLocatedBlock_sound
      Artifact.submissionArtifact .Osaka bitSquarePath rfl rfl
        (run_bitSquare input outer j byte offset acc base) rfl
        deployAddress_not_precompile).trans <|
    (Challenge.EvmProof.Stepper.runLocatedBlock_sound
      Artifact.submissionArtifact .Osaka bitMaskPath rfl rfl
        (run_bitMask input outer j byte offset acc base) rfl
        deployAddress_not_precompile).trans <|
    (Challenge.EvmProof.Stepper.runLocatedBlock_sound
      Artifact.submissionArtifact .Osaka bitProductPath rfl rfl
        (run_bitProduct input outer j byte offset acc base) rfl
        deployAddress_not_precompile).trans <|
    (Challenge.EvmProof.Stepper.runLocatedBlock_sound
      Artifact.submissionArtifact .Osaka bitChoosePath rfl rfl
        (run_bitChoose input outer j byte offset acc base) rfl
        deployAddress_not_precompile).trans <|
    Challenge.EvmProof.Stepper.runLocatedBlock_sound
      Artifact.submissionArtifact .Osaka bitAdvancePath rfl rfl
        (run_bitAdvance input outer j byte offset acc base hj) rfl
        deployAddress_not_precompile

def bitAfter (input : ByteArray) (byte : UInt256) (base : UInt256) :
    Nat → UInt256 → UInt256
  | 0, acc => acc
  | j + 1, acc => bitStep input byte j (bitAfter input byte base j acc) base

def gasSteps_bitLoop (input : ByteArray) (outer : Nat)
    (byte offset acc base : UInt256) :
    Challenge.EvmProof.GasSteps
      (bitLoopState input outer 0 byte offset acc base)
      (bitLoopState input outer 8 byte offset (bitAfter input byte base 8 acc) base) := by
  exact Challenge.EvmProof.GasSteps.iterateBounded (I := fun j =>
      bitLoopState input outer j byte offset (bitAfter input byte base j acc) base) 8
    (fun j hj => gasSteps_bitIteration input outer j byte offset
      (bitAfter input byte base j acc) base hj)

def gasSteps_bitFinish (input : ByteArray) (outer : Nat)
    (byte offset acc base : UInt256) (hvalid : ValidInput input)
    (houter : outer < exponentSize input) :
    Challenge.EvmProof.GasSteps
      (bitLoopState input outer 8 byte offset acc base)
      (expLoopState input (outer + 1) acc base) :=
  (Challenge.EvmProof.Stepper.runLocatedBlock_sound
      Artifact.submissionArtifact .Osaka bitGuardPath rfl rfl
        (run_bitFinishGuard input outer byte offset acc base) rfl
        deployAddress_not_precompile).trans
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
