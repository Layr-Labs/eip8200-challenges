import Challenge.Modexp.Submission.Proofs.Bytecode.WindowHitByteCorrect

set_option warningAsError true

/-!
# Fixed-width byte execution certificates

This module converts the four opaque concrete byte executions into composable
`GasSteps` contracts over the artifact-independent word-kernel state.  A later
adapter can instantiate the template with the concrete loop state without
unfolding any byte slice.
-/

namespace Challenge.Modexp.Submission.Proofs.Bytecode.WindowHitByteGas

open EvmSemantics
open EvmSemantics.EVM
open WindowByteKernel
open WindowHitByteSlices

private def sound {s t : State}
    (path : List (Challenge.EvmProof.Stepper.Located
      Artifact.submissionArtifact .Osaka))
    (h : Challenge.EvmProof.Stepper.runLocatedBlock path s = some t)
    (hrun : s.halt = .Running)
    (hcode : s.executionEnv.code = Artifact.submissionArtifact.code)
    (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    Challenge.EvmProof.GasSteps s t :=
  Challenge.EvmProof.Stepper.runLocatedBlock_sound
    Artifact.submissionArtifact .Osaka path hcode hfork h hrun hnp

def gasSteps_byte0 (template : State) (base modulus word pointer accumulator : UInt256)
    (rest : List UInt256) (hrest : rest.length ≤ 1000)
    (hcode : template.executionEnv.code = Artifact.submissionArtifact.code)
    (hfork : template.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig template.executionEnv.precompileConfig
      template.executionEnv.fork template.executionEnv.codeAddr = false) :
    Challenge.EvmProof.GasSteps
      (wordKernelState { template with halt := .Running } (UInt256.ofNat 3208)
        base modulus word pointer accumulator rest)
      (wordKernelState { template with halt := .Running } (UInt256.ofNat 3292)
        base modulus word pointer
        (WindowMath.byteWordStep modulus base accumulator
          (byteValue 0 word).toNat) rest) :=
  sound (segmentedBytePath 0)
    (WindowHitByteCorrect.run_byte0 template base modulus word pointer accumulator
      rest hrest) rfl hcode hfork hnp

def gasSteps_byte1 (template : State) (base modulus word pointer accumulator : UInt256)
    (rest : List UInt256) (hrest : rest.length ≤ 1000)
    (hcode : template.executionEnv.code = Artifact.submissionArtifact.code)
    (hfork : template.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig template.executionEnv.precompileConfig
      template.executionEnv.fork template.executionEnv.codeAddr = false) :
    Challenge.EvmProof.GasSteps
      (wordKernelState { template with halt := .Running } (UInt256.ofNat 3292)
        base modulus word pointer accumulator rest)
      (wordKernelState { template with halt := .Running } (UInt256.ofNat 3377)
        base modulus word pointer
        (WindowMath.byteWordStep modulus base accumulator
          (byteValue 1 word).toNat) rest) :=
  sound (segmentedBytePath 1)
    (WindowHitByteCorrect.run_byte1 template base modulus word pointer accumulator
      rest hrest) rfl hcode hfork hnp

def gasSteps_byte2 (template : State) (base modulus word pointer accumulator : UInt256)
    (rest : List UInt256) (hrest : rest.length ≤ 1000)
    (hcode : template.executionEnv.code = Artifact.submissionArtifact.code)
    (hfork : template.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig template.executionEnv.precompileConfig
      template.executionEnv.fork template.executionEnv.codeAddr = false) :
    Challenge.EvmProof.GasSteps
      (wordKernelState { template with halt := .Running } (UInt256.ofNat 3377)
        base modulus word pointer accumulator rest)
      (wordKernelState { template with halt := .Running } (UInt256.ofNat 3462)
        base modulus word pointer
        (WindowMath.byteWordStep modulus base accumulator
          (byteValue 2 word).toNat) rest) :=
  sound (segmentedBytePath 2)
    (WindowHitByteCorrect.run_byte2 template base modulus word pointer accumulator
      rest hrest) rfl hcode hfork hnp

def gasSteps_byte3 (template : State) (base modulus word pointer accumulator : UInt256)
    (rest : List UInt256) (hrest : rest.length ≤ 1000)
    (hcode : template.executionEnv.code = Artifact.submissionArtifact.code)
    (hfork : template.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig template.executionEnv.precompileConfig
      template.executionEnv.fork template.executionEnv.codeAddr = false) :
    Challenge.EvmProof.GasSteps
      (wordKernelState { template with halt := .Running } (UInt256.ofNat 3462)
        base modulus word pointer accumulator rest)
      (wordKernelState { template with halt := .Running } (UInt256.ofNat 3547)
        base modulus word pointer
        (WindowMath.byteWordStep modulus base accumulator
          (byteValue 3 word).toNat) rest) :=
  sound (segmentedBytePath 3)
    (WindowHitByteCorrect.run_byte3 template base modulus word pointer accumulator
      rest hrest) rfl hcode hfork hnp

def gasSteps_fourBytes (template : State)
    (base modulus word pointer accumulator : UInt256)
    (rest : List UInt256) (hrest : rest.length ≤ 1000)
    (hcode : template.executionEnv.code = Artifact.submissionArtifact.code)
    (hfork : template.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig template.executionEnv.precompileConfig
      template.executionEnv.fork template.executionEnv.codeAddr = false) :
    Challenge.EvmProof.GasSteps
      (wordKernelState { template with halt := .Running } (UInt256.ofNat 3208)
        base modulus word pointer accumulator rest)
      (wordKernelState { template with halt := .Running } (UInt256.ofNat 3547)
        base modulus word pointer
        (WindowMath.chunkWordStep modulus base accumulator word) rest) := by
  let a1 := WindowMath.byteWordStep modulus base accumulator
    (byteValue 0 word).toNat
  let a2 := WindowMath.byteWordStep modulus base a1
    (byteValue 1 word).toNat
  let a3 := WindowMath.byteWordStep modulus base a2
    (byteValue 2 word).toNat
  let a4 := WindowMath.byteWordStep modulus base a3
    (byteValue 3 word).toNat
  have h0 := gasSteps_byte0 template base modulus word pointer accumulator rest
    hrest hcode hfork hnp
  have h1 := gasSteps_byte1 template base modulus word pointer a1 rest
    hrest hcode hfork hnp
  have h2 := gasSteps_byte2 template base modulus word pointer a2 rest
    hrest hcode hfork hnp
  have h3 := gasSteps_byte3 template base modulus word pointer a3 rest
    hrest hcode hfork hnp
  have hall := ((h0.trans h1).trans h2).trans h3
  simpa [a1, a2, a3, a4, WindowMath.chunkWordStep, byteValue] using hall

end Challenge.Modexp.Submission.Proofs.Bytecode.WindowHitByteGas
