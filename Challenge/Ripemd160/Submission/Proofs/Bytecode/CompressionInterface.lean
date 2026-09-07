import Challenge.Ripemd160.Submission.Proofs.Bytecode.DriverTrace
import Challenge.Ripemd160.Submission.Proofs.Bytecode.HashSpecBridge
import Challenge.Ripemd160.Submission.Proofs.Bytecode.OutputModel

set_option warningAsError true
set_option maxRecDepth 30000
set_option maxHeartbeats 5000000
set_option linter.unusedSimpArgs false

/-!
# Compression-only interface

This module keeps the block-driver contract independent of the output
implementation.  It contains the exact seam fields used by the compression
proof and the driver composition that reaches the output entry.
-/

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.DirectCorrect

open Challenge.Ripemd160
open Challenge.EvmProof
open EvmSemantics
open EvmSemantics.EVM

structure CompressionSeam (input : ByteArray) where
  states : Nat → State
  initial : DriverTrace.setupEntry (states 0) input = PaddingTrace.padReturned input
  code : ∀ i, i ≤ DriverTrace.blockCount input →
    (states i).executionEnv.code = submissionBytecode
  fork : ∀ i, i ≤ DriverTrace.blockCount input →
    (states i).fork = .Osaka
  running : ∀ i, i ≤ DriverTrace.blockCount input →
    (states i).halt = .Running
  noPrecompile : ∀ i, i ≤ DriverTrace.blockCount input →
    Precompile.isPrecompileWithConfig (states i).executionEnv.precompileConfig
      (states i).executionEnv.fork (states i).executionEnv.codeAddr = false
  callStack : ∀ i, i ≤ DriverTrace.blockCount input →
    (states i).callStack = []
  compress : ∀ i, i < DriverTrace.blockCount input →
    GasSteps (DriverTrace.dispatchEntry (states i) input i)
      (DriverTrace.compressReturned (states (i + 1)) input i)
  finalWords : ∀ i : Fin 5,
    OutputTrace.hWord (states (DriverTrace.blockCount input)) i =
      Challenge.EvmProof.Word.ofUInt32
      (SpecBridge.absorbBlocks EvmSemantics.Crypto.Ripemd160.H0
          (Padding.paddedMessage input) 0
          (DriverTrace.blockCount input))[i]!

noncomputable def gasSteps_driver (input : ByteArray)
    (hfit : CalldataFits input) (seam : CompressionSeam input) :
    GasSteps (PaddingTrace.padReturned input)
      (DriverTrace.afterExit (seam.states (DriverTrace.blockCount input)) input) := by
  have gloop := DriverTrace.gasSteps_loop_of_compress seam.states input hfit
    seam.code seam.fork seam.running seam.noPrecompile seam.compress
  have hstart : DriverTrace.loopAt (seam.states 0) input 0 =
      PaddingTrace.padReturned input := by
    rw [← seam.initial]
    rfl
  exact GasSteps.cast gloop hstart rfl

end Challenge.Ripemd160.Submission.Proofs.Bytecode.DirectCorrect
