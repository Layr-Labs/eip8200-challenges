import Challenge.Ripemd160.Submission.Proofs.Bytecode.PackedDriverEntry
import Challenge.Ripemd160.Submission.Proofs.Bytecode.PackedDriverBounds
import Challenge.Ripemd160.Submission.Proofs.Bytecode.PackedCompressionBodyTrace

set_option warningAsError true
set_option autoImplicit false

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.PackedDriverBody

open Challenge.Ripemd160 Challenge.EvmProof
open EvmSemantics EvmSemantics.EVM

def endpoint (s : State) (input : ByteArray) (i : Nat)
    (h : Compression.HashState) : PackedStepFrame.Frame :=
  PackedCompressionBodyTrace.endpoint s (PackedDriverBounds.source i) h
    (UInt256.ofNat 466) (DriverTrace.blockOffsetWord i)
    (Padding.paddedWord input) []

def bodyMemory (s : State) (input : ByteArray) (i : Nat) : ByteArray :=
  (PackedPreprocessTrace.preprocessReturned s (PackedDriverBounds.source i)
    [UInt256.ofNat 466, DriverTrace.blockOffsetWord i,
      Padding.paddedWord input]).memory

/-- The actual driver landing instruction is included in the body trace.
The source-window and stack bounds are discharged from the caller's block
index rather than imposed as new caller assumptions. -/
theorem gasSteps_driverBody (s : State) (input : ByteArray) (i : Nat)
    (h : Compression.HashState) (hfit : CalldataFits input)
    (hi : i < DriverTrace.blockCount input)
    (hhash : StackMemory.hashAt s.memory = Compression.embedHash h)
    (hcode : s.executionEnv.code = submissionBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    ∃ t, ∃ _trace : GasSteps (DriverTrace.compressEntry s input i) t,
      t.stack = PackedStepFrame.frameStack (endpoint s input i h) ∧
      t.memory = bodyMemory s input i ∧
      t.executionEnv = s.executionEnv ∧ t.halt = .Running ∧
      t.callStack = s.callStack ∧ t.pc = UInt256.ofNat 5066 ∧
      16 ≤ t.activeWords.toNat := by
  obtain ⟨t, trace, hstack, hmem, henv, hhalt, hcalls, hpc, haw⟩ :=
    PackedCompressionBodyTrace.gasSteps_body s (PackedDriverBounds.source i) h
      (UInt256.ofNat 466) (DriverTrace.blockOffsetWord i)
      (Padding.paddedWord input) []
      (PackedDriverBounds.source_ge_512 i)
      (PackedDriverBounds.source_window_lt input hfit i hi)
      hhash (by decide) hcode hfork hrun hnp
  have landing := PackedDriverEntry.gasSteps_driverLanding s input i
    hcode hfork hrun hnp
  have joined : GasSteps (DriverTrace.compressEntry s input i) t :=
    landing.trans trace
  refine ⟨t, joined, ?_, hmem, henv, hhalt, hcalls, hpc, haw⟩
  simpa only [endpoint, List.append_nil] using hstack

#print axioms gasSteps_driverBody

end Challenge.Ripemd160.Submission.Proofs.Bytecode.PackedDriverBody
