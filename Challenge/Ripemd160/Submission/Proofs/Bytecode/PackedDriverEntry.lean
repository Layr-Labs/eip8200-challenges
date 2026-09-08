import Challenge.Ripemd160.Submission.Proofs.Bytecode.DriverTrace
import Challenge.Ripemd160.Submission.Proofs.Bytecode.PackedCompressionEntrySite
import Challenge.Ripemd160.Submission.Proofs.Bytecode.PackedCompressionGapSite

set_option warningAsError true
set_option autoImplicit false

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.PackedDriverEntry

open EvmSemantics EvmSemantics.EVM
open Challenge.EvmProof
open PackedCompressionEntrySite PackedCompressionGapSite

def entryStack (input : ByteArray) (i : Nat) : List UInt256 :=
  [DriverTrace.messageOffsetWord i, UInt256.ofNat 466,
    DriverTrace.blockOffsetWord i, Padding.paddedWord input]

/-- The driver really enters at 538; the gap proof starts one instruction
later. These states are linked by execution, not asserted equal. -/
def gasSteps_driverLanding (s : State) (input : ByteArray) (i : Nat)
    (hcode : s.executionEnv.code = Artifact.submissionArtifact.code)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    GasSteps (DriverTrace.compressEntry s input i)
      (gapEntry s (entryStack input i)) := by
  exact gasSteps_landingPath { s with stack := entryStack input i }
    (by simp [entryStack]) hcode hfork hrun hnp

#print axioms gasSteps_driverLanding

end Challenge.Ripemd160.Submission.Proofs.Bytecode.PackedDriverEntry
