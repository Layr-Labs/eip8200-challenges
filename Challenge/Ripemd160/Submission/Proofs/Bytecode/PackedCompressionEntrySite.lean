import Challenge.Ripemd160.Submission.Proofs.Bytecode.Artifact
import Challenge.EvmProof.Stepper
import Challenge.EvmProof.Word

set_option warningAsError true
set_option autoImplicit false
set_option maxRecDepth 10000

/-!
# Exact packed-compression landing site

The nonempty driver lands on the compression `JUMPDEST` at PC 538.  The
packed gap certificate starts at PC 539.  This file certifies that one-byte
artifact seam directly; it does not identify the surrounding driver and
compression traces by an assumed state equality.
-/

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.PackedCompressionEntrySite

open Challenge.EvmProof
open EvmSemantics EvmSemantics.EVM

private def wfJumpdest : Stepper.WellFormed .Osaka (.op .JUMPDEST) :=
  ⟨by decide, trivial, rfl⟩

/-- The actual compression landing instruction, index 296 / PC 538. -/
def landingPath : List (Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [⟨296, .op .JUMPDEST, by rfl, wfJumpdest⟩]

private theorem pc296 : Artifact.submissionArtifact.instructionPC 296 = 538 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

/-- Any state normalized to the actual compression landing PC. -/
def landingEntry (s : State) : State :=
  { s with pc := UInt256.ofNat 538 }

/-- The same state immediately after executing the landing `JUMPDEST`. -/
def landingExit (s : State) : State :=
  { s with pc := UInt256.ofNat 539 }

/-- Execute the exact landing `JUMPDEST`, advancing PC 538 to PC 539 while
preserving every other state field. -/
theorem run_landingPath (s : State) (hcap : s.stack.length < 1024) :
    Stepper.runLocatedBlock landingPath (landingEntry s) =
      some (landingExit s) := by
  simp [landingPath, Stepper.runLocatedBlock, Stepper.runLocated,
    Stepper.runInstr, landingEntry, landingExit, pc296, hcap,
    Challenge.EvmProof.Word.succ_ofNat_mod]

/-- Gas-parametric semantic certificate for the formerly missing 538 -> 539
compression-entry seam. -/
def gasSteps_landingPath (s : State) (hcap : s.stack.length < 1024)
    (hcode : s.executionEnv.code = Artifact.submissionArtifact.code)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    GasSteps (landingEntry s) (landingExit s) := by
  apply Stepper.runLocatedBlock_sound Artifact.submissionArtifact .Osaka
    landingPath
  · simpa [landingEntry] using hcode
  · simpa [landingEntry] using hfork
  · exact run_landingPath s hcap
  · simpa [landingEntry] using hrun
  · simpa [landingEntry] using hnp

#print axioms run_landingPath
#print axioms gasSteps_landingPath

end Challenge.Ripemd160.Submission.Proofs.Bytecode.PackedCompressionEntrySite
