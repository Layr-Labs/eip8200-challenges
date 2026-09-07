import Challenge.Modexp.Submission.Proofs.Bytecode.WindowHitTableEntryModulus
import Challenge.Modexp.Submission.Proofs.Bytecode.WindowHitTableEntryPrelude

set_option warningAsError true

namespace Challenge.Modexp.Submission.Proofs.Bytecode.WindowHitTableEntry

open EvmSemantics
open EvmSemantics.EVM
open WindowHitStates
open WindowHitPaths

abbrev run_modulus_nonzero := WindowHitTableEntryModulus.run_modulus_nonzero
abbrev run_modulus_zero := WindowHitTableEntryModulus.run_modulus_zero
abbrev run_tablePrelude := WindowHitTableEntryPrelude.run_tablePrelude

private def sound {s t : State}
    (path : List (Challenge.EvmProof.Stepper.Located
      Artifact.submissionArtifact .Osaka))
    (h : Challenge.EvmProof.Stepper.runLocatedBlock path s = some t)
    (hrun : s.halt = .Running := by rfl)
    (hcode : s.executionEnv.code = Artifact.submissionArtifact.code := by rfl)
    (hfork : s.fork = .Osaka := by rfl)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false := by
        exact deployAddress_not_precompile) :
    Challenge.EvmProof.GasSteps s t :=
  Challenge.EvmProof.Stepper.runLocatedBlock_sound
    Artifact.submissionArtifact .Osaka path hcode hfork h hrun hnp

def gasSteps_modulusNonzero (input : ByteArray)
    (hmodulus : modulusWord input ≠ 0) : ModulusNonzeroStep input :=
  sound modulusCheckPath (run_modulus_nonzero input hmodulus)

def gasSteps_modulusZero (input : ByteArray)
    (hmodulus : modulusWord input = 0) : ModulusZeroStep input :=
  sound modulusCheckPath (run_modulus_zero input hmodulus)

def gasSteps_tablePrelude (input : ByteArray) : TablePreludeStep input :=
  sound tablePreludePath (run_tablePrelude input)

end Challenge.Modexp.Submission.Proofs.Bytecode.WindowHitTableEntry
