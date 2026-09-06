import Challenge.Modexp.Submission.Proofs.Bytecode.Word
import Challenge.Modexp.Submission.Proofs.Bytecode.WordBaseTail
import Challenge.Modexp.Submission.Proofs.Bytecode.WordBaseFinish

set_option warningAsError true
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000

namespace Challenge.Modexp.Submission.Proofs.Bytecode.Word

open EvmSemantics
open EvmSemantics.EVM

def gasSteps_start (input : ByteArray) (hvalid : ValidInput input)
    (hmsize : 0 < modulusSize input) (hword : modulusSize input ≤ 32)
    (hmodulus : 0 < modulusValue input) :
    Challenge.EvmProof.GasSteps (Dispatch.wordEntryState input)
      (nonzeroState input) := by
  have hmodlt : modulusValue input < 2 ^ 256 :=
    (Challenge.EvmProof.Bytes.bytesToNatPadded_lt_pow input
      (modulusOffset input) (modulusSize input)).trans_le (by
        have hp := pow_le_pow_right₀ (by omega : 1 ≤ (256 : Nat)) hword
        exact hp.trans (by norm_num))
  exact (Challenge.EvmProof.Stepper.runLocatedBlock_sound
      Artifact.submissionArtifact .Osaka startLoadPath rfl rfl
        (run_startLoad input hvalid hmsize hword) rfl
        deployAddress_not_precompile).trans
    (Challenge.EvmProof.Stepper.runLocatedBlock_sound
      Artifact.submissionArtifact .Osaka startJumpPath rfl rfl
        (run_startJump_nonzero input hmodulus hmodlt) rfl
        deployAddress_not_precompile)

def gasSteps_baseSetup (input : ByteArray) :
    Challenge.EvmProof.GasSteps (nonzeroState input)
      (baseLoopState input 0 0) := by
  apply Challenge.EvmProof.Stepper.runLocatedBlock_sound
    Artifact.submissionArtifact .Osaka baseSetupPath
  · rfl
  · rfl
  · exact run_baseSetup input
  · rfl
  · exact deployAddress_not_precompile

def gasSteps_baseFinish (input : ByteArray) (base : UInt256)
    (hvalid : ValidInput input) (hword : modulusSize input ≤ 32) :
    Challenge.EvmProof.GasSteps (baseLoopState input (baseSize input) base)
      (expLoopState input 0
        (UInt256.ofNat 1 % UInt256.ofNat (modulusValue input)) base) := by
  exact (Challenge.EvmProof.Stepper.runLocatedBlock_sound
      Artifact.submissionArtifact .Osaka baseGuardPath rfl rfl
        (run_baseFinishGuard input base hvalid) rfl
        deployAddress_not_precompile).trans
    (Challenge.EvmProof.Stepper.runLocatedBlock_sound
      Artifact.submissionArtifact .Osaka baseFinishTailPath rfl rfl
        (run_baseFinishTail input base hvalid hword) rfl
        deployAddress_not_precompile)

def gasSteps_zeroModulus (input : ByteArray) (hvalid : ValidInput input)
    (hmsize : 0 < modulusSize input) (hword : modulusSize input ≤ 32)
    (hmodulus : modulusValue input = 0) :
    Challenge.EvmProof.GasSteps (Dispatch.wordEntryState input)
      (zeroModulusFinalState input) := by
  exact (Challenge.EvmProof.Stepper.runLocatedBlock_sound
      Artifact.submissionArtifact .Osaka startLoadPath rfl rfl
        (run_startLoad input hvalid hmsize hword) rfl
        deployAddress_not_precompile).trans <|
    (Challenge.EvmProof.Stepper.runLocatedBlock_sound
      Artifact.submissionArtifact .Osaka startJumpPath rfl rfl
        (run_startJump_zero input hmodulus) rfl
        deployAddress_not_precompile).trans
    (Challenge.EvmProof.Stepper.runLocatedBlock_sound
      Artifact.submissionArtifact .Osaka zeroTailPath rfl rfl
        (run_zeroTail input hvalid hmodulus) rfl deployAddress_not_precompile)

end Challenge.Modexp.Submission.Proofs.Bytecode.Word
