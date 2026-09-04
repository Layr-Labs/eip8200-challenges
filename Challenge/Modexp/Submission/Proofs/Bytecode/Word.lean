import Challenge.Modexp.Submission.Proofs.Bytecode.WordBitTail
set_option warningAsError true
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000
set_option maxErrors 1
/-!
# One-word MODEXP path: loop back-edge and gas certificates

Split out of the original single-file `Word` module; the earlier certificate
blocks now live in `WordDefs` and `WordExp`.
-/
namespace Challenge.Modexp.Submission.Proofs.Bytecode.Word

open EvmSemantics
open EvmSemantics.EVM

attribute [local simp] Challenge.EvmProof.Word.ofNat_add_mod
  Challenge.EvmProof.Word.succ_ofNat_mod


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

def gasSteps_baseIteration (input : ByteArray) (i : Nat) (base : UInt256)
    (hvalid : ValidInput input) (hi : i < baseSize input) :
    Challenge.EvmProof.GasSteps (baseLoopState input i base)
      (baseLoopState input (i + 1) (baseStep input i base)) := by
  have h562 : (562 : UInt256).toNat = 562 := by decide
  have hcap : (baseRest input i base).length < 1017 := by
    simp [baseRest, callerRest]
  have hjump : Decode.isValidJumpDest submissionBytecode
      (562 : UInt256).toNat = true := by
    rw [h562]
    exact jump562
  exact (Challenge.EvmProof.Stepper.runLocatedBlock_sound
      Artifact.submissionArtifact .Osaka baseGuardPath rfl rfl
        (run_baseGuard input i base hvalid hi) rfl
        deployAddress_not_precompile).trans <|
    (Challenge.EvmProof.Stepper.runLocatedBlock_sound
      Artifact.submissionArtifact .Osaka baseCallPath rfl rfl
        (run_baseCall input i base hvalid hi) rfl
        deployAddress_not_precompile).trans <|
    (Accessors.gasSteps_calldataByte (baseLoopState input i base)
      (UInt256.ofNat (96 + i)) 0 562 (baseRest input i base)
      hcap rfl rfl rfl deployAddress_not_precompile hjump).trans <|
    Challenge.EvmProof.Stepper.runLocatedBlock_sound
      Artifact.submissionArtifact .Osaka baseTailPath rfl rfl
        (run_baseTail input i base hvalid hi) rfl deployAddress_not_precompile

def gasSteps_baseLoop (input : ByteArray) (hvalid : ValidInput input) :
    Challenge.EvmProof.GasSteps (baseLoopState input 0 0)
      (baseLoopState input (baseSize input) (baseAfter input (baseSize input))) := by
  exact Challenge.EvmProof.GasSteps.iterateBounded (baseSize input)
    (fun i hi => gasSteps_baseIteration input i (baseAfter input i) hvalid hi)

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

def gasSteps_zeroModulus_total (input : ByteArray) (hvalid : ValidInput input)
    (hmsize : 0 < modulusSize input) (hword : modulusSize input ≤ 32)
    (hmodulus : modulusValue input = 0) :
    Challenge.EvmProof.GasSteps (initialState submissionBytecode input 0)
      (zeroModulusFinalState input) :=
  ((Main.gasSteps_header input hvalid).trans
    (Dispatch.gasSteps_wordEntry input hvalid hmsize hword)).trans
      (gasSteps_zeroModulus input hvalid hmsize hword hmodulus)

@[simp] theorem zeroModulusFinalState_isDone (input : ByteArray) :
    (zeroModulusFinalState input).isDone = true := by
  rfl

theorem zeroModulusFinalState_result (input : ByteArray)
    (hmsize : 0 < modulusSize input) (hmodulus : modulusValue input = 0) :
    (zeroModulusFinalState input).toResult = .returned (spec input) := by
  rw [show (zeroModulusFinalState input).toResult =
      .returned (Precompile.natToBytes 0 (modulusSize input)) by
    simp [zeroModulusFinalState, Algorithm.zeroBytes]]
  have hmodulus' :
      Precompile.bytesToNatPadded input
        (96 + baseSize input + exponentSize input) (modulusSize input) = 0 := by
    simpa [modulusValue, modulusOffset, expOffset, Nat.add_assoc] using hmodulus
  simp [spec, Nat.ne_of_gt hmsize, hmodulus', Precompile.modPow]

end Challenge.Modexp.Submission.Proofs.Bytecode.Word



