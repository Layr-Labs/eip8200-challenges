import Challenge.Modexp.Submission.Proofs.Bytecode.Word

set_option warningAsError true
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000

namespace Challenge.Modexp.Submission.Proofs.Bytecode.Word

open EvmSemantics
open EvmSemantics.EVM

attribute [local simp] Challenge.EvmProof.Word.ofNat_add_mod
  Challenge.EvmProof.Word.succ_ofNat_mod

set_option linter.unusedSimpArgs false in
theorem run_expGuard (input : ByteArray) (i : Nat) (acc base : UInt256)
    (hvalid : ValidInput input) (hi : i < exponentSize input) :
    Challenge.EvmProof.Stepper.runLocatedBlock expGuardPath
      (expLoopState input i acc base) = some (expGuardState input i acc base) := by
  rcases hvalid with ⟨_, hb, he, hm⟩
  have hi256 : i < 2 ^ 256 := by omega
  have he256 : exponentSize input < 2 ^ 256 := by omega
  have himod : i % 2 ^ 256 = i := Nat.mod_eq_of_lt hi256
  have hemod : exponentSize input % 2 ^ 256 = exponentSize input :=
    Nat.mod_eq_of_lt he256
  have hne : i ≠ exponentSize input := Nat.ne_of_lt hi
  have heq : UInt256.eq (UInt256.ofNat i) (UInt256.ofNat (exponentSize input)) =
      UInt256.ofNat 0 := by
    rw [UInt256.eq, Challenge.EvmProof.Word.word_toNat_ofNat,
      Challenge.EvmProof.Word.word_toNat_ofNat, himod, hemod, if_neg hne]
  have h598 : (202 : UInt256).toNat = 202 := by decide
  have hzeroNat : (UInt256.ofNat 0).toNat = 0 := by decide
  simp (config := { maxSteps := 150000 })
    [expGuardPath, opAt, pushAt,
      Challenge.EvmProof.Stepper.runLocatedBlock,
      Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
      expLoopState, expGuardState, nonzeroState, callerRest,
      Dispatch.wordEntryState, Main.headerState, initialState, expPCs,
      UInt256.isTrue, Challenge.EvmProof.Word.word_toNat_ofNat,
      hi, hi256, he256, himod, hemod, hne, heq, hzeroNat, h598]

set_option linter.unusedSimpArgs false in
theorem run_genericJump (input : ByteArray) (i : Nat) (acc base : UInt256) :
    Challenge.EvmProof.Stepper.runLocatedBlock genericJumpPath
      (expGuardState input i acc base) = some (genericState input i acc base) := by
  have h218 : (218 : UInt256).toNat = 218 := by decide
  have h218Word : (218 : UInt256) = UInt256.ofNat 218 := by decide
  simp (config := { maxSteps := 150000 })
    [genericJumpPath, opAt, pushAt,
      Challenge.EvmProof.Stepper.runLocatedBlock,
      Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
      expGuardState, genericState, expLoopState, nonzeroState, callerRest,
      Dispatch.wordEntryState, Main.headerState, initialState, expPCs,
      Challenge.EvmProof.Word.word_toNat_ofNat, h218, h218Word, jump218]

/-- From the loop head with a nonzero exponent width to the generic route entry. -/
def gasSteps_toGeneric (input : ByteArray) (acc base : UInt256)
    (hvalid : ValidInput input) (he : 0 < exponentSize input) :
    Challenge.EvmProof.GasSteps (expLoopState input 0 acc base) (genericState input 0 acc base) :=
  (Challenge.EvmProof.Stepper.runLocatedBlock_sound
      Artifact.submissionArtifact .Osaka expGuardPath rfl rfl
        (run_expGuard input 0 acc base hvalid he) rfl
        deployAddress_not_precompile).trans
    (Challenge.EvmProof.Stepper.runLocatedBlock_sound
      Artifact.submissionArtifact .Osaka genericJumpPath rfl rfl
        (run_genericJump input 0 acc base) rfl
        deployAddress_not_precompile)

end Challenge.Modexp.Submission.Proofs.Bytecode.Word
