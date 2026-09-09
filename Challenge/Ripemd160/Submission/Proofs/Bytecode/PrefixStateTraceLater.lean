import Challenge.Ripemd160.Submission.Proofs.Bytecode.FastEmptyBlock
import Challenge.Ripemd160.Submission.Proofs.Bytecode.PrefixStatePaths
import Challenge.Ripemd160.Submission.Proofs.Bytecode.PrefixStateModel

set_option warningAsError true
set_option maxRecDepth 50000
set_option maxHeartbeats 5000000
set_option linter.unusedSimpArgs false

/-! Raw later-block dispatch for the H8 checked prefix.

`PrefixStatePaths.laterPath` is the four-instruction prologue at PC 5193:
`JUMPDEST`, `DUP3` (stack index 2, duplicating the driver block offset),
`PUSH2 464`, and `JUMPI`.  For a later block (`i ≠ 0`, so the block offset
word is nonzero under the calldata-fit bound) the jump is taken and the
helper falls straight into the generic compression entry with the stack
unchanged.  No prefix bytes are inspected on this branch, so it applies to
every `i ≠ 0` regardless of `Matched`. -/

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.PrefixStateTraceLater

open Challenge.Ripemd160 Challenge.EvmProof EvmSemantics EvmSemantics.EVM

/-- The generic compression target `464` is a valid jump destination. -/
theorem jumpDest_generic : Decode.isValidJumpDest submissionBytecode 460 = true := by
  have hpc : Artifact.submissionArtifact.instructionPC 271 = 460 := by
    rw [ArtifactByteLength.instructionPC_eq_byteLength]
    decide
  have h := Artifact.submissionArtifact.isValidJumpDest_index 271 (by rfl)
  rw [hpc] at h
  exact h

/-- Driver block offsets stay inside the `UInt256` range. -/
theorem blockOffset_lt_uint256 (input : ByteArray)
    (hfit : Challenge.Ripemd160.CalldataFits input) (i : Nat)
    (hi : i ≤ DriverTrace.blockCount input) :
    DriverTrace.blockOffset i < 2 ^ 256 := by
  have hpad := Padding.paddedLength_lt input.size
  have heq := DriverTrace.paddedLength_eq_blockCount input
  unfold Challenge.Ripemd160.CalldataFits at hfit
  norm_num at hfit ⊢
  unfold DriverTrace.blockOffset
  omega

theorem run_later (s : State) (input : ByteArray) (i : Nat)
    (hne : i ≠ 0)
    (hoff : DriverTrace.blockOffset i < 2 ^ 256)
    (hcode : s.executionEnv.code = submissionBytecode)
    (hrun : s.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock PrefixStatePaths.laterPath
      (FastEmptyBlock.nonemptyEntry s input i) =
      some (DriverTrace.compressEntry s input i) := by
  have hdup : ((FastEmptyBlock.nonemptyEntry s input i).stack[2]? :
      Option UInt256) = some (DriverTrace.blockOffsetWord i) := by
    show ([DriverTrace.messageOffsetWord i, UInt256.ofNat 102,
        DriverTrace.blockOffsetWord i, Padding.paddedWord input][2]? :
        Option UInt256) = some _
    simp
  have hcond : UInt256.isTrue (DriverTrace.blockOffsetWord i) := by
    unfold UInt256.isTrue DriverTrace.blockOffsetWord
    rw [Challenge.EvmProof.Word.word_toNat_ofNat, Nat.mod_eq_of_lt hoff]
    unfold DriverTrace.blockOffset
    omega
  simp (config := { maxSteps := 300000 })
    [PrefixStatePaths.laterPath, Challenge.EvmProof.Stepper.runLocatedBlock,
      Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
      FastEmptyBlock.nonemptyEntry, DriverTrace.compressEntry,
      hdup, hcond, PrefixStatePaths.pc4013, PrefixStatePaths.pc4014,
      PrefixStatePaths.pc4015, PrefixStatePaths.pc4016,
      jumpDest_generic, hrun, hcode,
      Challenge.EvmProof.Word.word_toNat_ofNat,
      Challenge.EvmProof.Word.ofNat_add_mod,
      Challenge.EvmProof.Word.succ_ofNat_mod]

/-- `GasSteps` lift of the later dispatch, plain endpoints. -/
def gasSteps_later_plain (s : State) (input : ByteArray) (i : Nat)
    (hne : i ≠ 0)
    (hoff : DriverTrace.blockOffset i < 2 ^ 256)
    (hcode : s.executionEnv.code = submissionBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    Challenge.EvmProof.GasSteps (FastEmptyBlock.nonemptyEntry s input i)
      (DriverTrace.compressEntry s input i) :=
  Challenge.EvmProof.Stepper.runLocatedBlock_sound
    Artifact.submissionArtifact .Osaka PrefixStatePaths.laterPath
    hcode hfork (run_later s input i hne hoff hcode hrun) hrun hnp

/-- `GasSteps` lift of the later dispatch with an explicit offset bound. -/
def gasSteps_later (s : State) (input : ByteArray) (i : Nat)
    (hne : i ≠ 0)
    (hoff : DriverTrace.blockOffset i < 2 ^ 256)
    (hcode : s.executionEnv.code = submissionBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    Challenge.EvmProof.GasSteps (FastEmptyBlock.nonemptyEntry s input i)
      (DriverTrace.compressEntry (PrefixStateModel.prepared s i) input i) := by
  have hprep : PrefixStateModel.prepared s i = s := by
    unfold PrefixStateModel.prepared
    rw [if_neg hne]
  exact Challenge.EvmProof.GasSteps.cast
    (gasSteps_later_plain s input i hne hoff hcode hfork hrun hnp)
    rfl (by rw [hprep])

/-- Main later-block certificate from the driver bounds `hfit` and `hi`. -/
def gasSteps_later_of_bounds (s : State) (input : ByteArray) (i : Nat)
    (hne : i ≠ 0)
    (hfit : Challenge.Ripemd160.CalldataFits input)
    (hi : i < DriverTrace.blockCount input)
    (hcode : s.executionEnv.code = submissionBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    Challenge.EvmProof.GasSteps (FastEmptyBlock.nonemptyEntry s input i)
      (DriverTrace.compressEntry (PrefixStateModel.prepared s i) input i) :=
  gasSteps_later s input i hne
    (blockOffset_lt_uint256 input hfit i (Nat.le_of_lt hi))
    hcode hfork hrun hnp

#print axioms run_later
#print axioms gasSteps_later
#print axioms gasSteps_later_of_bounds

end Challenge.Ripemd160.Submission.Proofs.Bytecode.PrefixStateTraceLater
