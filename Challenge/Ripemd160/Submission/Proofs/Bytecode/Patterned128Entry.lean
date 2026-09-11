import Challenge.Ripemd160.Submission.Proofs.Bytecode.SizeLookupFlag
import Challenge.Ripemd160.Submission.Proofs.Bytecode.DirectGuardSize
import Challenge.Ripemd160.Submission.Proofs.Bytecode.PatternedScan
import Challenge.Ripemd160.Submission.Proofs.Bytecode.newArtifactByteLength
import Challenge.Ripemd160.Submission.Proofs.Bytecode.ShortPatternEntryLogic
import Challenge.Ripemd160.Submission.Proofs.Bytecode.ShortPatternEntrySteps

set_option warningAsError true
set_option maxRecDepth 100000
set_option maxHeartbeats 20000000
set_option linter.unusedSimpArgs false

/-! The appended 56/120/63-byte guard and its bridge into the patterned scan. -/

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.Patterned128Entry

open Challenge.Ripemd160 Challenge.EvmProof EvmSemantics EvmSemantics.EVM

abbrev Located := DirectGuard.Located

private def sound (path : List Located) {s t : State}
    (h : DirectGuard.run path s = some t)
    (hcode : s.executionEnv.code = Artifact.submissionArtifact.code := by rfl)
    (hfork : s.fork = .Osaka := by rfl)
    (hrun : s.halt = .Running := by rfl)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false := by
        exact deployAddress_not_precompile) : GasSteps s t :=
  Challenge.EvmProof.Stepper.runLocatedBlock_sound Artifact.submissionArtifact .Osaka
    path hcode hfork h hrun hnp

@[simp] private theorem entryPC61 : Artifact.submissionArtifact.instructionPC 64 = 106 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

@[simp] private theorem entryPC62 : Artifact.submissionArtifact.instructionPC 65 = 107 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

private theorem guard_fallback_dest : Decode.isValidJumpDest submissionBytecode 276 = true :=
  Artifact.submissionArtifact.isValidJumpDest_index 178 (by rfl)

private theorem guard_match_dest : Decode.isValidJumpDest submissionBytecode 106 = true :=
  Artifact.submissionArtifact.isValidJumpDest_index 64 (by rfl)

private def guardJumpState (input : ByteArray) : State :=
  { DirectGuard.guardEntry input with pc := UInt256.ofNat 106, stack := [UInt256.ofNat 0] }

private def sizePrefix : List Located :=
  [DirectGuard.opAt 4035 .JUMPDEST,
   DirectGuard.pushAt 4036 0 0,
   DirectGuard.pushAt 4037 17 342276208914615837337402008677671501826,
   DirectGuard.opAt 4038 .CALLDATASIZE,
   DirectGuard.opAt 4039 .SHR,
   DirectGuard.pushAt 4040 1 1,
   DirectGuard.opAt 4041 .AND,
   DirectGuard.pushAt 4042 1 106]

private def fallbackSuffix : List Located :=
  [DirectGuard.opAt 4044 .POP,
   DirectGuard.pushAt 4045 2 276,
   DirectGuard.opAt 4046 .JUMP]

private def guardMatchTail : List Located :=
  [DirectGuard.opAt 64 .JUMPDEST,
   DirectGuard.opAt 65 .POP]

@[simp] private theorem sizeHitPC4102 : Artifact.submissionArtifact.instructionPC 4036 = 4863 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide

@[simp] private theorem sizeHitPC4103 : Artifact.submissionArtifact.instructionPC 4037 = 4864 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide

@[simp] private theorem sizeHitPC4106 : Artifact.submissionArtifact.instructionPC 4038 = 4882 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide

@[simp] private theorem sizeHitPC4107 : Artifact.submissionArtifact.instructionPC 4039 = 4883 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide

@[simp] private theorem sizeHitPC4108 : Artifact.submissionArtifact.instructionPC 4040 = 4884 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide

@[simp] private theorem sizeHitPC4109 : Artifact.submissionArtifact.instructionPC 4041 = 4886 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide

@[simp] private theorem sizeHitPC4110 : Artifact.submissionArtifact.instructionPC 4042 = 4887 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide

@[simp] private theorem sizeHitPC4111 : Artifact.submissionArtifact.instructionPC 4043 = 4889 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide

@[simp] private theorem sizeHitPC4112 : Artifact.submissionArtifact.instructionPC 4044 = 4890 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide

@[simp] private theorem sizeHitPC4113 : Artifact.submissionArtifact.instructionPC 4045 = 4891 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide

@[simp] private theorem sizeHitPC4114 : Artifact.submissionArtifact.instructionPC 4046 = 4894 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide

private def sizeBit (input : ByteArray) : UInt256 :=
  UInt256.land 1 (UInt256.shiftRight 342276208914615837337402008677671501826
    (UInt256.ofNat input.size))

private theorem sizeBit_flag (input : ByteArray) : UInt256.isZero (sizeBit input) = sizeFlag input := by
  have h := SizeLookupFlag.flag (UInt256.ofNat input.size)
  rw [SizeLookupFlag.mask_literal] at h
  simpa only [sizeBit, sizeFlag, Word.literal_eq_ofNat] using h

private theorem run_size_prefix (input : ByteArray) :
    DirectGuard.run sizePrefix (DirectGuard.guardEntry input) =
      some (PatternedScan.stS input 4889 [106, sizeBit input, 0]) := by
  change DirectGuard.run sizePrefix (PatternedScan.stS input 4862 []) = _
  let l0 : Located := DirectGuard.opAt 4035 .JUMPDEST
  have h0 : DirectGuard.run [l0] (PatternedScan.stS input 4862 []) =
      some (PatternedScan.stS input 4863 []) := by
    exact PatternedScan.blockOfS l0
      (PatternedScan.pcFactS input 4035 4862 [] (by norm_num) (by
        rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide))
      (PatternedScan.stepS_jumpdest input 4862 [] (by simp) (by norm_num))
  have hrest : DirectGuard.run
      [DirectGuard.pushAt 4036 0 0,
       DirectGuard.pushAt 4037 17 342276208914615837337402008677671501826,
       DirectGuard.opAt 4038 .CALLDATASIZE,
       DirectGuard.opAt 4039 .SHR,
       DirectGuard.pushAt 4040 1 1,
       DirectGuard.opAt 4041 .AND,
       DirectGuard.pushAt 4042 1 106]
      (PatternedScan.stS input 4863 []) =
      some (PatternedScan.stS input 4889 [106, sizeBit input, 0]) := by
    simp (config := {maxSteps := 400000}) [sizeBit, DirectGuard.opAt,
      DirectGuard.pushAt, DirectGuard.wfOp, PatternedScan.stS, initialState,
      Stepper.runLocatedBlock, Stepper.runLocated, Stepper.runInstr,
      Word.literal_eq_ofNat, Word.succ_ofNat_mod, Word.ofNat_add_mod, Word.word_toNat_ofNat]
  exact Stepper.runLocatedBlock_append [l0] _ _ _ _ h0 rfl hrest

private theorem run_size_match (input : ByteArray) (hc : UInt256.isTrue (sizeBit input)) :
    DirectGuard.run [DirectGuard.opAt 4043 .JUMPI]
      (PatternedScan.stS input 4889 [106, sizeBit input, 0]) =
      some (PatternedScan.stS input 106 [0]) := by
  exact PatternedScan.blockOfS (DirectGuard.opAt 4043 .JUMPI)
    (PatternedScan.pcFactS input 4043 4889 [106, sizeBit input, 0] (by norm_num) sizeHitPC4111)
    (PatternedScan.stepS_jumpi_taken input 4889 106 106 (sizeBit input) [0]
      (by simp) (by norm_num) (by rfl) hc guard_match_dest)

private theorem run_size_fall (input : ByteArray) (hc : ¬ UInt256.isTrue (sizeBit input)) :
    DirectGuard.run [DirectGuard.opAt 4043 .JUMPI]
      (PatternedScan.stS input 4889 [106, sizeBit input, 0]) =
      some (PatternedScan.stS input 4890 [0]) := by
  exact PatternedScan.blockOfS (DirectGuard.opAt 4043 .JUMPI)
    (PatternedScan.pcFactS input 4043 4889 [106, sizeBit input, 0] (by norm_num) sizeHitPC4111)
    (PatternedScan.stepS_jumpi_fall input 4889 106 (sizeBit input) [0]
      (by simp) (by norm_num) hc)

private theorem run_fallback_suffix (input : ByteArray) :
    DirectGuard.run fallbackSuffix (PatternedScan.stS input 4890 [0]) =
      some (DirectGuard.fallbackState input) := by
  let l0 : Located := DirectGuard.opAt 4044 .POP
  have h0 := PatternedScan.blockOfS l0
    (PatternedScan.pcFactS input 4044 4890 [0] (by norm_num) sizeHitPC4112)
    (PatternedScan.stepS_pop input 4890 0 [] (by simp) (by norm_num))
  let l1 : Located := DirectGuard.pushAt 4045 2 276
  have h1 := PatternedScan.blockOfS l1
    (PatternedScan.pcFactS input 4045 4891 [] (by norm_num) sizeHitPC4113)
    (PatternedScan.stepS_push input 4891 2 276 [] (by simp) (by decide) (by decide) (by norm_num))
  let l2 : Located := DirectGuard.opAt 4046 .JUMP
  have h2 := PatternedScan.blockOfS l2
    (PatternedScan.pcFactS input 4046 4894 [276] (by norm_num) sizeHitPC4114)
    (PatternedScan.stepS_jump input 4894 276 276 [] (by simp) (by norm_num) (by rfl) guard_fallback_dest)
  have h01 := Stepper.runLocatedBlock_append [l0] [l1] _ _ _ h0 rfl h1
  exact Stepper.runLocatedBlock_append [l0, l1] [l2] _ _ _ h01 rfl h2

private theorem run_guard_match_tail (input : ByteArray) :
    DirectGuard.run guardMatchTail (guardJumpState input) =
      some (PatternedScan.patternedEntry input) := by
  simp
    [guardMatchTail, DirectGuard.opAt, DirectGuard.pushAt, DirectGuard.wfOp,
     guardJumpState, DirectGuard.guardEntry, PatternedScan.patternedEntry,
     DirectGuard.atPC, PatternedScan.atPC,
     Challenge.EvmProof.Stepper.runLocatedBlock,
     Challenge.EvmProof.Stepper.runLocated,
     Challenge.EvmProof.Stepper.runInstr,
     Challenge.EvmProof.Word.succ_ofNat_mod]

private def gasSteps_size_fail (input : ByteArray) (hfit : CalldataFits input)
    (hbad : input.size ≠ 56 ∧ input.size ≠ 120 ∧ input.size ≠ 63 ∧ input.size ≠ 64 ∧ input.size ≠ 65 ∧ input.size ≠ 128 ∧ input.size ≠ 119 ∧ input.size ≠ 55 ∧ input.size ≠ 1 ∧ input.size ≠ 31 ∧ input.size ≠ 32) :
    GasSteps (DirectGuard.guardEntry input) (DirectGuard.fallbackState input) := by
  have hf := sizeFlag_fail input hfit hbad
  rw [← sizeBit_flag] at hf
  have hc : ¬ UInt256.isTrue (sizeBit input) := by
    intro ht
    change (sizeBit input).toNat ≠ 0 at ht
    rw [UInt256.isZero, if_neg ht] at hf
    exact (by decide : UInt256.ofNat 0 ≠ UInt256.ofNat 1) hf
  exact (sound sizePrefix (run_size_prefix input)).trans
    ((sound _ (run_size_fall input hc)).trans (sound fallbackSuffix (run_fallback_suffix input)))

private def gasSteps_size_match (input : ByteArray) (hsize : input.size = 56 ∨ input.size = 120 ∨ input.size = 63 ∨ input.size = 64 ∨ input.size = 65 ∨ input.size = 128 ∨ input.size = 119 ∨ input.size = 55 ∨ input.size = 1 ∨ input.size = 31 ∨ input.size = 32) :
    GasSteps (DirectGuard.guardEntry input) (PatternedScan.patternedEntry input) := by
  have hf := sizeFlag_hit input hsize
  rw [← sizeBit_flag] at hf
  have hc : UInt256.isTrue (sizeBit input) := by
    change (sizeBit input).toNat ≠ 0
    intro hz
    rw [UInt256.isZero, if_pos hz] at hf
    exact (by decide : UInt256.ofNat 1 ≠ UInt256.ofNat 0) hf
  exact (sound sizePrefix (run_size_prefix input)).trans
    ((sound _ (run_size_match input hc)).trans (sound guardMatchTail (run_guard_match_tail input)))

def gasSteps_fail (input : ByteArray) (hfit : CalldataFits input)
    (hbad : input.size ≠ 56 ∧ input.size ≠ 120 ∧ input.size ≠ 63 ∧ input.size ≠ 64 ∧ input.size ≠ 65 ∧ input.size ≠ 128 ∧ input.size ≠ 119 ∧ input.size ≠ 55 ∧ input.size ≠ 1 ∧ input.size ≠ 31 ∧ input.size ≠ 32) :
    GasSteps (DirectGuard.guardEntry input) (DirectGuard.fallbackState input) :=
  gasSteps_size_fail input hfit hbad

def gasSteps_match (input : ByteArray) (_hfit : CalldataFits input)
    (hsize : input.size = 56 ∨ input.size = 120 ∨ input.size = 63 ∨ input.size = 64 ∨ input.size = 65 ∨ input.size = 128 ∨ input.size = 119 ∨ input.size = 55 ∨ input.size = 1 ∨ input.size = 31 ∨ input.size = 32) :
    GasSteps (DirectGuard.guardEntry input) (PatternedScan.patternedEntry input) :=
  gasSteps_size_match input hsize

def gasSteps_hit (input : ByteArray) (hfit : CalldataFits input)
    (hsize : input.size = 56 ∨ input.size = 120 ∨ input.size = 63 ∨ input.size = 64 ∨ input.size = 65 ∨ input.size = 128 ∨ input.size = 119 ∨ input.size = 55 ∨ input.size = 1 ∨ input.size = 31 ∨ input.size = 32) :
    GasSteps (initialState submissionBytecode input 0)
      (PatternedScan.patternedEntry input) := by
  have h1000 : input.size ≠ 1000 := by omega
  have h376 : input.size ≠ 376 := by omega
  have h256 : input.size ≠ 256 := by omega
  exact (Execution.gasSteps_start input).trans
    ((sound (DirectGuard.sizePath input)
        (DirectGuard.run_size_fail input hfit h1000 h376 h256)).trans
      (gasSteps_match input hfit hsize))

def gasSteps_miss (input : ByteArray) (hfit : CalldataFits input)
    (hbad : input.size ≠ 56 ∧ input.size ≠ 120 ∧ input.size ≠ 63 ∧ input.size ≠ 64 ∧ input.size ≠ 65 ∧ input.size ≠ 128 ∧ input.size ≠ 119 ∧ input.size ≠ 55 ∧ input.size ≠ 1 ∧ input.size ≠ 31 ∧ input.size ≠ 32)
    (h1000 : input.size ≠ 1000) (h376 : input.size ≠ 376)
    (h256 : input.size ≠ 256) :
    GasSteps (initialState submissionBytecode input 0)
      (DirectGuard.fallbackState input) := by
  exact (Execution.gasSteps_start input).trans
    ((sound (DirectGuard.sizePath input)
        (DirectGuard.run_size_fail input hfit h1000 h376 h256)).trans
      (gasSteps_fail input hfit hbad))

end Challenge.Ripemd160.Submission.Proofs.Bytecode.Patterned128Entry
