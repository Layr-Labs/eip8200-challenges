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

/- The failure path stops at JUMPI.  It must not include the success suffix:
   a taken JUMPI changes the PC to 360, so the next located instruction would
   fail the PC check. -/
@[simp] private theorem entryPC61 : Artifact.submissionArtifact.instructionPC 59 = 98 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

@[simp] private theorem entryPC62 : Artifact.submissionArtifact.instructionPC 60 = 99 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide









@[simp] private theorem entryPC4154 : Artifact.submissionArtifact.instructionPC 4126 = 5163 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

@[simp] private theorem entryPC4155 : Artifact.submissionArtifact.instructionPC 4127 = 5166 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

@[simp] private theorem entryPC4156 : Artifact.submissionArtifact.instructionPC 4128 = 5167 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

@[simp] private theorem entryPC4157 : Artifact.submissionArtifact.instructionPC 4129 = 5168 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

@[simp] private theorem entryPC4158 : Artifact.submissionArtifact.instructionPC 4130 = 5170 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

@[simp] private theorem entryPC4166 : Artifact.submissionArtifact.instructionPC 4119 = 5139 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

@[simp] private theorem entryPC4167 : Artifact.submissionArtifact.instructionPC 4120 = 5140 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

@[simp] private theorem entryPC4168 : Artifact.submissionArtifact.instructionPC 4121 = 5157 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

@[simp] private theorem entryPC4169 : Artifact.submissionArtifact.instructionPC 4122 = 5158 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

@[simp] private theorem entryPC4170 : Artifact.submissionArtifact.instructionPC 4123 = 5159 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

@[simp] private theorem entryPC4171 : Artifact.submissionArtifact.instructionPC 4124 = 5161 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

@[simp] private theorem entryPC4172 : Artifact.submissionArtifact.instructionPC 4125 = 5162 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

@[simp] private theorem entryPC4173 : Artifact.submissionArtifact.instructionPC 4125 = 5162 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

@[simp] private theorem entryPC4174 : Artifact.submissionArtifact.instructionPC 4125 = 5162 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

@[simp] private theorem entryPC4175 : Artifact.submissionArtifact.instructionPC 4125 = 5162 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

@[simp] private theorem entryPC4176 : Artifact.submissionArtifact.instructionPC 4125 = 5162 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

@[simp] private theorem entryPC4177 : Artifact.submissionArtifact.instructionPC 4125 = 5162 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

@[simp] private theorem entryPC4178 : Artifact.submissionArtifact.instructionPC 4125 = 5162 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide





@[simp] private theorem entryOr00 : UInt256.lor (UInt256.ofNat 0) (UInt256.ofNat 0) = UInt256.ofNat 0 := by rfl

@[simp] private theorem entryOr01 : UInt256.lor (UInt256.ofNat 0) (UInt256.ofNat 1) = UInt256.ofNat 1 := by rfl

@[simp] private theorem entryOr10 : UInt256.lor (UInt256.ofNat 1) (UInt256.ofNat 0) = UInt256.ofNat 1 := by rfl

@[simp] private theorem entryOr11 : UInt256.lor (UInt256.ofNat 1) (UInt256.ofNat 1) = UInt256.ofNat 1 := by rfl

private def guardJumpPath : List Located := []

private def guardSizePath : List Located :=
  [DirectGuard.opAt 4119 .JUMPDEST,
   DirectGuard.pushAt 4120 16 1329227995784915882199236691173048320,
   DirectGuard.opAt 4121 .CALLDATASIZE,
   DirectGuard.opAt 4122 .SHR,
   DirectGuard.pushAt 4123 1 1,
   DirectGuard.opAt 4124 .AND,
   DirectGuard.opAt 4125 .ISZERO]

private def guardBytePrefix : List Located :=
  [DirectGuard.pushAt 4126 2 360]

private def guardBytePath : List Located := guardBytePrefix ++ [DirectGuard.opAt 4127 .JUMPI]

private def guardCheckPath : List Located := guardJumpPath ++ guardSizePath ++ guardBytePath

private def guardMatchSuffix : List Located :=
  [DirectGuard.pushAt 4128 0 0,
   DirectGuard.pushAt 4129 1 98,
   DirectGuard.opAt 4130 .JUMP]

private def guardMatchTail : List Located :=
  [DirectGuard.opAt 59 .JUMPDEST, DirectGuard.opAt 60 .POP]

private def guardJumpState (input : ByteArray) : State :=
  { DirectGuard.guardEntry input with
    pc := UInt256.ofNat 98
    stack := [UInt256.ofNat 0] }

private theorem guard_fallback_dest :
    Decode.isValidJumpDest submissionBytecode 360 = true :=
  Artifact.submissionArtifact.isValidJumpDest_index 199 (by rfl)

private theorem guard_match_dest :
    Decode.isValidJumpDest submissionBytecode 98 = true :=
  Artifact.submissionArtifact.isValidJumpDest_index 59 (by rfl)

private def sizeEntry (input : ByteArray) : State := PatternedScan.stS input 5139 []
private def byteEntry (input : ByteArray) (flag : UInt256) : State :=
  PatternedScan.stS input 5163 [flag]
private def byteDone (input : ByteArray) : State := PatternedScan.stS input 5167 []

private theorem run_guard_jump (input : ByteArray) :
    DirectGuard.run guardJumpPath (DirectGuard.guardEntry input) = some (sizeEntry input) := by
  rfl

private theorem run_guard_size (input : ByteArray) :
    DirectGuard.run guardSizePath (sizeEntry input) = some (byteEntry input (sizeFlag input)) := by
  let m : UInt256 := 1329227995784915882199236691173048320
  let x : UInt256 := UInt256.ofNat input.size
  let shifted : UInt256 := UInt256.shiftRight m x
  let bit : UInt256 := UInt256.land 1 shifted
  let l0 : Located := DirectGuard.opAt 4119 .JUMPDEST
  have h0 := PatternedScan.blockOfS l0
    (PatternedScan.pcFactS input 4119 5139 [] (by norm_num) (by
      rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide))
    (PatternedScan.stepS_jumpdest input 5139 [] (by simp) (by norm_num))
  let l1 : Located := DirectGuard.pushAt 4120 16 1329227995784915882199236691173048320
  have h1 := PatternedScan.blockOfS l1
    (PatternedScan.pcFactS input 4120 5140 [] (by norm_num) (by
      rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide))
    (PatternedScan.stepS_push input 5140 16 1329227995784915882199236691173048320 [] (by simp) (by decide) (by decide) (by norm_num))
  let l3 : Located := DirectGuard.opAt 4121 .CALLDATASIZE
  have h3 := PatternedScan.blockOfS l3
    (PatternedScan.pcFactS input 4121 5157 [m] (by norm_num) (by
      rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide))
    (PatternedScan.stepS_calldatasize input 5157 [m] (by simp) (by norm_num))
  let l5 : Located := DirectGuard.opAt 4122 .SHR
  have h5 := PatternedScan.blockOfS l5
    (PatternedScan.pcFactS input 4122 5158 [x, m] (by norm_num) (by
      rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide))
    (PatternedScan.stepS_shr input 5158 x m [] (by simp) (by norm_num))
  let l6 : Located := DirectGuard.pushAt 4123 1 1
  have h6 := PatternedScan.blockOfS l6
    (PatternedScan.pcFactS input 4123 5159 [shifted] (by norm_num) (by
      rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide))
    (PatternedScan.stepS_push input 5159 1 1 [shifted] (by simp) (by decide) (by decide) (by norm_num))
  let l7 : Located := DirectGuard.opAt 4124 .AND
  have h7 := PatternedScan.blockOfS l7
    (PatternedScan.pcFactS input 4124 5161 [1, shifted] (by norm_num) (by
      rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide))
    (PatternedScan.stepS_and input 5161 1 shifted [] (by simp) (by norm_num))
  let l8 : Located := DirectGuard.opAt 4125 .ISZERO
  have h8 := PatternedScan.blockOfS l8
    (PatternedScan.pcFactS input 4125 5162 [bit] (by norm_num) (by
      rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide))
    (PatternedScan.stepS_iszero input 5162 bit [] (by simp) (by norm_num))
  have h01 := Stepper.runLocatedBlock_append [l0] [l1] _ _ _ h0 rfl h1
  have h03 := Stepper.runLocatedBlock_append [l0, l1] [l3] _ _ _ h01 rfl h3
  have h05 := Stepper.runLocatedBlock_append [l0, l1, l3] [l5] _ _ _ h03 rfl h5
  have h06 := Stepper.runLocatedBlock_append [l0, l1, l3, l5] [l6] _ _ _ h05 rfl h6
  have h07 := Stepper.runLocatedBlock_append [l0, l1, l3, l5, l6] [l7] _ _ _ h06 rfl h7
  have h08 := Stepper.runLocatedBlock_append [l0, l1, l3, l5, l6, l7] [l8] _ _ _ h07 rfl h8
  have hf : UInt256.isZero bit = sizeFlag input := by
    have h := SizeLookupFlag.flag x
    rw [SizeLookupFlag.mask_literal] at h
    simpa only [bit, shifted, m, x, sizeFlag, Word.literal_eq_ofNat] using h
  rw [hf] at h08
  exact h08


private theorem run_guard_byte_prefix (input : ByteArray) (flag : UInt256) :
    DirectGuard.run guardBytePrefix (byteEntry input flag) =
      some (PatternedScan.stS input 5166 [360, flag]) :=
  PatternedScan.blockOfS (DirectGuard.pushAt 4126 2 360)
    (PatternedScan.pcFactS input 4126 5163 [flag] (by norm_num) entryPC4154)
    (PatternedScan.stepS_push input 5163 2 360 [flag] (by simp) (by decide) (by decide) (by norm_num))

private theorem run_guard_byte_fail (input : ByteArray) (flag : UInt256)
    (hflag : flag = UInt256.ofNat 1) :
    DirectGuard.run guardBytePath (byteEntry input flag) = some (DirectGuard.fallbackState input) := by
  have ht : UInt256.isTrue flag := by rw [hflag]; decide
  have hj := PatternedScan.blockOfS (DirectGuard.opAt 4127 .JUMPI)
    (PatternedScan.pcFactS input 4127 5166 [360, flag] (by norm_num) entryPC4155)
    (PatternedScan.stepS_jumpi_taken input 5166 360 360 flag []
      (by simp) (by norm_num) (by simpa using Challenge.EvmProof.Word.literal_eq_ofNat 360)
      ht guard_fallback_dest)
  exact Challenge.EvmProof.Stepper.runLocatedBlock_append
    guardBytePrefix [DirectGuard.opAt 4127 .JUMPI] _ _ _ (run_guard_byte_prefix input flag) rfl hj

private theorem run_guard_fail (input : ByteArray) (hfit : CalldataFits input)
    (hbad : input.size ≠ 56 ∧ input.size ≠ 120 ∧ input.size ≠ 63) :
    DirectGuard.run guardCheckPath (DirectGuard.guardEntry input) =
      some (DirectGuard.fallbackState input) := by
  have hf : sizeFlag input = UInt256.ofNat 1 :=
    sizeFlag_fail input hfit hbad
  have hjs := Challenge.EvmProof.Stepper.runLocatedBlock_append
    guardJumpPath guardSizePath _ _ _ (run_guard_jump input) rfl (run_guard_size input)
  exact Challenge.EvmProof.Stepper.runLocatedBlock_append
    (guardJumpPath ++ guardSizePath) guardBytePath _ _ _ hjs rfl
    (run_guard_byte_fail input (sizeFlag input) hf)

private theorem run_guard_byte_match (input : ByteArray) :
    DirectGuard.run (guardBytePath ++ guardMatchSuffix)
      (byteEntry input (UInt256.ofNat 0)) = some (guardJumpState input) := by
  have hprefix := run_guard_byte_prefix input (UInt256.ofNat 0)
  have hj := PatternedScan.blockOfS (DirectGuard.opAt 4127 .JUMPI)
    (PatternedScan.pcFactS input 4127 5166 [360, UInt256.ofNat 0] (by norm_num) entryPC4155)
    (PatternedScan.stepS_jumpi_fall input 5166 360 (UInt256.ofNat 0) []
      (by simp) (by norm_num) (by decide))
  have h0 := PatternedScan.blockOfS (DirectGuard.pushAt 4128 0 0)
    (PatternedScan.pcFactS input 4128 5167 [] (by norm_num) entryPC4156)
    (PatternedScan.stepS_push0 input 5167 [] (by simp) (by norm_num))
  have h1 := PatternedScan.blockOfS (DirectGuard.pushAt 4129 1 98)
    (PatternedScan.pcFactS input 4129 5168 [0] (by norm_num) entryPC4157)
    (PatternedScan.stepS_push input 5168 1 98 [0] (by simp) (by decide) (by decide) (by norm_num))
  have h2 := PatternedScan.blockOfS (DirectGuard.opAt 4130 .JUMP)
    (PatternedScan.pcFactS input 4130 5170 [98, 0] (by norm_num) entryPC4158)
    (PatternedScan.stepS_jump input 5170 98 98 [0] (by simp) (by norm_num)
      (by simpa using Challenge.EvmProof.Word.literal_eq_ofNat 98) guard_match_dest)
  have hpj := Challenge.EvmProof.Stepper.runLocatedBlock_append
    guardBytePrefix [DirectGuard.opAt 4127 .JUMPI] _ _ _ hprefix rfl hj
  have h01 := Challenge.EvmProof.Stepper.runLocatedBlock_append
    [DirectGuard.pushAt 4128 0 0] [DirectGuard.pushAt 4129 1 98] _ _ _ h0 rfl h1
  have hs := Challenge.EvmProof.Stepper.runLocatedBlock_append
    [DirectGuard.pushAt 4128 0 0, DirectGuard.pushAt 4129 1 98]
    [DirectGuard.opAt 4130 .JUMP] _ _ _ h01 rfl h2
  exact Challenge.EvmProof.Stepper.runLocatedBlock_append
    guardBytePath guardMatchSuffix _ _ _ hpj rfl hs

private theorem run_guard_match_helper (input : ByteArray) (_hfit : CalldataFits input)
    (hsize : input.size = 56 ∨ input.size = 120 ∨ input.size = 63) :
    DirectGuard.run (guardCheckPath ++ guardMatchSuffix)
      (DirectGuard.guardEntry input) = some (guardJumpState input) := by
  have hs : DirectGuard.run guardSizePath (sizeEntry input) =
      some (byteEntry input (UInt256.ofNat 0)) := by
    simpa only [sizeFlag_hit input hsize] using run_guard_size input
  have hjs := Challenge.EvmProof.Stepper.runLocatedBlock_append
    guardJumpPath guardSizePath _ _ _ (run_guard_jump input) rfl hs
  simpa only [guardCheckPath, List.append_assoc] using
    (Challenge.EvmProof.Stepper.runLocatedBlock_append
      (guardJumpPath ++ guardSizePath) (guardBytePath ++ guardMatchSuffix) _ _ _ hjs rfl
      (run_guard_byte_match input))

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

def gasSteps_fail (input : ByteArray) (hfit : CalldataFits input)
    (hbad : input.size ≠ 56 ∧ input.size ≠ 120 ∧ input.size ≠ 63) :
    GasSteps (DirectGuard.guardEntry input) (DirectGuard.fallbackState input) :=
  sound guardCheckPath (run_guard_fail input hfit hbad)

def gasSteps_match (input : ByteArray) (hfit : CalldataFits input)
    (hsize : input.size = 56 ∨ input.size = 120 ∨ input.size = 63) :
    GasSteps (DirectGuard.guardEntry input) (PatternedScan.patternedEntry input) :=
  (sound (guardCheckPath ++ guardMatchSuffix)
      (run_guard_match_helper input hfit hsize)).trans
    (sound guardMatchTail (run_guard_match_tail input))

def gasSteps_hit (input : ByteArray) (hfit : CalldataFits input)
    (hsize : input.size = 56 ∨ input.size = 120 ∨ input.size = 63) :
    GasSteps (initialState submissionBytecode input 0)
      (PatternedScan.patternedEntry input) := by
  have h1000 : input.size ≠ 1000 := by omega
  have h376 : input.size ≠ 376 := by omega
  have h256 : input.size ≠ 256 := by omega
  exact (Execution.gasSteps_start input).trans
    ((sound DirectGuard.sizePath
        (DirectGuard.run_size_fail input hfit h1000 h376 h256)).trans
      (gasSteps_match input hfit hsize))

def gasSteps_miss (input : ByteArray) (hfit : CalldataFits input)
    (hbad : input.size ≠ 56 ∧ input.size ≠ 120 ∧ input.size ≠ 63)
    (h1000 : input.size ≠ 1000) (h376 : input.size ≠ 376)
    (h256 : input.size ≠ 256) :
    GasSteps (initialState submissionBytecode input 0)
      (DirectGuard.fallbackState input) := by
  exact (Execution.gasSteps_start input).trans
    ((sound DirectGuard.sizePath
        (DirectGuard.run_size_fail input hfit h1000 h376 h256)).trans
      (gasSteps_fail input hfit hbad))

end Challenge.Ripemd160.Submission.Proofs.Bytecode.Patterned128Entry
