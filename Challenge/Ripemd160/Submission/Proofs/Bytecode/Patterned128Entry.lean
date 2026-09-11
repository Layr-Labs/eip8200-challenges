import Challenge.Ripemd160.Submission.Proofs.Bytecode.DirectGuardSize
import Challenge.Ripemd160.Submission.Proofs.Bytecode.PatternedScan
import Challenge.Ripemd160.Submission.Proofs.Bytecode.newArtifactByteLength
import Challenge.Ripemd160.Submission.Proofs.Bytecode.ShortPatternEntryLogic
import Challenge.Ripemd160.Submission.Proofs.Bytecode.ShortPatternEntrySteps

set_option warningAsError true
set_option maxRecDepth 100000
set_option maxHeartbeats 20000000
set_option linter.unusedSimpArgs false

/-! The appended 56/120/63-byte bitmap guard and its bridge into the patterned
scan.  The guard tests `(bitmap >>> (size - 56)) &&& 1` where the bitmap has
bits 0, 7 and 64 set, so membership is exact for `{56, 63, 120}`. -/

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

@[simp] private theorem entryPC4119 : Artifact.submissionArtifact.instructionPC 4119 = 5142 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

@[simp] private theorem entryPC4120 : Artifact.submissionArtifact.instructionPC 4120 = 5143 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

@[simp] private theorem entryPC4121 : Artifact.submissionArtifact.instructionPC 4121 = 5156 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

@[simp] private theorem entryPC4122 : Artifact.submissionArtifact.instructionPC 4122 = 5158 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

@[simp] private theorem entryPC4123 : Artifact.submissionArtifact.instructionPC 4123 = 5159 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

@[simp] private theorem entryPC4124 : Artifact.submissionArtifact.instructionPC 4124 = 5160 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

@[simp] private theorem entryPC4125 : Artifact.submissionArtifact.instructionPC 4125 = 5161 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

@[simp] private theorem entryPC4126 : Artifact.submissionArtifact.instructionPC 4126 = 5163 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

@[simp] private theorem entryPC4127 : Artifact.submissionArtifact.instructionPC 4127 = 5164 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

@[simp] private theorem entryPC4128 : Artifact.submissionArtifact.instructionPC 4128 = 5165 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

@[simp] private theorem entryPC4129 : Artifact.submissionArtifact.instructionPC 4129 = 5168 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

@[simp] private theorem entryPC4130 : Artifact.submissionArtifact.instructionPC 4130 = 5169 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

@[simp] private theorem entryPC4131 : Artifact.submissionArtifact.instructionPC 4131 = 5170 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

@[simp] private theorem entryPC4132 : Artifact.submissionArtifact.instructionPC 4132 = 5172 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

private def guardSizePath : List Located :=
  [DirectGuard.opAt 4119 .JUMPDEST,
   DirectGuard.pushAt 4120 12 18446744073709551745,
   DirectGuard.pushAt 4121 1 56,
   DirectGuard.opAt 4122 .CALLDATASIZE,
   DirectGuard.opAt 4123 .SUB,
   DirectGuard.opAt 4124 .SHR,
   DirectGuard.pushAt 4125 1 1,
   DirectGuard.opAt 4126 .AND,
   DirectGuard.opAt 4127 .ISZERO]

private def guardJumpPath : List Located :=
  [DirectGuard.pushAt 4128 2 363, DirectGuard.opAt 4129 .JUMPI]

private def guardCheckPath : List Located := guardSizePath ++ guardJumpPath

private def guardMatchSuffix : List Located :=
  [DirectGuard.pushAt 4130 0 0,
   DirectGuard.pushAt 4131 1 101,
   DirectGuard.opAt 4132 .JUMP]

private def guardMatchTail : List Located :=
  [DirectGuard.opAt 59 .JUMPDEST, DirectGuard.opAt 60 .POP]

private def guardJumpState (input : ByteArray) : State :=
  { DirectGuard.guardEntry input with
    pc := UInt256.ofNat 101
    stack := [UInt256.ofNat 0] }

private theorem guard_fallback_dest :
    Decode.isValidJumpDest submissionBytecode 363 = true :=
  Artifact.submissionArtifact.isValidJumpDest_index 199 (by rfl)

private theorem guard_match_dest :
    Decode.isValidJumpDest submissionBytecode 101 = true :=
  Artifact.submissionArtifact.isValidJumpDest_index 59 (by rfl)

private def sizeEntry (input : ByteArray) : State := PatternedScan.stS input 5142 []
private def flagState (input : ByteArray) : State :=
  PatternedScan.stS input 5165 [sizeFlag input]

private theorem run_guard_size (input : ByteArray) :
    DirectGuard.run guardSizePath (sizeEntry input) = some (flagState input) := by
  let x : UInt256 := UInt256.ofNat input.size
  let bm : UInt256 := UInt256.ofNat 18446744073709551745
  let s : UInt256 := UInt256.sub x (UInt256.ofNat 56)
  let sh : UInt256 := UInt256.shiftRight bm s
  let m : UInt256 := UInt256.land (UInt256.ofNat 1) sh
  let l0 : Located := DirectGuard.opAt 4119 .JUMPDEST
  have h0 := PatternedScan.blockOfS l0
    (PatternedScan.pcFactS input 4119 5142 [] (by norm_num)
      entryPC4119)
    (PatternedScan.stepS_jumpdest input 5142 [] (by simp) (by norm_num))
  let l1 : Located := DirectGuard.pushAt 4120 12 18446744073709551745
  have h1 := PatternedScan.blockOfS l1
    (PatternedScan.pcFactS input 4120 5143 [] (by norm_num)
      entryPC4120)
    (PatternedScan.stepS_push input 5143 12 18446744073709551745 []
      (by simp) (by decide) (by decide) (by norm_num))
  let l2 : Located := DirectGuard.pushAt 4121 1 56
  have h2 := PatternedScan.blockOfS l2
    (PatternedScan.pcFactS input 4121 5156 [bm] (by norm_num)
      entryPC4121)
    (PatternedScan.stepS_push input 5156 1 56 [bm]
      (by simp) (by decide) (by decide) (by norm_num))
  let l3 : Located := DirectGuard.opAt 4122 .CALLDATASIZE
  have h3 := PatternedScan.blockOfS l3
    (PatternedScan.pcFactS input 4122 5158 [56, bm] (by norm_num)
      entryPC4122)
    (PatternedScan.stepS_calldatasize input 5158 [56, bm] (by simp) (by norm_num))
  let l4 : Located := DirectGuard.opAt 4123 .SUB
  have h4 := PatternedScan.blockOfS l4
    (PatternedScan.pcFactS input 4123 5159 [x, 56, bm] (by norm_num)
      entryPC4123)
    (PatternedScan.stepS_sub input 5159 x 56 [bm] (by simp) (by norm_num))
  let l5 : Located := DirectGuard.opAt 4124 .SHR
  have h5 := PatternedScan.blockOfS l5
    (PatternedScan.pcFactS input 4124 5160 [s, bm] (by norm_num)
      entryPC4124)
    (PatternedScan.stepS_shr input 5160 s bm [] (by simp) (by norm_num))
  let l6 : Located := DirectGuard.pushAt 4125 1 1
  have h6 := PatternedScan.blockOfS l6
    (PatternedScan.pcFactS input 4125 5161 [sh] (by norm_num)
      entryPC4125)
    (PatternedScan.stepS_push input 5161 1 1 [sh]
      (by simp) (by decide) (by decide) (by norm_num))
  let l7 : Located := DirectGuard.opAt 4126 .AND
  have h7 := PatternedScan.blockOfS l7
    (PatternedScan.pcFactS input 4126 5163 [1, sh] (by norm_num)
      entryPC4126)
    (PatternedScan.stepS_and input 5163 1 sh [] (by simp) (by norm_num))
  let l8 : Located := DirectGuard.opAt 4127 .ISZERO
  have h8 := PatternedScan.blockOfS l8
    (PatternedScan.pcFactS input 4127 5164 [m] (by norm_num)
      entryPC4127)
    (PatternedScan.stepS_iszero input 5164 m [] (by simp) (by norm_num))
  have h_1_2 := Stepper.runLocatedBlock_append
    [l1] [l2] _ _ _ h1 rfl h2
  have h_0_2 := Stepper.runLocatedBlock_append
    [l0] [l1, l2] _ _ _ h0 rfl h_1_2
  have h_3_4 := Stepper.runLocatedBlock_append
    [l3] [l4] _ _ _ h3 rfl h4
  have h_0_4 := Stepper.runLocatedBlock_append
    [l0, l1, l2] [l3, l4] _ _ _ h_0_2 rfl h_3_4
  have h_5_6 := Stepper.runLocatedBlock_append
    [l5] [l6] _ _ _ h5 rfl h6
  have h_7_8 := Stepper.runLocatedBlock_append
    [l7] [l8] _ _ _ h7 rfl h8
  have h_5_8 := Stepper.runLocatedBlock_append
    [l5, l6] [l7, l8] _ _ _ h_5_6 rfl h_7_8
  have h_0_8 := Stepper.runLocatedBlock_append
    [l0, l1, l2, l3, l4] [l5, l6, l7, l8] _ _ _ h_0_4 rfl h_5_8
  have hv : UInt256.isZero m = sizeFlag input := by
    simp only [m, sh, s, bm, x, sizeFlag, sizeBitmap, Word.literal_eq_ofNat]
  rw [hv] at h_0_8
  exact h_0_8

private theorem run_guard_fail (input : ByteArray)
    (hflag : sizeFlag input = UInt256.ofNat 1) :
    DirectGuard.run guardCheckPath (sizeEntry input) =
      some (DirectGuard.fallbackState input) := by
  have ht : UInt256.isTrue (sizeFlag input) := by
    rw [hflag]
    decide
  have hpush := PatternedScan.blockOfS (DirectGuard.pushAt 4128 2 363)
    (PatternedScan.pcFactS input 4128 5165 [sizeFlag input] (by norm_num)
      entryPC4128)
    (PatternedScan.stepS_push input 5165 2 363 [sizeFlag input]
      (by simp) (by decide) (by decide) (by norm_num))
  have hj := PatternedScan.blockOfS (DirectGuard.opAt 4129 .JUMPI)
    (PatternedScan.pcFactS input 4129 5168 [363, sizeFlag input] (by norm_num)
      entryPC4129)
    (PatternedScan.stepS_jumpi_taken input 5168 363 363 (sizeFlag input) []
      (by simp) (by norm_num) (by simpa using Challenge.EvmProof.Word.literal_eq_ofNat 363)
      ht guard_fallback_dest)
  have hjump := Challenge.EvmProof.Stepper.runLocatedBlock_append
    [DirectGuard.pushAt 4128 2 363] [DirectGuard.opAt 4129 .JUMPI] _ _ _
    hpush rfl hj
  exact Challenge.EvmProof.Stepper.runLocatedBlock_append
    guardSizePath guardJumpPath _ _ _ (run_guard_size input) rfl hjump

private theorem run_guard_match (input : ByteArray)
    (hflag : sizeFlag input = UInt256.ofNat 0) :
    DirectGuard.run (guardCheckPath ++ guardMatchSuffix)
      (sizeEntry input) = some (guardJumpState input) := by
  have hpush := PatternedScan.blockOfS (DirectGuard.pushAt 4128 2 363)
    (PatternedScan.pcFactS input 4128 5165 [sizeFlag input] (by norm_num)
      entryPC4128)
    (PatternedScan.stepS_push input 5165 2 363 [sizeFlag input]
      (by simp) (by decide) (by decide) (by norm_num))
  have hj := PatternedScan.blockOfS (DirectGuard.opAt 4129 .JUMPI)
    (PatternedScan.pcFactS input 4129 5168 [363, sizeFlag input] (by norm_num)
      entryPC4129)
    (PatternedScan.stepS_jumpi_fall input 5168 363 (sizeFlag input) []
      (by simp) (by norm_num) (by rw [hflag]; decide))
  have hjump := Challenge.EvmProof.Stepper.runLocatedBlock_append
    [DirectGuard.pushAt 4128 2 363] [DirectGuard.opAt 4129 .JUMPI] _ _ _
    hpush rfl hj
  have hcheck := Challenge.EvmProof.Stepper.runLocatedBlock_append
    guardSizePath guardJumpPath _ _ _ (run_guard_size input) rfl hjump
  have h0 := PatternedScan.blockOfS (DirectGuard.pushAt 4130 0 0)
    (PatternedScan.pcFactS input 4130 5169 [] (by norm_num) entryPC4130)
    (PatternedScan.stepS_push0 input 5169 [] (by simp) (by norm_num))
  have h1 := PatternedScan.blockOfS (DirectGuard.pushAt 4131 1 101)
    (PatternedScan.pcFactS input 4131 5170 [0] (by norm_num) entryPC4131)
    (PatternedScan.stepS_push input 5170 1 101 [0]
      (by simp) (by decide) (by decide) (by norm_num))
  have h2 := PatternedScan.blockOfS (DirectGuard.opAt 4132 .JUMP)
    (PatternedScan.pcFactS input 4132 5172 [101, 0] (by norm_num) entryPC4132)
    (PatternedScan.stepS_jump input 5172 101 101 [0] (by simp) (by norm_num)
      (by simpa using Challenge.EvmProof.Word.literal_eq_ofNat 101) guard_match_dest)
  have h01 := Challenge.EvmProof.Stepper.runLocatedBlock_append
    [DirectGuard.pushAt 4130 0 0] [DirectGuard.pushAt 4131 1 101] _ _ _ h0 rfl h1
  have hs := Challenge.EvmProof.Stepper.runLocatedBlock_append
    [DirectGuard.pushAt 4130 0 0, DirectGuard.pushAt 4131 1 101]
    [DirectGuard.opAt 4132 .JUMP] _ _ _ h01 rfl h2
  exact Challenge.EvmProof.Stepper.runLocatedBlock_append
    guardCheckPath guardMatchSuffix _ _ _ hcheck rfl hs

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
  sound guardCheckPath
    (run_guard_fail input (sizeFlag_fail input hfit hbad))

def gasSteps_match (input : ByteArray) (hfit : CalldataFits input)
    (hsize : input.size = 56 ∨ input.size = 120 ∨ input.size = 63) :
    GasSteps (DirectGuard.guardEntry input) (PatternedScan.patternedEntry input) :=
  (sound (guardCheckPath ++ guardMatchSuffix)
      (run_guard_match input (sizeFlag_hit input hsize))).trans
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
