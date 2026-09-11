import Challenge.Ripemd160.Submission.Proofs.Bytecode.OrLengthMask
import Challenge.Ripemd160.Submission.Proofs.Bytecode.CompactByteGuard
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

private theorem pc59 : Artifact.submissionArtifact.instructionPC 59 = 101 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

private theorem pc60 : Artifact.submissionArtifact.instructionPC 60 = 102 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

private theorem pc4128 : Artifact.submissionArtifact.instructionPC 4128 = 5154 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

private theorem pc4129 : Artifact.submissionArtifact.instructionPC 4129 = 5155 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

private theorem pc4130 : Artifact.submissionArtifact.instructionPC 4130 = 5157 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

private theorem pc4131 : Artifact.submissionArtifact.instructionPC 4131 = 5158 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

private theorem pc4132 : Artifact.submissionArtifact.instructionPC 4132 = 5160 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

private theorem pc4133 : Artifact.submissionArtifact.instructionPC 4133 = 5161 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

private theorem pc4134 : Artifact.submissionArtifact.instructionPC 4134 = 5162 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

private theorem pc4135 : Artifact.submissionArtifact.instructionPC 4135 = 5164 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

private theorem pc4136 : Artifact.submissionArtifact.instructionPC 4136 = 5165 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

private theorem pc4137 : Artifact.submissionArtifact.instructionPC 4137 = 5166 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

private theorem pc4138 : Artifact.submissionArtifact.instructionPC 4138 = 5167 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

private theorem pc4139 : Artifact.submissionArtifact.instructionPC 4139 = 5170 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

private theorem pc4140 : Artifact.submissionArtifact.instructionPC 4140 = 5171 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

private theorem pc4141 : Artifact.submissionArtifact.instructionPC 4141 = 5172 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

private theorem pc4142 : Artifact.submissionArtifact.instructionPC 4142 = 5174 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

private def guardSizePrefix : List Located :=
  [DirectGuard.opAt 4128 .CALLDATASIZE,
   DirectGuard.pushAt 4129 1 64,
   DirectGuard.opAt 4130 .OR,
   DirectGuard.pushAt 4131 1 120,
   DirectGuard.opAt 4132 .EQ,
   DirectGuard.opAt 4133 .CALLDATASIZE,
   DirectGuard.pushAt 4134 1 63,
   DirectGuard.opAt 4135 .EQ,
   DirectGuard.opAt 4136 .OR,
   DirectGuard.opAt 4137 .ISZERO,
   DirectGuard.pushAt 4138 2 363]

private def guardFailPath : List Located :=
  guardSizePrefix ++ [DirectGuard.opAt 4139 .JUMPI]

private def guardMatchSuffix : List Located :=
  [DirectGuard.pushAt 4140 0 0,
   DirectGuard.pushAt 4141 1 101,
   DirectGuard.opAt 4142 .JUMP]

private def guardPassPath : List Located := guardFailPath ++ guardMatchSuffix

private def guardMatchTail : List Located :=
  [DirectGuard.opAt 59 .JUMPDEST, DirectGuard.opAt 60 .POP]

private def guardJumpState (input : ByteArray) : State :=
  { DirectGuard.guardEntry input with
    pc := UInt256.ofNat 101
    stack := [UInt256.ofNat 0] }

private def sizeEntry (input : ByteArray) : State := PatternedScan.stS input 5154 []

private theorem guard_fallback_dest :
    Decode.isValidJumpDest submissionBytecode 363 = true :=
  Artifact.submissionArtifact.isValidJumpDest_index 199 (by rfl)

private theorem guard_match_dest :
    Decode.isValidJumpDest submissionBytecode 101 = true :=
  Artifact.submissionArtifact.isValidJumpDest_index 59 (by rfl)

private theorem run_guard_size (input : ByteArray) :
    DirectGuard.run guardSizePrefix (sizeEntry input) =
      some (PatternedScan.stS input 5170 [363, sizeFlag input]) := by
  let x : UInt256 := UInt256.ofNat input.size
  let masked : UInt256 := UInt256.lor 64 x
  let pair : UInt256 := UInt256.lor (UInt256.eq 120 x) (UInt256.eq 56 x)
  let v128 : UInt256 := UInt256.eq 63 x
  let both : UInt256 := UInt256.lor v128 pair
  let flag : UInt256 := UInt256.isZero both
  let l0 : Located := DirectGuard.opAt 4128 .CALLDATASIZE
  have h0 := PatternedScan.blockOfS l0
    (PatternedScan.pcFactS input 4128 5154 [] (by norm_num) pc4128)
    (PatternedScan.stepS_calldatasize input 5154 [] (by simp) (by norm_num))
  let l1 : Located := DirectGuard.pushAt 4129 1 64
  have h1 := PatternedScan.blockOfS l1
    (PatternedScan.pcFactS input 4129 5155 [x] (by norm_num) pc4129)
    (PatternedScan.stepS_push input 5155 1 64 [x] (by simp) (by decide) (by decide) (by norm_num))
  let l2 : Located := DirectGuard.opAt 4130 .OR
  have h2 := PatternedScan.blockOfS l2
    (PatternedScan.pcFactS input 4130 5157 [64, x] (by norm_num) pc4130)
    (PatternedScan.stepS_or input 5157 64 x [] (by simp) (by norm_num))
  let l3 : Located := DirectGuard.pushAt 4131 1 120
  have h3 := PatternedScan.blockOfS l3
    (PatternedScan.pcFactS input 4131 5158 [masked] (by norm_num) pc4131)
    (PatternedScan.stepS_push input 5158 1 120 [masked] (by simp) (by decide) (by decide) (by norm_num))
  let l4 : Located := DirectGuard.opAt 4132 .EQ
  have h4 := PatternedScan.blockOfS l4
    (PatternedScan.pcFactS input 4132 5160 [120, masked] (by norm_num) pc4132)
    (PatternedScan.stepS_eq input 5160 120 masked [] (by simp) (by norm_num))
  have hp : UInt256.eq (120 : UInt256) masked = pair := OrLengthMask.flags x
  rw [hp] at h4
  let l5 : Located := DirectGuard.opAt 4133 .CALLDATASIZE
  have h5 := PatternedScan.blockOfS l5
    (PatternedScan.pcFactS input 4133 5161 [pair] (by norm_num) pc4133)
    (PatternedScan.stepS_calldatasize input 5161 [pair] (by simp) (by norm_num))
  let l6 : Located := DirectGuard.pushAt 4134 1 63
  have h6 := PatternedScan.blockOfS l6
    (PatternedScan.pcFactS input 4134 5162 [x, pair] (by norm_num) pc4134)
    (PatternedScan.stepS_push input 5162 1 63 [x, pair] (by simp) (by decide) (by decide) (by norm_num))
  let l7 : Located := DirectGuard.opAt 4135 .EQ
  have h7 := PatternedScan.blockOfS l7
    (PatternedScan.pcFactS input 4135 5164 [63, x, pair] (by norm_num) pc4135)
    (PatternedScan.stepS_eq input 5164 63 x [pair] (by simp) (by norm_num))
  let l8 : Located := DirectGuard.opAt 4136 .OR
  have h8 := PatternedScan.blockOfS l8
    (PatternedScan.pcFactS input 4136 5165 [v128, pair] (by norm_num) pc4136)
    (PatternedScan.stepS_or input 5165 v128 pair [] (by simp) (by norm_num))
  let l9 : Located := DirectGuard.opAt 4137 .ISZERO
  have h9 := PatternedScan.blockOfS l9
    (PatternedScan.pcFactS input 4137 5166 [both] (by norm_num) pc4137)
    (PatternedScan.stepS_iszero input 5166 both [] (by simp) (by norm_num))
  let l10 : Located := DirectGuard.pushAt 4138 2 363
  have h10 := PatternedScan.blockOfS l10
    (PatternedScan.pcFactS input 4138 5167 [flag] (by norm_num) pc4138)
    (PatternedScan.stepS_push input 5167 2 363 [flag] (by simp) (by decide) (by decide) (by norm_num))
  have h_0_2 := Stepper.runLocatedBlock_append
    [l0] [l1] _ _ _ h0 rfl h1
  have h_3_5 := Stepper.runLocatedBlock_append
    [l3] [l4] _ _ _ h3 rfl h4
  have h_2_5 := Stepper.runLocatedBlock_append
    [l2] [l3, l4] _ _ _ h2 rfl h_3_5
  have h_0_5 := Stepper.runLocatedBlock_append
    [l0, l1] [l2, l3, l4] _ _ _ h_0_2 rfl h_2_5
  have h_6_8 := Stepper.runLocatedBlock_append
    [l6] [l7] _ _ _ h6 rfl h7
  have h_5_8 := Stepper.runLocatedBlock_append
    [l5] [l6, l7] _ _ _ h5 rfl h_6_8
  have h_9_11 := Stepper.runLocatedBlock_append
    [l9] [l10] _ _ _ h9 rfl h10
  have h_8_11 := Stepper.runLocatedBlock_append
    [l8] [l9, l10] _ _ _ h8 rfl h_9_11
  have h_5_11 := Stepper.runLocatedBlock_append
    [l5, l6, l7] [l8, l9, l10] _ _ _ h_5_8 rfl h_8_11
  have h_0_11 := Stepper.runLocatedBlock_append
    [l0, l1, l2, l3, l4] [l5, l6, l7, l8, l9, l10] _ _ _ h_0_5 rfl h_5_11
  have hv : flag = sizeFlag input := by
    simp only [flag, both, pair, v128, x, sizeFlag, Word.literal_eq_ofNat]
  rw [hv] at h_0_11
  exact h_0_11

private theorem run_size_fail (input : ByteArray) (hfit : CalldataFits input)
    (hbad : input.size ≠ 56 ∧ input.size ≠ 120 ∧ input.size ≠ 63) :
    DirectGuard.run guardFailPath (sizeEntry input) =
      some (DirectGuard.fallbackState input) := by
  have hp : DirectGuard.run guardSizePrefix (sizeEntry input) =
      some (PatternedScan.stS input 5170 [363, UInt256.ofNat 1]) := by
    simpa only [sizeFlag_fail input hfit hbad] using run_guard_size input
  have hj := PatternedScan.blockOfS (DirectGuard.opAt 4139 .JUMPI)
    (PatternedScan.pcFactS input 4139 5170 [363, UInt256.ofNat 1] (by norm_num) pc4139)
    (PatternedScan.stepS_jumpi_taken input 5170 363 363 (UInt256.ofNat 1) []
      (by simp) (by norm_num) (by simpa using Word.literal_eq_ofNat 363)
      (by decide) guard_fallback_dest)
  exact Stepper.runLocatedBlock_append guardSizePrefix [DirectGuard.opAt 4139 .JUMPI]
    _ _ _ hp rfl hj

private theorem run_size_match (input : ByteArray)
    (hsize : input.size = 56 ∨ input.size = 120 ∨ input.size = 63) :
    DirectGuard.run guardPassPath (sizeEntry input) = some (guardJumpState input) := by
  have hp : DirectGuard.run guardSizePrefix (sizeEntry input) =
      some (PatternedScan.stS input 5170 [363, UInt256.ofNat 0]) := by
    simpa only [sizeFlag_hit input hsize] using run_guard_size input
  have hj := PatternedScan.blockOfS (DirectGuard.opAt 4139 .JUMPI)
    (PatternedScan.pcFactS input 4139 5170 [363, UInt256.ofNat 0] (by norm_num) pc4139)
    (PatternedScan.stepS_jumpi_fall input 5170 363 (UInt256.ofNat 0) []
      (by simp) (by norm_num) (by decide))
  have h0 := PatternedScan.blockOfS (DirectGuard.pushAt 4140 0 0)
    (PatternedScan.pcFactS input 4140 5171 [] (by norm_num) pc4140)
    (PatternedScan.stepS_push0 input 5171 [] (by simp) (by norm_num))
  have h1 := PatternedScan.blockOfS (DirectGuard.pushAt 4141 1 101)
    (PatternedScan.pcFactS input 4141 5172 [0] (by norm_num) pc4141)
    (PatternedScan.stepS_push input 5172 1 101 [0]
      (by simp) (by decide) (by decide) (by norm_num))
  have h2 := PatternedScan.blockOfS (DirectGuard.opAt 4142 .JUMP)
    (PatternedScan.pcFactS input 4142 5174 [101, 0] (by norm_num) pc4142)
    (PatternedScan.stepS_jump input 5174 101 101 [0]
      (by simp) (by norm_num) (by simpa using Word.literal_eq_ofNat 101) guard_match_dest)
  have h01 := Stepper.runLocatedBlock_append
    [DirectGuard.pushAt 4140 0 0] [DirectGuard.pushAt 4141 1 101] _ _ _ h0 rfl h1
  have h012 := Stepper.runLocatedBlock_append
    [DirectGuard.pushAt 4140 0 0, DirectGuard.pushAt 4141 1 101]
    [DirectGuard.opAt 4142 .JUMP] _ _ _ h01 rfl h2
  have htail := Stepper.runLocatedBlock_append [DirectGuard.opAt 4139 .JUMPI]
    guardMatchSuffix _ _ _ hj rfl h012
  have hend : PatternedScan.stS input 101 [0] = guardJumpState input := by
    simp only [PatternedScan.stS, guardJumpState, DirectGuard.guardEntry,
      DirectGuard.atPC, Word.literal_eq_ofNat]
  have hfull := Stepper.runLocatedBlock_append guardSizePrefix
    ([DirectGuard.opAt 4139 .JUMPI] ++ guardMatchSuffix) _ _ _ hp rfl htail
  rw [hend] at hfull
  simpa only [DirectGuard.run, guardPassPath, guardFailPath, List.append_assoc] using hfull

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

/-- Reject a differing leading byte before evaluating the size test. -/
def gasSteps_fail (input : ByteArray) (hfit : CalldataFits input)
    (hbad : (input.size ≠ 56 ∧ input.size ≠ 120 ∧ input.size ≠ 63) ∨
      DirectGuard.firstByte input ≠ 7) :
    GasSteps (DirectGuard.guardEntry input) (DirectGuard.fallbackState input) := by
  by_cases hb : DirectGuard.firstByte input = 7
  · have hs : input.size ≠ 56 ∧ input.size ≠ 120 ∧ input.size ≠ 63 := by
      rcases hbad with hs | hbad
      · exact hs
      · exact False.elim (hbad hb)
    exact (CompactByteGuard.gasSteps_pass input hb).trans
      (sound guardFailPath (run_size_fail input hfit hs))
  · exact CompactByteGuard.gasSteps_fail input hb

def gasSteps_match (input : ByteArray) (_hfit : CalldataFits input)
    (hsize : input.size = 56 ∨ input.size = 120 ∨ input.size = 63)
    (hbyte : DirectGuard.firstByte input = 7) :
    GasSteps (DirectGuard.guardEntry input) (PatternedScan.patternedEntry input) :=
  (CompactByteGuard.gasSteps_pass input hbyte).trans
    ((sound guardPassPath (run_size_match input hsize)).trans
      (sound guardMatchTail (run_guard_match_tail input)))

def gasSteps_hit (input : ByteArray) (hfit : CalldataFits input)
    (hsize : input.size = 56 ∨ input.size = 120 ∨ input.size = 63) (hbyte : DirectGuard.firstByte input = 7) :
    GasSteps (initialState submissionBytecode input 0)
      (PatternedScan.patternedEntry input) := by
  have h1000 : input.size ≠ 1000 := by omega
  have h376 : input.size ≠ 376 := by omega
  have h256 : input.size ≠ 256 := by omega
  exact (Execution.gasSteps_start input).trans
    ((sound DirectGuard.sizePath
        (DirectGuard.run_size_fail input hfit h1000 h376 h256)).trans
      (gasSteps_match input hfit hsize hbyte))

def gasSteps_miss (input : ByteArray) (hfit : CalldataFits input)
    (hbad : (input.size ≠ 56 ∧ input.size ≠ 120 ∧ input.size ≠ 63) ∨
      DirectGuard.firstByte input ≠ 7)
    (h1000 : input.size ≠ 1000) (h376 : input.size ≠ 376)
    (h256 : input.size ≠ 256) :
    GasSteps (initialState submissionBytecode input 0)
      (DirectGuard.fallbackState input) := by
  exact (Execution.gasSteps_start input).trans
    ((sound DirectGuard.sizePath
        (DirectGuard.run_size_fail input hfit h1000 h376 h256)).trans
      (gasSteps_fail input hfit hbad))

end Challenge.Ripemd160.Submission.Proofs.Bytecode.Patterned128Entry
