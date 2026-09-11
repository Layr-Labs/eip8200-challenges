import Challenge.Ripemd160.Submission.Proofs.Bytecode.DirectGuardSize
import Challenge.Ripemd160.Submission.Proofs.Bytecode.newArtifactByteLength
import Challenge.Ripemd160.Submission.Proofs.Bytecode.ShortPatternEntrySteps

set_option warningAsError true
set_option maxRecDepth 100000
set_option maxHeartbeats 20000000
set_option linter.unusedSimpArgs false

/-! The compact first-byte filter preceding the size check. -/

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.CompactByteGuard

open Challenge.Ripemd160 Challenge.EvmProof EvmSemantics EvmSemantics.EVM

private abbrev Located := DirectGuard.Located

private def sound (path : List Located) {s t : State}
    (h : DirectGuard.run path s = some t)
    (hcode : s.executionEnv.code = Artifact.submissionArtifact.code := by rfl)
    (hfork : s.fork = .Osaka := by rfl)
    (hrun : s.halt = .Running := by rfl)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false := by
        exact deployAddress_not_precompile) : GasSteps s t :=
  Stepper.runLocatedBlock_sound Artifact.submissionArtifact .Osaka
    path hcode hfork h hrun hnp

private theorem pc4119 : Artifact.submissionArtifact.instructionPC 4119 = 5142 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

private theorem pc4120 : Artifact.submissionArtifact.instructionPC 4120 = 5143 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

private theorem pc4121 : Artifact.submissionArtifact.instructionPC 4121 = 5144 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

private theorem pc4122 : Artifact.submissionArtifact.instructionPC 4122 = 5145 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

private theorem pc4123 : Artifact.submissionArtifact.instructionPC 4123 = 5146 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

private theorem pc4124 : Artifact.submissionArtifact.instructionPC 4124 = 5147 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

private theorem pc4125 : Artifact.submissionArtifact.instructionPC 4125 = 5149 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

private theorem pc4126 : Artifact.submissionArtifact.instructionPC 4126 = 5150 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

private theorem pc4127 : Artifact.submissionArtifact.instructionPC 4127 = 5153 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

private theorem fallback_dest :
    Decode.isValidJumpDest submissionBytecode 363 = true :=
  Artifact.submissionArtifact.isValidJumpDest_index 199 (by rfl)

private theorem firstByte_eq_byteAt (input : ByteArray) :
    UInt256.byteAt (UInt256.ofNat 0) (MachineState.readWord input 0) =
      UInt256.ofNat (DirectGuard.firstByte input) := by
  simpa [DirectGuard.firstByte] using
    (Challenge.EvmProof.Bytes.byteAt_zero_readWord input 0)

private def byteFlag (input : ByteArray) : UInt256 :=
  UInt256.xor (UInt256.ofNat 7)
    (UInt256.byteAt (UInt256.ofNat 0) (MachineState.readWord input 0))

private theorem byteFlag_true (input : ByteArray)
    (hbyte : DirectGuard.firstByte input ≠ 7) :
    UInt256.isTrue (byteFlag input) := by
  intro hz
  have hx : byteFlag input = 0 := Word.word_ext hz
  have heq := (KnownInputLogic.wordXor_eq_zero_iff _ _).mp hx
  rw [firstByte_eq_byteAt] at heq
  have hlt : DirectGuard.firstByte input < 2 ^ 256 := by
    unfold DirectGuard.firstByte
    exact Nat.lt_trans (YulSemantics.EVM.byteFrom input.toList 0).toNat_lt
      (by norm_num)
  have heqNat := congrArg UInt256.toNat heq
  rw [Word.word_toNat_ofNat, Word.word_toNat_ofNat,
    Nat.mod_eq_of_lt (by norm_num), Nat.mod_eq_of_lt hlt] at heqNat
  exact hbyte heqNat.symm

private theorem byteFlag_zero (input : ByteArray)
    (hbyte : DirectGuard.firstByte input = 7) :
    byteFlag input = UInt256.ofNat 0 := by
  unfold byteFlag
  rw [firstByte_eq_byteAt, hbyte]
  decide

private def guardPrefix : List Located :=
  [DirectGuard.opAt 4119 .JUMPDEST,
   DirectGuard.pushAt 4120 0 0,
   DirectGuard.opAt 4121 .CALLDATALOAD,
   DirectGuard.pushAt 4122 0 0,
   DirectGuard.opAt 4123 .BYTE,
   DirectGuard.pushAt 4124 1 7,
   DirectGuard.opAt 4125 .XOR,
   DirectGuard.pushAt 4126 2 363]

private def guardFailPath : List Located :=
  guardPrefix ++ [DirectGuard.opAt 4127 .JUMPI]

private def guardPassSuffix : List Located :=
  [DirectGuard.opAt 4127 .JUMPI]

private theorem run_prefix (input : ByteArray) :
    DirectGuard.run guardPrefix (DirectGuard.guardEntry input) =
      some (PatternedScan.stS input 5153 [363, byteFlag input]) := by
  let w := MachineState.readWord input 0
  let b := UInt256.byteAt 0 w
  let z := UInt256.xor 7 b
  let l0 : Located := DirectGuard.opAt 4119 .JUMPDEST
  have h0 := PatternedScan.blockOfS l0
    (PatternedScan.pcFactS input 4119 5142 [] (by norm_num) pc4119)
    (PatternedScan.stepS_jumpdest input 5142 [] (by simp) (by norm_num))
  let l1 : Located := DirectGuard.pushAt 4120 0 0
  have h1 := PatternedScan.blockOfS l1
    (PatternedScan.pcFactS input 4120 5143 [] (by norm_num) pc4120)
    (PatternedScan.stepS_push0 input 5143 [] (by simp) (by norm_num))
  let l2 : Located := DirectGuard.opAt 4121 .CALLDATALOAD
  have h2 := PatternedScan.blockOfS l2
    (PatternedScan.pcFactS input 4121 5144 [0] (by norm_num) pc4121)
    (PatternedScan.stepS_calldataload input 5144 0 [] (by simp) (by norm_num))
  let l3 : Located := DirectGuard.pushAt 4122 0 0
  have h3 := PatternedScan.blockOfS l3
    (PatternedScan.pcFactS input 4122 5145 [w] (by norm_num) pc4122)
    (PatternedScan.stepS_push0 input 5145 [w] (by simp) (by norm_num))
  let l4 : Located := DirectGuard.opAt 4123 .BYTE
  have h4 := PatternedScan.blockOfS l4
    (PatternedScan.pcFactS input 4123 5146 [0, w] (by norm_num) pc4123)
    (PatternedScan.stepS_byte input 5146 0 w [] (by simp) (by norm_num))
  let l5 : Located := DirectGuard.pushAt 4124 1 7
  have h5 := PatternedScan.blockOfS l5
    (PatternedScan.pcFactS input 4124 5147 [b] (by norm_num) pc4124)
    (PatternedScan.stepS_push input 5147 1 7 [b]
      (by simp) (by decide) (by decide) (by norm_num))
  let l6 : Located := DirectGuard.opAt 4125 .XOR
  have h6 := PatternedScan.blockOfS l6
    (PatternedScan.pcFactS input 4125 5149 [7, b] (by norm_num) pc4125)
    (PatternedScan.stepS_xor input 5149 7 b [] (by simp) (by norm_num))
  let l7 : Located := DirectGuard.pushAt 4126 2 363
  have h7 := PatternedScan.blockOfS l7
    (PatternedScan.pcFactS input 4126 5150 [z] (by norm_num) pc4126)
    (PatternedScan.stepS_push input 5150 2 363 [z]
      (by simp) (by decide) (by decide) (by norm_num))
  have h01 := Stepper.runLocatedBlock_append [l0] [l1] _ _ _ h0 rfl h1
  have h23 := Stepper.runLocatedBlock_append [l2] [l3] _ _ _ h2 rfl h3
  have h03 := Stepper.runLocatedBlock_append [l0, l1] [l2, l3] _ _ _ h01 rfl h23
  have h45 := Stepper.runLocatedBlock_append [l4] [l5] _ _ _ h4 rfl h5
  have h67 := Stepper.runLocatedBlock_append [l6] [l7] _ _ _ h6 rfl h7
  have h47 := Stepper.runLocatedBlock_append [l4, l5] [l6, l7] _ _ _ h45 rfl h67
  have h07 := Stepper.runLocatedBlock_append
    [l0, l1, l2, l3] [l4, l5, l6, l7] _ _ _ h03 rfl h47
  have hz : z = byteFlag input := by
    simp only [z, b, w, byteFlag, Word.literal_eq_ofNat]
  rw [hz] at h07
  exact h07

private theorem run_fail (input : ByteArray)
    (hbyte : DirectGuard.firstByte input ≠ 7) :
    DirectGuard.run guardFailPath (DirectGuard.guardEntry input) =
      some (DirectGuard.fallbackState input) := by
  have hj := PatternedScan.blockOfS (DirectGuard.opAt 4127 .JUMPI)
    (PatternedScan.pcFactS input 4127 5153 [363, byteFlag input] (by norm_num) pc4127)
    (PatternedScan.stepS_jumpi_taken input 5153 363 363 (byteFlag input) []
      (by simp) (by norm_num)
      (by simpa using Word.literal_eq_ofNat 363) (byteFlag_true input hbyte) fallback_dest)
  exact Stepper.runLocatedBlock_append guardPrefix [DirectGuard.opAt 4127 .JUMPI]
    _ _ _ (run_prefix input) rfl hj

private theorem run_pass (input : ByteArray)
    (hbyte : DirectGuard.firstByte input = 7) :
    DirectGuard.run (guardPrefix ++ guardPassSuffix) (DirectGuard.guardEntry input) =
      some (DirectGuard.atPC input 5154) := by
  have hp : DirectGuard.run guardPrefix (DirectGuard.guardEntry input) =
      some (PatternedScan.stS input 5153 [363, UInt256.ofNat 0]) := by
    simpa only [byteFlag_zero input hbyte] using run_prefix input
  have hj := PatternedScan.blockOfS (DirectGuard.opAt 4127 .JUMPI)
    (PatternedScan.pcFactS input 4127 5153 [363, UInt256.ofNat 0] (by norm_num) pc4127)
    (PatternedScan.stepS_jumpi_fall input 5153 363 (UInt256.ofNat 0) []
      (by simp) (by norm_num) (by decide))
  exact Stepper.runLocatedBlock_append guardPrefix guardPassSuffix _ _ _ hp rfl hj

/-- A differing first byte branches directly to the RIPEMD fallback. -/
def gasSteps_fail (input : ByteArray) (hbyte : DirectGuard.firstByte input ≠ 7) :
    GasSteps (DirectGuard.guardEntry input) (DirectGuard.fallbackState input) :=
  sound guardFailPath (run_fail input hbyte)

/-- Matching the first byte preserves the empty stack at the size check. -/
def gasSteps_pass (input : ByteArray) (hbyte : DirectGuard.firstByte input = 7) :
    GasSteps (DirectGuard.guardEntry input) (DirectGuard.atPC input 5154) :=
  sound (guardPrefix ++ guardPassSuffix) (run_pass input hbyte)

end Challenge.Ripemd160.Submission.Proofs.Bytecode.CompactByteGuard
