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

@[simp] private theorem entryPC61 : Artifact.submissionArtifact.instructionPC 59 = 98 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

@[simp] private theorem entryPC62 : Artifact.submissionArtifact.instructionPC 60 = 99 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

private theorem firstByte_eq_byteAt (input : ByteArray) :
    UInt256.byteAt (UInt256.ofNat 0) (MachineState.readWord input 0) =
      UInt256.ofNat (DirectGuard.firstByte input) := by
  simpa [DirectGuard.firstByte] using
    (Challenge.EvmProof.Bytes.byteAt_zero_readWord input 0)

private theorem guard_byte_eq_zero (input : ByteArray)
    (hbyte : DirectGuard.firstByte input ≠ 7) :
    UInt256.eq (UInt256.ofNat 7)
        (UInt256.byteAt (UInt256.ofNat 0) (MachineState.readWord input 0)) =
      UInt256.ofNat 0 := by
  rw [firstByte_eq_byteAt]
  unfold UInt256.eq
  have hlt : DirectGuard.firstByte input < 2 ^ 256 := by
    unfold DirectGuard.firstByte
    exact Nat.lt_trans (YulSemantics.EVM.byteFrom input.toList 0).toNat_lt
      (by norm_num)
  rw [Challenge.EvmProof.Word.word_toNat_ofNat,
    Challenge.EvmProof.Word.word_toNat_ofNat,
    Nat.mod_eq_of_lt (by norm_num), Nat.mod_eq_of_lt hlt]
  simp [Ne.symm hbyte]

private def byteValue (input : ByteArray) : UInt256 :=
  UInt256.xor (UInt256.ofNat 7)
    (UInt256.byteAt (UInt256.ofNat 0) (MachineState.readWord input 0))

private theorem byteValue_zero (input : ByteArray) (hbyte : DirectGuard.firstByte input = 7) :
    byteValue input = UInt256.ofNat 0 := by
  rw [byteValue, firstByte_eq_byteAt, hbyte]
  decide

private theorem byteValue_true (input : ByteArray) (hbyte : DirectGuard.firstByte input ≠ 7) :
    UInt256.isTrue (byteValue input) := by
  intro hz
  have hx : UInt256.xor (UInt256.ofNat 7)
      (UInt256.byteAt (UInt256.ofNat 0) (MachineState.readWord input 0)) = 0 :=
    Word.word_ext hz
  have heq := (KnownInputLogic.wordXor_eq_zero_iff _ _).mp hx
  have hbad := guard_byte_eq_zero input hbyte
  rw [← heq] at hbad
  exact (by decide : UInt256.eq (UInt256.ofNat 7) (UInt256.ofNat 7) ≠ UInt256.ofNat 0) hbad

private theorem guard_fallback_dest : Decode.isValidJumpDest submissionBytecode 360 = true :=
  Artifact.submissionArtifact.isValidJumpDest_index 199 (by rfl)

private theorem guard_match_dest : Decode.isValidJumpDest submissionBytecode 98 = true :=
  Artifact.submissionArtifact.isValidJumpDest_index 59 (by rfl)

private def guardJumpState (input : ByteArray) : State :=
  { DirectGuard.guardEntry input with pc := UInt256.ofNat 98, stack := [UInt256.ofNat 0] }

private def bytePrefix : List Located :=
  [DirectGuard.opAt 4081 .JUMPDEST,
   DirectGuard.pushAt 4082 0 0,
   DirectGuard.opAt 4083 .CALLDATALOAD,
   DirectGuard.pushAt 4084 0 0,
   DirectGuard.opAt 4085 .BYTE,
   DirectGuard.pushAt 4086 1 7,
   DirectGuard.opAt 4087 .XOR,
   DirectGuard.pushAt 4088 2 360]

private def sizePrefix : List Located :=
  [DirectGuard.pushAt 4090 17 341611594916723379400914076344069914624,
   DirectGuard.opAt 4091 .CALLDATASIZE,
   DirectGuard.opAt 4092 .SHR,
   DirectGuard.pushAt 4093 1 1,
   DirectGuard.opAt 4094 .AND,
   DirectGuard.opAt 4095 .ISZERO,
   DirectGuard.pushAt 4096 2 360]

private def matchSuffix : List Located :=
  [DirectGuard.pushAt 4098 0 0,
   DirectGuard.pushAt 4099 1 98,
   DirectGuard.opAt 4100 .JUMP]

private def guardMatchTail : List Located :=
  [DirectGuard.opAt 59 .JUMPDEST,
   DirectGuard.opAt 60 .POP]

private theorem run_byte_prefix (input : ByteArray) :
    DirectGuard.run bytePrefix (PatternedScan.stS input 5035 []) =
      some (PatternedScan.stS input 5046 [360, byteValue input]) := by
  let w := MachineState.readWord input 0
  let b := UInt256.byteAt 0 w
  let v := UInt256.xor 7 b
  let l0 : Located := DirectGuard.opAt 4081 .JUMPDEST
  have h0 := PatternedScan.blockOfS l0
    (PatternedScan.pcFactS input 4081 5035 [] (by norm_num) (by
      rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide))
    (PatternedScan.stepS_jumpdest input 5035 [] (by simp) (by norm_num))
  let l1 : Located := DirectGuard.pushAt 4082 0 0
  have h1 := PatternedScan.blockOfS l1
    (PatternedScan.pcFactS input 4082 5036 [] (by norm_num) (by
      rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide))
    (PatternedScan.stepS_push0 input 5036 [] (by simp) (by norm_num))
  let l2 : Located := DirectGuard.opAt 4083 .CALLDATALOAD
  have h2 := PatternedScan.blockOfS l2
    (PatternedScan.pcFactS input 4083 5037 [0] (by norm_num) (by
      rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide))
    (PatternedScan.stepS_calldataload input 5037 0 [] (by simp) (by norm_num))
  let l3 : Located := DirectGuard.pushAt 4084 0 0
  have h3 := PatternedScan.blockOfS l3
    (PatternedScan.pcFactS input 4084 5038 [w] (by norm_num) (by
      rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide))
    (PatternedScan.stepS_push0 input 5038 [w] (by simp) (by norm_num))
  let l4 : Located := DirectGuard.opAt 4085 .BYTE
  have h4 := PatternedScan.blockOfS l4
    (PatternedScan.pcFactS input 4085 5039 [0, w] (by norm_num) (by
      rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide))
    (PatternedScan.stepS_byte input 5039 0 w [] (by simp) (by norm_num))
  let l5 : Located := DirectGuard.pushAt 4086 1 7
  have h5 := PatternedScan.blockOfS l5
    (PatternedScan.pcFactS input 4086 5040 [b] (by norm_num) (by
      rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide))
    (PatternedScan.stepS_push input 5040 1 7 [b] (by simp) (by decide) (by decide) (by norm_num))
  let l6 : Located := DirectGuard.opAt 4087 .XOR
  have h6 := PatternedScan.blockOfS l6
    (PatternedScan.pcFactS input 4087 5042 [7, b] (by norm_num) (by
      rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide))
    (PatternedScan.stepS_xor input 5042 7 b [] (by simp) (by norm_num))
  let l7 : Located := DirectGuard.pushAt 4088 2 360
  have h7 := PatternedScan.blockOfS l7
    (PatternedScan.pcFactS input 4088 5043 [v] (by norm_num) (by
      rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide))
    (PatternedScan.stepS_push input 5043 2 360 [v] (by simp) (by decide) (by decide) (by norm_num))
  have hseq1 := Stepper.runLocatedBlock_append [l0] [l1] _ _ _ h0 rfl h1
  have hseq2 := Stepper.runLocatedBlock_append [l0, l1] [l2] _ _ _ hseq1 rfl h2
  have hseq3 := Stepper.runLocatedBlock_append [l0, l1, l2] [l3] _ _ _ hseq2 rfl h3
  have hseq4 := Stepper.runLocatedBlock_append [l0, l1, l2, l3] [l4] _ _ _ hseq3 rfl h4
  have hseq5 := Stepper.runLocatedBlock_append [l0, l1, l2, l3, l4] [l5] _ _ _ hseq4 rfl h5
  have hseq6 := Stepper.runLocatedBlock_append [l0, l1, l2, l3, l4, l5] [l6] _ _ _ hseq5 rfl h6
  have hseq7 := Stepper.runLocatedBlock_append [l0, l1, l2, l3, l4, l5, l6] [l7] _ _ _ hseq6 rfl h7
  have hv : v = byteValue input := by
    simp only [v, b, w, byteValue, Word.literal_eq_ofNat]
  rw [hv] at hseq7
  exact hseq7

private theorem run_size_prefix (input : ByteArray) :
    DirectGuard.run sizePrefix (PatternedScan.stS input 5047 []) =
      some (PatternedScan.stS input 5074 [360, sizeFlag input]) := by
  let m : UInt256 := 341611594916723379400914076344069914624
  let x : UInt256 := UInt256.ofNat input.size
  let shifted : UInt256 := UInt256.shiftRight m x
  let bit : UInt256 := UInt256.land 1 shifted
  let f : UInt256 := UInt256.isZero bit
  let l0 : Located := DirectGuard.pushAt 4090 17 341611594916723379400914076344069914624
  have h0 := PatternedScan.blockOfS l0
    (PatternedScan.pcFactS input 4090 5047 [] (by norm_num) (by
      rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide))
    (PatternedScan.stepS_push input 5047 17 341611594916723379400914076344069914624 [] (by simp) (by decide) (by decide) (by norm_num))
  let l1 : Located := DirectGuard.opAt 4091 .CALLDATASIZE
  have h1 := PatternedScan.blockOfS l1
    (PatternedScan.pcFactS input 4091 5065 [m] (by norm_num) (by
      rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide))
    (PatternedScan.stepS_calldatasize input 5065 [m] (by simp) (by norm_num))
  let l2 : Located := DirectGuard.opAt 4092 .SHR
  have h2 := PatternedScan.blockOfS l2
    (PatternedScan.pcFactS input 4092 5066 [x, m] (by norm_num) (by
      rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide))
    (PatternedScan.stepS_shr input 5066 x m [] (by simp) (by norm_num))
  let l3 : Located := DirectGuard.pushAt 4093 1 1
  have h3 := PatternedScan.blockOfS l3
    (PatternedScan.pcFactS input 4093 5067 [shifted] (by norm_num) (by
      rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide))
    (PatternedScan.stepS_push input 5067 1 1 [shifted] (by simp) (by decide) (by decide) (by norm_num))
  let l4 : Located := DirectGuard.opAt 4094 .AND
  have h4 := PatternedScan.blockOfS l4
    (PatternedScan.pcFactS input 4094 5069 [1, shifted] (by norm_num) (by
      rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide))
    (PatternedScan.stepS_and input 5069 1 shifted [] (by simp) (by norm_num))
  let l5 : Located := DirectGuard.opAt 4095 .ISZERO
  have h5 := PatternedScan.blockOfS l5
    (PatternedScan.pcFactS input 4095 5070 [bit] (by norm_num) (by
      rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide))
    (PatternedScan.stepS_iszero input 5070 bit [] (by simp) (by norm_num))
  let l6 : Located := DirectGuard.pushAt 4096 2 360
  have h6 := PatternedScan.blockOfS l6
    (PatternedScan.pcFactS input 4096 5071 [f] (by norm_num) (by
      rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide))
    (PatternedScan.stepS_push input 5071 2 360 [f] (by simp) (by decide) (by decide) (by norm_num))
  have hseq1 := Stepper.runLocatedBlock_append [l0] [l1] _ _ _ h0 rfl h1
  have hseq2 := Stepper.runLocatedBlock_append [l0, l1] [l2] _ _ _ hseq1 rfl h2
  have hseq3 := Stepper.runLocatedBlock_append [l0, l1, l2] [l3] _ _ _ hseq2 rfl h3
  have hseq4 := Stepper.runLocatedBlock_append [l0, l1, l2, l3] [l4] _ _ _ hseq3 rfl h4
  have hseq5 := Stepper.runLocatedBlock_append [l0, l1, l2, l3, l4] [l5] _ _ _ hseq4 rfl h5
  have hseq6 := Stepper.runLocatedBlock_append [l0, l1, l2, l3, l4, l5] [l6] _ _ _ hseq5 rfl h6
  have hf : f = sizeFlag input := by
    have h := SizeLookupFlag.flag x
    rw [SizeLookupFlag.mask_literal] at h
    simpa only [f, bit, shifted, m, x, sizeFlag, Word.literal_eq_ofNat] using h
  rw [hf] at hseq6
  exact hseq6

private theorem run_byte_fail (input : ByteArray)
    (hbyte : DirectGuard.firstByte input ≠ 7) :
    DirectGuard.run [DirectGuard.opAt 4089 .JUMPI] (PatternedScan.stS input 5046 [360, byteValue input]) =
      some (DirectGuard.fallbackState input) := by
  exact PatternedScan.blockOfS (DirectGuard.opAt 4089 .JUMPI)
    (PatternedScan.pcFactS input 4089 5046 [360, byteValue input] (by norm_num) (by
      rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide))
    (PatternedScan.stepS_jumpi_taken input 5046 360 360 (byteValue input) []
      (by simp) (by norm_num) (by simpa using Word.literal_eq_ofNat 360) (byteValue_true input hbyte) guard_fallback_dest)

private theorem run_byte_fall (input : ByteArray) :
    DirectGuard.run [DirectGuard.opAt 4089 .JUMPI] (PatternedScan.stS input 5046 [360, UInt256.ofNat 0]) =
      some (PatternedScan.stS input 5047 []) := by
  exact PatternedScan.blockOfS (DirectGuard.opAt 4089 .JUMPI)
    (PatternedScan.pcFactS input 4089 5046 [360, UInt256.ofNat 0] (by norm_num) (by
      rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide))
    (PatternedScan.stepS_jumpi_fall input 5046 360 (UInt256.ofNat 0) []
      (by simp) (by norm_num) (by decide))

private theorem run_size_fail (input : ByteArray) :
    DirectGuard.run [DirectGuard.opAt 4097 .JUMPI] (PatternedScan.stS input 5074 [360, UInt256.ofNat 1]) =
      some (DirectGuard.fallbackState input) := by
  exact PatternedScan.blockOfS (DirectGuard.opAt 4097 .JUMPI)
    (PatternedScan.pcFactS input 4097 5074 [360, UInt256.ofNat 1] (by norm_num) (by
      rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide))
    (PatternedScan.stepS_jumpi_taken input 5074 360 360 (UInt256.ofNat 1) []
      (by simp) (by norm_num) (by simpa using Word.literal_eq_ofNat 360) (by decide) guard_fallback_dest)

private theorem run_size_fall (input : ByteArray) :
    DirectGuard.run [DirectGuard.opAt 4097 .JUMPI] (PatternedScan.stS input 5074 [360, UInt256.ofNat 0]) =
      some (PatternedScan.stS input 5075 []) := by
  exact PatternedScan.blockOfS (DirectGuard.opAt 4097 .JUMPI)
    (PatternedScan.pcFactS input 4097 5074 [360, UInt256.ofNat 0] (by norm_num) (by
      rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide))
    (PatternedScan.stepS_jumpi_fall input 5074 360 (UInt256.ofNat 0) []
      (by simp) (by norm_num) (by decide))

private theorem run_match_suffix (input : ByteArray) :
    DirectGuard.run matchSuffix (PatternedScan.stS input 5075 []) =
      some (PatternedScan.stS input 98 [UInt256.ofNat 0]) := by
  let l0 : Located := DirectGuard.pushAt 4098 0 0
  have h0 := PatternedScan.blockOfS l0
    (PatternedScan.pcFactS input 4098 5075 [] (by norm_num) (by
      rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide))
    (PatternedScan.stepS_push0 input 5075 [] (by simp) (by norm_num))
  let l1 : Located := DirectGuard.pushAt 4099 1 98
  have h1 := PatternedScan.blockOfS l1
    (PatternedScan.pcFactS input 4099 5076 [0] (by norm_num) (by
      rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide))
    (PatternedScan.stepS_push input 5076 1 98 [0] (by simp) (by decide) (by decide) (by norm_num))
  let l2 : Located := DirectGuard.opAt 4100 .JUMP
  have h2 := PatternedScan.blockOfS l2
    (PatternedScan.pcFactS input 4100 5078 [98, 0] (by norm_num) (by
      rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide))
    (PatternedScan.stepS_jump input 5078 98 98 [0] (by simp) (by norm_num) (by simpa using Word.literal_eq_ofNat 98) guard_match_dest)
  have hseq1 := Stepper.runLocatedBlock_append [l0] [l1] _ _ _ h0 rfl h1
  have hseq2 := Stepper.runLocatedBlock_append [l0, l1] [l2] _ _ _ hseq1 rfl h2
  exact hseq2

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

private def gasSteps_byte_match (input : ByteArray)
    (hbyte : DirectGuard.firstByte input = 7) :
    GasSteps (DirectGuard.guardEntry input) (PatternedScan.stS input 5047 []) := by
  have hp := run_byte_prefix input
  rw [byteValue_zero input hbyte] at hp
  exact (sound bytePrefix hp).trans (sound _ (run_byte_fall input))

private def gasSteps_byte_fail (input : ByteArray)
    (hbyte : DirectGuard.firstByte input ≠ 7) :
    GasSteps (DirectGuard.guardEntry input) (DirectGuard.fallbackState input) :=
  (sound bytePrefix (run_byte_prefix input)).trans (sound _ (run_byte_fail input hbyte))

private def gasSteps_size_fail (input : ByteArray) (hfit : CalldataFits input)
    (hbad : input.size ≠ 56 ∧ input.size ≠ 120 ∧ input.size ≠ 63 ∧ input.size ≠ 64 ∧ input.size ≠ 65 ∧ input.size ≠ 128) :
    GasSteps (PatternedScan.stS input 5047 []) (DirectGuard.fallbackState input) := by
  have hp := run_size_prefix input
  rw [sizeFlag_fail input hfit hbad] at hp
  exact (sound sizePrefix hp).trans (sound _ (run_size_fail input))

private def gasSteps_size_match (input : ByteArray) (hsize : input.size = 56 ∨ input.size = 120 ∨ input.size = 63 ∨ input.size = 64 ∨ input.size = 65 ∨ input.size = 128) :
    GasSteps (PatternedScan.stS input 5047 []) (PatternedScan.patternedEntry input) := by
  have hp := run_size_prefix input
  rw [sizeFlag_hit input hsize] at hp
  exact (sound sizePrefix hp).trans ((sound _ (run_size_fall input)).trans
    ((sound matchSuffix (run_match_suffix input)).trans (sound guardMatchTail (run_guard_match_tail input))))

def gasSteps_fail (input : ByteArray) (hfit : CalldataFits input)
    (hbad : (input.size ≠ 56 ∧ input.size ≠ 120 ∧ input.size ≠ 63 ∧ input.size ≠ 64 ∧ input.size ≠ 65 ∧ input.size ≠ 128) ∨ DirectGuard.firstByte input ≠ 7) :
    GasSteps (DirectGuard.guardEntry input) (DirectGuard.fallbackState input) := by
  by_cases hbyte : DirectGuard.firstByte input = 7
  · have hs : input.size ≠ 56 ∧ input.size ≠ 120 ∧ input.size ≠ 63 ∧ input.size ≠ 64 ∧ input.size ≠ 65 ∧ input.size ≠ 128 := by
      rcases hbad with hs | hb
      · exact hs
      · exact False.elim (hb hbyte)
    exact (gasSteps_byte_match input hbyte).trans (gasSteps_size_fail input hfit hs)
  · exact gasSteps_byte_fail input hbyte

def gasSteps_match (input : ByteArray) (_hfit : CalldataFits input)
    (hsize : input.size = 56 ∨ input.size = 120 ∨ input.size = 63 ∨ input.size = 64 ∨ input.size = 65 ∨ input.size = 128) (hbyte : DirectGuard.firstByte input = 7) :
    GasSteps (DirectGuard.guardEntry input) (PatternedScan.patternedEntry input) :=
  (gasSteps_byte_match input hbyte).trans (gasSteps_size_match input hsize)

def gasSteps_hit (input : ByteArray) (hfit : CalldataFits input)
    (hsize : input.size = 56 ∨ input.size = 120 ∨ input.size = 63 ∨ input.size = 64 ∨ input.size = 65 ∨ input.size = 128) (hbyte : DirectGuard.firstByte input = 7) :
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
    (hbad : (input.size ≠ 56 ∧ input.size ≠ 120 ∧ input.size ≠ 63 ∧ input.size ≠ 64 ∧ input.size ≠ 65 ∧ input.size ≠ 128) ∨
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
