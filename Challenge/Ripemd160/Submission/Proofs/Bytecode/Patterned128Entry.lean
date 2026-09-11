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

private theorem guard_fallback_dest : Decode.isValidJumpDest submissionBytecode 371 = true :=
  Artifact.submissionArtifact.isValidJumpDest_index 206 (by rfl)

private theorem guard_match_dest : Decode.isValidJumpDest submissionBytecode 106 = true :=
  Artifact.submissionArtifact.isValidJumpDest_index 64 (by rfl)

private def guardJumpState (input : ByteArray) : State :=
  { DirectGuard.guardEntry input with pc := UInt256.ofNat 106, stack := [UInt256.ofNat 0] }

private def bytePrefix : List Located :=
  [DirectGuard.opAt 4088 .JUMPDEST,
   DirectGuard.pushAt 4089 0 0,
   DirectGuard.opAt 4090 .CALLDATALOAD,
   DirectGuard.pushAt 4091 0 0,
   DirectGuard.opAt 4092 .BYTE,
   DirectGuard.pushAt 4093 1 7,
   DirectGuard.opAt 4094 .XOR,
   DirectGuard.pushAt 4095 2 371]

private def sizePrefix : List Located :=
  [DirectGuard.pushAt 4097 0 0,
   DirectGuard.pushAt 4098 10 4750036598980209542017,
   DirectGuard.pushAt 4099 1 56,
   DirectGuard.opAt 4100 .SHL,
   DirectGuard.opAt 4101 .CALLDATASIZE,
   DirectGuard.opAt 4102 .SHR,
   DirectGuard.pushAt 4103 1 1,
   DirectGuard.opAt 4104 .AND,
   DirectGuard.pushAt 4105 1 106]

private def fallbackSuffix : List Located :=
  [DirectGuard.opAt 4107 .POP,
   DirectGuard.pushAt 4108 2 371,
   DirectGuard.opAt 4109 .JUMP]

private def guardMatchTail : List Located :=
  [DirectGuard.opAt 64 .JUMPDEST,
   DirectGuard.opAt 65 .POP]

private theorem run_byte_prefix (input : ByteArray) :
    DirectGuard.run bytePrefix (PatternedScan.stS input 5046 []) =
      some (PatternedScan.stS input 5057 [371, byteValue input]) := by
  let w := MachineState.readWord input 0
  let b := UInt256.byteAt 0 w
  let v := UInt256.xor 7 b
  let l0 : Located := DirectGuard.opAt 4088 .JUMPDEST
  have h0 := PatternedScan.blockOfS l0
    (PatternedScan.pcFactS input 4088 5046 [] (by norm_num) (by
      rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide))
    (PatternedScan.stepS_jumpdest input 5046 [] (by simp) (by norm_num))
  let l1 : Located := DirectGuard.pushAt 4089 0 0
  have h1 := PatternedScan.blockOfS l1
    (PatternedScan.pcFactS input 4089 5047 [] (by norm_num) (by
      rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide))
    (PatternedScan.stepS_push0 input 5047 [] (by simp) (by norm_num))
  let l2 : Located := DirectGuard.opAt 4090 .CALLDATALOAD
  have h2 := PatternedScan.blockOfS l2
    (PatternedScan.pcFactS input 4090 5048 [0] (by norm_num) (by
      rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide))
    (PatternedScan.stepS_calldataload input 5048 0 [] (by simp) (by norm_num))
  let l3 : Located := DirectGuard.pushAt 4091 0 0
  have h3 := PatternedScan.blockOfS l3
    (PatternedScan.pcFactS input 4091 5049 [w] (by norm_num) (by
      rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide))
    (PatternedScan.stepS_push0 input 5049 [w] (by simp) (by norm_num))
  let l4 : Located := DirectGuard.opAt 4092 .BYTE
  have h4 := PatternedScan.blockOfS l4
    (PatternedScan.pcFactS input 4092 5050 [0, w] (by norm_num) (by
      rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide))
    (PatternedScan.stepS_byte input 5050 0 w [] (by simp) (by norm_num))
  let l5 : Located := DirectGuard.pushAt 4093 1 7
  have h5 := PatternedScan.blockOfS l5
    (PatternedScan.pcFactS input 4093 5051 [b] (by norm_num) (by
      rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide))
    (PatternedScan.stepS_push input 5051 1 7 [b] (by simp) (by decide) (by decide) (by norm_num))
  let l6 : Located := DirectGuard.opAt 4094 .XOR
  have h6 := PatternedScan.blockOfS l6
    (PatternedScan.pcFactS input 4094 5053 [7, b] (by norm_num) (by
      rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide))
    (PatternedScan.stepS_xor input 5053 7 b [] (by simp) (by norm_num))
  let l7 : Located := DirectGuard.pushAt 4095 2 371
  have h7 := PatternedScan.blockOfS l7
    (PatternedScan.pcFactS input 4095 5054 [v] (by norm_num) (by
      rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide))
    (PatternedScan.stepS_push input 5054 2 371 [v] (by simp) (by decide) (by decide) (by norm_num))
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

@[simp] private theorem sizeHitPC4102 : Artifact.submissionArtifact.instructionPC 4097 = 5058 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide

@[simp] private theorem sizeHitPC4103 : Artifact.submissionArtifact.instructionPC 4098 = 5059 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide

@[simp] private theorem sizeHitPC4104 : Artifact.submissionArtifact.instructionPC 4099 = 5070 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide

@[simp] private theorem sizeHitPC4105 : Artifact.submissionArtifact.instructionPC 4100 = 5072 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide

@[simp] private theorem sizeHitPC4106 : Artifact.submissionArtifact.instructionPC 4101 = 5073 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide

@[simp] private theorem sizeHitPC4107 : Artifact.submissionArtifact.instructionPC 4102 = 5074 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide

@[simp] private theorem sizeHitPC4108 : Artifact.submissionArtifact.instructionPC 4103 = 5075 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide

@[simp] private theorem sizeHitPC4109 : Artifact.submissionArtifact.instructionPC 4104 = 5077 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide

@[simp] private theorem sizeHitPC4110 : Artifact.submissionArtifact.instructionPC 4105 = 5078 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide

@[simp] private theorem sizeHitPC4111 : Artifact.submissionArtifact.instructionPC 4106 = 5080 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide

@[simp] private theorem sizeHitPC4112 : Artifact.submissionArtifact.instructionPC 4107 = 5081 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide

@[simp] private theorem sizeHitPC4113 : Artifact.submissionArtifact.instructionPC 4108 = 5082 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide

@[simp] private theorem sizeHitPC4114 : Artifact.submissionArtifact.instructionPC 4109 = 5085 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide

private def sizeBit (input : ByteArray) : UInt256 :=
  UInt256.land 1 (UInt256.shiftRight 342276208914615837337365979874210086912
    (UInt256.ofNat input.size))

private theorem sizeBit_flag (input : ByteArray) : UInt256.isZero (sizeBit input) = sizeFlag input := by
  have h := SizeLookupFlag.flag (UInt256.ofNat input.size)
  rw [SizeLookupFlag.mask_literal] at h
  simpa only [sizeBit, sizeFlag, Word.literal_eq_ofNat] using h

private theorem run_size_prefix (input : ByteArray) :
    DirectGuard.run sizePrefix (PatternedScan.stS input 5058 []) =
      some (PatternedScan.stS input 5080 [106, sizeBit input, 0]) := by
  have hm : UInt256.shiftLeft (UInt256.ofNat 4750036598980209542017) (UInt256.ofNat 56) =
      UInt256.ofNat 342276208914615837337365979874210086912 := by decide
  simp (config := {maxSteps := 400000}) [sizePrefix, sizeBit, DirectGuard.opAt,
    DirectGuard.pushAt, DirectGuard.wfOp, PatternedScan.stS, initialState,
    Stepper.runLocatedBlock, Stepper.runLocated, Stepper.runInstr,
    Word.literal_eq_ofNat, Word.succ_ofNat_mod, Word.ofNat_add_mod, Word.word_toNat_ofNat, hm]

private theorem run_byte_fail (input : ByteArray)
    (hbyte : DirectGuard.firstByte input ≠ 7) :
    DirectGuard.run [DirectGuard.opAt 4096 .JUMPI] (PatternedScan.stS input 5057 [371, byteValue input]) =
      some (DirectGuard.fallbackState input) := by
  exact PatternedScan.blockOfS (DirectGuard.opAt 4096 .JUMPI)
    (PatternedScan.pcFactS input 4096 5057 [371, byteValue input] (by norm_num) (by
      rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide))
    (PatternedScan.stepS_jumpi_taken input 5057 371 371 (byteValue input) []
      (by simp) (by norm_num) (by simpa using Word.literal_eq_ofNat 371) (byteValue_true input hbyte) guard_fallback_dest)

private theorem run_byte_fall (input : ByteArray) :
    DirectGuard.run [DirectGuard.opAt 4096 .JUMPI] (PatternedScan.stS input 5057 [371, UInt256.ofNat 0]) =
      some (PatternedScan.stS input 5058 []) := by
  exact PatternedScan.blockOfS (DirectGuard.opAt 4096 .JUMPI)
    (PatternedScan.pcFactS input 4096 5057 [371, UInt256.ofNat 0] (by norm_num) (by
      rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide))
    (PatternedScan.stepS_jumpi_fall input 5057 371 (UInt256.ofNat 0) []
      (by simp) (by norm_num) (by decide))

private theorem run_size_match (input : ByteArray) (hc : UInt256.isTrue (sizeBit input)) :
    DirectGuard.run [DirectGuard.opAt 4106 .JUMPI]
      (PatternedScan.stS input 5080 [106, sizeBit input, 0]) =
      some (PatternedScan.stS input 106 [0]) := by
  exact PatternedScan.blockOfS (DirectGuard.opAt 4106 .JUMPI)
    (PatternedScan.pcFactS input 4106 5080 [106, sizeBit input, 0] (by norm_num) sizeHitPC4111)
    (PatternedScan.stepS_jumpi_taken input 5080 106 106 (sizeBit input) [0]
      (by simp) (by norm_num) (by rfl) hc guard_match_dest)

private theorem run_size_fall (input : ByteArray) (hc : ¬ UInt256.isTrue (sizeBit input)) :
    DirectGuard.run [DirectGuard.opAt 4106 .JUMPI]
      (PatternedScan.stS input 5080 [106, sizeBit input, 0]) =
      some (PatternedScan.stS input 5081 [0]) := by
  exact PatternedScan.blockOfS (DirectGuard.opAt 4106 .JUMPI)
    (PatternedScan.pcFactS input 4106 5080 [106, sizeBit input, 0] (by norm_num) sizeHitPC4111)
    (PatternedScan.stepS_jumpi_fall input 5080 106 (sizeBit input) [0]
      (by simp) (by norm_num) hc)

private theorem run_fallback_suffix (input : ByteArray) :
    DirectGuard.run fallbackSuffix (PatternedScan.stS input 5081 [0]) =
      some (DirectGuard.fallbackState input) := by
  let l0 : Located := DirectGuard.opAt 4107 .POP
  have h0 := PatternedScan.blockOfS l0
    (PatternedScan.pcFactS input 4107 5081 [0] (by norm_num) sizeHitPC4112)
    (PatternedScan.stepS_pop input 5081 0 [] (by simp) (by norm_num))
  let l1 : Located := DirectGuard.pushAt 4108 2 371
  have h1 := PatternedScan.blockOfS l1
    (PatternedScan.pcFactS input 4108 5082 [] (by norm_num) sizeHitPC4113)
    (PatternedScan.stepS_push input 5082 2 371 [] (by simp) (by decide) (by decide) (by norm_num))
  let l2 : Located := DirectGuard.opAt 4109 .JUMP
  have h2 := PatternedScan.blockOfS l2
    (PatternedScan.pcFactS input 4109 5085 [371] (by norm_num) sizeHitPC4114)
    (PatternedScan.stepS_jump input 5085 371 371 [] (by simp) (by norm_num) (by rfl) guard_fallback_dest)
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

private def gasSteps_byte_match (input : ByteArray)
    (hbyte : DirectGuard.firstByte input = 7) :
    GasSteps (DirectGuard.guardEntry input) (PatternedScan.stS input 5058 []) := by
  have hp := run_byte_prefix input
  rw [byteValue_zero input hbyte] at hp
  exact (sound bytePrefix hp).trans (sound _ (run_byte_fall input))

private def gasSteps_byte_fail (input : ByteArray)
    (hbyte : DirectGuard.firstByte input ≠ 7) :
    GasSteps (DirectGuard.guardEntry input) (DirectGuard.fallbackState input) :=
  (sound bytePrefix (run_byte_prefix input)).trans (sound _ (run_byte_fail input hbyte))

private def gasSteps_size_fail (input : ByteArray) (hfit : CalldataFits input)
    (hbad : input.size ≠ 56 ∧ input.size ≠ 120 ∧ input.size ≠ 63 ∧ input.size ≠ 64 ∧ input.size ≠ 65 ∧ input.size ≠ 128 ∧ input.size ≠ 119) :
    GasSteps (PatternedScan.stS input 5058 []) (DirectGuard.fallbackState input) := by
  have hf := sizeFlag_fail input hfit hbad
  rw [← sizeBit_flag] at hf
  have hc : ¬ UInt256.isTrue (sizeBit input) := by
    intro ht
    change (sizeBit input).toNat ≠ 0 at ht
    rw [UInt256.isZero, if_neg ht] at hf
    exact (by decide : UInt256.ofNat 0 ≠ UInt256.ofNat 1) hf
  exact (sound sizePrefix (run_size_prefix input)).trans
    ((sound _ (run_size_fall input hc)).trans (sound fallbackSuffix (run_fallback_suffix input)))


private def gasSteps_size_match (input : ByteArray) (hsize : input.size = 56 ∨ input.size = 120 ∨ input.size = 63 ∨ input.size = 64 ∨ input.size = 65 ∨ input.size = 128 ∨ input.size = 119) :
    GasSteps (PatternedScan.stS input 5058 []) (PatternedScan.patternedEntry input) := by
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
    (hbad : (input.size ≠ 56 ∧ input.size ≠ 120 ∧ input.size ≠ 63 ∧ input.size ≠ 64 ∧ input.size ≠ 65 ∧ input.size ≠ 128 ∧ input.size ≠ 119) ∨ DirectGuard.firstByte input ≠ 7) :
    GasSteps (DirectGuard.guardEntry input) (DirectGuard.fallbackState input) := by
  by_cases hbyte : DirectGuard.firstByte input = 7
  · have hs : input.size ≠ 56 ∧ input.size ≠ 120 ∧ input.size ≠ 63 ∧ input.size ≠ 64 ∧ input.size ≠ 65 ∧ input.size ≠ 128 ∧ input.size ≠ 119 := by
      rcases hbad with hs | hb
      · exact hs
      · exact False.elim (hb hbyte)
    exact (gasSteps_byte_match input hbyte).trans (gasSteps_size_fail input hfit hs)
  · exact gasSteps_byte_fail input hbyte

def gasSteps_match (input : ByteArray) (_hfit : CalldataFits input)
    (hsize : input.size = 56 ∨ input.size = 120 ∨ input.size = 63 ∨ input.size = 64 ∨ input.size = 65 ∨ input.size = 128 ∨ input.size = 119) (hbyte : DirectGuard.firstByte input = 7) :
    GasSteps (DirectGuard.guardEntry input) (PatternedScan.patternedEntry input) :=
  (gasSteps_byte_match input hbyte).trans (gasSteps_size_match input hsize)

def gasSteps_hit (input : ByteArray) (hfit : CalldataFits input)
    (hsize : input.size = 56 ∨ input.size = 120 ∨ input.size = 63 ∨ input.size = 64 ∨ input.size = 65 ∨ input.size = 128 ∨ input.size = 119) (hbyte : DirectGuard.firstByte input = 7) :
    GasSteps (initialState submissionBytecode input 0)
      (PatternedScan.patternedEntry input) := by
  have h1000 : input.size ≠ 1000 := by omega
  have h376 : input.size ≠ 376 := by omega
  have h256 : input.size ≠ 256 := by omega
  exact (Execution.gasSteps_start input).trans
    ((sound (DirectGuard.sizePath input)
        (DirectGuard.run_size_fail input hfit h1000 h376 h256)).trans
      (gasSteps_match input hfit hsize hbyte))

def gasSteps_miss (input : ByteArray) (hfit : CalldataFits input)
    (hbad : (input.size ≠ 56 ∧ input.size ≠ 120 ∧ input.size ≠ 63 ∧ input.size ≠ 64 ∧ input.size ≠ 65 ∧ input.size ≠ 128 ∧ input.size ≠ 119) ∨
      DirectGuard.firstByte input ≠ 7)
    (h1000 : input.size ≠ 1000) (h376 : input.size ≠ 376)
    (h256 : input.size ≠ 256) :
    GasSteps (initialState submissionBytecode input 0)
      (DirectGuard.fallbackState input) := by
  exact (Execution.gasSteps_start input).trans
    ((sound (DirectGuard.sizePath input)
        (DirectGuard.run_size_fail input hfit h1000 h376 h256)).trans
      (gasSteps_fail input hfit hbad))

end Challenge.Ripemd160.Submission.Proofs.Bytecode.Patterned128Entry
