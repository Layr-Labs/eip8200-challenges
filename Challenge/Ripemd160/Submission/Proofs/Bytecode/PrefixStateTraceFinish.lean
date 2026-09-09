import Challenge.Ripemd160.Submission.Proofs.Bytecode.PrefixStateMemory
import Challenge.Ripemd160.Submission.Proofs.Bytecode.PrefixStatePaths
import Challenge.Ripemd160.Submission.Proofs.Bytecode.PrefixStateModel
import Challenge.Ripemd160.Submission.Proofs.Bytecode.BooleanSelect
import Challenge.Ripemd160.Submission.Proofs.Bytecode.KnownInputLogic

set_option warningAsError true
set_option maxRecDepth 50000
set_option maxHeartbeats 5000000
set_option linter.unusedSimpArgs false

/-!
# Checked-prefix finish: SWAR setup, the seven derived-word rungs, and installs

After the word-0 match the ladder derives every further expected word from
the word-0 literal with a bytewise `+0xA0` SWAR recurrence and compares it
with the next calldata word.  A word-1 mismatch bails to the generic
compressor; a word-2/3 mismatch installs `H1`; a word-4/5 mismatch installs
`H2`; six matches install `H3` unless the two depth-4 checks miss, while all
eight matches install `H4`.
-/

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.PrefixStateTraceFinish

open Challenge.Ripemd160 Challenge.EvmProof EvmSemantics EvmSemantics.EVM

/-! ## SWAR constants -/

def ONE : UInt256 := UInt256.ofNat 0x0101010101010101010101010101010101010101010101010101010101010101
def M7f : UInt256 := UInt256.ofNat 0x7f7f7f7f7f7f7f7f7f7f7f7f7f7f7f7f7f7f7f7f7f7f7f7f7f7f7f7f7f7f7f7f
def M80 : UInt256 := UInt256.ofNat 0x8080808080808080808080808080808080808080808080808080808080808080
def C20 : UInt256 := UInt256.ofNat 0x2020202020202020202020202020202020202020202020202020202020202020

theorem one_eq : UInt256.lnot ⟨0⟩ / UInt256.ofNat 255 = ONE := by decide
theorem one_eq' : UInt256.lnot (UInt256.ofNat 0) / UInt256.ofNat 255 = ONE := by decide
theorem one_eq'' : UInt256.lnot 0 / UInt256.ofNat 255 = ONE := by decide
theorem m7f_eq : UInt256.ofNat 127 * ONE = M7f := by decide
theorem m80_eq : UInt256.lnot M7f = M80 := by decide
theorem c20_eq : UInt256.shiftRight M80 (UInt256.ofNat 2) = C20 := by decide

private theorem zero_toNat : (⟨0⟩ : UInt256).toNat = 0 := rfl

/-! ## The word recurrence

Each rung computes `M80 ^^^ ((M80 &&& e) ^^^ (C20 + (M7f &&& e)))`, which is
`(e + 0xA0) mod 256` in every byte lane; on the patterned words this steps
word `k` to word `k + 1`. -/

theorem step0 : UInt256.xor M80 (UInt256.xor (UInt256.land M80 (0x072c51769bc0e50a2f54799ec3e80d32577ca1c6eb10355a7fa4c9ee13385d82 : UInt256))
    (C20 + UInt256.land M7f (0x072c51769bc0e50a2f54799ec3e80d32577ca1c6eb10355a7fa4c9ee13385d82 : UInt256))) = (0xa7ccf1163b6085aacff4193e6388add2f71c41668bb0d5fa1f44698eb3d8fd22 : UInt256) := by decide
theorem step0' : UInt256.xor M80 (UInt256.xor (UInt256.land M80 (UInt256.ofNat 0x072c51769bc0e50a2f54799ec3e80d32577ca1c6eb10355a7fa4c9ee13385d82))
    (C20 + UInt256.land M7f (UInt256.ofNat 0x072c51769bc0e50a2f54799ec3e80d32577ca1c6eb10355a7fa4c9ee13385d82))) = UInt256.ofNat 0xa7ccf1163b6085aacff4193e6388add2f71c41668bb0d5fa1f44698eb3d8fd22 := by decide
theorem step1 : UInt256.xor M80 (UInt256.xor (UInt256.land M80 (0xa7ccf1163b6085aacff4193e6388add2f71c41668bb0d5fa1f44698eb3d8fd22 : UInt256))
    (C20 + UInt256.land M7f (0xa7ccf1163b6085aacff4193e6388add2f71c41668bb0d5fa1f44698eb3d8fd22 : UInt256))) = (0x476c91b6db00254a6f94b9de03284d7297bce1062b50759abfe4092e53789dc2 : UInt256) := by decide
theorem step1' : UInt256.xor M80 (UInt256.xor (UInt256.land M80 (UInt256.ofNat 0xa7ccf1163b6085aacff4193e6388add2f71c41668bb0d5fa1f44698eb3d8fd22))
    (C20 + UInt256.land M7f (UInt256.ofNat 0xa7ccf1163b6085aacff4193e6388add2f71c41668bb0d5fa1f44698eb3d8fd22))) = UInt256.ofNat 0x476c91b6db00254a6f94b9de03284d7297bce1062b50759abfe4092e53789dc2 := by decide
theorem step2 : UInt256.xor M80 (UInt256.xor (UInt256.land M80 (0x476c91b6db00254a6f94b9de03284d7297bce1062b50759abfe4092e53789dc2 : UInt256))
    (C20 + UInt256.land M7f (0x476c91b6db00254a6f94b9de03284d7297bce1062b50759abfe4092e53789dc2 : UInt256))) = (0xe70c31567ba0c5ea0f34597ea3c8ed12375c81a6cbf0153a5f84a9cef3183d62 : UInt256) := by decide
theorem step2' : UInt256.xor M80 (UInt256.xor (UInt256.land M80 (UInt256.ofNat 0x476c91b6db00254a6f94b9de03284d7297bce1062b50759abfe4092e53789dc2))
    (C20 + UInt256.land M7f (UInt256.ofNat 0x476c91b6db00254a6f94b9de03284d7297bce1062b50759abfe4092e53789dc2))) = UInt256.ofNat 0xe70c31567ba0c5ea0f34597ea3c8ed12375c81a6cbf0153a5f84a9cef3183d62 := by decide
theorem step3 : UInt256.xor M80 (UInt256.xor (UInt256.land M80 (0xe70c31567ba0c5ea0f34597ea3c8ed12375c81a6cbf0153a5f84a9cef3183d62 : UInt256))
    (C20 + UInt256.land M7f (0xe70c31567ba0c5ea0f34597ea3c8ed12375c81a6cbf0153a5f84a9cef3183d62 : UInt256))) = (0x87acd1f61b40658aafd4f91e43688db2d7fc21466b90b5daff24496e93b8dd02 : UInt256) := by decide
theorem step3' : UInt256.xor M80 (UInt256.xor (UInt256.land M80 (UInt256.ofNat 0xe70c31567ba0c5ea0f34597ea3c8ed12375c81a6cbf0153a5f84a9cef3183d62))
    (C20 + UInt256.land M7f (UInt256.ofNat 0xe70c31567ba0c5ea0f34597ea3c8ed12375c81a6cbf0153a5f84a9cef3183d62))) = UInt256.ofNat 0x87acd1f61b40658aafd4f91e43688db2d7fc21466b90b5daff24496e93b8dd02 := by decide
theorem step4 : UInt256.xor M80 (UInt256.xor (UInt256.land M80 (0x87acd1f61b40658aafd4f91e43688db2d7fc21466b90b5daff24496e93b8dd02 : UInt256))
    (C20 + UInt256.land M7f (0x87acd1f61b40658aafd4f91e43688db2d7fc21466b90b5daff24496e93b8dd02 : UInt256))) = (0x274c7196bbe0052a4f7499bee3082d52779cc1e60b30557a9fc4e90e33587da2 : UInt256) := by decide
theorem step4' : UInt256.xor M80 (UInt256.xor (UInt256.land M80 (UInt256.ofNat 0x87acd1f61b40658aafd4f91e43688db2d7fc21466b90b5daff24496e93b8dd02))
    (C20 + UInt256.land M7f (UInt256.ofNat 0x87acd1f61b40658aafd4f91e43688db2d7fc21466b90b5daff24496e93b8dd02))) = UInt256.ofNat 0x274c7196bbe0052a4f7499bee3082d52779cc1e60b30557a9fc4e90e33587da2 := by decide

/-! ## Frames -/

private def frame (s : State) (input : ByteArray) (pc : Nat) : State :=
  { s with
    pc := UInt256.ofNat pc
    stack := [DriverTrace.messageOffsetWord 0, UInt256.ofNat 102,
      DriverTrace.blockOffsetWord 0, Padding.paddedWord input] }

/-- Entry at the SWAR setup (pc 5012), right after the word-0 match. -/
def entry (s : State) (input : ByteArray) : State := frame s input 5012

/-- Ladder frame after the scratch `MLOAD`: the running expected word `e`,
the three SWAR masks, then the driver stack. -/
def rungFrame (s : State) (input : ByteArray) (pc : Nat) (e : UInt256) : State :=
  { s with
    pc := UInt256.ofNat pc
    activeWords := s.activeWordsAfterUInt256 0 32
    stack := [e, C20, M80, M7f, DriverTrace.messageOffsetWord 0, UInt256.ofNat 102,
      DriverTrace.blockOffsetWord 0, Padding.paddedWord input] }

/-! ## Jump destinations -/

theorem jumpDest_generic : Decode.isValidJumpDest submissionBytecode 464 = true := by
  have hpc : Artifact.submissionArtifact.instructionPC 272 = 464 := by
    rw [ArtifactByteLength.instructionPC_eq_byteLength]
    decide
  have h := Artifact.submissionArtifact.isValidJumpDest_index 272 (by rfl)
  rw [hpc] at h
  exact h

theorem jumpDest_driver : Decode.isValidJumpDest submissionBytecode 102 = true := by
  have hpc : Artifact.submissionArtifact.instructionPC 64 = 102 := by
    rw [ArtifactByteLength.instructionPC_eq_byteLength]
    decide
  have h := Artifact.submissionArtifact.isValidJumpDest_index 64 (by rfl)
  rw [hpc] at h
  exact h

theorem jumpDest_hit2 : Decode.isValidJumpDest submissionBytecode 5179 = true := by
  have h := Artifact.submissionArtifact.isValidJumpDest_index 4210 (by rfl)
  rw [PrefixStatePaths.pc4210] at h
  exact h

theorem jumpDest_hit1 : Decode.isValidJumpDest submissionBytecode 5231 = true := by
  have h := Artifact.submissionArtifact.isValidJumpDest_index 4236 (by rfl)
  rw [PrefixStatePaths.pc4236] at h
  exact h

theorem jumpDest_bail : Decode.isValidJumpDest submissionBytecode 5278 = true := by
  have h := Artifact.submissionArtifact.isValidJumpDest_index 4258 (by rfl)
  rw [PrefixStatePaths.pc4258] at h
  exact h

theorem jumpDest_rung6 : Decode.isValidJumpDest submissionBytecode 5287 = true := by
  have h := Artifact.submissionArtifact.isValidJumpDest_index 4265 (by rfl)
  rw [PrefixStatePaths.pc4265] at h
  exact h

theorem jumpDest_hit3Fallback : Decode.isValidJumpDest submissionBytecode 5380 = true := by
  have h := Artifact.submissionArtifact.isValidJumpDest_index 4326 (by rfl)
  rw [PrefixStatePaths.pc4326] at h
  exact h

/-! ## SWAR setup -/

/-- The thirteen-instruction setup derives `ONE`, `M7f`, `M80`, `C20` on the
stack and seeds the running word from scratch word 0. -/
theorem run_setup (s : State) (input : ByteArray)
    (hmem0 : MachineState.readWord s.memory 0 = PatternedWordData.expectedWordAt 0)
    (hrun : s.halt = .Running) :
    Stepper.runLocatedBlock PrefixStatePaths.setupPath (entry s input) =
      some (rungFrame s input 5028 (PatternedWordData.expectedWordAt 0)) := by
  simp (config := { maxSteps := 1000000 })
    [PrefixStatePaths.setupPath, Stepper.runLocatedBlock, Stepper.runLocated,
      Stepper.runInstr, entry, frame, rungFrame, hmem0, hrun,
      one_eq, one_eq', one_eq'', m7f_eq, m80_eq, c20_eq,
      PrefixStatePaths.pc4087,
      PrefixStatePaths.pc4088,
      PrefixStatePaths.pc4089,
      PrefixStatePaths.pc4090,
      PrefixStatePaths.pc4091,
      PrefixStatePaths.pc4092,
      PrefixStatePaths.pc4093,
      PrefixStatePaths.pc4094,
      PrefixStatePaths.pc4095,
      PrefixStatePaths.pc4096,
      PrefixStatePaths.pc4097,
      PrefixStatePaths.pc4098,
      PrefixStatePaths.pc4099,
      State.activeWordsAfterUInt256, zero_toNat,
      Challenge.EvmProof.Word.word_toNat_ofNat,
      Challenge.EvmProof.Word.ofNat_add_mod,
      Challenge.EvmProof.Word.succ_ofNat_mod, Nat.mod_eq_of_lt]

/-! ## Rungs -/


/-- Rung 1 on a word-1 match: the running word steps to word 1 and the
`JUMPI` is not taken. -/
theorem run_rung1_hit (s : State) (input : ByteArray)
    (hword : MachineState.readWord input 32 = PatternedWordData.expectedWordAt 1)
    (hcalldata : s.executionEnv.calldata = input)
    (hrun : s.halt = .Running) :
    Stepper.runLocatedBlock PrefixStatePaths.rung1Path
      (rungFrame s input 5028 (PatternedWordData.expectedWordAt 0)) =
      some (rungFrame s input 5048 (PatternedWordData.expectedWordAt 1)) := by
  have hzero : UInt256.xor (MachineState.readWord input 32)
      (PatternedWordData.expectedWordAt 1) = 0 :=
    (KnownInputLogic.wordXor_eq_zero_iff _ _).2 hword
  have hzero' : UInt256.xor (PatternedWordData.expectedWordAt 1)
      (MachineState.readWord input 32) = 0 := by
    rw [hword]
    exact (KnownInputLogic.wordXor_eq_zero_iff _ _).2 rfl
  have hcond : (UInt256.xor (MachineState.readWord input 32)
      (PatternedWordData.expectedWordAt 1)).toNat = 0 := by
    rw [hzero]
    rfl
  have hcond' : (UInt256.xor (PatternedWordData.expectedWordAt 1)
      (MachineState.readWord input 32)).toNat = 0 := by
    rw [hzero']
    rfl
  have hcondL := hcond
  rw [PatternedWordData.expectedWordAt_1] at hcondL
  have hcondL' := hcond'
  rw [PatternedWordData.expectedWordAt_1] at hcondL'
  have hfalse : ¬ UInt256.isTrue (UInt256.xor (MachineState.readWord input 32)
      (PatternedWordData.expectedWordAt 1)) := by
    rw [hzero]
    decide
  have hfalse' : ¬ UInt256.isTrue (UInt256.xor (PatternedWordData.expectedWordAt 1)
      (MachineState.readWord input 32)) := by
    rw [hzero']
    decide
  have hfalseL := hfalse
  rw [PatternedWordData.expectedWordAt_1] at hfalseL
  have hfalseL' := hfalse'
  rw [PatternedWordData.expectedWordAt_1] at hfalseL'
  simp (config := { maxSteps := 1000000 })
    [PrefixStatePaths.rung1Path, Stepper.runLocatedBlock, Stepper.runLocated,
      Stepper.runInstr, rungFrame, step0, step0', step1, step1', step2, step2', step3, step3', step4, step4',
      hzero, hzero', hcond, hcond', hcondL, hcondL', hfalse, hfalse', hfalseL, hfalseL',
      jumpDest_bail,
      PrefixStatePaths.pc4100,
      PrefixStatePaths.pc4101,
      PrefixStatePaths.pc4102,
      PrefixStatePaths.pc4103,
      PrefixStatePaths.pc4104,
      PrefixStatePaths.pc4105,
      PrefixStatePaths.pc4106,
      PrefixStatePaths.pc4107,
      PrefixStatePaths.pc4108,
      PrefixStatePaths.pc4109,
      PrefixStatePaths.pc4110,
      PrefixStatePaths.pc4111,
      PrefixStatePaths.pc4112,
      PrefixStatePaths.pc4113,
      PrefixStatePaths.pc4114,
      PrefixStatePaths.pc4115,
      PrefixStatePaths.pc4116,
      UInt256.isTrue, hrun, hcalldata, List.exchange,
      State.activeWordsAfterUInt256, zero_toNat,
      Challenge.EvmProof.Word.word_toNat_ofNat,
      Challenge.EvmProof.Word.ofNat_add_mod,
      Challenge.EvmProof.Word.succ_ofNat_mod, Nat.mod_eq_of_lt]

/-- Rung 1 on a word-1 mismatch: the running word steps to word 1 and the
`JUMPI` is taken to pc 5278. -/
theorem run_rung1_miss (s : State) (input : ByteArray)
    (hword : MachineState.readWord input 32 ≠ PatternedWordData.expectedWordAt 1)
    (hcalldata : s.executionEnv.calldata = input)
    (hcode : s.executionEnv.code = submissionBytecode)
    (hrun : s.halt = .Running) :
    Stepper.runLocatedBlock PrefixStatePaths.rung1Path
      (rungFrame s input 5028 (PatternedWordData.expectedWordAt 0)) =
      some (rungFrame s input 5278 (PatternedWordData.expectedWordAt 1)) := by
  have htrue : UInt256.isTrue (UInt256.xor (MachineState.readWord input 32)
      (PatternedWordData.expectedWordAt 1)) := by
    intro hz
    apply hword
    apply (KnownInputLogic.wordXor_eq_zero_iff _ _).1
    apply Challenge.EvmProof.Word.word_ext
    simpa using hz
  have htrue' : UInt256.isTrue (UInt256.xor (PatternedWordData.expectedWordAt 1)
      (MachineState.readWord input 32)) := by
    intro hz
    apply hword
    have hzero : UInt256.xor (PatternedWordData.expectedWordAt 1)
        (MachineState.readWord input 32) = 0 := by
      apply Challenge.EvmProof.Word.word_ext
      simpa using hz
    exact ((KnownInputLogic.wordXor_eq_zero_iff _ _).1 hzero).symm
  have hcond : (UInt256.xor (MachineState.readWord input 32)
      (PatternedWordData.expectedWordAt 1)).toNat ≠ 0 := by
    intro hz
    apply hword
    apply (KnownInputLogic.wordXor_eq_zero_iff _ _).1
    apply Challenge.EvmProof.Word.word_ext
    simpa using hz
  have hcond' : (UInt256.xor (PatternedWordData.expectedWordAt 1)
      (MachineState.readWord input 32)).toNat ≠ 0 := by
    intro hz
    apply hword
    have hzero : UInt256.xor (PatternedWordData.expectedWordAt 1)
        (MachineState.readWord input 32) = 0 := by
      apply Challenge.EvmProof.Word.word_ext
      simpa using hz
    exact ((KnownInputLogic.wordXor_eq_zero_iff _ _).1 hzero).symm
  have hcondL := hcond
  rw [PatternedWordData.expectedWordAt_1] at hcondL
  have hcondL' := hcond'
  rw [PatternedWordData.expectedWordAt_1] at hcondL'
  have htrueL := htrue
  rw [PatternedWordData.expectedWordAt_1] at htrueL
  have htrueL' := htrue'
  rw [PatternedWordData.expectedWordAt_1] at htrueL'
  simp (config := { maxSteps := 1000000 })
    [PrefixStatePaths.rung1Path, Stepper.runLocatedBlock, Stepper.runLocated,
      Stepper.runInstr, rungFrame, step0, step0', step1, step1', step2, step2', step3, step3', step4, step4',
      htrue, htrue', hcond, hcond', hcondL, hcondL', htrueL, htrueL',
      jumpDest_bail, hcode,
      PrefixStatePaths.pc4100,
      PrefixStatePaths.pc4101,
      PrefixStatePaths.pc4102,
      PrefixStatePaths.pc4103,
      PrefixStatePaths.pc4104,
      PrefixStatePaths.pc4105,
      PrefixStatePaths.pc4106,
      PrefixStatePaths.pc4107,
      PrefixStatePaths.pc4108,
      PrefixStatePaths.pc4109,
      PrefixStatePaths.pc4110,
      PrefixStatePaths.pc4111,
      PrefixStatePaths.pc4112,
      PrefixStatePaths.pc4113,
      PrefixStatePaths.pc4114,
      PrefixStatePaths.pc4115,
      PrefixStatePaths.pc4116,
      UInt256.isTrue, hrun, hcalldata, List.exchange,
      State.activeWordsAfterUInt256, zero_toNat,
      Challenge.EvmProof.Word.word_toNat_ofNat,
      Challenge.EvmProof.Word.ofNat_add_mod,
      Challenge.EvmProof.Word.succ_ofNat_mod, Nat.mod_eq_of_lt]


/-- Rung 2 on a word-2 match: the running word steps to word 2 and the
`JUMPI` is not taken. -/
theorem run_rung2_hit (s : State) (input : ByteArray)
    (hword : MachineState.readWord input 64 = PatternedWordData.expectedWordAt 2)
    (hcalldata : s.executionEnv.calldata = input)
    (hrun : s.halt = .Running) :
    Stepper.runLocatedBlock PrefixStatePaths.rung2Path
      (rungFrame s input 5048 (PatternedWordData.expectedWordAt 1)) =
      some (rungFrame s input 5068 (PatternedWordData.expectedWordAt 2)) := by
  have hzero : UInt256.xor (MachineState.readWord input 64)
      (PatternedWordData.expectedWordAt 2) = 0 :=
    (KnownInputLogic.wordXor_eq_zero_iff _ _).2 hword
  have hzero' : UInt256.xor (PatternedWordData.expectedWordAt 2)
      (MachineState.readWord input 64) = 0 := by
    rw [hword]
    exact (KnownInputLogic.wordXor_eq_zero_iff _ _).2 rfl
  have hcond : (UInt256.xor (MachineState.readWord input 64)
      (PatternedWordData.expectedWordAt 2)).toNat = 0 := by
    rw [hzero]
    rfl
  have hcond' : (UInt256.xor (PatternedWordData.expectedWordAt 2)
      (MachineState.readWord input 64)).toNat = 0 := by
    rw [hzero']
    rfl
  have hcondL := hcond
  rw [PatternedWordData.expectedWordAt_2] at hcondL
  have hcondL' := hcond'
  rw [PatternedWordData.expectedWordAt_2] at hcondL'
  have hfalse : ¬ UInt256.isTrue (UInt256.xor (MachineState.readWord input 64)
      (PatternedWordData.expectedWordAt 2)) := by
    rw [hzero]
    decide
  have hfalse' : ¬ UInt256.isTrue (UInt256.xor (PatternedWordData.expectedWordAt 2)
      (MachineState.readWord input 64)) := by
    rw [hzero']
    decide
  have hfalseL := hfalse
  rw [PatternedWordData.expectedWordAt_2] at hfalseL
  have hfalseL' := hfalse'
  rw [PatternedWordData.expectedWordAt_2] at hfalseL'
  simp (config := { maxSteps := 1000000 })
    [PrefixStatePaths.rung2Path, Stepper.runLocatedBlock, Stepper.runLocated,
      Stepper.runInstr, rungFrame, step0, step0', step1, step1', step2, step2', step3, step3', step4, step4',
      hzero, hzero', hcond, hcond', hcondL, hcondL', hfalse, hfalse', hfalseL, hfalseL',
      jumpDest_hit1,
      PrefixStatePaths.pc4117,
      PrefixStatePaths.pc4118,
      PrefixStatePaths.pc4119,
      PrefixStatePaths.pc4120,
      PrefixStatePaths.pc4121,
      PrefixStatePaths.pc4122,
      PrefixStatePaths.pc4123,
      PrefixStatePaths.pc4124,
      PrefixStatePaths.pc4125,
      PrefixStatePaths.pc4126,
      PrefixStatePaths.pc4127,
      PrefixStatePaths.pc4128,
      PrefixStatePaths.pc4129,
      PrefixStatePaths.pc4130,
      PrefixStatePaths.pc4131,
      PrefixStatePaths.pc4132,
      PrefixStatePaths.pc4133,
      UInt256.isTrue, hrun, hcalldata, List.exchange,
      State.activeWordsAfterUInt256, zero_toNat,
      Challenge.EvmProof.Word.word_toNat_ofNat,
      Challenge.EvmProof.Word.ofNat_add_mod,
      Challenge.EvmProof.Word.succ_ofNat_mod, Nat.mod_eq_of_lt]

/-- Rung 2 on a word-2 mismatch: the running word steps to word 2 and the
`JUMPI` is taken to pc 5231. -/
theorem run_rung2_miss (s : State) (input : ByteArray)
    (hword : MachineState.readWord input 64 ≠ PatternedWordData.expectedWordAt 2)
    (hcalldata : s.executionEnv.calldata = input)
    (hcode : s.executionEnv.code = submissionBytecode)
    (hrun : s.halt = .Running) :
    Stepper.runLocatedBlock PrefixStatePaths.rung2Path
      (rungFrame s input 5048 (PatternedWordData.expectedWordAt 1)) =
      some (rungFrame s input 5231 (PatternedWordData.expectedWordAt 2)) := by
  have htrue : UInt256.isTrue (UInt256.xor (MachineState.readWord input 64)
      (PatternedWordData.expectedWordAt 2)) := by
    intro hz
    apply hword
    apply (KnownInputLogic.wordXor_eq_zero_iff _ _).1
    apply Challenge.EvmProof.Word.word_ext
    simpa using hz
  have htrue' : UInt256.isTrue (UInt256.xor (PatternedWordData.expectedWordAt 2)
      (MachineState.readWord input 64)) := by
    intro hz
    apply hword
    have hzero : UInt256.xor (PatternedWordData.expectedWordAt 2)
        (MachineState.readWord input 64) = 0 := by
      apply Challenge.EvmProof.Word.word_ext
      simpa using hz
    exact ((KnownInputLogic.wordXor_eq_zero_iff _ _).1 hzero).symm
  have hcond : (UInt256.xor (MachineState.readWord input 64)
      (PatternedWordData.expectedWordAt 2)).toNat ≠ 0 := by
    intro hz
    apply hword
    apply (KnownInputLogic.wordXor_eq_zero_iff _ _).1
    apply Challenge.EvmProof.Word.word_ext
    simpa using hz
  have hcond' : (UInt256.xor (PatternedWordData.expectedWordAt 2)
      (MachineState.readWord input 64)).toNat ≠ 0 := by
    intro hz
    apply hword
    have hzero : UInt256.xor (PatternedWordData.expectedWordAt 2)
        (MachineState.readWord input 64) = 0 := by
      apply Challenge.EvmProof.Word.word_ext
      simpa using hz
    exact ((KnownInputLogic.wordXor_eq_zero_iff _ _).1 hzero).symm
  have hcondL := hcond
  rw [PatternedWordData.expectedWordAt_2] at hcondL
  have hcondL' := hcond'
  rw [PatternedWordData.expectedWordAt_2] at hcondL'
  have htrueL := htrue
  rw [PatternedWordData.expectedWordAt_2] at htrueL
  have htrueL' := htrue'
  rw [PatternedWordData.expectedWordAt_2] at htrueL'
  simp (config := { maxSteps := 1000000 })
    [PrefixStatePaths.rung2Path, Stepper.runLocatedBlock, Stepper.runLocated,
      Stepper.runInstr, rungFrame, step0, step0', step1, step1', step2, step2', step3, step3', step4, step4',
      htrue, htrue', hcond, hcond', hcondL, hcondL', htrueL, htrueL',
      jumpDest_hit1, hcode,
      PrefixStatePaths.pc4117,
      PrefixStatePaths.pc4118,
      PrefixStatePaths.pc4119,
      PrefixStatePaths.pc4120,
      PrefixStatePaths.pc4121,
      PrefixStatePaths.pc4122,
      PrefixStatePaths.pc4123,
      PrefixStatePaths.pc4124,
      PrefixStatePaths.pc4125,
      PrefixStatePaths.pc4126,
      PrefixStatePaths.pc4127,
      PrefixStatePaths.pc4128,
      PrefixStatePaths.pc4129,
      PrefixStatePaths.pc4130,
      PrefixStatePaths.pc4131,
      PrefixStatePaths.pc4132,
      PrefixStatePaths.pc4133,
      UInt256.isTrue, hrun, hcalldata, List.exchange,
      State.activeWordsAfterUInt256, zero_toNat,
      Challenge.EvmProof.Word.word_toNat_ofNat,
      Challenge.EvmProof.Word.ofNat_add_mod,
      Challenge.EvmProof.Word.succ_ofNat_mod, Nat.mod_eq_of_lt]


/-- Rung 3 on a word-3 match: the running word steps to word 3 and the
`JUMPI` is not taken. -/
theorem run_rung3_hit (s : State) (input : ByteArray)
    (hword : MachineState.readWord input 96 = PatternedWordData.expectedWordAt 3)
    (hcalldata : s.executionEnv.calldata = input)
    (hrun : s.halt = .Running) :
    Stepper.runLocatedBlock PrefixStatePaths.rung3Path
      (rungFrame s input 5068 (PatternedWordData.expectedWordAt 2)) =
      some (rungFrame s input 5088 (PatternedWordData.expectedWordAt 3)) := by
  have hzero : UInt256.xor (MachineState.readWord input 96)
      (PatternedWordData.expectedWordAt 3) = 0 :=
    (KnownInputLogic.wordXor_eq_zero_iff _ _).2 hword
  have hzero' : UInt256.xor (PatternedWordData.expectedWordAt 3)
      (MachineState.readWord input 96) = 0 := by
    rw [hword]
    exact (KnownInputLogic.wordXor_eq_zero_iff _ _).2 rfl
  have hcond : (UInt256.xor (MachineState.readWord input 96)
      (PatternedWordData.expectedWordAt 3)).toNat = 0 := by
    rw [hzero]
    rfl
  have hcond' : (UInt256.xor (PatternedWordData.expectedWordAt 3)
      (MachineState.readWord input 96)).toNat = 0 := by
    rw [hzero']
    rfl
  have hcondL := hcond
  rw [PatternedWordData.expectedWordAt_3] at hcondL
  have hcondL' := hcond'
  rw [PatternedWordData.expectedWordAt_3] at hcondL'
  have hfalse : ¬ UInt256.isTrue (UInt256.xor (MachineState.readWord input 96)
      (PatternedWordData.expectedWordAt 3)) := by
    rw [hzero]
    decide
  have hfalse' : ¬ UInt256.isTrue (UInt256.xor (PatternedWordData.expectedWordAt 3)
      (MachineState.readWord input 96)) := by
    rw [hzero']
    decide
  have hfalseL := hfalse
  rw [PatternedWordData.expectedWordAt_3] at hfalseL
  have hfalseL' := hfalse'
  rw [PatternedWordData.expectedWordAt_3] at hfalseL'
  simp (config := { maxSteps := 1000000 })
    [PrefixStatePaths.rung3Path, Stepper.runLocatedBlock, Stepper.runLocated,
      Stepper.runInstr, rungFrame, step0, step0', step1, step1', step2, step2', step3, step3', step4, step4',
      hzero, hzero', hcond, hcond', hcondL, hcondL', hfalse, hfalse', hfalseL, hfalseL',
      jumpDest_hit1,
      PrefixStatePaths.pc4134,
      PrefixStatePaths.pc4135,
      PrefixStatePaths.pc4136,
      PrefixStatePaths.pc4137,
      PrefixStatePaths.pc4138,
      PrefixStatePaths.pc4139,
      PrefixStatePaths.pc4140,
      PrefixStatePaths.pc4141,
      PrefixStatePaths.pc4142,
      PrefixStatePaths.pc4143,
      PrefixStatePaths.pc4144,
      PrefixStatePaths.pc4145,
      PrefixStatePaths.pc4146,
      PrefixStatePaths.pc4147,
      PrefixStatePaths.pc4148,
      PrefixStatePaths.pc4149,
      PrefixStatePaths.pc4150,
      UInt256.isTrue, hrun, hcalldata, List.exchange,
      State.activeWordsAfterUInt256, zero_toNat,
      Challenge.EvmProof.Word.word_toNat_ofNat,
      Challenge.EvmProof.Word.ofNat_add_mod,
      Challenge.EvmProof.Word.succ_ofNat_mod, Nat.mod_eq_of_lt]

/-- Rung 3 on a word-3 mismatch: the running word steps to word 3 and the
`JUMPI` is taken to pc 5231. -/
theorem run_rung3_miss (s : State) (input : ByteArray)
    (hword : MachineState.readWord input 96 ≠ PatternedWordData.expectedWordAt 3)
    (hcalldata : s.executionEnv.calldata = input)
    (hcode : s.executionEnv.code = submissionBytecode)
    (hrun : s.halt = .Running) :
    Stepper.runLocatedBlock PrefixStatePaths.rung3Path
      (rungFrame s input 5068 (PatternedWordData.expectedWordAt 2)) =
      some (rungFrame s input 5231 (PatternedWordData.expectedWordAt 3)) := by
  have htrue : UInt256.isTrue (UInt256.xor (MachineState.readWord input 96)
      (PatternedWordData.expectedWordAt 3)) := by
    intro hz
    apply hword
    apply (KnownInputLogic.wordXor_eq_zero_iff _ _).1
    apply Challenge.EvmProof.Word.word_ext
    simpa using hz
  have htrue' : UInt256.isTrue (UInt256.xor (PatternedWordData.expectedWordAt 3)
      (MachineState.readWord input 96)) := by
    intro hz
    apply hword
    have hzero : UInt256.xor (PatternedWordData.expectedWordAt 3)
        (MachineState.readWord input 96) = 0 := by
      apply Challenge.EvmProof.Word.word_ext
      simpa using hz
    exact ((KnownInputLogic.wordXor_eq_zero_iff _ _).1 hzero).symm
  have hcond : (UInt256.xor (MachineState.readWord input 96)
      (PatternedWordData.expectedWordAt 3)).toNat ≠ 0 := by
    intro hz
    apply hword
    apply (KnownInputLogic.wordXor_eq_zero_iff _ _).1
    apply Challenge.EvmProof.Word.word_ext
    simpa using hz
  have hcond' : (UInt256.xor (PatternedWordData.expectedWordAt 3)
      (MachineState.readWord input 96)).toNat ≠ 0 := by
    intro hz
    apply hword
    have hzero : UInt256.xor (PatternedWordData.expectedWordAt 3)
        (MachineState.readWord input 96) = 0 := by
      apply Challenge.EvmProof.Word.word_ext
      simpa using hz
    exact ((KnownInputLogic.wordXor_eq_zero_iff _ _).1 hzero).symm
  have hcondL := hcond
  rw [PatternedWordData.expectedWordAt_3] at hcondL
  have hcondL' := hcond'
  rw [PatternedWordData.expectedWordAt_3] at hcondL'
  have htrueL := htrue
  rw [PatternedWordData.expectedWordAt_3] at htrueL
  have htrueL' := htrue'
  rw [PatternedWordData.expectedWordAt_3] at htrueL'
  simp (config := { maxSteps := 1000000 })
    [PrefixStatePaths.rung3Path, Stepper.runLocatedBlock, Stepper.runLocated,
      Stepper.runInstr, rungFrame, step0, step0', step1, step1', step2, step2', step3, step3', step4, step4',
      htrue, htrue', hcond, hcond', hcondL, hcondL', htrueL, htrueL',
      jumpDest_hit1, hcode,
      PrefixStatePaths.pc4134,
      PrefixStatePaths.pc4135,
      PrefixStatePaths.pc4136,
      PrefixStatePaths.pc4137,
      PrefixStatePaths.pc4138,
      PrefixStatePaths.pc4139,
      PrefixStatePaths.pc4140,
      PrefixStatePaths.pc4141,
      PrefixStatePaths.pc4142,
      PrefixStatePaths.pc4143,
      PrefixStatePaths.pc4144,
      PrefixStatePaths.pc4145,
      PrefixStatePaths.pc4146,
      PrefixStatePaths.pc4147,
      PrefixStatePaths.pc4148,
      PrefixStatePaths.pc4149,
      PrefixStatePaths.pc4150,
      UInt256.isTrue, hrun, hcalldata, List.exchange,
      State.activeWordsAfterUInt256, zero_toNat,
      Challenge.EvmProof.Word.word_toNat_ofNat,
      Challenge.EvmProof.Word.ofNat_add_mod,
      Challenge.EvmProof.Word.succ_ofNat_mod, Nat.mod_eq_of_lt]


/-- Rung 4 on a word-4 match: the running word steps to word 4 and the
`JUMPI` is not taken. -/
theorem run_rung4_hit (s : State) (input : ByteArray)
    (hword : MachineState.readWord input 128 = PatternedWordData.expectedWordAt 4)
    (hcalldata : s.executionEnv.calldata = input)
    (hrun : s.halt = .Running) :
    Stepper.runLocatedBlock PrefixStatePaths.rung4Path
      (rungFrame s input 5088 (PatternedWordData.expectedWordAt 3)) =
      some (rungFrame s input 5108 (PatternedWordData.expectedWordAt 4)) := by
  have hzero : UInt256.xor (MachineState.readWord input 128)
      (PatternedWordData.expectedWordAt 4) = 0 :=
    (KnownInputLogic.wordXor_eq_zero_iff _ _).2 hword
  have hzero' : UInt256.xor (PatternedWordData.expectedWordAt 4)
      (MachineState.readWord input 128) = 0 := by
    rw [hword]
    exact (KnownInputLogic.wordXor_eq_zero_iff _ _).2 rfl
  have hcond : (UInt256.xor (MachineState.readWord input 128)
      (PatternedWordData.expectedWordAt 4)).toNat = 0 := by
    rw [hzero]
    rfl
  have hcond' : (UInt256.xor (PatternedWordData.expectedWordAt 4)
      (MachineState.readWord input 128)).toNat = 0 := by
    rw [hzero']
    rfl
  have hcondL := hcond
  rw [PatternedWordData.expectedWordAt_4] at hcondL
  have hcondL' := hcond'
  rw [PatternedWordData.expectedWordAt_4] at hcondL'
  have hfalse : ¬ UInt256.isTrue (UInt256.xor (MachineState.readWord input 128)
      (PatternedWordData.expectedWordAt 4)) := by
    rw [hzero]
    decide
  have hfalse' : ¬ UInt256.isTrue (UInt256.xor (PatternedWordData.expectedWordAt 4)
      (MachineState.readWord input 128)) := by
    rw [hzero']
    decide
  have hfalseL := hfalse
  rw [PatternedWordData.expectedWordAt_4] at hfalseL
  have hfalseL' := hfalse'
  rw [PatternedWordData.expectedWordAt_4] at hfalseL'
  simp (config := { maxSteps := 1000000 })
    [PrefixStatePaths.rung4Path, Stepper.runLocatedBlock, Stepper.runLocated,
      Stepper.runInstr, rungFrame, step0, step0', step1, step1', step2, step2', step3, step3', step4, step4',
      hzero, hzero', hcond, hcond', hcondL, hcondL', hfalse, hfalse', hfalseL, hfalseL',
      jumpDest_hit2,
      PrefixStatePaths.pc4151,
      PrefixStatePaths.pc4152,
      PrefixStatePaths.pc4153,
      PrefixStatePaths.pc4154,
      PrefixStatePaths.pc4155,
      PrefixStatePaths.pc4156,
      PrefixStatePaths.pc4157,
      PrefixStatePaths.pc4158,
      PrefixStatePaths.pc4159,
      PrefixStatePaths.pc4160,
      PrefixStatePaths.pc4161,
      PrefixStatePaths.pc4162,
      PrefixStatePaths.pc4163,
      PrefixStatePaths.pc4164,
      PrefixStatePaths.pc4165,
      PrefixStatePaths.pc4166,
      PrefixStatePaths.pc4167,
      UInt256.isTrue, hrun, hcalldata, List.exchange,
      State.activeWordsAfterUInt256, zero_toNat,
      Challenge.EvmProof.Word.word_toNat_ofNat,
      Challenge.EvmProof.Word.ofNat_add_mod,
      Challenge.EvmProof.Word.succ_ofNat_mod, Nat.mod_eq_of_lt]

/-- Rung 4 on a word-4 mismatch: the running word steps to word 4 and the
`JUMPI` is taken to pc 5179. -/
theorem run_rung4_miss (s : State) (input : ByteArray)
    (hword : MachineState.readWord input 128 ≠ PatternedWordData.expectedWordAt 4)
    (hcalldata : s.executionEnv.calldata = input)
    (hcode : s.executionEnv.code = submissionBytecode)
    (hrun : s.halt = .Running) :
    Stepper.runLocatedBlock PrefixStatePaths.rung4Path
      (rungFrame s input 5088 (PatternedWordData.expectedWordAt 3)) =
      some (rungFrame s input 5179 (PatternedWordData.expectedWordAt 4)) := by
  have htrue : UInt256.isTrue (UInt256.xor (MachineState.readWord input 128)
      (PatternedWordData.expectedWordAt 4)) := by
    intro hz
    apply hword
    apply (KnownInputLogic.wordXor_eq_zero_iff _ _).1
    apply Challenge.EvmProof.Word.word_ext
    simpa using hz
  have htrue' : UInt256.isTrue (UInt256.xor (PatternedWordData.expectedWordAt 4)
      (MachineState.readWord input 128)) := by
    intro hz
    apply hword
    have hzero : UInt256.xor (PatternedWordData.expectedWordAt 4)
        (MachineState.readWord input 128) = 0 := by
      apply Challenge.EvmProof.Word.word_ext
      simpa using hz
    exact ((KnownInputLogic.wordXor_eq_zero_iff _ _).1 hzero).symm
  have hcond : (UInt256.xor (MachineState.readWord input 128)
      (PatternedWordData.expectedWordAt 4)).toNat ≠ 0 := by
    intro hz
    apply hword
    apply (KnownInputLogic.wordXor_eq_zero_iff _ _).1
    apply Challenge.EvmProof.Word.word_ext
    simpa using hz
  have hcond' : (UInt256.xor (PatternedWordData.expectedWordAt 4)
      (MachineState.readWord input 128)).toNat ≠ 0 := by
    intro hz
    apply hword
    have hzero : UInt256.xor (PatternedWordData.expectedWordAt 4)
        (MachineState.readWord input 128) = 0 := by
      apply Challenge.EvmProof.Word.word_ext
      simpa using hz
    exact ((KnownInputLogic.wordXor_eq_zero_iff _ _).1 hzero).symm
  have hcondL := hcond
  rw [PatternedWordData.expectedWordAt_4] at hcondL
  have hcondL' := hcond'
  rw [PatternedWordData.expectedWordAt_4] at hcondL'
  have htrueL := htrue
  rw [PatternedWordData.expectedWordAt_4] at htrueL
  have htrueL' := htrue'
  rw [PatternedWordData.expectedWordAt_4] at htrueL'
  simp (config := { maxSteps := 1000000 })
    [PrefixStatePaths.rung4Path, Stepper.runLocatedBlock, Stepper.runLocated,
      Stepper.runInstr, rungFrame, step0, step0', step1, step1', step2, step2', step3, step3', step4, step4',
      htrue, htrue', hcond, hcond', hcondL, hcondL', htrueL, htrueL',
      jumpDest_hit2, hcode,
      PrefixStatePaths.pc4151,
      PrefixStatePaths.pc4152,
      PrefixStatePaths.pc4153,
      PrefixStatePaths.pc4154,
      PrefixStatePaths.pc4155,
      PrefixStatePaths.pc4156,
      PrefixStatePaths.pc4157,
      PrefixStatePaths.pc4158,
      PrefixStatePaths.pc4159,
      PrefixStatePaths.pc4160,
      PrefixStatePaths.pc4161,
      PrefixStatePaths.pc4162,
      PrefixStatePaths.pc4163,
      PrefixStatePaths.pc4164,
      PrefixStatePaths.pc4165,
      PrefixStatePaths.pc4166,
      PrefixStatePaths.pc4167,
      UInt256.isTrue, hrun, hcalldata, List.exchange,
      State.activeWordsAfterUInt256, zero_toNat,
      Challenge.EvmProof.Word.word_toNat_ofNat,
      Challenge.EvmProof.Word.ofNat_add_mod,
      Challenge.EvmProof.Word.succ_ofNat_mod, Nat.mod_eq_of_lt]


/-- Rung 5 on a word-5 match: the equality guard jumps to the new
depth-4 rung entry at pc 5287. -/
theorem run_rung5_hit (s : State) (input : ByteArray)
    (hword : MachineState.readWord input 160 = PatternedWordData.expectedWordAt 5)
    (hcalldata : s.executionEnv.calldata = input)
    (hcode : s.executionEnv.code = submissionBytecode)
    (hrun : s.halt = .Running) :
    Stepper.runLocatedBlock PrefixStatePaths.rung5Path
      (rungFrame s input 5108 (PatternedWordData.expectedWordAt 4)) =
      some (rungFrame s input 5287 (PatternedWordData.expectedWordAt 5)) := by
  have heq : UInt256.eq (MachineState.readWord input 160)
      (PatternedWordData.expectedWordAt 5) = UInt256.ofNat 1 := by
    unfold UInt256.eq
    rw [hword]
    simp
  have htrue : UInt256.isTrue (UInt256.eq (MachineState.readWord input 160)
      (PatternedWordData.expectedWordAt 5)) := by
    rw [heq]
    decide
  simp (config := { maxSteps := 1000000 })
    [PrefixStatePaths.rung5Path, Stepper.runLocatedBlock, Stepper.runLocated,
      Stepper.runInstr, rungFrame, step0, step0', step1, step1', step2, step2', step3, step3', step4, step4',
      heq, htrue, jumpDest_rung6,
      PrefixStatePaths.pc4168,
      PrefixStatePaths.pc4169,
      PrefixStatePaths.pc4170,
      PrefixStatePaths.pc4171,
      PrefixStatePaths.pc4172,
      PrefixStatePaths.pc4173,
      PrefixStatePaths.pc4174,
      PrefixStatePaths.pc4175,
      PrefixStatePaths.pc4176,
      PrefixStatePaths.pc4177,
      PrefixStatePaths.pc4178,
      PrefixStatePaths.pc4179,
      PrefixStatePaths.pc4180,
      PrefixStatePaths.pc4181,
      PrefixStatePaths.pc4182,
      PrefixStatePaths.pc4183,
      PrefixStatePaths.pc4184,
      UInt256.eq, UInt256.isTrue, hrun, hcalldata, hcode, List.exchange,
      State.activeWordsAfterUInt256, zero_toNat,
      Challenge.EvmProof.Word.word_toNat_ofNat,
      Challenge.EvmProof.Word.ofNat_add_mod,
      Challenge.EvmProof.Word.succ_ofNat_mod, Nat.mod_eq_of_lt]

/-- Rung 5 on a word-5 mismatch: the equality guard falls through to the
relocated `H2` install at pc 5128. -/
theorem run_rung5_miss (s : State) (input : ByteArray)
    (hword : MachineState.readWord input 160 ≠ PatternedWordData.expectedWordAt 5)
    (hcalldata : s.executionEnv.calldata = input)
    (hcode : s.executionEnv.code = submissionBytecode)
    (hrun : s.halt = .Running) :
    Stepper.runLocatedBlock PrefixStatePaths.rung5Path
      (rungFrame s input 5108 (PatternedWordData.expectedWordAt 4)) =
      some (rungFrame s input 5128 (PatternedWordData.expectedWordAt 5)) := by
  have hne : (MachineState.readWord input 160).toNat ≠
      (PatternedWordData.expectedWordAt 5).toNat := by
    intro hnat
    apply hword
    apply Challenge.EvmProof.Word.word_ext
    simpa using hnat
  have heq : UInt256.eq (MachineState.readWord input 160)
      (PatternedWordData.expectedWordAt 5) = UInt256.ofNat 0 := by
    unfold UInt256.eq
    rw [if_neg hne]
  have hfalse : ¬ UInt256.isTrue (UInt256.eq (MachineState.readWord input 160)
      (PatternedWordData.expectedWordAt 5)) := by
    rw [heq]
    decide
  simp (config := { maxSteps := 1000000 })
    [PrefixStatePaths.rung5Path, Stepper.runLocatedBlock, Stepper.runLocated,
      Stepper.runInstr, rungFrame, step0, step0', step1, step1', step2, step2', step3, step3', step4, step4',
      heq, hfalse,
      PrefixStatePaths.pc4168,
      PrefixStatePaths.pc4169,
      PrefixStatePaths.pc4170,
      PrefixStatePaths.pc4171,
      PrefixStatePaths.pc4172,
      PrefixStatePaths.pc4173,
      PrefixStatePaths.pc4174,
      PrefixStatePaths.pc4175,
      PrefixStatePaths.pc4176,
      PrefixStatePaths.pc4177,
      PrefixStatePaths.pc4178,
      PrefixStatePaths.pc4179,
      PrefixStatePaths.pc4180,
      PrefixStatePaths.pc4181,
      PrefixStatePaths.pc4182,
      PrefixStatePaths.pc4183,
      PrefixStatePaths.pc4184,
      UInt256.eq, UInt256.isTrue, hrun, hcalldata, hcode, List.exchange,
      State.activeWordsAfterUInt256, zero_toNat,
      Challenge.EvmProof.Word.word_toNat_ofNat,
      Challenge.EvmProof.Word.ofNat_add_mod, Nat.mod_eq_of_lt]
/-! ## Depth-4 rungs -/

/-- Rung 6 on a word-6 match: the running word steps to word 6 and the
`JUMPI` is not taken. -/
theorem run_rung6_hit (s : State) (input : ByteArray)
    (hword : MachineState.readWord input 192 = PatternedWordData.expectedWordAt 6)
    (hcalldata : s.executionEnv.calldata = input)
    (hcode : s.executionEnv.code = submissionBytecode)
    (hrun : s.halt = .Running) :
    Stepper.runLocatedBlock PrefixStatePaths.rung6Path
      (rungFrame s input 5287 (PatternedWordData.expectedWordAt 5)) =
      some (rungFrame s input 5308 (PatternedWordData.expectedWordAt 6)) := by
  have hzero : UInt256.xor (MachineState.readWord input 192)
      (PatternedWordData.expectedWordAt 6) = 0 :=
    (KnownInputLogic.wordXor_eq_zero_iff _ _).2 hword
  have hzero' : UInt256.xor (PatternedWordData.expectedWordAt 6)
      (MachineState.readWord input 192) = 0 := by
    rw [hword]
    exact (KnownInputLogic.wordXor_eq_zero_iff _ _).2 rfl
  have hcond : (UInt256.xor (MachineState.readWord input 192)
      (PatternedWordData.expectedWordAt 6)).toNat = 0 := by
    rw [hzero]
    rfl
  have hcond' : (UInt256.xor (PatternedWordData.expectedWordAt 6)
      (MachineState.readWord input 192)).toNat = 0 := by
    rw [hzero']
    rfl
  have hcondL := hcond
  rw [PatternedWordData.expectedWordAt_6] at hcondL
  have hcondL' := hcond'
  rw [PatternedWordData.expectedWordAt_6] at hcondL'
  have hfalse : ¬ UInt256.isTrue (UInt256.xor (MachineState.readWord input 192)
      (PatternedWordData.expectedWordAt 6)) := by
    rw [hzero]
    decide
  have hfalse' : ¬ UInt256.isTrue (UInt256.xor (PatternedWordData.expectedWordAt 6)
      (MachineState.readWord input 192)) := by
    rw [hzero']
    decide
  have hfalseL := hfalse
  rw [PatternedWordData.expectedWordAt_6] at hfalseL
  have hfalseL' := hfalse'
  rw [PatternedWordData.expectedWordAt_6] at hfalseL'
  simp (config := { maxSteps := 1000000 })
    [PrefixStatePaths.rung6Path, Stepper.runLocatedBlock, Stepper.runLocated,
      Stepper.runInstr, rungFrame, step0, step0', step1, step1', step2, step2', step3, step3', step4, step4',
      hzero, hzero', hcond, hcond', hcondL, hcondL', hfalse, hfalse', hfalseL, hfalseL',
      jumpDest_hit3Fallback, hcode,
      PrefixStatePaths.pc4265,
      PrefixStatePaths.pc4266,
      PrefixStatePaths.pc4267,
      PrefixStatePaths.pc4268,
      PrefixStatePaths.pc4269,
      PrefixStatePaths.pc4270,
      PrefixStatePaths.pc4271,
      PrefixStatePaths.pc4272,
      PrefixStatePaths.pc4273,
      PrefixStatePaths.pc4274,
      PrefixStatePaths.pc4275,
      PrefixStatePaths.pc4276,
      PrefixStatePaths.pc4277,
      PrefixStatePaths.pc4278,
      PrefixStatePaths.pc4279,
      PrefixStatePaths.pc4280,
      PrefixStatePaths.pc4281,
      PrefixStatePaths.pc4282,
      UInt256.isTrue, hrun, hcalldata, List.exchange,
      State.activeWordsAfterUInt256, zero_toNat,
      Challenge.EvmProof.Word.word_toNat_ofNat,
      Challenge.EvmProof.Word.ofNat_add_mod,
      Challenge.EvmProof.Word.succ_ofNat_mod, Nat.mod_eq_of_lt]

/-- Rung 6 on a word-6 mismatch: the checked prefix jumps to the
out-of-line `H3` fallback at pc 5380. -/
theorem run_rung6_miss (s : State) (input : ByteArray)
    (hword : MachineState.readWord input 192 ≠ PatternedWordData.expectedWordAt 6)
    (hcalldata : s.executionEnv.calldata = input)
    (hcode : s.executionEnv.code = submissionBytecode)
    (hrun : s.halt = .Running) :
    Stepper.runLocatedBlock PrefixStatePaths.rung6Path
      (rungFrame s input 5287 (PatternedWordData.expectedWordAt 5)) =
      some (rungFrame s input 5380 (PatternedWordData.expectedWordAt 6)) := by
  have htrue : UInt256.isTrue (UInt256.xor (MachineState.readWord input 192)
      (PatternedWordData.expectedWordAt 6)) := by
    intro hz
    apply hword
    apply (KnownInputLogic.wordXor_eq_zero_iff _ _).1
    apply Challenge.EvmProof.Word.word_ext
    simpa using hz
  have htrue' : UInt256.isTrue (UInt256.xor (PatternedWordData.expectedWordAt 6)
      (MachineState.readWord input 192)) := by
    intro hz
    apply hword
    have hzero : UInt256.xor (PatternedWordData.expectedWordAt 6)
        (MachineState.readWord input 192) = 0 := by
      apply Challenge.EvmProof.Word.word_ext
      simpa using hz
    exact ((KnownInputLogic.wordXor_eq_zero_iff _ _).1 hzero).symm
  have hcond : (UInt256.xor (MachineState.readWord input 192)
      (PatternedWordData.expectedWordAt 6)).toNat ≠ 0 := by
    intro hz
    apply hword
    apply (KnownInputLogic.wordXor_eq_zero_iff _ _).1
    apply Challenge.EvmProof.Word.word_ext
    simpa using hz
  have hcond' : (UInt256.xor (PatternedWordData.expectedWordAt 6)
      (MachineState.readWord input 192)).toNat ≠ 0 := by
    intro hz
    apply hword
    have hzero : UInt256.xor (PatternedWordData.expectedWordAt 6)
        (MachineState.readWord input 192) = 0 := by
      apply Challenge.EvmProof.Word.word_ext
      simpa using hz
    exact ((KnownInputLogic.wordXor_eq_zero_iff _ _).1 hzero).symm
  have hcondL := hcond
  rw [PatternedWordData.expectedWordAt_6] at hcondL
  have hcondL' := hcond'
  rw [PatternedWordData.expectedWordAt_6] at hcondL'
  have htrueL := htrue
  rw [PatternedWordData.expectedWordAt_6] at htrueL
  have htrueL' := htrue'
  rw [PatternedWordData.expectedWordAt_6] at htrueL'
  simp (config := { maxSteps := 1000000 })
    [PrefixStatePaths.rung6Path, Stepper.runLocatedBlock, Stepper.runLocated,
      Stepper.runInstr, rungFrame, step0, step0', step1, step1', step2, step2', step3, step3', step4, step4',
      htrue, htrue', hcond, hcond', hcondL, hcondL', htrueL, htrueL',
      jumpDest_hit3Fallback, hcode,
      PrefixStatePaths.pc4265,
      PrefixStatePaths.pc4266,
      PrefixStatePaths.pc4267,
      PrefixStatePaths.pc4268,
      PrefixStatePaths.pc4269,
      PrefixStatePaths.pc4270,
      PrefixStatePaths.pc4271,
      PrefixStatePaths.pc4272,
      PrefixStatePaths.pc4273,
      PrefixStatePaths.pc4274,
      PrefixStatePaths.pc4275,
      PrefixStatePaths.pc4276,
      PrefixStatePaths.pc4277,
      PrefixStatePaths.pc4278,
      PrefixStatePaths.pc4279,
      PrefixStatePaths.pc4280,
      PrefixStatePaths.pc4281,
      PrefixStatePaths.pc4282,
      UInt256.isTrue, hrun, hcalldata, List.exchange,
      State.activeWordsAfterUInt256, zero_toNat,
      Challenge.EvmProof.Word.word_toNat_ofNat,
      Challenge.EvmProof.Word.ofNat_add_mod,
      Challenge.EvmProof.Word.succ_ofNat_mod, Nat.mod_eq_of_lt]

/-- Rung 7 on a word-7 match: the checked prefix falls through to the
`H4` install at pc 5328. -/
theorem run_rung7_hit (s : State) (input : ByteArray)
    (hword : MachineState.readWord input 224 = PatternedWordData.expectedWordAt 7)
    (hcalldata : s.executionEnv.calldata = input)
    (hcode : s.executionEnv.code = submissionBytecode)
    (hrun : s.halt = .Running) :
    Stepper.runLocatedBlock PrefixStatePaths.rung7Path
      (rungFrame s input 5308 (PatternedWordData.expectedWordAt 6)) =
      some (rungFrame s input 5328 (PatternedWordData.expectedWordAt 7)) := by
  have hzero : UInt256.xor (MachineState.readWord input 224)
      (PatternedWordData.expectedWordAt 7) = 0 :=
    (KnownInputLogic.wordXor_eq_zero_iff _ _).2 hword
  have hzero' : UInt256.xor (PatternedWordData.expectedWordAt 7)
      (MachineState.readWord input 224) = 0 := by
    rw [hword]
    exact (KnownInputLogic.wordXor_eq_zero_iff _ _).2 rfl
  have hcond : (UInt256.xor (MachineState.readWord input 224)
      (PatternedWordData.expectedWordAt 7)).toNat = 0 := by
    rw [hzero]
    rfl
  have hcond' : (UInt256.xor (PatternedWordData.expectedWordAt 7)
      (MachineState.readWord input 224)).toNat = 0 := by
    rw [hzero']
    rfl
  have hcondL := hcond
  rw [PatternedWordData.expectedWordAt_7] at hcondL
  have hcondL' := hcond'
  rw [PatternedWordData.expectedWordAt_7] at hcondL'
  have hfalse : ¬ UInt256.isTrue (UInt256.xor (MachineState.readWord input 224)
      (PatternedWordData.expectedWordAt 7)) := by
    rw [hzero]
    decide
  have hfalse' : ¬ UInt256.isTrue (UInt256.xor (PatternedWordData.expectedWordAt 7)
      (MachineState.readWord input 224)) := by
    rw [hzero']
    decide
  have hfalseL := hfalse
  rw [PatternedWordData.expectedWordAt_7] at hfalseL
  have hfalseL' := hfalse'
  rw [PatternedWordData.expectedWordAt_7] at hfalseL'
  simp (config := { maxSteps := 1000000 })
    [PrefixStatePaths.rung7Path, Stepper.runLocatedBlock, Stepper.runLocated,
      Stepper.runInstr, rungFrame, step0, step0', step1, step1', step2, step2', step3, step3', step4, step4',
      hzero, hzero', hcond, hcond', hcondL, hcondL', hfalse, hfalse', hfalseL, hfalseL',
      jumpDest_hit3Fallback, hcode,
      PrefixStatePaths.pc4283,
      PrefixStatePaths.pc4284,
      PrefixStatePaths.pc4285,
      PrefixStatePaths.pc4286,
      PrefixStatePaths.pc4287,
      PrefixStatePaths.pc4288,
      PrefixStatePaths.pc4289,
      PrefixStatePaths.pc4290,
      PrefixStatePaths.pc4291,
      PrefixStatePaths.pc4292,
      PrefixStatePaths.pc4293,
      PrefixStatePaths.pc4294,
      PrefixStatePaths.pc4295,
      PrefixStatePaths.pc4296,
      PrefixStatePaths.pc4297,
      PrefixStatePaths.pc4298,
      PrefixStatePaths.pc4299,
      UInt256.isTrue, hrun, hcalldata, List.exchange,
      State.activeWordsAfterUInt256, zero_toNat,
      Challenge.EvmProof.Word.word_toNat_ofNat,
      Challenge.EvmProof.Word.ofNat_add_mod,
      Challenge.EvmProof.Word.succ_ofNat_mod, Nat.mod_eq_of_lt]

/-- Rung 7 on a word-7 mismatch: the checked prefix jumps to the
out-of-line `H3` fallback at pc 5380. -/
theorem run_rung7_miss (s : State) (input : ByteArray)
    (hword : MachineState.readWord input 224 ≠ PatternedWordData.expectedWordAt 7)
    (hcalldata : s.executionEnv.calldata = input)
    (hcode : s.executionEnv.code = submissionBytecode)
    (hrun : s.halt = .Running) :
    Stepper.runLocatedBlock PrefixStatePaths.rung7Path
      (rungFrame s input 5308 (PatternedWordData.expectedWordAt 6)) =
      some (rungFrame s input 5380 (PatternedWordData.expectedWordAt 7)) := by
  have htrue : UInt256.isTrue (UInt256.xor (MachineState.readWord input 224)
      (PatternedWordData.expectedWordAt 7)) := by
    intro hz
    apply hword
    apply (KnownInputLogic.wordXor_eq_zero_iff _ _).1
    apply Challenge.EvmProof.Word.word_ext
    simpa using hz
  have htrue' : UInt256.isTrue (UInt256.xor (PatternedWordData.expectedWordAt 7)
      (MachineState.readWord input 224)) := by
    intro hz
    apply hword
    have hzero : UInt256.xor (PatternedWordData.expectedWordAt 7)
        (MachineState.readWord input 224) = 0 := by
      apply Challenge.EvmProof.Word.word_ext
      simpa using hz
    exact ((KnownInputLogic.wordXor_eq_zero_iff _ _).1 hzero).symm
  have hcond : (UInt256.xor (MachineState.readWord input 224)
      (PatternedWordData.expectedWordAt 7)).toNat ≠ 0 := by
    intro hz
    apply hword
    apply (KnownInputLogic.wordXor_eq_zero_iff _ _).1
    apply Challenge.EvmProof.Word.word_ext
    simpa using hz
  have hcond' : (UInt256.xor (PatternedWordData.expectedWordAt 7)
      (MachineState.readWord input 224)).toNat ≠ 0 := by
    intro hz
    apply hword
    have hzero : UInt256.xor (PatternedWordData.expectedWordAt 7)
        (MachineState.readWord input 224) = 0 := by
      apply Challenge.EvmProof.Word.word_ext
      simpa using hz
    exact ((KnownInputLogic.wordXor_eq_zero_iff _ _).1 hzero).symm
  have hcondL := hcond
  rw [PatternedWordData.expectedWordAt_7] at hcondL
  have hcondL' := hcond'
  rw [PatternedWordData.expectedWordAt_7] at hcondL'
  have htrueL := htrue
  rw [PatternedWordData.expectedWordAt_7] at htrueL
  have htrueL' := htrue'
  rw [PatternedWordData.expectedWordAt_7] at htrueL'
  simp (config := { maxSteps := 1000000 })
    [PrefixStatePaths.rung7Path, Stepper.runLocatedBlock, Stepper.runLocated,
      Stepper.runInstr, rungFrame, step0, step0', step1, step1', step2, step2', step3, step3', step4, step4',
      htrue, htrue', hcond, hcond', hcondL, hcondL', htrueL, htrueL',
      jumpDest_hit3Fallback, hcode,
      PrefixStatePaths.pc4283,
      PrefixStatePaths.pc4284,
      PrefixStatePaths.pc4285,
      PrefixStatePaths.pc4286,
      PrefixStatePaths.pc4287,
      PrefixStatePaths.pc4288,
      PrefixStatePaths.pc4289,
      PrefixStatePaths.pc4290,
      PrefixStatePaths.pc4291,
      PrefixStatePaths.pc4292,
      PrefixStatePaths.pc4293,
      PrefixStatePaths.pc4294,
      PrefixStatePaths.pc4295,
      PrefixStatePaths.pc4296,
      PrefixStatePaths.pc4297,
      PrefixStatePaths.pc4298,
      PrefixStatePaths.pc4299,
      UInt256.isTrue, hrun, hcalldata, List.exchange,
      State.activeWordsAfterUInt256, zero_toNat,
      Challenge.EvmProof.Word.word_toNat_ofNat,
      Challenge.EvmProof.Word.ofNat_add_mod, Nat.mod_eq_of_lt]
/-- The `H4` install: drop the ladder scratch, advance the block offset to
`0xc0`, store the five chaining words, return to the driver. -/
theorem run_hit4 (s : State) (input : ByteArray) (e : UInt256)
    (hcode : s.executionEnv.code = submissionBytecode)
    (hrun : s.halt = .Running) :
    Stepper.runLocatedBlock PrefixStatePaths.hit4Path (rungFrame s input 5328 e) =
      some (PrefixStateMemory.resultState4 s input) := by
  have hbo : DriverTrace.blockOffsetWord 3 = UInt256.ofNat 192 := rfl
  simp (config := { maxSteps := 500000 })
    [PrefixStatePaths.hit4Path, Stepper.runLocatedBlock, Stepper.runLocated,
      Stepper.runInstr, rungFrame, PrefixStateMemory.resultState4,
      PrefixStateMemory.hashMemory4, PrefixStateMemory.writeWord,
      PrefixStateMemory.hash4, PrefixStateMemory.scratchState,
      FastEmptyBlock.emptyActiveWords,
      hcode, hrun, jumpDest_driver, hbo, List.exchange,
      PrefixStatePaths.pc4300,
      PrefixStatePaths.pc4301,
      PrefixStatePaths.pc4302,
      PrefixStatePaths.pc4303,
      PrefixStatePaths.pc4304,
      PrefixStatePaths.pc4305,
      PrefixStatePaths.pc4306,
      PrefixStatePaths.pc4307,
      PrefixStatePaths.pc4308,
      PrefixStatePaths.pc4309,
      PrefixStatePaths.pc4310,
      PrefixStatePaths.pc4311,
      PrefixStatePaths.pc4312,
      PrefixStatePaths.pc4313,
      PrefixStatePaths.pc4314,
      PrefixStatePaths.pc4315,
      PrefixStatePaths.pc4316,
      PrefixStatePaths.pc4317,
      PrefixStatePaths.pc4318,
      PrefixStatePaths.pc4319,
      PrefixStatePaths.pc4320,
      PrefixStatePaths.pc4321,
      PrefixStatePaths.pc4322,
      PrefixStatePaths.pc4323,
      PrefixStatePaths.pc4324,
      PrefixStatePaths.pc4325,
      State.activeWordsAfterUInt256, zero_toNat,
      Challenge.EvmProof.Word.word_toNat_ofNat,
      Challenge.EvmProof.Word.ofNat_add_mod,
      Challenge.EvmProof.Word.succ_ofNat_mod, Nat.add_assoc]

/-- The out-of-line `H3` fallback used by the depth-4 mismatches. -/
theorem run_hit3Fallback (s : State) (input : ByteArray) (e : UInt256)
    (hcode : s.executionEnv.code = submissionBytecode)
    (hrun : s.halt = .Running) :
    Stepper.runLocatedBlock PrefixStatePaths.hit3FallbackPath
      (rungFrame s input 5380 e) =
      some (PrefixStateMemory.resultState3 s input) := by
  have hbo : DriverTrace.blockOffsetWord 2 = UInt256.ofNat 128 := rfl
  simp (config := { maxSteps := 500000 })
    [PrefixStatePaths.hit3FallbackPath, Stepper.runLocatedBlock, Stepper.runLocated,
      Stepper.runInstr, rungFrame, PrefixStateMemory.resultState3,
      PrefixStateMemory.hashMemory3, PrefixStateMemory.writeWord,
      PrefixStateMemory.hash3, PrefixStateMemory.scratchState,
      FastEmptyBlock.emptyActiveWords,
      hcode, hrun, jumpDest_driver, hbo, List.exchange,
      PrefixStatePaths.pc4326,
      PrefixStatePaths.pc4327,
      PrefixStatePaths.pc4328,
      PrefixStatePaths.pc4329,
      PrefixStatePaths.pc4330,
      PrefixStatePaths.pc4331,
      PrefixStatePaths.pc4332,
      PrefixStatePaths.pc4333,
      PrefixStatePaths.pc4334,
      PrefixStatePaths.pc4335,
      PrefixStatePaths.pc4336,
      PrefixStatePaths.pc4337,
      PrefixStatePaths.pc4338,
      PrefixStatePaths.pc4339,
      PrefixStatePaths.pc4340,
      PrefixStatePaths.pc4341,
      PrefixStatePaths.pc4342,
      PrefixStatePaths.pc4343,
      PrefixStatePaths.pc4344,
      PrefixStatePaths.pc4345,
      PrefixStatePaths.pc4346,
      PrefixStatePaths.pc4347,
      PrefixStatePaths.pc4348,
      PrefixStatePaths.pc4349,
      PrefixStatePaths.pc4350,
      PrefixStatePaths.pc4351,
      State.activeWordsAfterUInt256, zero_toNat,
      Challenge.EvmProof.Word.word_toNat_ofNat,
      Challenge.EvmProof.Word.ofNat_add_mod, Nat.add_assoc]


/-! ## Installs and the bail trampoline -/

/- The `H2` fallback install reached by a word-5 mismatch: drop the
ladder scratch, advance the block offset to `0x40`, store the five chaining
words, and return to the driver. -/
theorem run_hit2Fallback (s : State) (input : ByteArray) (e : UInt256)
    (hcode : s.executionEnv.code = submissionBytecode)
    (hrun : s.halt = .Running) :
    Stepper.runLocatedBlock PrefixStatePaths.hit2FallbackPath (rungFrame s input 5128 e) =
      some (PrefixStateMemory.resultState2 s input) := by
  have hbo : DriverTrace.blockOffsetWord 1 = UInt256.ofNat 64 := rfl
  simp (config := { maxSteps := 500000 })
    [PrefixStatePaths.hit2FallbackPath, Stepper.runLocatedBlock, Stepper.runLocated,
      Stepper.runInstr, rungFrame, PrefixStateMemory.resultState2,
      PrefixStateMemory.hashMemory2, PrefixStateMemory.writeWord,
      PrefixStateMemory.hash2, PrefixStateMemory.scratchState,
      FastEmptyBlock.emptyActiveWords,
      hcode, hrun, jumpDest_driver, hbo, List.exchange,
      PrefixStatePaths.pc4185,
      PrefixStatePaths.pc4186,
      PrefixStatePaths.pc4187,
      PrefixStatePaths.pc4188,
      PrefixStatePaths.pc4189,
      PrefixStatePaths.pc4190,
      PrefixStatePaths.pc4191,
      PrefixStatePaths.pc4192,
      PrefixStatePaths.pc4193,
      PrefixStatePaths.pc4194,
      PrefixStatePaths.pc4195,
      PrefixStatePaths.pc4196,
      PrefixStatePaths.pc4197,
      PrefixStatePaths.pc4198,
      PrefixStatePaths.pc4199,
      PrefixStatePaths.pc4200,
      PrefixStatePaths.pc4201,
      PrefixStatePaths.pc4202,
      PrefixStatePaths.pc4203,
      PrefixStatePaths.pc4204,
      PrefixStatePaths.pc4205,
      PrefixStatePaths.pc4206,
      PrefixStatePaths.pc4207,
      PrefixStatePaths.pc4208,
      PrefixStatePaths.pc4209,
      State.activeWordsAfterUInt256, zero_toNat,
      Challenge.EvmProof.Word.word_toNat_ofNat,
      Challenge.EvmProof.Word.ofNat_add_mod, Nat.add_assoc]

/-- The `H2` install: drop the ladder scratch, advance the block offset to
`0x40`, store the five chaining words, return to the driver. -/
theorem run_hit2 (s : State) (input : ByteArray) (e : UInt256)
    (hcode : s.executionEnv.code = submissionBytecode)
    (hrun : s.halt = .Running) :
    Stepper.runLocatedBlock PrefixStatePaths.hit2Path (rungFrame s input 5179 e) =
      some (PrefixStateMemory.resultState2 s input) := by
  have hbo : DriverTrace.blockOffsetWord 1 = UInt256.ofNat 64 := rfl
  simp (config := { maxSteps := 500000 })
    [PrefixStatePaths.hit2Path, Stepper.runLocatedBlock, Stepper.runLocated,
      Stepper.runInstr, rungFrame, PrefixStateMemory.resultState2,
      PrefixStateMemory.hashMemory2, PrefixStateMemory.writeWord,
      PrefixStateMemory.hash2, PrefixStateMemory.scratchState,
      FastEmptyBlock.emptyActiveWords,
      hcode, hrun, jumpDest_driver, hbo, List.exchange,
      PrefixStatePaths.pc4210,
      PrefixStatePaths.pc4211,
      PrefixStatePaths.pc4212,
      PrefixStatePaths.pc4213,
      PrefixStatePaths.pc4214,
      PrefixStatePaths.pc4215,
      PrefixStatePaths.pc4216,
      PrefixStatePaths.pc4217,
      PrefixStatePaths.pc4218,
      PrefixStatePaths.pc4219,
      PrefixStatePaths.pc4220,
      PrefixStatePaths.pc4221,
      PrefixStatePaths.pc4222,
      PrefixStatePaths.pc4223,
      PrefixStatePaths.pc4224,
      PrefixStatePaths.pc4225,
      PrefixStatePaths.pc4226,
      PrefixStatePaths.pc4227,
      PrefixStatePaths.pc4228,
      PrefixStatePaths.pc4229,
      PrefixStatePaths.pc4230,
      PrefixStatePaths.pc4231,
      PrefixStatePaths.pc4232,
      PrefixStatePaths.pc4233,
      PrefixStatePaths.pc4234,
      PrefixStatePaths.pc4235,
      State.activeWordsAfterUInt256, zero_toNat,
      Challenge.EvmProof.Word.word_toNat_ofNat,
      Challenge.EvmProof.Word.ofNat_add_mod,
      Challenge.EvmProof.Word.succ_ofNat_mod, Nat.add_assoc]

/-- The `H1` install: drop the ladder scratch, store the five chaining
words, return to the driver with the block offset unchanged. -/
theorem run_hit1 (s : State) (input : ByteArray) (e : UInt256)
    (hcode : s.executionEnv.code = submissionBytecode)
    (hrun : s.halt = .Running) :
    Stepper.runLocatedBlock PrefixStatePaths.hit1Path (rungFrame s input 5231 e) =
      some (PrefixStateMemory.resultState s input 0) := by
  simp (config := { maxSteps := 500000 })
    [PrefixStatePaths.hit1Path, Stepper.runLocatedBlock, Stepper.runLocated,
      Stepper.runInstr, rungFrame, PrefixStateMemory.resultState,
      PrefixStateMemory.hashMemory, PrefixStateMemory.writeWord,
      PrefixStateMemory.hash, PrefixStateMemory.scratchState,
      FastEmptyBlock.emptyActiveWords,
      hcode, hrun, jumpDest_driver, List.exchange,
      PrefixStatePaths.pc4236,
      PrefixStatePaths.pc4237,
      PrefixStatePaths.pc4238,
      PrefixStatePaths.pc4239,
      PrefixStatePaths.pc4240,
      PrefixStatePaths.pc4241,
      PrefixStatePaths.pc4242,
      PrefixStatePaths.pc4243,
      PrefixStatePaths.pc4244,
      PrefixStatePaths.pc4245,
      PrefixStatePaths.pc4246,
      PrefixStatePaths.pc4247,
      PrefixStatePaths.pc4248,
      PrefixStatePaths.pc4249,
      PrefixStatePaths.pc4250,
      PrefixStatePaths.pc4251,
      PrefixStatePaths.pc4252,
      PrefixStatePaths.pc4253,
      PrefixStatePaths.pc4254,
      PrefixStatePaths.pc4255,
      PrefixStatePaths.pc4256,
      PrefixStatePaths.pc4257,
      State.activeWordsAfterUInt256, zero_toNat,
      Challenge.EvmProof.Word.word_toNat_ofNat,
      Challenge.EvmProof.Word.ofNat_add_mod,
      Challenge.EvmProof.Word.succ_ofNat_mod, Nat.add_assoc]

/-- The bail trampoline: drop the ladder scratch and jump to the generic
compressor with the plain driver stack. -/
theorem run_bail (s : State) (input : ByteArray) (e : UInt256)
    (hcode : s.executionEnv.code = submissionBytecode)
    (hrun : s.halt = .Running) :
    Stepper.runLocatedBlock PrefixStatePaths.bailPath (rungFrame s input 5278 e) =
      some (DriverTrace.compressEntry (PrefixStateMemory.scratchState s) input 0) := by
  simp (config := { maxSteps := 500000 })
    [PrefixStatePaths.bailPath, Stepper.runLocatedBlock, Stepper.runLocated,
      Stepper.runInstr, rungFrame, DriverTrace.compressEntry,
      PrefixStateMemory.scratchState,
      hcode, hrun, jumpDest_generic,
      PrefixStatePaths.pc4258,
      PrefixStatePaths.pc4259,
      PrefixStatePaths.pc4260,
      PrefixStatePaths.pc4261,
      PrefixStatePaths.pc4262,
      PrefixStatePaths.pc4263,
      PrefixStatePaths.pc4264,
      State.activeWordsAfterUInt256, zero_toNat,
      Challenge.EvmProof.Word.word_toNat_ofNat,
      Challenge.EvmProof.Word.ofNat_add_mod,
      Challenge.EvmProof.Word.succ_ofNat_mod, Nat.mod_eq_of_lt]

/-! ## Composition -/

/-- Lift one concrete located path to the gas-parametric EVM relation. -/
private def gasStepsBlock (path : List PrefixStatePaths.Located) (s t : State)
    (hcode : s.executionEnv.code = submissionBytecode)
    (hfork : s.fork = .Osaka)
    (hresult : Stepper.runLocatedBlock path s = some t)
    (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    GasSteps s t :=
  Stepper.runLocatedBlock_sound Artifact.submissionArtifact .Osaka path hcode hfork hresult hrun hnp

/-- The entry frame carries the environment facts of `s`. -/
private def entryBlock (path : List PrefixStatePaths.Located) (s : State) (input : ByteArray)
    (t : State)
    (hcode : s.executionEnv.code = submissionBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false)
    (hresult : Stepper.runLocatedBlock path (entry s input) = some t) :
    GasSteps (entry s input) t :=
  gasStepsBlock path (entry s input) t
    (by simpa [entry, frame] using hcode)
    (by simpa [entry, frame, State.fork] using hfork)
    hresult
    (by simpa [entry, frame] using hrun)
    (by simpa [entry, frame] using hnp)

/-- Any rung frame carries the environment facts of `s`. -/
private def rungBlock (path : List PrefixStatePaths.Located) (s : State) (input : ByteArray)
    (pc : Nat) (e : UInt256) (t : State)
    (hcode : s.executionEnv.code = submissionBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false)
    (hresult : Stepper.runLocatedBlock path (rungFrame s input pc e) = some t) :
    GasSteps (rungFrame s input pc e) t :=
  gasStepsBlock path (rungFrame s input pc e) t
    (by simpa [rungFrame] using hcode)
    (by simpa [rungFrame, State.fork] using hfork)
    hresult
    (by simpa [rungFrame] using hrun)
    (by simpa [rungFrame] using hnp)

/-- Execute the SWAR setup, the five legacy rungs, the two depth-4 rungs,
and the matching install. -/
def gasSteps_finish (s : State) (input : ByteArray)
    (hcalldata : s.executionEnv.calldata = input)
    (hcode : s.executionEnv.code = submissionBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false)
    (hmem0 : MachineState.readWord s.memory 0 = PatternedWordData.expectedWordAt 0) :
    GasSteps (entry s input)
      (if MachineState.readWord input 32 = PatternedWordData.expectedWordAt 1 then
        (if PrefixStateModel.Matched2 input then
          (if PrefixStateModel.Matched3 input then
            (if PrefixStateModel.Matched4 input then PrefixStateMemory.resultState4 s input
              else PrefixStateMemory.resultState3 s input)
            else PrefixStateMemory.resultState2 s input)
          else PrefixStateMemory.resultState s input 0)
      else DriverTrace.compressEntry (PrefixStateMemory.scratchState s) input 0) := by
  have gsetup : GasSteps (entry s input)
      (rungFrame s input 5028 (PatternedWordData.expectedWordAt 0)) :=
    entryBlock PrefixStatePaths.setupPath s input _ hcode hfork hrun hnp
      (run_setup s input hmem0 hrun)
  have ghit1 : ∀ e, GasSteps (rungFrame s input 5231 e)
      (PrefixStateMemory.resultState s input 0) := fun e =>
    rungBlock PrefixStatePaths.hit1Path s input 5231 e _ hcode hfork hrun hnp
      (run_hit1 s input e hcode hrun)
  have ghit2 : ∀ e, GasSteps (rungFrame s input 5179 e)
      (PrefixStateMemory.resultState2 s input) := fun e =>
    rungBlock PrefixStatePaths.hit2Path s input 5179 e _ hcode hfork hrun hnp
      (run_hit2 s input e hcode hrun)
  have ghit2Fallback : ∀ e, GasSteps (rungFrame s input 5128 e)
      (PrefixStateMemory.resultState2 s input) := fun e =>
    rungBlock PrefixStatePaths.hit2FallbackPath s input 5128 e _ hcode hfork hrun hnp
      (run_hit2Fallback s input e hcode hrun)
  have ghit3Fallback : ∀ e, GasSteps (rungFrame s input 5380 e)
      (PrefixStateMemory.resultState3 s input) := fun e =>
    rungBlock PrefixStatePaths.hit3FallbackPath s input 5380 e _ hcode hfork hrun hnp
      (run_hit3Fallback s input e hcode hrun)
  have ghit4 : ∀ e, GasSteps (rungFrame s input 5328 e)
      (PrefixStateMemory.resultState4 s input) := fun e =>
    rungBlock PrefixStatePaths.hit4Path s input 5328 e _ hcode hfork hrun hnp
      (run_hit4 s input e hcode hrun)
  have gbail : ∀ e, GasSteps (rungFrame s input 5278 e)
      (DriverTrace.compressEntry (PrefixStateMemory.scratchState s) input 0) := fun e =>
    rungBlock PrefixStatePaths.bailPath s input 5278 e _ hcode hfork hrun hnp
      (run_bail s input e hcode hrun)
  by_cases hw1 : MachineState.readWord input 32 = PatternedWordData.expectedWordAt 1
  · rw [if_pos hw1]
    have g1 : GasSteps (rungFrame s input 5028 (PatternedWordData.expectedWordAt 0))
        (rungFrame s input 5048 (PatternedWordData.expectedWordAt 1)) :=
      rungBlock PrefixStatePaths.rung1Path s input 5028 _ _ hcode hfork hrun hnp
        (run_rung1_hit s input hw1 hcalldata hrun)
    by_cases hw2 : MachineState.readWord input 64 = PatternedWordData.expectedWordAt 2
    · have g2 : GasSteps (rungFrame s input 5048 (PatternedWordData.expectedWordAt 1))
          (rungFrame s input 5068 (PatternedWordData.expectedWordAt 2)) :=
        rungBlock PrefixStatePaths.rung2Path s input 5048 _ _ hcode hfork hrun hnp
          (run_rung2_hit s input hw2 hcalldata hrun)
      by_cases hw3 : MachineState.readWord input 96 = PatternedWordData.expectedWordAt 3
      · have hm2 : PrefixStateModel.Matched2 input := ⟨hw2, hw3⟩
        rw [if_pos hm2]
        have g3 : GasSteps (rungFrame s input 5068 (PatternedWordData.expectedWordAt 2))
            (rungFrame s input 5088 (PatternedWordData.expectedWordAt 3)) :=
          rungBlock PrefixStatePaths.rung3Path s input 5068 _ _ hcode hfork hrun hnp
            (run_rung3_hit s input hw3 hcalldata hrun)
        by_cases hw4 : MachineState.readWord input 128 = PatternedWordData.expectedWordAt 4
        · have g4 : GasSteps (rungFrame s input 5088 (PatternedWordData.expectedWordAt 3))
              (rungFrame s input 5108 (PatternedWordData.expectedWordAt 4)) :=
            rungBlock PrefixStatePaths.rung4Path s input 5088 _ _ hcode hfork hrun hnp
              (run_rung4_hit s input hw4 hcalldata hrun)
          by_cases hw5 : MachineState.readWord input 160 = PatternedWordData.expectedWordAt 5
          · have hm3 : PrefixStateModel.Matched3 input := ⟨hw4, hw5⟩
            rw [if_pos hm3]
            have g5 : GasSteps (rungFrame s input 5108 (PatternedWordData.expectedWordAt 4))
                (rungFrame s input 5287 (PatternedWordData.expectedWordAt 5)) :=
              rungBlock PrefixStatePaths.rung5Path s input 5108 _ _ hcode hfork hrun hnp
                (run_rung5_hit s input hw5 hcalldata hcode hrun)
            by_cases hw6 : MachineState.readWord input 192 = PatternedWordData.expectedWordAt 6
            · have g6 : GasSteps
                  (rungFrame s input 5287 (PatternedWordData.expectedWordAt 5))
                  (rungFrame s input 5308 (PatternedWordData.expectedWordAt 6)) :=
                rungBlock PrefixStatePaths.rung6Path s input 5287 _ _ hcode hfork hrun hnp
                  (run_rung6_hit s input hw6 hcalldata hcode hrun)
              by_cases hw7 : MachineState.readWord input 224 = PatternedWordData.expectedWordAt 7
              · have hm4 : PrefixStateModel.Matched4 input := ⟨hw6, hw7⟩
                rw [if_pos hm4]
                have g7 : GasSteps
                    (rungFrame s input 5308 (PatternedWordData.expectedWordAt 6))
                    (rungFrame s input 5328 (PatternedWordData.expectedWordAt 7)) :=
                  rungBlock PrefixStatePaths.rung7Path s input 5308 _ _ hcode hfork hrun hnp
                    (run_rung7_hit s input hw7 hcalldata hcode hrun)
                exact gsetup.trans
                  (g1.trans (g2.trans (g3.trans (g4.trans
                    (g5.trans (g6.trans (g7.trans (ghit4 _))))))))
              · rw [if_neg (fun h => hw7 h.2)]
                have g7 : GasSteps
                    (rungFrame s input 5308 (PatternedWordData.expectedWordAt 6))
                    (rungFrame s input 5380 (PatternedWordData.expectedWordAt 7)) :=
                  rungBlock PrefixStatePaths.rung7Path s input 5308 _ _ hcode hfork hrun hnp
                    (run_rung7_miss s input hw7 hcalldata hcode hrun)
                exact gsetup.trans
                  (g1.trans (g2.trans (g3.trans (g4.trans
                    (g5.trans (g6.trans (g7.trans (ghit3Fallback _))))))))
            · rw [if_neg (fun h => hw6 h.1)]
              have g6 : GasSteps
                  (rungFrame s input 5287 (PatternedWordData.expectedWordAt 5))
                  (rungFrame s input 5380 (PatternedWordData.expectedWordAt 6)) :=
                rungBlock PrefixStatePaths.rung6Path s input 5287 _ _ hcode hfork hrun hnp
                  (run_rung6_miss s input hw6 hcalldata hcode hrun)
              exact gsetup.trans
                (g1.trans (g2.trans (g3.trans (g4.trans
                  (g5.trans (g6.trans (ghit3Fallback _)))))))
          · rw [if_neg (fun h => hw5 h.2)]
            have g5 : GasSteps (rungFrame s input 5108 (PatternedWordData.expectedWordAt 4))
                (rungFrame s input 5128 (PatternedWordData.expectedWordAt 5)) :=
              rungBlock PrefixStatePaths.rung5Path s input 5108 _ _ hcode hfork hrun hnp
                (run_rung5_miss s input hw5 hcalldata hcode hrun)
            exact gsetup.trans
              (g1.trans (g2.trans (g3.trans (g4.trans (g5.trans (ghit2Fallback _))))))
        · rw [if_neg (fun h => hw4 h.1)]
          have g4 : GasSteps (rungFrame s input 5088 (PatternedWordData.expectedWordAt 3))
              (rungFrame s input 5179 (PatternedWordData.expectedWordAt 4)) :=
            rungBlock PrefixStatePaths.rung4Path s input 5088 _ _ hcode hfork hrun hnp
              (run_rung4_miss s input hw4 hcalldata hcode hrun)
          exact gsetup.trans (g1.trans (g2.trans (g3.trans (g4.trans (ghit2 _)))))
      · rw [if_neg (fun h => hw3 h.2)]
        have g3 : GasSteps (rungFrame s input 5068 (PatternedWordData.expectedWordAt 2))
            (rungFrame s input 5231 (PatternedWordData.expectedWordAt 3)) :=
          rungBlock PrefixStatePaths.rung3Path s input 5068 _ _ hcode hfork hrun hnp
            (run_rung3_miss s input hw3 hcalldata hcode hrun)
        exact gsetup.trans (g1.trans (g2.trans (g3.trans (ghit1 _))))
    · rw [if_neg (fun h => hw2 h.1)]
      have g2 : GasSteps (rungFrame s input 5048 (PatternedWordData.expectedWordAt 1))
          (rungFrame s input 5231 (PatternedWordData.expectedWordAt 2)) :=
        rungBlock PrefixStatePaths.rung2Path s input 5048 _ _ hcode hfork hrun hnp
          (run_rung2_miss s input hw2 hcalldata hcode hrun)
      exact gsetup.trans (g1.trans (g2.trans (ghit1 _)))
  · rw [if_neg hw1]
    have g1 : GasSteps (rungFrame s input 5028 (PatternedWordData.expectedWordAt 0))
        (rungFrame s input 5278 (PatternedWordData.expectedWordAt 1)) :=
      rungBlock PrefixStatePaths.rung1Path s input 5028 _ _ hcode hfork hrun hnp
        (run_rung1_miss s input hw1 hcalldata hcode hrun)
    exact gsetup.trans (g1.trans (gbail _))

#print axioms run_setup
#print axioms run_hit2Fallback
#print axioms gasSteps_finish

end Challenge.Ripemd160.Submission.Proofs.Bytecode.PrefixStateTraceFinish
