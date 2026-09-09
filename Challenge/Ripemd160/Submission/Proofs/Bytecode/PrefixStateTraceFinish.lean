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
# Checked-prefix finish: SWAR setup, the five derived-word rungs, and the installs

After the word-0 match the ladder derives every further expected word from
the word-0 literal with a bytewise `+0xA0` SWAR recurrence and compares it
with the next calldata word.  A word-1 mismatch bails to the generic
compressor; a word-2/3 mismatch installs `H1`; a word-4/5 mismatch installs
`H2`; six matches install `H3` with blocks 0..2 consumed.
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

/-- Entry at the SWAR setup (pc 5062), right after the word-0 match. -/
def entry (s : State) (input : ByteArray) : State := frame s input 5062

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

theorem jumpDest_hit2 : Decode.isValidJumpDest submissionBytecode 5229 = true := by
  have h := Artifact.submissionArtifact.isValidJumpDest_index 4203 (by rfl)
  rw [PrefixStatePaths.pc4210] at h
  exact h

theorem jumpDest_hit1 : Decode.isValidJumpDest submissionBytecode 5281 = true := by
  have h := Artifact.submissionArtifact.isValidJumpDest_index 4229 (by rfl)
  rw [PrefixStatePaths.pc4236] at h
  exact h

theorem jumpDest_bail : Decode.isValidJumpDest submissionBytecode 5328 = true := by
  have h := Artifact.submissionArtifact.isValidJumpDest_index 4251 (by rfl)
  rw [PrefixStatePaths.pc4258] at h
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
`JUMPI` is taken to pc 5328. -/
theorem run_rung1_miss (s : State) (input : ByteArray)
    (hword : MachineState.readWord input 32 ≠ PatternedWordData.expectedWordAt 1)
    (hcalldata : s.executionEnv.calldata = input)
    (hcode : s.executionEnv.code = submissionBytecode)
    (hrun : s.halt = .Running) :
    Stepper.runLocatedBlock PrefixStatePaths.rung1Path
      (rungFrame s input 5028 (PatternedWordData.expectedWordAt 0)) =
      some (rungFrame s input 5328 (PatternedWordData.expectedWordAt 1)) := by
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
`JUMPI` is taken to pc 5281. -/
theorem run_rung2_miss (s : State) (input : ByteArray)
    (hword : MachineState.readWord input 64 ≠ PatternedWordData.expectedWordAt 2)
    (hcalldata : s.executionEnv.calldata = input)
    (hcode : s.executionEnv.code = submissionBytecode)
    (hrun : s.halt = .Running) :
    Stepper.runLocatedBlock PrefixStatePaths.rung2Path
      (rungFrame s input 5048 (PatternedWordData.expectedWordAt 1)) =
      some (rungFrame s input 5281 (PatternedWordData.expectedWordAt 2)) := by
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
`JUMPI` is taken to pc 5281. -/
theorem run_rung3_miss (s : State) (input : ByteArray)
    (hword : MachineState.readWord input 96 ≠ PatternedWordData.expectedWordAt 3)
    (hcalldata : s.executionEnv.calldata = input)
    (hcode : s.executionEnv.code = submissionBytecode)
    (hrun : s.halt = .Running) :
    Stepper.runLocatedBlock PrefixStatePaths.rung3Path
      (rungFrame s input 5068 (PatternedWordData.expectedWordAt 2)) =
      some (rungFrame s input 5281 (PatternedWordData.expectedWordAt 3)) := by
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
`JUMPI` is taken to pc 5229. -/
theorem run_rung4_miss (s : State) (input : ByteArray)
    (hword : MachineState.readWord input 128 ≠ PatternedWordData.expectedWordAt 4)
    (hcalldata : s.executionEnv.calldata = input)
    (hcode : s.executionEnv.code = submissionBytecode)
    (hrun : s.halt = .Running) :
    Stepper.runLocatedBlock PrefixStatePaths.rung4Path
      (rungFrame s input 5088 (PatternedWordData.expectedWordAt 3)) =
      some (rungFrame s input 5229 (PatternedWordData.expectedWordAt 4)) := by
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


/-- Rung 5 on a word-5 match: the running word steps to word 5 and the
`JUMPI` is not taken. -/
theorem run_rung5_hit (s : State) (input : ByteArray)
    (hword : MachineState.readWord input 160 = PatternedWordData.expectedWordAt 5)
    (hcalldata : s.executionEnv.calldata = input)
    (hrun : s.halt = .Running) :
    Stepper.runLocatedBlock PrefixStatePaths.rung5Path
      (rungFrame s input 5108 (PatternedWordData.expectedWordAt 4)) =
      some (rungFrame s input 5128 (PatternedWordData.expectedWordAt 5)) := by
  have hzero : UInt256.xor (MachineState.readWord input 160)
      (PatternedWordData.expectedWordAt 5) = 0 :=
    (KnownInputLogic.wordXor_eq_zero_iff _ _).2 hword
  have hzero' : UInt256.xor (PatternedWordData.expectedWordAt 5)
      (MachineState.readWord input 160) = 0 := by
    rw [hword]
    exact (KnownInputLogic.wordXor_eq_zero_iff _ _).2 rfl
  have hcond : (UInt256.xor (MachineState.readWord input 160)
      (PatternedWordData.expectedWordAt 5)).toNat = 0 := by
    rw [hzero]
    rfl
  have hcond' : (UInt256.xor (PatternedWordData.expectedWordAt 5)
      (MachineState.readWord input 160)).toNat = 0 := by
    rw [hzero']
    rfl
  have hcondL := hcond
  rw [PatternedWordData.expectedWordAt_5] at hcondL
  have hcondL' := hcond'
  rw [PatternedWordData.expectedWordAt_5] at hcondL'
  have hfalse : ¬ UInt256.isTrue (UInt256.xor (MachineState.readWord input 160)
      (PatternedWordData.expectedWordAt 5)) := by
    rw [hzero]
    decide
  have hfalse' : ¬ UInt256.isTrue (UInt256.xor (PatternedWordData.expectedWordAt 5)
      (MachineState.readWord input 160)) := by
    rw [hzero']
    decide
  have hfalseL := hfalse
  rw [PatternedWordData.expectedWordAt_5] at hfalseL
  have hfalseL' := hfalse'
  rw [PatternedWordData.expectedWordAt_5] at hfalseL'
  simp (config := { maxSteps := 1000000 })
    [PrefixStatePaths.rung5Path, Stepper.runLocatedBlock, Stepper.runLocated,
      Stepper.runInstr, rungFrame, step0, step0', step1, step1', step2, step2', step3, step3', step4, step4',
      hzero, hzero', hcond, hcond', hcondL, hcondL', hfalse, hfalse', hfalseL, hfalseL',
      jumpDest_hit2,
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
      UInt256.isTrue, hrun, hcalldata, List.exchange,
      State.activeWordsAfterUInt256, zero_toNat,
      Challenge.EvmProof.Word.word_toNat_ofNat,
      Challenge.EvmProof.Word.ofNat_add_mod,
      Challenge.EvmProof.Word.succ_ofNat_mod, Nat.mod_eq_of_lt]

/-- Rung 5 on a word-5 mismatch: the running word steps to word 5 and the
`JUMPI` is taken to pc 5229. -/
theorem run_rung5_miss (s : State) (input : ByteArray)
    (hword : MachineState.readWord input 160 ≠ PatternedWordData.expectedWordAt 5)
    (hcalldata : s.executionEnv.calldata = input)
    (hcode : s.executionEnv.code = submissionBytecode)
    (hrun : s.halt = .Running) :
    Stepper.runLocatedBlock PrefixStatePaths.rung5Path
      (rungFrame s input 5108 (PatternedWordData.expectedWordAt 4)) =
      some (rungFrame s input 5229 (PatternedWordData.expectedWordAt 5)) := by
  have htrue : UInt256.isTrue (UInt256.xor (MachineState.readWord input 160)
      (PatternedWordData.expectedWordAt 5)) := by
    intro hz
    apply hword
    apply (KnownInputLogic.wordXor_eq_zero_iff _ _).1
    apply Challenge.EvmProof.Word.word_ext
    simpa using hz
  have htrue' : UInt256.isTrue (UInt256.xor (PatternedWordData.expectedWordAt 5)
      (MachineState.readWord input 160)) := by
    intro hz
    apply hword
    have hzero : UInt256.xor (PatternedWordData.expectedWordAt 5)
        (MachineState.readWord input 160) = 0 := by
      apply Challenge.EvmProof.Word.word_ext
      simpa using hz
    exact ((KnownInputLogic.wordXor_eq_zero_iff _ _).1 hzero).symm
  have hcond : (UInt256.xor (MachineState.readWord input 160)
      (PatternedWordData.expectedWordAt 5)).toNat ≠ 0 := by
    intro hz
    apply hword
    apply (KnownInputLogic.wordXor_eq_zero_iff _ _).1
    apply Challenge.EvmProof.Word.word_ext
    simpa using hz
  have hcond' : (UInt256.xor (PatternedWordData.expectedWordAt 5)
      (MachineState.readWord input 160)).toNat ≠ 0 := by
    intro hz
    apply hword
    have hzero : UInt256.xor (PatternedWordData.expectedWordAt 5)
        (MachineState.readWord input 160) = 0 := by
      apply Challenge.EvmProof.Word.word_ext
      simpa using hz
    exact ((KnownInputLogic.wordXor_eq_zero_iff _ _).1 hzero).symm
  have hcondL := hcond
  rw [PatternedWordData.expectedWordAt_5] at hcondL
  have hcondL' := hcond'
  rw [PatternedWordData.expectedWordAt_5] at hcondL'
  have htrueL := htrue
  rw [PatternedWordData.expectedWordAt_5] at htrueL
  have htrueL' := htrue'
  rw [PatternedWordData.expectedWordAt_5] at htrueL'
  simp (config := { maxSteps := 1000000 })
    [PrefixStatePaths.rung5Path, Stepper.runLocatedBlock, Stepper.runLocated,
      Stepper.runInstr, rungFrame, step0, step0', step1, step1', step2, step2', step3, step3', step4, step4',
      htrue, htrue', hcond, hcond', hcondL, hcondL', htrueL, htrueL',
      jumpDest_hit2, hcode,
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
      UInt256.isTrue, hrun, hcalldata, List.exchange,
      State.activeWordsAfterUInt256, zero_toNat,
      Challenge.EvmProof.Word.word_toNat_ofNat,
      Challenge.EvmProof.Word.ofNat_add_mod,
      Challenge.EvmProof.Word.succ_ofNat_mod, Nat.mod_eq_of_lt]


/-! ## Installs and the bail trampoline -/

/-- The `H3` install: drop the ladder scratch, advance the block offset to
`0x80`, store the five chaining words, return to the driver. -/
theorem run_hit3 (s : State) (input : ByteArray) (e : UInt256)
    (hcode : s.executionEnv.code = submissionBytecode)
    (hrun : s.halt = .Running) :
    Stepper.runLocatedBlock PrefixStatePaths.hit3Path (rungFrame s input 5128 e) =
      some (PrefixStateMemory.resultState3 s input) := by
  have hbo : DriverTrace.blockOffsetWord 2 = UInt256.ofNat 128 := rfl
  simp (config := { maxSteps := 500000 })
    [PrefixStatePaths.hit3Path, Stepper.runLocatedBlock, Stepper.runLocated,
      Stepper.runInstr, rungFrame, PrefixStateMemory.resultState3,
      PrefixStateMemory.hashMemory3, PrefixStateMemory.writeWord,
      PrefixStateMemory.hash3, PrefixStateMemory.scratchState,
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
      Challenge.EvmProof.Word.ofNat_add_mod,
      Challenge.EvmProof.Word.succ_ofNat_mod, Nat.add_assoc]

/-- The `H2` install: drop the ladder scratch, advance the block offset to
`0x40`, store the five chaining words, return to the driver. -/
theorem run_hit2 (s : State) (input : ByteArray) (e : UInt256)
    (hcode : s.executionEnv.code = submissionBytecode)
    (hrun : s.halt = .Running) :
    Stepper.runLocatedBlock PrefixStatePaths.hit2Path (rungFrame s input 5229 e) =
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
    Stepper.runLocatedBlock PrefixStatePaths.hit1Path (rungFrame s input 5281 e) =
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
    Stepper.runLocatedBlock PrefixStatePaths.bailPath (rungFrame s input 5328 e) =
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

/-- Execute the SWAR setup, the five rungs and the matching install. -/
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
          (if PrefixStateModel.Matched3 input then PrefixStateMemory.resultState3 s input
            else PrefixStateMemory.resultState2 s input)
          else PrefixStateMemory.resultState s input 0)
      else DriverTrace.compressEntry (PrefixStateMemory.scratchState s) input 0) := by
  have gsetup : GasSteps (entry s input)
      (rungFrame s input 5028 (PatternedWordData.expectedWordAt 0)) :=
    entryBlock PrefixStatePaths.setupPath s input _ hcode hfork hrun hnp
      (run_setup s input hmem0 hrun)
  have ghit1 : ∀ e, GasSteps (rungFrame s input 5281 e)
      (PrefixStateMemory.resultState s input 0) := fun e =>
    rungBlock PrefixStatePaths.hit1Path s input 5281 e _ hcode hfork hrun hnp
      (run_hit1 s input e hcode hrun)
  have ghit2 : ∀ e, GasSteps (rungFrame s input 5229 e)
      (PrefixStateMemory.resultState2 s input) := fun e =>
    rungBlock PrefixStatePaths.hit2Path s input 5229 e _ hcode hfork hrun hnp
      (run_hit2 s input e hcode hrun)
  have ghit3 : ∀ e, GasSteps (rungFrame s input 5128 e)
      (PrefixStateMemory.resultState3 s input) := fun e =>
    rungBlock PrefixStatePaths.hit3Path s input 5128 e _ hcode hfork hrun hnp
      (run_hit3 s input e hcode hrun)
  have gbail : ∀ e, GasSteps (rungFrame s input 5328 e)
      (DriverTrace.compressEntry (PrefixStateMemory.scratchState s) input 0) := fun e =>
    rungBlock PrefixStatePaths.bailPath s input 5328 e _ hcode hfork hrun hnp
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
                (rungFrame s input 5128 (PatternedWordData.expectedWordAt 5)) :=
              rungBlock PrefixStatePaths.rung5Path s input 5108 _ _ hcode hfork hrun hnp
                (run_rung5_hit s input hw5 hcalldata hrun)
            exact gsetup.trans (g1.trans (g2.trans (g3.trans (g4.trans (g5.trans (ghit3 _))))))
          · rw [if_neg (fun h => hw5 h.2)]
            have g5 : GasSteps (rungFrame s input 5108 (PatternedWordData.expectedWordAt 4))
                (rungFrame s input 5229 (PatternedWordData.expectedWordAt 5)) :=
              rungBlock PrefixStatePaths.rung5Path s input 5108 _ _ hcode hfork hrun hnp
                (run_rung5_miss s input hw5 hcalldata hcode hrun)
            exact gsetup.trans (g1.trans (g2.trans (g3.trans (g4.trans (g5.trans (ghit2 _))))))
        · rw [if_neg (fun h => hw4 h.1)]
          have g4 : GasSteps (rungFrame s input 5088 (PatternedWordData.expectedWordAt 3))
              (rungFrame s input 5229 (PatternedWordData.expectedWordAt 4)) :=
            rungBlock PrefixStatePaths.rung4Path s input 5088 _ _ hcode hfork hrun hnp
              (run_rung4_miss s input hw4 hcalldata hcode hrun)
          exact gsetup.trans (g1.trans (g2.trans (g3.trans (g4.trans (ghit2 _)))))
      · rw [if_neg (fun h => hw3 h.2)]
        have g3 : GasSteps (rungFrame s input 5068 (PatternedWordData.expectedWordAt 2))
            (rungFrame s input 5281 (PatternedWordData.expectedWordAt 3)) :=
          rungBlock PrefixStatePaths.rung3Path s input 5068 _ _ hcode hfork hrun hnp
            (run_rung3_miss s input hw3 hcalldata hcode hrun)
        exact gsetup.trans (g1.trans (g2.trans (g3.trans (ghit1 _))))
    · rw [if_neg (fun h => hw2 h.1)]
      have g2 : GasSteps (rungFrame s input 5048 (PatternedWordData.expectedWordAt 1))
          (rungFrame s input 5281 (PatternedWordData.expectedWordAt 2)) :=
        rungBlock PrefixStatePaths.rung2Path s input 5048 _ _ hcode hfork hrun hnp
          (run_rung2_miss s input hw2 hcalldata hcode hrun)
      exact gsetup.trans (g1.trans (g2.trans (ghit1 _)))
  · rw [if_neg hw1]
    have g1 : GasSteps (rungFrame s input 5028 (PatternedWordData.expectedWordAt 0))
        (rungFrame s input 5328 (PatternedWordData.expectedWordAt 1)) :=
      rungBlock PrefixStatePaths.rung1Path s input 5028 _ _ hcode hfork hrun hnp
        (run_rung1_miss s input hw1 hcalldata hcode hrun)
    exact gsetup.trans (g1.trans (gbail _))

#print axioms run_setup
#print axioms run_hit3
#print axioms gasSteps_finish

end Challenge.Ripemd160.Submission.Proofs.Bytecode.PrefixStateTraceFinish
