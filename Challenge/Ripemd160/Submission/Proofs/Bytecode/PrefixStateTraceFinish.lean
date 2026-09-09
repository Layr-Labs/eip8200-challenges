import Challenge.Ripemd160.Submission.Proofs.Bytecode.PrefixStateFourth
import Challenge.Ripemd160.Submission.Proofs.Bytecode.PrefixStatePaths
import Challenge.Ripemd160.Submission.Proofs.Bytecode.KnownInputLogic

set_option warningAsError true
set_option maxRecDepth 50000
set_option maxHeartbeats 5000000
set_option linter.unusedSimpArgs false

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.PrefixStateTraceFinish
open Challenge.Ripemd160 Challenge.EvmProof EvmSemantics EvmSemantics.EVM

def byteMask : UInt256 := UInt256.ofNat 29061543965444064733758992315905984716114819680788219994216805398064471752768

private def frame (s : State) (input : ByteArray) (pc : Nat) : State :=
  { s with
    pc := UInt256.ofNat pc
    stack := [DriverTrace.messageOffsetWord 0, UInt256.ofNat 102,
      DriverTrace.blockOffsetWord 0, Padding.paddedWord input] }

private def maskFrame (s : State) (input : ByteArray) (pc : Nat) : State :=
  { s with
    pc := UInt256.ofNat pc
    stack := [byteMask, UInt256.ofNat 102,
      DriverTrace.blockOffsetWord 0, Padding.paddedWord input] }

def entry (s : State) (input : ByteArray) : State := frame s input 5019

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

theorem jumpDest_h1 : Decode.isValidJumpDest submissionBytecode 5276 = true := by
  have hpc : Artifact.submissionArtifact.instructionPC 4200 = 5276 := by
    rw [ArtifactByteLength.instructionPC_eq_byteLength]
    decide
  have h := Artifact.submissionArtifact.isValidJumpDest_index 4200 (by rfl)
  rw [hpc] at h
  exact h

theorem jumpDest_h2 : Decode.isValidJumpDest submissionBytecode 5241 = true := by
  have hpc : Artifact.submissionArtifact.instructionPC 4188 = 5241 := by
    rw [ArtifactByteLength.instructionPC_eq_byteLength]
    decide
  have h := Artifact.submissionArtifact.isValidJumpDest_index 4188 (by rfl)
  rw [hpc] at h
  exact h

theorem jumpDest_h3 : Decode.isValidJumpDest submissionBytecode 5206 = true := by
  have hpc : Artifact.submissionArtifact.instructionPC 4176 = 5206 := by
    rw [ArtifactByteLength.instructionPC_eq_byteLength]
    decide
  have h := Artifact.submissionArtifact.isValidJumpDest_index 4176 (by rfl)
  rw [hpc] at h
  exact h

theorem jumpDest_store : Decode.isValidJumpDest submissionBytecode 5302 = true := by
  have hpc : Artifact.submissionArtifact.instructionPC 4206 = 5302 := by
    rw [ArtifactByteLength.instructionPC_eq_byteLength]
    decide
  have h := Artifact.submissionArtifact.isValidJumpDest_index 4206 (by rfl)
  rw [hpc] at h
  exact h

theorem jumpDest_bail : Decode.isValidJumpDest submissionBytecode 5320 = true := by
  have hpc : Artifact.submissionArtifact.instructionPC 4219 = 5320 := by
    rw [ArtifactByteLength.instructionPC_eq_byteLength]
    decide
  have h := Artifact.submissionArtifact.isValidJumpDest_index 4219 (by rfl)
  rw [hpc] at h
  exact h

theorem byteMask_construct :
    UInt256.ofNat 64 * (UInt256.lnot (UInt256.ofNat 0) / UInt256.ofNat 255) = byteMask := by decide

theorem byteMask_construct_zero :
    UInt256.ofNat 64 * (UInt256.lnot (⟨0⟩ : UInt256) / UInt256.ofNat 255) = byteMask := by decide

theorem xor_nat_zero_iff (a b : UInt256) : (UInt256.xor a b).toNat = 0 ↔ a = b := by
  constructor
  · intro h
    apply (KnownInputLogic.wordXor_eq_zero_iff _ _).1
    apply Challenge.EvmProof.Word.word_ext
    simpa using h
  · intro h
    have hz := (KnownInputLogic.wordXor_eq_zero_iff a b).2 h
    rw [hz]
    rfl

theorem run_prepare (s : State) (input : ByteArray) (hrun : s.halt = .Running) :
    Stepper.runLocatedBlock PrefixStatePaths.preparePath (entry s input) =
      some (maskFrame s input 5028) := by
  simp (config := { maxSteps := 500000 })
    [PrefixStatePaths.preparePath, entry, frame, byteMask_construct, byteMask_construct_zero, hrun, Stepper.runLocatedBlock, Stepper.runLocated, Stepper.runInstr, maskFrame,
      State.activeWordsAfterUInt256, List.exchange,
      Challenge.EvmProof.Word.word_toNat_ofNat, Challenge.EvmProof.Word.ofNat_add_mod,
      Challenge.EvmProof.Word.succ_ofNat_mod, Nat.add_assoc]

theorem run_word1_hit (s : State) (input : ByteArray)
    (hword : MachineState.readWord input 32 = PatternedWordData.expectedWordAt 1)
    (hcalldata : s.executionEnv.calldata = input)
    (hcode : s.executionEnv.code = submissionBytecode)
    (hrun : s.halt = .Running) :
    Stepper.runLocatedBlock PrefixStatePaths.word1Path (maskFrame s input 5028) =
      some (maskFrame s input 5069) := by
  have hcond : (UInt256.xor (MachineState.readWord input 32)
      (PatternedWordData.expectedWordAt 1)).toNat = 0 := by
    exact (xor_nat_zero_iff _ _).2 hword
  have hcondL := hcond
  rw [PatternedWordData.expectedWordAt_1] at hcondL
  simp (config := { maxSteps := 500000 })
    [PrefixStatePaths.word1Path, Stepper.runLocatedBlock, Stepper.runLocated, Stepper.runInstr, maskFrame,
      State.activeWordsAfterUInt256, List.exchange,
      Challenge.EvmProof.Word.word_toNat_ofNat, Challenge.EvmProof.Word.ofNat_add_mod,
      Challenge.EvmProof.Word.succ_ofNat_mod, Nat.add_assoc,
      hcalldata, hcode, hrun, hcond, hcondL, jumpDest_bail]

theorem run_word1_miss (s : State) (input : ByteArray)
    (hword : MachineState.readWord input 32 ≠ PatternedWordData.expectedWordAt 1)
    (hcalldata : s.executionEnv.calldata = input)
    (hcode : s.executionEnv.code = submissionBytecode)
    (hrun : s.halt = .Running) :
    Stepper.runLocatedBlock PrefixStatePaths.word1Path (maskFrame s input 5028) =
      some (maskFrame s input 5320) := by
  have hcond : (UInt256.xor (MachineState.readWord input 32)
      (PatternedWordData.expectedWordAt 1)).toNat ≠ 0 := by
    intro hz
    exact hword ((xor_nat_zero_iff _ _).1 hz)
  have hcondL := hcond
  rw [PatternedWordData.expectedWordAt_1] at hcondL
  simp (config := { maxSteps := 500000 })
    [PrefixStatePaths.word1Path, Stepper.runLocatedBlock, Stepper.runLocated, Stepper.runInstr, maskFrame,
      State.activeWordsAfterUInt256, List.exchange,
      Challenge.EvmProof.Word.word_toNat_ofNat, Challenge.EvmProof.Word.ofNat_add_mod,
      Challenge.EvmProof.Word.succ_ofNat_mod, Nat.add_assoc,
      hcalldata, hcode, hrun, hcond, hcondL, jumpDest_bail]

def expected2 (b : UInt256) : UInt256 := UInt256.xor byteMask (UInt256.xor (UInt256.land byteMask b + UInt256.land byteMask b) b)

theorem expected2_value : expected2 (PatternedWordData.expectedWordAt 0) =
    PatternedWordData.expectedWordAt 2 := by decide

theorem run_word2_hit (s : State) (input : ByteArray)
    (hbase : MachineState.readWord input 0 = PatternedWordData.expectedWordAt 0)
    (hword : MachineState.readWord input 64 = PatternedWordData.expectedWordAt 2)
    (hcalldata : s.executionEnv.calldata = input)
    (hcode : s.executionEnv.code = submissionBytecode)
    (hrun : s.halt = .Running) :
    Stepper.runLocatedBlock PrefixStatePaths.word2Path (maskFrame s input 5069) =
      some (maskFrame s input 5087) := by
  have hcond : (UInt256.xor (MachineState.readWord input 64)
      (PatternedWordData.expectedWordAt 2)).toNat = 0 := by
    exact (xor_nat_zero_iff _ _).2 hword
  have hexpected : expected2 (MachineState.readWord input 0) =
      PatternedWordData.expectedWordAt 2 := by
    rw [hbase, expected2_value]
  unfold expected2 at hexpected
  have hcondL := hcond
  rw [PatternedWordData.expectedWordAt_2] at hcondL
  have hexpectedL := hexpected
  rw [PatternedWordData.expectedWordAt_2] at hexpectedL
  simp (config := { maxSteps := 500000 })
    [PrefixStatePaths.word2Path, Stepper.runLocatedBlock, Stepper.runLocated, Stepper.runInstr, maskFrame,
      State.activeWordsAfterUInt256, List.exchange,
      Challenge.EvmProof.Word.word_toNat_ofNat, Challenge.EvmProof.Word.ofNat_add_mod,
      Challenge.EvmProof.Word.succ_ofNat_mod, Nat.add_assoc,
      hcalldata, hcode, hrun, hcond, hcondL, hexpected, hexpectedL, jumpDest_h1]

theorem run_word2_miss (s : State) (input : ByteArray)
    (hbase : MachineState.readWord input 0 = PatternedWordData.expectedWordAt 0)
    (hword : MachineState.readWord input 64 ≠ PatternedWordData.expectedWordAt 2)
    (hcalldata : s.executionEnv.calldata = input)
    (hcode : s.executionEnv.code = submissionBytecode)
    (hrun : s.halt = .Running) :
    Stepper.runLocatedBlock PrefixStatePaths.word2Path (maskFrame s input 5069) =
      some (maskFrame s input 5276) := by
  have hcond : (UInt256.xor (MachineState.readWord input 64)
      (PatternedWordData.expectedWordAt 2)).toNat ≠ 0 := by
    intro hz
    exact hword ((xor_nat_zero_iff _ _).1 hz)
  have hexpected : expected2 (MachineState.readWord input 0) =
      PatternedWordData.expectedWordAt 2 := by
    rw [hbase, expected2_value]
  unfold expected2 at hexpected
  have hcondL := hcond
  rw [PatternedWordData.expectedWordAt_2] at hcondL
  have hexpectedL := hexpected
  rw [PatternedWordData.expectedWordAt_2] at hexpectedL
  simp (config := { maxSteps := 500000 })
    [PrefixStatePaths.word2Path, Stepper.runLocatedBlock, Stepper.runLocated, Stepper.runInstr, maskFrame,
      State.activeWordsAfterUInt256, List.exchange,
      Challenge.EvmProof.Word.word_toNat_ofNat, Challenge.EvmProof.Word.ofNat_add_mod,
      Challenge.EvmProof.Word.succ_ofNat_mod, Nat.add_assoc,
      hcalldata, hcode, hrun, hcond, hcondL, hexpected, hexpectedL, jumpDest_h1]

def expected3 (b : UInt256) : UInt256 := UInt256.xor byteMask (UInt256.xor (UInt256.land byteMask b + UInt256.land byteMask b) b)

theorem expected3_value : expected3 (PatternedWordData.expectedWordAt 1) =
    PatternedWordData.expectedWordAt 3 := by decide

theorem run_word3_hit (s : State) (input : ByteArray)
    (hbase : MachineState.readWord input 32 = PatternedWordData.expectedWordAt 1)
    (hword : MachineState.readWord input 96 = PatternedWordData.expectedWordAt 3)
    (hcalldata : s.executionEnv.calldata = input)
    (hcode : s.executionEnv.code = submissionBytecode)
    (hrun : s.halt = .Running) :
    Stepper.runLocatedBlock PrefixStatePaths.word3Path (maskFrame s input 5087) =
      some (maskFrame s input 5106) := by
  have hcond : (UInt256.xor (MachineState.readWord input 96)
      (PatternedWordData.expectedWordAt 3)).toNat = 0 := by
    exact (xor_nat_zero_iff _ _).2 hword
  have hexpected : expected3 (MachineState.readWord input 32) =
      PatternedWordData.expectedWordAt 3 := by
    rw [hbase, expected3_value]
  unfold expected3 at hexpected
  have hcondL := hcond
  rw [PatternedWordData.expectedWordAt_3] at hcondL
  have hexpectedL := hexpected
  rw [PatternedWordData.expectedWordAt_3] at hexpectedL
  simp (config := { maxSteps := 500000 })
    [PrefixStatePaths.word3Path, Stepper.runLocatedBlock, Stepper.runLocated, Stepper.runInstr, maskFrame,
      State.activeWordsAfterUInt256, List.exchange,
      Challenge.EvmProof.Word.word_toNat_ofNat, Challenge.EvmProof.Word.ofNat_add_mod,
      Challenge.EvmProof.Word.succ_ofNat_mod, Nat.add_assoc,
      hcalldata, hcode, hrun, hcond, hcondL, hexpected, hexpectedL, jumpDest_h1]

theorem run_word3_miss (s : State) (input : ByteArray)
    (hbase : MachineState.readWord input 32 = PatternedWordData.expectedWordAt 1)
    (hword : MachineState.readWord input 96 ≠ PatternedWordData.expectedWordAt 3)
    (hcalldata : s.executionEnv.calldata = input)
    (hcode : s.executionEnv.code = submissionBytecode)
    (hrun : s.halt = .Running) :
    Stepper.runLocatedBlock PrefixStatePaths.word3Path (maskFrame s input 5087) =
      some (maskFrame s input 5276) := by
  have hcond : (UInt256.xor (MachineState.readWord input 96)
      (PatternedWordData.expectedWordAt 3)).toNat ≠ 0 := by
    intro hz
    exact hword ((xor_nat_zero_iff _ _).1 hz)
  have hexpected : expected3 (MachineState.readWord input 32) =
      PatternedWordData.expectedWordAt 3 := by
    rw [hbase, expected3_value]
  unfold expected3 at hexpected
  have hcondL := hcond
  rw [PatternedWordData.expectedWordAt_3] at hcondL
  have hexpectedL := hexpected
  rw [PatternedWordData.expectedWordAt_3] at hexpectedL
  simp (config := { maxSteps := 500000 })
    [PrefixStatePaths.word3Path, Stepper.runLocatedBlock, Stepper.runLocated, Stepper.runInstr, maskFrame,
      State.activeWordsAfterUInt256, List.exchange,
      Challenge.EvmProof.Word.word_toNat_ofNat, Challenge.EvmProof.Word.ofNat_add_mod,
      Challenge.EvmProof.Word.succ_ofNat_mod, Nat.add_assoc,
      hcalldata, hcode, hrun, hcond, hcondL, hexpected, hexpectedL, jumpDest_h1]

def expected4 (b : UInt256) : UInt256 := UInt256.xor (byteMask + byteMask) b

theorem expected4_value : expected4 (PatternedWordData.expectedWordAt 0) =
    PatternedWordData.expectedWordAt 4 := by decide

theorem run_word4_hit (s : State) (input : ByteArray)
    (hbase : MachineState.readWord input 0 = PatternedWordData.expectedWordAt 0)
    (hword : MachineState.readWord input 128 = PatternedWordData.expectedWordAt 4)
    (hcalldata : s.executionEnv.calldata = input)
    (hcode : s.executionEnv.code = submissionBytecode)
    (hrun : s.halt = .Running) :
    Stepper.runLocatedBlock PrefixStatePaths.word4Path (maskFrame s input 5106) =
      some (maskFrame s input 5120) := by
  have hcond : (UInt256.xor (MachineState.readWord input 128)
      (PatternedWordData.expectedWordAt 4)).toNat = 0 := by
    exact (xor_nat_zero_iff _ _).2 hword
  have hexpected : expected4 (MachineState.readWord input 0) =
      PatternedWordData.expectedWordAt 4 := by
    rw [hbase, expected4_value]
  unfold expected4 at hexpected
  have hcondL := hcond
  rw [PatternedWordData.expectedWordAt_4] at hcondL
  have hexpectedL := hexpected
  rw [PatternedWordData.expectedWordAt_4] at hexpectedL
  simp (config := { maxSteps := 500000 })
    [PrefixStatePaths.word4Path, Stepper.runLocatedBlock, Stepper.runLocated, Stepper.runInstr, maskFrame,
      State.activeWordsAfterUInt256, List.exchange,
      Challenge.EvmProof.Word.word_toNat_ofNat, Challenge.EvmProof.Word.ofNat_add_mod,
      Challenge.EvmProof.Word.succ_ofNat_mod, Nat.add_assoc,
      hcalldata, hcode, hrun, hcond, hcondL, hexpected, hexpectedL, jumpDest_h2]

theorem run_word4_miss (s : State) (input : ByteArray)
    (hbase : MachineState.readWord input 0 = PatternedWordData.expectedWordAt 0)
    (hword : MachineState.readWord input 128 ≠ PatternedWordData.expectedWordAt 4)
    (hcalldata : s.executionEnv.calldata = input)
    (hcode : s.executionEnv.code = submissionBytecode)
    (hrun : s.halt = .Running) :
    Stepper.runLocatedBlock PrefixStatePaths.word4Path (maskFrame s input 5106) =
      some (maskFrame s input 5241) := by
  have hcond : (UInt256.xor (MachineState.readWord input 128)
      (PatternedWordData.expectedWordAt 4)).toNat ≠ 0 := by
    intro hz
    exact hword ((xor_nat_zero_iff _ _).1 hz)
  have hexpected : expected4 (MachineState.readWord input 0) =
      PatternedWordData.expectedWordAt 4 := by
    rw [hbase, expected4_value]
  unfold expected4 at hexpected
  have hcondL := hcond
  rw [PatternedWordData.expectedWordAt_4] at hcondL
  have hexpectedL := hexpected
  rw [PatternedWordData.expectedWordAt_4] at hexpectedL
  simp (config := { maxSteps := 500000 })
    [PrefixStatePaths.word4Path, Stepper.runLocatedBlock, Stepper.runLocated, Stepper.runInstr, maskFrame,
      State.activeWordsAfterUInt256, List.exchange,
      Challenge.EvmProof.Word.word_toNat_ofNat, Challenge.EvmProof.Word.ofNat_add_mod,
      Challenge.EvmProof.Word.succ_ofNat_mod, Nat.add_assoc,
      hcalldata, hcode, hrun, hcond, hcondL, hexpected, hexpectedL, jumpDest_h2]

def expected5 (b : UInt256) : UInt256 := UInt256.xor (byteMask + byteMask) b

theorem expected5_value : expected5 (PatternedWordData.expectedWordAt 1) =
    PatternedWordData.expectedWordAt 5 := by decide

theorem run_word5_hit (s : State) (input : ByteArray)
    (hbase : MachineState.readWord input 32 = PatternedWordData.expectedWordAt 1)
    (hword : MachineState.readWord input 160 = PatternedWordData.expectedWordAt 5)
    (hcalldata : s.executionEnv.calldata = input)
    (hcode : s.executionEnv.code = submissionBytecode)
    (hrun : s.halt = .Running) :
    Stepper.runLocatedBlock PrefixStatePaths.word5Path (maskFrame s input 5120) =
      some (maskFrame s input 5135) := by
  have hcond : (UInt256.xor (MachineState.readWord input 160)
      (PatternedWordData.expectedWordAt 5)).toNat = 0 := by
    exact (xor_nat_zero_iff _ _).2 hword
  have hexpected : expected5 (MachineState.readWord input 32) =
      PatternedWordData.expectedWordAt 5 := by
    rw [hbase, expected5_value]
  unfold expected5 at hexpected
  have hcondL := hcond
  rw [PatternedWordData.expectedWordAt_5] at hcondL
  have hexpectedL := hexpected
  rw [PatternedWordData.expectedWordAt_5] at hexpectedL
  simp (config := { maxSteps := 500000 })
    [PrefixStatePaths.word5Path, Stepper.runLocatedBlock, Stepper.runLocated, Stepper.runInstr, maskFrame,
      State.activeWordsAfterUInt256, List.exchange,
      Challenge.EvmProof.Word.word_toNat_ofNat, Challenge.EvmProof.Word.ofNat_add_mod,
      Challenge.EvmProof.Word.succ_ofNat_mod, Nat.add_assoc,
      hcalldata, hcode, hrun, hcond, hcondL, hexpected, hexpectedL, jumpDest_h2]

theorem run_word5_miss (s : State) (input : ByteArray)
    (hbase : MachineState.readWord input 32 = PatternedWordData.expectedWordAt 1)
    (hword : MachineState.readWord input 160 ≠ PatternedWordData.expectedWordAt 5)
    (hcalldata : s.executionEnv.calldata = input)
    (hcode : s.executionEnv.code = submissionBytecode)
    (hrun : s.halt = .Running) :
    Stepper.runLocatedBlock PrefixStatePaths.word5Path (maskFrame s input 5120) =
      some (maskFrame s input 5241) := by
  have hcond : (UInt256.xor (MachineState.readWord input 160)
      (PatternedWordData.expectedWordAt 5)).toNat ≠ 0 := by
    intro hz
    exact hword ((xor_nat_zero_iff _ _).1 hz)
  have hexpected : expected5 (MachineState.readWord input 32) =
      PatternedWordData.expectedWordAt 5 := by
    rw [hbase, expected5_value]
  unfold expected5 at hexpected
  have hcondL := hcond
  rw [PatternedWordData.expectedWordAt_5] at hcondL
  have hexpectedL := hexpected
  rw [PatternedWordData.expectedWordAt_5] at hexpectedL
  simp (config := { maxSteps := 500000 })
    [PrefixStatePaths.word5Path, Stepper.runLocatedBlock, Stepper.runLocated, Stepper.runInstr, maskFrame,
      State.activeWordsAfterUInt256, List.exchange,
      Challenge.EvmProof.Word.word_toNat_ofNat, Challenge.EvmProof.Word.ofNat_add_mod,
      Challenge.EvmProof.Word.succ_ofNat_mod, Nat.add_assoc,
      hcalldata, hcode, hrun, hcond, hcondL, hexpected, hexpectedL, jumpDest_h2]

def expected6 (b : UInt256) : UInt256 := UInt256.xor (byteMask + byteMask) b

theorem expected6_value : expected6 (PatternedWordData.expectedWordAt 2) =
    PatternedWordData.expectedWordAt 6 := by decide

theorem run_word6_hit (s : State) (input : ByteArray)
    (hbase : MachineState.readWord input 64 = PatternedWordData.expectedWordAt 2)
    (hword : MachineState.readWord input 192 = PatternedWordData.expectedWordAt 6)
    (hcalldata : s.executionEnv.calldata = input)
    (hcode : s.executionEnv.code = submissionBytecode)
    (hrun : s.halt = .Running) :
    Stepper.runLocatedBlock PrefixStatePaths.word6Path (maskFrame s input 5135) =
      some (maskFrame s input 5150) := by
  have hcond : (UInt256.xor (MachineState.readWord input 192)
      (PatternedWordData.expectedWordAt 6)).toNat = 0 := by
    exact (xor_nat_zero_iff _ _).2 hword
  have hexpected : expected6 (MachineState.readWord input 64) =
      PatternedWordData.expectedWordAt 6 := by
    rw [hbase, expected6_value]
  unfold expected6 at hexpected
  have hcondL := hcond
  rw [PatternedWordData.expectedWordAt_6] at hcondL
  have hexpectedL := hexpected
  rw [PatternedWordData.expectedWordAt_6] at hexpectedL
  simp (config := { maxSteps := 500000 })
    [PrefixStatePaths.word6Path, Stepper.runLocatedBlock, Stepper.runLocated, Stepper.runInstr, maskFrame,
      State.activeWordsAfterUInt256, List.exchange,
      Challenge.EvmProof.Word.word_toNat_ofNat, Challenge.EvmProof.Word.ofNat_add_mod,
      Challenge.EvmProof.Word.succ_ofNat_mod, Nat.add_assoc,
      hcalldata, hcode, hrun, hcond, hcondL, hexpected, hexpectedL, jumpDest_h3]

theorem run_word6_miss (s : State) (input : ByteArray)
    (hbase : MachineState.readWord input 64 = PatternedWordData.expectedWordAt 2)
    (hword : MachineState.readWord input 192 ≠ PatternedWordData.expectedWordAt 6)
    (hcalldata : s.executionEnv.calldata = input)
    (hcode : s.executionEnv.code = submissionBytecode)
    (hrun : s.halt = .Running) :
    Stepper.runLocatedBlock PrefixStatePaths.word6Path (maskFrame s input 5135) =
      some (maskFrame s input 5206) := by
  have hcond : (UInt256.xor (MachineState.readWord input 192)
      (PatternedWordData.expectedWordAt 6)).toNat ≠ 0 := by
    intro hz
    exact hword ((xor_nat_zero_iff _ _).1 hz)
  have hexpected : expected6 (MachineState.readWord input 64) =
      PatternedWordData.expectedWordAt 6 := by
    rw [hbase, expected6_value]
  unfold expected6 at hexpected
  have hcondL := hcond
  rw [PatternedWordData.expectedWordAt_6] at hcondL
  have hexpectedL := hexpected
  rw [PatternedWordData.expectedWordAt_6] at hexpectedL
  simp (config := { maxSteps := 500000 })
    [PrefixStatePaths.word6Path, Stepper.runLocatedBlock, Stepper.runLocated, Stepper.runInstr, maskFrame,
      State.activeWordsAfterUInt256, List.exchange,
      Challenge.EvmProof.Word.word_toNat_ofNat, Challenge.EvmProof.Word.ofNat_add_mod,
      Challenge.EvmProof.Word.succ_ofNat_mod, Nat.add_assoc,
      hcalldata, hcode, hrun, hcond, hcondL, hexpected, hexpectedL, jumpDest_h3]

def expected7 (b : UInt256) : UInt256 := UInt256.xor (UInt256.ofNat 99006248207) (UInt256.xor (byteMask + byteMask) b)

theorem expected7_value : expected7 (PatternedWordData.expectedWordAt 3) =
    PatternedWordData.expectedWordAt 7 := by decide

theorem run_word7_hit (s : State) (input : ByteArray)
    (hbase : MachineState.readWord input 96 = PatternedWordData.expectedWordAt 3)
    (hword : MachineState.readWord input 224 = PatternedWordData.expectedWordAt 7)
    (hcalldata : s.executionEnv.calldata = input)
    (hcode : s.executionEnv.code = submissionBytecode)
    (hrun : s.halt = .Running) :
    Stepper.runLocatedBlock PrefixStatePaths.word7Path (maskFrame s input 5150) =
      some (maskFrame s input 5172) := by
  have hcond : (UInt256.xor (MachineState.readWord input 224)
      (PatternedWordData.expectedWordAt 7)).toNat = 0 := by
    exact (xor_nat_zero_iff _ _).2 hword
  have hexpected : expected7 (MachineState.readWord input 96) =
      PatternedWordData.expectedWordAt 7 := by
    rw [hbase, expected7_value]
  unfold expected7 at hexpected
  have hcondL := hcond
  rw [PatternedWordData.expectedWordAt_7] at hcondL
  have hexpectedL := hexpected
  rw [PatternedWordData.expectedWordAt_7] at hexpectedL
  simp (config := { maxSteps := 500000 })
    [PrefixStatePaths.word7Path, Stepper.runLocatedBlock, Stepper.runLocated, Stepper.runInstr, maskFrame,
      State.activeWordsAfterUInt256, List.exchange,
      Challenge.EvmProof.Word.word_toNat_ofNat, Challenge.EvmProof.Word.ofNat_add_mod,
      Challenge.EvmProof.Word.succ_ofNat_mod, Nat.add_assoc,
      hcalldata, hcode, hrun, hcond, hcondL, hexpected, hexpectedL, jumpDest_h3]

theorem run_word7_miss (s : State) (input : ByteArray)
    (hbase : MachineState.readWord input 96 = PatternedWordData.expectedWordAt 3)
    (hword : MachineState.readWord input 224 ≠ PatternedWordData.expectedWordAt 7)
    (hcalldata : s.executionEnv.calldata = input)
    (hcode : s.executionEnv.code = submissionBytecode)
    (hrun : s.halt = .Running) :
    Stepper.runLocatedBlock PrefixStatePaths.word7Path (maskFrame s input 5150) =
      some (maskFrame s input 5206) := by
  have hcond : (UInt256.xor (MachineState.readWord input 224)
      (PatternedWordData.expectedWordAt 7)).toNat ≠ 0 := by
    intro hz
    exact hword ((xor_nat_zero_iff _ _).1 hz)
  have hexpected : expected7 (MachineState.readWord input 96) =
      PatternedWordData.expectedWordAt 7 := by
    rw [hbase, expected7_value]
  unfold expected7 at hexpected
  have hcondL := hcond
  rw [PatternedWordData.expectedWordAt_7] at hcondL
  have hexpectedL := hexpected
  rw [PatternedWordData.expectedWordAt_7] at hexpectedL
  simp (config := { maxSteps := 500000 })
    [PrefixStatePaths.word7Path, Stepper.runLocatedBlock, Stepper.runLocated, Stepper.runInstr, maskFrame,
      State.activeWordsAfterUInt256, List.exchange,
      Challenge.EvmProof.Word.word_toNat_ofNat, Challenge.EvmProof.Word.ofNat_add_mod,
      Challenge.EvmProof.Word.succ_ofNat_mod, Nat.add_assoc,
      hcalldata, hcode, hrun, hcond, hcondL, hexpected, hexpectedL, jumpDest_h3]

theorem run_h1 (s : State) (input : ByteArray)
    (hscratch : PrefixStateMemory.scratchState s = s)
    (hcode : s.executionEnv.code = submissionBytecode)
    (hrun : s.halt = .Running) :
    Stepper.runLocatedBlock (PrefixStatePaths.h1Path ++ PrefixStatePaths.storePath)
      (maskFrame s input 5276) = some (PrefixStateMemory.resultState s input 0) := by
  simp (config := { maxSteps := 1000000 })
    [PrefixStatePaths.h1Path, PrefixStatePaths.storePath, Stepper.runLocatedBlock, Stepper.runLocated, Stepper.runInstr, maskFrame,
      State.activeWordsAfterUInt256, List.exchange,
      Challenge.EvmProof.Word.word_toNat_ofNat, Challenge.EvmProof.Word.ofNat_add_mod,
      Challenge.EvmProof.Word.succ_ofNat_mod, Nat.add_assoc,
      PrefixStateMemory.resultState, PrefixStateMemory.hashMemory,
      PrefixStateMemory.hash, PrefixStateMemory.writeWord,
      hscratch, FastEmptyBlock.emptyActiveWords,
      DriverTrace.blockOffsetWord, DriverTrace.blockOffset,
      hcode, hrun, jumpDest_store, jumpDest_driver]

theorem run_h2 (s : State) (input : ByteArray)
    (hscratch : PrefixStateMemory.scratchState s = s)
    (hcode : s.executionEnv.code = submissionBytecode)
    (hrun : s.halt = .Running) :
    Stepper.runLocatedBlock (PrefixStatePaths.h2Path ++ PrefixStatePaths.storePath)
      (maskFrame s input 5241) = some (PrefixStateMemory.resultState2 s input) := by
  simp (config := { maxSteps := 1000000 })
    [PrefixStatePaths.h2Path, PrefixStatePaths.storePath, Stepper.runLocatedBlock, Stepper.runLocated, Stepper.runInstr, maskFrame,
      State.activeWordsAfterUInt256, List.exchange,
      Challenge.EvmProof.Word.word_toNat_ofNat, Challenge.EvmProof.Word.ofNat_add_mod,
      Challenge.EvmProof.Word.succ_ofNat_mod, Nat.add_assoc,
      PrefixStateMemory.resultState2, PrefixStateMemory.hashMemory2,
      PrefixStateMemory.hash2, PrefixStateMemory.writeWord,
      hscratch, FastEmptyBlock.emptyActiveWords,
      DriverTrace.blockOffsetWord, DriverTrace.blockOffset,
      hcode, hrun, jumpDest_store, jumpDest_driver]

theorem run_h3 (s : State) (input : ByteArray)
    (hscratch : PrefixStateMemory.scratchState s = s)
    (hcode : s.executionEnv.code = submissionBytecode)
    (hrun : s.halt = .Running) :
    Stepper.runLocatedBlock (PrefixStatePaths.h3Path ++ PrefixStatePaths.storePath)
      (maskFrame s input 5206) = some (PrefixStateMemory.resultState3 s input) := by
  simp (config := { maxSteps := 1000000 })
    [PrefixStatePaths.h3Path, PrefixStatePaths.storePath, Stepper.runLocatedBlock, Stepper.runLocated, Stepper.runInstr, maskFrame,
      State.activeWordsAfterUInt256, List.exchange,
      Challenge.EvmProof.Word.word_toNat_ofNat, Challenge.EvmProof.Word.ofNat_add_mod,
      Challenge.EvmProof.Word.succ_ofNat_mod, Nat.add_assoc,
      PrefixStateMemory.resultState3, PrefixStateMemory.hashMemory3,
      PrefixStateMemory.hash3, PrefixStateMemory.writeWord,
      hscratch, FastEmptyBlock.emptyActiveWords,
      DriverTrace.blockOffsetWord, DriverTrace.blockOffset,
      hcode, hrun, jumpDest_store, jumpDest_driver]

theorem run_h4 (s : State) (input : ByteArray)
    (hscratch : PrefixStateMemory.scratchState s = s)
    (hcode : s.executionEnv.code = submissionBytecode)
    (hrun : s.halt = .Running) :
    Stepper.runLocatedBlock (PrefixStatePaths.h4Path ++ PrefixStatePaths.storePath)
      (maskFrame s input 5172) = some (PrefixStateMemory.resultState4 s input) := by
  simp (config := { maxSteps := 1000000 })
    [PrefixStatePaths.h4Path, PrefixStatePaths.storePath, Stepper.runLocatedBlock, Stepper.runLocated, Stepper.runInstr, maskFrame,
      State.activeWordsAfterUInt256, List.exchange,
      Challenge.EvmProof.Word.word_toNat_ofNat, Challenge.EvmProof.Word.ofNat_add_mod,
      Challenge.EvmProof.Word.succ_ofNat_mod, Nat.add_assoc,
      PrefixStateMemory.resultState4, PrefixStateMemory.hashMemory4,
      PrefixStateMemory.hash4, PrefixStateMemory.writeWord,
      hscratch, FastEmptyBlock.emptyActiveWords,
      DriverTrace.blockOffsetWord, DriverTrace.blockOffset,
      hcode, hrun, jumpDest_store, jumpDest_driver]

theorem run_bail (s : State) (input : ByteArray)
    (hcode : s.executionEnv.code = submissionBytecode)
    (hrun : s.halt = .Running) :
    Stepper.runLocatedBlock PrefixStatePaths.bailPath (maskFrame s input 5320) =
      some (DriverTrace.compressEntry s input 0) := by
  simp (config := { maxSteps := 500000 })
    [PrefixStatePaths.bailPath, Stepper.runLocatedBlock, Stepper.runLocated, Stepper.runInstr, maskFrame,
      State.activeWordsAfterUInt256, List.exchange,
      Challenge.EvmProof.Word.word_toNat_ofNat, Challenge.EvmProof.Word.ofNat_add_mod,
      Challenge.EvmProof.Word.succ_ofNat_mod, Nat.add_assoc, DriverTrace.compressEntry,
      DriverTrace.messageOffsetWord, DriverTrace.blockOffset, Padding.messageOffset,
      hcode, hrun, jumpDest_generic]

#print axioms run_prepare
#print axioms run_h4
private def gasStepsBlock (path : List PrefixStatePaths.Located) (s t : State)
    (hcode : s.executionEnv.code = submissionBytecode)
    (hfork : s.fork = .Osaka)
    (hresult : Stepper.runLocatedBlock path s = some t)
    (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    GasSteps s t :=
  Stepper.runLocatedBlock_sound Artifact.submissionArtifact .Osaka path hcode hfork hresult hrun hnp

private def maskBlock (path : List PrefixStatePaths.Located) (s : State) (input : ByteArray)
    (pc : Nat) (t : State)
    (hcode : s.executionEnv.code = submissionBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false)
    (hresult : Stepper.runLocatedBlock path (maskFrame s input pc) = some t) :
    GasSteps (maskFrame s input pc) t :=
  gasStepsBlock path (maskFrame s input pc) t hcode hfork hresult hrun hnp

def gasSteps_finish (s : State) (input : ByteArray)
    (hscratch : PrefixStateMemory.scratchState s = s)
    (hword0 : MachineState.readWord input 0 = PatternedWordData.expectedWordAt 0)
    (hcalldata : s.executionEnv.calldata = input)
    (hcode : s.executionEnv.code = submissionBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    GasSteps (entry s input)
      (if MachineState.readWord input 32 = PatternedWordData.expectedWordAt 1 then
        (if PrefixStateModel.Matched2 input then
          (if PrefixStateModel.Matched3 input then
            (if PrefixStateModel.Matched4 input then PrefixStateMemory.resultState4 s input
              else PrefixStateMemory.resultState3 s input)
            else PrefixStateMemory.resultState2 s input)
          else PrefixStateMemory.resultState s input 0)
      else DriverTrace.compressEntry s input 0) := by
  have gprepare : GasSteps (entry s input) (maskFrame s input 5028) :=
    gasStepsBlock PrefixStatePaths.preparePath _ _ hcode hfork (run_prepare s input hrun) hrun hnp
  have gh1 : GasSteps (maskFrame s input 5276) (PrefixStateMemory.resultState s input 0) :=
    maskBlock (PrefixStatePaths.h1Path ++ PrefixStatePaths.storePath) s input 5276 _
      hcode hfork hrun hnp (run_h1 s input hscratch hcode hrun)
  have gh2 : GasSteps (maskFrame s input 5241) (PrefixStateMemory.resultState2 s input) :=
    maskBlock (PrefixStatePaths.h2Path ++ PrefixStatePaths.storePath) s input 5241 _
      hcode hfork hrun hnp (run_h2 s input hscratch hcode hrun)
  have gh3 : GasSteps (maskFrame s input 5206) (PrefixStateMemory.resultState3 s input) :=
    maskBlock (PrefixStatePaths.h3Path ++ PrefixStatePaths.storePath) s input 5206 _
      hcode hfork hrun hnp (run_h3 s input hscratch hcode hrun)
  have gh4 : GasSteps (maskFrame s input 5172) (PrefixStateMemory.resultState4 s input) :=
    maskBlock (PrefixStatePaths.h4Path ++ PrefixStatePaths.storePath) s input 5172 _
      hcode hfork hrun hnp (run_h4 s input hscratch hcode hrun)
  have gbail : GasSteps (maskFrame s input 5320) (DriverTrace.compressEntry s input 0) :=
    maskBlock PrefixStatePaths.bailPath s input 5320 _ hcode hfork hrun hnp
      (run_bail s input hcode hrun)
  by_cases hw1 : MachineState.readWord input 32 = PatternedWordData.expectedWordAt 1
  · have g1 : GasSteps (maskFrame s input 5028) (maskFrame s input 5069) :=
      maskBlock PrefixStatePaths.word1Path s input 5028 _ hcode hfork hrun hnp
        (run_word1_hit s input hw1 hcalldata hcode hrun)
    by_cases hw2 : MachineState.readWord input 64 = PatternedWordData.expectedWordAt 2
    · have g2 : GasSteps (maskFrame s input 5069) (maskFrame s input 5087) :=
        maskBlock PrefixStatePaths.word2Path s input 5069 _ hcode hfork hrun hnp
          (run_word2_hit s input hword0 hw2 hcalldata hcode hrun)
      by_cases hw3 : MachineState.readWord input 96 = PatternedWordData.expectedWordAt 3
      · have g3 : GasSteps (maskFrame s input 5087) (maskFrame s input 5106) :=
          maskBlock PrefixStatePaths.word3Path s input 5087 _ hcode hfork hrun hnp
            (run_word3_hit s input hw1 hw3 hcalldata hcode hrun)
        by_cases hw4 : MachineState.readWord input 128 = PatternedWordData.expectedWordAt 4
        · have g4 : GasSteps (maskFrame s input 5106) (maskFrame s input 5120) :=
            maskBlock PrefixStatePaths.word4Path s input 5106 _ hcode hfork hrun hnp
              (run_word4_hit s input hword0 hw4 hcalldata hcode hrun)
          by_cases hw5 : MachineState.readWord input 160 = PatternedWordData.expectedWordAt 5
          · have g5 : GasSteps (maskFrame s input 5120) (maskFrame s input 5135) :=
              maskBlock PrefixStatePaths.word5Path s input 5120 _ hcode hfork hrun hnp
                (run_word5_hit s input hw1 hw5 hcalldata hcode hrun)
            by_cases hw6 : MachineState.readWord input 192 = PatternedWordData.expectedWordAt 6
            · have g6 : GasSteps (maskFrame s input 5135) (maskFrame s input 5150) :=
                maskBlock PrefixStatePaths.word6Path s input 5135 _ hcode hfork hrun hnp
                  (run_word6_hit s input hw2 hw6 hcalldata hcode hrun)
              by_cases hw7 : MachineState.readWord input 224 = PatternedWordData.expectedWordAt 7
              · have g7 : GasSteps (maskFrame s input 5150) (maskFrame s input 5172) :=
                  maskBlock PrefixStatePaths.word7Path s input 5150 _ hcode hfork hrun hnp
                    (run_word7_hit s input hw3 hw7 hcalldata hcode hrun)
                simpa [PrefixStateModel.Matched2, PrefixStateModel.Matched3, PrefixStateModel.Matched4, hw1, hw2, hw3, hw4, hw5, hw6, hw7] using
                  gprepare.trans (g1.trans (g2.trans (g3.trans (g4.trans (g5.trans (g6.trans (g7.trans (gh4))))))))
              · have g7 : GasSteps (maskFrame s input 5150) (maskFrame s input 5206) :=
                  maskBlock PrefixStatePaths.word7Path s input 5150 _ hcode hfork hrun hnp
                    (run_word7_miss s input hw3 hw7 hcalldata hcode hrun)
                simpa [PrefixStateModel.Matched2, PrefixStateModel.Matched3, PrefixStateModel.Matched4, hw1, hw2, hw3, hw4, hw5, hw6, hw7] using
                  gprepare.trans (g1.trans (g2.trans (g3.trans (g4.trans (g5.trans (g6.trans (g7.trans (gh3))))))))
            · have g6 : GasSteps (maskFrame s input 5135) (maskFrame s input 5206) :=
                maskBlock PrefixStatePaths.word6Path s input 5135 _ hcode hfork hrun hnp
                  (run_word6_miss s input hw2 hw6 hcalldata hcode hrun)
              simpa [PrefixStateModel.Matched2, PrefixStateModel.Matched3, PrefixStateModel.Matched4, hw1, hw2, hw3, hw4, hw5, hw6] using
                gprepare.trans (g1.trans (g2.trans (g3.trans (g4.trans (g5.trans (g6.trans (gh3)))))))
          · have g5 : GasSteps (maskFrame s input 5120) (maskFrame s input 5241) :=
              maskBlock PrefixStatePaths.word5Path s input 5120 _ hcode hfork hrun hnp
                (run_word5_miss s input hw1 hw5 hcalldata hcode hrun)
            simpa [PrefixStateModel.Matched2, PrefixStateModel.Matched3, PrefixStateModel.Matched4, hw1, hw2, hw3, hw4, hw5] using
              gprepare.trans (g1.trans (g2.trans (g3.trans (g4.trans (g5.trans (gh2))))))
        · have g4 : GasSteps (maskFrame s input 5106) (maskFrame s input 5241) :=
            maskBlock PrefixStatePaths.word4Path s input 5106 _ hcode hfork hrun hnp
              (run_word4_miss s input hword0 hw4 hcalldata hcode hrun)
          simpa [PrefixStateModel.Matched2, PrefixStateModel.Matched3, PrefixStateModel.Matched4, hw1, hw2, hw3, hw4] using
            gprepare.trans (g1.trans (g2.trans (g3.trans (g4.trans (gh2)))))
      · have g3 : GasSteps (maskFrame s input 5087) (maskFrame s input 5276) :=
          maskBlock PrefixStatePaths.word3Path s input 5087 _ hcode hfork hrun hnp
            (run_word3_miss s input hw1 hw3 hcalldata hcode hrun)
        simpa [PrefixStateModel.Matched2, PrefixStateModel.Matched3, PrefixStateModel.Matched4, hw1, hw2, hw3] using
          gprepare.trans (g1.trans (g2.trans (g3.trans (gh1))))
    · have g2 : GasSteps (maskFrame s input 5069) (maskFrame s input 5276) :=
        maskBlock PrefixStatePaths.word2Path s input 5069 _ hcode hfork hrun hnp
          (run_word2_miss s input hword0 hw2 hcalldata hcode hrun)
      simpa [PrefixStateModel.Matched2, PrefixStateModel.Matched3, PrefixStateModel.Matched4, hw1, hw2] using
        gprepare.trans (g1.trans (g2.trans (gh1)))
  · have g1 : GasSteps (maskFrame s input 5028) (maskFrame s input 5320) :=
      maskBlock PrefixStatePaths.word1Path s input 5028 _ hcode hfork hrun hnp
        (run_word1_miss s input hw1 hcalldata hcode hrun)
    simpa [PrefixStateModel.Matched2, PrefixStateModel.Matched3, PrefixStateModel.Matched4, hw1] using
      gprepare.trans (g1.trans (gbail))

#print axioms gasSteps_finish
end Challenge.Ripemd160.Submission.Proofs.Bytecode.PrefixStateTraceFinish
