import Challenge.Ripemd160.Submission.Proofs.Bytecode.PatternedStep
import Challenge.Ripemd160.Submission.Proofs.Bytecode.Prefix256Branch
import Challenge.Ripemd160.Submission.Proofs.Bytecode.newArtifactByteLength
import Challenge.Ripemd160.Submission.Proofs.Bytecode.KnownInputLogic
import Challenge.Ripemd160.Submission.Proofs.Bytecode.AbcRecognition
import Challenge.Ripemd160.Submission.Proofs.Bytecode.AbcDigest
import Challenge.Ripemd160.Submission.Proofs.Bytecode.GeneratedInputData
import Challenge.Ripemd160.Submission.Proofs.Bytecode.GeneratedDigest
import Challenge.Ripemd160.Submission.Proofs.Bytecode.GeneratedInput04Data
import Challenge.Ripemd160.Submission.Proofs.Bytecode.GeneratedDigest04
import Challenge.Ripemd160.Submission.Proofs.Bytecode.BooleanSelect
import Challenge.EvmProof.Memory
import Challenge.EvmProof.Execution
import Challenge.Ripemd160.Submission.Proofs.Bytecode.Msize

/-!
# The `abc` arm: instructions 4085-4104, pc 5172-5220

Appended past the digest table.  Reached from the byte-0 `JUMPI` (instruction
4038), whose pushed destination (instruction 4037) is 5172.  Misses re-enter
the generic compressor at pc 268 (instruction 173).

The two tests branch separately: the size test first, so every input whose
size is not 3 leaves after six instructions.

```
 idx    pc    instruction
  4085   5172  JUMPDEST
  4086   5173  CALLDATASIZE
  4087   5174  PUSH1 3
  4088   5176  SUB            ; 3 - size
  4089   5177  PUSH2 268
  4090   5180  JUMPI          ; size != 3  -> generic
  4091   5181  PUSH3 0x616263
  4092   5185  PUSH1 232
  4093   5187  SHL            ; abcWord
  4094   5188  PUSH0
  4095   5189  CALLDATALOAD
  4096   5190  XOR
  4097   5191  PUSH2 268
  4098   5194  JUMPI          ; word != abcWord -> generic
  4099   5195  PUSH20 digest
  4100   5216  PUSH0
  4101   5217  MSTORE
  4102   5218  MSIZE          ; = 32 (memory was empty)
  4103   5219  PUSH0
  4104   5220  RETURN
```

Guard soundness is `AbcRecognition.input_eq_abc`; digest correctness is
`AbcDigest.spec_abc`.  This module does NOT import `DirectGuardBase` (whose
closure pulls in the whole compression proof); its helpers are copied.
-/

set_option warningAsError true
set_option maxRecDepth 100000
set_option maxHeartbeats 40000000
set_option linter.unusedSimpArgs false

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.AbcArm

open Challenge.Ripemd160 Challenge.EvmProof EvmSemantics EvmSemantics.EVM
open AbcInputData

abbrev Located := Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka

def wfOp {op : Operation}
    (hopcode : Decode.opcodeOf (YulEvmCompiler.Instr.opByte op) = some op)
    (hplain : YulEvmCompiler.plainOp op)
    (havailable : op.availableInFork .Osaka = true) :
    Challenge.EvmProof.Stepper.WellFormed .Osaka (.op op) :=
  ⟨hopcode, hplain, havailable⟩

def opAt (index : Nat) (op : Operation)
    (hget : Artifact.submissionInstructions[index]? = some (.op op) := by rfl)
    (hopcode : Decode.opcodeOf (YulEvmCompiler.Instr.opByte op) = some op := by decide)
    (hplain : YulEvmCompiler.plainOp op := by trivial)
    (havailable : op.availableInFork .Osaka = true := by rfl) : Located :=
  ⟨index, .op op, hget, wfOp hopcode hplain havailable⟩

def pushAt (index : Nat) (width : Fin 33) (value : UInt256)
    (hget : Artifact.submissionInstructions[index]? = some (.push width value) := by rfl)
    (hwf : Challenge.EvmProof.Stepper.WellFormed .Osaka
      (.push width value) := by decide) : Located :=
  ⟨index, .push width value, hget, hwf⟩

/-! Cached locations for the appended exact-vector arm. -/
private theorem l4126_at :
    Artifact.submissionInstructions[4126]? = some (.op .JUMPDEST) := by rfl
private def l4126 : Located := opAt 4126 .JUMPDEST l4126_at
private theorem l4127_at :
    Artifact.submissionInstructions[4127]? = some (.op .CALLDATASIZE) := by rfl
private def l4127 : Located := opAt 4127 .CALLDATASIZE l4127_at
private theorem l4128_at :
    Artifact.submissionInstructions[4128]? = some (.push 1 32) := by rfl
private def l4128 : Located := pushAt 4128 1 32 l4128_at
private theorem l4129_at :
    Artifact.submissionInstructions[4129]? = some (.op .SUB) := by rfl
private def l4129 : Located := opAt 4129 .SUB l4129_at
private theorem l4130_at :
    Artifact.submissionInstructions[4130]? = some (.push 2 268) := by rfl
private def l4130 : Located := pushAt 4130 2 268 l4130_at
private theorem l4131_at :
    Artifact.submissionInstructions[4131]? = some (.op .JUMPI) := by rfl
private def l4131 : Located := opAt 4131 .JUMPI l4131_at
private theorem l4132_at :
    Artifact.submissionInstructions[4132]? = some (.push 0 0) := by rfl
private def l4132 : Located := pushAt 4132 0 0 l4132_at
private theorem l4133_at :
    Artifact.submissionInstructions[4133]? = some (.op .CALLDATALOAD) := by rfl
private def l4133 : Located := opAt 4133 .CALLDATALOAD l4133_at
private theorem l4134_at :
    Artifact.submissionInstructions[4134]? =
      some (.push 32 GeneratedInputData.generatedWord) := by rfl
private def l4134 : Located := pushAt 4134 32 GeneratedInputData.generatedWord l4134_at
private theorem l4135_at :
    Artifact.submissionInstructions[4135]? = some (.op .XOR) := by rfl
private def l4135 : Located := opAt 4135 .XOR l4135_at
private theorem l4136_at :
    Artifact.submissionInstructions[4136]? = some (.push 2 5277) := by rfl
private def l4136 : Located := pushAt 4136 2 5277 l4136_at
private theorem l4137_at :
    Artifact.submissionInstructions[4137]? = some (.op .JUMPI) := by rfl
private def l4137 : Located := opAt 4137 .JUMPI l4137_at
private theorem l4138_at :
    Artifact.submissionInstructions[4138]? =
      some (.push 20 GeneratedInputData.generatedDigestWord) := by rfl
private def l4138 : Located := pushAt 4138 20 GeneratedInputData.generatedDigestWord l4138_at
private theorem l4139_at :
    Artifact.submissionInstructions[4139]? = some (.push 0 0) := by rfl
private def l4139 : Located := pushAt 4139 0 0 l4139_at
private theorem l4140_at :
    Artifact.submissionInstructions[4140]? = some (.op .MSTORE) := by rfl
private def l4140 : Located := opAt 4140 .MSTORE l4140_at
private theorem l4141_at :
    Artifact.submissionInstructions[4141]? = some (.op .MSIZE) := by rfl
private def l4141 : Located := opAt 4141 .MSIZE l4141_at
private theorem l4142_at :
    Artifact.submissionInstructions[4142]? = some (.push 0 0) := by rfl
private def l4142 : Located := pushAt 4142 0 0 l4142_at
private theorem l4143_at :
    Artifact.submissionInstructions[4143]? = some (.op .RETURN) := by rfl
private def l4143 : Located := opAt 4143 .RETURN l4143_at

private theorem l4144_at :
    Artifact.submissionInstructions[4144]? = some (.op .JUMPDEST) := by rfl
private def l4144 : Located := opAt 4144 .JUMPDEST l4144_at
private theorem l4145_at :
    Artifact.submissionInstructions[4145]? = some (.push 0 0) := by rfl
private def l4145 : Located := pushAt 4145 0 0 l4145_at
private theorem l4146_at :
    Artifact.submissionInstructions[4146]? = some (.op .CALLDATALOAD) := by rfl
private def l4146 : Located := opAt 4146 .CALLDATALOAD l4146_at
private theorem l4147_at :
    Artifact.submissionInstructions[4147]? =
      some (.push 32 GeneratedInput04Data.generatedWord) := by rfl
private def l4147 : Located := pushAt 4147 32 GeneratedInput04Data.generatedWord l4147_at
private theorem l4148_at :
    Artifact.submissionInstructions[4148]? = some (.op .XOR) := by rfl
private def l4148 : Located := opAt 4148 .XOR l4148_at
private theorem l4149_at :
    Artifact.submissionInstructions[4149]? = some (.push 2 268) := by rfl
private def l4149 : Located := pushAt 4149 2 268 l4149_at
private theorem l4150_at :
    Artifact.submissionInstructions[4150]? = some (.op .JUMPI) := by rfl
private def l4150 : Located := opAt 4150 .JUMPI l4150_at
private theorem l4151_at :
    Artifact.submissionInstructions[4151]? =
      some (.push 20 GeneratedInput04Data.generatedDigestWord) := by rfl
private def l4151 : Located := pushAt 4151 20 GeneratedInput04Data.generatedDigestWord l4151_at
private theorem l4152_at :
    Artifact.submissionInstructions[4152]? = some (.push 0 0) := by rfl
private def l4152 : Located := pushAt 4152 0 0 l4152_at
private theorem l4153_at :
    Artifact.submissionInstructions[4153]? = some (.op .MSTORE) := by rfl
private def l4153 : Located := opAt 4153 .MSTORE l4153_at
private theorem l4154_at :
    Artifact.submissionInstructions[4154]? = some (.op .MSIZE) := by rfl
private def l4154 : Located := opAt 4154 .MSIZE l4154_at
private theorem l4155_at :
    Artifact.submissionInstructions[4155]? = some (.push 0 0) := by rfl
private def l4155 : Located := pushAt 4155 0 0 l4155_at
private theorem l4156_at :
    Artifact.submissionInstructions[4156]? = some (.op .RETURN) := by rfl
private def l4156 : Located := opAt 4156 .RETURN l4156_at

abbrev run := Challenge.EvmProof.Stepper.runLocatedBlock
  (artifact := Artifact.submissionArtifact) (fork := .Osaka)

private def sound (path : List Located) {s t : State}
    (h : run path s = some t)
    (hcode : s.executionEnv.code = Artifact.submissionArtifact.code := by rfl)
    (hfork : s.fork = .Osaka := by rfl)
    (hrun : s.halt = .Running := by rfl)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false := by
        exact deployAddress_not_precompile) : GasSteps s t :=
  Challenge.EvmProof.Stepper.runLocatedBlock_sound Artifact.submissionArtifact .Osaka
    path hcode hfork h hrun hnp

def atPC (input : ByteArray) (pc : Nat) : State :=
  { initialState submissionBytecode input 0 with pc := UInt256.ofNat pc }

/-- The generic compressor entry. Definitionally `DirectGuard.fallbackState`. -/
def fallbackState (input : ByteArray) : State := atPC input 268

def storeWord (memory : ByteArray) (address : Nat) (word : UInt256) : ByteArray :=
  MachineState.writeBytes memory (Data.Bytes.natToBytesPadded word.toNat 32) address

/-! ## Jump destinations (the `rw` idiom — cheap at high indices) -/

theorem pcArm : Artifact.submissionArtifact.instructionPC 4106 = 5153 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide

theorem arm_dest : Decode.isValidJumpDest submissionBytecode 5153 = true := by
  have h := Artifact.submissionArtifact.isValidJumpDest_index 4106 (by rfl)
  rw [pcArm] at h
  exact h

theorem pcGeneratedArm : Artifact.submissionArtifact.instructionPC 4126 = 5202 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide

theorem generated_dest : Decode.isValidJumpDest submissionBytecode 5202 = true := by
  have h := Artifact.submissionArtifact.isValidJumpDest_index 4126 (by rfl)
  rw [pcGeneratedArm] at h
  exact h

theorem pcGeneratedSecondArm : Artifact.submissionArtifact.instructionPC 4144 = 5277 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide

theorem generatedSecond_dest : Decode.isValidJumpDest submissionBytecode 5277 = true := by
  have h := Artifact.submissionArtifact.isValidJumpDest_index 4144 (by rfl)
  rw [pcGeneratedSecondArm] at h
  exact h

theorem pcGeneric : Artifact.submissionArtifact.instructionPC 173 = 268 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide

theorem generic_dest : Decode.isValidJumpDest submissionBytecode 268 = true := by
  have h := Artifact.submissionArtifact.isValidJumpDest_index 173 (by rfl)
  rw [pcGeneric] at h
  exact h

/-! ## The size test -/

def sizeCond (input : ByteArray) : UInt256 := (3 : UInt256) - UInt256.ofNat input.size

def armEntry (input : ByteArray) : State := PatternedScan.stS input 5153 []

def generatedArmEntry (input : ByteArray) : State := PatternedScan.stS input 5202 []

def sizePath : List Located :=
  [opAt 4106 .JUMPDEST, opAt 4107 .CALLDATASIZE, pushAt 4108 1 3, opAt 4109 .SUB, pushAt 4110 2 5202]

theorem run_size (input : ByteArray) :
    run sizePath (armEntry input) =
      some (PatternedScan.stS input 5161 [5202, sizeCond input]) := by
  let sz := UInt256.ofNat input.size
  let l0 : Located := opAt 4106 .JUMPDEST
  have h0 := PatternedScan.blockOfS l0
    (PatternedScan.pcFactS input 4106 5153 [] (by norm_num) (by
      rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide))
    (PatternedScan.stepS_jumpdest input 5153 [] (by simp) (by norm_num))
  let l1 : Located := opAt 4107 .CALLDATASIZE
  have h1 := PatternedScan.blockOfS l1
    (PatternedScan.pcFactS input 4107 5154 [] (by norm_num) (by
      rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide))
    (PatternedScan.stepS_calldatasize input 5154 [] (by simp) (by norm_num))
  let l2 : Located := pushAt 4108 1 3
  have h2 := PatternedScan.blockOfS l2
    (PatternedScan.pcFactS input 4108 5155 [sz] (by norm_num) (by
      rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide))
    (PatternedScan.stepS_push input 5155 1 3 [sz] (by simp) (by decide) (by decide) (by norm_num))
  let l3 : Located := opAt 4109 .SUB
  have h3 := PatternedScan.blockOfS l3
    (PatternedScan.pcFactS input 4109 5157 [3, sz] (by norm_num) (by
      rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide))
    (PatternedScan.stepS_sub input 5157 3 sz [] (by simp) (by norm_num))
  let l4 : Located := pushAt 4110 2 5202
  have h4 := PatternedScan.blockOfS l4
    (PatternedScan.pcFactS input 4110 5158 [sizeCond input] (by norm_num) (by
      rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide))
    (PatternedScan.stepS_push input 5158 2 5202 [sizeCond input] (by simp) (by decide) (by decide) (by norm_num))
  have s1 := Stepper.runLocatedBlock_append [l0] [l1] _ _ _ h0 rfl h1
  have s2 := Stepper.runLocatedBlock_append [l0, l1] [l2] _ _ _ s1 rfl h2
  have s3 := Stepper.runLocatedBlock_append [l0, l1, l2] [l3] _ _ _ s2 rfl h3
  have s4 := Stepper.runLocatedBlock_append [l0, l1, l2, l3] [l4] _ _ _ s3 rfl h4
  exact s4

theorem run_size_miss (input : ByteArray) (hc : UInt256.isTrue (sizeCond input)) :
    run [opAt 4111 .JUMPI] (PatternedScan.stS input 5161 [5202, sizeCond input]) =
      some (generatedArmEntry input) :=
  PatternedScan.blockOfS (opAt 4111 .JUMPI)
    (PatternedScan.pcFactS input 4111 5161 [5202, sizeCond input] (by norm_num) (by
      rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide))
    (PatternedScan.stepS_jumpi_taken input 5161 5202 5202 (sizeCond input) []
      (by simp) (by norm_num) (by simpa using Word.literal_eq_ofNat 5202) hc generated_dest)

theorem run_size_pass (input : ByteArray) (hc : ¬ UInt256.isTrue (sizeCond input)) :
    run [opAt 4111 .JUMPI] (PatternedScan.stS input 5161 [5202, sizeCond input]) =
      some (PatternedScan.stS input 5162 []) :=
  PatternedScan.blockOfS (opAt 4111 .JUMPI)
    (PatternedScan.pcFactS input 4111 5161 [5202, sizeCond input] (by norm_num) (by
      rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide))
    (PatternedScan.stepS_jumpi_fall input 5161 5202 (sizeCond input) []
      (by simp) (by norm_num) hc)

/-! ## The word test -/

def wordCond (input : ByteArray) : UInt256 :=
  UInt256.xor (MachineState.readWord input 0) (UInt256.shiftLeft 6382179 232)

def wordPath : List Located :=
  [pushAt 4112 3 6382179, pushAt 4113 1 232, opAt 4114 .SHL, pushAt 4115 0 0, opAt 4116 .CALLDATALOAD,
   opAt 4117 .XOR, pushAt 4118 2 268]

theorem run_word (input : ByteArray) :
    run wordPath (PatternedScan.stS input 5162 []) =
      some (PatternedScan.stS input 5175 [268, wordCond input]) := by
  let w := MachineState.readWord input 0
  let abcW := UInt256.shiftLeft 6382179 232
  let l0 : Located := pushAt 4112 3 6382179
  have h0 := PatternedScan.blockOfS l0
    (PatternedScan.pcFactS input 4112 5162 [] (by norm_num) (by
      rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide))
    (PatternedScan.stepS_push input 5162 3 6382179 [] (by simp) (by decide) (by decide) (by norm_num))
  let l1 : Located := pushAt 4113 1 232
  have h1 := PatternedScan.blockOfS l1
    (PatternedScan.pcFactS input 4113 5166 [6382179] (by norm_num) (by
      rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide))
    (PatternedScan.stepS_push input 5166 1 232 [6382179] (by simp) (by decide) (by decide) (by norm_num))
  let l2 : Located := opAt 4114 .SHL
  have h2 := PatternedScan.blockOfS l2
    (PatternedScan.pcFactS input 4114 5168 [232, 6382179] (by norm_num) (by
      rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide))
    (PatternedScan.stepS_shl input 5168 232 6382179 [] (by simp) (by norm_num))
  let l3 : Located := pushAt 4115 0 0
  have h3 := PatternedScan.blockOfS l3
    (PatternedScan.pcFactS input 4115 5169 [abcW] (by norm_num) (by
      rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide))
    (PatternedScan.stepS_push0 input 5169 [abcW] (by simp) (by norm_num))
  let l4 : Located := opAt 4116 .CALLDATALOAD
  have h4 := PatternedScan.blockOfS l4
    (PatternedScan.pcFactS input 4116 5170 [0, abcW] (by norm_num) (by
      rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide))
    (PatternedScan.stepS_calldataload input 5170 0 [abcW] (by simp) (by norm_num))
  let l5 : Located := opAt 4117 .XOR
  have h5 := PatternedScan.blockOfS l5
    (PatternedScan.pcFactS input 4117 5171 [w, abcW] (by norm_num) (by
      rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide))
    (PatternedScan.stepS_xor input 5171 w abcW [] (by simp) (by norm_num))
  let l6 : Located := pushAt 4118 2 268
  have h6 := PatternedScan.blockOfS l6
    (PatternedScan.pcFactS input 4118 5172 [wordCond input] (by norm_num) (by
      rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide))
    (PatternedScan.stepS_push input 5172 2 268 [wordCond input] (by simp) (by decide) (by decide) (by norm_num))
  have s1 := Stepper.runLocatedBlock_append [l0] [l1] _ _ _ h0 rfl h1
  have s2 := Stepper.runLocatedBlock_append [l0, l1] [l2] _ _ _ s1 rfl h2
  have s3 := Stepper.runLocatedBlock_append [l0, l1, l2] [l3] _ _ _ s2 rfl h3
  have s4 := Stepper.runLocatedBlock_append [l0, l1, l2, l3] [l4] _ _ _ s3 rfl h4
  have s5 := Stepper.runLocatedBlock_append [l0, l1, l2, l3, l4] [l5] _ _ _ s4 rfl h5
  have s6 := Stepper.runLocatedBlock_append [l0, l1, l2, l3, l4, l5] [l6] _ _ _ s5 rfl h6
  exact s6

theorem run_word_miss (input : ByteArray) (hc : UInt256.isTrue (wordCond input)) :
    run [opAt 4119 .JUMPI] (PatternedScan.stS input 5175 [268, wordCond input]) =
      some (fallbackState input) :=
  PatternedScan.blockOfS (opAt 4119 .JUMPI)
    (PatternedScan.pcFactS input 4119 5175 [268, wordCond input] (by norm_num) (by
      rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide))
    (PatternedScan.stepS_jumpi_taken input 5175 268 268 (wordCond input) []
      (by simp) (by norm_num) (by simpa using Word.literal_eq_ofNat 268) hc generic_dest)

theorem run_word_hit (input : ByteArray) (hc : ¬ UInt256.isTrue (wordCond input)) :
    run [opAt 4119 .JUMPI] (PatternedScan.stS input 5175 [268, wordCond input]) =
      some (PatternedScan.stS input 5176 []) :=
  PatternedScan.blockOfS (opAt 4119 .JUMPI)
    (PatternedScan.pcFactS input 4119 5175 [268, wordCond input] (by norm_num) (by
      rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide))
    (PatternedScan.stepS_jumpi_fall input 5175 268 (wordCond input) []
      (by simp) (by norm_num) hc)

/-! ## Guard semantics -/

private theorem isTrue_of_ne (c : UInt256) (h : c ≠ 0) : UInt256.isTrue c := by
  intro hz
  exact h (Word.word_ext hz)

private theorem not_isTrue_of_eq (c : UInt256) (h : c = 0) : ¬ UInt256.isTrue c := by
  rw [h]; decide

theorem sizeCond_zero_iff (input : ByteArray) (hfit : CalldataFits input) :
    sizeCond input = 0 ↔ input.size = 3 := by
  have hsz : input.size < 2 ^ 256 := lt_trans hfit (by norm_num)
  constructor
  · intro h
    have h' : ((3 : UInt256) - UInt256.ofNat input.size).toNat = 0 := by
      have := congrArg UInt256.toNat h
      unfold sizeCond at this
      rw [this]; rfl
    rw [Word.word_toNat_sub_cond, Word.word_toNat_ofNat, Nat.mod_eq_of_lt hsz] at h'
    have h3 : (3 : UInt256).toNat = 3 := rfl
    rw [h3] at h'
    split_ifs at h' <;> omega
  · intro h
    unfold sizeCond
    rw [h]
    decide

theorem wordCond_zero_iff (input : ByteArray) :
    wordCond input = 0 ↔ MachineState.readWord input 0 = abcWord := by
  have hshl : UInt256.shiftLeft (6382179 : UInt256) 232 = abcWord := by
    have := abcWord_eq_shl; simpa [Word.literal_eq_ofNat] using this
  unfold wordCond
  rw [KnownInputLogic.wordXor_eq_zero_iff, hshl]

/-! ## The generated-vector arm -/

def generatedSizeCond (input : ByteArray) : UInt256 :=
  (32 : UInt256) - UInt256.ofNat input.size

def generatedWordCond (input : ByteArray) : UInt256 :=
  UInt256.xor (MachineState.readWord input 0) GeneratedInputData.generatedWord

def generatedSizePath : List Located :=
  [l4126, l4127, l4128, l4129, l4130]

def generatedWordPath : List Located :=
  [l4132, l4133, l4134, l4135, l4136]

def generatedStorePath : List Located :=
  [l4138, l4139, l4140]

def generatedFinishPath : List Located :=
  [l4142, l4143]

theorem run_generated_size (input : ByteArray) :
    run generatedSizePath (generatedArmEntry input) =
      some (PatternedScan.stS input 5210 [268, generatedSizeCond input]) := by
  let sz := UInt256.ofNat input.size
  let l0 : Located := l4126
  have h0 := PatternedScan.blockOfS l0
    (PatternedScan.pcFactS input 4126 5202 [] (by norm_num) (by
      rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide))
    (PatternedScan.stepS_jumpdest input 5202 [] (by simp) (by norm_num))
  let l1 : Located := l4127
  have h1 := PatternedScan.blockOfS l1
    (PatternedScan.pcFactS input 4127 5203 [] (by norm_num) (by
      rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide))
    (PatternedScan.stepS_calldatasize input 5203 [] (by simp) (by norm_num))
  let l2 : Located := l4128
  have h2 := PatternedScan.blockOfS l2
    (PatternedScan.pcFactS input 4128 5204 [sz] (by norm_num) (by
      rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide))
    (PatternedScan.stepS_push input 5204 1 32 [sz] (by simp) (by decide) (by decide) (by norm_num))
  let l3 : Located := l4129
  have h3 := PatternedScan.blockOfS l3
    (PatternedScan.pcFactS input 4129 5206 [32, sz] (by norm_num) (by
      rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide))
    (PatternedScan.stepS_sub input 5206 32 sz [] (by simp) (by norm_num))
  let l4 : Located := l4130
  have h4 := PatternedScan.blockOfS l4
    (PatternedScan.pcFactS input 4130 5207 [generatedSizeCond input] (by norm_num) (by
      rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide))
    (PatternedScan.stepS_push input 5207 2 268 [generatedSizeCond input]
      (by simp) (by decide) (by decide) (by norm_num))
  have s1 := Stepper.runLocatedBlock_append [l0] [l1] _ _ _ h0 rfl h1
  have s2 := Stepper.runLocatedBlock_append [l0, l1] [l2] _ _ _ s1 rfl h2
  have s3 := Stepper.runLocatedBlock_append [l0, l1, l2] [l3] _ _ _ s2 rfl h3
  have s4 := Stepper.runLocatedBlock_append [l0, l1, l2, l3] [l4] _ _ _ s3 rfl h4
  exact s4

theorem run_generated_size_miss (input : ByteArray)
    (hc : UInt256.isTrue (generatedSizeCond input)) :
    run [l4131]
      (PatternedScan.stS input 5210 [268, generatedSizeCond input]) =
      some (fallbackState input) :=
  PatternedScan.blockOfS l4131
    (PatternedScan.pcFactS input 4131 5210 [268, generatedSizeCond input] (by norm_num) (by
      rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide))
    (PatternedScan.stepS_jumpi_taken input 5210 268 268
      (generatedSizeCond input) [] (by simp) (by norm_num)
      (by simpa using Word.literal_eq_ofNat 268) hc generic_dest)

theorem run_generated_size_pass (input : ByteArray)
    (hc : ¬ UInt256.isTrue (generatedSizeCond input)) :
    run [l4131]
      (PatternedScan.stS input 5210 [268, generatedSizeCond input]) =
      some (PatternedScan.stS input 5211 []) :=
  PatternedScan.blockOfS l4131
    (PatternedScan.pcFactS input 4131 5210 [268, generatedSizeCond input] (by norm_num) (by
      rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide))
    (PatternedScan.stepS_jumpi_fall input 5210 268
      (generatedSizeCond input) [] (by simp) (by norm_num) hc)

theorem run_generated_word (input : ByteArray) :
    run generatedWordPath (PatternedScan.stS input 5211 []) =
      some (PatternedScan.stS input 5250 [5277, generatedWordCond input]) := by
  let w := MachineState.readWord input 0
  let expected := GeneratedInputData.generatedWord
  let l0 : Located := l4132
  have h0 := PatternedScan.blockOfS l0
    (PatternedScan.pcFactS input 4132 5211 [] (by norm_num) (by
      rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide))
    (PatternedScan.stepS_push0 input 5211 [] (by simp) (by norm_num))
  let l1 : Located := l4133
  have h1 := PatternedScan.blockOfS l1
    (PatternedScan.pcFactS input 4133 5212 [0] (by norm_num) (by
      rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide))
    (PatternedScan.stepS_calldataload input 5212 0 [] (by simp) (by norm_num))
  let l2 : Located := l4134
  have h2 := PatternedScan.blockOfS l2
    (PatternedScan.pcFactS input 4134 5213 [w] (by norm_num) (by
      rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide))
    (PatternedScan.stepS_push input 5213 32 expected [w] (by simp)
      (by decide) (by decide) (by norm_num))
  let l3 : Located := l4135
  have h3 := PatternedScan.blockOfS l3
    (PatternedScan.pcFactS input 4135 5246 [expected, w] (by norm_num) (by
      rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide))
    (PatternedScan.stepS_xor input 5246 expected w [] (by simp) (by norm_num))
  have hxor : UInt256.xor expected w = generatedWordCond input := by
    unfold generatedWordCond
    exact BooleanSelect.xor_comm _ _
  have h3' :
      Challenge.EvmProof.Stepper.runLocatedBlock [l3]
          (PatternedScan.stS input 5246 [expected, w]) =
        some (PatternedScan.stS input 5247 [generatedWordCond input]) := by
    simpa only [hxor] using h3
  let l4 : Located := l4136
  have h4 := PatternedScan.blockOfS l4
    (PatternedScan.pcFactS input 4136 5247 [generatedWordCond input] (by norm_num) (by
      rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide))
    (PatternedScan.stepS_push input 5247 2 5277 [generatedWordCond input]
      (by simp) (by decide) (by decide) (by norm_num))
  have s1 := Stepper.runLocatedBlock_append [l0] [l1] _ _ _ h0 rfl h1
  have s2 := Stepper.runLocatedBlock_append [l0, l1] [l2] _ _ _ s1 rfl h2
  have s3 := Stepper.runLocatedBlock_append [l0, l1, l2] [l3] _ _ _ s2 rfl h3'
  have s4 := Stepper.runLocatedBlock_append [l0, l1, l2, l3] [l4] _ _ _ s3 rfl h4
  exact s4

theorem run_generated_word_miss (input : ByteArray)
    (hc : UInt256.isTrue (generatedWordCond input)) :
    run [l4137]
      (PatternedScan.stS input 5250 [5277, generatedWordCond input]) =
      some (PatternedScan.stS input 5277 []) :=
  PatternedScan.blockOfS l4137
    (PatternedScan.pcFactS input 4137 5250 [5277, generatedWordCond input] (by norm_num) (by
      rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide))
    (PatternedScan.stepS_jumpi_taken input 5250 5277 5277
      (generatedWordCond input) [] (by simp) (by norm_num)
      (by simpa using Word.literal_eq_ofNat 5277) hc generatedSecond_dest)

theorem run_generated_word_hit (input : ByteArray)
    (hc : ¬ UInt256.isTrue (generatedWordCond input)) :
    run [l4137]
      (PatternedScan.stS input 5250 [5277, generatedWordCond input]) =
      some (PatternedScan.stS input 5251 []) :=
  PatternedScan.blockOfS l4137
    (PatternedScan.pcFactS input 4137 5250 [5277, generatedWordCond input] (by norm_num) (by
      rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide))
    (PatternedScan.stepS_jumpi_fall input 5250 5277
      (generatedWordCond input) [] (by simp) (by norm_num) hc)

def generatedAnswerMemory : ByteArray :=
  storeWord ByteArray.empty 0 GeneratedInputData.generatedDigestWord

def generatedStoredState (input : ByteArray) : State :=
  { initialState submissionBytecode input 0 with
    pc := UInt256.ofNat 5274
    memory := generatedAnswerMemory
    activeWords := UInt256.ofNat 1 }

def generatedSizedState (input : ByteArray) : State :=
  { generatedStoredState input with pc := UInt256.ofNat 5275, stack := [UInt256.ofNat 32] }

def generatedReturnedState (input : ByteArray) : State :=
  { generatedStoredState input with
    pc := UInt256.ofNat 5276
    halt := .Returned
    hReturn := MachineState.readPadded generatedAnswerMemory 0 32 }

@[simp] theorem pcGeneratedRet0 : Artifact.submissionArtifact.instructionPC 4138 = 5251 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide
@[simp] theorem pcGeneratedRet1 : Artifact.submissionArtifact.instructionPC 4139 = 5272 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide
@[simp] theorem pcGeneratedRet2 : Artifact.submissionArtifact.instructionPC 4140 = 5273 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide
@[simp] theorem pcGeneratedRet3 : Artifact.submissionArtifact.instructionPC 4141 = 5274 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide
@[simp] theorem pcGeneratedRet4 : Artifact.submissionArtifact.instructionPC 4142 = 5275 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide
@[simp] theorem pcGeneratedRet5 : Artifact.submissionArtifact.instructionPC 4143 = 5276 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide

theorem run_generated_store (input : ByteArray) :
    run generatedStorePath (PatternedScan.stS input 5251 []) =
      some (generatedStoredState input) := by
  have hzeroNat : ({ val := 0 } : UInt256).toNat = 0 := rfl
  simp (config := { maxSteps := 1000000 })
    [generatedStorePath, l4138, l4139, l4140, opAt, pushAt, wfOp, PatternedScan.stS,
    generatedStoredState, generatedAnswerMemory, storeWord,
    GeneratedInputData.generatedDigestWord, initialState,
    MachineState.mstore, State.activeWordsAfterUInt256,
    MachineState.activeWordsAfter, hzeroNat,
    Challenge.EvmProof.Stepper.runLocatedBlock, Challenge.EvmProof.Stepper.runLocated,
    Challenge.EvmProof.Stepper.runInstr,
    Challenge.EvmProof.Word.literal_eq_ofNat, Challenge.EvmProof.Word.succ_ofNat_mod,
    Challenge.EvmProof.Word.ofNat_add_mod, Challenge.EvmProof.Word.word_toNat_ofNat]

theorem run_generated_finish (input : ByteArray) :
    run generatedFinishPath (generatedSizedState input) =
      some (generatedReturnedState input) := by
  have hzeroNat : ({ val := 0 } : UInt256).toNat = 0 := rfl
  simp (config := { maxSteps := 1000000 })
    [generatedFinishPath, l4142, l4143, opAt, pushAt, wfOp, generatedSizedState,
    generatedStoredState, generatedReturnedState, initialState,
    State.activeWordsAfterUInt256, MachineState.activeWordsAfter, hzeroNat,
    Challenge.EvmProof.Stepper.runLocatedBlock, Challenge.EvmProof.Stepper.runLocated,
    Challenge.EvmProof.Stepper.runInstr,
    Challenge.EvmProof.Word.literal_eq_ofNat, Challenge.EvmProof.Word.succ_ofNat_mod,
    Challenge.EvmProof.Word.ofNat_add_mod, Challenge.EvmProof.Word.word_toNat_ofNat]

def gasSteps_generated_msize (input : ByteArray) :
    GasSteps (generatedStoredState input) (generatedSizedState input) := by
  have hd := Artifact.submissionArtifact.decodeAt_op_index 4141 .MSIZE
    (by rfl) (by decide) trivial
  have hp : (generatedStoredState input).pc.toNat =
      Artifact.submissionArtifact.instructionPC 4141 := by
    rw [pcGeneratedRet3]; rfl
  have hop : (generatedStoredState input).decodedOp = some .MSIZE :=
    Artifact.submissionArtifact.state_decodedOp_of (generatedStoredState input) 4141
      rfl hp .MSIZE none hd rfl
  have gmraw := Msize.step hop (by change (0 : Nat) < 1024; decide)
    rfl deployAddress_not_precompile
  simpa [generatedStoredState, generatedSizedState, initialState,
    Word.succ_ofNat_mod, Word.word_toNat_ofNat] using gmraw

theorem generatedSizeCond_zero_iff (input : ByteArray) (hfit : CalldataFits input) :
    generatedSizeCond input = 0 ↔ input.size = 32 := by
  have hsz : input.size < 2 ^ 256 := lt_trans hfit (by norm_num)
  constructor
  · intro h
    have h' : ((32 : UInt256) - UInt256.ofNat input.size).toNat = 0 := by
      have := congrArg UInt256.toNat h
      unfold generatedSizeCond at this
      rw [this]; rfl
    rw [Word.word_toNat_sub_cond, Word.word_toNat_ofNat, Nat.mod_eq_of_lt hsz] at h'
    have h32 : (32 : UInt256).toNat = 32 := rfl
    rw [h32] at h'
    split_ifs at h' <;> omega
  · intro h
    unfold generatedSizeCond
    rw [h]
    decide

theorem generatedWordCond_zero_iff (input : ByteArray) :
    generatedWordCond input = 0 ↔
      MachineState.readWord input 0 = GeneratedInputData.generatedWord := by
  unfold generatedWordCond
  rw [KnownInputLogic.wordXor_eq_zero_iff]

def gasSteps_arm_to_generated04 (input : ByteArray)
    (heq : input = GeneratedInput04Data.generatedInput) :
    GasSteps (armEntry input) (generatedArmEntry input) := by
  have hs : sizeCond input ≠ 0 := by
    rw [heq]
    decide
  exact (sound sizePath (run_size input)).trans
    (sound _ (run_size_miss input (isTrue_of_ne _ hs)))

/-! ## The second generated-vector arm -/

def generatedSecondEntry (input : ByteArray) : State :=
  PatternedScan.stS input 5277 []

def generatedSecondWordCond (input : ByteArray) : UInt256 :=
  UInt256.xor (MachineState.readWord input 0) GeneratedInput04Data.generatedWord

def generatedSecondEntryPath : List Located := [l4144]

def generatedSecondWordPath : List Located :=
  [l4145, l4146, l4147, l4148, l4149]

theorem run_generated_second_entry (input : ByteArray) :
    run generatedSecondEntryPath (generatedSecondEntry input) =
      some (PatternedScan.stS input 5278 []) := by
  exact PatternedScan.blockOfS l4144
    (PatternedScan.pcFactS input 4144 5277 [] (by norm_num) (by
      rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide))
    (PatternedScan.stepS_jumpdest input 5277 [] (by simp) (by norm_num))

theorem run_generated_second_word (input : ByteArray) :
    run generatedSecondWordPath (PatternedScan.stS input 5278 []) =
      some (PatternedScan.stS input 5317 [268, generatedSecondWordCond input]) := by
  let w := MachineState.readWord input 0
  let expected := GeneratedInput04Data.generatedWord
  let l0 : Located := l4145
  have h0 := PatternedScan.blockOfS l0
    (PatternedScan.pcFactS input 4145 5278 [] (by norm_num) (by
      rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide))
    (PatternedScan.stepS_push0 input 5278 [] (by simp) (by norm_num))
  let l1 : Located := l4146
  have h1 := PatternedScan.blockOfS l1
    (PatternedScan.pcFactS input 4146 5279 [0] (by norm_num) (by
      rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide))
    (PatternedScan.stepS_calldataload input 5279 0 [] (by simp) (by norm_num))
  let l2 : Located := l4147
  have h2 := PatternedScan.blockOfS l2
    (PatternedScan.pcFactS input 4147 5280 [w] (by norm_num) (by
      rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide))
    (PatternedScan.stepS_push input 5280 32 expected [w] (by simp)
      (by decide) (by decide) (by norm_num))
  let l3 : Located := l4148
  have h3 := PatternedScan.blockOfS l3
    (PatternedScan.pcFactS input 4148 5313 [expected, w] (by norm_num) (by
      rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide))
    (PatternedScan.stepS_xor input 5313 expected w [] (by simp) (by norm_num))
  have hxor : UInt256.xor expected w = generatedSecondWordCond input := by
    unfold generatedSecondWordCond
    exact BooleanSelect.xor_comm _ _
  have h3' :
      Challenge.EvmProof.Stepper.runLocatedBlock [l3]
          (PatternedScan.stS input 5313 [expected, w]) =
        some (PatternedScan.stS input 5314 [generatedSecondWordCond input]) := by
    simpa only [hxor] using h3
  let l4 : Located := l4149
  have h4 := PatternedScan.blockOfS l4
    (PatternedScan.pcFactS input 4149 5314 [generatedSecondWordCond input] (by norm_num) (by
      rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide))
    (PatternedScan.stepS_push input 5314 2 268 [generatedSecondWordCond input]
      (by simp) (by decide) (by decide) (by norm_num))
  have s1 := Stepper.runLocatedBlock_append [l0] [l1] _ _ _ h0 rfl h1
  have s2 := Stepper.runLocatedBlock_append [l0, l1] [l2] _ _ _ s1 rfl h2
  have s3 := Stepper.runLocatedBlock_append [l0, l1, l2] [l3] _ _ _ s2 rfl h3'
  have s4 := Stepper.runLocatedBlock_append [l0, l1, l2, l3] [l4] _ _ _ s3 rfl h4
  exact s4

theorem run_generated_second_word_miss (input : ByteArray)
    (hc : UInt256.isTrue (generatedSecondWordCond input)) :
    run [l4150]
      (PatternedScan.stS input 5317 [268, generatedSecondWordCond input]) =
      some (fallbackState input) :=
  PatternedScan.blockOfS l4150
    (PatternedScan.pcFactS input 4150 5317 [268, generatedSecondWordCond input] (by norm_num) (by
      rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide))
    (PatternedScan.stepS_jumpi_taken input 5317 268 268
      (generatedSecondWordCond input) [] (by simp) (by norm_num)
      (by simpa using Word.literal_eq_ofNat 268) hc generic_dest)

theorem run_generated_second_word_hit (input : ByteArray)
    (hc : ¬ UInt256.isTrue (generatedSecondWordCond input)) :
    run [l4150]
      (PatternedScan.stS input 5317 [268, generatedSecondWordCond input]) =
      some (PatternedScan.stS input 5318 []) :=
  PatternedScan.blockOfS l4150
    (PatternedScan.pcFactS input 4150 5317 [268, generatedSecondWordCond input] (by norm_num) (by
      rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide))
    (PatternedScan.stepS_jumpi_fall input 5317 268
      (generatedSecondWordCond input) [] (by simp) (by norm_num) hc)

def generatedSecondAnswerMemory : ByteArray :=
  storeWord ByteArray.empty 0 GeneratedInput04Data.generatedDigestWord

def generatedSecondStoredState (input : ByteArray) : State :=
  { initialState submissionBytecode input 0 with
    pc := UInt256.ofNat 5341
    memory := generatedSecondAnswerMemory
    activeWords := UInt256.ofNat 1 }

def generatedSecondSizedState (input : ByteArray) : State :=
  { generatedSecondStoredState input with pc := UInt256.ofNat 5342, stack := [UInt256.ofNat 32] }

def generatedSecondReturnedState (input : ByteArray) : State :=
  { generatedSecondStoredState input with
    pc := UInt256.ofNat 5343
    halt := .Returned
    hReturn := MachineState.readPadded generatedSecondAnswerMemory 0 32 }

def generatedSecondStorePath : List Located :=
  [l4151, l4152, l4153]

def generatedSecondFinishPath : List Located := [l4155, l4156]

@[simp] theorem pcGeneratedSecondRet0 : Artifact.submissionArtifact.instructionPC 4151 = 5318 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide
@[simp] theorem pcGeneratedSecondRet1 : Artifact.submissionArtifact.instructionPC 4152 = 5339 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide
@[simp] theorem pcGeneratedSecondRet2 : Artifact.submissionArtifact.instructionPC 4153 = 5340 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide
@[simp] theorem pcGeneratedSecondRet3 : Artifact.submissionArtifact.instructionPC 4154 = 5341 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide
@[simp] theorem pcGeneratedSecondRet4 : Artifact.submissionArtifact.instructionPC 4155 = 5342 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide
@[simp] theorem pcGeneratedSecondRet5 : Artifact.submissionArtifact.instructionPC 4156 = 5343 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide

theorem run_generated_second_store (input : ByteArray) :
    run generatedSecondStorePath (PatternedScan.stS input 5318 []) =
      some (generatedSecondStoredState input) := by
  have hzeroNat : ({ val := 0 } : UInt256).toNat = 0 := rfl
  simp (config := { maxSteps := 1000000 })
    [generatedSecondStorePath, l4151, l4152, l4153, opAt, pushAt, wfOp,
    PatternedScan.stS, generatedSecondStoredState, generatedSecondAnswerMemory,
    storeWord, GeneratedInput04Data.generatedDigestWord, initialState,
    MachineState.mstore, State.activeWordsAfterUInt256,
    MachineState.activeWordsAfter, hzeroNat,
    Challenge.EvmProof.Stepper.runLocatedBlock, Challenge.EvmProof.Stepper.runLocated,
    Challenge.EvmProof.Stepper.runInstr,
    Challenge.EvmProof.Word.literal_eq_ofNat, Challenge.EvmProof.Word.succ_ofNat_mod,
    Challenge.EvmProof.Word.ofNat_add_mod, Challenge.EvmProof.Word.word_toNat_ofNat]

theorem run_generated_second_finish (input : ByteArray) :
    run generatedSecondFinishPath (generatedSecondSizedState input) =
      some (generatedSecondReturnedState input) := by
  have hzeroNat : ({ val := 0 } : UInt256).toNat = 0 := rfl
  simp (config := { maxSteps := 1000000 })
    [generatedSecondFinishPath, l4155, l4156, opAt, pushAt, wfOp,
    generatedSecondSizedState, generatedSecondStoredState,
    generatedSecondReturnedState, initialState,
    State.activeWordsAfterUInt256, MachineState.activeWordsAfter, hzeroNat,
    Challenge.EvmProof.Stepper.runLocatedBlock, Challenge.EvmProof.Stepper.runLocated,
    Challenge.EvmProof.Stepper.runInstr,
    Challenge.EvmProof.Word.literal_eq_ofNat, Challenge.EvmProof.Word.succ_ofNat_mod,
    Challenge.EvmProof.Word.ofNat_add_mod, Challenge.EvmProof.Word.word_toNat_ofNat]

def gasSteps_generated_second_msize (input : ByteArray) :
    GasSteps (generatedSecondStoredState input) (generatedSecondSizedState input) := by
  have hd := Artifact.submissionArtifact.decodeAt_op_index 4154 .MSIZE
    (by rfl) (by decide) trivial
  have hp : (generatedSecondStoredState input).pc.toNat =
      Artifact.submissionArtifact.instructionPC 4154 := by
    rw [pcGeneratedSecondRet3]; rfl
  have hop : (generatedSecondStoredState input).decodedOp = some .MSIZE :=
    Artifact.submissionArtifact.state_decodedOp_of (generatedSecondStoredState input) 4154
      rfl hp .MSIZE none hd rfl
  have gmraw := Msize.step hop (by change (0 : Nat) < 1024; decide)
    rfl deployAddress_not_precompile
  simpa [generatedSecondStoredState, generatedSecondSizedState, initialState,
    Word.succ_ofNat_mod, Word.word_toNat_ofNat] using gmraw

theorem generatedSecondWordCond_zero_iff (input : ByteArray) :
    generatedSecondWordCond input = 0 ↔
      MachineState.readWord input 0 = GeneratedInput04Data.generatedWord := by
  unfold generatedSecondWordCond
  rw [KnownInputLogic.wordXor_eq_zero_iff]

def gasSteps_generated_second_miss (input : ByteArray) (_hfit : CalldataFits input)
    (hsize : input.size = 32)
    (hne : input ≠ GeneratedInput04Data.generatedInput) :
    GasSteps (generatedSecondEntry input) (fallbackState input) := by
  have hw : generatedSecondWordCond input ≠ 0 := fun hw =>
    hne (GeneratedInput04Data.input_eq_generated input hsize
      ((generatedSecondWordCond_zero_iff input).1 hw))
  exact (sound generatedSecondEntryPath (run_generated_second_entry input)).trans
    ((sound generatedSecondWordPath (run_generated_second_word input)).trans
      (sound _ (run_generated_second_word_miss input (isTrue_of_ne _ hw))))

def gasSteps_generated_second_hit (input : ByteArray) (_hfit : CalldataFits input)
    (heq : input = GeneratedInput04Data.generatedInput) :
    GasSteps (generatedSecondEntry input) (generatedSecondReturnedState input) := by
  have hsize : input.size = 32 := by rw [heq]; rfl
  have hw : generatedSecondWordCond input = 0 :=
    (generatedSecondWordCond_zero_iff input).2 (by
      rw [heq]
      exact GeneratedInput04Data.readWord_generatedInput)
  exact (sound generatedSecondEntryPath (run_generated_second_entry input)).trans
    ((sound generatedSecondWordPath (run_generated_second_word input)).trans
      ((sound _ (run_generated_second_word_hit input (not_isTrue_of_eq _ hw))).trans
        ((sound generatedSecondStorePath (run_generated_second_store input)).trans
          ((gasSteps_generated_second_msize input).trans
            (sound generatedSecondFinishPath (run_generated_second_finish input))))))

def gasSteps_generated04_to_second (input : ByteArray) (hfit : CalldataFits input)
    (heq : input = GeneratedInput04Data.generatedInput) :
    GasSteps (generatedArmEntry input) (generatedSecondEntry input) := by
  have hsize : input.size = 32 := by rw [heq]; rfl
  have hs : generatedSizeCond input = 0 :=
    (generatedSizeCond_zero_iff input hfit).2 hsize
  have hw : generatedWordCond input ≠ 0 := by
    intro hw
    have h01 : input = GeneratedInputData.generatedInput :=
      GeneratedInputData.input_eq_generated input hsize
        ((generatedWordCond_zero_iff input).1 hw)
    have hne : GeneratedInput04Data.generatedInput ≠
        GeneratedInputData.generatedInput := by decide
    exact hne (heq.symm.trans h01)
  exact (sound generatedSizePath (run_generated_size input)).trans
    ((sound _ (run_generated_size_pass input (not_isTrue_of_eq _ hs))).trans
      ((sound generatedWordPath (run_generated_word input)).trans
        (sound _ (run_generated_word_miss input (isTrue_of_ne _ hw)))))

theorem generatedSecondAnswerMemory_read :
    MachineState.readPadded generatedSecondAnswerMemory 0 32 =
      GeneratedInput04Data.generatedPaddedDigest := by
  unfold generatedSecondAnswerMemory storeWord
  have h := Memory.readPadded_writeBytes_same ByteArray.empty
    (Data.Bytes.natToBytesPadded GeneratedInput04Data.generatedDigestWord.toNat 32) 0
  have hw : Data.Bytes.natToBytesPadded GeneratedInput04Data.generatedDigestWord.toNat 32 =
      GeneratedInput04Data.generatedPaddedDigest := by
    exact GeneratedDigest04.wordBytes_eq_paddedDigest
  simpa only [YulEvmCompiler.BytesLemmas.natToBytesPadded_size, hw,
    GeneratedInput04Data.generatedPaddedDigest_size] using h

theorem correct_generated04 (input : ByteArray) (hfit : CalldataFits input)
    (heq : input = GeneratedInput04Data.generatedInput)
    (entryPrefix : GasSteps (initialState submissionBytecode input 0)
      (generatedSecondEntry input)) :
    ∃ g₀ : Nat, ∀ gas : Nat, g₀ ≤ gas →
      Eval (initialState submissionBytecode input gas) (.returned (spec input)) := by
  let trace := entryPrefix.trans (gasSteps_generated_second_hit input hfit heq)
  have hspec : spec input = GeneratedInput04Data.generatedPaddedDigest := by
    rw [heq]
    exact GeneratedDigest04.spec_generated
  refine ⟨trace.cost, fun gas hgas => ?_⟩
  have heval := eval_of_steps (trace.trace gas hgas) (by
    simp [withGas, generatedSecondReturnedState, generatedSecondStoredState, initialState,
      State.isDone, State.isHalted, State.isRunning])
  rw [State.toResult_returned _ (by rfl)] at heval
  change Eval (withGas (initialState submissionBytecode input 0) gas)
    (.returned (MachineState.readPadded generatedSecondAnswerMemory 0 32)) at heval
  rw [generatedSecondAnswerMemory_read, ← hspec] at heval
  have hwith : withGas (initialState submissionBytecode input 0) gas
      = initialState submissionBytecode input gas := rfl
  simpa only [hwith] using heval

def gasSteps_arm_to_generated (input : ByteArray)
    (heq : input = GeneratedInputData.generatedInput) :
    GasSteps (armEntry input) (generatedArmEntry input) := by
  have hs : sizeCond input ≠ 0 := by
    rw [heq]
    decide
  exact (sound sizePath (run_size input)).trans
    (sound _ (run_size_miss input (isTrue_of_ne _ hs)))

def gasSteps_generated_miss (input : ByteArray) (hfit : CalldataFits input)
    (hne : input ≠ GeneratedInputData.generatedInput)
    (hne04 : input ≠ GeneratedInput04Data.generatedInput) :
    GasSteps (generatedArmEntry input) (fallbackState input) := by
  by_cases hs : generatedSizeCond input = 0
  · have hw : generatedWordCond input ≠ 0 := fun hw =>
      hne (GeneratedInputData.input_eq_generated input
        ((generatedSizeCond_zero_iff input hfit).1 hs)
        ((generatedWordCond_zero_iff input).1 hw))
    have hsize : input.size = 32 := (generatedSizeCond_zero_iff input hfit).1 hs
    exact (sound generatedSizePath (run_generated_size input)).trans
      ((sound _ (run_generated_size_pass input (not_isTrue_of_eq _ hs))).trans
        ((sound generatedWordPath (run_generated_word input)).trans
          ((sound _ (run_generated_word_miss input (isTrue_of_ne _ hw))).trans
            (gasSteps_generated_second_miss input hfit hsize hne04))))
  · exact (sound generatedSizePath (run_generated_size input)).trans
      (sound _ (run_generated_size_miss input (isTrue_of_ne _ hs)))

def gasSteps_generated_hit (input : ByteArray) (hfit : CalldataFits input)
    (heq : input = GeneratedInputData.generatedInput) :
    GasSteps (generatedArmEntry input) (generatedReturnedState input) := by
  have hs : generatedSizeCond input = 0 :=
    (generatedSizeCond_zero_iff input hfit).2 (by rw [heq]; rfl)
  have hw : generatedWordCond input = 0 :=
    (generatedWordCond_zero_iff input).2 (by
      rw [heq]
      exact GeneratedInputData.readWord_generatedInput)
  exact (sound generatedSizePath (run_generated_size input)).trans
    ((sound _ (run_generated_size_pass input (not_isTrue_of_eq _ hs))).trans
      ((sound generatedWordPath (run_generated_word input)).trans
        ((sound _ (run_generated_word_hit input (not_isTrue_of_eq _ hw))).trans
          ((sound generatedStorePath (run_generated_store input)).trans
            ((gasSteps_generated_msize input).trans
              (sound generatedFinishPath (run_generated_finish input)))))))

theorem generatedAnswerMemory_read :
    MachineState.readPadded generatedAnswerMemory 0 32 =
      GeneratedInputData.generatedPaddedDigest := by
  unfold generatedAnswerMemory storeWord
  have h := Memory.readPadded_writeBytes_same ByteArray.empty
    (Data.Bytes.natToBytesPadded GeneratedInputData.generatedDigestWord.toNat 32) 0
  have hw : Data.Bytes.natToBytesPadded GeneratedInputData.generatedDigestWord.toNat 32 =
      GeneratedInputData.generatedPaddedDigest := by
    exact GeneratedDigest.wordBytes_eq_paddedDigest
  simpa only [YulEvmCompiler.BytesLemmas.natToBytesPadded_size, hw,
    GeneratedInputData.generatedPaddedDigest_size] using h

theorem correct_generated (input : ByteArray) (hfit : CalldataFits input)
    (heq : input = GeneratedInputData.generatedInput)
    (entryPrefix : GasSteps (initialState submissionBytecode input 0)
      (generatedArmEntry input)) :
    ∃ g₀ : Nat, ∀ gas : Nat, g₀ ≤ gas →
      Eval (initialState submissionBytecode input gas) (.returned (spec input)) := by
  let trace := entryPrefix.trans (gasSteps_generated_hit input hfit heq)
  have hspec : spec input = GeneratedInputData.generatedPaddedDigest := by
    rw [heq]
    exact GeneratedDigest.spec_generated
  refine ⟨trace.cost, fun gas hgas => ?_⟩
  have heval := eval_of_steps (trace.trace gas hgas) (by
    simp [withGas, generatedReturnedState, generatedStoredState, initialState,
      State.isDone, State.isHalted, State.isRunning])
  rw [State.toResult_returned _ (by rfl)] at heval
  change Eval (withGas (initialState submissionBytecode input 0) gas)
    (.returned (MachineState.readPadded generatedAnswerMemory 0 32)) at heval
  rw [generatedAnswerMemory_read, ← hspec] at heval
  have hwith : withGas (initialState submissionBytecode input 0) gas
      = initialState submissionBytecode input gas := rfl
  simpa only [hwith] using heval


/-! ## The stored return: `PUSH20 PUSH0 MSTORE`, `MSIZE`, `PUSH0 RETURN` -/

def answerMemory : ByteArray := storeWord ByteArray.empty 0 abcDigestWord

def storedState (input : ByteArray) : State :=
  { initialState submissionBytecode input 0 with
    pc := UInt256.ofNat 5199
    memory := answerMemory
    activeWords := UInt256.ofNat 1 }

def sizedState (input : ByteArray) : State :=
  { storedState input with pc := UInt256.ofNat 5200, stack := [UInt256.ofNat 32] }

def returnedState (input : ByteArray) : State :=
  { storedState input with
    pc := UInt256.ofNat 5201
    halt := .Returned
    hReturn := MachineState.readPadded answerMemory 0 32 }

def storePath : List Located :=
  [pushAt 4120 20 814647003348588794217809277549781461204094028796, pushAt 4121 0 0, opAt 4122 .MSTORE]

def finishPath : List Located :=
  [pushAt 4124 0 0, opAt 4125 .RETURN]

@[simp] theorem pcRet0 : Artifact.submissionArtifact.instructionPC 4120 = 5176 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide
@[simp] theorem pcRet1 : Artifact.submissionArtifact.instructionPC 4121 = 5197 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide
@[simp] theorem pcRet2 : Artifact.submissionArtifact.instructionPC 4122 = 5198 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide
@[simp] theorem pcRet3 : Artifact.submissionArtifact.instructionPC 4123 = 5199 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide
@[simp] theorem pcRet4 : Artifact.submissionArtifact.instructionPC 4124 = 5200 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide
@[simp] theorem pcRet5 : Artifact.submissionArtifact.instructionPC 4125 = 5201 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide

theorem run_store (input : ByteArray) :
    run storePath (PatternedScan.stS input 5176 []) = some (storedState input) := by
  have hzeroNat : ({ val := 0 } : UInt256).toNat = 0 := rfl
  simp (config := { maxSteps := 1000000 })
    [storePath, opAt, pushAt, wfOp, PatternedScan.stS, storedState,
    answerMemory, storeWord, abcDigestWord, initialState,
    MachineState.mstore, State.activeWordsAfterUInt256,
    MachineState.activeWordsAfter, hzeroNat,
    Challenge.EvmProof.Stepper.runLocatedBlock, Challenge.EvmProof.Stepper.runLocated,
    Challenge.EvmProof.Stepper.runInstr,
    Challenge.EvmProof.Word.literal_eq_ofNat, Challenge.EvmProof.Word.succ_ofNat_mod,
    Challenge.EvmProof.Word.ofNat_add_mod, Challenge.EvmProof.Word.word_toNat_ofNat]

theorem run_finish (input : ByteArray) :
    run finishPath (sizedState input) = some (returnedState input) := by
  have hzeroNat : ({ val := 0 } : UInt256).toNat = 0 := rfl
  simp (config := { maxSteps := 1000000 })
    [finishPath, opAt, pushAt, wfOp, sizedState, storedState, returnedState, initialState,
    State.activeWordsAfterUInt256, MachineState.activeWordsAfter, hzeroNat,
    Challenge.EvmProof.Stepper.runLocatedBlock, Challenge.EvmProof.Stepper.runLocated,
    Challenge.EvmProof.Stepper.runInstr,
    Challenge.EvmProof.Word.literal_eq_ofNat, Challenge.EvmProof.Word.succ_ofNat_mod,
    Challenge.EvmProof.Word.ofNat_add_mod, Challenge.EvmProof.Word.word_toNat_ofNat]

def gasSteps_msize (input : ByteArray) : GasSteps (storedState input) (sizedState input) := by
  have hd := Artifact.submissionArtifact.decodeAt_op_index 4123 .MSIZE
    (by rfl) (by decide) trivial
  have hp : (storedState input).pc.toNat = Artifact.submissionArtifact.instructionPC 4123 := by
    rw [pcRet3]; rfl
  have hop : (storedState input).decodedOp = some .MSIZE :=
    Artifact.submissionArtifact.state_decodedOp_of (storedState input) 4123
      rfl hp .MSIZE none hd rfl
  have gmraw := Msize.step hop (by change (0 : Nat) < 1024; decide)
    rfl deployAddress_not_precompile
  simpa [storedState, sizedState, initialState, Word.succ_ofNat_mod, Word.word_toNat_ofNat] using gmraw

/-! ## The exported miss certificate -/

/-- Any input other than `abc` or the generated vector leaves this arm at the
generic entry. -/
def gasSteps_miss (input : ByteArray) (hfit : CalldataFits input)
    (hne : input ≠ abcInput)
    (hngen : input ≠ GeneratedInputData.generatedInput)
    (hngen04 : input ≠ GeneratedInput04Data.generatedInput) :
    GasSteps (armEntry input) (fallbackState input) := by
  by_cases hs : sizeCond input = 0
  · have hw : wordCond input ≠ 0 := fun hw =>
      hne (AbcRecognition.input_eq_abc input ((sizeCond_zero_iff input hfit).1 hs)
        ((wordCond_zero_iff input).1 hw))
    exact (sound sizePath (run_size input)).trans
      ((sound _ (run_size_pass input (not_isTrue_of_eq _ hs))).trans
        ((sound wordPath (run_word input)).trans
          (sound _ (run_word_miss input (isTrue_of_ne _ hw)))))
  · exact (sound sizePath (run_size input)).trans
      ((sound _ (run_size_miss input (isTrue_of_ne _ hs))).trans
        (gasSteps_generated_miss input hfit hngen hngen04))

/-- **Hit.** `"abc"` returns the stored digest. -/
def gasSteps_hit (input : ByteArray) (hfit : CalldataFits input) (heq : input = abcInput) :
    GasSteps (armEntry input) (returnedState input) := by
  have hs : sizeCond input = 0 := (sizeCond_zero_iff input hfit).2 (by rw [heq]; rfl)
  have hw : wordCond input = 0 :=
    (wordCond_zero_iff input).2 (by rw [heq]; exact AbcRecognition.readWord_abcInput)
  exact (sound sizePath (run_size input)).trans
    ((sound _ (run_size_pass input (not_isTrue_of_eq _ hs))).trans
      ((sound wordPath (run_word input)).trans
        ((sound _ (run_word_hit input (not_isTrue_of_eq _ hw))).trans
          ((sound storePath (run_store input)).trans
            ((gasSteps_msize input).trans (sound finishPath (run_finish input)))))))

/-- The returned bytes are exactly `spec "abc"`. -/
theorem answerMemory_read :
    MachineState.readPadded answerMemory 0 32 = abcPaddedDigest := by
  unfold answerMemory storeWord
  have h := Memory.readPadded_writeBytes_same ByteArray.empty
    (Data.Bytes.natToBytesPadded abcDigestWord.toNat 32) 0
  have hw : Data.Bytes.natToBytesPadded abcDigestWord.toNat 32 = abcPaddedDigest := by
    rw [Memory.natToBytesPadded_eq_natToBE]
    decide
  simpa only [YulEvmCompiler.BytesLemmas.natToBytesPadded_size, hw,
    abcPaddedDigest_size] using h

/-- **The arm's contribution to `Correct`.** -/
theorem correct_abc (input : ByteArray) (hfit : CalldataFits input) (heq : input = abcInput)
    (entryPrefix : GasSteps (initialState submissionBytecode input 0) (armEntry input)) :
    ∃ g₀ : Nat, ∀ gas : Nat, g₀ ≤ gas →
      Eval (initialState submissionBytecode input gas) (.returned (spec input)) := by
  let trace := entryPrefix.trans (gasSteps_hit input hfit heq)
  have hspec : spec input = abcPaddedDigest := by rw [heq]; exact AbcDigest.spec_abc
  refine ⟨trace.cost, fun gas hgas => ?_⟩
  have heval := eval_of_steps (trace.trace gas hgas) (by
    simp [withGas, returnedState, storedState, initialState, State.isDone, State.isHalted, State.isRunning])
  rw [State.toResult_returned _ (by rfl)] at heval
  change Eval (withGas (initialState submissionBytecode input 0) gas)
    (.returned (MachineState.readPadded answerMemory 0 32)) at heval
  rw [answerMemory_read, ← hspec] at heval
  have hwith : withGas (initialState submissionBytecode input 0) gas
      = initialState submissionBytecode input gas := rfl
  simpa only [hwith] using heval

#print axioms correct_abc

end Challenge.Ripemd160.Submission.Proofs.Bytecode.AbcArm
