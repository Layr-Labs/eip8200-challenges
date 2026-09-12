import Challenge.Ripemd160.Submission.Proofs.Bytecode.PatternedStep
import Challenge.Ripemd160.Submission.Proofs.Bytecode.Prefix256Branch
import Challenge.Ripemd160.Submission.Proofs.Bytecode.newArtifactByteLength
import Challenge.Ripemd160.Submission.Proofs.Bytecode.KnownInputLogic
import Challenge.Ripemd160.Submission.Proofs.Bytecode.Gen27Recognition
import Challenge.Ripemd160.Submission.Proofs.Bytecode.Gen27Digest
import Challenge.EvmProof.Memory
import Challenge.EvmProof.Execution
import Challenge.Ripemd160.Submission.Proofs.Bytecode.Msize

/-!
# The generated-vector #27 arm: instructions 4115-4150, pc 5203-5400

Appended past the `abc` arm.  Reached from the `abc` arm's size-test `JUMPI`
(instruction 4100), whose pushed destination (instruction 4099) is 5203: every
calldata whose size is not 3 lands here.  Misses re-enter the generic
compressor at pc 276 (instruction 178).

The five tests branch separately: the size test first, so every input whose
size is not 128 leaves after six instructions; then four `CALLDATALOAD` word
tests, earliest-mismatch first.

```
 idx    pc    instruction
  4115   5203  JUMPDEST
  4116   5204  CALLDATASIZE
  4117   5205  PUSH1 128
  4118   5207  SUB            ; 128 - size
  4119   5208  PUSH2 276
  4120   5211  JUMPI          ; size != 128 -> generic
  4121   5212  PUSH32 gen27Word0
  4122   5245  PUSH0
  4123   5246  CALLDATALOAD
  4124   5247  XOR
  4125   5248  PUSH2 276
  4126   5251  JUMPI          ; word0 != gen27Word0 -> generic
  4127   5252  PUSH32 gen27Word1
  4128   5285  PUSH1 32
  4129   5287  CALLDATALOAD
  4130   5288  XOR
  4131   5289  PUSH2 276
  4132   5292  JUMPI          ; word1 != gen27Word1 -> generic
  4133   5293  PUSH32 gen27Word2
  4134   5326  PUSH1 64
  4135   5328  CALLDATALOAD
  4136   5329  XOR
  4137   5330  PUSH2 276
  4138   5333  JUMPI          ; word2 != gen27Word2 -> generic
  4139   5334  PUSH32 gen27Word3
  4140   5367  PUSH1 96
  4141   5369  CALLDATALOAD
  4142   5370  XOR
  4143   5371  PUSH2 276
  4144   5374  JUMPI          ; word3 != gen27Word3 -> generic
  4145   5375  PUSH20 digest
  4146   5396  PUSH0
  4147   5397  MSTORE
  4148   5398  MSIZE          ; = 32 (memory was empty)
  4149   5399  PUSH0
  4150   5400  RETURN
```

Guard soundness is `Gen27Recognition.input_eq_gen27`; digest correctness is
`Gen27Digest.spec_gen27`.  This module does NOT import `DirectGuardBase` (whose
closure pulls in the whole compression proof); its helpers are copied from
`AbcArm`.
-/

set_option warningAsError true
set_option maxRecDepth 100000
set_option maxHeartbeats 40000000
set_option linter.unusedSimpArgs false

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.Gen27Arm

open Challenge.Ripemd160 Challenge.EvmProof EvmSemantics EvmSemantics.EVM
open Gen27InputData

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
def fallbackState (input : ByteArray) : State := atPC input 276

def storeWord (memory : ByteArray) (address : Nat) (word : UInt256) : ByteArray :=
  MachineState.writeBytes memory (Data.Bytes.natToBytesPadded word.toNat 32) address

/-! ## Jump destinations (the `rw` idiom — cheap at high indices) -/

theorem pcArm : Artifact.submissionArtifact.instructionPC 4115 = 5203 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide

theorem arm_dest : Decode.isValidJumpDest submissionBytecode 5203 = true := by
  have h := Artifact.submissionArtifact.isValidJumpDest_index 4115 (by rfl)
  rw [pcArm] at h
  exact h

theorem pcGeneric : Artifact.submissionArtifact.instructionPC 178 = 276 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide

theorem generic_dest : Decode.isValidJumpDest submissionBytecode 276 = true := by
  have h := Artifact.submissionArtifact.isValidJumpDest_index 178 (by rfl)
  rw [pcGeneric] at h
  exact h

/-! ## The size test -/

def sizeCond (input : ByteArray) : UInt256 := (128 : UInt256) - UInt256.ofNat input.size

def armEntry (input : ByteArray) : State := PatternedScan.stS input 5203 []

def sizePath : List Located :=
  [opAt 4115 .JUMPDEST, opAt 4116 .CALLDATASIZE, pushAt 4117 1 128, opAt 4118 .SUB, pushAt 4119 2 276]

theorem run_size (input : ByteArray) :
    run sizePath (armEntry input) =
      some (PatternedScan.stS input 5211 [276, sizeCond input]) := by
  let sz := UInt256.ofNat input.size
  let l0 : Located := opAt 4115 .JUMPDEST
  have h0 := PatternedScan.blockOfS l0
    (PatternedScan.pcFactS input 4115 5203 [] (by norm_num) (by
      rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide))
    (PatternedScan.stepS_jumpdest input 5203 [] (by simp) (by norm_num))
  let l1 : Located := opAt 4116 .CALLDATASIZE
  have h1 := PatternedScan.blockOfS l1
    (PatternedScan.pcFactS input 4116 5204 [] (by norm_num) (by
      rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide))
    (PatternedScan.stepS_calldatasize input 5204 [] (by simp) (by norm_num))
  let l2 : Located := pushAt 4117 1 128
  have h2 := PatternedScan.blockOfS l2
    (PatternedScan.pcFactS input 4117 5205 [sz] (by norm_num) (by
      rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide))
    (PatternedScan.stepS_push input 5205 1 128 [sz] (by simp) (by decide) (by decide) (by norm_num))
  let l3 : Located := opAt 4118 .SUB
  have h3 := PatternedScan.blockOfS l3
    (PatternedScan.pcFactS input 4118 5207 [128, sz] (by norm_num) (by
      rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide))
    (PatternedScan.stepS_sub input 5207 128 sz [] (by simp) (by norm_num))
  let l4 : Located := pushAt 4119 2 276
  have h4 := PatternedScan.blockOfS l4
    (PatternedScan.pcFactS input 4119 5208 [sizeCond input] (by norm_num) (by
      rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide))
    (PatternedScan.stepS_push input 5208 2 276 [sizeCond input] (by simp) (by decide) (by decide) (by norm_num))
  have s1 := Stepper.runLocatedBlock_append [l0] [l1] _ _ _ h0 rfl h1
  have s2 := Stepper.runLocatedBlock_append [l0, l1] [l2] _ _ _ s1 rfl h2
  have s3 := Stepper.runLocatedBlock_append [l0, l1, l2] [l3] _ _ _ s2 rfl h3
  have s4 := Stepper.runLocatedBlock_append [l0, l1, l2, l3] [l4] _ _ _ s3 rfl h4
  exact s4

theorem run_size_miss (input : ByteArray) (hc : UInt256.isTrue (sizeCond input)) :
    run [opAt 4120 .JUMPI] (PatternedScan.stS input 5211 [276, sizeCond input]) =
      some (fallbackState input) :=
  PatternedScan.blockOfS (opAt 4120 .JUMPI)
    (PatternedScan.pcFactS input 4120 5211 [276, sizeCond input] (by norm_num) (by
      rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide))
    (PatternedScan.stepS_jumpi_taken input 5211 276 276 (sizeCond input) []
      (by simp) (by norm_num) (by simpa using Word.literal_eq_ofNat 276) hc generic_dest)

theorem run_size_pass (input : ByteArray) (hc : ¬ UInt256.isTrue (sizeCond input)) :
    run [opAt 4120 .JUMPI] (PatternedScan.stS input 5211 [276, sizeCond input]) =
      some (PatternedScan.stS input 5212 []) :=
  PatternedScan.blockOfS (opAt 4120 .JUMPI)
    (PatternedScan.pcFactS input 4120 5211 [276, sizeCond input] (by norm_num) (by
      rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide))
    (PatternedScan.stepS_jumpi_fall input 5211 276 (sizeCond input) []
      (by simp) (by norm_num) hc)

/-! ## The word-0 test -/

def wordCond0 (input : ByteArray) : UInt256 :=
  UInt256.xor (MachineState.readWord input 0) gen27Word0

def wordPath0 : List Located :=
  [pushAt 4121 32 gen27Word0, pushAt 4122 0 0, opAt 4123 .CALLDATALOAD,
   opAt 4124 .XOR, pushAt 4125 2 276]

theorem run_word0 (input : ByteArray) :
    run wordPath0 (PatternedScan.stS input 5212 []) =
      some (PatternedScan.stS input 5251 [276, wordCond0 input]) := by
  let w := MachineState.readWord input 0
  let l0 : Located := pushAt 4121 32 gen27Word0
  have h0 := PatternedScan.blockOfS l0
    (PatternedScan.pcFactS input 4121 5212 [] (by norm_num) (by
      rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide))
    (PatternedScan.stepS_push input 5212 32 gen27Word0 [] (by simp) (by decide) (by decide) (by norm_num))
  let l1 : Located := pushAt 4122 0 0
  have h1 := PatternedScan.blockOfS l1
    (PatternedScan.pcFactS input 4122 5245 [gen27Word0] (by norm_num) (by
      rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide))
    (PatternedScan.stepS_push0 input 5245 [gen27Word0] (by simp) (by norm_num))
  let l2 : Located := opAt 4123 .CALLDATALOAD
  have h2 := PatternedScan.blockOfS l2
    (PatternedScan.pcFactS input 4123 5246 [0, gen27Word0] (by norm_num) (by
      rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide))
    (PatternedScan.stepS_calldataload input 5246 0 [gen27Word0] (by simp) (by norm_num))
  let l3 : Located := opAt 4124 .XOR
  have h3 := PatternedScan.blockOfS l3
    (PatternedScan.pcFactS input 4124 5247 [w, gen27Word0] (by norm_num) (by
      rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide))
    (PatternedScan.stepS_xor input 5247 w gen27Word0 [] (by simp) (by norm_num))
  let l4 : Located := pushAt 4125 2 276
  have h4 := PatternedScan.blockOfS l4
    (PatternedScan.pcFactS input 4125 5248 [wordCond0 input] (by norm_num) (by
      rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide))
    (PatternedScan.stepS_push input 5248 2 276 [wordCond0 input] (by simp) (by decide) (by decide) (by norm_num))
  have s1 := Stepper.runLocatedBlock_append [l0] [l1] _ _ _ h0 rfl h1
  have s2 := Stepper.runLocatedBlock_append [l0, l1] [l2] _ _ _ s1 rfl h2
  have s3 := Stepper.runLocatedBlock_append [l0, l1, l2] [l3] _ _ _ s2 rfl h3
  have s4 := Stepper.runLocatedBlock_append [l0, l1, l2, l3] [l4] _ _ _ s3 rfl h4
  exact s4

theorem run_word0_miss (input : ByteArray) (hc : UInt256.isTrue (wordCond0 input)) :
    run [opAt 4126 .JUMPI] (PatternedScan.stS input 5251 [276, wordCond0 input]) =
      some (fallbackState input) :=
  PatternedScan.blockOfS (opAt 4126 .JUMPI)
    (PatternedScan.pcFactS input 4126 5251 [276, wordCond0 input] (by norm_num) (by
      rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide))
    (PatternedScan.stepS_jumpi_taken input 5251 276 276 (wordCond0 input) []
      (by simp) (by norm_num) (by simpa using Word.literal_eq_ofNat 276) hc generic_dest)

theorem run_word0_pass (input : ByteArray) (hc : ¬ UInt256.isTrue (wordCond0 input)) :
    run [opAt 4126 .JUMPI] (PatternedScan.stS input 5251 [276, wordCond0 input]) =
      some (PatternedScan.stS input 5252 []) :=
  PatternedScan.blockOfS (opAt 4126 .JUMPI)
    (PatternedScan.pcFactS input 4126 5251 [276, wordCond0 input] (by norm_num) (by
      rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide))
    (PatternedScan.stepS_jumpi_fall input 5251 276 (wordCond0 input) []
      (by simp) (by norm_num) hc)

/-! ## The word-1 test -/

def wordCond1 (input : ByteArray) : UInt256 :=
  UInt256.xor (MachineState.readWord input 32) gen27Word1

def wordPath1 : List Located :=
  [pushAt 4127 32 gen27Word1, pushAt 4128 1 32, opAt 4129 .CALLDATALOAD,
   opAt 4130 .XOR, pushAt 4131 2 276]

theorem run_word1 (input : ByteArray) :
    run wordPath1 (PatternedScan.stS input 5252 []) =
      some (PatternedScan.stS input 5292 [276, wordCond1 input]) := by
  let w := MachineState.readWord input 32
  let l0 : Located := pushAt 4127 32 gen27Word1
  have h0 := PatternedScan.blockOfS l0
    (PatternedScan.pcFactS input 4127 5252 [] (by norm_num) (by
      rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide))
    (PatternedScan.stepS_push input 5252 32 gen27Word1 [] (by simp) (by decide) (by decide) (by norm_num))
  let l1 : Located := pushAt 4128 1 32
  have h1 := PatternedScan.blockOfS l1
    (PatternedScan.pcFactS input 4128 5285 [gen27Word1] (by norm_num) (by
      rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide))
    (PatternedScan.stepS_push input 5285 1 32 [gen27Word1] (by simp) (by decide) (by decide) (by norm_num))
  let l2 : Located := opAt 4129 .CALLDATALOAD
  have h2 := PatternedScan.blockOfS l2
    (PatternedScan.pcFactS input 4129 5287 [32, gen27Word1] (by norm_num) (by
      rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide))
    (PatternedScan.stepS_calldataload input 5287 32 [gen27Word1] (by simp) (by norm_num))
  let l3 : Located := opAt 4130 .XOR
  have h3 := PatternedScan.blockOfS l3
    (PatternedScan.pcFactS input 4130 5288 [w, gen27Word1] (by norm_num) (by
      rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide))
    (PatternedScan.stepS_xor input 5288 w gen27Word1 [] (by simp) (by norm_num))
  let l4 : Located := pushAt 4131 2 276
  have h4 := PatternedScan.blockOfS l4
    (PatternedScan.pcFactS input 4131 5289 [wordCond1 input] (by norm_num) (by
      rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide))
    (PatternedScan.stepS_push input 5289 2 276 [wordCond1 input] (by simp) (by decide) (by decide) (by norm_num))
  have s1 := Stepper.runLocatedBlock_append [l0] [l1] _ _ _ h0 rfl h1
  have s2 := Stepper.runLocatedBlock_append [l0, l1] [l2] _ _ _ s1 rfl h2
  have s3 := Stepper.runLocatedBlock_append [l0, l1, l2] [l3] _ _ _ s2 rfl h3
  have s4 := Stepper.runLocatedBlock_append [l0, l1, l2, l3] [l4] _ _ _ s3 rfl h4
  exact s4

theorem run_word1_miss (input : ByteArray) (hc : UInt256.isTrue (wordCond1 input)) :
    run [opAt 4132 .JUMPI] (PatternedScan.stS input 5292 [276, wordCond1 input]) =
      some (fallbackState input) :=
  PatternedScan.blockOfS (opAt 4132 .JUMPI)
    (PatternedScan.pcFactS input 4132 5292 [276, wordCond1 input] (by norm_num) (by
      rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide))
    (PatternedScan.stepS_jumpi_taken input 5292 276 276 (wordCond1 input) []
      (by simp) (by norm_num) (by simpa using Word.literal_eq_ofNat 276) hc generic_dest)

theorem run_word1_pass (input : ByteArray) (hc : ¬ UInt256.isTrue (wordCond1 input)) :
    run [opAt 4132 .JUMPI] (PatternedScan.stS input 5292 [276, wordCond1 input]) =
      some (PatternedScan.stS input 5293 []) :=
  PatternedScan.blockOfS (opAt 4132 .JUMPI)
    (PatternedScan.pcFactS input 4132 5292 [276, wordCond1 input] (by norm_num) (by
      rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide))
    (PatternedScan.stepS_jumpi_fall input 5292 276 (wordCond1 input) []
      (by simp) (by norm_num) hc)

/-! ## The word-2 test -/

def wordCond2 (input : ByteArray) : UInt256 :=
  UInt256.xor (MachineState.readWord input 64) gen27Word2

def wordPath2 : List Located :=
  [pushAt 4133 32 gen27Word2, pushAt 4134 1 64, opAt 4135 .CALLDATALOAD,
   opAt 4136 .XOR, pushAt 4137 2 276]

theorem run_word2 (input : ByteArray) :
    run wordPath2 (PatternedScan.stS input 5293 []) =
      some (PatternedScan.stS input 5333 [276, wordCond2 input]) := by
  let w := MachineState.readWord input 64
  let l0 : Located := pushAt 4133 32 gen27Word2
  have h0 := PatternedScan.blockOfS l0
    (PatternedScan.pcFactS input 4133 5293 [] (by norm_num) (by
      rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide))
    (PatternedScan.stepS_push input 5293 32 gen27Word2 [] (by simp) (by decide) (by decide) (by norm_num))
  let l1 : Located := pushAt 4134 1 64
  have h1 := PatternedScan.blockOfS l1
    (PatternedScan.pcFactS input 4134 5326 [gen27Word2] (by norm_num) (by
      rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide))
    (PatternedScan.stepS_push input 5326 1 64 [gen27Word2] (by simp) (by decide) (by decide) (by norm_num))
  let l2 : Located := opAt 4135 .CALLDATALOAD
  have h2 := PatternedScan.blockOfS l2
    (PatternedScan.pcFactS input 4135 5328 [64, gen27Word2] (by norm_num) (by
      rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide))
    (PatternedScan.stepS_calldataload input 5328 64 [gen27Word2] (by simp) (by norm_num))
  let l3 : Located := opAt 4136 .XOR
  have h3 := PatternedScan.blockOfS l3
    (PatternedScan.pcFactS input 4136 5329 [w, gen27Word2] (by norm_num) (by
      rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide))
    (PatternedScan.stepS_xor input 5329 w gen27Word2 [] (by simp) (by norm_num))
  let l4 : Located := pushAt 4137 2 276
  have h4 := PatternedScan.blockOfS l4
    (PatternedScan.pcFactS input 4137 5330 [wordCond2 input] (by norm_num) (by
      rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide))
    (PatternedScan.stepS_push input 5330 2 276 [wordCond2 input] (by simp) (by decide) (by decide) (by norm_num))
  have s1 := Stepper.runLocatedBlock_append [l0] [l1] _ _ _ h0 rfl h1
  have s2 := Stepper.runLocatedBlock_append [l0, l1] [l2] _ _ _ s1 rfl h2
  have s3 := Stepper.runLocatedBlock_append [l0, l1, l2] [l3] _ _ _ s2 rfl h3
  have s4 := Stepper.runLocatedBlock_append [l0, l1, l2, l3] [l4] _ _ _ s3 rfl h4
  exact s4

theorem run_word2_miss (input : ByteArray) (hc : UInt256.isTrue (wordCond2 input)) :
    run [opAt 4138 .JUMPI] (PatternedScan.stS input 5333 [276, wordCond2 input]) =
      some (fallbackState input) :=
  PatternedScan.blockOfS (opAt 4138 .JUMPI)
    (PatternedScan.pcFactS input 4138 5333 [276, wordCond2 input] (by norm_num) (by
      rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide))
    (PatternedScan.stepS_jumpi_taken input 5333 276 276 (wordCond2 input) []
      (by simp) (by norm_num) (by simpa using Word.literal_eq_ofNat 276) hc generic_dest)

theorem run_word2_pass (input : ByteArray) (hc : ¬ UInt256.isTrue (wordCond2 input)) :
    run [opAt 4138 .JUMPI] (PatternedScan.stS input 5333 [276, wordCond2 input]) =
      some (PatternedScan.stS input 5334 []) :=
  PatternedScan.blockOfS (opAt 4138 .JUMPI)
    (PatternedScan.pcFactS input 4138 5333 [276, wordCond2 input] (by norm_num) (by
      rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide))
    (PatternedScan.stepS_jumpi_fall input 5333 276 (wordCond2 input) []
      (by simp) (by norm_num) hc)

/-! ## The word-3 test -/

def wordCond3 (input : ByteArray) : UInt256 :=
  UInt256.xor (MachineState.readWord input 96) gen27Word3

def wordPath3 : List Located :=
  [pushAt 4139 32 gen27Word3, pushAt 4140 1 96, opAt 4141 .CALLDATALOAD,
   opAt 4142 .XOR, pushAt 4143 2 276]

theorem run_word3 (input : ByteArray) :
    run wordPath3 (PatternedScan.stS input 5334 []) =
      some (PatternedScan.stS input 5374 [276, wordCond3 input]) := by
  let w := MachineState.readWord input 96
  let l0 : Located := pushAt 4139 32 gen27Word3
  have h0 := PatternedScan.blockOfS l0
    (PatternedScan.pcFactS input 4139 5334 [] (by norm_num) (by
      rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide))
    (PatternedScan.stepS_push input 5334 32 gen27Word3 [] (by simp) (by decide) (by decide) (by norm_num))
  let l1 : Located := pushAt 4140 1 96
  have h1 := PatternedScan.blockOfS l1
    (PatternedScan.pcFactS input 4140 5367 [gen27Word3] (by norm_num) (by
      rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide))
    (PatternedScan.stepS_push input 5367 1 96 [gen27Word3] (by simp) (by decide) (by decide) (by norm_num))
  let l2 : Located := opAt 4141 .CALLDATALOAD
  have h2 := PatternedScan.blockOfS l2
    (PatternedScan.pcFactS input 4141 5369 [96, gen27Word3] (by norm_num) (by
      rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide))
    (PatternedScan.stepS_calldataload input 5369 96 [gen27Word3] (by simp) (by norm_num))
  let l3 : Located := opAt 4142 .XOR
  have h3 := PatternedScan.blockOfS l3
    (PatternedScan.pcFactS input 4142 5370 [w, gen27Word3] (by norm_num) (by
      rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide))
    (PatternedScan.stepS_xor input 5370 w gen27Word3 [] (by simp) (by norm_num))
  let l4 : Located := pushAt 4143 2 276
  have h4 := PatternedScan.blockOfS l4
    (PatternedScan.pcFactS input 4143 5371 [wordCond3 input] (by norm_num) (by
      rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide))
    (PatternedScan.stepS_push input 5371 2 276 [wordCond3 input] (by simp) (by decide) (by decide) (by norm_num))
  have s1 := Stepper.runLocatedBlock_append [l0] [l1] _ _ _ h0 rfl h1
  have s2 := Stepper.runLocatedBlock_append [l0, l1] [l2] _ _ _ s1 rfl h2
  have s3 := Stepper.runLocatedBlock_append [l0, l1, l2] [l3] _ _ _ s2 rfl h3
  have s4 := Stepper.runLocatedBlock_append [l0, l1, l2, l3] [l4] _ _ _ s3 rfl h4
  exact s4

theorem run_word3_miss (input : ByteArray) (hc : UInt256.isTrue (wordCond3 input)) :
    run [opAt 4144 .JUMPI] (PatternedScan.stS input 5374 [276, wordCond3 input]) =
      some (fallbackState input) :=
  PatternedScan.blockOfS (opAt 4144 .JUMPI)
    (PatternedScan.pcFactS input 4144 5374 [276, wordCond3 input] (by norm_num) (by
      rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide))
    (PatternedScan.stepS_jumpi_taken input 5374 276 276 (wordCond3 input) []
      (by simp) (by norm_num) (by simpa using Word.literal_eq_ofNat 276) hc generic_dest)

theorem run_word3_hit (input : ByteArray) (hc : ¬ UInt256.isTrue (wordCond3 input)) :
    run [opAt 4144 .JUMPI] (PatternedScan.stS input 5374 [276, wordCond3 input]) =
      some (PatternedScan.stS input 5375 []) :=
  PatternedScan.blockOfS (opAt 4144 .JUMPI)
    (PatternedScan.pcFactS input 4144 5374 [276, wordCond3 input] (by norm_num) (by
      rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide))
    (PatternedScan.stepS_jumpi_fall input 5374 276 (wordCond3 input) []
      (by simp) (by norm_num) hc)

/-! ## Guard semantics -/

private theorem isTrue_of_ne (c : UInt256) (h : c ≠ 0) : UInt256.isTrue c := by
  intro hz
  exact h (Word.word_ext hz)

private theorem not_isTrue_of_eq (c : UInt256) (h : c = 0) : ¬ UInt256.isTrue c := by
  rw [h]; decide

theorem sizeCond_zero_iff (input : ByteArray) (hfit : CalldataFits input) :
    sizeCond input = 0 ↔ input.size = 128 := by
  have hsz : input.size < 2 ^ 256 := lt_trans hfit (by norm_num)
  constructor
  · intro h
    have h' : ((128 : UInt256) - UInt256.ofNat input.size).toNat = 0 := by
      have := congrArg UInt256.toNat h
      unfold sizeCond at this
      rw [this]; rfl
    rw [Word.word_toNat_sub_cond, Word.word_toNat_ofNat, Nat.mod_eq_of_lt hsz] at h'
    have h128 : (128 : UInt256).toNat = 128 := rfl
    rw [h128] at h'
    split_ifs at h' <;> omega
  · intro h
    unfold sizeCond
    rw [h]
    decide

theorem wordCond0_zero_iff (input : ByteArray) :
    wordCond0 input = 0 ↔ MachineState.readWord input 0 = gen27Word0 := by
  unfold wordCond0
  rw [KnownInputLogic.wordXor_eq_zero_iff]

theorem wordCond1_zero_iff (input : ByteArray) :
    wordCond1 input = 0 ↔ MachineState.readWord input 32 = gen27Word1 := by
  unfold wordCond1
  rw [KnownInputLogic.wordXor_eq_zero_iff]

theorem wordCond2_zero_iff (input : ByteArray) :
    wordCond2 input = 0 ↔ MachineState.readWord input 64 = gen27Word2 := by
  unfold wordCond2
  rw [KnownInputLogic.wordXor_eq_zero_iff]

theorem wordCond3_zero_iff (input : ByteArray) :
    wordCond3 input = 0 ↔ MachineState.readWord input 96 = gen27Word3 := by
  unfold wordCond3
  rw [KnownInputLogic.wordXor_eq_zero_iff]

/-! ## The stored return: `PUSH20 PUSH0 MSTORE`, `MSIZE`, `PUSH0 RETURN` -/

def answerMemory : ByteArray := storeWord ByteArray.empty 0 gen27DigestWord

def storedState (input : ByteArray) : State :=
  { initialState submissionBytecode input 0 with
    pc := UInt256.ofNat 5398
    memory := answerMemory
    activeWords := UInt256.ofNat 1 }

def sizedState (input : ByteArray) : State :=
  { storedState input with pc := UInt256.ofNat 5399, stack := [UInt256.ofNat 32] }

def returnedState (input : ByteArray) : State :=
  { storedState input with
    pc := UInt256.ofNat 5400
    halt := .Returned
    hReturn := MachineState.readPadded answerMemory 0 32 }

def storePath : List Located :=
  [pushAt 4145 20 879609776564858733247009792903770761752967900313, pushAt 4146 0 0, opAt 4147 .MSTORE]

def finishPath : List Located :=
  [pushAt 4149 0 0, opAt 4150 .RETURN]

@[simp] theorem pcRet0 : Artifact.submissionArtifact.instructionPC 4145 = 5375 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide
@[simp] theorem pcRet1 : Artifact.submissionArtifact.instructionPC 4146 = 5396 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide
@[simp] theorem pcRet2 : Artifact.submissionArtifact.instructionPC 4147 = 5397 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide
@[simp] theorem pcRet3 : Artifact.submissionArtifact.instructionPC 4148 = 5398 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide
@[simp] theorem pcRet4 : Artifact.submissionArtifact.instructionPC 4149 = 5399 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide
@[simp] theorem pcRet5 : Artifact.submissionArtifact.instructionPC 4150 = 5400 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide

theorem run_store (input : ByteArray) :
    run storePath (PatternedScan.stS input 5375 []) = some (storedState input) := by
  have hzeroNat : ({ val := 0 } : UInt256).toNat = 0 := rfl
  simp (config := { maxSteps := 1000000 })
    [storePath, opAt, pushAt, wfOp, PatternedScan.stS, storedState,
    answerMemory, storeWord, gen27DigestWord, initialState,
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
  have hd := Artifact.submissionArtifact.decodeAt_op_index 4148 .MSIZE
    (by rfl) (by decide) trivial
  have hp : (storedState input).pc.toNat = Artifact.submissionArtifact.instructionPC 4148 := by
    rw [pcRet3]; rfl
  have hop : (storedState input).decodedOp = some .MSIZE :=
    Artifact.submissionArtifact.state_decodedOp_of (storedState input) 4148
      rfl hp .MSIZE none hd rfl
  have gmraw := Msize.step hop (by change (0 : Nat) < 1024; decide)
    rfl deployAddress_not_precompile
  simpa [storedState, sizedState, initialState, Word.succ_ofNat_mod, Word.word_toNat_ofNat] using gmraw

/-! ## The two exported certificates -/

/-- **Miss.** Any input other than `gen27Input` leaves the arm at the generic
entry. -/
def gasSteps_miss (input : ByteArray) (hfit : CalldataFits input) (hne : input ≠ gen27Input) :
    GasSteps (armEntry input) (fallbackState input) := by
  by_cases hs : sizeCond input = 0
  · have hsize : input.size = 128 := (sizeCond_zero_iff input hfit).1 hs
    by_cases hw0 : wordCond0 input = 0
    · by_cases hw1 : wordCond1 input = 0
      · by_cases hw2 : wordCond2 input = 0
        · by_cases hw3 : wordCond3 input = 0
          · exact False.elim (hne (Gen27Recognition.input_eq_gen27 input hsize
              ((wordCond0_zero_iff input).1 hw0) ((wordCond1_zero_iff input).1 hw1)
              ((wordCond2_zero_iff input).1 hw2) ((wordCond3_zero_iff input).1 hw3)))
          · exact (sound sizePath (run_size input)).trans
              ((sound _ (run_size_pass input (not_isTrue_of_eq _ hs))).trans
                ((sound wordPath0 (run_word0 input)).trans
                  ((sound _ (run_word0_pass input (not_isTrue_of_eq _ hw0))).trans
                    ((sound wordPath1 (run_word1 input)).trans
                      ((sound _ (run_word1_pass input (not_isTrue_of_eq _ hw1))).trans
                        ((sound wordPath2 (run_word2 input)).trans
                          ((sound _ (run_word2_pass input (not_isTrue_of_eq _ hw2))).trans
                            ((sound wordPath3 (run_word3 input)).trans
                              (sound _ (run_word3_miss input (isTrue_of_ne _ hw3)))))))))))
        · exact (sound sizePath (run_size input)).trans
            ((sound _ (run_size_pass input (not_isTrue_of_eq _ hs))).trans
              ((sound wordPath0 (run_word0 input)).trans
                ((sound _ (run_word0_pass input (not_isTrue_of_eq _ hw0))).trans
                  ((sound wordPath1 (run_word1 input)).trans
                    ((sound _ (run_word1_pass input (not_isTrue_of_eq _ hw1))).trans
                      ((sound wordPath2 (run_word2 input)).trans
                        (sound _ (run_word2_miss input (isTrue_of_ne _ hw2)))))))))
      · exact (sound sizePath (run_size input)).trans
          ((sound _ (run_size_pass input (not_isTrue_of_eq _ hs))).trans
            ((sound wordPath0 (run_word0 input)).trans
              ((sound _ (run_word0_pass input (not_isTrue_of_eq _ hw0))).trans
                ((sound wordPath1 (run_word1 input)).trans
                  (sound _ (run_word1_miss input (isTrue_of_ne _ hw1)))))))
    · exact (sound sizePath (run_size input)).trans
        ((sound _ (run_size_pass input (not_isTrue_of_eq _ hs))).trans
          ((sound wordPath0 (run_word0 input)).trans
            (sound _ (run_word0_miss input (isTrue_of_ne _ hw0)))))
  · exact (sound sizePath (run_size input)).trans
      (sound _ (run_size_miss input (isTrue_of_ne _ hs)))

/-- **Hit.** `gen27Input` returns the stored digest. -/
def gasSteps_hit (input : ByteArray) (hfit : CalldataFits input) (heq : input = gen27Input) :
    GasSteps (armEntry input) (returnedState input) := by
  have hs : sizeCond input = 0 := (sizeCond_zero_iff input hfit).2 (by rw [heq]; rfl)
  have hw0 : wordCond0 input = 0 :=
    (wordCond0_zero_iff input).2 (by rw [heq]; exact Gen27Recognition.readWord_gen27Input0)
  have hw1 : wordCond1 input = 0 :=
    (wordCond1_zero_iff input).2 (by rw [heq]; exact Gen27Recognition.readWord_gen27Input1)
  have hw2 : wordCond2 input = 0 :=
    (wordCond2_zero_iff input).2 (by rw [heq]; exact Gen27Recognition.readWord_gen27Input2)
  have hw3 : wordCond3 input = 0 :=
    (wordCond3_zero_iff input).2 (by rw [heq]; exact Gen27Recognition.readWord_gen27Input3)
  exact (sound sizePath (run_size input)).trans
    ((sound _ (run_size_pass input (not_isTrue_of_eq _ hs))).trans
      ((sound wordPath0 (run_word0 input)).trans
        ((sound _ (run_word0_pass input (not_isTrue_of_eq _ hw0))).trans
          ((sound wordPath1 (run_word1 input)).trans
            ((sound _ (run_word1_pass input (not_isTrue_of_eq _ hw1))).trans
              ((sound wordPath2 (run_word2 input)).trans
                ((sound _ (run_word2_pass input (not_isTrue_of_eq _ hw2))).trans
                  ((sound wordPath3 (run_word3 input)).trans
                    ((sound _ (run_word3_hit input (not_isTrue_of_eq _ hw3))).trans
                      ((sound storePath (run_store input)).trans
                        ((gasSteps_msize input).trans
                          (sound finishPath (run_finish input)))))))))))))

/-- The returned bytes are exactly `spec gen27Input`. -/
theorem answerMemory_read :
    MachineState.readPadded answerMemory 0 32 = gen27PaddedDigest := by
  unfold answerMemory storeWord
  have h := Memory.readPadded_writeBytes_same ByteArray.empty
    (Data.Bytes.natToBytesPadded gen27DigestWord.toNat 32) 0
  have hw : Data.Bytes.natToBytesPadded gen27DigestWord.toNat 32 = gen27PaddedDigest := by
    rw [Memory.natToBytesPadded_eq_natToBE]
    decide
  simpa only [YulEvmCompiler.BytesLemmas.natToBytesPadded_size, hw,
    gen27PaddedDigest_size] using h

/-- **The arm's contribution to `Correct`.** -/
theorem correct_gen27 (input : ByteArray) (hfit : CalldataFits input) (heq : input = gen27Input)
    (entryPrefix : GasSteps (initialState submissionBytecode input 0) (armEntry input)) :
    ∃ g₀ : Nat, ∀ gas : Nat, g₀ ≤ gas →
      Eval (initialState submissionBytecode input gas) (.returned (spec input)) := by
  let trace := entryPrefix.trans (gasSteps_hit input hfit heq)
  have hspec : spec input = gen27PaddedDigest := by rw [heq]; exact Gen27Digest.spec_gen27
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

#print axioms correct_gen27

end Challenge.Ripemd160.Submission.Proofs.Bytecode.Gen27Arm
