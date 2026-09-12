import Challenge.Ripemd160.Submission.Proofs.Bytecode.PatternedStep
import Challenge.Ripemd160.Submission.Proofs.Bytecode.Prefix256Branch
import Challenge.Ripemd160.Submission.Proofs.Bytecode.newArtifactByteLength
import Challenge.Ripemd160.Submission.Proofs.Bytecode.KnownInputLogic
import Challenge.Ripemd160.Submission.Proofs.Bytecode.AbcRecognition
import Challenge.Ripemd160.Submission.Proofs.Bytecode.AbcDigest
import Challenge.Ripemd160.Submission.Proofs.Bytecode.EmptySpec
import Challenge.EvmProof.Memory
import Challenge.EvmProof.Execution
import Challenge.Ripemd160.Submission.Proofs.Bytecode.Msize

/-!
# The `abc` arm: instructions 4095-4114, pc 5154-5202; empty dispatch 4115-4124, pc 5203-5234

Appended past the digest table.  Reached from the byte-0 `JUMPI` (instruction
4053), whose pushed destination (instruction 4052) is 5154.  Size misses jump
to the appended dispatch at pc 5203 (instruction 4115): a non-empty input
re-enters the generic compressor at pc 276 (instruction 178), while the empty
input falls through to a stored-digest return.  Word misses still re-enter the
generic compressor at pc 276.

The two tests branch separately: the size test first, so every input whose
size is not 3 leaves after six instructions.

```
 idx    pc    instruction
  4095   5154  JUMPDEST
  4096   5155  CALLDATASIZE
  4097   5156  PUSH1 3
  4098   5158  SUB            ; 3 - size
  4099   5159  PUSH2 5203
  4100   5162  JUMPI          ; size != 3  -> dispatch
  4101   5163  PUSH3 0x616263
  4102   5167  PUSH1 232
  4103   5169  SHL            ; abcWord
  4104   5170  PUSH0
  4105   5171  CALLDATALOAD
  4106   5172  XOR
  4107   5173  PUSH2 276
  4108   5176  JUMPI          ; word != abcWord -> generic
  4109   5177  PUSH20 digest
  4110   5198  PUSH0
  4111   5199  MSTORE
  4112   5200  MSIZE          ; = 32 (memory was empty)
  4113   5201  PUSH0
  4114   5202  RETURN
  4115   5203  JUMPDEST
  4116   5204  CALLDATASIZE
  4117   5205  PUSH2 276
  4118   5208  JUMPI          ; size != 0  -> generic
  4119   5209  PUSH20 emptyDigest
  4120   5230  PUSH0
  4121   5231  MSTORE
  4122   5232  MSIZE          ; = 32 (memory was empty)
  4123   5233  PUSH0
  4124   5234  RETURN
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

theorem pcArm : Artifact.submissionArtifact.instructionPC 4095 = 5154 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide

theorem arm_dest : Decode.isValidJumpDest submissionBytecode 5154 = true := by
  have h := Artifact.submissionArtifact.isValidJumpDest_index 4095 (by rfl)
  rw [pcArm] at h
  exact h

theorem pcGeneric : Artifact.submissionArtifact.instructionPC 178 = 276 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide

theorem generic_dest : Decode.isValidJumpDest submissionBytecode 276 = true := by
  have h := Artifact.submissionArtifact.isValidJumpDest_index 178 (by rfl)
  rw [pcGeneric] at h
  exact h

theorem pcDispatch : Artifact.submissionArtifact.instructionPC 4115 = 5203 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide

theorem dispatch_dest : Decode.isValidJumpDest submissionBytecode 5203 = true := by
  have h := Artifact.submissionArtifact.isValidJumpDest_index 4115 (by rfl)
  rw [pcDispatch] at h
  exact h

/-! ## The size test -/

def sizeCond (input : ByteArray) : UInt256 := (3 : UInt256) - UInt256.ofNat input.size

def armEntry (input : ByteArray) : State := PatternedScan.stS input 5154 []

def sizePath : List Located :=
  [opAt 4095 .JUMPDEST, opAt 4096 .CALLDATASIZE, pushAt 4097 1 3, opAt 4098 .SUB, pushAt 4099 2 5203]

theorem run_size (input : ByteArray) :
    run sizePath (armEntry input) =
      some (PatternedScan.stS input 5162 [5203, sizeCond input]) := by
  let sz := UInt256.ofNat input.size
  let l0 : Located := opAt 4095 .JUMPDEST
  have h0 := PatternedScan.blockOfS l0
    (PatternedScan.pcFactS input 4095 5154 [] (by norm_num) (by
      rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide))
    (PatternedScan.stepS_jumpdest input 5154 [] (by simp) (by norm_num))
  let l1 : Located := opAt 4096 .CALLDATASIZE
  have h1 := PatternedScan.blockOfS l1
    (PatternedScan.pcFactS input 4096 5155 [] (by norm_num) (by
      rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide))
    (PatternedScan.stepS_calldatasize input 5155 [] (by simp) (by norm_num))
  let l2 : Located := pushAt 4097 1 3
  have h2 := PatternedScan.blockOfS l2
    (PatternedScan.pcFactS input 4097 5156 [sz] (by norm_num) (by
      rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide))
    (PatternedScan.stepS_push input 5156 1 3 [sz] (by simp) (by decide) (by decide) (by norm_num))
  let l3 : Located := opAt 4098 .SUB
  have h3 := PatternedScan.blockOfS l3
    (PatternedScan.pcFactS input 4098 5158 [3, sz] (by norm_num) (by
      rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide))
  let l4 : Located := pushAt 4099 2 5203
  have h4 := PatternedScan.blockOfS l4
    (PatternedScan.pcFactS input 4099 5159 [sizeCond input] (by norm_num) (by
      rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide))
    (PatternedScan.stepS_push input 5159 2 5203 [sizeCond input] (by simp) (by decide) (by decide) (by norm_num))
  have s1 := Stepper.runLocatedBlock_append [l0] [l1] _ _ _ h0 rfl h1
  have s2 := Stepper.runLocatedBlock_append [l0, l1] [l2] _ _ _ s1 rfl h2
  have s3 := Stepper.runLocatedBlock_append [l0, l1, l2] [l3] _ _ _ s2 rfl h3
  have s4 := Stepper.runLocatedBlock_append [l0, l1, l2, l3] [l4] _ _ _ s3 rfl h4
  exact s4

theorem run_size_miss (input : ByteArray) (hc : UInt256.isTrue (sizeCond input)) :
    run [opAt 4100 .JUMPI] (PatternedScan.stS input 5162 [5203, sizeCond input]) =
      some (PatternedScan.stS input 5203 []) :=
  PatternedScan.blockOfS (opAt 4100 .JUMPI)
    (PatternedScan.pcFactS input 4100 5162 [5203, sizeCond input] (by norm_num) (by
      rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide))
    (PatternedScan.stepS_jumpi_taken input 5162 5203 5203 (sizeCond input) []
      (by simp) (by norm_num) (by simpa using Word.literal_eq_ofNat 5203) hc dispatch_dest)

theorem run_size_pass (input : ByteArray) (hc : ¬ UInt256.isTrue (sizeCond input)) :
    run [opAt 4100 .JUMPI] (PatternedScan.stS input 5162 [5203, sizeCond input]) =
      some (PatternedScan.stS input 5163 []) :=
  PatternedScan.blockOfS (opAt 4100 .JUMPI)
    (PatternedScan.pcFactS input 4100 5162 [5203, sizeCond input] (by norm_num) (by
      rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide))
    (PatternedScan.stepS_jumpi_fall input 5162 5203 (sizeCond input) []
      (by simp) (by norm_num) hc)

/-! ## The empty dispatch: `JUMPDEST CALLDATASIZE PUSH2 276 JUMPI` -/

def dispatchEntry (input : ByteArray) : State := PatternedScan.stS input 5203 []

def dispatchPath : List Located :=
  [opAt 4115 .JUMPDEST, opAt 4116 .CALLDATASIZE, pushAt 4117 2 276]

theorem run_dispatch (input : ByteArray) :
    run dispatchPath (dispatchEntry input) =
      some (PatternedScan.stS input 5208 [276, UInt256.ofNat input.size]) := by
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
  let l2 : Located := pushAt 4117 2 276
  have h2 := PatternedScan.blockOfS l2
    (PatternedScan.pcFactS input 4117 5205 [sz] (by norm_num) (by
      rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide))
    (PatternedScan.stepS_push input 5205 2 276 [sz] (by simp) (by decide) (by decide) (by norm_num))
  have s1 := Stepper.runLocatedBlock_append [l0] [l1] _ _ _ h0 rfl h1
  have s2 := Stepper.runLocatedBlock_append [l0, l1] [l2] _ _ _ s1 rfl h2
  exact s2

theorem run_dispatch_miss (input : ByteArray)
    (hc : UInt256.isTrue (UInt256.ofNat input.size)) :
    run [opAt 4118 .JUMPI] (PatternedScan.stS input 5208 [276, UInt256.ofNat input.size]) =
      some (fallbackState input) :=
  PatternedScan.blockOfS (opAt 4118 .JUMPI)
    (PatternedScan.pcFactS input 4118 5208 [276, UInt256.ofNat input.size] (by norm_num) (by
      rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide))
    (PatternedScan.stepS_jumpi_taken input 5208 276 276 (UInt256.ofNat input.size) []
      (by simp) (by norm_num) (by simpa using Word.literal_eq_ofNat 276) hc generic_dest)

theorem run_dispatch_empty (input : ByteArray)
    (hc : ¬ UInt256.isTrue (UInt256.ofNat input.size)) :
    run [opAt 4118 .JUMPI] (PatternedScan.stS input 5208 [276, UInt256.ofNat input.size]) =
      some (PatternedScan.stS input 5209 []) :=
  PatternedScan.blockOfS (opAt 4118 .JUMPI)
    (PatternedScan.pcFactS input 4118 5208 [276, UInt256.ofNat input.size] (by norm_num) (by
      rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide))
    (PatternedScan.stepS_jumpi_fall input 5208 276 (UInt256.ofNat input.size) []
      (by simp) (by norm_num) hc)

/-! ## The word test -/

def wordCond (input : ByteArray) : UInt256 :=
  UInt256.xor (MachineState.readWord input 0) (UInt256.shiftLeft 6382179 232)

def wordPath : List Located :=
  [pushAt 4101 3 6382179, pushAt 4102 1 232, opAt 4103 .SHL, pushAt 4104 0 0, opAt 4105 .CALLDATALOAD,
   opAt 4106 .XOR, pushAt 4107 2 276]

theorem run_word (input : ByteArray) :
    run wordPath (PatternedScan.stS input 5163 []) =
      some (PatternedScan.stS input 5176 [276, wordCond input]) := by
  let w := MachineState.readWord input 0
  let abcW := UInt256.shiftLeft 6382179 232
  let l0 : Located := pushAt 4101 3 6382179
  have h0 := PatternedScan.blockOfS l0
    (PatternedScan.pcFactS input 4101 5163 [] (by norm_num) (by
      rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide))
    (PatternedScan.stepS_push input 5163 3 6382179 [] (by simp) (by decide) (by decide) (by norm_num))
  let l1 : Located := pushAt 4102 1 232
  have h1 := PatternedScan.blockOfS l1
    (PatternedScan.pcFactS input 4102 5167 [6382179] (by norm_num) (by
      rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide))
    (PatternedScan.stepS_push input 5167 1 232 [6382179] (by simp) (by decide) (by decide) (by norm_num))
  let l2 : Located := opAt 4103 .SHL
  have h2 := PatternedScan.blockOfS l2
    (PatternedScan.pcFactS input 4103 5169 [232, 6382179] (by norm_num) (by
      rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide))
    (PatternedScan.stepS_shl input 5169 232 6382179 [] (by simp) (by norm_num))
  let l3 : Located := pushAt 4104 0 0
  have h3 := PatternedScan.blockOfS l3
    (PatternedScan.pcFactS input 4104 5170 [abcW] (by norm_num) (by
      rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide))
    (PatternedScan.stepS_push0 input 5170 [abcW] (by simp) (by norm_num))
  let l4 : Located := opAt 4105 .CALLDATALOAD
  have h4 := PatternedScan.blockOfS l4
    (PatternedScan.pcFactS input 4105 5171 [0, abcW] (by norm_num) (by
      rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide))
    (PatternedScan.stepS_calldataload input 5171 0 [abcW] (by simp) (by norm_num))
  let l5 : Located := opAt 4106 .XOR
  have h5 := PatternedScan.blockOfS l5
    (PatternedScan.pcFactS input 4106 5172 [w, abcW] (by norm_num) (by
      rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide))
    (PatternedScan.stepS_xor input 5172 w abcW [] (by simp) (by norm_num))
  let l6 : Located := pushAt 4107 2 276
  have h6 := PatternedScan.blockOfS l6
    (PatternedScan.pcFactS input 4107 5173 [wordCond input] (by norm_num) (by
      rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide))
    (PatternedScan.stepS_push input 5173 2 276 [wordCond input] (by simp) (by decide) (by decide) (by norm_num))
  have s1 := Stepper.runLocatedBlock_append [l0] [l1] _ _ _ h0 rfl h1
  have s2 := Stepper.runLocatedBlock_append [l0, l1] [l2] _ _ _ s1 rfl h2
  have s3 := Stepper.runLocatedBlock_append [l0, l1, l2] [l3] _ _ _ s2 rfl h3
  have s4 := Stepper.runLocatedBlock_append [l0, l1, l2, l3] [l4] _ _ _ s3 rfl h4
  have s5 := Stepper.runLocatedBlock_append [l0, l1, l2, l3, l4] [l5] _ _ _ s4 rfl h5
  have s6 := Stepper.runLocatedBlock_append [l0, l1, l2, l3, l4, l5] [l6] _ _ _ s5 rfl h6
  exact s6

theorem run_word_miss (input : ByteArray) (hc : UInt256.isTrue (wordCond input)) :
    run [opAt 4108 .JUMPI] (PatternedScan.stS input 5176 [276, wordCond input]) =
      some (fallbackState input) :=
  PatternedScan.blockOfS (opAt 4108 .JUMPI)
    (PatternedScan.pcFactS input 4108 5176 [276, wordCond input] (by norm_num) (by
      rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide))
    (PatternedScan.stepS_jumpi_taken input 5176 276 276 (wordCond input) []
      (by simp) (by norm_num) (by simpa using Word.literal_eq_ofNat 276) hc generic_dest)

theorem run_word_hit (input : ByteArray) (hc : ¬ UInt256.isTrue (wordCond input)) :
    run [opAt 4108 .JUMPI] (PatternedScan.stS input 5176 [276, wordCond input]) =
      some (PatternedScan.stS input 5177 []) :=
  PatternedScan.blockOfS (opAt 4108 .JUMPI)
    (PatternedScan.pcFactS input 4108 5176 [276, wordCond input] (by norm_num) (by
      rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide))
    (PatternedScan.stepS_jumpi_fall input 5176 276 (wordCond input) []
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

/-! ## The stored return: `PUSH20 PUSH0 MSTORE`, `MSIZE`, `PUSH0 RETURN` -/

def answerMemory : ByteArray := storeWord ByteArray.empty 0 abcDigestWord

def storedState (input : ByteArray) : State :=
  { initialState submissionBytecode input 0 with
    pc := UInt256.ofNat 5200
    memory := answerMemory
    activeWords := UInt256.ofNat 1 }

def sizedState (input : ByteArray) : State :=
  { storedState input with pc := UInt256.ofNat 5201, stack := [UInt256.ofNat 32] }

def returnedState (input : ByteArray) : State :=
  { storedState input with
    pc := UInt256.ofNat 5202
    halt := .Returned
    hReturn := MachineState.readPadded answerMemory 0 32 }

def storePath : List Located :=
  [pushAt 4109 20 814647003348588794217809277549781461204094028796, pushAt 4110 0 0, opAt 4111 .MSTORE]

def finishPath : List Located :=
  [pushAt 4113 0 0, opAt 4114 .RETURN]

@[simp] theorem pcRet0 : Artifact.submissionArtifact.instructionPC 4109 = 5177 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide
@[simp] theorem pcRet1 : Artifact.submissionArtifact.instructionPC 4110 = 5198 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide
@[simp] theorem pcRet2 : Artifact.submissionArtifact.instructionPC 4111 = 5199 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide
@[simp] theorem pcRet3 : Artifact.submissionArtifact.instructionPC 4112 = 5200 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide
@[simp] theorem pcRet4 : Artifact.submissionArtifact.instructionPC 4113 = 5201 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide
@[simp] theorem pcRet5 : Artifact.submissionArtifact.instructionPC 4114 = 5202 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide

theorem run_store (input : ByteArray) :
    run storePath (PatternedScan.stS input 5177 []) = some (storedState input) := by
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
  have hd := Artifact.submissionArtifact.decodeAt_op_index 4112 .MSIZE
    (by rfl) (by decide) trivial
  have hp : (storedState input).pc.toNat = Artifact.submissionArtifact.instructionPC 4112 := by
    rw [pcRet3]; rfl
  have hop : (storedState input).decodedOp = some .MSIZE :=
    Artifact.submissionArtifact.state_decodedOp_of (storedState input) 4112
      rfl hp .MSIZE none hd rfl
  have gmraw := Msize.step hop (by change (0 : Nat) < 1024; decide)
    rfl deployAddress_not_precompile
  simpa [storedState, sizedState, initialState, Word.succ_ofNat_mod, Word.word_toNat_ofNat] using gmraw

/-! ## The empty stored return: `PUSH20 PUSH0 MSTORE`, `MSIZE`, `PUSH0 RETURN` -/

def emptyDigestWord : UInt256 := 0x9c1185a5c5e9fc54612808977ee8f548b2258d31

def emptyAnswerMemory : ByteArray := storeWord ByteArray.empty 0 emptyDigestWord

def emptyStoredState (input : ByteArray) : State :=
  { initialState submissionBytecode input 0 with
    pc := UInt256.ofNat 5232
    memory := emptyAnswerMemory
    activeWords := UInt256.ofNat 1 }

def emptySizedState (input : ByteArray) : State :=
  { emptyStoredState input with pc := UInt256.ofNat 5233, stack := [UInt256.ofNat 32] }

def emptyReturnedState (input : ByteArray) : State :=
  { emptyStoredState input with
    pc := UInt256.ofNat 5234
    halt := .Returned
    hReturn := MachineState.readPadded emptyAnswerMemory 0 32 }

def emptyStorePath : List Located :=
  [pushAt 4119 20 890993315260586290631548281360202943075753233713, pushAt 4120 0 0, opAt 4121 .MSTORE]

def emptyFinishPath : List Located :=
  [pushAt 4123 0 0, opAt 4124 .RETURN]

@[simp] theorem pcEmpty0 : Artifact.submissionArtifact.instructionPC 4119 = 5209 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide
@[simp] theorem pcEmpty1 : Artifact.submissionArtifact.instructionPC 4120 = 5230 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide
@[simp] theorem pcEmpty2 : Artifact.submissionArtifact.instructionPC 4121 = 5231 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide
@[simp] theorem pcEmpty3 : Artifact.submissionArtifact.instructionPC 4122 = 5232 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide
@[simp] theorem pcEmpty4 : Artifact.submissionArtifact.instructionPC 4123 = 5233 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide
@[simp] theorem pcEmpty5 : Artifact.submissionArtifact.instructionPC 4124 = 5234 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide

theorem run_empty_store (input : ByteArray) :
    run emptyStorePath (PatternedScan.stS input 5209 []) = some (emptyStoredState input) := by
  have hzeroNat : ({ val := 0 } : UInt256).toNat = 0 := rfl
  simp (config := { maxSteps := 1000000 })
    [emptyStorePath, opAt, pushAt, wfOp, PatternedScan.stS, emptyStoredState,
    emptyAnswerMemory, storeWord, emptyDigestWord, initialState,
    MachineState.mstore, State.activeWordsAfterUInt256,
    MachineState.activeWordsAfter, hzeroNat,
    Challenge.EvmProof.Stepper.runLocatedBlock, Challenge.EvmProof.Stepper.runLocated,
    Challenge.EvmProof.Stepper.runInstr,
    Challenge.EvmProof.Word.literal_eq_ofNat, Challenge.EvmProof.Word.succ_ofNat_mod,
    Challenge.EvmProof.Word.ofNat_add_mod, Challenge.EvmProof.Word.word_toNat_ofNat]

theorem run_empty_finish (input : ByteArray) :
    run emptyFinishPath (emptySizedState input) = some (emptyReturnedState input) := by
  have hzeroNat : ({ val := 0 } : UInt256).toNat = 0 := rfl
  simp (config := { maxSteps := 1000000 })
    [emptyFinishPath, opAt, pushAt, wfOp, emptySizedState, emptyStoredState, emptyReturnedState, initialState,
    State.activeWordsAfterUInt256, MachineState.activeWordsAfter, hzeroNat,
    Challenge.EvmProof.Stepper.runLocatedBlock, Challenge.EvmProof.Stepper.runLocated,
    Challenge.EvmProof.Stepper.runInstr,
    Challenge.EvmProof.Word.literal_eq_ofNat, Challenge.EvmProof.Word.succ_ofNat_mod,
    Challenge.EvmProof.Word.ofNat_add_mod, Challenge.EvmProof.Word.word_toNat_ofNat]

def gasSteps_empty_msize (input : ByteArray) : GasSteps (emptyStoredState input) (emptySizedState input) := by
  have hd := Artifact.submissionArtifact.decodeAt_op_index 4122 .MSIZE
    (by rfl) (by decide) trivial
  have hp : (emptyStoredState input).pc.toNat = Artifact.submissionArtifact.instructionPC 4122 := by
    rw [pcEmpty3]; rfl
  have hop : (emptyStoredState input).decodedOp = some .MSIZE :=
    Artifact.submissionArtifact.state_decodedOp_of (emptyStoredState input) 4122
      rfl hp .MSIZE none hd rfl
  have gmraw := Msize.step hop (by change (0 : Nat) < 1024; decide)
    rfl deployAddress_not_precompile
  simpa [emptyStoredState, emptySizedState, initialState, Word.succ_ofNat_mod, Word.word_toNat_ofNat] using gmraw

/-- `UInt256.ofNat input.size` is nonzero exactly when the input is nonempty. -/
theorem ofNat_size_ne_zero (input : ByteArray) (hfit : CalldataFits input)
    (hnz : input.size ≠ 0) : UInt256.ofNat input.size ≠ 0 := by
  intro h
  have h' : (UInt256.ofNat input.size).toNat = 0 := by rw [h]; rfl
  rw [Word.word_toNat_ofNat, Nat.mod_eq_of_lt (Nat.lt_trans hfit (by norm_num))] at h'
  exact hnz h'

/-! ## The exported certificates -/

/-- **Miss.** Any nonempty input other than `"abc"` leaves the arm at the generic entry. -/
def gasSteps_miss (input : ByteArray) (hfit : CalldataFits input) (hne : input ≠ abcInput)
    (hnz : input.size ≠ 0) :
    GasSteps (armEntry input) (fallbackState input) :=
  if hs : sizeCond input = 0 then
    have hw : wordCond input ≠ 0 := fun hw =>
      hne (AbcRecognition.input_eq_abc input ((sizeCond_zero_iff input hfit).1 hs)
        ((wordCond_zero_iff input).1 hw))
    (sound sizePath (run_size input)).trans
      ((sound _ (run_size_pass input (not_isTrue_of_eq _ hs))).trans
        ((sound wordPath (run_word input)).trans
          (sound _ (run_word_miss input (isTrue_of_ne _ hw)))))
  else
    (sound sizePath (run_size input)).trans
      ((sound _ (run_size_miss input (isTrue_of_ne _ hs))).trans
        ((sound dispatchPath (run_dispatch input)).trans
          (sound _ (run_dispatch_miss input
            (isTrue_of_ne _ (ofNat_size_ne_zero input hfit hnz))))))

/-- **Empty.** The empty input returns the stored empty digest. -/
def gasSteps_empty (input : ByteArray) (hsize : input.size = 0) :
    GasSteps (armEntry input) (emptyReturnedState input) := by
  have hs : sizeCond input ≠ 0 := by
    unfold sizeCond
    rw [hsize]
    decide
  have hz : ¬ UInt256.isTrue (UInt256.ofNat input.size) := by
    rw [hsize]
    decide
  exact (sound sizePath (run_size input)).trans
    ((sound _ (run_size_miss input (isTrue_of_ne _ hs))).trans
      ((sound dispatchPath (run_dispatch input)).trans
        ((sound _ (run_dispatch_empty input hz)).trans
          ((sound emptyStorePath (run_empty_store input)).trans
            ((gasSteps_empty_msize input).trans
              (sound emptyFinishPath (run_empty_finish input)))))))


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

/-- The returned bytes are exactly `spec ""`. -/
theorem emptyAnswerMemory_read :
    MachineState.readPadded emptyAnswerMemory 0 32 = EmptySpec.emptyOutput := by
  unfold emptyAnswerMemory storeWord
  have h := Memory.readPadded_writeBytes_same ByteArray.empty
    (Data.Bytes.natToBytesPadded emptyDigestWord.toNat 32) 0
  have hw : Data.Bytes.natToBytesPadded emptyDigestWord.toNat 32 = EmptySpec.emptyOutput := by
    rw [Memory.natToBytesPadded_eq_natToBE]
    decide
  simpa only [YulEvmCompiler.BytesLemmas.natToBytesPadded_size, hw] using h

/-- **The empty arm's contribution to `Correct`.** -/
theorem correct_empty (input : ByteArray) (hsize : input.size = 0)
    (entryPrefix : GasSteps (initialState submissionBytecode input 0) (armEntry input)) :
    ∃ g₀ : Nat, ∀ gas : Nat, g₀ ≤ gas →
      Eval (initialState submissionBytecode input gas) (.returned (spec input)) := by
  let trace := entryPrefix.trans (gasSteps_empty input hsize)
  have hinput : input = ByteArray.empty := by
    apply ByteArray.ext
    apply Array.ext
    · simpa using hsize
    · intro i hi
      simp [hsize] at hi
  have hspec : spec input = EmptySpec.emptyOutput := by
    rw [hinput]; exact EmptySpec.spec_empty
  refine ⟨trace.cost, fun gas hgas => ?_⟩
  have heval := eval_of_steps (trace.trace gas hgas) (by
    simp [withGas, emptyReturnedState, emptyStoredState, initialState, State.isDone, State.isHalted, State.isRunning])
  rw [State.toResult_returned _ (by rfl)] at heval
  change Eval (withGas (initialState submissionBytecode input 0) gas)
    (.returned (MachineState.readPadded emptyAnswerMemory 0 32)) at heval
  rw [emptyAnswerMemory_read, ← hspec] at heval
  have hwith : withGas (initialState submissionBytecode input 0) gas
      = initialState submissionBytecode input gas := rfl
  simpa only [hwith] using heval

#print axioms correct_abc

end Challenge.Ripemd160.Submission.Proofs.Bytecode.AbcArm
