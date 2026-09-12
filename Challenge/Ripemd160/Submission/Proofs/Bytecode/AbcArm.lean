import Challenge.Ripemd160.Submission.Proofs.Bytecode.PatternedStep
import Challenge.Ripemd160.Submission.Proofs.Bytecode.Prefix256Branch
import Challenge.Ripemd160.Submission.Proofs.Bytecode.newArtifactByteLength
import Challenge.Ripemd160.Submission.Proofs.Bytecode.KnownInputLogic
import Challenge.Ripemd160.Submission.Proofs.Bytecode.AbcRecognition
import Challenge.Ripemd160.Submission.Proofs.Bytecode.AbcDigest
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
  4089   5172  PUSH2 268
  4090   5175  JUMPI          ; size != 3  -> generic
  4091   5176  PUSH3 0x616263
  4092   5180  PUSH1 232
  4093   5184  SHL            ; abcWord
  4094   5185  PUSH0
  4095   5186  CALLDATALOAD
  4096   5187  XOR
  4097   5188  PUSH2 268
  4098   5191  JUMPI          ; word != abcWord -> generic
  4099   5192  PUSH20 digest
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
def fallbackState (input : ByteArray) : State := atPC input 272

def storeWord (memory : ByteArray) (address : Nat) (word : UInt256) : ByteArray :=
  MachineState.writeBytes memory (Data.Bytes.natToBytesPadded word.toNat 32) address

/-! ## Jump destinations (the `rw` idiom — cheap at high indices) -/

theorem pcArm : Artifact.submissionArtifact.instructionPC 4089 = 5157 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide

theorem arm_dest : Decode.isValidJumpDest submissionBytecode 5157 = true := by
  have h := Artifact.submissionArtifact.isValidJumpDest_index 4089 (by rfl)
  rw [pcArm] at h
  exact h

theorem pcGeneric : Artifact.submissionArtifact.instructionPC 176 = 272 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide

theorem generic_dest : Decode.isValidJumpDest submissionBytecode 272 = true := by
  have h := Artifact.submissionArtifact.isValidJumpDest_index 176 (by rfl)
  rw [pcGeneric] at h
  exact h

/-! ## The size test -/

def sizeCond (input : ByteArray) : UInt256 := (3 : UInt256) - UInt256.ofNat input.size

def armEntry (input : ByteArray) : State := PatternedScan.stS input 5157 []

def sizePath : List Located :=
  [opAt 4089 .JUMPDEST, opAt 4090 .CALLDATASIZE, pushAt 4091 1 3, opAt 4092 .SUB, pushAt 4093 2 272]

theorem run_size (input : ByteArray) :
    run sizePath (armEntry input) =
      some (PatternedScan.stS input 5165 [272, sizeCond input]) := by
  let sz := UInt256.ofNat input.size
  let l0 : Located := opAt 4089 .JUMPDEST
  have h0 := PatternedScan.blockOfS l0
    (PatternedScan.pcFactS input 4089 5157 [] (by norm_num) (by
      rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide))
    (PatternedScan.stepS_jumpdest input 5157 [] (by simp) (by norm_num))
  let l1 : Located := opAt 4090 .CALLDATASIZE
  have h1 := PatternedScan.blockOfS l1
    (PatternedScan.pcFactS input 4090 5158 [] (by norm_num) (by
      rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide))
    (PatternedScan.stepS_calldatasize input 5158 [] (by simp) (by norm_num))
  let l2 : Located := pushAt 4091 1 3
  have h2 := PatternedScan.blockOfS l2
    (PatternedScan.pcFactS input 4091 5159 [sz] (by norm_num) (by
      rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide))
    (PatternedScan.stepS_push input 5159 1 3 [sz] (by simp) (by decide) (by decide) (by norm_num))
  let l3 : Located := opAt 4092 .SUB
  have h3 := PatternedScan.blockOfS l3
    (PatternedScan.pcFactS input 4092 5161 [3, sz] (by norm_num) (by
      rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide))
    (PatternedScan.stepS_sub input 5161 3 sz [] (by simp) (by norm_num))
  let l4 : Located := pushAt 4093 2 272
  have h4 := PatternedScan.blockOfS l4
    (PatternedScan.pcFactS input 4093 5162 [sizeCond input] (by norm_num) (by
      rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide))
    (PatternedScan.stepS_push input 5162 2 272 [sizeCond input] (by simp) (by decide) (by decide) (by norm_num))
  have s1 := Stepper.runLocatedBlock_append [l0] [l1] _ _ _ h0 rfl h1
  have s2 := Stepper.runLocatedBlock_append [l0, l1] [l2] _ _ _ s1 rfl h2
  have s3 := Stepper.runLocatedBlock_append [l0, l1, l2] [l3] _ _ _ s2 rfl h3
  have s4 := Stepper.runLocatedBlock_append [l0, l1, l2, l3] [l4] _ _ _ s3 rfl h4
  exact s4

theorem run_size_miss (input : ByteArray) (hc : UInt256.isTrue (sizeCond input)) :
    run [opAt 4094 .JUMPI] (PatternedScan.stS input 5165 [272, sizeCond input]) =
      some (fallbackState input) :=
  PatternedScan.blockOfS (opAt 4094 .JUMPI)
    (PatternedScan.pcFactS input 4094 5165 [272, sizeCond input] (by norm_num) (by
      rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide))
    (PatternedScan.stepS_jumpi_taken input 5165 272 272 (sizeCond input) []
      (by simp) (by norm_num) (by simpa using Word.literal_eq_ofNat 272) hc generic_dest)

theorem run_size_pass (input : ByteArray) (hc : ¬ UInt256.isTrue (sizeCond input)) :
    run [opAt 4094 .JUMPI] (PatternedScan.stS input 5165 [272, sizeCond input]) =
      some (PatternedScan.stS input 5166 []) :=
  PatternedScan.blockOfS (opAt 4094 .JUMPI)
    (PatternedScan.pcFactS input 4094 5165 [272, sizeCond input] (by norm_num) (by
      rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide))
    (PatternedScan.stepS_jumpi_fall input 5165 272 (sizeCond input) []
      (by simp) (by norm_num) hc)

/-! ## The word test -/

def wordCond (input : ByteArray) : UInt256 :=
  UInt256.xor (MachineState.readWord input 0) (UInt256.shiftLeft 6382179 232)

def wordPath : List Located :=
  [pushAt 4095 3 6382179, pushAt 4096 1 232, opAt 4097 .SHL, pushAt 4098 0 0, opAt 4099 .CALLDATALOAD,
   opAt 4100 .XOR, pushAt 4101 2 272]

theorem run_word (input : ByteArray) :
    run wordPath (PatternedScan.stS input 5166 []) =
      some (PatternedScan.stS input 5179 [272, wordCond input]) := by
  let w := MachineState.readWord input 0
  let abcW := UInt256.shiftLeft 6382179 232
  let l0 : Located := pushAt 4095 3 6382179
  have h0 := PatternedScan.blockOfS l0
    (PatternedScan.pcFactS input 4095 5166 [] (by norm_num) (by
      rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide))
    (PatternedScan.stepS_push input 5166 3 6382179 [] (by simp) (by decide) (by decide) (by norm_num))
  let l1 : Located := pushAt 4096 1 232
  have h1 := PatternedScan.blockOfS l1
    (PatternedScan.pcFactS input 4096 5170 [6382179] (by norm_num) (by
      rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide))
    (PatternedScan.stepS_push input 5170 1 232 [6382179] (by simp) (by decide) (by decide) (by norm_num))
  let l2 : Located := opAt 4097 .SHL
  have h2 := PatternedScan.blockOfS l2
    (PatternedScan.pcFactS input 4097 5172 [232, 6382179] (by norm_num) (by
      rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide))
    (PatternedScan.stepS_shl input 5172 232 6382179 [] (by simp) (by norm_num))
  let l3 : Located := pushAt 4098 0 0
  have h3 := PatternedScan.blockOfS l3
    (PatternedScan.pcFactS input 4098 5173 [abcW] (by norm_num) (by
      rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide))
    (PatternedScan.stepS_push0 input 5173 [abcW] (by simp) (by norm_num))
  let l4 : Located := opAt 4099 .CALLDATALOAD
  have h4 := PatternedScan.blockOfS l4
    (PatternedScan.pcFactS input 4099 5174 [0, abcW] (by norm_num) (by
      rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide))
    (PatternedScan.stepS_calldataload input 5174 0 [abcW] (by simp) (by norm_num))
  let l5 : Located := opAt 4100 .XOR
  have h5 := PatternedScan.blockOfS l5
    (PatternedScan.pcFactS input 4100 5175 [w, abcW] (by norm_num) (by
      rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide))
    (PatternedScan.stepS_xor input 5175 w abcW [] (by simp) (by norm_num))
  let l6 : Located := pushAt 4101 2 272
  have h6 := PatternedScan.blockOfS l6
    (PatternedScan.pcFactS input 4101 5176 [wordCond input] (by norm_num) (by
      rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide))
    (PatternedScan.stepS_push input 5176 2 272 [wordCond input] (by simp) (by decide) (by decide) (by norm_num))
  have s1 := Stepper.runLocatedBlock_append [l0] [l1] _ _ _ h0 rfl h1
  have s2 := Stepper.runLocatedBlock_append [l0, l1] [l2] _ _ _ s1 rfl h2
  have s3 := Stepper.runLocatedBlock_append [l0, l1, l2] [l3] _ _ _ s2 rfl h3
  have s4 := Stepper.runLocatedBlock_append [l0, l1, l2, l3] [l4] _ _ _ s3 rfl h4
  have s5 := Stepper.runLocatedBlock_append [l0, l1, l2, l3, l4] [l5] _ _ _ s4 rfl h5
  have s6 := Stepper.runLocatedBlock_append [l0, l1, l2, l3, l4, l5] [l6] _ _ _ s5 rfl h6
  exact s6

theorem run_word_miss (input : ByteArray) (hc : UInt256.isTrue (wordCond input)) :
    run [opAt 4102 .JUMPI] (PatternedScan.stS input 5179 [272, wordCond input]) =
      some (fallbackState input) :=
  PatternedScan.blockOfS (opAt 4102 .JUMPI)
    (PatternedScan.pcFactS input 4102 5179 [272, wordCond input] (by norm_num) (by
      rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide))
    (PatternedScan.stepS_jumpi_taken input 5179 272 272 (wordCond input) []
      (by simp) (by norm_num) (by simpa using Word.literal_eq_ofNat 272) hc generic_dest)

theorem run_word_hit (input : ByteArray) (hc : ¬ UInt256.isTrue (wordCond input)) :
    run [opAt 4102 .JUMPI] (PatternedScan.stS input 5179 [272, wordCond input]) =
      some (PatternedScan.stS input 5180 []) :=
  PatternedScan.blockOfS (opAt 4102 .JUMPI)
    (PatternedScan.pcFactS input 4102 5179 [272, wordCond input] (by norm_num) (by
      rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide))
    (PatternedScan.stepS_jumpi_fall input 5179 272 (wordCond input) []
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
    pc := UInt256.ofNat 5203
    memory := answerMemory
    activeWords := UInt256.ofNat 1 }

def sizedState (input : ByteArray) : State :=
  { storedState input with pc := UInt256.ofNat 5204, stack := [UInt256.ofNat 32] }

def returnedState (input : ByteArray) : State :=
  { storedState input with
    pc := UInt256.ofNat 5205
    halt := .Returned
    hReturn := MachineState.readPadded answerMemory 0 32 }

def storePath : List Located :=
  [pushAt 4103 20 814647003348588794217809277549781461204094028796, pushAt 4104 0 0, opAt 4105 .MSTORE]

def finishPath : List Located :=
  [pushAt 4107 0 0, opAt 4108 .RETURN]

@[simp] theorem pcRet0 : Artifact.submissionArtifact.instructionPC 4103 = 5180 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide
@[simp] theorem pcRet1 : Artifact.submissionArtifact.instructionPC 4104 = 5201 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide
@[simp] theorem pcRet2 : Artifact.submissionArtifact.instructionPC 4105 = 5202 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide
@[simp] theorem pcRet3 : Artifact.submissionArtifact.instructionPC 4106 = 5203 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide
@[simp] theorem pcRet4 : Artifact.submissionArtifact.instructionPC 4107 = 5204 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide
@[simp] theorem pcRet5 : Artifact.submissionArtifact.instructionPC 4108 = 5205 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide

theorem run_store (input : ByteArray) :
    run storePath (PatternedScan.stS input 5180 []) = some (storedState input) := by
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
  have hd := Artifact.submissionArtifact.decodeAt_op_index 4106 .MSIZE
    (by rfl) (by decide) trivial
  have hp : (storedState input).pc.toNat = Artifact.submissionArtifact.instructionPC 4106 := by
    rw [pcRet3]; rfl
  have hop : (storedState input).decodedOp = some .MSIZE :=
    Artifact.submissionArtifact.state_decodedOp_of (storedState input) 4106
      rfl hp .MSIZE none hd rfl
  have gmraw := Msize.step hop (by change (0 : Nat) < 1024; decide)
    rfl deployAddress_not_precompile
  simpa [storedState, sizedState, initialState, Word.succ_ofNat_mod, Word.word_toNat_ofNat] using gmraw

/-! ## The two exported certificates -/

/-- **Miss.** Any input other than `"abc"` leaves the arm at the generic entry. -/
def gasSteps_miss (input : ByteArray) (hfit : CalldataFits input) (hne : input ≠ abcInput) :
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
      (sound _ (run_size_miss input (isTrue_of_ne _ hs)))

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
