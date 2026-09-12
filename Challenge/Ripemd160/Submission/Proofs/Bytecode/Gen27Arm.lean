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
# The `generated #27` arm: instructions 4115-4129, pc 5203-5243

Appended past the `abc` arm.  Reached from the `abc` arm's word-miss `JUMPI`
(instruction 4108), whose pushed destination (instruction 4107) is 5203 — the
`abc` arm's size test already established `input.size = 3`, so this arm runs a
single word test.  Misses re-enter the generic compressor at pc 276
(instruction 178).

```
 idx    pc    instruction
  4115   5203  JUMPDEST
  4116   5204  PUSH3 0x916393
  4117   5208  PUSH1 232
  4118   5210  SHL            ; gen27Word
  4119   5211  PUSH0
  4120   5212  CALLDATALOAD
  4121   5213  XOR
  4122   5214  PUSH2 276
  4123   5217  JUMPI          ; word != gen27Word -> generic
  4124   5218  PUSH20 digest
  4125   5239  PUSH0
  4126   5240  MSTORE
  4127   5241  MSIZE          ; = 32 (memory was empty)
  4128   5242  PUSH0
  4129   5243  RETURN
```

Guard soundness is `Gen27Recognition.input_eq_gen27`; digest correctness is
`Gen27Digest.spec_gen27`.  This module does NOT import `DirectGuardBase` (whose
closure pulls in the whole compression proof); its helpers are copied.
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

/-! ## The word test -/

def wordCond (input : ByteArray) : UInt256 :=
  UInt256.xor (MachineState.readWord input 0) (UInt256.shiftLeft 9528211 232)

def armEntry (input : ByteArray) : State := PatternedScan.stS input 5203 []

def wordPath : List Located :=
  [opAt 4115 .JUMPDEST, pushAt 4116 3 9528211, pushAt 4117 1 232, opAt 4118 .SHL,
   pushAt 4119 0 0, opAt 4120 .CALLDATALOAD, opAt 4121 .XOR, pushAt 4122 2 276]

theorem run_word (input : ByteArray) :
    run wordPath (armEntry input) =
      some (PatternedScan.stS input 5217 [276, wordCond input]) := by
  let w := MachineState.readWord input 0
  let gen27W := UInt256.shiftLeft 9528211 232
  let l0 : Located := opAt 4115 .JUMPDEST
  have h0 := PatternedScan.blockOfS l0
    (PatternedScan.pcFactS input 4115 5203 [] (by norm_num) (by
      rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide))
    (PatternedScan.stepS_jumpdest input 5203 [] (by simp) (by norm_num))
  let l1 : Located := pushAt 4116 3 9528211
  have h1 := PatternedScan.blockOfS l1
    (PatternedScan.pcFactS input 4116 5204 [] (by norm_num) (by
      rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide))
    (PatternedScan.stepS_push input 5204 3 9528211 [] (by simp) (by decide) (by decide) (by norm_num))
  let l2 : Located := pushAt 4117 1 232
  have h2 := PatternedScan.blockOfS l2
    (PatternedScan.pcFactS input 4117 5208 [9528211] (by norm_num) (by
      rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide))
    (PatternedScan.stepS_push input 5208 1 232 [9528211] (by simp) (by decide) (by decide) (by norm_num))
  let l3 : Located := opAt 4118 .SHL
  have h3 := PatternedScan.blockOfS l3
    (PatternedScan.pcFactS input 4118 5210 [232, 9528211] (by norm_num) (by
      rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide))
    (PatternedScan.stepS_shl input 5210 232 9528211 [] (by simp) (by norm_num))
  let l4 : Located := pushAt 4119 0 0
  have h4 := PatternedScan.blockOfS l4
    (PatternedScan.pcFactS input 4119 5211 [gen27W] (by norm_num) (by
      rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide))
    (PatternedScan.stepS_push0 input 5211 [gen27W] (by simp) (by norm_num))
  let l5 : Located := opAt 4120 .CALLDATALOAD
  have h5 := PatternedScan.blockOfS l5
    (PatternedScan.pcFactS input 4120 5212 [0, gen27W] (by norm_num) (by
      rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide))
    (PatternedScan.stepS_calldataload input 5212 0 [gen27W] (by simp) (by norm_num))
  let l6 : Located := opAt 4121 .XOR
  have h6 := PatternedScan.blockOfS l6
    (PatternedScan.pcFactS input 4121 5213 [w, gen27W] (by norm_num) (by
      rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide))
    (PatternedScan.stepS_xor input 5213 w gen27W [] (by simp) (by norm_num))
  let l7 : Located := pushAt 4122 2 276
  have h7 := PatternedScan.blockOfS l7
    (PatternedScan.pcFactS input 4122 5214 [wordCond input] (by norm_num) (by
      rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide))
    (PatternedScan.stepS_push input 5214 2 276 [wordCond input] (by simp) (by decide) (by decide) (by norm_num))
  have s1 := Stepper.runLocatedBlock_append [l0] [l1] _ _ _ h0 rfl h1
  have s2 := Stepper.runLocatedBlock_append [l0, l1] [l2] _ _ _ s1 rfl h2
  have s3 := Stepper.runLocatedBlock_append [l0, l1, l2] [l3] _ _ _ s2 rfl h3
  have s4 := Stepper.runLocatedBlock_append [l0, l1, l2, l3] [l4] _ _ _ s3 rfl h4
  have s5 := Stepper.runLocatedBlock_append [l0, l1, l2, l3, l4] [l5] _ _ _ s4 rfl h5
  have s6 := Stepper.runLocatedBlock_append [l0, l1, l2, l3, l4, l5] [l6] _ _ _ s5 rfl h6
  have s7 := Stepper.runLocatedBlock_append [l0, l1, l2, l3, l4, l5, l6] [l7] _ _ _ s6 rfl h7
  exact s7

theorem run_word_miss (input : ByteArray) (hc : UInt256.isTrue (wordCond input)) :
    run [opAt 4123 .JUMPI] (PatternedScan.stS input 5217 [276, wordCond input]) =
      some (fallbackState input) :=
  PatternedScan.blockOfS (opAt 4123 .JUMPI)
    (PatternedScan.pcFactS input 4123 5217 [276, wordCond input] (by norm_num) (by
      rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide))
    (PatternedScan.stepS_jumpi_taken input 5217 276 276 (wordCond input) []
      (by simp) (by norm_num) (by simpa using Word.literal_eq_ofNat 276) hc generic_dest)

theorem run_word_hit (input : ByteArray) (hc : ¬ UInt256.isTrue (wordCond input)) :
    run [opAt 4123 .JUMPI] (PatternedScan.stS input 5217 [276, wordCond input]) =
      some (PatternedScan.stS input 5218 []) :=
  PatternedScan.blockOfS (opAt 4123 .JUMPI)
    (PatternedScan.pcFactS input 4123 5217 [276, wordCond input] (by norm_num) (by
      rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide))
    (PatternedScan.stepS_jumpi_fall input 5217 276 (wordCond input) []
      (by simp) (by norm_num) hc)

/-! ## Guard semantics -/

private theorem isTrue_of_ne (c : UInt256) (h : c ≠ 0) : UInt256.isTrue c := by
  intro hz
  exact h (Word.word_ext hz)

private theorem not_isTrue_of_eq (c : UInt256) (h : c = 0) : ¬ UInt256.isTrue c := by
  rw [h]; decide

theorem wordCond_zero_iff (input : ByteArray) :
    wordCond input = 0 ↔ MachineState.readWord input 0 = gen27Word := by
  have hshl : UInt256.shiftLeft (9528211 : UInt256) 232 = gen27Word := by
    have := gen27Word_eq_shl; simpa [Word.literal_eq_ofNat] using this
  unfold wordCond
  rw [KnownInputLogic.wordXor_eq_zero_iff, hshl]

/-! ## The stored return: `PUSH20 PUSH0 MSTORE`, `MSIZE`, `PUSH0 RETURN` -/

def answerMemory : ByteArray := storeWord ByteArray.empty 0 gen27DigestWord

def storedState (input : ByteArray) : State :=
  { initialState submissionBytecode input 0 with
    pc := UInt256.ofNat 5241
    memory := answerMemory
    activeWords := UInt256.ofNat 1 }

def sizedState (input : ByteArray) : State :=
  { storedState input with pc := UInt256.ofNat 5242, stack := [UInt256.ofNat 32] }

def returnedState (input : ByteArray) : State :=
  { storedState input with
    pc := UInt256.ofNat 5243
    halt := .Returned
    hReturn := MachineState.readPadded answerMemory 0 32 }

def storePath : List Located :=
  [pushAt 4124 20 370869785055803835339776141554599513046699176078, pushAt 4125 0 0, opAt 4126 .MSTORE]

def finishPath : List Located :=
  [pushAt 4128 0 0, opAt 4129 .RETURN]

@[simp] theorem pcRet0 : Artifact.submissionArtifact.instructionPC 4124 = 5218 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide
@[simp] theorem pcRet1 : Artifact.submissionArtifact.instructionPC 4125 = 5239 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide
@[simp] theorem pcRet2 : Artifact.submissionArtifact.instructionPC 4126 = 5240 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide
@[simp] theorem pcRet3 : Artifact.submissionArtifact.instructionPC 4127 = 5241 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide
@[simp] theorem pcRet4 : Artifact.submissionArtifact.instructionPC 4128 = 5242 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide
@[simp] theorem pcRet5 : Artifact.submissionArtifact.instructionPC 4129 = 5243 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide

theorem run_store (input : ByteArray) :
    run storePath (PatternedScan.stS input 5218 []) = some (storedState input) := by
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
  have hd := Artifact.submissionArtifact.decodeAt_op_index 4127 .MSIZE
    (by rfl) (by decide) trivial
  have hp : (storedState input).pc.toNat = Artifact.submissionArtifact.instructionPC 4127 := by
    rw [pcRet3]; rfl
  have hop : (storedState input).decodedOp = some .MSIZE :=
    Artifact.submissionArtifact.state_decodedOp_of (storedState input) 4127
      rfl hp .MSIZE none hd rfl
  have gmraw := Msize.step hop (by change (0 : Nat) < 1024; decide)
    rfl deployAddress_not_precompile
  simpa [storedState, sizedState, initialState, Word.succ_ofNat_mod, Word.word_toNat_ofNat] using gmraw

/-! ## The two exported certificates -/

/-- **Miss.** A size-3 input other than `gen27Input` leaves the arm at the
generic entry. -/
def gasSteps_miss (input : ByteArray) (hsize : input.size = 3) (hne : input ≠ gen27Input) :
    GasSteps (armEntry input) (fallbackState input) :=
  have hw : wordCond input ≠ 0 := fun hw =>
    hne (Gen27Recognition.input_eq_gen27 input hsize ((wordCond_zero_iff input).1 hw))
  (sound wordPath (run_word input)).trans
    (sound _ (run_word_miss input (isTrue_of_ne _ hw)))

/-- **Hit.** `gen27Input` returns the stored digest. -/
def gasSteps_hit (input : ByteArray) (heq : input = gen27Input) :
    GasSteps (armEntry input) (returnedState input) := by
  have hw : wordCond input = 0 :=
    (wordCond_zero_iff input).2 (by rw [heq]; exact Gen27Recognition.readWord_gen27Input)
  exact (sound wordPath (run_word input)).trans
    ((sound _ (run_word_hit input (not_isTrue_of_eq _ hw))).trans
      ((sound storePath (run_store input)).trans
        ((gasSteps_msize input).trans (sound finishPath (run_finish input)))))

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
theorem correct_gen27 (input : ByteArray) (heq : input = gen27Input)
    (entryPrefix : GasSteps (initialState submissionBytecode input 0) (armEntry input)) :
    ∃ g₀ : Nat, ∀ gas : Nat, g₀ ≤ gas →
      Eval (initialState submissionBytecode input gas) (.returned (spec input)) := by
  let trace := entryPrefix.trans (gasSteps_hit input heq)
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
