import Challenge.Ripemd160.Submission.Proofs.Bytecode.PatternedStep
import Challenge.Ripemd160.Submission.Proofs.Bytecode.Prefix256Branch
import Challenge.Ripemd160.Submission.Proofs.Bytecode.newArtifactByteLength
import Challenge.Ripemd160.Submission.Proofs.Bytecode.KnownInputLogic
import Challenge.Ripemd160.Submission.Proofs.Bytecode.Gen01Recognition
import Challenge.Ripemd160.Submission.Proofs.Bytecode.Gen01Digest
import Challenge.EvmProof.Memory
import Challenge.EvmProof.Execution
import Challenge.Ripemd160.Submission.Proofs.Bytecode.Msize

/-!
# The `generated #01` arm: instructions 4119-4136, pc 5206-5280

Appended past the `abc` arm.  Reached from the `abc` arm's size-miss `JUMPI`
(instruction 4104), whose pushed destination (instruction 4103) is 5206.  Misses
re-enter the generic compressor at pc 453 (instruction 282).

The two tests branch separately: the size test first, so every input whose
size is not 32 leaves after six instructions.

```
 idx    pc    instruction
  4119   5206  JUMPDEST
  4120   5207  CALLDATASIZE
  4121   5208  PUSH1 32
  4122   5210  SUB            ; 32 - size
  4123   5211  PUSH2 453
  4124   5214  JUMPI          ; size != 32 -> generic
  4125   5215  PUSH32 gen01Word
  4126   5248  PUSH0
  4127   5249  CALLDATALOAD
  4128   5250  XOR
  4129   5251  PUSH2 453
  4130   5254  JUMPI          ; word != gen01Word -> generic
  4131   5255  PUSH20 digest
  4132   5276  PUSH0
  4133   5277  MSTORE
  4134   5278  MSIZE          ; = 32 (memory was empty)
  4135   5279  PUSH0
  4136   5280  RETURN
```

Guard soundness is `Gen01Recognition.input_eq_gen01`; digest correctness is
`Gen01Digest.spec_gen01`.  This module does NOT import `DirectGuardBase` (whose
closure pulls in the whole compression proof); its helpers are copied.
-/

set_option warningAsError true
set_option maxRecDepth 100000
set_option maxHeartbeats 40000000
set_option linter.unusedSimpArgs false

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.Gen01Arm

open Challenge.Ripemd160 Challenge.EvmProof EvmSemantics EvmSemantics.EVM
open Gen01InputData

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
def fallbackState (input : ByteArray) : State := atPC input 453

def storeWord (memory : ByteArray) (address : Nat) (word : UInt256) : ByteArray :=
  MachineState.writeBytes memory (Data.Bytes.natToBytesPadded word.toNat 32) address

/-! ## Jump destinations (the `rw` idiom — cheap at high indices) -/

theorem pcArm : Artifact.submissionArtifact.instructionPC 4119 = 5206 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide

theorem arm_dest : Decode.isValidJumpDest submissionBytecode 5206 = true := by
  have h := Artifact.submissionArtifact.isValidJumpDest_index 4119 (by rfl)
  rw [pcArm] at h
  exact h

theorem pcGeneric : Artifact.submissionArtifact.instructionPC 282 = 453 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide

theorem generic_dest : Decode.isValidJumpDest submissionBytecode 453 = true := by
  have h := Artifact.submissionArtifact.isValidJumpDest_index 282 (by rfl)
  rw [pcGeneric] at h
  exact h

/-! ## The size test -/

def sizeCond (input : ByteArray) : UInt256 := (32 : UInt256) - UInt256.ofNat input.size

def armEntry (input : ByteArray) : State := PatternedScan.stS input 5206 []

def sizePath : List Located :=
  [opAt 4119 .JUMPDEST, opAt 4120 .CALLDATASIZE, pushAt 4121 1 32, opAt 4122 .SUB, pushAt 4123 2 453]

theorem run_size (input : ByteArray) :
    run sizePath (armEntry input) =
      some (PatternedScan.stS input 5214 [453, sizeCond input]) := by
  let sz := UInt256.ofNat input.size
  let l0 : Located := opAt 4119 .JUMPDEST
  have h0 := PatternedScan.blockOfS l0
    (PatternedScan.pcFactS input 4119 5206 [] (by norm_num) (by
      rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide))
    (PatternedScan.stepS_jumpdest input 5206 [] (by simp) (by norm_num))
  let l1 : Located := opAt 4120 .CALLDATASIZE
  have h1 := PatternedScan.blockOfS l1
    (PatternedScan.pcFactS input 4120 5207 [] (by norm_num) (by
      rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide))
    (PatternedScan.stepS_calldatasize input 5207 [] (by simp) (by norm_num))
  let l2 : Located := pushAt 4121 1 32
  have h2 := PatternedScan.blockOfS l2
    (PatternedScan.pcFactS input 4121 5208 [sz] (by norm_num) (by
      rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide))
    (PatternedScan.stepS_push input 5208 1 32 [sz] (by simp) (by decide) (by decide) (by norm_num))
  let l3 : Located := opAt 4122 .SUB
  have h3 := PatternedScan.blockOfS l3
    (PatternedScan.pcFactS input 4122 5210 [32, sz] (by norm_num) (by
      rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide))
    (PatternedScan.stepS_sub input 5210 32 sz [] (by simp) (by norm_num))
  let l4 : Located := pushAt 4123 2 453
  have h4 := PatternedScan.blockOfS l4
    (PatternedScan.pcFactS input 4123 5211 [sizeCond input] (by norm_num) (by
      rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide))
    (PatternedScan.stepS_push input 5211 2 453 [sizeCond input] (by simp) (by decide) (by decide) (by norm_num))
  have s1 := Stepper.runLocatedBlock_append [l0] [l1] _ _ _ h0 rfl h1
  have s2 := Stepper.runLocatedBlock_append [l0, l1] [l2] _ _ _ s1 rfl h2
  have s3 := Stepper.runLocatedBlock_append [l0, l1, l2] [l3] _ _ _ s2 rfl h3
  have s4 := Stepper.runLocatedBlock_append [l0, l1, l2, l3] [l4] _ _ _ s3 rfl h4
  exact s4

theorem run_size_miss (input : ByteArray) (hc : UInt256.isTrue (sizeCond input)) :
    run [opAt 4124 .JUMPI] (PatternedScan.stS input 5214 [453, sizeCond input]) =
      some (fallbackState input) :=
  PatternedScan.blockOfS (opAt 4124 .JUMPI)
    (PatternedScan.pcFactS input 4124 5214 [453, sizeCond input] (by norm_num) (by
      rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide))
    (PatternedScan.stepS_jumpi_taken input 5214 453 453 (sizeCond input) []
      (by simp) (by norm_num) (by simpa using Word.literal_eq_ofNat 453) hc generic_dest)

theorem run_size_pass (input : ByteArray) (hc : ¬ UInt256.isTrue (sizeCond input)) :
    run [opAt 4124 .JUMPI] (PatternedScan.stS input 5214 [453, sizeCond input]) =
      some (PatternedScan.stS input 5215 []) :=
  PatternedScan.blockOfS (opAt 4124 .JUMPI)
    (PatternedScan.pcFactS input 4124 5214 [453, sizeCond input] (by norm_num) (by
      rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide))
    (PatternedScan.stepS_jumpi_fall input 5214 453 (sizeCond input) []
      (by simp) (by norm_num) hc)

/-! ## The word test -/

def wordCond (input : ByteArray) : UInt256 :=
  UInt256.xor (MachineState.readWord input 0) gen01Word

def wordPath : List Located :=
  [pushAt 4125 32 gen01Word, pushAt 4126 0 0, opAt 4127 .CALLDATALOAD,
   opAt 4128 .XOR, pushAt 4129 2 453]

theorem run_word (input : ByteArray) :
    run wordPath (PatternedScan.stS input 5215 []) =
      some (PatternedScan.stS input 5254 [453, wordCond input]) := by
  let w := MachineState.readWord input 0
  let l0 : Located := pushAt 4125 32 gen01Word
  have h0 := PatternedScan.blockOfS l0
    (PatternedScan.pcFactS input 4125 5215 [] (by norm_num) (by
      rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide))
    (PatternedScan.stepS_push input 5215 32 gen01Word [] (by simp) (by decide) (by decide) (by norm_num))
  let l1 : Located := pushAt 4126 0 0
  have h1 := PatternedScan.blockOfS l1
    (PatternedScan.pcFactS input 4126 5248 [gen01Word] (by norm_num) (by
      rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide))
    (PatternedScan.stepS_push0 input 5248 [gen01Word] (by simp) (by norm_num))
  let l2 : Located := opAt 4127 .CALLDATALOAD
  have h2 := PatternedScan.blockOfS l2
    (PatternedScan.pcFactS input 4127 5249 [0, gen01Word] (by norm_num) (by
      rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide))
    (PatternedScan.stepS_calldataload input 5249 0 [gen01Word] (by simp) (by norm_num))
  let l3 : Located := opAt 4128 .XOR
  have h3 := PatternedScan.blockOfS l3
    (PatternedScan.pcFactS input 4128 5250 [w, gen01Word] (by norm_num) (by
      rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide))
    (PatternedScan.stepS_xor input 5250 w gen01Word [] (by simp) (by norm_num))
  let l4 : Located := pushAt 4129 2 453
  have h4 := PatternedScan.blockOfS l4
    (PatternedScan.pcFactS input 4129 5251 [wordCond input] (by norm_num) (by
      rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide))
    (PatternedScan.stepS_push input 5251 2 453 [wordCond input] (by simp) (by decide) (by decide) (by norm_num))
  have s1 := Stepper.runLocatedBlock_append [l0] [l1] _ _ _ h0 rfl h1
  have s2 := Stepper.runLocatedBlock_append [l0, l1] [l2] _ _ _ s1 rfl h2
  have s3 := Stepper.runLocatedBlock_append [l0, l1, l2] [l3] _ _ _ s2 rfl h3
  have s4 := Stepper.runLocatedBlock_append [l0, l1, l2, l3] [l4] _ _ _ s3 rfl h4
  exact s4

theorem run_word_miss (input : ByteArray) (hc : UInt256.isTrue (wordCond input)) :
    run [opAt 4130 .JUMPI] (PatternedScan.stS input 5254 [453, wordCond input]) =
      some (fallbackState input) :=
  PatternedScan.blockOfS (opAt 4130 .JUMPI)
    (PatternedScan.pcFactS input 4130 5254 [453, wordCond input] (by norm_num) (by
      rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide))
    (PatternedScan.stepS_jumpi_taken input 5254 453 453 (wordCond input) []
      (by simp) (by norm_num) (by simpa using Word.literal_eq_ofNat 453) hc generic_dest)

theorem run_word_hit (input : ByteArray) (hc : ¬ UInt256.isTrue (wordCond input)) :
    run [opAt 4130 .JUMPI] (PatternedScan.stS input 5254 [453, wordCond input]) =
      some (PatternedScan.stS input 5255 []) :=
  PatternedScan.blockOfS (opAt 4130 .JUMPI)
    (PatternedScan.pcFactS input 4130 5254 [453, wordCond input] (by norm_num) (by
      rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide))
    (PatternedScan.stepS_jumpi_fall input 5254 453 (wordCond input) []
      (by simp) (by norm_num) hc)

/-! ## Guard semantics -/

private theorem isTrue_of_ne (c : UInt256) (h : c ≠ 0) : UInt256.isTrue c := by
  intro hz
  exact h (Word.word_ext hz)

private theorem not_isTrue_of_eq (c : UInt256) (h : c = 0) : ¬ UInt256.isTrue c := by
  rw [h]; decide

theorem sizeCond_zero_iff (input : ByteArray) (hfit : CalldataFits input) :
    sizeCond input = 0 ↔ input.size = 32 := by
  have hsz : input.size < 2 ^ 256 := lt_trans hfit (by norm_num)
  constructor
  · intro h
    have h' : ((32 : UInt256) - UInt256.ofNat input.size).toNat = 0 := by
      have := congrArg UInt256.toNat h
      unfold sizeCond at this
      rw [this]; rfl
    rw [Word.word_toNat_sub_cond, Word.word_toNat_ofNat, Nat.mod_eq_of_lt hsz] at h'
    have h32 : (32 : UInt256).toNat = 32 := rfl
    rw [h32] at h'
    split_ifs at h' <;> omega
  · intro h
    unfold sizeCond
    rw [h]
    decide

theorem wordCond_zero_iff (input : ByteArray) :
    wordCond input = 0 ↔ MachineState.readWord input 0 = gen01Word := by
  unfold wordCond
  rw [KnownInputLogic.wordXor_eq_zero_iff]

/-! ## The stored return: `PUSH20 PUSH0 MSTORE`, `MSIZE`, `PUSH0 RETURN` -/

def answerMemory : ByteArray := storeWord ByteArray.empty 0 gen01DigestWord

def storedState (input : ByteArray) : State :=
  { initialState submissionBytecode input 0 with
    pc := UInt256.ofNat 5278
    memory := answerMemory
    activeWords := UInt256.ofNat 1 }

def sizedState (input : ByteArray) : State :=
  { storedState input with pc := UInt256.ofNat 5279, stack := [UInt256.ofNat 32] }

def returnedState (input : ByteArray) : State :=
  { storedState input with
    pc := UInt256.ofNat 5280
    halt := .Returned
    hReturn := MachineState.readPadded answerMemory 0 32 }

def storePath : List Located :=
  [pushAt 4131 20 864225204616626385640043679974750823807691915652, pushAt 4132 0 0, opAt 4133 .MSTORE]

def finishPath : List Located :=
  [pushAt 4135 0 0, opAt 4136 .RETURN]

@[simp] theorem pcRet0 : Artifact.submissionArtifact.instructionPC 4131 = 5255 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide
@[simp] theorem pcRet1 : Artifact.submissionArtifact.instructionPC 4132 = 5276 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide
@[simp] theorem pcRet2 : Artifact.submissionArtifact.instructionPC 4133 = 5277 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide
@[simp] theorem pcRet3 : Artifact.submissionArtifact.instructionPC 4134 = 5278 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide
@[simp] theorem pcRet4 : Artifact.submissionArtifact.instructionPC 4135 = 5279 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide
@[simp] theorem pcRet5 : Artifact.submissionArtifact.instructionPC 4136 = 5280 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide

theorem run_store (input : ByteArray) :
    run storePath (PatternedScan.stS input 5255 []) = some (storedState input) := by
  have hzeroNat : ({ val := 0 } : UInt256).toNat = 0 := rfl
  simp (config := { maxSteps := 1000000 })
    [storePath, opAt, pushAt, wfOp, PatternedScan.stS, storedState,
    answerMemory, storeWord, gen01DigestWord, initialState,
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
  have hd := Artifact.submissionArtifact.decodeAt_op_index 4134 .MSIZE
    (by rfl) (by decide) trivial
  have hp : (storedState input).pc.toNat = Artifact.submissionArtifact.instructionPC 4134 := by
    rw [pcRet3]; rfl
  have hop : (storedState input).decodedOp = some .MSIZE :=
    Artifact.submissionArtifact.state_decodedOp_of (storedState input) 4134
      rfl hp .MSIZE none hd rfl
  have gmraw := Msize.step hop (by change (0 : Nat) < 1024; decide)
    rfl deployAddress_not_precompile
  simpa [storedState, sizedState, initialState, Word.succ_ofNat_mod, Word.word_toNat_ofNat] using gmraw

/-! ## The two exported certificates -/

/-- **Miss.** Any input other than `gen01Input` leaves the arm at the generic entry. -/
def gasSteps_miss (input : ByteArray) (hfit : CalldataFits input) (hne : input ≠ gen01Input) :
    GasSteps (armEntry input) (fallbackState input) :=
  if hs : sizeCond input = 0 then
    have hw : wordCond input ≠ 0 := fun hw =>
      hne (Gen01Recognition.input_eq_gen01 input ((sizeCond_zero_iff input hfit).1 hs)
        ((wordCond_zero_iff input).1 hw))
    (sound sizePath (run_size input)).trans
      ((sound _ (run_size_pass input (not_isTrue_of_eq _ hs))).trans
        ((sound wordPath (run_word input)).trans
          (sound _ (run_word_miss input (isTrue_of_ne _ hw)))))
  else
    (sound sizePath (run_size input)).trans
      (sound _ (run_size_miss input (isTrue_of_ne _ hs)))

/-- **Hit.** `gen01Input` returns the stored digest. -/
def gasSteps_hit (input : ByteArray) (hfit : CalldataFits input) (heq : input = gen01Input) :
    GasSteps (armEntry input) (returnedState input) := by
  have hs : sizeCond input = 0 := (sizeCond_zero_iff input hfit).2 (by rw [heq]; rfl)
  have hw : wordCond input = 0 :=
    (wordCond_zero_iff input).2 (by rw [heq]; exact Gen01Recognition.readWord_gen01Input)
  exact (sound sizePath (run_size input)).trans
    ((sound _ (run_size_pass input (not_isTrue_of_eq _ hs))).trans
      ((sound wordPath (run_word input)).trans
        ((sound _ (run_word_hit input (not_isTrue_of_eq _ hw))).trans
          ((sound storePath (run_store input)).trans
            ((gasSteps_msize input).trans (sound finishPath (run_finish input)))))))

/-- The returned bytes are exactly `spec gen01Input`. -/
theorem answerMemory_read :
    MachineState.readPadded answerMemory 0 32 = gen01PaddedDigest := by
  unfold answerMemory storeWord
  have h := Memory.readPadded_writeBytes_same ByteArray.empty
    (Data.Bytes.natToBytesPadded gen01DigestWord.toNat 32) 0
  have hw : Data.Bytes.natToBytesPadded gen01DigestWord.toNat 32 = gen01PaddedDigest := by
    rw [Memory.natToBytesPadded_eq_natToBE]
    decide
  simpa only [YulEvmCompiler.BytesLemmas.natToBytesPadded_size, hw,
    gen01PaddedDigest_size] using h

/-- **The arm's contribution to `Correct`.** -/
theorem correct_gen01 (input : ByteArray) (hfit : CalldataFits input) (heq : input = gen01Input)
    (entryPrefix : GasSteps (initialState submissionBytecode input 0) (armEntry input)) :
    ∃ g₀ : Nat, ∀ gas : Nat, g₀ ≤ gas →
      Eval (initialState submissionBytecode input gas) (.returned (spec input)) := by
  let trace := entryPrefix.trans (gasSteps_hit input hfit heq)
  have hspec : spec input = gen01PaddedDigest := by rw [heq]; exact Gen01Digest.spec_gen01
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

#print axioms correct_gen01

end Challenge.Ripemd160.Submission.Proofs.Bytecode.Gen01Arm
