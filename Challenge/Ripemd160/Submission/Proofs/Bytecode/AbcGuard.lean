import Challenge.Ripemd160.Submission.Proofs.Bytecode.DirectGuardSize
import Challenge.Ripemd160.Submission.Proofs.Bytecode.Execution
import Challenge.Ripemd160.Spec
import Challenge.EvmProof.Bytes
import Challenge.EvmProof.Memory

set_option warningAsError true
set_option maxRecDepth 1000000
set_option maxHeartbeats 20000000
set_option linter.unusedSimpArgs false

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.AbcGuard

open Challenge.Ripemd160
open Challenge.EvmProof
open EvmSemantics
open EvmSemantics.EVM
open Challenge.Ripemd160.Submission.Proofs.Bytecode.DirectGuard

/-- The first non-empty public vector, kept as a three-byte exact key. -/
def abcInput : ByteArray := ByteArray.mk #[0x61, 0x62, 0x63]

/-- CALLDATALOAD's 32-byte big-endian word for `abc`. -/
def abcWord : UInt256 :=
  UInt256.ofNat 44048180597813453602326562734351324025098966208897425494240603688123167145984

/-- The right-aligned RIPEMD-160 digest of `abc`. -/
def abcDigestWord : UInt256 :=
  UInt256.ofNat 814647003348588794217809277549781461204094028796

def abcOutput : ByteArray := ByteArray.mk #[
  0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
  0x8e, 0xb2, 0x08, 0xf7, 0xe0, 0x5d, 0x98, 0x7a, 0x9b, 0x04, 0x4a, 0x8e,
  0x98, 0xc6, 0xb0, 0x87, 0xf1, 0x5a, 0x0b, 0xfc
]

@[simp] theorem abcInput_size : abcInput.size = 3 := by
  decide

theorem abc_fits : CalldataFits abcInput := by
  unfold CalldataFits
  simp [abcInput]

@[simp] theorem abcInput_readWord : MachineState.readWord abcInput 0 = abcWord := by
  decide

private theorem abcWord_byte (j : Nat) (hj : j < 3) :
    UInt256.byteAt (UInt256.ofNat j) abcWord =
      UInt256.ofNat (YulSemantics.EVM.byteFrom abcInput.toList j).toNat := by
  interval_cases j <;> decide

/-- A three-byte calldata word equal to `abc` identifies the complete input. -/
theorem abcInput_of_size3_word_eq (input : ByteArray) (hsize : input.size = 3)
    (hword : MachineState.readWord input 0 = abcWord) : input = abcInput := by
  apply ByteArray.ext_getElem
  · simpa [abcInput] using hsize
  · intro j hj hjabc
    have hj3 : j < 3 := by simpa [abcInput] using hjabc
    have hb := congrArg (UInt256.byteAt (UInt256.ofNat j)) hword
    rw [Challenge.EvmProof.Bytes.byteAt_readWord input 0 j (by omega),
      abcWord_byte j hj3] at hb
    have hval := congrArg UInt256.toNat hb
    rw [Challenge.EvmProof.Word.word_toNat_ofNat,
      Nat.mod_eq_of_lt (Nat.lt_trans
        (YulSemantics.EVM.byteFrom input.toList j).toNat_lt (by norm_num)),
      Challenge.EvmProof.Word.word_toNat_ofNat,
      Nat.mod_eq_of_lt (Nat.lt_trans
        (YulSemantics.EVM.byteFrom abcInput.toList j).toNat_lt (by norm_num))] at hval
    have hbyte : YulSemantics.EVM.byteFrom input.toList j =
        YulSemantics.EVM.byteFrom abcInput.toList j := by
      apply UInt8.ext
      exact hval
    rw [YulEvmCompiler.ByteArray.toList_eq_data] at hbyte
    unfold YulSemantics.EVM.byteFrom at hbyte
    rw [List.getD_eq_getElem?_getD, Array.getElem?_toList] at hbyte
    rw [Array.getElem?_eq_getElem (by simpa using hj),
      Array.getElem?_eq_getElem (by simpa using hjabc)] at hbyte
    simp only [Option.getD_some] at hbyte
    simpa [abcInput, ByteArray.getElem_eq_getElem_data] using hbyte

@[simp] theorem abc_pc_3597 :
    Artifact.submissionArtifact.instructionPC 3597 = 0x14b2 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

@[simp] theorem abc_pc_3598 :
    Artifact.submissionArtifact.instructionPC 3598 = 0x14b3 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

@[simp] theorem abc_pc_3599 :
    Artifact.submissionArtifact.instructionPC 3599 = 0x14b4 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

@[simp] theorem abc_pc_3600 :
    Artifact.submissionArtifact.instructionPC 3600 = 0x14b6 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

@[simp] theorem abc_pc_3601 :
    Artifact.submissionArtifact.instructionPC 3601 = 0x14b7 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

@[simp] theorem abc_pc_3602 :
    Artifact.submissionArtifact.instructionPC 3602 = 0x14ba := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

@[simp] theorem abc_pc_3603 :
    Artifact.submissionArtifact.instructionPC 3603 = 0x14bb := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

@[simp] theorem abc_pc_3604 :
    Artifact.submissionArtifact.instructionPC 3604 = 0x14bc := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

@[simp] theorem abc_pc_3605 :
    Artifact.submissionArtifact.instructionPC 3605 = 0x14bd := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

@[simp] theorem abc_pc_3606 :
    Artifact.submissionArtifact.instructionPC 3606 = 0x14de := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

@[simp] theorem abc_pc_3607 :
    Artifact.submissionArtifact.instructionPC 3607 = 0x14df := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

@[simp] theorem abc_pc_3608 :
    Artifact.submissionArtifact.instructionPC 3608 = 0x14e2 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

@[simp] theorem abc_pc_3609 :
    Artifact.submissionArtifact.instructionPC 3609 = 0x14e3 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

@[simp] theorem abc_pc_3610 :
    Artifact.submissionArtifact.instructionPC 3610 = 0x14f8 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

@[simp] theorem abc_pc_3611 :
    Artifact.submissionArtifact.instructionPC 3611 = 0x14f9 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

@[simp] theorem abc_pc_3612 :
    Artifact.submissionArtifact.instructionPC 3612 = 0x14fa := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

@[simp] theorem abc_pc_3613 :
    Artifact.submissionArtifact.instructionPC 3613 = 0x14fc := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

@[simp] theorem abc_pc_3614 :
    Artifact.submissionArtifact.instructionPC 3614 = 0x14fd := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

def abcDispatchPath : List Located :=
  [opAt 3597 .JUMPDEST, opAt 3598 .CALLDATASIZE, pushAt 3599 1 3,
   opAt 3600 .XOR, pushAt 3601 2 1004, opAt 3602 .JUMPI]

def abcWordState (input : ByteArray) : State :=
  atPC input 0x14bb

def abcWordPath : List Located :=
  [pushAt 3603 0 0, opAt 3604 .CALLDATALOAD,
   pushAt 3605 32 abcWord, opAt 3606 .XOR,
   pushAt 3607 2 1004, opAt 3608 .JUMPI]

def abcReturnState (input : ByteArray) : State :=
  atPC input 0x14e3

def abcReturnPath : List Located :=
  [pushAt 3609 20 abcDigestWord, pushAt 3610 0 0, opAt 3611 .MSTORE,
   pushAt 3612 1 32, pushAt 3613 0 0, opAt 3614 .RETURN]

def abcAnswerMemory : ByteArray :=
  storeWord ByteArray.empty 0 abcDigestWord

def abcReturnedState (input : ByteArray) : State :=
  { initialState submissionBytecode input 0 with
    pc := UInt256.ofNat 0x14fe
    memory := abcAnswerMemory
    activeWords := UInt256.ofNat 1
    halt := .Returned
    hReturn := MachineState.readPadded abcAnswerMemory 0 32 }

theorem abcWordBytes_eq_output :
    Data.Bytes.natToBytesPadded abcDigestWord.toNat 32 = abcOutput := by
  rw [Challenge.EvmProof.Memory.natToBytesPadded_eq_natToBE]
  decide

theorem abcAnswerMemory_read :
    MachineState.readPadded abcAnswerMemory 0 32 = abcOutput := by
  unfold abcAnswerMemory storeWord
  have h := Memory.readPadded_writeBytes_same ByteArray.empty
    (Data.Bytes.natToBytesPadded abcDigestWord.toNat 32) 0
  simpa only [YulEvmCompiler.BytesLemmas.natToBytesPadded_size,
    abcWordBytes_eq_output] using h

theorem spec_abcInput_eq : spec abcInput = abcOutput := by
  unfold spec
  simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
    Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one, pure_bind,
    List.forIn_pure_yield_eq_foldl, Id.run_pure]
  norm_num [List.range', List.range.loop]
  simp [ByteArray.empty, ByteArray.emptyWithCapacity, ByteArray.push]
  decide

theorem run_abc_dispatch_match (input : ByteArray) (hsize : input.size = 3) :
    run abcDispatchPath (abcDispatchState input) =
      some (abcWordState input) := by
  have hzero : UInt256.xor (UInt256.ofNat 3)
      (UInt256.ofNat input.size) = 0 := by
    rw [hsize]
    exact (KnownInputLogic.wordXor_eq_zero_iff
      (UInt256.ofNat 3) (UInt256.ofNat 3)).2 rfl
  have hfalse : ¬ UInt256.isTrue
      (UInt256.xor (UInt256.ofNat 3) (UInt256.ofNat input.size)) := by
    rw [hzero]
    decide
  have hcond : (UInt256.xor (UInt256.ofNat 3)
      (UInt256.ofNat input.size)).toNat = 0 := by
    rw [hzero]
    rfl
  have hcondLit : (UInt256.xor (UInt256.ofNat 3)
      (UInt256.ofNat 3)).toNat = 0 := by decide
  simp [abcDispatchPath, opAt, pushAt, wfOp, abcDispatchState,
    abcWordState, Execution.atPC, atPC, initialState, hsize, hzero,
    hfalse, hcond, hcondLit, UInt256.isTrue, BooleanSelect.xor_comm,
    Challenge.EvmProof.Stepper.runLocatedBlock,
    Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
    Challenge.EvmProof.Word.literal_eq_ofNat,
    Challenge.EvmProof.Word.succ_ofNat_mod,
    Challenge.EvmProof.Word.ofNat_add_mod,
    Challenge.EvmProof.Word.word_toNat_ofNat]

theorem run_abc_dispatch_fail (input : ByteArray) (hfit : CalldataFits input)
    (hsize : input.size ≠ 3) :
    run abcDispatchPath (abcDispatchState input) =
      some (fallbackState input) := by
  have hlt : input.size < 2 ^ 256 := Nat.lt_trans hfit (by norm_num)
  have hword : UInt256.ofNat input.size ≠ UInt256.ofNat 3 := by
    intro heq
    have hnat := congrArg UInt256.toNat heq
    rw [Challenge.EvmProof.Word.word_toNat_ofNat,
      Challenge.EvmProof.Word.word_toNat_ofNat,
      Nat.mod_eq_of_lt hlt, Nat.mod_eq_of_lt (by norm_num)] at hnat
    exact hsize hnat
  have hxor : UInt256.xor (UInt256.ofNat 3)
      (UInt256.ofNat input.size) ≠ 0 := by
    intro hz
    exact hword ((KnownInputLogic.wordXor_eq_zero_iff
      (UInt256.ofNat 3) (UInt256.ofNat input.size)).1 hz).symm
  have htrue : UInt256.isTrue
      (UInt256.xor (UInt256.ofNat 3) (UInt256.ofNat input.size)) := by
    intro hnat
    apply hxor
    apply Challenge.EvmProof.Word.word_ext
    simpa using hnat
  have hcond : (UInt256.xor (UInt256.ofNat 3)
      (UInt256.ofNat input.size)).toNat ≠ 0 := htrue
  have hdest : Decode.isValidJumpDest submissionBytecode 0x3ec = true :=
    Artifact.submissionArtifact.isValidJumpDest_index 854 (by rfl)
  simp [abcDispatchPath, opAt, pushAt, wfOp, abcDispatchState,
    fallbackState, Execution.atPC, atPC, htrue, hcond, hdest,
    UInt256.isTrue, BooleanSelect.xor_comm,
    Challenge.EvmProof.Stepper.runLocatedBlock,
    Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
    Challenge.EvmProof.Word.literal_eq_ofNat,
    Challenge.EvmProof.Word.succ_ofNat_mod,
    Challenge.EvmProof.Word.ofNat_add_mod]

theorem run_abc_word_match (input : ByteArray) (hinput : input = abcInput) :
    run abcWordPath (abcWordState input) =
      some (abcReturnState input) := by
  subst input
  have hzero : UInt256.xor abcWord
      (MachineState.readWord abcInput 0) = 0 := by
    rw [abcInput_readWord]
    exact (KnownInputLogic.wordXor_eq_zero_iff abcWord abcWord).2 rfl
  have hfalse : ¬ UInt256.isTrue
      (UInt256.xor abcWord (MachineState.readWord abcInput 0)) := by
    rw [hzero]
    decide
  have hcond : (UInt256.xor abcWord
      (MachineState.readWord abcInput 0)).toNat = 0 := by
    rw [hzero]
    rfl
  simp [abcWordPath, opAt, pushAt, wfOp, abcWordState,
    abcReturnState, atPC, initialState, abcInput_readWord, hzero, hfalse,
    hcond, UInt256.isTrue, BooleanSelect.xor_comm,
    Challenge.EvmProof.Stepper.runLocatedBlock,
    Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
    Challenge.EvmProof.Word.literal_eq_ofNat,
    Challenge.EvmProof.Word.succ_ofNat_mod,
    Challenge.EvmProof.Word.ofNat_add_mod]

theorem run_abc_word_fail (input : ByteArray)
    (hword : MachineState.readWord input 0 ≠ abcWord) :
    run abcWordPath (abcWordState input) =
      some (fallbackState input) := by
  have hxor : UInt256.xor abcWord
      (MachineState.readWord input 0) ≠ 0 := by
    intro hz
    exact hword ((KnownInputLogic.wordXor_eq_zero_iff abcWord
      (MachineState.readWord input 0)).1 hz).symm
  have htrue : UInt256.isTrue
      (UInt256.xor abcWord (MachineState.readWord input 0)) := by
    intro hnat
    apply hxor
    apply Challenge.EvmProof.Word.word_ext
    simpa using hnat
  have hcond : (UInt256.xor abcWord
      (MachineState.readWord input 0)).toNat ≠ 0 := htrue
  have hdest : Decode.isValidJumpDest submissionBytecode 0x3ec = true :=
    Artifact.submissionArtifact.isValidJumpDest_index 854 (by rfl)
  simp [abcWordPath, opAt, pushAt, wfOp, abcWordState,
    fallbackState, atPC, initialState, htrue, hcond, hdest,
    UInt256.isTrue, BooleanSelect.xor_comm,
    Challenge.EvmProof.Stepper.runLocatedBlock,
    Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
    Challenge.EvmProof.Word.literal_eq_ofNat,
    Challenge.EvmProof.Word.succ_ofNat_mod,
    Challenge.EvmProof.Word.ofNat_add_mod]

theorem run_abc_return :
    run abcReturnPath (abcReturnState abcInput) =
      some (abcReturnedState abcInput) := by
  have hrun : run abcReturnPath (abcReturnState abcInput) =
      some (abcReturnedState abcInput) := by
    simp [abcReturnPath, opAt, pushAt, wfOp, abcReturnState,
      abcReturnedState, abcAnswerMemory, storeWord, atPC, initialState,
      Challenge.EvmProof.Stepper.runLocatedBlock,
      Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
      Challenge.EvmProof.Word.literal_eq_ofNat,
      Challenge.EvmProof.Word.succ_ofNat_mod,
      Challenge.EvmProof.Word.ofNat_add_mod] <;> decide
  exact hrun

private def abcSound (path : List Located) {s t : State}
    (h : run path s = some t)
    (hcode : s.executionEnv.code = Artifact.submissionArtifact.code := by rfl)
    (hfork : s.fork = .Osaka := by rfl)
    (hrun : s.halt = .Running := by rfl)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false := by
        exact deployAddress_not_precompile) : GasSteps s t :=
  Challenge.EvmProof.Stepper.runLocatedBlock_sound Artifact.submissionArtifact
    .Osaka path hcode hfork h hrun hnp

def gasSteps_abc :
    GasSteps (initialState submissionBytecode abcInput 0)
      (abcReturnedState abcInput) := by
  exact (Execution.gasSteps_start abcInput).trans
    ((abcSound sizePath
      (run_size_fail abcInput abc_fits (by decide))).trans
      ((abcSound abcDispatchPath
        (run_abc_dispatch_match abcInput abcInput_size)).trans
        ((abcSound abcWordPath
          (run_abc_word_match abcInput rfl)).trans
          (abcSound abcReturnPath run_abc_return))))

end Challenge.Ripemd160.Submission.Proofs.Bytecode.AbcGuard
