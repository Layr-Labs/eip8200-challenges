import Challenge.Ripemd160.Submission.Proofs.Bytecode.PcEncoding
import Challenge.Ripemd160.Submission.Proofs.Bytecode.Padding
import Challenge.Ripemd160.Submission.Proofs.Bytecode.StackTail
import Challenge.Ripemd160.Submission.Proofs.Bytecode.RawExpressionAC
import Challenge.Ripemd160.Submission.Proofs.Bytecode.Trace
import Challenge.Ripemd160.Submission.Proofs.Bytecode.Main
import Challenge.Ripemd160.Submission.Proofs.Bytecode.StaggerPersistentStart
import Challenge.Ripemd160.Submission.Proofs.Bytecode.ColdGuardFixup
import Challenge.Ripemd160.Submission.Proofs.Bytecode.DataStepper
import Challenge.Ripemd160.Submission.Proofs.Bytecode.Msize
import Challenge.Ripemd160.Submission.Proofs.Bytecode.PadLimitArithmetic
set_option warningAsError true
set_option maxRecDepth 20000
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
/-!
# Direct execution of the RIPEMD-160 padding function (setup, guard, sentinel, footer loop and exit)

The fixed setup and the eight-iteration little-endian footer loop are exposed
as located paths.  The resulting state is shared by correctness and exact gas
accounting.
-/

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.PaddingTrace

open EvmSemantics
open EvmSemantics.EVM

@[simp] private theorem literalZeroNat : (⟨0⟩ : UInt256).toNat = 0 := rfl

private def wfOp {op : Operation}
    (hopcode : Decode.opcodeOf (Challenge.EvmProof.PcEncoding.opByte op) = some op)
    (hplain : YulEvmCompiler.plainOp op)
    (havailable : op.availableInFork .Osaka = true) :
    Challenge.EvmProof.DataStepper.WellFormed .Osaka (.op op) :=
  ⟨hopcode, hplain, havailable⟩

/-- The padding code is entered directly after the initial stores and falls
through into the driver entry, so no return address is pushed. -/
def padEntry (input : ByteArray) : State :=
  { Main.initializedState input with
    pc := UInt256.ofNat 309
    stack := [DenseScheduleTemplate.mask8, DenseScheduleTemplate.mask16] }

@[simp] private theorem padEntry_halt (input : ByteArray) :
    (padEntry input).halt = .Running := by rfl

@[simp] private theorem padEntry_fork (input : ByteArray) :
    (padEntry input).fork = .Osaka := by rfl

@[simp] private theorem padEntry_code (input : ByteArray) :
    (padEntry input).executionEnv.code = submissionBytecode := by rfl

@[simp] private theorem padEntry_calldata (input : ByteArray) :
    (padEntry input).executionEnv.calldata = input := by rfl

@[simp] private theorem initializedPC764 :
    Artifact.instructionPC 155 = 246 := by change Artifact.submissionArtifact.instructionPC 155 = 246; rw [Challenge.Ripemd160.Submission.Proofs.Bytecode.ArtifactByteLength.instructionPC_eq_byteLength]; rfl

/-! Instruction PCs of the sentinel/footer setup (99..110), the 192-stub jump (114..115), the exit block at 198
(116..123) and the footer loop tail (3412..3416) in this layout. -/

@[simp] private theorem padPc99 :
    Artifact.submissionArtifact.instructionPC 99 = 172 := by
  rw [Challenge.Ripemd160.Submission.Proofs.Bytecode.ArtifactByteLength.instructionPC_eq_byteLength]; rfl

@[simp] private theorem padPci99 :
    Artifact.instructionPC 99 = 172 := by
  change Artifact.submissionArtifact.instructionPC 99 = 172
  rw [Challenge.Ripemd160.Submission.Proofs.Bytecode.ArtifactByteLength.instructionPC_eq_byteLength]; rfl

@[simp] private theorem padPc108 :
    Artifact.submissionArtifact.instructionPC 108 = 187 := by
  rw [Challenge.Ripemd160.Submission.Proofs.Bytecode.ArtifactByteLength.instructionPC_eq_byteLength]; rfl

@[simp] private theorem padPci108 :
    Artifact.instructionPC 108 = 187 := by
  change Artifact.submissionArtifact.instructionPC 108 = 187
  rw [Challenge.Ripemd160.Submission.Proofs.Bytecode.ArtifactByteLength.instructionPC_eq_byteLength]; rfl

@[simp] private theorem padPc109 :
    Artifact.submissionArtifact.instructionPC 109 = 189 := by
  rw [Challenge.Ripemd160.Submission.Proofs.Bytecode.ArtifactByteLength.instructionPC_eq_byteLength]; rfl

@[simp] private theorem padPci109 :
    Artifact.instructionPC 109 = 189 := by
  change Artifact.submissionArtifact.instructionPC 109 = 189
  rw [Challenge.Ripemd160.Submission.Proofs.Bytecode.ArtifactByteLength.instructionPC_eq_byteLength]; rfl

@[simp] private theorem padPc110 :
    Artifact.submissionArtifact.instructionPC 110 = 190 := by
  rw [Challenge.Ripemd160.Submission.Proofs.Bytecode.ArtifactByteLength.instructionPC_eq_byteLength]; rfl

@[simp] private theorem padPci110 :
    Artifact.instructionPC 110 = 190 := by
  change Artifact.submissionArtifact.instructionPC 110 = 190
  rw [Challenge.Ripemd160.Submission.Proofs.Bytecode.ArtifactByteLength.instructionPC_eq_byteLength]; rfl

@[simp] private theorem padPc114 :
    Artifact.submissionArtifact.instructionPC 114 = 195 := by
  rw [Challenge.Ripemd160.Submission.Proofs.Bytecode.ArtifactByteLength.instructionPC_eq_byteLength]; rfl

@[simp] private theorem padPci114 :
    Artifact.instructionPC 114 = 195 := by
  change Artifact.submissionArtifact.instructionPC 114 = 195
  rw [Challenge.Ripemd160.Submission.Proofs.Bytecode.ArtifactByteLength.instructionPC_eq_byteLength]; rfl

@[simp] private theorem padPc115 :
    Artifact.submissionArtifact.instructionPC 115 = 197 := by
  rw [Challenge.Ripemd160.Submission.Proofs.Bytecode.ArtifactByteLength.instructionPC_eq_byteLength]; rfl

@[simp] private theorem padPci115 :
    Artifact.instructionPC 115 = 197 := by
  change Artifact.submissionArtifact.instructionPC 115 = 197
  rw [Challenge.Ripemd160.Submission.Proofs.Bytecode.ArtifactByteLength.instructionPC_eq_byteLength]; rfl

@[simp] private theorem padPc116 :
    Artifact.submissionArtifact.instructionPC 116 = 198 := by
  rw [Challenge.Ripemd160.Submission.Proofs.Bytecode.ArtifactByteLength.instructionPC_eq_byteLength]; rfl

@[simp] private theorem padPci116 :
    Artifact.instructionPC 116 = 198 := by
  change Artifact.submissionArtifact.instructionPC 116 = 198
  rw [Challenge.Ripemd160.Submission.Proofs.Bytecode.ArtifactByteLength.instructionPC_eq_byteLength]; rfl

@[simp] private theorem padPc117 :
    Artifact.submissionArtifact.instructionPC 117 = 199 := by
  rw [Challenge.Ripemd160.Submission.Proofs.Bytecode.ArtifactByteLength.instructionPC_eq_byteLength]; rfl

@[simp] private theorem padPci117 :
    Artifact.instructionPC 117 = 199 := by
  change Artifact.submissionArtifact.instructionPC 117 = 199
  rw [Challenge.Ripemd160.Submission.Proofs.Bytecode.ArtifactByteLength.instructionPC_eq_byteLength]; rfl

@[simp] private theorem padPc118 :
    Artifact.submissionArtifact.instructionPC 118 = 201 := by
  rw [Challenge.Ripemd160.Submission.Proofs.Bytecode.ArtifactByteLength.instructionPC_eq_byteLength]; rfl

@[simp] private theorem padPci118 :
    Artifact.instructionPC 118 = 201 := by
  change Artifact.submissionArtifact.instructionPC 118 = 201
  rw [Challenge.Ripemd160.Submission.Proofs.Bytecode.ArtifactByteLength.instructionPC_eq_byteLength]; rfl

@[simp] private theorem padPc119 :
    Artifact.submissionArtifact.instructionPC 119 = 202 := by
  rw [Challenge.Ripemd160.Submission.Proofs.Bytecode.ArtifactByteLength.instructionPC_eq_byteLength]; rfl

@[simp] private theorem padPci119 :
    Artifact.instructionPC 119 = 202 := by
  change Artifact.submissionArtifact.instructionPC 119 = 202
  rw [Challenge.Ripemd160.Submission.Proofs.Bytecode.ArtifactByteLength.instructionPC_eq_byteLength]; rfl

@[simp] private theorem padPc120 :
    Artifact.submissionArtifact.instructionPC 120 = 203 := by
  rw [Challenge.Ripemd160.Submission.Proofs.Bytecode.ArtifactByteLength.instructionPC_eq_byteLength]; rfl

@[simp] private theorem padPci120 :
    Artifact.instructionPC 120 = 203 := by
  change Artifact.submissionArtifact.instructionPC 120 = 203
  rw [Challenge.Ripemd160.Submission.Proofs.Bytecode.ArtifactByteLength.instructionPC_eq_byteLength]; rfl

@[simp] private theorem padPc121 :
    Artifact.submissionArtifact.instructionPC 121 = 204 := by
  rw [Challenge.Ripemd160.Submission.Proofs.Bytecode.ArtifactByteLength.instructionPC_eq_byteLength]; rfl

@[simp] private theorem padPci121 :
    Artifact.instructionPC 121 = 204 := by
  change Artifact.submissionArtifact.instructionPC 121 = 204
  rw [Challenge.Ripemd160.Submission.Proofs.Bytecode.ArtifactByteLength.instructionPC_eq_byteLength]; rfl

@[simp] private theorem padPc122 :
    Artifact.submissionArtifact.instructionPC 122 = 205 := by
  rw [Challenge.Ripemd160.Submission.Proofs.Bytecode.ArtifactByteLength.instructionPC_eq_byteLength]; rfl

@[simp] private theorem padPci122 :
    Artifact.instructionPC 122 = 205 := by
  change Artifact.submissionArtifact.instructionPC 122 = 205
  rw [Challenge.Ripemd160.Submission.Proofs.Bytecode.ArtifactByteLength.instructionPC_eq_byteLength]; rfl

@[simp] private theorem padPc123 :
    Artifact.submissionArtifact.instructionPC 123 = 206 := by
  rw [Challenge.Ripemd160.Submission.Proofs.Bytecode.ArtifactByteLength.instructionPC_eq_byteLength]; rfl

@[simp] private theorem padPci123 :
    Artifact.instructionPC 123 = 206 := by
  change Artifact.submissionArtifact.instructionPC 123 = 206
  rw [Challenge.Ripemd160.Submission.Proofs.Bytecode.ArtifactByteLength.instructionPC_eq_byteLength]; rfl

set_option maxRecDepth 100000 in
@[simp] private theorem padPc3607 :
    Artifact.submissionArtifact.instructionPC 3405 = 4557 := by
  rw [Challenge.Ripemd160.Submission.Proofs.Bytecode.ArtifactByteLength.instructionPC_eq_byteLength]; rfl

set_option maxRecDepth 100000 in
@[simp] private theorem padPci3607 :
    Artifact.instructionPC 3405 = 4557 := by
  change Artifact.submissionArtifact.instructionPC 3405 = 4557
  rw [Challenge.Ripemd160.Submission.Proofs.Bytecode.ArtifactByteLength.instructionPC_eq_byteLength]; rfl

set_option maxRecDepth 100000 in
@[simp] private theorem padPc3608 :
    Artifact.submissionArtifact.instructionPC 3406 = 4558 := by
  rw [Challenge.Ripemd160.Submission.Proofs.Bytecode.ArtifactByteLength.instructionPC_eq_byteLength]; rfl

set_option maxRecDepth 100000 in
@[simp] private theorem padPci3608 :
    Artifact.instructionPC 3406 = 4558 := by
  change Artifact.submissionArtifact.instructionPC 3406 = 4558
  rw [Challenge.Ripemd160.Submission.Proofs.Bytecode.ArtifactByteLength.instructionPC_eq_byteLength]; rfl

set_option maxRecDepth 100000 in
@[simp] private theorem padPc3609 :
    Artifact.submissionArtifact.instructionPC 3407 = 4559 := by
  rw [Challenge.Ripemd160.Submission.Proofs.Bytecode.ArtifactByteLength.instructionPC_eq_byteLength]; rfl

set_option maxRecDepth 100000 in
@[simp] private theorem padPci3609 :
    Artifact.instructionPC 3407 = 4559 := by
  change Artifact.submissionArtifact.instructionPC 3407 = 4559
  rw [Challenge.Ripemd160.Submission.Proofs.Bytecode.ArtifactByteLength.instructionPC_eq_byteLength]; rfl

set_option maxRecDepth 100000 in
@[simp] private theorem padPc3610 :
    Artifact.submissionArtifact.instructionPC 3408 = 4560 := by
  rw [Challenge.Ripemd160.Submission.Proofs.Bytecode.ArtifactByteLength.instructionPC_eq_byteLength]; rfl

set_option maxRecDepth 100000 in
@[simp] private theorem padPci3610 :
    Artifact.instructionPC 3408 = 4560 := by
  change Artifact.submissionArtifact.instructionPC 3408 = 4560
  rw [Challenge.Ripemd160.Submission.Proofs.Bytecode.ArtifactByteLength.instructionPC_eq_byteLength]; rfl

set_option maxRecDepth 100000 in
@[simp] private theorem padPc3611 :
    Artifact.submissionArtifact.instructionPC 3409 = 4561 := by
  rw [Challenge.Ripemd160.Submission.Proofs.Bytecode.ArtifactByteLength.instructionPC_eq_byteLength]; rfl

set_option maxRecDepth 100000 in
@[simp] private theorem padPci3611 :
    Artifact.instructionPC 3409 = 4561 := by
  change Artifact.submissionArtifact.instructionPC 3409 = 4561
  rw [Challenge.Ripemd160.Submission.Proofs.Bytecode.ArtifactByteLength.instructionPC_eq_byteLength]; rfl

set_option maxRecDepth 100000 in
@[simp] private theorem padPc3612 :
    Artifact.submissionArtifact.instructionPC 3410 = 4562 := by
  rw [Challenge.Ripemd160.Submission.Proofs.Bytecode.ArtifactByteLength.instructionPC_eq_byteLength]; rfl

set_option maxRecDepth 100000 in
@[simp] private theorem padPci3612 :
    Artifact.instructionPC 3410 = 4562 := by
  change Artifact.submissionArtifact.instructionPC 3410 = 4562
  rw [Challenge.Ripemd160.Submission.Proofs.Bytecode.ArtifactByteLength.instructionPC_eq_byteLength]; rfl

set_option maxRecDepth 100000 in
@[simp] private theorem padPc3613 :
    Artifact.submissionArtifact.instructionPC 3411 = 4564 := by
  rw [Challenge.Ripemd160.Submission.Proofs.Bytecode.ArtifactByteLength.instructionPC_eq_byteLength]; rfl

set_option maxRecDepth 100000 in
@[simp] private theorem padPci3613 :
    Artifact.instructionPC 3411 = 4564 := by
  change Artifact.submissionArtifact.instructionPC 3411 = 4564
  rw [Challenge.Ripemd160.Submission.Proofs.Bytecode.ArtifactByteLength.instructionPC_eq_byteLength]; rfl

@[simp] private theorem initializedCalldata (input : ByteArray) :
    (Main.initializedState input).executionEnv.calldata = input := by rfl

def enterPath : List
    (Challenge.EvmProof.DataStepper.Located Artifact.submissionArtifact .Osaka) :=
  Artifact.padEnterPath

private theorem mask16_literal :
    UInt256.ofNat
        1766820105243087041267848467410591083712559083657179364930612997358944255 =
      DenseScheduleTemplate.mask16 := by decide

private theorem mask8_literal :
    UInt256.ofNat 450552876409790643671482431940419874915447411150352389258589821042463539455 = DenseScheduleTemplate.mask8 := by decide

set_option maxHeartbeats 400000 in
/-- The hash entry computes the two byte-swap masks once; they stay below the limit for the
whole hash. -/
theorem run_enter (input : ByteArray) :
    Challenge.EvmProof.DataStepper.runLocatedBlock enterPath
      (Main.initializedState input) = some (padEntry input) := by
  have hzero : ({val := 0} : UInt256) = UInt256.ofNat 0 := rfl
  have p246 : Artifact.submissionArtifact.instructionPC 155 = 246 := by
    rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl
  have p277 : Artifact.submissionArtifact.instructionPC 156 = 277 := by
    rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl
  simp [enterPath, Artifact.padEnterPath, Challenge.EvmProof.DataStepper.runLocatedBlock,
    Challenge.EvmProof.DataStepper.runLocated, Challenge.EvmProof.DataStepper.runInstr,
    padEntry, Main.initializedState, Execution.mainStart, Execution.atPC, hzero,
    p246, p277, initialState]
  exact ⟨mask8_literal, mask16_literal⟩

def gasSteps_enterPad (input : ByteArray) :
    Challenge.EvmProof.GasSteps (Main.initializedState input) (padEntry input) := by
  apply Challenge.EvmProof.DataStepper.runLocatedBlock_sound
    Artifact.submissionArtifact .Osaka enterPath
  · rfl
  · rfl
  · exact run_enter input
  · rfl
  · exact deployAddress_not_precompile

/-- Before the calldata copy (`CALLDATASIZE PUSH0 PUSH2 0x420 CALLDATACOPY CALLDATASIZE PUSH2 0x420`):
afterwards the input sits at memory 1056 with the zero offset 1056 and the calldata size (the
fast-entry continuation) on the stack. -/
def padLengthReady (input : ByteArray) : State :=
  { padEntry input with pc := UInt256.ofNat 309 }

/-- The state right after the copy. -/
def padCopyDone (input : ByteArray) : State :=
  { padLengthReady input with
    pc := UInt256.ofNat 319
    stack := [UInt256.ofNat 1056, UInt256.ofNat input.size, DenseScheduleTemplate.mask8, DenseScheduleTemplate.mask16]
    memory := MachineState.writeBytes (padLengthReady input).memory
      (MachineState.readPadded input 0 input.size) Padding.messageOffset
    activeWords := (padLengthReady input).activeWordsAfterUInt256
      Padding.messageOffset input.size }

@[simp] private theorem padLengthReady_halt (input : ByteArray) :
    (padLengthReady input).halt = .Running := by rfl

@[simp] private theorem padLengthReady_fork (input : ByteArray) :
    (padLengthReady input).fork = .Osaka := by rfl

@[simp] private theorem padLengthReady_code (input : ByteArray) :
    (padLengthReady input).executionEnv.code = submissionBytecode := by rfl

@[simp] private theorem padLengthReady_calldata (input : ByteArray) :
    (padLengthReady input).executionEnv.calldata = input := by rfl

@[simp] private theorem padLengthReady_stack (input : ByteArray) :
    (padLengthReady input).stack = [DenseScheduleTemplate.mask8, DenseScheduleTemplate.mask16] := by
  rfl

/-- The fast-entry continuation pushed after the copy: the calldata size, which is the entry of
the next phase (64 pad-only block, 128 and 192 stubs) for the fast-entry lengths. -/
def copiedLimit (input : ByteArray) : UInt256 := UInt256.ofNat input.size

/-- The active size right after the copy: `1056 + ceil32 size`. -/
def copiedMsize (input : ByteArray) : UInt256 :=
  UInt256.ofNat (32 * (padCopyDone input).activeWords.toNat)

theorem copiedMsize_aligned (input : ByteArray) (hfit : CalldataFits input)
    (hz : input.size % 32 = 0) (hpos : 0 < input.size) :
    copiedMsize input = UInt256.ofNat (1056 + input.size) := by
  have hsize : input.size < 2 ^ 64 := hfit
  have haw : (padCopyDone input).activeWords.toNat = 33 + input.size / 32 := by
    change (UInt256.ofNat (MachineState.activeWordsAfter
      (padLengthReady input).activeWords.toNat Padding.messageOffset input.size)).toNat = _
    have h0 : (padLengthReady input).activeWords.toNat = 0 := by rfl
    rw [h0]
    unfold MachineState.activeWordsAfter
    rw [if_neg (by omega)]
    dsimp only
    unfold Padding.messageOffset
    have hv : Nat.max 0 ((1056 + input.size - 1) / 32 + 1) = 33 + input.size / 32 := by
      change max 0 ((1056 + input.size - 1) / 32 + 1) = _
      rw [Nat.max_eq_right (Nat.zero_le _)]
      omega
    rw [hv, Challenge.EvmProof.Word.word_toNat_ofNat]
    have h2 : (2:Nat)^64 < 2^256 := by decide
    exact Nat.mod_eq_of_lt (by omega)
  unfold copiedMsize
  rw [haw]
  congr 1
  omega

def bitLengthWord (input : ByteArray) : UInt256 :=
  UInt256.shiftLeft (UInt256.ofNat input.size) (UInt256.ofNat 3)

def lengthOffsetWord (input : ByteArray) : UInt256 :=
  PadLimitArithmetic.coldRounded (UInt256.ofNat input.size) + UInt256.ofNat 89

/-- The persistent block-loop frame at hash entry: the initial chaining words and the six
resident round constants above the zero offset and the padded limit. -/
def initialFrame (input : ByteArray) : List UInt256 :=
  StaggerPersistentFrame.frame StackRunBridge.initialHashState (UInt256.ofNat 1056)
    (copiedLimit input) [DenseScheduleTemplate.mask8, DenseScheduleTemplate.mask16]

@[simp] theorem initialFrame_length (input : ByteArray) : (initialFrame input).length = 15 := by
  simp [initialFrame, StaggerPersistentFrame.frame]

/-- The frame of the cold padding code: the cold block installed the output entry 9667 in slot 12. -/
def padFrame (_input : ByteArray) : List UInt256 :=
  StaggerPersistentFrame.frame StackRunBridge.initialHashState (UInt256.ofNat 1056)
    (UInt256.ofNat 9667) [DenseScheduleTemplate.mask8, DenseScheduleTemplate.mask16]

@[simp] theorem padFrame_length (input : ByteArray) : (padFrame input).length = 15 := by
  simp [padFrame, StaggerPersistentFrame.frame]

/-- The frame the padding code leaves at the block-loop head: the generic continuation 48 (the
last-block test) replaces the output entry in slot 12. -/
def glFrame : List UInt256 :=
  StaggerPersistentFrame.frame StackRunBridge.initialHashState (UInt256.ofNat 1056)
    (UInt256.ofNat 48) [DenseScheduleTemplate.mask8, DenseScheduleTemplate.mask16]

@[simp] theorem glFrame_length : glFrame.length = 15 := by
  simp [glFrame, StaggerPersistentFrame.frame]

def padCopied (input : ByteArray) : State := padCopyDone input

/-- State after the eleven frame pushes. -/
def padFramed (input : ByteArray) : State :=
  { padCopied input with
    pc := UInt256.ofNat 447
    stack := initialFrame input }

/-- Fast-entry input (64, 128 or 192 bytes): the padding code falls straight into the block
loop with only the calldata copy in memory. -/
def padSkip (input : ByteArray) : State :=
  { padCopied input with
    pc := UInt256.ofNat 461
    stack := initialFrame input }

/-- Partial last block: the clean state at the sentinel store 166 (the base of the 32-byte block
run, which writes its two scratch bytes on the way). -/
def padGuardMiss (input : ByteArray) : State :=
  { padCopied input with
    pc := UInt256.ofNat 166
    stack := padFrame input }

/-- The state the 32-byte block leaves at the sentinel store 166: scratch bytes 165 and 188 are
still written (nothing undoes them; they lie outside the message and the block loop's zero band). -/
def padDirty (input : ByteArray) : State :=
  { padGuardMiss input with
    memory := ColdGuardFixup.wMemory (padGuardMiss input).memory
      ColdGuardFixup.dirtyB ColdGuardFixup.dirtyC }

def padSentinel (input : ByteArray) : State :=
  { padDirty input with
    pc := UInt256.ofNat 172
    stack := padFrame input
    memory := MachineState.writeBytes (padDirty input).memory
      (ByteArray.mk #[0x80]) (Padding.messageOffset + input.size)
    activeWords := (padDirty input).activeWordsAfterUInt256
      (Padding.messageOffset + input.size) 1 }

@[simp] private theorem padCopied_halt (input : ByteArray) :
    (padCopied input).halt = .Running := by rfl

@[simp] private theorem padCopied_pcToNat (input : ByteArray) :
    (padCopied input).pc.toNat = 319 := by rfl

@[simp] private theorem padCopied_pc (input : ByteArray) :
    (padCopied input).pc = UInt256.ofNat 319 := by rfl

@[simp] private theorem padCopied_stack (input : ByteArray) :
    (padCopied input).stack =
      [UInt256.ofNat 1056, copiedLimit input, DenseScheduleTemplate.mask8, DenseScheduleTemplate.mask16] := by
  rfl

@[simp] theorem padCopied_calldata (input : ByteArray) :
    (padCopied input).executionEnv.calldata = input := by rfl

@[simp] theorem padCopied_code (input : ByteArray) :
    (padCopied input).executionEnv.code = submissionBytecode := by rfl

@[simp] private theorem padFramed_halt (input : ByteArray) :
    (padFramed input).halt = .Running := by rfl

@[simp] private theorem padFramed_pc (input : ByteArray) :
    (padFramed input).pc = UInt256.ofNat 447 := by rfl

@[simp] private theorem padFramed_code (input : ByteArray) :
    (padFramed input).executionEnv.code = submissionBytecode := by rfl

@[simp] private theorem padFramed_calldata (input : ByteArray) :
    (padFramed input).executionEnv.calldata = input := by rfl

@[simp] private theorem padGuardMiss_halt (input : ByteArray) :
    (padGuardMiss input).halt = .Running := by rfl

@[simp] private theorem padGuardMiss_pc (input : ByteArray) :
    (padGuardMiss input).pc = UInt256.ofNat 166 := by rfl

@[simp] private theorem padGuardMiss_code (input : ByteArray) :
    (padGuardMiss input).executionEnv.code = submissionBytecode := by rfl

@[simp] private theorem padGuardMiss_calldata (input : ByteArray) :
    (padGuardMiss input).executionEnv.calldata = input := by rfl

@[simp] private theorem padDirty_halt (input : ByteArray) :
    (padDirty input).halt = .Running := by rfl

@[simp] private theorem padDirty_pc (input : ByteArray) :
    (padDirty input).pc = UInt256.ofNat 166 := by rfl

@[simp] private theorem padDirty_code (input : ByteArray) :
    (padDirty input).executionEnv.code = submissionBytecode := by rfl

@[simp] private theorem padDirty_calldata (input : ByteArray) :
    (padDirty input).executionEnv.calldata = input := by rfl

@[simp] private theorem padSentinel_halt (input : ByteArray) :
    (padSentinel input).halt = .Running := by rfl

@[simp] private theorem padSentinel_pcToNat (input : ByteArray) :
    (padSentinel input).pc.toNat = 172 := by rfl

@[simp] private theorem padSentinel_pc (input : ByteArray) :
    (padSentinel input).pc = UInt256.ofNat 172 := by rfl

@[simp] private theorem padSentinel_pcSucc (input : ByteArray) :
    (padSentinel input).pc.succ = UInt256.ofNat 173 := by
  rw [padSentinel_pc, Challenge.EvmProof.Word.succ_ofNat (by norm_num)]

@[simp] private theorem padSentinel_stack (input : ByteArray) :
    (padSentinel input).stack = padFrame input := by
  rfl

@[simp] private theorem padSentinel_calldata (input : ByteArray) :
    (padSentinel input).executionEnv.calldata = input := by rfl

def lengthCopyPath : List
    (Challenge.EvmProof.DataStepper.Located Artifact.submissionArtifact .Osaka) :=
  Artifact.padCopyPath
def guardPath : List
    (Challenge.EvmProof.DataStepper.Located Artifact.submissionArtifact .Osaka) :=
  Artifact.padGuardPath
def lengthSentinelPath : List
    (Challenge.EvmProof.DataStepper.Located Artifact.submissionArtifact .Osaka) :=
  Artifact.padSentinelPath
def lengthFooterSetupPath : List
    (Challenge.EvmProof.DataStepper.Located Artifact.submissionArtifact .Osaka) :=
  Artifact.padFooterSetupPath
def lengthSentinelAddressPath := lengthSentinelPath.take 4
def lengthSentinelStorePath := lengthSentinelPath.drop 4

def padSentinelAddressReady (input : ByteArray) : State :=
  { padDirty input with
    pc := UInt256.ofNat 171
    stack := [UInt256.ofNat Padding.messageOffset + UInt256.ofNat input.size,
      UInt256.ofNat 128] ++ padFrame input }

def padSentinelStored (input : ByteArray) : State :=
  { padSentinelAddressReady input with
    pc := UInt256.ofNat 172
    stack := padFrame input
    memory := MachineState.writeBytes (padSentinelAddressReady input).memory
      (ByteArray.mk #[0x80])
      (UInt256.ofNat Padding.messageOffset + UInt256.ofNat input.size).toNat
    activeWords := (padSentinelAddressReady input).activeWordsAfterUInt256
      (UInt256.ofNat Padding.messageOffset + UInt256.ofNat input.size).toNat 1 }

@[simp] private theorem padSentinelAddressReady_halt (input : ByteArray) :
    (padSentinelAddressReady input).halt = .Running := by rfl

@[simp] private theorem padSentinelAddressReady_pc (input : ByteArray) :
    (padSentinelAddressReady input).pc = UInt256.ofNat 171 := by rfl

@[simp] private theorem padSentinelAddressReady_stack (input : ByteArray) :
    (padSentinelAddressReady input).stack =
      [UInt256.ofNat Padding.messageOffset + UInt256.ofNat input.size,
        UInt256.ofNat 128] ++ padFrame input := by rfl

@[simp] private theorem padSentinelAddressReady_memory (input : ByteArray) :
    (padSentinelAddressReady input).memory = (padDirty input).memory := by rfl

@[simp] private theorem padSentinelAddressReady_activeWords (input : ByteArray) :
    (padSentinelAddressReady input).activeWords = (padDirty input).activeWords := by rfl

set_option maxHeartbeats 200000 in
@[simp] private theorem padLengthReady_pc (input : ByteArray) :
    (padLengthReady input).pc = UInt256.ofNat 309 := by rfl

theorem run_lengthCopy (input : ByteArray) (hfit : CalldataFits input) :
    Challenge.EvmProof.DataStepper.runLocatedBlock lengthCopyPath
      (padLengthReady input) = some (padCopyDone input) := by
  have hsize : input.size < 2 ^ 256 := Nat.lt_trans hfit (by norm_num)
  have hsizeWord : (UInt256.ofNat input.size).toNat = input.size := by
    rw [Challenge.EvmProof.Word.word_toNat_ofNat, Nat.mod_eq_of_lt hsize]
  have hzero : (⟨0⟩ : UInt256) = UInt256.ofNat 0 := by rfl
  have hpc := padLengthReady_pc input
  have hstack := padLengthReady_stack input
  have hdata := padLengthReady_calldata input
  have hrun := padLengthReady_halt input
  unfold padCopyDone
  generalize padLengthReady input = s at hpc hstack hdata hrun ⊢
  simp [lengthCopyPath, Artifact.padCopyPath,
    Challenge.EvmProof.DataStepper.runLocatedBlock,
    Challenge.EvmProof.DataStepper.runLocated, Challenge.EvmProof.DataStepper.runInstr,
    State.activeWordsAfterUInt256, Padding.messageOffset,
    hpc, hstack, hdata, hrun, hsizeWord, hzero]

/-- Initialize the complete resident frame before the alignment guard. -/
def gasSteps_push (input : ByteArray) :
    Challenge.EvmProof.GasSteps (padCopied input) (padFramed input) := by
  have g := StaggerPersistentStart.gasSteps_push (padCopied input) (copiedLimit input)
    [DenseScheduleTemplate.mask8, DenseScheduleTemplate.mask16]
    (by decide) rfl rfl rfl deployAddress_not_precompile
  exact Challenge.EvmProof.GasSteps.cast g (by rfl) (by rfl)

/-! ## Whole-block test -/

private theorem xor_zero_iff (a b : Nat) : a ^^^ b = 0 ↔ a = b := by
  constructor
  · intro h
    have e : a ^^^ (a ^^^ b) = a ^^^ 0 := by rw [h]
    rw [← Nat.xor_assoc, Nat.xor_self, Nat.zero_xor, Nat.xor_zero] at e
    exact e.symm
  · intro h
    rw [h, Nat.xor_self]

private theorem mask_c0 (n : Nat) (hn : n < 2 ^ 64) :
    n &&& ((2 ^ 64 - 1) ^^^ 192) = 0 ↔ (n % 64 = 0 ∧ n < 256) := by
  rw [Nat.and_xor_distrib_left, Nat.and_two_pow_sub_one_eq_mod, Nat.mod_eq_of_lt hn,
    xor_zero_iff]
  constructor
  · intro h
    have hle : n ≤ 192 := by
      have : n &&& 192 ≤ 192 := Nat.and_le_right
      omega
    have h63 : n &&& 63 = 0 := by
      have e : n &&& 63 = (n &&& 192) &&& 63 := by rw [← h]
      rw [e, Nat.and_assoc, show (192 &&& 63 : Nat) = 0 by decide, Nat.and_zero]
    rw [show (63:Nat) = 2 ^ 6 - 1 by norm_num, Nat.and_two_pow_sub_one_eq_mod] at h63
    omega
  · intro ⟨h1, h2⟩
    have : n = 0 ∨ n = 64 ∨ n = 128 ∨ n = 192 := by omega
    rcases this with h | h | h | h <;> rw [h] <;> decide

/-- The guard uses the low 64 bits of `NOT 192`, sufficient under `CalldataFits`. -/
private theorem guardMask_toNat : (UInt256.ofNat 18446744073709551423).toNat = (2 ^ 64 - 1) ^^^ 192 := by
  decide

private theorem guard_zero_iff (input : ByteArray) (hfit : CalldataFits input) :
    (UInt256.land (UInt256.ofNat input.size) (UInt256.ofNat 18446744073709551423)).toNat = 0 ↔
      (input.size % 64 = 0 ∧ input.size < 256) := by
  have hsize : input.size < 2 ^ 256 := Nat.lt_trans hfit (by norm_num)
  rw [Challenge.EvmProof.Word.word_toNat_land, guardMask_toNat,
    Challenge.EvmProof.Word.word_toNat_ofNat, Nat.mod_eq_of_lt hsize]
  exact mask_c0 input.size hfit

def padGuardTaken (input : ByteArray) : State :=
  {padGuardMiss input with pc := UInt256.ofNat 143, stack := initialFrame input}

theorem padGuardMiss_memory (input : ByteArray) :
    (padGuardMiss input).memory = Shared32Scratch.copiedMemory input := by
  change MachineState.writeBytes ByteArray.empty
    (MachineState.readPadded input 0 input.size) 1056 = Shared32Scratch.copiedMemory input
  rw [Challenge.EvmProof.Memory.readPadded_zero_size]
  rfl

theorem padGuardMiss_active (input : ByteArray) (hfit : CalldataFits input)
    (hpos : 0 < input.size) : 34 ≤ (padGuardMiss input).activeWords.toNat := by
  have hsize : input.size < 2 ^ 64 := hfit
  change 34 ≤ (UInt256.ofNat (MachineState.activeWordsAfter
    (padLengthReady input).activeWords.toNat Padding.messageOffset input.size)).toNat
  have h0 : (padLengthReady input).activeWords.toNat = 0 := by rfl
  rw [h0]
  unfold MachineState.activeWordsAfter
  rw [if_neg (by omega)]
  dsimp only
  unfold Padding.messageOffset
  have hv : Nat.max 0 ((1056 + input.size - 1) / 32 + 1) = (1055 + input.size) / 32 + 1 := by
    change max 0 ((1056 + input.size - 1) / 32 + 1) = _
    rw [Nat.max_eq_right (Nat.zero_le _)]
    omega
  have hlt : (1055 + input.size) / 32 + 1 < 2 ^ 256 :=
    Nat.lt_trans (by omega : (1055 + input.size) / 32 + 1 < 2 ^ 64) (by norm_num)
  rw [hv, Challenge.EvmProof.Word.word_toNat_ofNat, Nat.mod_eq_of_lt hlt]
  omega

theorem padGuardMiss_msize (input : ByteArray) (hpos : 0 < input.size) :
    189 ≤ (padGuardMiss input).memory.size := by
  rw [padGuardMiss_memory, Shared32Scratch.copiedMemory_size input hpos]
  omega

theorem padGuardMiss_zero (input : ByteArray) :
    ∀ a, 157 ≤ a → a < 189 → (padGuardMiss input).memory[a]?.getD 0 = 0 := by
  intro a _ ha
  rw [padGuardMiss_memory]
  exact Shared32Scratch.copiedMemory_zero input a (by omega)

set_option maxHeartbeats 400000 in
theorem run_guardSkip (input : ByteArray) (hfit : CalldataFits input)
    (hz : input.size % 64 = 0 ∧ input.size < 256) :
    Challenge.EvmProof.DataStepper.runLocatedBlock guardPath
      (padFramed input) = some (padSkip input) := by
  have hv := (guard_zero_iff input hfit).mpr hz
  simp [guardPath, Artifact.padGuardPath,
    Challenge.EvmProof.DataStepper.runLocatedBlock,
    Challenge.EvmProof.DataStepper.runLocated, Challenge.EvmProof.DataStepper.runInstr,
    padFramed, padSkip, UInt256.isTrue, hv]

set_option maxHeartbeats 400000 in
theorem run_guardMiss (input : ByteArray) (hfit : CalldataFits input)
    (hnz : ¬ (input.size % 64 = 0 ∧ input.size < 256)) :
    Challenge.EvmProof.DataStepper.runLocatedBlock guardPath
      (padFramed input) = some (padGuardTaken input) := by
  have hv : (UInt256.land (UInt256.ofNat input.size) (UInt256.ofNat 18446744073709551423)).toNat ≠ 0 :=
    fun h => hnz ((guard_zero_iff input hfit).mp h)
  simp [guardPath, Artifact.padGuardPath,
    Challenge.EvmProof.DataStepper.runLocatedBlock,
    Challenge.EvmProof.DataStepper.runLocated, Challenge.EvmProof.DataStepper.runInstr,
    padFramed, padGuardTaken, padGuardMiss, UInt256.isTrue, hv]

def gasSteps_guardSkip (input : ByteArray) (hfit : CalldataFits input)
    (hz : input.size % 64 = 0 ∧ input.size < 256) :
    Challenge.EvmProof.GasSteps (padFramed input) (padSkip input) :=
  Challenge.EvmProof.DataStepper.runLocatedBlock_sound
    Artifact.submissionArtifact .Osaka guardPath (by rfl) (by rfl)
    (run_guardSkip input hfit hz) (by rfl) deployAddress_not_precompile

def gasSteps_guardMiss (input : ByteArray) (hfit : CalldataFits input)
    (hn32 : input.size ≠ 32) (hnz : ¬ (input.size % 64 = 0 ∧ input.size < 256)) :
    Challenge.EvmProof.GasSteps (padFramed input) (padDirty input) := by
  have g := Challenge.EvmProof.DataStepper.runLocatedBlock_sound
    Artifact.submissionArtifact .Osaka guardPath (by rfl) (by rfl)
    (run_guardMiss input hfit hnz) (by rfl) deployAddress_not_precompile
  have hpos : 0 < input.size := by
    by_contra h
    exact hnz ⟨by omega, by omega⟩
  have gp := ColdGuardFixup.gasSteps_partial (padGuardMiss input)
    StackRunBridge.initialHashState (UInt256.ofNat 1056) (copiedLimit input)
    [DenseScheduleTemplate.mask8, DenseScheduleTemplate.mask16]
    (by decide) rfl rfl rfl deployAddress_not_precompile
    (by exact Nat.lt_trans hfit (by norm_num)) hn32
    (padGuardMiss_active input hfit hpos)
    (by rw [padGuardMiss_memory]; have hh := Shared32Scratch.copiedMemory_size input hpos; omega)
    (by rw [padGuardMiss_memory]; intro a ha hb; exact Shared32Scratch.copiedMemory_zero input a (by omega)) rfl
  exact g.trans gp

set_option maxHeartbeats 400000 in
theorem run_lengthSentinelAddress (input : ByteArray) :
    Challenge.EvmProof.DataStepper.runLocatedBlock lengthSentinelAddressPath
      (padDirty input) = some (padSentinelAddressReady input) := by
  simp [lengthSentinelAddressPath, lengthSentinelPath,
    Artifact.padSentinelPath, Challenge.EvmProof.DataStepper.runLocatedBlock,
    Challenge.EvmProof.DataStepper.runLocated, Challenge.EvmProof.DataStepper.runInstr,
    padSentinelAddressReady, padDirty, padGuardMiss, padFrame, StaggerPersistentFrame.frame,
    Padding.messageOffset, Challenge.EvmProof.Word.word_add_comm]

set_option maxHeartbeats 400000 in
theorem run_lengthSentinelStore (input : ByteArray)
    (_hfit : CalldataFits input) :
    Challenge.EvmProof.DataStepper.runLocatedBlock lengthSentinelStorePath
      (padSentinelAddressReady input) = some (padSentinelStored input) := by
  simp [lengthSentinelStorePath, lengthSentinelPath,
    Artifact.padSentinelPath,
    Challenge.EvmProof.DataStepper.runLocatedBlock,
    Challenge.EvmProof.DataStepper.runLocated, Challenge.EvmProof.DataStepper.runInstr,
    padSentinelStored, State.activeWordsAfterUInt256]

theorem padSentinelStored_eq (input : ByteArray)
    (hfit : CalldataFits input) : padSentinelStored input = padSentinel input := by
  have hsum : Padding.messageOffset + input.size < 2 ^ 256 := by
    unfold CalldataFits at hfit
    norm_num [Padding.messageOffset] at hfit ⊢
    omega
  have hadd : UInt256.ofNat Padding.messageOffset + UInt256.ofNat input.size =
      UInt256.ofNat (Padding.messageOffset + input.size) :=
    Challenge.EvmProof.Word.ofNat_add_ofNat hsum
  have haddNat : (UInt256.ofNat Padding.messageOffset +
      UInt256.ofNat input.size).toNat = Padding.messageOffset + input.size := by
    rw [hadd, Challenge.EvmProof.Word.word_toNat_ofNat,
      Nat.mod_eq_of_lt hsum]
  unfold padSentinelStored padSentinel padSentinelAddressReady
  rw [show (UInt256.ofNat Padding.messageOffset +
    UInt256.ofNat input.size).toNat = Padding.messageOffset + input.size by
      exact haddNat]
  generalize padDirty input = s
  cases s
  rfl
/-! ## Little-endian footer loop

The artifact masks the bit length to 64 bits and then walks the footer bytes
least-significant first, stopping as soon as the residual length is zero.  The
old version wrote a zero sentinel at the high end of the footer window; the
candidate has removed that write, so the loop starts from the sentinel state
and its first store is also the first memory expansion in this window. -/

/-- Residual length after `i` byte-shifts, exactly as the machine holds it. -/
def lengthShift (input : ByteArray) : Nat → UInt256
  | 0 => bitLengthWord input
  | i + 1 => UInt256.shiftRight (lengthShift input i) (UInt256.ofNat 8)

/-- Footer cursor after `i` increments. -/
def lengthAddr (input : ByteArray) : Nat → UInt256
  | 0 => lengthOffsetWord input
  | i + 1 => UInt256.ofNat 1 + lengthAddr input i

/-- The most significant footer byte, written before the loop. -/
def topByteWord (input : ByteArray) : UInt256 :=
  UInt256.shiftRight (bitLengthWord input) (UInt256.ofNat 0x38)

def topByteAddr (input : ByteArray) : UInt256 :=
  UInt256.ofNat 7 + lengthOffsetWord input

def footerStart (input : ByteArray) : Nat :=
  Padding.messageOffset + Padding.paddedLength input.size - 8

def lengthLoopMemory (input : ByteArray) : Nat → ByteArray
  | 0 => (padSentinel input).memory
  | i + 1 => MachineState.writeBytes (lengthLoopMemory input i)
      (ByteArray.mk #[UInt8.ofNat ((lengthShift input i).toNat % 256)])
      (lengthAddr input i).toNat

/-! `activeWords` follows the actual one-byte stores.  In particular, this is
not pre-expanded at loop entry: the first iteration reaches the footer's
last word, and subsequent stores stay in that same word. -/
def lengthLoopActiveWords (input : ByteArray) : Nat → UInt256
  | 0 => (padSentinel input).activeWords
  | i + 1 => UInt256.ofNat (MachineState.activeWordsAfter
      (lengthLoopActiveWords input i).toNat (lengthAddr input i).toNat 1)
def lengthLoopState (input : ByteArray) (i : Nat) : State :=
  { padSentinel input with
    pc := UInt256.ofNat 4547
    stack := lengthAddr input i :: lengthShift input i :: UInt256.ofNat 4547 :: padFrame input
    memory := lengthLoopMemory input i
    activeWords := lengthLoopActiveWords input i }

/-- The footer loop at the end of the executable code (4547..4565): store the low byte, advance
the cursor, shift the residual, and `DUP4 JUMPI` back to the head 4547 that stays under the two
loop registers while the residual is nonzero. -/
def lengthIterationPath : List
    (Challenge.EvmProof.DataStepper.Located Artifact.submissionArtifact .Osaka) :=
  [⟨3397, .op .JUMPDEST, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨3398, .op (.Dup ⟨1, by decide⟩), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨3399, .op (.Dup ⟨1, by decide⟩), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨3400, .op .MSTORE8, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨3401, .push ⟨1, by decide⟩ (UInt256.ofNat 1), by rfl, by decide⟩,
   ⟨3402, .op .ADD, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨3403, .op (.Swap ⟨0, by decide⟩), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨3404, .push ⟨1, by decide⟩ (UInt256.ofNat 8), by rfl, by decide⟩,
   ⟨3405, .op .SHR, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨3406, .op (.Swap ⟨0, by decide⟩), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨3407, .op (.Dup ⟨1, by decide⟩), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨3408, .op (.Dup ⟨3, by decide⟩), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨3409, .op .JUMPI, by rfl, wfOp (by decide) trivial rfl⟩]

def lengthBodyPath := lengthIterationPath.take 10
def lengthBranchPath := lengthIterationPath.drop 10

@[simp] private theorem lengthLoopState_halt (input : ByteArray) (i : Nat) :
    (lengthLoopState input i).halt = .Running := by rfl

@[simp] private theorem lengthLoopState_fork (input : ByteArray) (i : Nat) :
    (lengthLoopState input i).fork = .Osaka := by rfl

@[simp] private theorem lengthLoopState_code (input : ByteArray) (i : Nat) :
    (lengthLoopState input i).executionEnv.code = submissionBytecode := by rfl

@[simp] private theorem lengthLoopState_pc (input : ByteArray) (i : Nat) :
    (lengthLoopState input i).pc = UInt256.ofNat 4547 := by rfl

@[simp] private theorem lengthLoopState_stack (input : ByteArray) (i : Nat) :
    (lengthLoopState input i).stack =
      lengthAddr input i :: lengthShift input i :: UInt256.ofNat 4547 :: padFrame input := by rfl

@[simp] private theorem padSentinel_code (input : ByteArray) :
    (padSentinel input).executionEnv.code = submissionBytecode := by rfl

/-- State after one low-byte store and both register updates (at the `DUP2` 4559). -/
def lengthSteppedState (input : ByteArray) (i : Nat) : State :=
  { lengthLoopState input i with
    pc := UInt256.ofNat 4559
    stack := lengthAddr input (i + 1) :: lengthShift input (i + 1) :: UInt256.ofNat 4547 ::
      padFrame input
    memory := lengthLoopMemory input (i + 1)
    activeWords := lengthLoopActiveWords input (i + 1) }

def lengthBackReturned (input : ByteArray) (i : Nat) : State :=
  { lengthSteppedState input i with pc := UInt256.ofNat 4547 }

def lengthExitPending (input : ByteArray) (i : Nat) : State :=
  { lengthSteppedState input i with pc := UInt256.ofNat 4562 }

theorem lengthBackReturned_eq (input : ByteArray) (i : Nat) :
    lengthBackReturned input i = lengthLoopState input (i + 1) := by
  unfold lengthBackReturned lengthSteppedState lengthLoopState
  generalize padSentinel input = s
  cases s
  rfl

@[simp] private theorem lengthSteppedState_halt (input : ByteArray) (i : Nat) :
    (lengthSteppedState input i).halt = .Running := by rfl

@[simp] private theorem lengthSteppedState_pc (input : ByteArray) (i : Nat) :
    (lengthSteppedState input i).pc = UInt256.ofNat 4559 := by rfl

@[simp] private theorem lengthSteppedState_code (input : ByteArray) (i : Nat) :
    (lengthSteppedState input i).executionEnv.code = submissionBytecode := by rfl

@[simp] private theorem validLengthLoopHead :
    Decode.isValidJumpDest submissionBytecode 4547 = true := by
  have hpc : Artifact.submissionArtifact.instructionPC 3397 = 4547 := by rw [Challenge.Ripemd160.Submission.Proofs.Bytecode.ArtifactByteLength.instructionPC_eq_byteLength]; rfl
  rw [← hpc]
  exact Artifact.submissionArtifact.isValidJumpDest_index 3397 (by rfl)

theorem validJump4949 :
    Decode.isValidJumpDest submissionBytecode (UInt256.ofNat 4547).toNat = true :=
  validLengthLoopHead

private theorem validJump198 :
    Decode.isValidJumpDest submissionBytecode 198 = true := by
  have hpc : Artifact.submissionArtifact.instructionPC 116 = 198 := padPc116
  rw [← hpc]
  exact Artifact.submissionArtifact.isValidJumpDest_index 116 (by rfl)

private theorem validJump461 :
    Decode.isValidJumpDest submissionBytecode (UInt256.ofNat 461).toNat = true :=
  Artifact.validJumpDest_loop

/-! ## Arithmetic bridge for the masked bit length -/

private theorem shiftLeft_ofNat_wrap {value shift : Nat}
    (hvalue : value < 2 ^ 256) (hshift : shift < 256) :
    UInt256.shiftLeft (UInt256.ofNat value) (UInt256.ofNat shift) =
      UInt256.ofNat ((value * 2 ^ shift) % 2 ^ 256) := by
  have hshift256 : shift < 2 ^ 256 := Nat.lt_trans hshift (by norm_num)
  have hshiftWord : (UInt256.ofNat shift).toNat = shift := by
    rw [Challenge.EvmProof.Word.word_toNat_ofNat, Nat.mod_eq_of_lt hshift256]
  unfold UInt256.shiftLeft
  rw [if_neg (by omega), hshiftWord, Challenge.EvmProof.Word.word_toNat_ofNat,
    Nat.mod_eq_of_lt hvalue, Nat.shiftLeft_eq,
    show UInt256.size = 2 ^ 256 by rfl]

/-- Unmasked bit length: `size <<< 3 = size * 8` on `CalldataFits`. -/
theorem bitLengthWord_toNat (input : ByteArray) (hfit : CalldataFits input) :
    (bitLengthWord input).toNat = input.size * 8 := by
  have hsize : input.size < 2 ^ 256 := Nat.lt_trans hfit (by norm_num)
  have hres : input.size * 2 ^ 3 < 2 ^ 256 := by
    have : input.size * 8 < 2 ^ 64 * 8 := Nat.mul_lt_mul_of_pos_right hfit (by decide)
    omega
  rw [bitLengthWord,
    Challenge.EvmProof.Word.shiftLeft_ofNat hsize (by decide : (3 : Nat) < 256) hres,
    Challenge.EvmProof.Word.word_toNat_ofNat]
  have : input.size * 2 ^ 3 = input.size * 8 := by
    simp [show (8 : Nat) = 2 ^ 3 by norm_num]
  rw [this, Nat.mod_eq_of_lt]
  have : input.size * 8 < 2 ^ 64 * 8 := Nat.mul_lt_mul_of_pos_right hfit (by decide)
  omega

theorem lengthShift_toNat (input : ByteArray) (hfit : CalldataFits input) (i : Nat) :
    (lengthShift input i).toNat = input.size * 8 / 2 ^ (8 * i) := by
  induction i with
  | zero => simpa [lengthShift] using bitLengthWord_toNat input hfit
  | succ i ih =>
      have hlt : (lengthShift input i).toNat < 2 ^ 256 := (lengthShift input i).val.isLt
      rw [lengthShift,
        Challenge.EvmProof.Word.word_eq_ofNat_toNat (lengthShift input i),
        Challenge.EvmProof.Word.shiftRight_ofNat hlt (by norm_num : (8 : Nat) < 256),
        Challenge.EvmProof.Word.word_toNat_ofNat, Nat.shiftRight_eq_div_pow,
        Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (Nat.div_le_self _ _) hlt), ih,
        Nat.div_div_eq_div_mul, ← Nat.pow_add]
      congr 2

theorem lengthShift_eight (input : ByteArray) (hfit : CalldataFits input)
    (h : input.size < 2 ^ 61) :
    lengthShift input 8 = ⟨0⟩ := by
  have hto := lengthShift_toNat input hfit 8
  have hz : input.size * 8 / 2 ^ (8 * 8) = 0 := by
    apply Nat.div_eq_of_lt
    have : input.size * 8 < 2 ^ 61 * 8 := Nat.mul_lt_mul_of_pos_right h (by decide)
    have : (2 : Nat) ^ 64 = 2 ^ 61 * 8 := by
      rw [show (8 : Nat) = 2 ^ 3 by norm_num, ← Nat.pow_add]
    omega
  apply Challenge.EvmProof.Word.word_ext
  rw [hto, hz]
  rfl

theorem lengthShift_nine (input : ByteArray) (hfit : CalldataFits input) :
    lengthShift input 9 = ⟨0⟩ := by
  have hto := lengthShift_toNat input hfit 9
  have hz : input.size * 8 / 2 ^ (8 * 9) = 0 := by
    apply Nat.div_eq_of_lt
    have : input.size * 8 < 2 ^ 64 * 8 := Nat.mul_lt_mul_of_pos_right hfit (by decide)
    have : (2 : Nat) ^ 64 * 8 = 2 ^ 67 := by
      rw [show (8 : Nat) = 2 ^ 3 by norm_num, ← Nat.pow_add]
    have : (2 : Nat) ^ 67 < 2 ^ 72 := by decide
    omega
  apply Challenge.EvmProof.Word.word_ext
  rw [hto, hz]
  rfl

/-! The machine exits after the first zero residual byte.  This finite
selector is definitionally independent of the calldata bound; the bound is
used only to prove that its fallback branch (iteration eight) is zero. -/
def lengthStop (input : ByteArray) : Nat :=
  if lengthShift input 1 = ⟨0⟩ then 1 else
  if lengthShift input 2 = ⟨0⟩ then 2 else
  if lengthShift input 3 = ⟨0⟩ then 3 else
  if lengthShift input 4 = ⟨0⟩ then 4 else
  if lengthShift input 5 = ⟨0⟩ then 5 else
  if lengthShift input 6 = ⟨0⟩ then 6 else
  if lengthShift input 7 = ⟨0⟩ then 7 else
    if lengthShift input 8 = ⟨0⟩ then 8 else 9

theorem lengthStop_pos (input : ByteArray) : 0 < lengthStop input := by
  unfold lengthStop
  split
  · omega
  · split
    · omega
    · split
      · omega
      · split
        · omega
        · split
          · omega
          · split
            · omega
            · split
              · omega
              · split
                · omega
                · omega

theorem lengthStop_le (input : ByteArray) : lengthStop input ≤ 9 := by
  unfold lengthStop
  split
  · omega
  · split
    · omega
    · split
      · omega
      · split
        · omega
        · split
          · omega
          · split
            · omega
            · split
              · omega
              · split
                · omega
                · omega

theorem lengthShift_stop_zero (input : ByteArray) (hfit : CalldataFits input) :
    lengthShift input (lengthStop input) = ⟨0⟩ := by
  simp only [lengthStop]
  split
  · assumption
  · split
    · assumption
    · split
      · assumption
      · split
        · assumption
        · split
          · assumption
          · split
            · assumption
            · split
              · assumption
              · split
                · assumption
                · exact lengthShift_nine input hfit

theorem lengthStop_eq_succ_of_nonzero (input : ByteArray) (i : Nat)
    (hi : i < 9)
    (hprior : ∀ j, 0 < j → j ≤ i → lengthShift input j ≠ ⟨0⟩)
    (hz : lengthShift input (i + 1) = ⟨0⟩) :
    lengthStop input = i + 1 := by
  interval_cases i <;> simp_all [lengthStop]

theorem footerCount_spec (input : ByteArray) (hfit : CalldataFits input) :
    1 ≤ lengthStop input ∧ lengthStop input ≤ 9 ∧
      lengthShift input (lengthStop input) = ⟨0⟩ ∧
      ∀ j, 1 ≤ j → j < lengthStop input →
        lengthShift input j ≠ ⟨0⟩ := by
  have hpos := lengthStop_pos input
  have hle := lengthStop_le input
  refine ⟨by omega, hle,
    lengthShift_stop_zero input hfit, ?_⟩
  intro j hj hstop
  have hj8 : j < 9 := by omega
  simp only [lengthStop] at hstop
  all_goals repeat' first | split at hstop | simp_all
  all_goals interval_cases j <;> simp_all

theorem lengthOffsetWord_eq (input : ByteArray) (hfit : CalldataFits input) :
    (lengthOffsetWord input).toNat =
      Padding.messageOffset + Padding.paddedLength input.size - 8 := by
  have hlt := Padding.paddedLength_lt input.size
  have hsum : Padding.paddedLength input.size + 1048 < 2 ^ 256 := by
    unfold CalldataFits at hfit
    norm_num at hfit ⊢
    omega
  rw [lengthOffsetWord, PadLimitArithmetic.coldRounded_input input hfit,
    PadLimitArithmetic.footer_addr input hfit, Padding.paddedWord_eq input hfit,
    Challenge.EvmProof.Word.ofNat_add_ofNat hsum,
    Challenge.EvmProof.Word.word_toNat_ofNat, Nat.mod_eq_of_lt hsum]
  unfold Padding.messageOffset
  omega

theorem lengthAddr_toNat (input : ByteArray) (hfit : CalldataFits input)
    (i : Nat) (hi : i ≤ 9) :
    (lengthAddr input i).toNat =
      Padding.messageOffset + Padding.paddedLength input.size - 8 + i := by
  induction i with
  | zero => simpa [lengthAddr] using lengthOffsetWord_eq input hfit
  | succ i ih =>
      have hlt := Padding.paddedLength_lt input.size
      have hbound : 1 + (Padding.messageOffset + Padding.paddedLength input.size - 8 + i)
          < 2 ^ 256 := by
        unfold CalldataFits at hfit
        unfold Padding.messageOffset
        norm_num at hfit ⊢
        omega
      rw [lengthAddr,
        Challenge.EvmProof.Word.word_eq_ofNat_toNat (lengthAddr input i),
        ih (by omega),
        Challenge.EvmProof.Word.ofNat_add_ofNat hbound,
        Challenge.EvmProof.Word.word_toNat_ofNat, Nat.mod_eq_of_lt hbound]
      omega

theorem topByteAddr_toNat (input : ByteArray) (hfit : CalldataFits input) :
    (topByteAddr input).toNat =
      Padding.messageOffset + Padding.paddedLength input.size - 8 + 7 := by
  have hlt := Padding.paddedLength_lt input.size
  have hbound : 7 + (Padding.messageOffset + Padding.paddedLength input.size - 8)
      < 2 ^ 256 := by
    unfold CalldataFits at hfit
    unfold Padding.messageOffset
    norm_num at hfit ⊢
    omega
  rw [topByteAddr,
    Challenge.EvmProof.Word.word_eq_ofNat_toNat (lengthOffsetWord input),
    lengthOffsetWord_eq input hfit,
    Challenge.EvmProof.Word.ofNat_add_ofNat hbound,
    Challenge.EvmProof.Word.word_toNat_ofNat, Nat.mod_eq_of_lt hbound]
  omega

/-! The recursive definition above is deliberately transparent.  The
corresponding store-step theorem is useful to callers that need the machine's
wrapped representation rather than a pre-expanded approximation. -/
@[simp] private theorem lengthLoopActiveWords_zero (input : ByteArray) :
    lengthLoopActiveWords input 0 = (padSentinel input).activeWords := by rfl

@[simp] private theorem lengthLoopActiveWords_succ (input : ByteArray) (i : Nat) :
    lengthLoopActiveWords input (i + 1) =
      UInt256.ofNat (MachineState.activeWordsAfter
        (lengthLoopActiveWords input i).toNat (lengthAddr input i).toNat 1) := by rfl

private theorem zero_toNat : (⟨0⟩ : UInt256).toNat = 0 := rfl
private theorem ofNat_zero_eq : UInt256.ofNat 0 = (⟨0⟩ : UInt256) := rfl

private theorem toNat_ne_zero_of_ne (x : UInt256) (hne : x ≠ ⟨0⟩) :
    x.toNat ≠ 0 := by
  intro h
  exact hne (Challenge.EvmProof.Word.word_ext (h.trans zero_toNat.symm))

private theorem isZero_of_ne (x : UInt256) (hne : x ≠ ⟨0⟩) :
    UInt256.isZero x = UInt256.ofNat 0 := by
  unfold UInt256.isZero
  exact if_neg (toNat_ne_zero_of_ne x hne)

private theorem isZero_of_eq (x : UInt256) (hz : x = ⟨0⟩) :
    UInt256.isZero x = UInt256.ofNat 1 := by
  subst hz
  unfold UInt256.isZero
  exact if_pos zero_toNat

set_option maxHeartbeats 800000 in
theorem run_lengthBody (input : ByteArray) (_hfit : CalldataFits input)
    (i : Nat) (_hi : i < 9) :
    Challenge.EvmProof.DataStepper.runLocatedBlock lengthBodyPath
      (lengthLoopState input i) = some (lengthSteppedState input i) := by
  simp [lengthBodyPath, lengthIterationPath,
    Challenge.EvmProof.DataStepper.runLocatedBlock,
    Challenge.EvmProof.DataStepper.runLocated, Challenge.EvmProof.DataStepper.runInstr,
    lengthSteppedState, lengthLoopState, lengthLoopMemory, lengthAddr, lengthShift,
    List.exchange, State.activeWordsAfterUInt256, lengthLoopActiveWords]

set_option maxHeartbeats 400000 in
theorem run_lengthBranchBack (input : ByteArray) (i : Nat)
    (hne : lengthShift input (i + 1) ≠ ⟨0⟩) :
    Challenge.EvmProof.DataStepper.runLocatedBlock lengthBranchPath
      (lengthSteppedState input i) = some (lengthBackReturned input i) := by
  have htrue : UInt256.isTrue (lengthShift input (i + 1)) = true := by
    simp [UInt256.isTrue, toNat_ne_zero_of_ne _ hne]
  simp [lengthBranchPath, lengthIterationPath,
    Challenge.EvmProof.DataStepper.runLocatedBlock,
    Challenge.EvmProof.DataStepper.runLocated, Challenge.EvmProof.DataStepper.runInstr,
    lengthSteppedState, lengthBackReturned, htrue, validJump4949]

set_option maxHeartbeats 400000 in
theorem run_lengthBranchExit (input : ByteArray) (i : Nat)
    (hz : lengthShift input (i + 1) = ⟨0⟩) :
    Challenge.EvmProof.DataStepper.runLocatedBlock lengthBranchPath
      (lengthSteppedState input i) = some (lengthExitPending input i) := by
  have hfalse : UInt256.isTrue (lengthShift input (i + 1)) = false := by
    simp [UInt256.isTrue, hz]
  simp [lengthBranchPath, lengthIterationPath,
    Challenge.EvmProof.DataStepper.runLocatedBlock,
    Challenge.EvmProof.DataStepper.runLocated, Challenge.EvmProof.DataStepper.runInstr,
    lengthSteppedState, lengthExitPending, hfalse]

def gasSteps_lengthIteration (input : ByteArray) (hfit : CalldataFits input)
    (i : Nat) (hi : i < 9) (hne : lengthShift input (i + 1) ≠ ⟨0⟩) :
    Challenge.EvmProof.GasSteps (lengthLoopState input i)
      (lengthLoopState input (i + 1)) := by
  have g₁ := Challenge.EvmProof.DataStepper.runLocatedBlock_sound
    Artifact.submissionArtifact .Osaka lengthBodyPath (by rfl) (by rfl)
    (run_lengthBody input hfit i hi) (by rfl) (by rfl)
  have g2raw := Challenge.EvmProof.DataStepper.runLocatedBlock_sound
    Artifact.submissionArtifact .Osaka lengthBranchPath (by rfl) (by rfl)
    (run_lengthBranchBack input i hne) (by rfl) (by rfl)
  have g₂ := Challenge.EvmProof.GasSteps.cast g2raw rfl
    (lengthBackReturned_eq input i)
  exact g₁.trans g₂

/-! ## Loop exit and return -/

def padFinalMemory (input : ByteArray) : ByteArray :=
  (lengthLoopState input (lengthStop input)).memory

def padReturned (input : ByteArray) : State :=
  { lengthLoopState input (lengthStop input) with
    pc := UInt256.ofNat 461
    stack := glFrame }

theorem lengthLoopActiveWords_succ_toNat (input : ByteArray)
    (hfit : CalldataFits input) (i : Nat) (hi : i ≤ 9) :
    (lengthLoopActiveWords input (i + 1)).toNat =
      Nat.max (lengthLoopActiveWords input i).toNat
        ((Padding.messageOffset + Padding.paddedLength input.size - 8 + i) / 32 + 1) := by
  have hlt := Padding.paddedLength_lt input.size
  have hcur : (lengthLoopActiveWords input i).toNat < 2 ^ 256 :=
    (lengthLoopActiveWords input i).val.isLt
  have hdiv : (Padding.messageOffset + Padding.paddedLength input.size - 8 + i) / 32
      ≤ Padding.messageOffset + Padding.paddedLength input.size - 8 + i :=
    Nat.div_le_self _ _
  have hbig : Padding.messageOffset + Padding.paddedLength input.size - 8 + i + 1
      < 2 ^ 256 := by
    unfold CalldataFits at hfit
    unfold Padding.messageOffset
    norm_num at hfit ⊢
    omega
  rw [lengthLoopActiveWords, Challenge.EvmProof.Word.word_toNat_ofNat,
    lengthAddr_toNat input hfit i hi]
  unfold MachineState.activeWordsAfter
  rw [if_neg (by decide : (1 : Nat) ≠ 0)]
  dsimp only
  refine Nat.mod_eq_of_lt ?_
  simp only [Nat.add_sub_cancel]
  rw [Nat.max_lt]
  exact ⟨hcur, by omega⟩

theorem padReturned_allocated (input : ByteArray) (hfit : CalldataFits input) :
    (Padding.messageOffset + Padding.paddedLength input.size + 31) / 32 ≤
      (padReturned input).activeWords.toNat := by
  have hp := lengthStop_pos input
  have hl := lengthStop_le input
  let j := lengthStop input - 1
  have hs : lengthStop input = j + 1 := by dsimp [j]; omega
  change _ ≤ (lengthLoopActiveWords input (lengthStop input)).toNat
  rw [hs, lengthLoopActiveWords_succ_toNat input hfit j (by dsimp [j]; omega)]
  apply Nat.le_trans ?_ (Nat.le_max_right _ _)
  have halign : Padding.paddedLength input.size % 64 = 0 := by
    unfold Padding.paddedLength
    omega
  unfold Padding.messageOffset
  omega

@[simp] theorem padReturned_pc (input : ByteArray) :
    (padReturned input).pc = UInt256.ofNat 461 := by rfl

@[simp] theorem padReturned_stack (input : ByteArray) :
    (padReturned input).stack = glFrame := by rfl

@[simp] theorem padReturned_halt (input : ByteArray) :
    (padReturned input).halt = .Running := by rfl

@[simp] theorem padReturned_code (input : ByteArray) :
    (padReturned input).executionEnv.code = submissionBytecode := by rfl

@[simp] theorem padReturned_fork (input : ByteArray) :
    (padReturned input).fork = .Osaka := by rfl

@[simp] theorem padReturned_codeAddr (input : ByteArray) :
    (padReturned input).executionEnv.codeAddr = deployAddress := by rfl

@[simp] theorem padReturned_noPrecompile (input : ByteArray) :
    Precompile.isPrecompileWithConfig (padReturned input).executionEnv.precompileConfig
      (padReturned input).executionEnv.fork
      (padReturned input).executionEnv.codeAddr = false := by
  exact deployAddress_not_precompile

def lengthExitPath : List
    (Challenge.EvmProof.DataStepper.Located Artifact.submissionArtifact .Osaka) :=
  Artifact.padExitPath

def lengthExitEntered (input : ByteArray) (i : Nat) : State :=
  { lengthLoopState input i with pc := UInt256.ofNat 4562 }

theorem lengthExitPending_eq (input : ByteArray) (i : Nat) :
    lengthExitPending input i = lengthExitEntered input (i + 1) := by
  unfold lengthExitPending lengthSteppedState
    lengthExitEntered lengthLoopState
  generalize padSentinel input = s
  cases s
  rfl

/-- After `PUSH1 198 JUMP`, the generic continuation 48 replaces the output entry (`SWAP16`), the
four `POP`s drop it and the three loop words, and the padding code jumps to the block-loop head. -/
def lengthExitReturned (input : ByteArray) (i : Nat) : State :=
  { lengthExitEntered input i with
    pc := UInt256.ofNat 461
    stack := glFrame }

@[simp] private theorem lengthExitEntered_halt (input : ByteArray) (i : Nat) :
    (lengthExitEntered input i).halt = .Running := by rfl

@[simp] private theorem lengthExitEntered_pc (input : ByteArray) (i : Nat) :
    (lengthExitEntered input i).pc = UInt256.ofNat 4562 := by rfl

@[simp] private theorem lengthExitEntered_code (input : ByteArray) (i : Nat) :
    (lengthExitEntered input i).executionEnv.code = submissionBytecode := by rfl

set_option maxHeartbeats 400000 in
/-- Keep memory and the concrete bytecode opaque while checking the stack-only
exit.  Expanding the full padding state here duplicates the large code array
in the kernel's record-update reductions. -/
private theorem run_lengthExitPop_opaque (s : State) (input : ByteArray)
    (a b : UInt256) (hrun : s.halt = .Running)
    (h198 : Decode.isValidJumpDest s.executionEnv.code 198 = true)
    (h461 : Decode.isValidJumpDest s.executionEnv.code 461 = true) :
    Challenge.EvmProof.DataStepper.runLocatedBlock lengthExitPath
      { s with
        pc := UInt256.ofNat 4562
        stack := a :: b :: UInt256.ofNat 4547 :: padFrame input } =
      some { s with pc := UInt256.ofNat 461, stack := glFrame } := by
  simp [lengthExitPath, Artifact.padExitPath,
    Challenge.EvmProof.DataStepper.runLocatedBlock,
    Challenge.EvmProof.DataStepper.runLocated, Challenge.EvmProof.DataStepper.runInstr,
    padFrame, glFrame, StaggerPersistentFrame.frame,
    List.exchange, List.getElem?_cons_zero, List.getElem?_cons_succ,
    h198, h461, hrun]

set_option maxHeartbeats 400000 in
theorem run_lengthExitPop (input : ByteArray) (i : Nat) :
    Challenge.EvmProof.DataStepper.runLocatedBlock lengthExitPath
      (lengthExitEntered input i) = some (lengthExitReturned input i) := by
  exact run_lengthExitPop_opaque (lengthLoopState input i) input
    (lengthAddr input i) (lengthShift input i) (by rfl)
    validJump198 validJump461

end Challenge.Ripemd160.Submission.Proofs.Bytecode.PaddingTrace
