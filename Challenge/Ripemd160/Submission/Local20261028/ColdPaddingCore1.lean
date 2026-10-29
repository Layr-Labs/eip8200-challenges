import Challenge.Ripemd160.Submission.Local20261028.ColdPaddingCore0
import Challenge.Ripemd160.Submission.Local20261028.ColdShared32Scratch
import Challenge.Ripemd160.Submission.Proofs.Bytecode.PcEncoding
import Challenge.Ripemd160.Submission.Proofs.Bytecode.Padding
import Challenge.Ripemd160.Submission.Proofs.Bytecode.StackTail
import Challenge.Ripemd160.Submission.Proofs.Bytecode.RawExpressionAC
import Challenge.Ripemd160.Submission.Local20261028.ColdTrace
import Challenge.Ripemd160.Submission.Local20261028.ColdMain
import Challenge.Ripemd160.Submission.Local20261028.ColdStaggerPersistentStart
import Challenge.Ripemd160.Submission.Local20261028.ColdGuardFinish
import Challenge.Ripemd160.Submission.Proofs.Bytecode.DataStepper
import Challenge.Ripemd160.Submission.Proofs.Bytecode.Msize
import Challenge.Ripemd160.Submission.Proofs.Bytecode.PadLimitArithmetic
set_option warningAsError true
set_option linter.unusedSimpArgs false
set_option maxRecDepth 1000000
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
/-!
# Direct execution of the RIPEMD-160 padding function (setup, guard, sentinel, footer loop and exit)

The fixed setup and the eight-iteration little-endian footer loop are exposed
as located paths.  The resulting state is shared by correctness and exact gas
accounting.
-/

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.Local20261028.Control.PaddingTrace
open EvmSemantics EvmSemantics.EVM
/-- The padding code is entered directly after the initial stores and falls
through into the driver entry, so no return address is pushed. -/
def padEntry (input : ByteArray) : State :=
  { Control.Main.initializedState input with
    pc := UInt256.ofNat 309
    stack := [DenseScheduleTemplate.mask8, DenseScheduleTemplate.mask16] }

@[simp] theorem padEntry_halt (input : ByteArray) :
    (padEntry input).halt = .Running := by rfl

@[simp] theorem padEntry_fork (input : ByteArray) :
    (padEntry input).fork = .Osaka := by rfl

@[simp] theorem padEntry_code (input : ByteArray) :
    (padEntry input).executionEnv.code = submissionBytecode := by rfl

@[simp] theorem padEntry_calldata (input : ByteArray) :
    (padEntry input).executionEnv.calldata = input := by rfl

@[simp] theorem initializedPC764 :
    Artifact.instructionPC 134 = 246 := by change Artifact.submissionArtifact.instructionPC 134 = 246; rw [Challenge.Ripemd160.Submission.Proofs.Bytecode.ArtifactByteLength.instructionPC_eq_byteLength]; rfl

/-! Instruction PCs of the sentinel/footer setup (99..110), the 192-stub jump (114..115), the exit block at 198
(116..123) and the footer loop tail (3412..3416) in this layout. -/

@[simp] theorem padPc99 :
    Control.Artifact.submissionArtifact.instructionPC 6815 = 10004 := by
  rw [Challenge.Ripemd160.Submission.Proofs.Bytecode.ArtifactByteLength.instructionPC_eq_byteLength]; rfl

@[simp] theorem padPci99 :
    Control.Artifact.instructionPC 6815 = 10004 := by
  change Control.Artifact.submissionArtifact.instructionPC 6815 = 10004
  rw [Challenge.Ripemd160.Submission.Proofs.Bytecode.ArtifactByteLength.instructionPC_eq_byteLength]; rfl

@[simp] theorem padPc108 :
    Control.Artifact.submissionArtifact.instructionPC 6824 = 10019 := by
  rw [Challenge.Ripemd160.Submission.Proofs.Bytecode.ArtifactByteLength.instructionPC_eq_byteLength]; rfl

@[simp] theorem padPci108 :
    Control.Artifact.instructionPC 6824 = 10019 := by
  change Control.Artifact.submissionArtifact.instructionPC 6824 = 10019
  rw [Challenge.Ripemd160.Submission.Proofs.Bytecode.ArtifactByteLength.instructionPC_eq_byteLength]; rfl

@[simp] theorem padPc109 :
    Control.Artifact.submissionArtifact.instructionPC 6825 = 10021 := by
  rw [Challenge.Ripemd160.Submission.Proofs.Bytecode.ArtifactByteLength.instructionPC_eq_byteLength]; rfl

@[simp] theorem padPci109 :
    Control.Artifact.instructionPC 6825 = 10021 := by
  change Control.Artifact.submissionArtifact.instructionPC 6825 = 10021
  rw [Challenge.Ripemd160.Submission.Proofs.Bytecode.ArtifactByteLength.instructionPC_eq_byteLength]; rfl

@[simp] theorem padPc110 :
    Control.Artifact.submissionArtifact.instructionPC 6826 = 10022 := by
  rw [Challenge.Ripemd160.Submission.Proofs.Bytecode.ArtifactByteLength.instructionPC_eq_byteLength]; rfl

@[simp] theorem padPci110 :
    Control.Artifact.instructionPC 6826 = 10022 := by
  change Control.Artifact.submissionArtifact.instructionPC 6826 = 10022
  rw [Challenge.Ripemd160.Submission.Proofs.Bytecode.ArtifactByteLength.instructionPC_eq_byteLength]; rfl

@[simp] theorem padPc114 :
    Control.Artifact.submissionArtifact.instructionPC 95 = 195 := by
  rw [Challenge.Ripemd160.Submission.Proofs.Bytecode.ArtifactByteLength.instructionPC_eq_byteLength]; rfl

@[simp] theorem padPci114 :
    Control.Artifact.instructionPC 95 = 195 := by
  change Control.Artifact.submissionArtifact.instructionPC 95 = 195
  rw [Challenge.Ripemd160.Submission.Proofs.Bytecode.ArtifactByteLength.instructionPC_eq_byteLength]; rfl

@[simp] theorem padPc115 :
    Control.Artifact.submissionArtifact.instructionPC 96 = 197 := by
  rw [Challenge.Ripemd160.Submission.Proofs.Bytecode.ArtifactByteLength.instructionPC_eq_byteLength]; rfl

@[simp] theorem padPci115 :
    Control.Artifact.instructionPC 96 = 197 := by
  change Control.Artifact.submissionArtifact.instructionPC 96 = 197
  rw [Challenge.Ripemd160.Submission.Proofs.Bytecode.ArtifactByteLength.instructionPC_eq_byteLength]; rfl

@[simp] theorem padPc116 :
    Control.Artifact.submissionArtifact.instructionPC 97 = 198 := by
  rw [Challenge.Ripemd160.Submission.Proofs.Bytecode.ArtifactByteLength.instructionPC_eq_byteLength]; rfl

@[simp] theorem padPci116 :
    Control.Artifact.instructionPC 97 = 198 := by
  change Control.Artifact.submissionArtifact.instructionPC 97 = 198
  rw [Challenge.Ripemd160.Submission.Proofs.Bytecode.ArtifactByteLength.instructionPC_eq_byteLength]; rfl

@[simp] theorem padPc117 :
    Control.Artifact.submissionArtifact.instructionPC 98 = 199 := by
  rw [Challenge.Ripemd160.Submission.Proofs.Bytecode.ArtifactByteLength.instructionPC_eq_byteLength]; rfl

@[simp] theorem padPci117 :
    Control.Artifact.instructionPC 98 = 199 := by
  change Control.Artifact.submissionArtifact.instructionPC 98 = 199
  rw [Challenge.Ripemd160.Submission.Proofs.Bytecode.ArtifactByteLength.instructionPC_eq_byteLength]; rfl

@[simp] theorem padPc118 :
    Control.Artifact.submissionArtifact.instructionPC 99 = 201 := by
  rw [Challenge.Ripemd160.Submission.Proofs.Bytecode.ArtifactByteLength.instructionPC_eq_byteLength]; rfl

@[simp] theorem padPci118 :
    Control.Artifact.instructionPC 99 = 201 := by
  change Control.Artifact.submissionArtifact.instructionPC 99 = 201
  rw [Challenge.Ripemd160.Submission.Proofs.Bytecode.ArtifactByteLength.instructionPC_eq_byteLength]; rfl

@[simp] theorem padPc119 :
    Control.Artifact.submissionArtifact.instructionPC 100 = 202 := by
  rw [Challenge.Ripemd160.Submission.Proofs.Bytecode.ArtifactByteLength.instructionPC_eq_byteLength]; rfl

@[simp] theorem padPci119 :
    Control.Artifact.instructionPC 100 = 202 := by
  change Control.Artifact.submissionArtifact.instructionPC 100 = 202
  rw [Challenge.Ripemd160.Submission.Proofs.Bytecode.ArtifactByteLength.instructionPC_eq_byteLength]; rfl

@[simp] theorem padPc120 :
    Control.Artifact.submissionArtifact.instructionPC 101 = 203 := by
  rw [Challenge.Ripemd160.Submission.Proofs.Bytecode.ArtifactByteLength.instructionPC_eq_byteLength]; rfl

@[simp] theorem padPci120 :
    Control.Artifact.instructionPC 101 = 203 := by
  change Control.Artifact.submissionArtifact.instructionPC 101 = 203
  rw [Challenge.Ripemd160.Submission.Proofs.Bytecode.ArtifactByteLength.instructionPC_eq_byteLength]; rfl

@[simp] theorem padPc121 :
    Control.Artifact.submissionArtifact.instructionPC 102 = 204 := by
  rw [Challenge.Ripemd160.Submission.Proofs.Bytecode.ArtifactByteLength.instructionPC_eq_byteLength]; rfl

@[simp] theorem padPci121 :
    Control.Artifact.instructionPC 102 = 204 := by
  change Control.Artifact.submissionArtifact.instructionPC 102 = 204
  rw [Challenge.Ripemd160.Submission.Proofs.Bytecode.ArtifactByteLength.instructionPC_eq_byteLength]; rfl

@[simp] theorem padPc122 :
    Control.Artifact.submissionArtifact.instructionPC 103 = 205 := by
  rw [Challenge.Ripemd160.Submission.Proofs.Bytecode.ArtifactByteLength.instructionPC_eq_byteLength]; rfl

@[simp] theorem padPci122 :
    Control.Artifact.instructionPC 103 = 205 := by
  change Control.Artifact.submissionArtifact.instructionPC 103 = 205
  rw [Challenge.Ripemd160.Submission.Proofs.Bytecode.ArtifactByteLength.instructionPC_eq_byteLength]; rfl

@[simp] theorem padPc123 :
    Control.Artifact.submissionArtifact.instructionPC 104 = 206 := by
  rw [Challenge.Ripemd160.Submission.Proofs.Bytecode.ArtifactByteLength.instructionPC_eq_byteLength]; rfl

@[simp] theorem padPci123 :
    Control.Artifact.instructionPC 104 = 206 := by
  change Control.Artifact.submissionArtifact.instructionPC 104 = 206
  rw [Challenge.Ripemd160.Submission.Proofs.Bytecode.ArtifactByteLength.instructionPC_eq_byteLength]; rfl

set_option maxRecDepth 100000 in
@[simp] theorem padPc3607 :
    Control.Artifact.submissionArtifact.instructionPC 3358 = 4593 := by
  rw [Challenge.Ripemd160.Submission.Proofs.Bytecode.ArtifactByteLength.instructionPC_eq_byteLength]; rfl

set_option maxRecDepth 100000 in
@[simp] theorem padPci3607 :
    Control.Artifact.instructionPC 3358 = 4593 := by
  change Control.Artifact.submissionArtifact.instructionPC 3358 = 4593
  rw [Challenge.Ripemd160.Submission.Proofs.Bytecode.ArtifactByteLength.instructionPC_eq_byteLength]; rfl

set_option maxRecDepth 100000 in
@[simp] theorem padPc3608 :
    Control.Artifact.submissionArtifact.instructionPC 3359 = 4594 := by
  rw [Challenge.Ripemd160.Submission.Proofs.Bytecode.ArtifactByteLength.instructionPC_eq_byteLength]; rfl

set_option maxRecDepth 100000 in
@[simp] theorem padPci3608 :
    Control.Artifact.instructionPC 3359 = 4594 := by
  change Control.Artifact.submissionArtifact.instructionPC 3359 = 4594
  rw [Challenge.Ripemd160.Submission.Proofs.Bytecode.ArtifactByteLength.instructionPC_eq_byteLength]; rfl

set_option maxRecDepth 100000 in
@[simp] theorem padPc3609 :
    Control.Artifact.submissionArtifact.instructionPC 3360 = 4595 := by
  rw [Challenge.Ripemd160.Submission.Proofs.Bytecode.ArtifactByteLength.instructionPC_eq_byteLength]; rfl

set_option maxRecDepth 100000 in
@[simp] theorem padPci3609 :
    Control.Artifact.instructionPC 3360 = 4595 := by
  change Control.Artifact.submissionArtifact.instructionPC 3360 = 4595
  rw [Challenge.Ripemd160.Submission.Proofs.Bytecode.ArtifactByteLength.instructionPC_eq_byteLength]; rfl

set_option maxRecDepth 100000 in
@[simp] theorem padPc3610 :
    Control.Artifact.submissionArtifact.instructionPC 3361 = 4596 := by
  rw [Challenge.Ripemd160.Submission.Proofs.Bytecode.ArtifactByteLength.instructionPC_eq_byteLength]; rfl

set_option maxRecDepth 100000 in
@[simp] theorem padPci3610 :
    Control.Artifact.instructionPC 3361 = 4596 := by
  change Control.Artifact.submissionArtifact.instructionPC 3361 = 4596
  rw [Challenge.Ripemd160.Submission.Proofs.Bytecode.ArtifactByteLength.instructionPC_eq_byteLength]; rfl

set_option maxRecDepth 100000 in
@[simp] theorem padPc3611 :
    Control.Artifact.submissionArtifact.instructionPC 3362 = 4597 := by
  rw [Challenge.Ripemd160.Submission.Proofs.Bytecode.ArtifactByteLength.instructionPC_eq_byteLength]; rfl

set_option maxRecDepth 100000 in
@[simp] theorem padPci3611 :
    Control.Artifact.instructionPC 3362 = 4597 := by
  change Control.Artifact.submissionArtifact.instructionPC 3362 = 4597
  rw [Challenge.Ripemd160.Submission.Proofs.Bytecode.ArtifactByteLength.instructionPC_eq_byteLength]; rfl

set_option maxRecDepth 100000 in
@[simp] theorem padPc3612 :
    Control.Artifact.submissionArtifact.instructionPC 3363 = 4598 := by
  rw [Challenge.Ripemd160.Submission.Proofs.Bytecode.ArtifactByteLength.instructionPC_eq_byteLength]; rfl

set_option maxRecDepth 100000 in
@[simp] theorem padPci3612 :
    Control.Artifact.instructionPC 3363 = 4598 := by
  change Control.Artifact.submissionArtifact.instructionPC 3363 = 4598
  rw [Challenge.Ripemd160.Submission.Proofs.Bytecode.ArtifactByteLength.instructionPC_eq_byteLength]; rfl

set_option maxRecDepth 100000 in
@[simp] theorem padPc3613 :
    Control.Artifact.submissionArtifact.instructionPC 3364 = 4600 := by
  rw [Challenge.Ripemd160.Submission.Proofs.Bytecode.ArtifactByteLength.instructionPC_eq_byteLength]; rfl

set_option maxRecDepth 100000 in
@[simp] theorem padPci3613 :
    Control.Artifact.instructionPC 3364 = 4600 := by
  change Control.Artifact.submissionArtifact.instructionPC 3364 = 4600
  rw [Challenge.Ripemd160.Submission.Proofs.Bytecode.ArtifactByteLength.instructionPC_eq_byteLength]; rfl

@[simp] theorem initializedCalldata (input : ByteArray) :
    (Control.Main.initializedState input).executionEnv.calldata = input := by rfl

def enterPath : List
    (Challenge.EvmProof.DataStepper.Located Control.Artifact.submissionArtifact .Osaka) :=
  Control.Artifact.padEnterPath

theorem mask16_literal :
    UInt256.ofNat
        1766820105243087041267848467410591083712559083657179364930612997358944255 =
      DenseScheduleTemplate.mask16 := by decide

theorem mask8_literal :
    UInt256.ofNat 450552876409790643671482431940419874915447411150352389258589821042463539455 = DenseScheduleTemplate.mask8 := by decide

set_option maxHeartbeats 400000 in
/-- The hash entry computes the two byte-swap masks once; they stay below the limit for the
whole hash. -/
theorem run_enter (input : ByteArray) :
    Challenge.EvmProof.DataStepper.runLocatedBlock enterPath
      (Control.Main.initializedState input) = some (padEntry input) := by
  have hzero : ({val := 0} : UInt256) = UInt256.ofNat 0 := rfl
  have p246 : Control.Artifact.submissionArtifact.instructionPC 134 = 246 := by
    rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl
  have p277 : Control.Artifact.submissionArtifact.instructionPC 135 = 277 := by
    rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl
  simp [enterPath, Control.Artifact.padEnterPath, Challenge.EvmProof.DataStepper.runLocatedBlock,
    Challenge.EvmProof.DataStepper.runLocated, Challenge.EvmProof.DataStepper.runInstr,
    padEntry, Control.Main.initializedState, Control.Execution.mainStart, Control.Execution.atPC, hzero,
    p246, p277, initialState]
  exact ⟨mask8_literal, mask16_literal⟩

def gasSteps_enterPad (input : ByteArray) :
    Challenge.EvmProof.GasSteps (Control.Main.initializedState input) (padEntry input) := by
  apply Challenge.EvmProof.DataStepper.runLocatedBlock_sound
    Control.Artifact.submissionArtifact .Osaka enterPath
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

@[simp] theorem padLengthReady_halt (input : ByteArray) :
    (padLengthReady input).halt = .Running := by rfl

@[simp] theorem padLengthReady_fork (input : ByteArray) :
    (padLengthReady input).fork = .Osaka := by rfl

@[simp] theorem padLengthReady_code (input : ByteArray) :
    (padLengthReady input).executionEnv.code = submissionBytecode := by rfl

@[simp] theorem padLengthReady_calldata (input : ByteArray) :
    (padLengthReady input).executionEnv.calldata = input := by rfl

@[simp] theorem padLengthReady_stack (input : ByteArray) :
    (padLengthReady input).stack = [DenseScheduleTemplate.mask8, DenseScheduleTemplate.mask16] := by
  rfl


end Challenge.Ripemd160.Submission.Proofs.Bytecode.Local20261028.Control.PaddingTrace
