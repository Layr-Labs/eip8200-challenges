import Challenge.Ripemd160.Submission.Proofs.Bytecode.Padding
import Challenge.Ripemd160.Submission.Proofs.Bytecode.StackTail
import Challenge.Ripemd160.Submission.Proofs.Bytecode.RawExpressionAC
import Challenge.Ripemd160.Submission.Proofs.Bytecode.Trace
import Challenge.Ripemd160.Submission.Proofs.Bytecode.Main
import Challenge.Ripemd160.Submission.Proofs.Bytecode.StaggerPersistentStart
import Challenge.Ripemd160.Submission.Proofs.Bytecode.DataStepper
import Challenge.Ripemd160.Submission.Proofs.Bytecode.Msize
import Challenge.Ripemd160.Submission.Proofs.Bytecode.PadLimitArithmetic
set_option warningAsError true
set_option maxRecDepth 20000
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
/-!
# Direct execution of the RIPEMD-160 padding function

The fixed setup and the eight-iteration little-endian footer loop are exposed
as located paths.  The resulting state is shared by correctness and exact gas
accounting.
-/

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.PaddingTrace

open EvmSemantics
open EvmSemantics.EVM

@[simp] private theorem literalZeroNat : (⟨0⟩ : UInt256).toNat = 0 := rfl

private def wfOp {op : Operation}
    (hopcode : Decode.opcodeOf (YulEvmCompiler.Instr.opByte op) = some op)
    (hplain : YulEvmCompiler.plainOp op)
    (havailable : op.availableInFork .Osaka = true) :
    Challenge.EvmProof.DataStepper.WellFormed .Osaka (.op op) :=
  ⟨hopcode, hplain, havailable⟩

/-- The padding code is entered directly after the initial stores and falls
through into the driver entry, so no return address is pushed. -/
def padEntry (input : ByteArray) : State :=
  { Main.initializedState input with
    pc := UInt256.ofNat 310
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
    Artifact.instructionPC 148 = 247 := by change Artifact.submissionArtifact.instructionPC 148 = 247; rw [Challenge.Ripemd160.Submission.Proofs.Bytecode.ArtifactByteLength.instructionPC_eq_byteLength]; rfl

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
private theorem run_enter (input : ByteArray) :
    Challenge.EvmProof.DataStepper.runLocatedBlock enterPath
      (Main.initializedState input) = some (padEntry input) := by
  have hzero : ({val := 0} : UInt256) = UInt256.ofNat 0 := rfl
  have p245 : Artifact.submissionArtifact.instructionPC 148 = 247 := by
    rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl
  have p246 : Artifact.submissionArtifact.instructionPC 149 = 278 := by
    rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl
  simp [enterPath, Artifact.padEnterPath, Challenge.EvmProof.DataStepper.runLocatedBlock,
    Challenge.EvmProof.DataStepper.runLocated, Challenge.EvmProof.DataStepper.runInstr,
    padEntry, Main.initializedState, Execution.mainStart, Execution.atPC, hzero,
    p245, p246, initialState]
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

/-- After the calldata copy (`CALLDATASIZE PUSH0 PUSH2 0x420 CALLDATACOPY`): the input sits at
memory 1056, and the next instruction (`MSIZE`) reads the active size as the loop limit. -/
def padLengthReady (input : ByteArray) : State :=
  { padEntry input with pc := UInt256.ofNat 310 }

/-- The state right after the copy, before `MSIZE`. -/
def padCopyDone (input : ByteArray) : State :=
  { padLengthReady input with
    pc := UInt256.ofNat 316
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

/-- The raw loop limit read by `MSIZE` right after the copy: `1056 + ceil32 size`. -/
def copiedLimit (input : ByteArray) : UInt256 :=
  UInt256.ofNat (32 * (padCopyDone input).activeWords.toNat)

theorem copiedLimit_aligned (input : ByteArray) (hfit : CalldataFits input)
    (hz : input.size % 32 = 0) (hpos : 0 < input.size) :
    copiedLimit input = UInt256.ofNat (1056 + input.size) := by
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
  unfold copiedLimit
  rw [haw]
  congr 1
  omega

def bitLengthWord (input : ByteArray) : UInt256 :=
  UInt256.shiftLeft (UInt256.ofNat input.size) (UInt256.ofNat 3)

def lengthOffsetWord (input : ByteArray) : UInt256 :=
  PadLimitArithmetic.coldRounded (UInt256.ofNat input.size) + UInt256.ofNat 25

/-- The persistent block-loop frame at hash entry: the initial chaining words and the six
resident round constants above the zero offset and the padded limit. -/
def initialFrame (input : ByteArray) : List UInt256 :=
  StaggerPersistentFrame.frame StackRunBridge.initialHashState (UInt256.ofNat 1056)
    (copiedLimit input) [DenseScheduleTemplate.mask8, DenseScheduleTemplate.mask16]

@[simp] theorem initialFrame_length (input : ByteArray) : (initialFrame input).length = 15 := by
  simp [initialFrame, StaggerPersistentFrame.frame]

def padFrame (input : ByteArray) : List UInt256 :=
  StaggerPersistentFrame.frame StackRunBridge.initialHashState (UInt256.ofNat 1056)
    (PadLimitArithmetic.coldRounded (UInt256.ofNat input.size))
    [DenseScheduleTemplate.mask8, DenseScheduleTemplate.mask16]

@[simp] theorem padFrame_length (input : ByteArray) : (padFrame input).length = 15 := by
  simp [padFrame, StaggerPersistentFrame.frame]

def padCopied (input : ByteArray) : State :=
  { padCopyDone input with
    pc := UInt256.ofNat 317
    stack := [copiedLimit input, DenseScheduleTemplate.mask8, DenseScheduleTemplate.mask16] }

/-- State after the eleven frame pushes. -/
def padFramed (input : ByteArray) : State :=
  { padCopied input with
    pc := UInt256.ofNat 448
    stack := initialFrame input }

/-- Fast-entry input (64, 128 or 192 bytes): the padding code falls straight into the block
loop with only the calldata copy in memory. -/
def padSkip (input : ByteArray) : State :=
  { padCopied input with
    pc := UInt256.ofNat 456
    stack := initialFrame input }

/-- Partial last block: fall through into the sentinel store. -/
def padGuardMiss (input : ByteArray) : State :=
  { padCopied input with
    pc := UInt256.ofNat 208
    stack := padFrame input }

def padSentinel (input : ByteArray) : State :=
  { padCopied input with
    pc := UInt256.ofNat 216
    stack := padFrame input
    memory := MachineState.writeBytes (padCopied input).memory
      (ByteArray.mk #[0x80]) (Padding.messageOffset + input.size)
    activeWords := (padCopied input).activeWordsAfterUInt256
      (Padding.messageOffset + input.size) 1 }

@[simp] private theorem padCopied_halt (input : ByteArray) :
    (padCopied input).halt = .Running := by rfl

@[simp] private theorem padCopied_pcToNat (input : ByteArray) :
    (padCopied input).pc.toNat = 317 := by rfl

@[simp] private theorem padCopied_pc (input : ByteArray) :
    (padCopied input).pc = UInt256.ofNat 317 := by rfl

@[simp] private theorem padCopied_stack (input : ByteArray) :
    (padCopied input).stack =
      [copiedLimit input, DenseScheduleTemplate.mask8, DenseScheduleTemplate.mask16] := by
  rfl

@[simp] theorem padCopied_calldata (input : ByteArray) :
    (padCopied input).executionEnv.calldata = input := by rfl

@[simp] theorem padCopied_code (input : ByteArray) :
    (padCopied input).executionEnv.code = submissionBytecode := by rfl

@[simp] private theorem padFramed_halt (input : ByteArray) :
    (padFramed input).halt = .Running := by rfl

@[simp] private theorem padFramed_pc (input : ByteArray) :
    (padFramed input).pc = UInt256.ofNat 448 := by rfl

@[simp] private theorem padFramed_code (input : ByteArray) :
    (padFramed input).executionEnv.code = submissionBytecode := by rfl

@[simp] private theorem padFramed_calldata (input : ByteArray) :
    (padFramed input).executionEnv.calldata = input := by rfl

@[simp] private theorem padGuardMiss_halt (input : ByteArray) :
    (padGuardMiss input).halt = .Running := by rfl

@[simp] private theorem padGuardMiss_pc (input : ByteArray) :
    (padGuardMiss input).pc = UInt256.ofNat 208 := by rfl

@[simp] private theorem padGuardMiss_code (input : ByteArray) :
    (padGuardMiss input).executionEnv.code = submissionBytecode := by rfl

@[simp] private theorem padGuardMiss_calldata (input : ByteArray) :
    (padGuardMiss input).executionEnv.calldata = input := by rfl

@[simp] private theorem padSentinel_halt (input : ByteArray) :
    (padSentinel input).halt = .Running := by rfl

@[simp] private theorem padSentinel_pcToNat (input : ByteArray) :
    (padSentinel input).pc.toNat = 216 := by rfl

@[simp] private theorem padSentinel_pc (input : ByteArray) :
    (padSentinel input).pc = UInt256.ofNat 216 := by rfl

@[simp] private theorem padSentinel_pcSucc (input : ByteArray) :
    (padSentinel input).pc.succ = UInt256.ofNat 217 := by
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
  { padCopied input with
    pc := UInt256.ofNat 215
    stack := [UInt256.ofNat Padding.messageOffset + UInt256.ofNat input.size,
      UInt256.ofNat 128] ++ padFrame input }

def padSentinelStored (input : ByteArray) : State :=
  { padSentinelAddressReady input with
    pc := UInt256.ofNat 216
    stack := padFrame input
    memory := MachineState.writeBytes (padSentinelAddressReady input).memory
      (ByteArray.mk #[0x80])
      (UInt256.ofNat Padding.messageOffset + UInt256.ofNat input.size).toNat
    activeWords := (padSentinelAddressReady input).activeWordsAfterUInt256
      (UInt256.ofNat Padding.messageOffset + UInt256.ofNat input.size).toNat 1 }

@[simp] private theorem padSentinelAddressReady_halt (input : ByteArray) :
    (padSentinelAddressReady input).halt = .Running := by rfl

@[simp] private theorem padSentinelAddressReady_pc (input : ByteArray) :
    (padSentinelAddressReady input).pc = UInt256.ofNat 215 := by rfl

@[simp] private theorem padSentinelAddressReady_stack (input : ByteArray) :
    (padSentinelAddressReady input).stack =
      [UInt256.ofNat Padding.messageOffset + UInt256.ofNat input.size,
        UInt256.ofNat 128] ++ padFrame input := by rfl

@[simp] private theorem padSentinelAddressReady_memory (input : ByteArray) :
    (padSentinelAddressReady input).memory = (padCopied input).memory := by rfl

@[simp] private theorem padSentinelAddressReady_activeWords (input : ByteArray) :
    (padSentinelAddressReady input).activeWords = (padCopied input).activeWords := by rfl

set_option maxHeartbeats 200000 in
@[simp] private theorem padLengthReady_pc (input : ByteArray) :
    (padLengthReady input).pc = UInt256.ofNat 310 := by rfl

private theorem run_lengthCopy (input : ByteArray) (hfit : CalldataFits input) :
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

private theorem mask_c0 (n : Nat) (hn : n < 2 ^ 256) :
    n &&& ((2 ^ 256 - 1) ^^^ 192) = 0 ↔ (n % 64 = 0 ∧ n < 256) := by
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

private theorem lnot192_toNat : (UInt256.lnot (UInt256.ofNat 192)).toNat = (2 ^ 256 - 1) ^^^ 192 := by
  decide

private theorem guard_zero_iff (input : ByteArray) (hfit : CalldataFits input) :
    (UInt256.land (UInt256.ofNat input.size) (UInt256.lnot (UInt256.ofNat 192))).toNat = 0 ↔
      (input.size % 64 = 0 ∧ input.size < 256) := by
  have hsize : input.size < 2 ^ 256 := Nat.lt_trans hfit (by norm_num)
  rw [Challenge.EvmProof.Word.word_toNat_land, lnot192_toNat,
    Challenge.EvmProof.Word.word_toNat_ofNat, Nat.mod_eq_of_lt hsize]
  exact mask_c0 input.size hsize

def padGuardTaken (input : ByteArray) : State :=
  {padGuardMiss input with pc := UInt256.ofNat 190, stack := initialFrame input}

set_option maxHeartbeats 400000 in
private theorem run_guardSkip (input : ByteArray) (hfit : CalldataFits input)
    (hz : input.size % 64 = 0 ∧ input.size < 256) :
    Challenge.EvmProof.DataStepper.runLocatedBlock guardPath
      (padFramed input) = some (padSkip input) := by
  have hv := (guard_zero_iff input hfit).mpr hz
  simp [guardPath, Artifact.padGuardPath,
    Challenge.EvmProof.DataStepper.runLocatedBlock,
    Challenge.EvmProof.DataStepper.runLocated, Challenge.EvmProof.DataStepper.runInstr,
    padFramed, padSkip, UInt256.isTrue, hv]

set_option maxHeartbeats 400000 in
private theorem run_guardMiss (input : ByteArray) (hfit : CalldataFits input)
    (hnz : ¬ (input.size % 64 = 0 ∧ input.size < 256)) :
    Challenge.EvmProof.DataStepper.runLocatedBlock guardPath
      (padFramed input) = some (padGuardTaken input) := by
  have hv : (UInt256.land (UInt256.ofNat input.size) (UInt256.lnot (UInt256.ofNat 192))).toNat ≠ 0 :=
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
    Challenge.EvmProof.GasSteps (padFramed input) (padGuardMiss input) := by
  have g := Challenge.EvmProof.DataStepper.runLocatedBlock_sound
    Artifact.submissionArtifact .Osaka guardPath (by rfl) (by rfl)
    (run_guardMiss input hfit hnz) (by rfl) deployAddress_not_precompile
  have gp := StaggerPersistentStart.gasSteps_partial (padGuardMiss input)
    StackRunBridge.initialHashState (UInt256.ofNat 1056) (copiedLimit input)
    [DenseScheduleTemplate.mask8, DenseScheduleTemplate.mask16]
    (by decide) rfl rfl rfl deployAddress_not_precompile
    (by exact Nat.lt_trans hfit (by norm_num)) hn32
  exact g.trans gp

set_option maxHeartbeats 400000 in
private theorem run_lengthSentinelAddress (input : ByteArray) :
    Challenge.EvmProof.DataStepper.runLocatedBlock lengthSentinelAddressPath
      (padGuardMiss input) = some (padSentinelAddressReady input) := by
  simp [lengthSentinelAddressPath, lengthSentinelPath,
    Artifact.padSentinelPath, Challenge.EvmProof.DataStepper.runLocatedBlock,
    Challenge.EvmProof.DataStepper.runLocated, Challenge.EvmProof.DataStepper.runInstr,
    padSentinelAddressReady, padGuardMiss, Padding.messageOffset, Challenge.EvmProof.Word.word_add_comm]

set_option maxHeartbeats 400000 in
private theorem run_lengthSentinelStore (input : ByteArray)
    (_hfit : CalldataFits input) :
    Challenge.EvmProof.DataStepper.runLocatedBlock lengthSentinelStorePath
      (padSentinelAddressReady input) = some (padSentinelStored input) := by
  simp [lengthSentinelStorePath, lengthSentinelPath,
    Artifact.padSentinelPath,
    Challenge.EvmProof.DataStepper.runLocatedBlock,
    Challenge.EvmProof.DataStepper.runLocated, Challenge.EvmProof.DataStepper.runInstr,
    padSentinelStored, State.activeWordsAfterUInt256]

private theorem padSentinelStored_eq (input : ByteArray)
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
  generalize padCopied input = s
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
    pc := UInt256.ofNat 224
    stack := lengthAddr input i :: lengthShift input i :: padFrame input
    memory := lengthLoopMemory input i
    activeWords := lengthLoopActiveWords input i }

def lengthIterationPath : List
    (Challenge.EvmProof.DataStepper.Located Artifact.submissionArtifact .Osaka) :=
  [⟨130, .op .JUMPDEST, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨131, .op (.Dup ⟨1, by decide⟩), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨132, .op (.Dup ⟨1, by decide⟩), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨133, .op .MSTORE8, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨134, .push ⟨1, by decide⟩ (UInt256.ofNat 1), by rfl, by decide⟩,
   ⟨135, .op .ADD, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨136, .op (.Swap ⟨0, by decide⟩), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨137, .push ⟨1, by decide⟩ (UInt256.ofNat 8), by rfl, by decide⟩,
   ⟨138, .op .SHR, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨139, .op (.Swap ⟨0, by decide⟩), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨140, .op (.Dup ⟨1, by decide⟩), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨141, .push ⟨1, by decide⟩ (UInt256.ofNat 224), by rfl, by decide⟩,
   ⟨142, .op .JUMPI, by rfl, wfOp (by decide) trivial rfl⟩]

def lengthBodyPath := lengthIterationPath.take 10
def lengthBranchPath := lengthIterationPath.drop 10

@[simp] private theorem lengthLoopState_halt (input : ByteArray) (i : Nat) :
    (lengthLoopState input i).halt = .Running := by rfl

@[simp] private theorem lengthLoopState_fork (input : ByteArray) (i : Nat) :
    (lengthLoopState input i).fork = .Osaka := by rfl

@[simp] private theorem lengthLoopState_code (input : ByteArray) (i : Nat) :
    (lengthLoopState input i).executionEnv.code = submissionBytecode := by rfl

@[simp] private theorem lengthLoopState_pc (input : ByteArray) (i : Nat) :
    (lengthLoopState input i).pc = UInt256.ofNat 224 := by rfl

@[simp] private theorem lengthLoopState_stack (input : ByteArray) (i : Nat) :
    (lengthLoopState input i).stack =
      lengthAddr input i :: lengthShift input i :: padFrame input := by rfl

@[simp] private theorem padSentinel_code (input : ByteArray) :
    (padSentinel input).executionEnv.code = submissionBytecode := by rfl

/-- State after one low-byte store and both register updates. -/
def lengthSteppedState (input : ByteArray) (i : Nat) : State :=
  { lengthLoopState input i with
    pc := UInt256.ofNat 236
    stack := lengthAddr input (i + 1) :: lengthShift input (i + 1) :: padFrame input
    memory := lengthLoopMemory input (i + 1)
    activeWords := lengthLoopActiveWords input (i + 1) }

def lengthBranchReady (input : ByteArray) (i : Nat) : State :=
  { lengthSteppedState input i with
    pc := UInt256.ofNat 239
    stack := [UInt256.ofNat 224, lengthShift input (i + 1)] ++
      (lengthSteppedState input i).stack }

def lengthBackReturned (input : ByteArray) (i : Nat) : State :=
  { lengthBranchReady input i with
    pc := UInt256.ofNat 224
    stack := (lengthSteppedState input i).stack }

def lengthExitPending (input : ByteArray) (i : Nat) : State :=
  { lengthBranchReady input i with
    pc := UInt256.ofNat 240
    stack := (lengthSteppedState input i).stack }

private theorem lengthBackReturned_eq (input : ByteArray) (i : Nat) :
    lengthBackReturned input i = lengthLoopState input (i + 1) := by
  unfold lengthBackReturned lengthBranchReady lengthSteppedState lengthLoopState
  generalize padSentinel input = s
  cases s
  rfl

@[simp] private theorem lengthSteppedState_halt (input : ByteArray) (i : Nat) :
    (lengthSteppedState input i).halt = .Running := by rfl

@[simp] private theorem lengthSteppedState_pc (input : ByteArray) (i : Nat) :
    (lengthSteppedState input i).pc = UInt256.ofNat 236 := by rfl

@[simp] private theorem lengthBranchReady_halt (input : ByteArray) (i : Nat) :
    (lengthBranchReady input i).halt = .Running := by rfl

@[simp] private theorem lengthBranchReady_pc (input : ByteArray) (i : Nat) :
    (lengthBranchReady input i).pc = UInt256.ofNat 239 := by rfl

@[simp] private theorem lengthSteppedState_code (input : ByteArray) (i : Nat) :
    (lengthSteppedState input i).executionEnv.code = submissionBytecode := by rfl

@[simp] private theorem lengthBranchReady_code (input : ByteArray) (i : Nat) :
    (lengthBranchReady input i).executionEnv.code = submissionBytecode := by rfl

@[simp] private theorem validLengthLoopHead :
    Decode.isValidJumpDest submissionBytecode 224 = true := by
  have hpc : Artifact.submissionArtifact.instructionPC 130 = 224 := by rw [Challenge.Ripemd160.Submission.Proofs.Bytecode.ArtifactByteLength.instructionPC_eq_byteLength]; rfl
  rw [← hpc]
  exact Artifact.submissionArtifact.isValidJumpDest_index 130 (by rfl)

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

private theorem run_lengthBody (input : ByteArray) (_hfit : CalldataFits input)
    (i : Nat) (_hi : i < 9) :
    Challenge.EvmProof.DataStepper.runLocatedBlock lengthBodyPath
      (lengthLoopState input i) = some (lengthSteppedState input i) := by
  simp [lengthBodyPath, lengthIterationPath,
    Challenge.EvmProof.DataStepper.runLocatedBlock,
    Challenge.EvmProof.DataStepper.runLocated, Challenge.EvmProof.DataStepper.runInstr,
    lengthSteppedState, lengthLoopState, lengthLoopMemory, lengthAddr,
    lengthShift, List.exchange, State.activeWordsAfterUInt256,
    lengthLoopActiveWords]

private theorem run_lengthBranchBack (input : ByteArray) (i : Nat)
    (hne : lengthShift input (i + 1) ≠ ⟨0⟩) :
    Challenge.EvmProof.DataStepper.runLocatedBlock lengthBranchPath
      (lengthSteppedState input i) = some (lengthBackReturned input i) := by
  have htrue : UInt256.isTrue (lengthShift input (i + 1)) = true := by
    simp [UInt256.isTrue, toNat_ne_zero_of_ne _ hne]
  simp [lengthBranchPath, lengthIterationPath,
    Challenge.EvmProof.DataStepper.runLocatedBlock,
    Challenge.EvmProof.DataStepper.runLocated, Challenge.EvmProof.DataStepper.runInstr,
    lengthSteppedState, lengthBranchReady, lengthBackReturned, htrue]

private theorem run_lengthBranchExit (input : ByteArray) (i : Nat)
    (hz : lengthShift input (i + 1) = ⟨0⟩) :
    Challenge.EvmProof.DataStepper.runLocatedBlock lengthBranchPath
      (lengthSteppedState input i) = some (lengthExitPending input i) := by
  have hfalse : UInt256.isTrue (lengthShift input (i + 1)) = false := by
    simp [UInt256.isTrue, hz]
  simp [lengthBranchPath, lengthIterationPath,
    Challenge.EvmProof.DataStepper.runLocatedBlock,
    Challenge.EvmProof.DataStepper.runLocated, Challenge.EvmProof.DataStepper.runInstr,
    lengthSteppedState, lengthBranchReady, lengthExitPending, hfalse]

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
    pc := UInt256.ofNat 457
    stack := padFrame input }

private theorem lengthLoopActiveWords_succ_toNat (input : ByteArray)
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
    (padReturned input).pc = UInt256.ofNat 457 := by rfl

@[simp] theorem padReturned_stack (input : ByteArray) :
    (padReturned input).stack = padFrame input := by rfl

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
  { lengthLoopState input i with pc := UInt256.ofNat 240 }

private theorem lengthExitPending_eq (input : ByteArray) (i : Nat) :
    lengthExitPending input i = lengthExitEntered input (i + 1) := by
  unfold lengthExitPending lengthBranchReady lengthSteppedState
    lengthExitEntered lengthLoopState
  generalize padSentinel input = s
  cases s
  rfl

/-- After the two `POP`s the padding code jumps to the block-loop head with the
persistent frame. -/
def lengthExitReturned (input : ByteArray) (i : Nat) : State :=
  { lengthExitEntered input i with
    pc := UInt256.ofNat 457
    stack := padFrame input }

@[simp] private theorem lengthExitEntered_halt (input : ByteArray) (i : Nat) :
    (lengthExitEntered input i).halt = .Running := by rfl

@[simp] private theorem lengthExitEntered_pc (input : ByteArray) (i : Nat) :
    (lengthExitEntered input i).pc = UInt256.ofNat 240 := by rfl

@[simp] private theorem lengthExitEntered_code (input : ByteArray) (i : Nat) :
    (lengthExitEntered input i).executionEnv.code = submissionBytecode := by rfl

set_option maxHeartbeats 400000 in
private theorem run_lengthExitPop (input : ByteArray) (i : Nat) :
    Challenge.EvmProof.DataStepper.runLocatedBlock lengthExitPath
      (lengthExitEntered input i) = some (lengthExitReturned input i) := by
  simp [lengthExitPath, Artifact.padExitPath,
    Challenge.EvmProof.DataStepper.runLocatedBlock,
    Challenge.EvmProof.DataStepper.runLocated, Challenge.EvmProof.DataStepper.runInstr,
    lengthExitEntered, lengthExitReturned, lengthLoopState]

/-! ## The footer window is beyond the sentinel image -/

@[simp] private theorem oneByte_size (b : UInt8) :
    (ByteArray.mk #[b]).size = 1 := rfl

private theorem mod64_div_byte (x j : Nat) (hj : j < 8) :
    x % 2 ^ 64 / 2 ^ (8 * j) % 256 = x / 2 ^ (8 * j) % 256 := by
  have hsplit : (2:Nat) ^ 64 = 2 ^ (8 * j) * 2 ^ (64 - 8 * j) := by
    rw [← Nat.pow_add]; congr 1; omega
  have hdvd : (256:Nat) ∣ 2 ^ (64 - 8 * j) := by
    have h8 : 8 ≤ 64 - 8 * j := by omega
    simpa using Nat.pow_dvd_pow 2 h8
  rw [hsplit, Nat.mod_mul_right_div_self, Nat.mod_mod_of_dvd _ hdvd]

private theorem padLengthReady_size_le (input : ByteArray) :
    (padLengthReady input).memory.size ≤ Padding.messageOffset := by
  exact Nat.zero_le _

private theorem sentinel_size_le (input : ByteArray) (_hfit : CalldataFits input) :
    (padSentinel input).memory.size ≤
      Padding.messageOffset + Padding.paddedLength input.size - 8 := by
  have hbase := padLengthReady_size_le input
  have hlen : input.size + 9 ≤ Padding.paddedLength input.size := by
    unfold Padding.paddedLength
    omega
  rw [padSentinel, padCopied, padCopyDone]
  rw [MachineState.writeBytes_size, MachineState.writeBytes_size]
  simp only [Challenge.EvmProof.Memory.readPadded_size, oneByte_size]
  split <;> split <;>
    unfold Padding.messageOffset at hbase ⊢ <;> omega

/-! ## Final footer image -/

theorem lengthBytes_of_shift_zero (input : ByteArray) (hfit : CalldataFits input)
    (i j : Nat) (hij : i ≤ j) (hj : j < 8) (hz : lengthShift input i = ⟨0⟩) :
    (Padding.lengthBytes input)[j]?.getD 0 = 0 := by
  have hzn : input.size * 8 / 2 ^ (8 * i) = 0 := by
    have := lengthShift_toNat input hfit i
    rw [hz] at this
    simpa using this.symm
  have hlt : input.size * 8 < 2 ^ (8 * i) := by
    exact Nat.lt_of_div_eq_zero (by positivity) hzn
  rw [Challenge.EvmProof.Memory.getD0_eq_getElem _ _
    (by simpa using hj : j < (Padding.lengthBytes input).size),
    Padding.lengthByte input j hj]
  have : input.size * 8 / 2 ^ (8 * j) = 0 := by
    apply Nat.div_eq_of_lt
    exact Nat.lt_of_lt_of_le hlt (Nat.pow_le_pow_right (by norm_num) (by omega))
  rw [this]
  rfl

theorem topByte_eq (input : ByteArray) (hfit : CalldataFits input) :
    UInt8.ofNat ((topByteWord input).toNat % 256) =
      (Padding.lengthBytes input)[7]?.getD 0 := by
  have hlt : (bitLengthWord input).toNat < 2 ^ 256 := (bitLengthWord input).val.isLt
  have hshift : (topByteWord input).toNat = input.size * 8 / 2 ^ 56 := by
    rw [topByteWord,
      Challenge.EvmProof.Word.word_eq_ofNat_toNat (bitLengthWord input),
      Challenge.EvmProof.Word.shiftRight_ofNat hlt (by norm_num : (0x38 : Nat) < 256),
      Challenge.EvmProof.Word.word_toNat_ofNat, Nat.shiftRight_eq_div_pow,
      bitLengthWord_toNat input hfit]
    rw [Nat.mod_eq_of_lt]
    have hbits : input.size * 8 < 2 ^ 256 := by
      have hto := bitLengthWord_toNat input hfit
      omega
    exact Nat.lt_of_le_of_lt (Nat.div_le_self _ _) hbits
  rw [hshift,
    Challenge.EvmProof.Memory.getD0_eq_getElem _ _
      (by simp : (7 : Nat) < (Padding.lengthBytes input).size),
    Padding.lengthByte input 7 (by norm_num)]

theorem lengthShift_byte_eq (input : ByteArray) (hfit : CalldataFits input)
    (i : Nat) (hi : i < 8) :
    UInt8.ofNat ((lengthShift input i).toNat % 256) =
      (Padding.lengthBytes input)[i]?.getD 0 := by
  rw [lengthShift_toNat input hfit i,
    Challenge.EvmProof.Memory.getD0_eq_getElem _ _
      (by simpa using hi : i < (Padding.lengthBytes input).size),
    Padding.lengthByte input i hi]

/-- Pointwise image of the footer memory after `i` loop steps. -/
theorem lengthLoopMemory_getD (input : ByteArray) (hfit : CalldataFits input)
    (i : Nat) (hi : i ≤ 9) (a : Nat) :
    (lengthLoopMemory input i)[a]?.getD 0 =
      if (Padding.messageOffset + Padding.paddedLength input.size - 8) ≤ a ∧ a < (Padding.messageOffset + Padding.paddedLength input.size - 8) + i then
        if a - (Padding.messageOffset + Padding.paddedLength input.size - 8) < 8 then
          (Padding.lengthBytes input)[a - (Padding.messageOffset + Padding.paddedLength input.size - 8)]?.getD 0
        else UInt8.ofNat ((lengthShift input 8).toNat % 256)
      else (padSentinel input).memory[a]?.getD 0 := by
  induction i with
  | zero =>
      have hzero : ¬ ((Padding.messageOffset + Padding.paddedLength input.size - 8) ≤ a ∧
          a < (Padding.messageOffset + Padding.paddedLength input.size - 8) + 0) := by
        omega
      rw [lengthLoopMemory, if_neg hzero]
  | succ i ih =>
      have hii : i < 9 := by omega
      rw [lengthLoopMemory, MachineState.writeBytes_getElem?_getD,
        lengthAddr_toNat input hfit i (by omega)]
      simp only [oneByte_size]
      by_cases h8 : i < 8
      · rw [lengthShift_byte_eq input hfit i h8, ih (by omega)]
        by_cases hin : (Padding.messageOffset + Padding.paddedLength input.size - 8) + i ≤ a ∧ a < (Padding.messageOffset + Padding.paddedLength input.size - 8) + i + 1
        · have haeq : a = (Padding.messageOffset + Padding.paddedLength input.size - 8) + i := by omega
          subst haeq
          simp [h8]
          rfl
        · rw [if_neg (by omega)]
          by_cases hlt : (Padding.messageOffset + Padding.paddedLength input.size - 8) ≤ a ∧ a < (Padding.messageOffset + Padding.paddedLength input.size - 8) + i
          · rw [if_pos hlt, if_pos (by omega), if_pos (by omega)]
          · have hne : ¬ ((Padding.messageOffset + Padding.paddedLength input.size - 8) ≤ a ∧ a < (Padding.messageOffset + Padding.paddedLength input.size - 8) + (i + 1)) := by
              omega
            rw [if_neg hlt, if_neg hne]
      · have hi8 : i = 8 := by omega
        subst hi8
        rw [ih (by omega)]
        by_cases hin : (Padding.messageOffset + Padding.paddedLength input.size - 8) + 8 ≤ a ∧ a < (Padding.messageOffset + Padding.paddedLength input.size - 8) + 8 + 1
        · have haeq : a = (Padding.messageOffset + Padding.paddedLength input.size - 8) + 8 := by omega
          subst haeq
          simp
          rfl
        · rw [if_neg (by omega)]
          by_cases hlt : (Padding.messageOffset + Padding.paddedLength input.size - 8) ≤ a ∧ a < (Padding.messageOffset + Padding.paddedLength input.size - 8) + 8
          · rw [if_pos hlt, if_pos (by omega), if_pos (by omega)]
          · have hne : ¬ ((Padding.messageOffset + Padding.paddedLength input.size - 8) ≤ a ∧ a < (Padding.messageOffset + Padding.paddedLength input.size - 8) + 9) := by
              omega
            rw [if_neg hlt, if_neg hne]

theorem padFinalMemory_getD (input : ByteArray) (_hfit : CalldataFits input) (a : Nat)
    (ha : a < Padding.messageOffset + Padding.paddedLength input.size) :
    (padFinalMemory input)[a]?.getD 0 =
      if (Padding.messageOffset + Padding.paddedLength input.size - 8) ≤ a ∧ a < (Padding.messageOffset + Padding.paddedLength input.size - 8) + 8 then
        (Padding.lengthBytes input)[a - (Padding.messageOffset + Padding.paddedLength input.size - 8)]?.getD 0
      else (padSentinel input).memory[a]?.getD 0 := by
  have hstop : lengthStop input ≤ 9 := lengthStop_le input
  have hzero := lengthShift_stop_zero input _hfit
  change (lengthLoopMemory input (lengthStop input))[a]?.getD 0 = _
  rw [lengthLoopMemory_getD input _hfit (lengthStop input) hstop a]
  by_cases hin :
      (Padding.messageOffset + Padding.paddedLength input.size - 8) ≤ a ∧
        a < (Padding.messageOffset + Padding.paddedLength input.size - 8) + lengthStop input
  · rw [if_pos hin, if_pos (by omega), if_pos (by omega)]
  · rw [if_neg hin]
    by_cases hfull :
        (Padding.messageOffset + Padding.paddedLength input.size - 8) ≤ a ∧
          a < (Padding.messageOffset + Padding.paddedLength input.size - 8) + 8
    · rw [if_pos hfull]
      have hj : a - (Padding.messageOffset + Padding.paddedLength input.size - 8) < 8 := by
        omega
      have hij : lengthStop input ≤
          a - (Padding.messageOffset + Padding.paddedLength input.size - 8) := by
        omega
      have hbyte := lengthBytes_of_shift_zero input _hfit (lengthStop input)
        (a - (Padding.messageOffset + Padding.paddedLength input.size - 8)) hij hj hzero
      have hs := sentinel_size_le input _hfit
      have hsent := Challenge.EvmProof.Memory.getElem?_getD_eq_zero_of_size_le
        (padSentinel input).memory a (by omega)
      rw [hsent, hbyte]
    · rw [if_neg hfull]

theorem padFinalMemory_getD_paddedMemory (input : ByteArray)
    (hfit : CalldataFits input) (a : Nat)
    (ha : a < Padding.messageOffset + Padding.paddedLength input.size) :
    (padFinalMemory input)[a]?.getD 0 =
      (Padding.paddedMemory (padLengthReady input).memory input)[a]?.getD 0 := by
  have hsentinel : (padSentinel input).memory =
      Padding.sentinelMemory (padLengthReady input).memory input := by
    simp [padSentinel, padCopied, padCopyDone, Padding.sentinelMemory,
      Padding.copiedMemory, Challenge.EvmProof.Memory.readPadded_zero_size]
  rw [padFinalMemory_getD input hfit a ha, Padding.paddedMemory,
    MachineState.writeBytes_getElem?_getD, hsentinel]
  simp only [Padding.lengthBytes_size]

theorem padReturned_memory (input : ByteArray) (_hfit : CalldataFits input) :
    (padReturned input).memory = padFinalMemory input := by
  rfl

theorem padReturned_readPadded (input : ByteArray) (hfit : CalldataFits input)
    (a n : Nat) (ha : a + n ≤ Padding.messageOffset + Padding.paddedLength input.size) :
    MachineState.readPadded (padReturned input).memory a n =
      MachineState.readPadded
        (Padding.paddedMemory (padLengthReady input).memory input) a n := by
  apply Challenge.EvmProof.Memory.readPadded_congr
  intro i hi
  rw [padReturned_memory input hfit]
  exact padFinalMemory_getD_paddedMemory input hfit (a + i) (by omega)

theorem padReturned_readWord (input : ByteArray) (hfit : CalldataFits input)
    (a : Nat) (ha : a + 32 ≤ Padding.messageOffset + Padding.paddedLength input.size) :
    MachineState.readWord (padReturned input).memory a =
      MachineState.readWord
        (Padding.paddedMemory (padLengthReady input).memory input) a := by
  unfold MachineState.readWord
  rw [padReturned_readPadded input hfit a 32 ha]

theorem padReturned_getD_window (input : ByteArray) (hfit : CalldataFits input)
    (a : Nat) (ha : a < Padding.messageOffset + Padding.paddedLength input.size) :
    (padReturned input).memory[a]?.getD 0 =
      (Padding.paddedMemory (padLengthReady input).memory input)[a]?.getD 0 := by
  rw [padReturned_memory input hfit]
  exact padFinalMemory_getD_paddedMemory input hfit a ha

theorem lengthLoopMemory_size (input : ByteArray) (hfit : CalldataFits input)
    (i : Nat) (hi : i ≤ 9) :
    (lengthLoopMemory input i).size =
      if i = 0 then (padSentinel input).memory.size
      else (Padding.messageOffset + Padding.paddedLength input.size - 8) + i := by
  induction i with
  | zero =>
      simp [lengthLoopMemory]
  | succ i ih =>
      have hii : i < 9 := by omega
      rw [lengthLoopMemory, MachineState.writeBytes_size,
        lengthAddr_toNat input hfit i (by omega), ih (by omega)]
      simp only [oneByte_size, if_neg (by decide : ¬ (1 = 0))]
      by_cases hi0 : i = 0
      · subst i
        have hs := sentinel_size_le input hfit
        simp at ih ⊢
        omega
      · simp only [if_neg hi0]
        simp at ih ⊢
        omega

theorem padFinalMemory_size (input : ByteArray) (hfit : CalldataFits input) :
    (padFinalMemory input).size =
      footerStart input + lengthStop input := by
  have hstop : lengthStop input ≤ 9 := lengthStop_le input
  have hs := lengthLoopMemory_size input hfit (lengthStop input) hstop
  have hstop0 : lengthStop input ≠ 0 := Nat.ne_of_gt (lengthStop_pos input)
  change (lengthLoopMemory input (lengthStop input)).size = _
  unfold footerStart
  rw [hs, if_neg hstop0]

theorem lengthLoopMemory_final_at_stop (input : ByteArray) :
    lengthLoopMemory input (lengthStop input) = padFinalMemory input := by
  rfl

private theorem lengthExitReturned_eq_stop (input : ByteArray)
    (_hfit : CalldataFits input) :
    lengthExitReturned input (lengthStop input) = padReturned input := by
  unfold lengthExitReturned lengthExitEntered padReturned
  rfl

def gasSteps_lengthExitEntered (input : ByteArray) (i : Nat) :
    Challenge.EvmProof.GasSteps (lengthExitEntered input i)
      (lengthExitReturned input i) := by
  have g1raw := Challenge.EvmProof.DataStepper.runLocatedBlock_sound
    Artifact.submissionArtifact .Osaka lengthExitPath (by rfl) (by rfl)
    (run_lengthExitPop input i) (by rfl) (by rfl)
  exact Challenge.EvmProof.GasSteps.cast g1raw rfl rfl

def gasSteps_lengthIterationExit (input : ByteArray) (hfit : CalldataFits input)
    (i : Nat) (hi : i < 9) (hz : lengthShift input (i + 1) = ⟨0⟩) :
    Challenge.EvmProof.GasSteps (lengthLoopState input i)
      (lengthExitReturned input (i + 1)) := by
  have g₁ := Challenge.EvmProof.DataStepper.runLocatedBlock_sound
    Artifact.submissionArtifact .Osaka lengthBodyPath (by rfl) (by rfl)
    (run_lengthBody input hfit i hi) (by rfl) (by rfl)
  have g2raw := Challenge.EvmProof.DataStepper.runLocatedBlock_sound
    Artifact.submissionArtifact .Osaka lengthBranchPath (by rfl) (by rfl)
    (run_lengthBranchExit input i hz) (by rfl) (by rfl)
  have g₂ := Challenge.EvmProof.GasSteps.cast g2raw rfl
    (lengthExitPending_eq input i)
  exact g₁.trans (g₂.trans
    (gasSteps_lengthExitEntered input (i + 1)))

/-- Run the footer loop from a known nonzero residual with bounded shifts left. -/
noncomputable def gasSteps_lengthLoopFrom (input : ByteArray)
    (hfit : CalldataFits input) :
    (fuel i : Nat) → i + fuel = 9 →
      (∀ j, 0 < j → j ≤ i → lengthShift input j ≠ ⟨0⟩) →
      lengthShift input i ≠ ⟨0⟩ →
    Challenge.EvmProof.GasSteps (lengthLoopState input i) (padReturned input)
  | 0, i, hsum, _hprior, hne => by
      have hi : i = 9 := by omega
      subst hi
      exact False.elim (hne (lengthShift_nine input hfit))
  | fuel + 1, i, hsum, hprior, hne =>
      if hz : lengthShift input (i + 1) = ⟨0⟩ then
        have hstop := lengthStop_eq_succ_of_nonzero input i (by omega) hprior hz
        have hret : lengthExitReturned input (i + 1) = padReturned input := by
          rw [← hstop]
          exact lengthExitReturned_eq_stop input hfit
        Challenge.EvmProof.GasSteps.cast
          (gasSteps_lengthIterationExit input hfit i (by omega) hz) rfl hret
      else
        have hprior' : ∀ j, 0 < j → j ≤ i + 1 →
            lengthShift input j ≠ ⟨0⟩ := by
          intro j hj hjle
          by_cases hji : j ≤ i
          · exact hprior j hj hji
          · have hjeq : j = i + 1 := by omega
            subst hjeq
            exact hz
        (gasSteps_lengthIteration input hfit i (by omega) hz).trans
          (gasSteps_lengthLoopFrom input hfit fuel (i + 1) (by omega)
            hprior' hz)

noncomputable def gasSteps_lengthLoop (input : ByteArray) (hfit : CalldataFits input) :
    Challenge.EvmProof.GasSteps (lengthLoopState input 0) (padReturned input) :=
  if hz : lengthShift input 1 = ⟨0⟩ then
    have hstop := lengthStop_eq_succ_of_nonzero input 0 (by norm_num)
      (fun j hj hle => by omega) hz
    have hstop' : lengthStop input = 1 := by simpa using hstop
    have hret : lengthExitReturned input 1 = padReturned input := by
      rw [← hstop']
      exact lengthExitReturned_eq_stop input hfit
    Challenge.EvmProof.GasSteps.cast
      (gasSteps_lengthIterationExit input hfit 0 (by norm_num) hz) rfl hret
  else
    (gasSteps_lengthIteration input hfit 0 (by norm_num) hz).trans
      (gasSteps_lengthLoopFrom input hfit 8 1 (by norm_num)
        (fun j hj hle => by
          have hj1 : j = 1 := by omega
          subst hj1
          exact hz) hz)

set_option maxHeartbeats 800000 in
private theorem run_lengthFooterSetup (input : ByteArray) :
    Challenge.EvmProof.DataStepper.runLocatedBlock lengthFooterSetupPath
      (padSentinel input) = some (lengthLoopState input 0) := by
  have haddressOrder : UInt256.ofNat 25 + PadLimitArithmetic.coldRounded (UInt256.ofNat input.size) =
      PadLimitArithmetic.coldRounded (UInt256.ofNat input.size) + UInt256.ofNat 25 :=
    Challenge.EvmProof.Word.word_add_comm _ _
  simp [lengthFooterSetupPath, Artifact.padFooterSetupPath,
    Challenge.EvmProof.DataStepper.runLocatedBlock,
    Challenge.EvmProof.DataStepper.runLocated, Challenge.EvmProof.DataStepper.runInstr,
    lengthLoopState, lengthLoopMemory, lengthLoopActiveWords,
    lengthAddr, lengthShift, padFrame, StaggerPersistentFrame.frame,
    lengthOffsetWord, bitLengthWord, haddressOrder]

def gasSteps_lengthSetup (input : ByteArray) (hfit : CalldataFits input) :
    Challenge.EvmProof.GasSteps (padGuardMiss input)
      (lengthLoopState input 0) := by
  have g₂ₐ := Challenge.EvmProof.DataStepper.runLocatedBlock_sound
    Artifact.submissionArtifact .Osaka lengthSentinelAddressPath (by rfl) (by rfl)
    (run_lengthSentinelAddress input) (by rfl) deployAddress_not_precompile
  have g2raw := Challenge.EvmProof.DataStepper.runLocatedBlock_sound
    Artifact.submissionArtifact .Osaka lengthSentinelStorePath (by rfl) (by rfl)
    (run_lengthSentinelStore input hfit) (by rfl) deployAddress_not_precompile
  have g2b := Challenge.EvmProof.GasSteps.cast g2raw rfl
    (padSentinelStored_eq input hfit)
  have g₃ := Challenge.EvmProof.DataStepper.runLocatedBlock_sound
    Artifact.submissionArtifact .Osaka lengthFooterSetupPath (by rfl) (by rfl)
    (run_lengthFooterSetup input) (by rfl) deployAddress_not_precompile
  exact g₂ₐ.trans (g2b.trans g₃)

def gasSteps_lengthReady (input : ByteArray) :
    Challenge.EvmProof.GasSteps (padEntry input) (padLengthReady input) :=
  Challenge.EvmProof.GasSteps.refl _

def gasSteps_lengthCopy (input : ByteArray) (hfit : CalldataFits input) :
    Challenge.EvmProof.GasSteps (padLengthReady input) (padCopyDone input) :=
  Challenge.EvmProof.DataStepper.runLocatedBlock_sound
    Artifact.submissionArtifact .Osaka lengthCopyPath (by rfl) (by rfl)
    (run_lengthCopy input hfit) (by rfl) deployAddress_not_precompile

/-- `MSIZE` after the copy pushes the raw loop limit `1056 + ceil32 size`. -/
def gasSteps_msizeTail (input : ByteArray) (rho : List UInt256) (hcap : rho.length ≤ 20) :
    Challenge.EvmProof.GasSteps (StackTail.append (padCopyDone input) rho)
      (StackTail.append (padCopied input) rho) := by
  let s := StackTail.append (padCopyDone input) rho
  have hd := Artifact.submissionArtifact.decodeAt_op_index 154 .MSIZE (by rfl) (by decide) trivial
  have hp : s.pc.toNat = Artifact.submissionArtifact.instructionPC 154 := by
    rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl
  have hop : s.decodedOp = some .MSIZE :=
    Artifact.submissionArtifact.state_decodedOp_of s 154 rfl hp .MSIZE none hd rfl
  have g := Msize.step hop (by
      change (StackTail.append (padCopyDone input) rho).stack.length < 1024
      simp [StackTail.append, padCopyDone, padLengthReady, padEntry]; omega)
    rfl deployAddress_not_precompile
  exact g.cast rfl (by
    simp [s, StackTail.append, padCopied, padCopyDone, copiedLimit, Challenge.EvmProof.Word.succ_ofNat_mod,
      Challenge.EvmProof.Word.word_toNat_ofNat])

def gasSteps_msize (input : ByteArray) :
    Challenge.EvmProof.GasSteps (padCopyDone input) (padCopied input) := by
  let s := padCopyDone input
  have hd := Artifact.submissionArtifact.decodeAt_op_index 154 .MSIZE (by rfl) (by decide) trivial
  have hp : s.pc.toNat = Artifact.submissionArtifact.instructionPC 154 := by
    rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl
  have hop : s.decodedOp = some .MSIZE :=
    Artifact.submissionArtifact.state_decodedOp_of s 154 rfl hp .MSIZE none hd rfl
  have g := Msize.step hop (by
      change (padCopyDone input).stack.length < 1024
      simp [padCopyDone, padLengthReady, padEntry])
    rfl deployAddress_not_precompile
  exact g.cast rfl (by
    simp [s, padCopied, padCopyDone, copiedLimit, Challenge.EvmProof.Word.succ_ofNat_mod,
      Challenge.EvmProof.Word.word_toNat_ofNat])

/-- Complete certified execution from the challenge initial state through the
calldata copy and the frame pushes. -/
private def gasSteps_padPrefix (input : ByteArray) (hfit : CalldataFits input)
    (entryPrefix : Challenge.EvmProof.GasSteps (initialState submissionBytecode input 0)
      (Execution.atPC input 247)) :
    Challenge.EvmProof.GasSteps (initialState submissionBytecode input 0)
      (padFramed input) :=
  (Main.gasSteps_initialize input entryPrefix).trans
    ((gasSteps_enterPad input).trans ((gasSteps_lengthReady input).trans
      ((gasSteps_lengthCopy input hfit).trans ((gasSteps_msize input).trans (gasSteps_push input)))))

noncomputable def gasSteps_padBody (input : ByteArray) (hfit : CalldataFits input)
    (hn32 : input.size ≠ 32) (hnz : ¬ (input.size % 64 = 0 ∧ input.size < 256)) :
    Challenge.EvmProof.GasSteps (padFramed input) (padReturned input) :=
  (gasSteps_guardMiss input hfit hn32 hnz).trans
    ((gasSteps_lengthSetup input hfit).trans (gasSteps_lengthLoop input hfit))

/-- Block-loop entry state.  A fast-entry input skips the sentinel and footer stores: its
pad-only block is scheduled from the table and never reads message memory.  Every other
input (including whole-block inputs of 256 bytes or more) writes the sentinel and footer. -/
def entryState (input : ByteArray) : State :=
  if input.size % 64 = 0 ∧ input.size < 256 then padSkip input else padReturned input

theorem entryState_skip (input : ByteArray) (hz : input.size % 64 = 0 ∧ input.size < 256) :
    entryState input = padSkip input := by
  unfold entryState
  rw [if_pos hz]

theorem entryState_miss (input : ByteArray) (hnz : ¬ (input.size % 64 = 0 ∧ input.size < 256)) :
    entryState input = padReturned input := by
  unfold entryState
  rw [if_neg hnz]

theorem entryState_eta (input : ByteArray) :
    entryState input = {entryState input with
      pc := UInt256.ofNat (if input.size % 64 = 0 ∧ input.size < 256 then 456 else 457)
      stack := if input.size % 64 = 0 ∧ input.size < 256 then initialFrame input else padFrame input} := by
  by_cases hz : input.size % 64 = 0 ∧ input.size < 256
  · simp only [entryState_skip input hz, if_pos hz]
    rfl
  · simp only [entryState_miss input hz, if_neg hz]
    rfl

noncomputable def gasSteps_pad (input : ByteArray) (hfit : CalldataFits input)
    (hn32 : input.size ≠ 32)
    (entryPrefix : Challenge.EvmProof.GasSteps (initialState submissionBytecode input 0)
      (Execution.atPC input 247)) :
    Challenge.EvmProof.GasSteps (initialState submissionBytecode input 0)
      (entryState input) :=
  if hz : input.size % 64 = 0 ∧ input.size < 256 then
    Challenge.EvmProof.GasSteps.cast
      ((gasSteps_padPrefix input hfit entryPrefix).trans (gasSteps_guardSkip input hfit hz))
      rfl (entryState_skip input hz).symm
  else
    Challenge.EvmProof.GasSteps.cast
      ((gasSteps_padPrefix input hfit entryPrefix).trans (gasSteps_padBody input hfit hn32 hz))
      rfl (entryState_miss input hz).symm


/-! Stack suffix adapters reuse the established symbolic path evaluations. -/
private def liftTail (path : List (Challenge.EvmProof.DataStepper.Located
    Artifact.submissionArtifact .Osaka)) {s t : State}
    (hr : Challenge.EvmProof.DataStepper.runLocatedBlock path s = some t)
    (hsize : s.stack.length + path.length ≤ 100)
    (rho : List UInt256) (hcap : rho.length ≤ 20)
    (hcode : s.executionEnv.code = Artifact.submissionArtifact.code)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    Challenge.EvmProof.GasSteps (StackTail.append s rho) (StackTail.append t rho) :=
  StackTail.gasSteps path rho (by omega) hr hcode hfork hrun hnp

def tail_enter (input : ByteArray)
    (rho : List UInt256) (hcap : rho.length ≤ 20) :
    Challenge.EvmProof.GasSteps (StackTail.append (Main.initializedState input) rho)
      (StackTail.append (padEntry input) rho) :=
  liftTail enterPath (run_enter input) (by change 2 ≤ 100; decide) rho hcap rfl rfl rfl deployAddress_not_precompile

def tail_length (input : ByteArray)
    (rho : List UInt256) (_hcap : rho.length ≤ 20) :
    Challenge.EvmProof.GasSteps (StackTail.append (padEntry input) rho)
      (StackTail.append (padLengthReady input) rho) :=
  Challenge.EvmProof.GasSteps.refl _

def tail_copy (input : ByteArray) (hfit : CalldataFits input)
    (rho : List UInt256) (hcap : rho.length ≤ 20) :
    Challenge.EvmProof.GasSteps (StackTail.append (padLengthReady input) rho)
      (StackTail.append (padCopied input) rho) :=
  (liftTail lengthCopyPath (run_lengthCopy input hfit) (by change 6 ≤ 100; decide) rho hcap rfl rfl rfl
    deployAddress_not_precompile).trans (gasSteps_msizeTail input rho hcap)

def tail_guardSkip (input : ByteArray) (hfit : CalldataFits input) (hz : input.size % 64 = 0 ∧ input.size < 256)
    (rho : List UInt256) (hcap : rho.length ≤ 20) :
    Challenge.EvmProof.GasSteps (StackTail.append (padFramed input) rho)
      (StackTail.append (padSkip input) rho) :=
  liftTail guardPath (run_guardSkip input hfit hz) (by change 21 ≤ 100; decide) rho hcap rfl rfl rfl deployAddress_not_precompile

def tail_guardTaken (input : ByteArray) (hfit : CalldataFits input) (hnz : ¬ (input.size % 64 = 0 ∧ input.size < 256))
    (rho : List UInt256) (hcap : rho.length ≤ 20) :
    Challenge.EvmProof.GasSteps (StackTail.append (padFramed input) rho)
      (StackTail.append (padGuardTaken input) rho) :=
  liftTail guardPath (run_guardMiss input hfit hnz) (by change 21 ≤ 100; decide) rho hcap rfl rfl rfl deployAddress_not_precompile

def tail_sentinelAddress (input : ByteArray)
    (rho : List UInt256) (hcap : rho.length ≤ 20) :
    Challenge.EvmProof.GasSteps (StackTail.append (padGuardMiss input) rho)
      (StackTail.append (padSentinelAddressReady input) rho) :=
  liftTail lengthSentinelAddressPath (run_lengthSentinelAddress input) (by change 19 ≤ 100; decide) rho hcap rfl rfl rfl deployAddress_not_precompile

def tail_sentinelStore (input : ByteArray) (hfit : CalldataFits input)
    (rho : List UInt256) (hcap : rho.length ≤ 20) :
    Challenge.EvmProof.GasSteps (StackTail.append (padSentinelAddressReady input) rho)
      (StackTail.append (padSentinelStored input) rho) :=
  liftTail lengthSentinelStorePath (run_lengthSentinelStore input hfit) (by change 18 ≤ 100; decide) rho hcap rfl rfl rfl deployAddress_not_precompile

def tail_footer (input : ByteArray)
    (rho : List UInt256) (hcap : rho.length ≤ 20) :
    Challenge.EvmProof.GasSteps (StackTail.append (padSentinel input) rho)
      (StackTail.append (lengthLoopState input 0) rho) :=
  liftTail lengthFooterSetupPath (run_lengthFooterSetup input) (by change 21 ≤ 100; decide) rho hcap rfl rfl rfl deployAddress_not_precompile

def tail_body (input : ByteArray) (hfit : CalldataFits input) (i : Nat) (hi : i < 9)
    (rho : List UInt256) (hcap : rho.length ≤ 20) :
    Challenge.EvmProof.GasSteps (StackTail.append (lengthLoopState input i) rho)
      (StackTail.append (lengthSteppedState input i) rho) :=
  liftTail lengthBodyPath (run_lengthBody input hfit i hi) (by change 27 ≤ 100; decide) rho hcap rfl rfl rfl deployAddress_not_precompile

def tail_back (input : ByteArray) (i : Nat) (hne : lengthShift input (i + 1) ≠ ⟨0⟩)
    (rho : List UInt256) (hcap : rho.length ≤ 20) :
    Challenge.EvmProof.GasSteps (StackTail.append (lengthSteppedState input i) rho)
      (StackTail.append (lengthBackReturned input i) rho) :=
  liftTail lengthBranchPath (run_lengthBranchBack input i hne) (by change 20 ≤ 100; decide) rho hcap rfl rfl rfl deployAddress_not_precompile

def tail_exitBranch (input : ByteArray) (i : Nat) (hz : lengthShift input (i + 1) = ⟨0⟩)
    (rho : List UInt256) (hcap : rho.length ≤ 20) :
    Challenge.EvmProof.GasSteps (StackTail.append (lengthSteppedState input i) rho)
      (StackTail.append (lengthExitPending input i) rho) :=
  liftTail lengthBranchPath (run_lengthBranchExit input i hz) (by change 20 ≤ 100; decide) rho hcap rfl rfl rfl deployAddress_not_precompile

def tail_exitPop (input : ByteArray) (i : Nat)
    (rho : List UInt256) (hcap : rho.length ≤ 20) :
    Challenge.EvmProof.GasSteps (StackTail.append (lengthExitEntered input i) rho)
      (StackTail.append (lengthExitReturned input i) rho) :=
  liftTail lengthExitPath (run_lengthExitPop input i) (by change 21 ≤ 100; decide) rho hcap rfl rfl rfl deployAddress_not_precompile

theorem tail_sentinel_eq (input : ByteArray) (hfit : CalldataFits input) : padSentinelStored input = padSentinel input := padSentinelStored_eq input hfit

theorem tail_back_eq (input : ByteArray) (i : Nat) : lengthBackReturned input i = lengthLoopState input (i + 1) := lengthBackReturned_eq input i

theorem tail_exit_eq (input : ByteArray) (i : Nat) : lengthExitPending input i = lengthExitEntered input (i + 1) := lengthExitPending_eq input i

theorem tail_returned_eq (input : ByteArray) (hfit : CalldataFits input) : lengthExitReturned input (lengthStop input) = padReturned input := lengthExitReturned_eq_stop input hfit

#print axioms gasSteps_pad

end Challenge.Ripemd160.Submission.Proofs.Bytecode.PaddingTrace
