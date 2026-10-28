import Challenge.Ripemd160.Submission.Local20261028.ColdPaddingCore1
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

/-- The frame of the cold padding code: the cold block installed the output entry 9949 in slot 12. -/
def padFrame (_input : ByteArray) : List UInt256 :=
  StaggerPersistentFrame.frame StackRunBridge.initialHashState (UInt256.ofNat 1056)
    (UInt256.ofNat 9949) [DenseScheduleTemplate.mask8, DenseScheduleTemplate.mask16]

@[simp] theorem padFrame_length (input : ByteArray) : (padFrame input).length = 15 := by
  simp [padFrame, StaggerPersistentFrame.frame]

/-- The frame the padding code leaves at the block-loop head: the generic continuation 48 (the
last-block test) replaces the output entry in slot 12. -/
def glFrame : List UInt256 :=
  StaggerPersistentFrame.frame StackRunBridge.initialHashState (UInt256.ofNat 1056)
    (UInt256.ofNat 222) [DenseScheduleTemplate.mask8, DenseScheduleTemplate.mask16]

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
    pc := UInt256.ofNat 9998
    stack := padFrame input }

/-- The state the 32-byte block leaves at the sentinel store 166: scratch bytes 165 and 188 are
still written (nothing undoes them; they lie outside the message and the block loop's zero band). -/
def padDirty (input : ByteArray) : State :=
  { padGuardMiss input with
    memory := Control.ColdGuardFixup.wMemory (padGuardMiss input).memory
      Control.ColdGuardFixup.dirtyB Control.ColdGuardFixup.dirtyC }

def padSentinel (input : ByteArray) : State :=
  { padDirty input with
    pc := UInt256.ofNat 10004
    stack := padFrame input
    memory := MachineState.writeBytes (padDirty input).memory
      (ByteArray.mk #[0x80]) (Padding.messageOffset + input.size)
    activeWords := (padDirty input).activeWordsAfterUInt256
      (Padding.messageOffset + input.size) 1 }

@[simp] theorem padCopied_halt (input : ByteArray) :
    (padCopied input).halt = .Running := by rfl

@[simp] theorem padCopied_pcToNat (input : ByteArray) :
    (padCopied input).pc.toNat = 319 := by rfl

@[simp] theorem padCopied_pc (input : ByteArray) :
    (padCopied input).pc = UInt256.ofNat 319 := by rfl

@[simp] theorem padCopied_stack (input : ByteArray) :
    (padCopied input).stack =
      [UInt256.ofNat 1056, copiedLimit input, DenseScheduleTemplate.mask8, DenseScheduleTemplate.mask16] := by
  rfl

@[simp] theorem padCopied_calldata (input : ByteArray) :
    (padCopied input).executionEnv.calldata = input := by rfl

@[simp] theorem padCopied_code (input : ByteArray) :
    (padCopied input).executionEnv.code = submissionBytecode := by rfl

@[simp] theorem padFramed_halt (input : ByteArray) :
    (padFramed input).halt = .Running := by rfl

@[simp] theorem padFramed_pc (input : ByteArray) :
    (padFramed input).pc = UInt256.ofNat 447 := by rfl

@[simp] theorem padFramed_code (input : ByteArray) :
    (padFramed input).executionEnv.code = submissionBytecode := by rfl

@[simp] theorem padFramed_calldata (input : ByteArray) :
    (padFramed input).executionEnv.calldata = input := by rfl

@[simp] theorem padGuardMiss_halt (input : ByteArray) :
    (padGuardMiss input).halt = .Running := by rfl

@[simp] theorem padGuardMiss_pc (input : ByteArray) :
    (padGuardMiss input).pc = UInt256.ofNat 9998 := by rfl

@[simp] theorem padGuardMiss_code (input : ByteArray) :
    (padGuardMiss input).executionEnv.code = submissionBytecode := by rfl

@[simp] theorem padGuardMiss_calldata (input : ByteArray) :
    (padGuardMiss input).executionEnv.calldata = input := by rfl

@[simp] theorem padDirty_halt (input : ByteArray) :
    (padDirty input).halt = .Running := by rfl

@[simp] theorem padDirty_pc (input : ByteArray) :
    (padDirty input).pc = UInt256.ofNat 9998 := by rfl

@[simp] theorem padDirty_code (input : ByteArray) :
    (padDirty input).executionEnv.code = submissionBytecode := by rfl

@[simp] theorem padDirty_calldata (input : ByteArray) :
    (padDirty input).executionEnv.calldata = input := by rfl

@[simp] theorem padSentinel_halt (input : ByteArray) :
    (padSentinel input).halt = .Running := by rfl

@[simp] theorem padSentinel_pcToNat (input : ByteArray) :
    (padSentinel input).pc.toNat = 10004 := by rfl

@[simp] theorem padSentinel_pc (input : ByteArray) :
    (padSentinel input).pc = UInt256.ofNat 10004 := by rfl

@[simp] theorem padSentinel_pcSucc (input : ByteArray) :
    (padSentinel input).pc.succ = UInt256.ofNat 10005 := by
  rw [padSentinel_pc, Challenge.EvmProof.Word.succ_ofNat (by norm_num)]

@[simp] theorem padSentinel_stack (input : ByteArray) :
    (padSentinel input).stack = padFrame input := by
  rfl

@[simp] theorem padSentinel_calldata (input : ByteArray) :
    (padSentinel input).executionEnv.calldata = input := by rfl

def lengthCopyPath : List
    (Challenge.EvmProof.DataStepper.Located Control.Artifact.submissionArtifact .Osaka) :=
  Control.Artifact.padCopyPath
def guardPath : List
    (Challenge.EvmProof.DataStepper.Located Control.Artifact.submissionArtifact .Osaka) :=
  Control.Artifact.padGuardPath
def lengthSentinelPath : List
    (Challenge.EvmProof.DataStepper.Located Control.Artifact.submissionArtifact .Osaka) :=
  Control.Artifact.padSentinelPath
def lengthFooterSetupPath : List
    (Challenge.EvmProof.DataStepper.Located Control.Artifact.submissionArtifact .Osaka) :=
  Control.Artifact.padFooterSetupPath
def lengthSentinelAddressPath := lengthSentinelPath.take 4
def lengthSentinelStorePath := lengthSentinelPath.drop 4

def padSentinelAddressReady (input : ByteArray) : State :=
  { padDirty input with
    pc := UInt256.ofNat 10003
    stack := [UInt256.ofNat Padding.messageOffset + UInt256.ofNat input.size,
      UInt256.ofNat 128] ++ padFrame input }

def padSentinelStored (input : ByteArray) : State :=
  { padSentinelAddressReady input with
    pc := UInt256.ofNat 10004
    stack := padFrame input
    memory := MachineState.writeBytes (padSentinelAddressReady input).memory
      (ByteArray.mk #[0x80])
      (UInt256.ofNat Padding.messageOffset + UInt256.ofNat input.size).toNat
    activeWords := (padSentinelAddressReady input).activeWordsAfterUInt256
      (UInt256.ofNat Padding.messageOffset + UInt256.ofNat input.size).toNat 1 }

@[simp] theorem padSentinelAddressReady_halt (input : ByteArray) :
    (padSentinelAddressReady input).halt = .Running := by rfl

@[simp] theorem padSentinelAddressReady_pc (input : ByteArray) :
    (padSentinelAddressReady input).pc = UInt256.ofNat 10003 := by rfl

@[simp] theorem padSentinelAddressReady_stack (input : ByteArray) :
    (padSentinelAddressReady input).stack =
      [UInt256.ofNat Padding.messageOffset + UInt256.ofNat input.size,
        UInt256.ofNat 128] ++ padFrame input := by rfl

@[simp] theorem padSentinelAddressReady_memory (input : ByteArray) :
    (padSentinelAddressReady input).memory = (padDirty input).memory := by rfl

@[simp] theorem padSentinelAddressReady_activeWords (input : ByteArray) :
    (padSentinelAddressReady input).activeWords = (padDirty input).activeWords := by rfl

set_option maxHeartbeats 200000 in
@[simp] theorem padLengthReady_pc (input : ByteArray) :
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
  simp [lengthCopyPath, Control.Artifact.padCopyPath,
    Challenge.EvmProof.DataStepper.runLocatedBlock,
    Challenge.EvmProof.DataStepper.runLocated, Challenge.EvmProof.DataStepper.runInstr,
    State.activeWordsAfterUInt256, Padding.messageOffset,
    hpc, hstack, hdata, hrun, hsizeWord, hzero]

/-- Initialize the complete resident frame before the alignment guard. -/
def gasSteps_push (input : ByteArray) :
    Challenge.EvmProof.GasSteps (padCopied input) (padFramed input) := by
  have g := Control.StaggerPersistentStart.gasSteps_push (padCopied input) (copiedLimit input)
    [DenseScheduleTemplate.mask8, DenseScheduleTemplate.mask16]
    (by decide) rfl rfl rfl deployAddress_not_precompile
  exact Challenge.EvmProof.GasSteps.cast g (by rfl) (by rfl)

/-! ## Whole-block test -/

theorem xor_zero_iff (a b : Nat) : a ^^^ b = 0 ↔ a = b := by
  constructor
  · intro h
    have e : a ^^^ (a ^^^ b) = a ^^^ 0 := by rw [h]
    rw [← Nat.xor_assoc, Nat.xor_self, Nat.zero_xor, Nat.xor_zero] at e
    exact e.symm
  · intro h
    rw [h, Nat.xor_self]

theorem mask_c0 (n : Nat) (hn : n < 2 ^ 64) :
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
theorem guardMask_toNat : (UInt256.ofNat 18446744073709551423).toNat = (2 ^ 64 - 1) ^^^ 192 := by
  decide

theorem guard_zero_iff (input : ByteArray) (hfit : CalldataFits input) :
    (UInt256.land (UInt256.ofNat input.size) (UInt256.ofNat 18446744073709551423)).toNat = 0 ↔
      (input.size % 64 = 0 ∧ input.size < 256) := by
  have hsize : input.size < 2 ^ 256 := Nat.lt_trans hfit (by norm_num)
  rw [Challenge.EvmProof.Word.word_toNat_land, guardMask_toNat,
    Challenge.EvmProof.Word.word_toNat_ofNat, Nat.mod_eq_of_lt hsize]
  exact mask_c0 input.size hfit

def padGuardTaken (input : ByteArray) : State :=
  {padGuardMiss input with pc := UInt256.ofNat 143, stack := initialFrame input}

theorem padGuardMiss_memory (input : ByteArray) :
    (padGuardMiss input).memory = Control.Shared32Scratch.copiedMemory input := by
  change MachineState.writeBytes ByteArray.empty
    (MachineState.readPadded input 0 input.size) 1056 = Control.Shared32Scratch.copiedMemory input
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
  rw [padGuardMiss_memory, Control.Shared32Scratch.copiedMemory_size input hpos]
  omega

theorem padGuardMiss_zero (input : ByteArray) :
    ∀ a, 157 ≤ a → a < 189 → (padGuardMiss input).memory[a]?.getD 0 = 0 := by
  intro a _ ha
  rw [padGuardMiss_memory]
  exact Control.Shared32Scratch.copiedMemory_zero input a (by omega)

set_option maxHeartbeats 400000 in
theorem run_guardSkip (input : ByteArray) (hfit : CalldataFits input)
    (hz : input.size % 64 = 0 ∧ input.size < 256) :
    Challenge.EvmProof.DataStepper.runLocatedBlock guardPath
      (padFramed input) = some (padSkip input) := by
  have hv := (guard_zero_iff input hfit).mpr hz
  simp [guardPath, Control.Artifact.padGuardPath,
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
  simp [guardPath, Control.Artifact.padGuardPath,
    Challenge.EvmProof.DataStepper.runLocatedBlock,
    Challenge.EvmProof.DataStepper.runLocated, Challenge.EvmProof.DataStepper.runInstr,
    padFramed, padGuardTaken, padGuardMiss, UInt256.isTrue, hv]

def gasSteps_guardSkip (input : ByteArray) (hfit : CalldataFits input)
    (hz : input.size % 64 = 0 ∧ input.size < 256) :
    Challenge.EvmProof.GasSteps (padFramed input) (padSkip input) :=
  Challenge.EvmProof.DataStepper.runLocatedBlock_sound
    Control.Artifact.submissionArtifact .Osaka guardPath (by rfl) (by rfl)
    (run_guardSkip input hfit hz) (by rfl) deployAddress_not_precompile

def gasSteps_guardMiss (input : ByteArray) (hfit : CalldataFits input)
    (hn32 : input.size ≠ 32) (hnz : ¬ (input.size % 64 = 0 ∧ input.size < 256)) :
    Challenge.EvmProof.GasSteps (padFramed input) (padDirty input) := by
  have g := Challenge.EvmProof.DataStepper.runLocatedBlock_sound
    Control.Artifact.submissionArtifact .Osaka guardPath (by rfl) (by rfl)
    (run_guardMiss input hfit hnz) (by rfl) deployAddress_not_precompile
  have hpos : 0 < input.size := by
    by_contra h
    exact hnz ⟨by omega, by omega⟩
  have gp := Control.ColdGuardFixup.gasSteps_partial (padGuardMiss input)
    StackRunBridge.initialHashState (UInt256.ofNat 1056) (copiedLimit input)
    [DenseScheduleTemplate.mask8, DenseScheduleTemplate.mask16]
    (by decide) rfl rfl rfl deployAddress_not_precompile
    (by exact Nat.lt_trans hfit (by norm_num)) hn32
    (padGuardMiss_active input hfit hpos)
    (by rw [padGuardMiss_memory]; have hh := Control.Shared32Scratch.copiedMemory_size input hpos; omega)
    (by rw [padGuardMiss_memory]; intro a ha hb; exact Control.Shared32Scratch.copiedMemory_zero input a (by omega)) rfl
  exact g.trans gp

set_option maxHeartbeats 400000 in
theorem run_lengthSentinelAddress (input : ByteArray) :
    Challenge.EvmProof.DataStepper.runLocatedBlock lengthSentinelAddressPath
      (padDirty input) = some (padSentinelAddressReady input) := by
  simp [lengthSentinelAddressPath, lengthSentinelPath,
    Control.Artifact.padSentinelPath, Challenge.EvmProof.DataStepper.runLocatedBlock,
    Challenge.EvmProof.DataStepper.runLocated, Challenge.EvmProof.DataStepper.runInstr,
    padSentinelAddressReady, padDirty, padGuardMiss, padFrame, StaggerPersistentFrame.frame,
    Padding.messageOffset, Challenge.EvmProof.Word.word_add_comm]

set_option maxHeartbeats 400000 in
theorem run_lengthSentinelStore (input : ByteArray)
    (_hfit : CalldataFits input) :
    Challenge.EvmProof.DataStepper.runLocatedBlock lengthSentinelStorePath
      (padSentinelAddressReady input) = some (padSentinelStored input) := by
  simp [lengthSentinelStorePath, lengthSentinelPath,
    Control.Artifact.padSentinelPath,
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


end Challenge.Ripemd160.Submission.Proofs.Bytecode.Local20261028.Control.PaddingTrace
