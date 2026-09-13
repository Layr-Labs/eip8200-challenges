import Challenge.Ripemd160.Submission.Proofs.Bytecode.Padding
import Challenge.Ripemd160.Submission.Proofs.Bytecode.Trace
import Challenge.Ripemd160.Submission.Proofs.Bytecode.Main
import Challenge.Ripemd160.Submission.Proofs.Bytecode.StaggerPersistentStart
import Challenge.Ripemd160.Submission.Proofs.Bytecode.DataStepper
set_option warningAsError true
set_option maxRecDepth 20000
set_option maxHeartbeats 2000000
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
    pc := UInt256.ofNat 352
    stack := [] }

@[simp] private theorem padEntry_halt (input : ByteArray) :
    (padEntry input).halt = .Running := by rfl

@[simp] private theorem padEntry_fork (input : ByteArray) :
    (padEntry input).fork = .Osaka := by rfl

@[simp] private theorem padEntry_code (input : ByteArray) :
    (padEntry input).executionEnv.code = submissionBytecode := by rfl

@[simp] private theorem padEntry_calldata (input : ByteArray) :
    (padEntry input).executionEnv.calldata = input := by rfl

@[simp] private theorem initializedPC764 :
    Artifact.instructionPC 239 = 352 := by change Artifact.submissionArtifact.instructionPC 239 = 352; rw [Challenge.Ripemd160.Submission.Proofs.Bytecode.ArtifactByteLength.instructionPC_eq_byteLength]; rfl

@[simp] private theorem initializedCalldata (input : ByteArray) :
    (Main.initializedState input).executionEnv.calldata = input := by rfl

def enterPath : List
    (Challenge.EvmProof.DataStepper.Located Artifact.submissionArtifact .Osaka) :=
  Artifact.padEnterPath

set_option maxHeartbeats 200000 in
private theorem run_enter (input : ByteArray) :
    Challenge.EvmProof.DataStepper.runLocatedBlock enterPath
      (Main.initializedState input) = some (padEntry input) := by
  have hpc : (Main.initializedState input).pc = UInt256.ofNat 352 := by
    rw [Main.initializedState_pc, initializedPC764]
  have hstack := Main.initializedState_stack input
  simp only [enterPath, Artifact.padEnterPath, Challenge.EvmProof.DataStepper.runLocatedBlock]
  rw [padEntry, ← hpc, ← hstack]

def gasSteps_enterPad (input : ByteArray) :
    Challenge.EvmProof.GasSteps (Main.initializedState input) (padEntry input) := by
  apply Challenge.EvmProof.DataStepper.runLocatedBlock_sound
    Artifact.submissionArtifact .Osaka enterPath
  · rfl
  · rfl
  · exact run_enter input
  · rfl
  · exact deployAddress_not_precompile

def paddedLengthPath : List
    (Challenge.EvmProof.DataStepper.Located Artifact.submissionArtifact .Osaka) :=
  Artifact.padLengthPath

def padLengthReady (input : ByteArray) : State :=
  { padEntry input with
    pc := UInt256.ofNat (Artifact.instructionPC 245)
    stack := [Padding.paddedWord input] }

@[simp] private theorem padLengthReady_halt (input : ByteArray) :
    (padLengthReady input).halt = .Running := by rfl

@[simp] private theorem padLengthReady_fork (input : ByteArray) :
    (padLengthReady input).fork = .Osaka := by rfl

@[simp] private theorem padLengthReady_code (input : ByteArray) :
    (padLengthReady input).executionEnv.code = submissionBytecode := by rfl

@[simp] private theorem padLengthReady_calldata (input : ByteArray) :
    (padLengthReady input).executionEnv.calldata = input := by rfl

@[simp] private theorem padLengthReady_pcToNat (input : ByteArray) :
    (padLengthReady input).pc.toNat = 360 := by rfl

@[simp] private theorem padLengthReady_pc (input : ByteArray) :
    (padLengthReady input).pc = UInt256.ofNat 360 := by rfl

@[simp] private theorem padLengthReady_pcSucc (input : ByteArray) :
    (padLengthReady input).pc.succ = UInt256.ofNat 361 := by
  rw [padLengthReady_pc, Challenge.EvmProof.Word.succ_ofNat (by norm_num)]

@[simp] private theorem padLengthReady_stack (input : ByteArray) :
    (padLengthReady input).stack = [Padding.paddedWord input] := by
  rfl

/-- Clearing the low six bits with `NOT 63; AND` is exactly the shift pair the
base used: both round `x` down to a multiple of 64. -/
private theorem mask_low6_nat (n : Nat) (hn : n < 2 ^ 256) :
    (2 ^ 256 - 1 - 63) &&& n = n >>> 6 <<< 6 := by
  have hm : (2:Nat) ^ 256 - 1 - 63 = (2 ^ 250 - 1) <<< 6 := by
    rw [Nat.shiftLeft_eq]
    have h : (2:Nat) ^ 250 * 2 ^ 6 = 2 ^ 256 := by rw [← pow_add]
    have h2 : (1:Nat) ≤ 2 ^ 250 := Nat.one_le_two_pow
    omega
  rw [hm]
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.testBit_and, Nat.testBit_shiftLeft, Nat.testBit_shiftLeft,
    Nat.testBit_shiftRight, Nat.testBit_two_pow_sub_one]
  by_cases h6 : i ≥ 6
  · by_cases h256 : i < 256
    · rw [show 6 + (i - 6) = i by omega]
      simp [h6, show i - 6 < 250 by omega]
    · have hle : (2:Nat) ^ 256 ≤ 2 ^ i := Nat.pow_le_pow_right (by norm_num) (by omega)
      have hz : n.testBit i = false := Nat.testBit_lt_two_pow (by omega)
      rw [show 6 + (i - 6) = i by omega]
      simp [h6, hz]
  · simp [h6]

private theorem land_not63 (x : UInt256) :
    (UInt256.ofNat 63).lnot.land x =
      (x.shiftRight (UInt256.ofNat 6)).shiftLeft (UInt256.ofNat 6) := by
  have hx : x.toNat < 2 ^ 256 := x.val.isLt
  have h6 : (UInt256.ofNat 6).toNat = 6 := by
    rw [Challenge.EvmProof.Word.word_toNat_ofNat]; norm_num
  apply Challenge.EvmProof.Word.word_ext
  rw [Challenge.EvmProof.Word.word_toNat_land]
  unfold UInt256.lnot UInt256.shiftLeft UInt256.shiftRight
  rw [if_neg (by omega : ¬ (UInt256.ofNat 6).toNat ≥ 256)]
  rw [Challenge.EvmProof.Word.word_toNat_ofNat,
    Challenge.EvmProof.Word.word_toNat_ofNat, h6]
  change ((2 ^ 256 - 1 - (UInt256.ofNat 63).toNat) % 2 ^ 256) &&& x.toNat
      = ((⟨x.val >>> (UInt256.ofNat 6).val⟩ : UInt256).toNat <<< 6) % 2 ^ 256 % 2 ^ 256
  have h63 : (UInt256.ofNat 63).toNat = 63 := by
    rw [Challenge.EvmProof.Word.word_toNat_ofNat]; norm_num
  have hsr : (⟨x.val >>> (UInt256.ofNat 6).val⟩ : UInt256).toNat = x.toNat >>> 6 := by
    show (x.val >>> (UInt256.ofNat 6).val).val = _
    rw [Fin.shiftRight_val]
    congr 1
  have hbound : x.toNat >>> 6 <<< 6 < 2 ^ 256 := by
    have : x.toNat >>> 6 <<< 6 ≤ x.toNat := by
      rw [Nat.shiftLeft_eq, Nat.shiftRight_eq_div_pow]
      exact Nat.div_mul_le_self _ _
    omega
  rw [h63, hsr, Nat.mod_eq_of_lt (by omega : (2:Nat) ^ 256 - 1 - 63 < 2 ^ 256),
    Nat.mod_eq_of_lt hbound, Nat.mod_eq_of_lt hbound]
  exact mask_low6_nat x.toNat hx

set_option maxHeartbeats 200000 in
private theorem run_paddedLength (input : ByteArray) :
    Challenge.EvmProof.DataStepper.runLocatedBlock paddedLengthPath (padEntry input) =
      some (padLengthReady input) := by
  simp [paddedLengthPath, Artifact.padLengthPath, Challenge.EvmProof.DataStepper.runLocatedBlock,
    Challenge.EvmProof.DataStepper.runLocated, Challenge.EvmProof.DataStepper.runInstr,
    padEntry, padLengthReady,
    Padding.paddedWord, land_not63, Challenge.EvmProof.Word.word_add_comm]

def gasSteps_paddedLength (input : ByteArray) :
    Challenge.EvmProof.GasSteps (padEntry input) (padLengthReady input) := by
  apply Challenge.EvmProof.DataStepper.runLocatedBlock_sound
    Artifact.submissionArtifact .Osaka paddedLengthPath
  · rfl
  · rfl
  · exact run_paddedLength input
  · rfl
  · exact deployAddress_not_precompile

def bitLengthWord (input : ByteArray) : UInt256 :=
  UInt256.shiftLeft (UInt256.ofNat input.size) (UInt256.ofNat 3)

def lengthOffsetWord (input : ByteArray) : UInt256 :=
  Padding.paddedWord input + UInt256.ofNat 0x458

/-- The persistent block-loop frame at hash entry: the initial chaining words and the six
resident round constants above the zero offset and the padded limit. -/
def padFrame (input : ByteArray) : List UInt256 := [Padding.paddedWord input]

@[simp] theorem padFrame_length (input : ByteArray) : (padFrame input).length = 1 := by
  simp [padFrame]

def padCopied (input : ByteArray) : State :=
  { padLengthReady input with
    pc := UInt256.ofNat (Artifact.instructionPC 249)
    stack := [Padding.paddedWord input]
    memory := MachineState.writeBytes (padLengthReady input).memory
      (MachineState.readPadded input 0 input.size) Padding.messageOffset
    activeWords := (padLengthReady input).activeWordsAfterUInt256
      Padding.messageOffset input.size }

/-- State after the eleven frame pushes. -/
def padFramed (input : ByteArray) : State :=
  { padCopied input with
    pc := UInt256.ofNat 366
    stack := padFrame input }

/-- Whole-block input: the padding code jumps straight to the block loop with only the
calldata copy in memory. -/
def padSkip (input : ByteArray) : State :=
  { padCopied input with
    pc := UInt256.ofNat 374
    stack := padFrame input }

/-- Partial last block: fall through into the sentinel store. -/
def padGuardMiss (input : ByteArray) : State :=
  { padCopied input with
    pc := UInt256.ofNat (Artifact.instructionPC 3767)
    stack := padFrame input }

def padSentinel (input : ByteArray) : State :=
  { padCopied input with
    pc := UInt256.ofNat (Artifact.instructionPC 3772)
    stack := padFrame input
    memory := MachineState.writeBytes (padCopied input).memory
      (ByteArray.mk #[0x80]) (Padding.messageOffset + input.size)
    activeWords := (padCopied input).activeWordsAfterUInt256
      (Padding.messageOffset + input.size) 1 }

@[simp] private theorem padCopied_halt (input : ByteArray) :
    (padCopied input).halt = .Running := by rfl

@[simp] private theorem padCopied_pcToNat (input : ByteArray) :
    (padCopied input).pc.toNat = 366 := by rfl

@[simp] private theorem padCopied_pc (input : ByteArray) :
    (padCopied input).pc = UInt256.ofNat 366 := by rfl

@[simp] private theorem padCopied_stack (input : ByteArray) :
    (padCopied input).stack =
      [Padding.paddedWord input] := by
  rfl

@[simp] theorem padCopied_calldata (input : ByteArray) :
    (padCopied input).executionEnv.calldata = input := by rfl

@[simp] theorem padCopied_code (input : ByteArray) :
    (padCopied input).executionEnv.code = submissionBytecode := by rfl

@[simp] private theorem padFramed_halt (input : ByteArray) :
    (padFramed input).halt = .Running := by rfl

@[simp] private theorem padFramed_pc (input : ByteArray) :
    (padFramed input).pc = UInt256.ofNat 366 := by rfl

@[simp] private theorem padFramed_code (input : ByteArray) :
    (padFramed input).executionEnv.code = submissionBytecode := by rfl

@[simp] private theorem padFramed_calldata (input : ByteArray) :
    (padFramed input).executionEnv.calldata = input := by rfl

@[simp] private theorem padGuardMiss_halt (input : ByteArray) :
    (padGuardMiss input).halt = .Running := by rfl

@[simp] private theorem padGuardMiss_pc (input : ByteArray) :
    (padGuardMiss input).pc = UInt256.ofNat 4719 := by rfl

@[simp] private theorem padGuardMiss_code (input : ByteArray) :
    (padGuardMiss input).executionEnv.code = submissionBytecode := by rfl

@[simp] private theorem padGuardMiss_calldata (input : ByteArray) :
    (padGuardMiss input).executionEnv.calldata = input := by rfl

@[simp] private theorem padSentinel_halt (input : ByteArray) :
    (padSentinel input).halt = .Running := by rfl

@[simp] private theorem padSentinel_pcToNat (input : ByteArray) :
    (padSentinel input).pc.toNat = 4727 := by rfl

@[simp] private theorem padSentinel_pc (input : ByteArray) :
    (padSentinel input).pc = UInt256.ofNat 4727 := by rfl

@[simp] private theorem padSentinel_pcSucc (input : ByteArray) :
    (padSentinel input).pc.succ = UInt256.ofNat 4728 := by
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
    pc := UInt256.ofNat (Artifact.instructionPC 3771)
    stack := [UInt256.ofNat Padding.messageOffset + UInt256.ofNat input.size,
      UInt256.ofNat 128] ++ padFrame input }

def padSentinelStored (input : ByteArray) : State :=
  { padSentinelAddressReady input with
    pc := UInt256.ofNat (Artifact.instructionPC 3772)
    stack := padFrame input
    memory := MachineState.writeBytes (padSentinelAddressReady input).memory
      (ByteArray.mk #[0x80])
      (UInt256.ofNat Padding.messageOffset + UInt256.ofNat input.size).toNat
    activeWords := (padSentinelAddressReady input).activeWordsAfterUInt256
      (UInt256.ofNat Padding.messageOffset + UInt256.ofNat input.size).toNat 1 }

@[simp] private theorem padSentinelAddressReady_halt (input : ByteArray) :
    (padSentinelAddressReady input).halt = .Running := by rfl

@[simp] private theorem padSentinelAddressReady_pc (input : ByteArray) :
    (padSentinelAddressReady input).pc = UInt256.ofNat 4726 := by rfl

@[simp] private theorem padSentinelAddressReady_stack (input : ByteArray) :
    (padSentinelAddressReady input).stack =
      [UInt256.ofNat Padding.messageOffset + UInt256.ofNat input.size,
        UInt256.ofNat 128] ++ padFrame input := by rfl

@[simp] private theorem padSentinelAddressReady_memory (input : ByteArray) :
    (padSentinelAddressReady input).memory = (padCopied input).memory := by rfl

@[simp] private theorem padSentinelAddressReady_activeWords (input : ByteArray) :
    (padSentinelAddressReady input).activeWords = (padCopied input).activeWords := by rfl

set_option maxHeartbeats 200000 in
theorem run_lengthCopy (input : ByteArray) (hfit : CalldataFits input) :
    Challenge.EvmProof.DataStepper.runLocatedBlock lengthCopyPath
      (padLengthReady input) = some (padCopied input) := by
  have hsize : input.size < 2 ^ 256 := Nat.lt_trans hfit (by norm_num)
  have hsizeWord : (UInt256.ofNat input.size).toNat = input.size := by
    rw [Challenge.EvmProof.Word.word_toNat_ofNat, Nat.mod_eq_of_lt hsize]
  have hzero : (⟨0⟩ : UInt256) = UInt256.ofNat 0 := by rfl
  simp [lengthCopyPath, Artifact.padCopyPath,
    Challenge.EvmProof.DataStepper.runLocatedBlock,
    Challenge.EvmProof.DataStepper.runLocated, Challenge.EvmProof.DataStepper.runInstr,
    padCopied, padLengthReady, State.activeWordsAfterUInt256, Padding.messageOffset,
    hsizeWord, hzero]

/-- No resident frame is needed during padding setup. -/
def gasSteps_push (input : ByteArray) :
    Challenge.EvmProof.GasSteps (padCopied input) (padFramed input) := by
  exact Challenge.EvmProof.GasSteps.cast (Challenge.EvmProof.GasSteps.refl (padCopied input)) rfl rfl

/-! ## Whole-block test -/

private theorem guard_toNat (input : ByteArray) (hfit : CalldataFits input) :
    (UInt256.land (UInt256.ofNat input.size) (UInt256.ofNat 63)).toNat = input.size % 64 := by
  have hsize : input.size < 2 ^ 256 := Nat.lt_trans hfit (by norm_num)
  rw [Challenge.EvmProof.Word.word_toNat_land, Challenge.EvmProof.Word.word_toNat_ofNat,
    Challenge.EvmProof.Word.word_toNat_ofNat, Nat.mod_eq_of_lt hsize,
    Nat.mod_eq_of_lt (by norm_num : (63:Nat) < 2 ^ 256)]
  have h63 : (63:Nat) = 2 ^ 6 - 1 := by norm_num
  rw [h63, Nat.and_two_pow_sub_one_eq_mod]

private theorem guard_isZero_skip (input : ByteArray) (hfit : CalldataFits input)
    (hz : input.size % 64 = 0) :
    UInt256.isZero (UInt256.land (UInt256.ofNat input.size) (UInt256.ofNat 63)) =
      UInt256.ofNat 1 := by
  unfold UInt256.isZero
  rw [if_pos (by rw [guard_toNat input hfit, hz])]

private theorem guard_isZero_miss (input : ByteArray) (hfit : CalldataFits input)
    (hnz : input.size % 64 ≠ 0) :
    UInt256.isZero (UInt256.land (UInt256.ofNat input.size) (UInt256.ofNat 63)) =
      UInt256.ofNat 0 := by
  unfold UInt256.isZero
  rw [if_neg (by rw [guard_toNat input hfit]; exact hnz)]

def padGuardTaken (input : ByteArray) : State :=
  {padGuardMiss input with pc := UInt256.ofNat 4718}

set_option maxHeartbeats 400000 in
private theorem run_guardSkip (input : ByteArray) (hfit : CalldataFits input)
    (hz : input.size % 64 = 0) :
    Challenge.EvmProof.DataStepper.runLocatedBlock guardPath
      (padFramed input) = some (padSkip input) := by
  simp [guardPath, Artifact.padGuardPath,
    Challenge.EvmProof.DataStepper.runLocatedBlock,
    Challenge.EvmProof.DataStepper.runLocated, Challenge.EvmProof.DataStepper.runInstr,
    padFramed, padSkip, UInt256.isTrue,
    guard_toNat input hfit, hz]

set_option maxHeartbeats 400000 in
private theorem run_guardMiss (input : ByteArray) (hfit : CalldataFits input)
    (hnz : input.size % 64 ≠ 0) :
    Challenge.EvmProof.DataStepper.runLocatedBlock guardPath
      (padFramed input) = some (padGuardTaken input) := by
  simp [guardPath, Artifact.padGuardPath,
    Challenge.EvmProof.DataStepper.runLocatedBlock,
    Challenge.EvmProof.DataStepper.runLocated, Challenge.EvmProof.DataStepper.runInstr,
    padFramed, padGuardTaken, padGuardMiss, UInt256.isTrue,
    guard_toNat input hfit, hnz]

def gasSteps_guardSkip (input : ByteArray) (hfit : CalldataFits input)
    (hz : input.size % 64 = 0) :
    Challenge.EvmProof.GasSteps (padFramed input) (padSkip input) :=
  Challenge.EvmProof.DataStepper.runLocatedBlock_sound
    Artifact.submissionArtifact .Osaka guardPath (by rfl) (by rfl)
    (run_guardSkip input hfit hz) (by rfl) deployAddress_not_precompile

def gasSteps_guardMiss (input : ByteArray) (hfit : CalldataFits input)
    (hnz : input.size % 64 ≠ 0) :
    Challenge.EvmProof.GasSteps (padFramed input) (padGuardMiss input) := by
  have g := Challenge.EvmProof.DataStepper.runLocatedBlock_sound
    Artifact.submissionArtifact .Osaka guardPath (by rfl) (by rfl)
    (run_guardMiss input hfit hnz) (by rfl) deployAddress_not_precompile
  have gp := StaggerPersistentStart.gasSteps_partial (padGuardMiss input) (padFrame input)
    (by simp [padFrame]) rfl rfl rfl deployAddress_not_precompile
  exact g.trans gp

set_option maxHeartbeats 400000 in
theorem run_lengthSentinelAddress (input : ByteArray) :
    Challenge.EvmProof.DataStepper.runLocatedBlock lengthSentinelAddressPath
      (padGuardMiss input) = some (padSentinelAddressReady input) := by
  simp [lengthSentinelAddressPath, lengthSentinelPath,
    Artifact.padSentinelPath, Challenge.EvmProof.DataStepper.runLocatedBlock,
    Challenge.EvmProof.DataStepper.runLocated, Challenge.EvmProof.DataStepper.runInstr,
    padSentinelAddressReady, padGuardMiss, Padding.messageOffset]

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
    pc := UInt256.ofNat (Artifact.instructionPC 3778)
    stack := lengthAddr input i :: lengthShift input i :: padFrame input
    memory := lengthLoopMemory input i
    activeWords := lengthLoopActiveWords input i }

def lengthIterationPath : List
    (Challenge.EvmProof.DataStepper.Located Artifact.submissionArtifact .Osaka) :=
  [⟨3778, .op .JUMPDEST, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨3779, .op (.Dup ⟨1, by decide⟩), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨3780, .op (.Dup ⟨1, by decide⟩), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨3781, .op .MSTORE8, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨3782, .push ⟨1, by decide⟩ (UInt256.ofNat 1), by rfl, by decide⟩,
   ⟨3783, .op .ADD, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨3784, .op (.Swap ⟨0, by decide⟩), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨3785, .push ⟨1, by decide⟩ (UInt256.ofNat 8), by rfl, by decide⟩,
   ⟨3786, .op .SHR, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨3787, .op (.Swap ⟨0, by decide⟩), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨3788, .op (.Dup ⟨1, by decide⟩), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨3789, .push ⟨2, by decide⟩ (UInt256.ofNat 4736), by rfl, by decide⟩,
   ⟨3790, .op .JUMPI, by rfl, wfOp (by decide) trivial rfl⟩]

def lengthBodyPath := lengthIterationPath.take 10
def lengthBranchPath := lengthIterationPath.drop 10

@[simp] private theorem lengthLoopState_halt (input : ByteArray) (i : Nat) :
    (lengthLoopState input i).halt = .Running := by rfl

@[simp] private theorem lengthLoopState_fork (input : ByteArray) (i : Nat) :
    (lengthLoopState input i).fork = .Osaka := by rfl

@[simp] private theorem lengthLoopState_code (input : ByteArray) (i : Nat) :
    (lengthLoopState input i).executionEnv.code = submissionBytecode := by rfl

@[simp] private theorem lengthLoopState_pc (input : ByteArray) (i : Nat) :
    (lengthLoopState input i).pc = UInt256.ofNat 4736 := by rfl

@[simp] private theorem lengthLoopState_stack (input : ByteArray) (i : Nat) :
    (lengthLoopState input i).stack =
      lengthAddr input i :: lengthShift input i :: padFrame input := by rfl

@[simp] private theorem padSentinel_code (input : ByteArray) :
    (padSentinel input).executionEnv.code = submissionBytecode := by rfl

/-- State after one low-byte store and both register updates. -/
def lengthSteppedState (input : ByteArray) (i : Nat) : State :=
  { lengthLoopState input i with
    pc := UInt256.ofNat (Artifact.instructionPC 3788)
    stack := lengthAddr input (i + 1) :: lengthShift input (i + 1) :: padFrame input
    memory := lengthLoopMemory input (i + 1)
    activeWords := lengthLoopActiveWords input (i + 1) }

def lengthBranchReady (input : ByteArray) (i : Nat) : State :=
  { lengthSteppedState input i with
    pc := UInt256.ofNat (Artifact.instructionPC 3790)
    stack := [UInt256.ofNat 4736, lengthShift input (i + 1)] ++
      (lengthSteppedState input i).stack }

def lengthBackReturned (input : ByteArray) (i : Nat) : State :=
  { lengthBranchReady input i with
    pc := UInt256.ofNat 4736
    stack := (lengthSteppedState input i).stack }

def lengthExitPending (input : ByteArray) (i : Nat) : State :=
  { lengthBranchReady input i with
    pc := UInt256.ofNat (Artifact.instructionPC 3791)
    stack := (lengthSteppedState input i).stack }

theorem lengthBackReturned_eq (input : ByteArray) (i : Nat) :
    lengthBackReturned input i = lengthLoopState input (i + 1) := by
  unfold lengthBackReturned lengthBranchReady lengthSteppedState lengthLoopState
  generalize padSentinel input = s
  cases s
  rfl

@[simp] private theorem lengthSteppedState_halt (input : ByteArray) (i : Nat) :
    (lengthSteppedState input i).halt = .Running := by rfl

@[simp] private theorem lengthSteppedState_pc (input : ByteArray) (i : Nat) :
    (lengthSteppedState input i).pc = UInt256.ofNat 4748 := by rfl

@[simp] private theorem lengthBranchReady_halt (input : ByteArray) (i : Nat) :
    (lengthBranchReady input i).halt = .Running := by rfl

@[simp] private theorem lengthBranchReady_pc (input : ByteArray) (i : Nat) :
    (lengthBranchReady input i).pc = UInt256.ofNat 4752 := by rfl

@[simp] private theorem lengthSteppedState_code (input : ByteArray) (i : Nat) :
    (lengthSteppedState input i).executionEnv.code = submissionBytecode := by rfl

@[simp] private theorem lengthBranchReady_code (input : ByteArray) (i : Nat) :
    (lengthBranchReady input i).executionEnv.code = submissionBytecode := by rfl

@[simp] private theorem validLengthLoopHead :
    Decode.isValidJumpDest submissionBytecode 4736 = true := by
  have hpc : Artifact.submissionArtifact.instructionPC 3778 = 4736 := by rw [Challenge.Ripemd160.Submission.Proofs.Bytecode.ArtifactByteLength.instructionPC_eq_byteLength]; rfl
  rw [← hpc]
  exact Artifact.submissionArtifact.isValidJumpDest_index 3778 (by rfl)

/-! ## Arithmetic bridge for the masked bit length -/
end Challenge.Ripemd160.Submission.Proofs.Bytecode.PaddingTrace
