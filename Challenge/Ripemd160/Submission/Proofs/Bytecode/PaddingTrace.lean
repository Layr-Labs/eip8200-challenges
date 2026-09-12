import Challenge.Ripemd160.Submission.Proofs.Bytecode.Padding
import Challenge.Ripemd160.Submission.Proofs.Bytecode.Trace
import Challenge.Ripemd160.Submission.Proofs.Bytecode.Main
import Challenge.EvmProof.Stepper
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
    Challenge.EvmProof.Stepper.WellFormed .Osaka (.op op) :=
  ⟨hopcode, hplain, havailable⟩

/-- The padding code is entered directly after the initial stores and falls
through into the driver entry, so no return address is pushed. -/
def padEntry (input : ByteArray) : State :=
  { Main.initializedState input with
    pc := UInt256.ofNat 336
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
    Artifact.instructionPC 231 = 336 := by change Artifact.submissionArtifact.instructionPC 231 = 336; rw [Challenge.Ripemd160.Submission.Proofs.Bytecode.ArtifactByteLength.instructionPC_eq_byteLength]; rfl

@[simp] private theorem initializedCalldata (input : ByteArray) :
    (Main.initializedState input).executionEnv.calldata = input := by rfl

def enterPath : List
    (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  Artifact.padEnterPath

set_option maxHeartbeats 200000 in
private theorem run_enter (input : ByteArray) :
    Challenge.EvmProof.Stepper.runLocatedBlock enterPath
      (Main.initializedState input) = some (padEntry input) := by
  have hpc : (Main.initializedState input).pc = UInt256.ofNat 336 := by
    rw [Main.initializedState_pc, initializedPC764]
  have hstack := Main.initializedState_stack input
  simp only [enterPath, Artifact.padEnterPath, Challenge.EvmProof.Stepper.runLocatedBlock]
  rw [padEntry, ← hpc, ← hstack]

def gasSteps_enterPad (input : ByteArray) :
    Challenge.EvmProof.GasSteps (Main.initializedState input) (padEntry input) := by
  apply Challenge.EvmProof.Stepper.runLocatedBlock_sound
    Artifact.submissionArtifact .Osaka enterPath
  · rfl
  · rfl
  · exact run_enter input
  · rfl
  · exact deployAddress_not_precompile

def paddedLengthPath : List
    (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  Artifact.padLengthPath

def padLengthReady (input : ByteArray) : State :=
  { padEntry input with
    pc := UInt256.ofNat (Artifact.instructionPC 238)
    stack := [UInt256.ofNat input.size, Padding.paddedWord input] }

@[simp] private theorem padLengthReady_halt (input : ByteArray) :
    (padLengthReady input).halt = .Running := by rfl

@[simp] private theorem padLengthReady_fork (input : ByteArray) :
    (padLengthReady input).fork = .Osaka := by rfl

@[simp] private theorem padLengthReady_code (input : ByteArray) :
    (padLengthReady input).executionEnv.code = submissionBytecode := by rfl

@[simp] private theorem padLengthReady_calldata (input : ByteArray) :
    (padLengthReady input).executionEnv.calldata = input := by rfl

@[simp] private theorem padLengthReady_pcToNat (input : ByteArray) :
    (padLengthReady input).pc.toNat = 345 := by rfl

@[simp] private theorem padLengthReady_pc (input : ByteArray) :
    (padLengthReady input).pc = UInt256.ofNat 345 := by rfl

@[simp] private theorem padLengthReady_pcSucc (input : ByteArray) :
    (padLengthReady input).pc.succ = UInt256.ofNat 346 := by
  rw [padLengthReady_pc, Challenge.EvmProof.Word.succ_ofNat (by norm_num)]

@[simp] private theorem padLengthReady_stack (input : ByteArray) :
    (padLengthReady input).stack =
      [UInt256.ofNat input.size, Padding.paddedWord input] := by
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
    Challenge.EvmProof.Stepper.runLocatedBlock paddedLengthPath (padEntry input) =
      some (padLengthReady input) := by
  simp [paddedLengthPath, Artifact.padLengthPath, Challenge.EvmProof.Stepper.runLocatedBlock,
    Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
    padEntry, padLengthReady,
    Padding.paddedWord, land_not63, Challenge.EvmProof.Word.word_add_comm]

def gasSteps_paddedLength (input : ByteArray) :
    Challenge.EvmProof.GasSteps (padEntry input) (padLengthReady input) := by
  apply Challenge.EvmProof.Stepper.runLocatedBlock_sound
    Artifact.submissionArtifact .Osaka paddedLengthPath
  · rfl
  · rfl
  · exact run_paddedLength input
  · rfl
  · exact deployAddress_not_precompile

def bitLengthWord (input : ByteArray) : UInt256 :=
  UInt256.shiftRight
    (UInt256.shiftLeft (UInt256.ofNat input.size) (UInt256.ofNat 195))
    (UInt256.ofNat 192)

def lengthOffsetWord (input : ByteArray) : UInt256 :=
  Padding.paddedWord input + UInt256.ofNat 0x478

def padCopied (input : ByteArray) : State :=
  { padLengthReady input with
    pc := UInt256.ofNat (Artifact.instructionPC 242)
    memory := MachineState.writeBytes (padLengthReady input).memory
      (MachineState.readPadded input 0 input.size) Padding.messageOffset
    activeWords := (padLengthReady input).activeWordsAfterUInt256
      Padding.messageOffset input.size }

def padSentinel (input : ByteArray) : State :=
  { padCopied input with
    pc := UInt256.ofNat (Artifact.instructionPC 247)
    stack := [UInt256.ofNat input.size, Padding.paddedWord input]
    memory := MachineState.writeBytes (padCopied input).memory
      (ByteArray.mk #[0x80]) (Padding.messageOffset + input.size)
    activeWords := (padCopied input).activeWordsAfterUInt256
      (Padding.messageOffset + input.size) 1 }

@[simp] private theorem padCopied_halt (input : ByteArray) :
    (padCopied input).halt = .Running := by rfl

@[simp] private theorem padCopied_pcToNat (input : ByteArray) :
    (padCopied input).pc.toNat = 351 := by rfl

@[simp] private theorem padCopied_pc (input : ByteArray) :
    (padCopied input).pc = UInt256.ofNat 351 := by rfl

@[simp] private theorem padCopied_stack (input : ByteArray) :
    (padCopied input).stack =
      [UInt256.ofNat input.size, Padding.paddedWord input] := by
  rfl

@[simp] private theorem padCopied_calldata (input : ByteArray) :
    (padCopied input).executionEnv.calldata = input := by rfl

@[simp] private theorem padSentinel_halt (input : ByteArray) :
    (padSentinel input).halt = .Running := by rfl

@[simp] private theorem padSentinel_pcToNat (input : ByteArray) :
    (padSentinel input).pc.toNat = 359 := by rfl

@[simp] private theorem padSentinel_pc (input : ByteArray) :
    (padSentinel input).pc = UInt256.ofNat 359 := by rfl

@[simp] private theorem padSentinel_pcSucc (input : ByteArray) :
    (padSentinel input).pc.succ = UInt256.ofNat 360 := by
  rw [padSentinel_pc, Challenge.EvmProof.Word.succ_ofNat (by norm_num)]

@[simp] private theorem padSentinel_stack (input : ByteArray) :
    (padSentinel input).stack =
      [UInt256.ofNat input.size, Padding.paddedWord input] := by
  rfl

def lengthSetupPath : List
    (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  Artifact.padSetupPath

def lengthCopyPath := lengthSetupPath.take 4
def lengthSentinelPath := (lengthSetupPath.drop 4).take 5
def lengthFooterSetupPath := (lengthSetupPath.drop 9).dropLast.dropLast
def lengthSentinelAddressPath := lengthSentinelPath.take 4
def lengthSentinelStorePath := lengthSentinelPath.drop 4

def padSentinelAddressReady (input : ByteArray) : State :=
  { padCopied input with
    pc := UInt256.ofNat (Artifact.instructionPC 246)
    stack := [UInt256.ofNat Padding.messageOffset + UInt256.ofNat input.size,
      UInt256.ofNat 128, UInt256.ofNat input.size, Padding.paddedWord input] }

def padSentinelStored (input : ByteArray) : State :=
  { padSentinelAddressReady input with
    pc := UInt256.ofNat (Artifact.instructionPC 247)
    stack := [UInt256.ofNat input.size, Padding.paddedWord input]
    memory := MachineState.writeBytes (padSentinelAddressReady input).memory
      (ByteArray.mk #[0x80])
      (UInt256.ofNat Padding.messageOffset + UInt256.ofNat input.size).toNat
    activeWords := (padSentinelAddressReady input).activeWordsAfterUInt256
      (UInt256.ofNat Padding.messageOffset + UInt256.ofNat input.size).toNat 1 }

@[simp] private theorem padSentinelAddressReady_halt (input : ByteArray) :
    (padSentinelAddressReady input).halt = .Running := by rfl

@[simp] private theorem padSentinelAddressReady_pc (input : ByteArray) :
    (padSentinelAddressReady input).pc = UInt256.ofNat 358 := by rfl

@[simp] private theorem padSentinelAddressReady_stack (input : ByteArray) :
    (padSentinelAddressReady input).stack =
      [UInt256.ofNat Padding.messageOffset + UInt256.ofNat input.size,
        UInt256.ofNat 128, UInt256.ofNat input.size, Padding.paddedWord input] := by rfl

@[simp] private theorem padSentinelAddressReady_memory (input : ByteArray) :
    (padSentinelAddressReady input).memory = (padCopied input).memory := by rfl

@[simp] private theorem padSentinelAddressReady_activeWords (input : ByteArray) :
    (padSentinelAddressReady input).activeWords = (padCopied input).activeWords := by rfl

set_option maxHeartbeats 200000 in
private theorem run_lengthCopy (input : ByteArray) (hfit : CalldataFits input) :
    Challenge.EvmProof.Stepper.runLocatedBlock lengthCopyPath
      (padLengthReady input) = some (padCopied input) := by
  have hsize : input.size < 2 ^ 256 := Nat.lt_trans hfit (by norm_num)
  have hsizeWord : (UInt256.ofNat input.size).toNat = input.size := by
    rw [Challenge.EvmProof.Word.word_toNat_ofNat, Nat.mod_eq_of_lt hsize]
  have hzero : (⟨0⟩ : UInt256) = UInt256.ofNat 0 := by rfl
  simp [lengthCopyPath, lengthSetupPath, Artifact.padSetupPath,
    Challenge.EvmProof.Stepper.runLocatedBlock,
    Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
    padCopied, padLengthReady, State.activeWordsAfterUInt256, Padding.messageOffset,
    hsizeWord, hzero]

set_option maxHeartbeats 200000 in
private theorem run_lengthSentinelAddress (input : ByteArray) :
    Challenge.EvmProof.Stepper.runLocatedBlock lengthSentinelAddressPath
      (padCopied input) = some (padSentinelAddressReady input) := by
  simp [lengthSentinelAddressPath, lengthSentinelPath, lengthSetupPath,
    Artifact.padSetupPath, Challenge.EvmProof.Stepper.runLocatedBlock,
    Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
    padSentinelAddressReady, padCopied, padLengthReady, Padding.messageOffset]

set_option maxHeartbeats 200000 in
private theorem run_lengthSentinelStore (input : ByteArray)
    (_hfit : CalldataFits input) :
    Challenge.EvmProof.Stepper.runLocatedBlock lengthSentinelStorePath
      (padSentinelAddressReady input) = some (padSentinelStored input) := by
  simp [lengthSentinelStorePath, lengthSentinelPath, lengthSetupPath,
    Artifact.padSetupPath,
    Challenge.EvmProof.Stepper.runLocatedBlock,
    Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
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
    pc := UInt256.ofNat (Artifact.instructionPC 254)
    stack := [lengthAddr input i, lengthShift input i,
      Padding.paddedWord input]
    memory := lengthLoopMemory input i
    activeWords := lengthLoopActiveWords input i }

def lengthIterationPath : List
    (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [⟨254, .op .JUMPDEST, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨255, .op (.Dup ⟨1, by decide⟩), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨256, .op (.Dup ⟨1, by decide⟩), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨257, .op .MSTORE8, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨258, .push ⟨1, by decide⟩ (UInt256.ofNat 1), by rfl, by decide⟩,
   ⟨259, .op .ADD, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨260, .op (.Swap ⟨0, by decide⟩), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨261, .push ⟨1, by decide⟩ (UInt256.ofNat 8), by rfl, by decide⟩,
   ⟨262, .op .SHR, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨263, .op (.Swap ⟨0, by decide⟩), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨264, .op (.Dup ⟨1, by decide⟩), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨265, .push ⟨2, by decide⟩ (UInt256.ofNat 370), by rfl, by decide⟩,
   ⟨266, .op .JUMPI, by rfl, wfOp (by decide) trivial rfl⟩]

def lengthBodyPath := lengthIterationPath.take 10
def lengthBranchPath := lengthIterationPath.drop 10

@[simp] private theorem lengthLoopState_halt (input : ByteArray) (i : Nat) :
    (lengthLoopState input i).halt = .Running := by rfl

@[simp] private theorem lengthLoopState_fork (input : ByteArray) (i : Nat) :
    (lengthLoopState input i).fork = .Osaka := by rfl

@[simp] private theorem lengthLoopState_code (input : ByteArray) (i : Nat) :
    (lengthLoopState input i).executionEnv.code = submissionBytecode := by rfl

@[simp] private theorem lengthLoopState_pc (input : ByteArray) (i : Nat) :
    (lengthLoopState input i).pc = UInt256.ofNat 370 := by rfl

@[simp] private theorem lengthLoopState_stack (input : ByteArray) (i : Nat) :
    (lengthLoopState input i).stack =
      [lengthAddr input i, lengthShift input i,
        Padding.paddedWord input] := by rfl

@[simp] private theorem padSentinel_code (input : ByteArray) :
    (padSentinel input).executionEnv.code = submissionBytecode := by rfl

/-- State after one low-byte store and both register updates. -/
def lengthSteppedState (input : ByteArray) (i : Nat) : State :=
  { lengthLoopState input i with
    pc := UInt256.ofNat (Artifact.instructionPC 264)
    stack := [lengthAddr input (i + 1), lengthShift input (i + 1),
      Padding.paddedWord input]
    memory := lengthLoopMemory input (i + 1)
    activeWords := lengthLoopActiveWords input (i + 1) }

def lengthBranchReady (input : ByteArray) (i : Nat) : State :=
  { lengthSteppedState input i with
    pc := UInt256.ofNat (Artifact.instructionPC 266)
    stack := [UInt256.ofNat 0x52, lengthShift input (i + 1)] ++
      (lengthSteppedState input i).stack }

def lengthBackReturned (input : ByteArray) (i : Nat) : State :=
  { lengthBranchReady input i with
    pc := UInt256.ofNat 370
    stack := (lengthSteppedState input i).stack }

def lengthExitPending (input : ByteArray) (i : Nat) : State :=
  { lengthBranchReady input i with
    pc := UInt256.ofNat (Artifact.instructionPC 267)
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
    (lengthSteppedState input i).pc = UInt256.ofNat 382 := by rfl

@[simp] private theorem lengthBranchReady_halt (input : ByteArray) (i : Nat) :
    (lengthBranchReady input i).halt = .Running := by rfl

@[simp] private theorem lengthBranchReady_pc (input : ByteArray) (i : Nat) :
    (lengthBranchReady input i).pc = UInt256.ofNat 386 := by rfl

@[simp] private theorem lengthSteppedState_code (input : ByteArray) (i : Nat) :
    (lengthSteppedState input i).executionEnv.code = submissionBytecode := by rfl

@[simp] private theorem lengthBranchReady_code (input : ByteArray) (i : Nat) :
    (lengthBranchReady input i).executionEnv.code = submissionBytecode := by rfl

@[simp] private theorem validLengthLoopHead :
    Decode.isValidJumpDest submissionBytecode 370 = true := by
  have hpc : Artifact.submissionArtifact.instructionPC 254 = 370 := by rw [Challenge.Ripemd160.Submission.Proofs.Bytecode.ArtifactByteLength.instructionPC_eq_byteLength]; rfl
  rw [← hpc]
  exact Artifact.submissionArtifact.isValidJumpDest_index 254 (by rfl)

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

/-- The masked bit length: `(size <<< 195) >>> 192 = size * 8 mod 2^64`. -/
theorem bitLengthWord_toNat (input : ByteArray) (hfit : CalldataFits input) :
    (bitLengthWord input).toNat = input.size * 8 % 2 ^ 64 := by
  have hsize : input.size < 2 ^ 256 := Nat.lt_trans hfit (by norm_num)
  have hleft : UInt256.shiftLeft (UInt256.ofNat input.size) (UInt256.ofNat 195) =
      UInt256.ofNat ((input.size * 2 ^ 195) % 2 ^ 256) :=
    shiftLeft_ofNat_wrap hsize (by norm_num)
  have hmod : (input.size * 2 ^ 195) % 2 ^ 256 < 2 ^ 256 := Nat.mod_lt _ (by positivity)
  rw [bitLengthWord, hleft,
    Challenge.EvmProof.Word.shiftRight_ofNat hmod (by norm_num : (192 : Nat) < 256),
    Challenge.EvmProof.Word.word_toNat_ofNat]
  have hstep : (input.size * 2 ^ 195) % 2 ^ 256 = (input.size % 2 ^ 61) * 2 ^ 195 := by
    rw [show (2 : Nat) ^ 256 = 2 ^ 61 * 2 ^ 195 by rw [← Nat.pow_add]]
    exact Nat.mul_mod_mul_right _ _ _
  rw [hstep, Nat.shiftRight_eq_div_pow,
    show (2 : Nat) ^ 195 = 2 ^ 192 * 2 ^ 3 by rw [← Nat.pow_add],
    ← Nat.mul_assoc, Nat.mul_comm (input.size % 2 ^ 61) (2 ^ 192),
    Nat.mul_assoc, Nat.mul_div_cancel_left _ (by positivity)]
  have hgoal : input.size * 8 % 2 ^ 64 = input.size % 2 ^ 61 * 2 ^ 3 := by
    rw [show (2 : Nat) ^ 64 = 2 ^ 61 * 2 ^ 3 by rw [← Nat.pow_add],
      show input.size * 8 = input.size * 2 ^ 3 by norm_num]
    exact Nat.mul_mod_mul_right _ _ _
  rw [hgoal]
  norm_num
  omega

theorem lengthShift_toNat (input : ByteArray) (hfit : CalldataFits input) (i : Nat) :
    (lengthShift input i).toNat = input.size * 8 % 2 ^ 64 / 2 ^ (8 * i) := by
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

theorem lengthShift_eight (input : ByteArray) (hfit : CalldataFits input) :
    lengthShift input 8 = ⟨0⟩ := by
  have h := lengthShift_toNat input hfit 8
  have hz : input.size * 8 % 2 ^ 64 / 2 ^ (8 * 8) = 0 := by
    apply Nat.div_eq_of_lt
    have := Nat.mod_lt (input.size * 8) (show 0 < 2 ^ 64 by positivity)
    simpa using this
  rw [hz] at h
  apply Challenge.EvmProof.Word.word_ext
  rw [h]
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
  if lengthShift input 7 = ⟨0⟩ then 7 else 8

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
              · omega

theorem lengthStop_le (input : ByteArray) : lengthStop input ≤ 8 := by
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
              · exact lengthShift_eight input hfit

theorem lengthStop_eq_succ_of_nonzero (input : ByteArray) (i : Nat)
    (hi : i < 8)
    (hprior : ∀ j, 0 < j → j ≤ i → lengthShift input j ≠ ⟨0⟩)
    (hz : lengthShift input (i + 1) = ⟨0⟩) :
    lengthStop input = i + 1 := by
  interval_cases i <;> simp_all [lengthStop]

theorem footerCount_spec (input : ByteArray) (hfit : CalldataFits input) :
    1 ≤ lengthStop input ∧ lengthStop input ≤ 8 ∧
      lengthShift input (lengthStop input) = ⟨0⟩ ∧
      ∀ j, 1 ≤ j → j < lengthStop input →
        lengthShift input j ≠ ⟨0⟩ := by
  have hpos := lengthStop_pos input
  have hle := lengthStop_le input
  refine ⟨by omega, hle,
    lengthShift_stop_zero input hfit, ?_⟩
  intro j hj hstop
  have hj8 : j < 8 := by omega
  simp only [lengthStop] at hstop
  all_goals repeat' first | split at hstop | simp_all
  all_goals interval_cases j <;> simp_all

theorem lengthOffsetWord_eq (input : ByteArray) (hfit : CalldataFits input) :
    (lengthOffsetWord input).toNat =
      Padding.messageOffset + Padding.paddedLength input.size - 8 := by
  have hlt := Padding.paddedLength_lt input.size
  have hsum : Padding.paddedLength input.size + 0x478 < 2 ^ 256 := by
    unfold CalldataFits at hfit
    norm_num at hfit ⊢
    omega
  rw [lengthOffsetWord, Padding.paddedWord_eq input hfit,
    Challenge.EvmProof.Word.ofNat_add_ofNat hsum,
    Challenge.EvmProof.Word.word_toNat_ofNat, Nat.mod_eq_of_lt hsum]
  unfold Padding.messageOffset
  omega

theorem lengthAddr_toNat (input : ByteArray) (hfit : CalldataFits input)
    (i : Nat) (hi : i ≤ 8) :
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
    (i : Nat) (_hi : i < 8) :
    Challenge.EvmProof.Stepper.runLocatedBlock lengthBodyPath
      (lengthLoopState input i) = some (lengthSteppedState input i) := by
  simp [lengthBodyPath, lengthIterationPath,
    Challenge.EvmProof.Stepper.runLocatedBlock,
    Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
    lengthSteppedState, lengthLoopState, lengthLoopMemory, lengthAddr,
    lengthShift, List.exchange, State.activeWordsAfterUInt256,
    lengthLoopActiveWords]

private theorem run_lengthBranchBack (input : ByteArray) (i : Nat)
    (hne : lengthShift input (i + 1) ≠ ⟨0⟩) :
    Challenge.EvmProof.Stepper.runLocatedBlock lengthBranchPath
      (lengthSteppedState input i) = some (lengthBackReturned input i) := by
  have htrue : UInt256.isTrue (lengthShift input (i + 1)) = true := by
    simp [UInt256.isTrue, toNat_ne_zero_of_ne _ hne]
  simp [lengthBranchPath, lengthIterationPath,
    Challenge.EvmProof.Stepper.runLocatedBlock,
    Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
    lengthSteppedState, lengthBranchReady, lengthBackReturned, htrue]

private theorem run_lengthBranchExit (input : ByteArray) (i : Nat)
    (hz : lengthShift input (i + 1) = ⟨0⟩) :
    Challenge.EvmProof.Stepper.runLocatedBlock lengthBranchPath
      (lengthSteppedState input i) = some (lengthExitPending input i) := by
  have hfalse : UInt256.isTrue (lengthShift input (i + 1)) = false := by
    simp [UInt256.isTrue, hz]
  simp [lengthBranchPath, lengthIterationPath,
    Challenge.EvmProof.Stepper.runLocatedBlock,
    Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
    lengthSteppedState, lengthBranchReady, lengthExitPending, hfalse]

def gasSteps_lengthIteration (input : ByteArray) (hfit : CalldataFits input)
    (i : Nat) (hi : i < 8) (hne : lengthShift input (i + 1) ≠ ⟨0⟩) :
    Challenge.EvmProof.GasSteps (lengthLoopState input i)
      (lengthLoopState input (i + 1)) := by
  have g₁ := Challenge.EvmProof.Stepper.runLocatedBlock_sound
    Artifact.submissionArtifact .Osaka lengthBodyPath (by rfl) (by rfl)
    (run_lengthBody input hfit i hi) (by rfl) (by rfl)
  have g2raw := Challenge.EvmProof.Stepper.runLocatedBlock_sound
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
    pc := UInt256.ofNat 388
    stack := [UInt256.ofNat 0, Padding.paddedWord input] }

private theorem lengthLoopActiveWords_succ_toNat (input : ByteArray)
    (hfit : CalldataFits input) (i : Nat) (hi : i ≤ 8) :
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
    (Padding.messageOffset + Padding.paddedLength input.size) / 32 ≤
      (padReturned input).activeWords.toNat := by
  have hp := lengthStop_pos input
  have hl := lengthStop_le input
  let j := lengthStop input - 1
  have hs : lengthStop input = j + 1 := by dsimp [j]; omega
  change _ ≤ (lengthLoopActiveWords input (lengthStop input)).toNat
  rw [hs, lengthLoopActiveWords_succ_toNat input hfit j (by dsimp [j]; omega)]
  apply Nat.le_trans ?_ (Nat.le_max_right _ _)
  unfold Padding.messageOffset
  omega

@[simp] theorem padReturned_pc (input : ByteArray) :
    (padReturned input).pc = UInt256.ofNat 388 := by rfl

@[simp] theorem padReturned_stack (input : ByteArray) :
    (padReturned input).stack = [UInt256.ofNat 0, Padding.paddedWord input] := by rfl

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
    (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [⟨267, .op .POP, by rfl, wfOp (by decide) trivial rfl⟩]

@[simp] private theorem pcExitPop :
    Artifact.submissionArtifact.instructionPC 267 = 387 := by
  rw [Challenge.Ripemd160.Submission.Proofs.Bytecode.ArtifactByteLength.instructionPC_eq_byteLength]; rfl

def lengthExitEntered (input : ByteArray) (i : Nat) : State :=
  { lengthLoopState input i with pc := UInt256.ofNat 387 }

private theorem lengthExitPending_eq (input : ByteArray) (i : Nat) :
    lengthExitPending input i = lengthExitEntered input (i + 1) := by
  unfold lengthExitPending lengthBranchReady lengthSteppedState
    lengthExitEntered lengthLoopState
  generalize padSentinel input = s
  cases s
  rfl

/-- After the final `POP` the padding code falls through into the driver
entry at pc 364. -/
def lengthExitReturned (input : ByteArray) (i : Nat) : State :=
  { lengthExitEntered input i with
    pc := UInt256.ofNat 388
    stack := [lengthShift input i, Padding.paddedWord input] }

@[simp] private theorem lengthExitEntered_halt (input : ByteArray) (i : Nat) :
    (lengthExitEntered input i).halt = .Running := by rfl

@[simp] private theorem lengthExitEntered_pc (input : ByteArray) (i : Nat) :
    (lengthExitEntered input i).pc = UInt256.ofNat 387 := by rfl

@[simp] private theorem lengthExitEntered_code (input : ByteArray) (i : Nat) :
    (lengthExitEntered input i).executionEnv.code = submissionBytecode := by rfl

private theorem run_lengthExitPop (input : ByteArray) (i : Nat) :
    Challenge.EvmProof.Stepper.runLocatedBlock lengthExitPath
      (lengthExitEntered input i) = some (lengthExitReturned input i) := by
  simp [lengthExitPath,
    Challenge.EvmProof.Stepper.runLocatedBlock,
    Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
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
  rw [padSentinel, padCopied]
  rw [MachineState.writeBytes_size, MachineState.writeBytes_size]
  simp only [Challenge.EvmProof.Memory.readPadded_size, oneByte_size]
  split <;> split <;>
    unfold Padding.messageOffset at hbase ⊢ <;> omega

/-! ## Final footer image -/

theorem lengthBytes_of_shift_zero (input : ByteArray) (hfit : CalldataFits input)
    (i j : Nat) (hij : i ≤ j) (hj : j < 8) (hz : lengthShift input i = ⟨0⟩) :
    (Padding.lengthBytes input)[j]?.getD 0 = 0 := by
  have hzn : input.size * 8 % 2 ^ 64 / 2 ^ (8 * i) = 0 := by
    have := lengthShift_toNat input hfit i
    rw [hz] at this
    simpa using this.symm
  have hlt : input.size * 8 % 2 ^ 64 < 2 ^ (8 * i) := by
    exact Nat.lt_of_div_eq_zero (by positivity) hzn
  rw [Challenge.EvmProof.Memory.getD0_eq_getElem _ _
    (by simpa using hj : j < (Padding.lengthBytes input).size),
    Padding.lengthByte input j hj]
  have hdiv : input.size * 8 / 2 ^ (8 * j) % 256 =
      input.size * 8 % 2 ^ 64 / 2 ^ (8 * j) % 256 :=
    (mod64_div_byte (input.size * 8) j hj).symm
  rw [hdiv]
  have : input.size * 8 % 2 ^ 64 / 2 ^ (8 * j) = 0 := by
    apply Nat.div_eq_of_lt
    exact Nat.lt_of_lt_of_le hlt (Nat.pow_le_pow_right (by norm_num) (by omega))
  rw [this]
  rfl

theorem topByte_eq (input : ByteArray) (hfit : CalldataFits input) :
    UInt8.ofNat ((topByteWord input).toNat % 256) =
      (Padding.lengthBytes input)[7]?.getD 0 := by
  have hlt : (bitLengthWord input).toNat < 2 ^ 256 := (bitLengthWord input).val.isLt
  have hshift : (topByteWord input).toNat = input.size * 8 % 2 ^ 64 / 2 ^ 56 := by
    rw [topByteWord,
      Challenge.EvmProof.Word.word_eq_ofNat_toNat (bitLengthWord input),
      Challenge.EvmProof.Word.shiftRight_ofNat hlt (by norm_num : (0x38 : Nat) < 256),
      Challenge.EvmProof.Word.word_toNat_ofNat, Nat.shiftRight_eq_div_pow,
      bitLengthWord_toNat input hfit]
    rw [Nat.mod_eq_of_lt]
    exact Nat.lt_of_le_of_lt (Nat.div_le_self _ _)
      (Nat.lt_of_lt_of_le (Nat.mod_lt _ (by positivity)) (by norm_num))
  rw [hshift,
    Challenge.EvmProof.Memory.getD0_eq_getElem _ _
      (by simp : (7 : Nat) < (Padding.lengthBytes input).size),
    Padding.lengthByte input 7 (by norm_num)]
  congr 1
  have h7 := mod64_div_byte (input.size * 8) 7 (by norm_num)
  simpa using h7

theorem lengthShift_byte_eq (input : ByteArray) (hfit : CalldataFits input)
    (i : Nat) (hi : i < 8) :
    UInt8.ofNat ((lengthShift input i).toNat % 256) =
      (Padding.lengthBytes input)[i]?.getD 0 := by
  rw [lengthShift_toNat input hfit i,
    Challenge.EvmProof.Memory.getD0_eq_getElem _ _
      (by simpa using hi : i < (Padding.lengthBytes input).size),
    Padding.lengthByte input i hi]
  congr 1
  exact mod64_div_byte (input.size * 8) i hi

/-- Pointwise image of the footer memory after `i` loop steps. -/
theorem lengthLoopMemory_getD (input : ByteArray) (hfit : CalldataFits input)
    (i : Nat) (hi : i ≤ 8) (a : Nat) :
    (lengthLoopMemory input i)[a]?.getD 0 =
      if (Padding.messageOffset + Padding.paddedLength input.size - 8) ≤ a ∧ a < (Padding.messageOffset + Padding.paddedLength input.size - 8) + i then
        (Padding.lengthBytes input)[a - (Padding.messageOffset + Padding.paddedLength input.size - 8)]?.getD 0
      else (padSentinel input).memory[a]?.getD 0 := by
  induction i with
  | zero =>
      have hzero : ¬ ((Padding.messageOffset + Padding.paddedLength input.size - 8) ≤ a ∧
          a < (Padding.messageOffset + Padding.paddedLength input.size - 8) + 0) := by
        omega
      rw [lengthLoopMemory, if_neg hzero]
  | succ i ih =>
      have hii : i < 8 := by omega
      rw [lengthLoopMemory, MachineState.writeBytes_getElem?_getD,
        lengthAddr_toNat input hfit i (by omega),
        lengthShift_byte_eq input hfit i hii, ih (by omega)]
      simp only [oneByte_size]
      by_cases hin : (Padding.messageOffset + Padding.paddedLength input.size - 8) + i ≤ a ∧ a < (Padding.messageOffset + Padding.paddedLength input.size - 8) + i + 1
      · have haeq : a = (Padding.messageOffset + Padding.paddedLength input.size - 8) + i := by omega
        subst haeq
        rw [if_pos (by omega), if_pos (by omega), Nat.sub_self,
          Nat.add_sub_cancel_left]
        rfl
      · rw [if_neg (by omega)]
        by_cases hlt : (Padding.messageOffset + Padding.paddedLength input.size - 8) ≤ a ∧ a < (Padding.messageOffset + Padding.paddedLength input.size - 8) + i
        · rw [if_pos hlt, if_pos (by omega)]
        · have hne : ¬ ((Padding.messageOffset + Padding.paddedLength input.size - 8) ≤ a ∧ a < (Padding.messageOffset + Padding.paddedLength input.size - 8) + (i + 1)) := by
            omega
          rw [if_neg hlt, if_neg hne]

theorem padFinalMemory_getD (input : ByteArray) (_hfit : CalldataFits input) (a : Nat) :
    (padFinalMemory input)[a]?.getD 0 =
      if (Padding.messageOffset + Padding.paddedLength input.size - 8) ≤ a ∧ a < (Padding.messageOffset + Padding.paddedLength input.size - 8) + 8 then
        (Padding.lengthBytes input)[a - (Padding.messageOffset + Padding.paddedLength input.size - 8)]?.getD 0
      else (padSentinel input).memory[a]?.getD 0 := by
  have hstop : lengthStop input ≤ 8 := lengthStop_le input
  have hzero := lengthShift_stop_zero input _hfit
  change (lengthLoopMemory input (lengthStop input))[a]?.getD 0 = _
  rw [lengthLoopMemory_getD input _hfit (lengthStop input) hstop a]
  by_cases hin :
      (Padding.messageOffset + Padding.paddedLength input.size - 8) ≤ a ∧
        a < (Padding.messageOffset + Padding.paddedLength input.size - 8) + lengthStop input
  · rw [if_pos hin, if_pos (by omega)]
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
    (hfit : CalldataFits input) (a : Nat) :
    (padFinalMemory input)[a]?.getD 0 =
      (Padding.paddedMemory (padLengthReady input).memory input)[a]?.getD 0 := by
  have hsentinel : (padSentinel input).memory =
      Padding.sentinelMemory (padLengthReady input).memory input := by
    simp [padSentinel, padCopied, Padding.sentinelMemory,
      Padding.copiedMemory, Challenge.EvmProof.Memory.readPadded_zero_size]
  rw [padFinalMemory_getD input hfit a, Padding.paddedMemory,
    MachineState.writeBytes_getElem?_getD, hsentinel]
  simp only [Padding.lengthBytes_size]

theorem padReturned_memory (input : ByteArray) (_hfit : CalldataFits input) :
    (padReturned input).memory = padFinalMemory input := by
  rfl

theorem padReturned_readPadded (input : ByteArray) (hfit : CalldataFits input)
    (a n : Nat) :
    MachineState.readPadded (padReturned input).memory a n =
      MachineState.readPadded
        (Padding.paddedMemory (padLengthReady input).memory input) a n := by
  apply Challenge.EvmProof.Memory.readPadded_congr
  intro i _hi
  rw [padReturned_memory input hfit]
  exact padFinalMemory_getD_paddedMemory input hfit (a + i)

theorem padReturned_readWord (input : ByteArray) (hfit : CalldataFits input)
    (a : Nat) :
    MachineState.readWord (padReturned input).memory a =
      MachineState.readWord
        (Padding.paddedMemory (padLengthReady input).memory input) a := by
  unfold MachineState.readWord
  rw [padReturned_readPadded input hfit a 32]

theorem lengthLoopMemory_size (input : ByteArray) (hfit : CalldataFits input)
    (i : Nat) (hi : i ≤ 8) :
    (lengthLoopMemory input i).size =
      if i = 0 then (padSentinel input).memory.size
      else (Padding.messageOffset + Padding.paddedLength input.size - 8) + i := by
  induction i with
  | zero =>
      simp [lengthLoopMemory]
  | succ i ih =>
      have hii : i < 8 := by omega
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
  have hstop : lengthStop input ≤ 8 := lengthStop_le input
  have hs := lengthLoopMemory_size input hfit (lengthStop input) hstop
  have hstop0 : lengthStop input ≠ 0 := Nat.ne_of_gt (lengthStop_pos input)
  change (lengthLoopMemory input (lengthStop input)).size = _
  unfold footerStart
  rw [hs, if_neg hstop0]

theorem lengthLoopMemory_final_at_stop (input : ByteArray) :
    lengthLoopMemory input (lengthStop input) = padFinalMemory input := by
  rfl

private theorem lengthExitReturned_eq_stop (input : ByteArray)
    (hfit : CalldataFits input) :
    lengthExitReturned input (lengthStop input) = padReturned input := by
  unfold lengthExitReturned lengthExitEntered padReturned
  rw [lengthShift_stop_zero input hfit]
  rfl

def gasSteps_lengthExitEntered (input : ByteArray) (i : Nat) :
    Challenge.EvmProof.GasSteps (lengthExitEntered input i)
      (lengthExitReturned input i) := by
  have g1raw := Challenge.EvmProof.Stepper.runLocatedBlock_sound
    Artifact.submissionArtifact .Osaka lengthExitPath (by rfl) (by rfl)
    (run_lengthExitPop input i) (by rfl) (by rfl)
  exact Challenge.EvmProof.GasSteps.cast g1raw rfl rfl

def gasSteps_lengthIterationExit (input : ByteArray) (hfit : CalldataFits input)
    (i : Nat) (hi : i < 8) (hz : lengthShift input (i + 1) = ⟨0⟩) :
    Challenge.EvmProof.GasSteps (lengthLoopState input i)
      (lengthExitReturned input (i + 1)) := by
  have g₁ := Challenge.EvmProof.Stepper.runLocatedBlock_sound
    Artifact.submissionArtifact .Osaka lengthBodyPath (by rfl) (by rfl)
    (run_lengthBody input hfit i hi) (by rfl) (by rfl)
  have g2raw := Challenge.EvmProof.Stepper.runLocatedBlock_sound
    Artifact.submissionArtifact .Osaka lengthBranchPath (by rfl) (by rfl)
    (run_lengthBranchExit input i hz) (by rfl) (by rfl)
  have g₂ := Challenge.EvmProof.GasSteps.cast g2raw rfl
    (lengthExitPending_eq input i)
  exact g₁.trans (g₂.trans
    (gasSteps_lengthExitEntered input (i + 1)))

/-- Run the footer loop from a known nonzero residual with bounded shifts left. -/
noncomputable def gasSteps_lengthLoopFrom (input : ByteArray)
    (hfit : CalldataFits input) :
    (fuel i : Nat) → i + fuel = 8 →
      (∀ j, 0 < j → j ≤ i → lengthShift input j ≠ ⟨0⟩) →
      lengthShift input i ≠ ⟨0⟩ →
    Challenge.EvmProof.GasSteps (lengthLoopState input i) (padReturned input)
  | 0, i, hsum, _hprior, hne => by
      have hi : i = 8 := by omega
      subst hi
      exact False.elim (hne (lengthShift_eight input hfit))
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
      (gasSteps_lengthLoopFrom input hfit 7 1 (by norm_num)
        (fun j hj hle => by
          have hj1 : j = 1 := by omega
          subst hj1
          exact hz) hz)

set_option maxHeartbeats 400000 in
private theorem run_lengthFooterSetup (input : ByteArray) :
    Challenge.EvmProof.Stepper.runLocatedBlock lengthFooterSetupPath
      (padSentinel input) = some (lengthLoopState input 0) := by
  have haddressOrder : UInt256.ofNat 1144 + Padding.paddedWord input =
      Padding.paddedWord input + UInt256.ofNat 1144 := Challenge.EvmProof.Word.word_add_comm _ _
  simp [lengthFooterSetupPath, lengthSetupPath, Artifact.padSetupPath,
    Challenge.EvmProof.Stepper.runLocatedBlock,
    Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
    lengthLoopState, lengthLoopMemory, lengthLoopActiveWords,
    lengthAddr, lengthShift,
    lengthOffsetWord, bitLengthWord, haddressOrder]

def gasSteps_lengthSetup (input : ByteArray) (hfit : CalldataFits input) :
    Challenge.EvmProof.GasSteps (padLengthReady input)
      (lengthLoopState input 0) := by
  have g₁ := Challenge.EvmProof.Stepper.runLocatedBlock_sound
    Artifact.submissionArtifact .Osaka lengthCopyPath (by rfl) (by rfl)
    (run_lengthCopy input hfit) (by rfl) deployAddress_not_precompile
  have g₂ₐ := Challenge.EvmProof.Stepper.runLocatedBlock_sound
    Artifact.submissionArtifact .Osaka lengthSentinelAddressPath (by rfl) (by rfl)
    (run_lengthSentinelAddress input) (by rfl) deployAddress_not_precompile
  have g2raw := Challenge.EvmProof.Stepper.runLocatedBlock_sound
    Artifact.submissionArtifact .Osaka lengthSentinelStorePath (by rfl) (by rfl)
    (run_lengthSentinelStore input hfit) (by rfl) deployAddress_not_precompile
  have g2b := Challenge.EvmProof.GasSteps.cast g2raw rfl
    (padSentinelStored_eq input hfit)
  have g₂ := g₂ₐ.trans g2b
  have g₃ := Challenge.EvmProof.Stepper.runLocatedBlock_sound
    Artifact.submissionArtifact .Osaka lengthFooterSetupPath (by rfl) (by rfl)
    (run_lengthFooterSetup input) (by rfl) deployAddress_not_precompile
  exact g₁.trans (g₂.trans g₃)

/-- Complete certified execution from the challenge initial state through the
RIPEMD-160 padding function. -/
private def gasSteps_padPrefix (input : ByteArray)
    (entryPrefix : Challenge.EvmProof.GasSteps (initialState submissionBytecode input 0)
      (Execution.atPC input 335)) :
    Challenge.EvmProof.GasSteps (initialState submissionBytecode input 0)
      (padLengthReady input) :=
  (Main.gasSteps_initialize input entryPrefix).trans
    ((gasSteps_enterPad input).trans (gasSteps_paddedLength input))

noncomputable def gasSteps_padBody (input : ByteArray) (hfit : CalldataFits input) :
    Challenge.EvmProof.GasSteps (padLengthReady input) (padReturned input) :=
  (gasSteps_lengthSetup input hfit).trans (gasSteps_lengthLoop input hfit)

noncomputable def gasSteps_pad (input : ByteArray) (hfit : CalldataFits input)
    (entryPrefix : Challenge.EvmProof.GasSteps (initialState submissionBytecode input 0)
      (Execution.atPC input 335)) :
    Challenge.EvmProof.GasSteps (initialState submissionBytecode input 0)
      (padReturned input) :=
  (gasSteps_padPrefix input entryPrefix).trans (gasSteps_padBody input hfit)

#print axioms gasSteps_pad

end Challenge.Ripemd160.Submission.Proofs.Bytecode.PaddingTrace
