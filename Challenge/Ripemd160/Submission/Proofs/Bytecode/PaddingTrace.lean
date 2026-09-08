import Challenge.Ripemd160.Submission.Proofs.Bytecode.Padding
import Challenge.Ripemd160.Submission.Proofs.Bytecode.Trace
import Challenge.Ripemd160.Submission.Proofs.Bytecode.Main
import Challenge.Ripemd160.Submission.Proofs.Bytecode.ShortPaddingMemory
import Challenge.Ripemd160.Submission.Proofs.Bytecode.ShortFooter
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

private def wfOp {op : Operation}
    (hopcode : Decode.opcodeOf (YulEvmCompiler.Instr.opByte op) = some op)
    (hplain : YulEvmCompiler.plainOp op)
    (havailable : op.availableInFork .Osaka = true) :
    Challenge.EvmProof.Stepper.WellFormed .Osaka (.op op) :=
  ⟨hopcode, hplain, havailable⟩

@[simp] private theorem slowRefPC4056 :
    Artifact.submissionArtifact.instructionPC 4056 = 5308 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide +kernel

@[simp] private theorem slowPC4056 :
    Artifact.instructionPC 4056 = 5308 := slowRefPC4056

@[simp] private theorem slowRefPC4057 :
    Artifact.submissionArtifact.instructionPC 4057 = 5309 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide +kernel

@[simp] private theorem slowPC4057 :
    Artifact.instructionPC 4057 = 5309 := slowRefPC4057

@[simp] private theorem slowRefPC4058 :
    Artifact.submissionArtifact.instructionPC 4058 = 5311 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide +kernel

@[simp] private theorem slowPC4058 :
    Artifact.instructionPC 4058 = 5311 := slowRefPC4058

@[simp] private theorem slowRefPC4059 :
    Artifact.submissionArtifact.instructionPC 4059 = 5312 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide +kernel

@[simp] private theorem slowPC4059 :
    Artifact.instructionPC 4059 = 5312 := slowRefPC4059

@[simp] private theorem slowRefPC4060 :
    Artifact.submissionArtifact.instructionPC 4060 = 5314 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide +kernel

@[simp] private theorem slowPC4060 :
    Artifact.instructionPC 4060 = 5314 := slowRefPC4060

@[simp] private theorem slowRefPC4061 :
    Artifact.submissionArtifact.instructionPC 4061 = 5315 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide +kernel

@[simp] private theorem slowPC4061 :
    Artifact.instructionPC 4061 = 5315 := slowRefPC4061

@[simp] private theorem slowRefPC4062 :
    Artifact.submissionArtifact.instructionPC 4062 = 5318 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide +kernel

@[simp] private theorem slowPC4062 :
    Artifact.instructionPC 4062 = 5318 := slowRefPC4062

@[simp] private theorem slowRefPC4063 :
    Artifact.submissionArtifact.instructionPC 4063 = 5319 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide +kernel

@[simp] private theorem slowPC4063 :
    Artifact.instructionPC 4063 = 5319 := slowRefPC4063

@[simp] private theorem slowRefPC4064 :
    Artifact.submissionArtifact.instructionPC 4064 = 5320 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide +kernel

@[simp] private theorem slowPC4064 :
    Artifact.instructionPC 4064 = 5320 := slowRefPC4064

@[simp] private theorem slowRefPC4065 :
    Artifact.submissionArtifact.instructionPC 4065 = 5321 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide +kernel

@[simp] private theorem slowPC4065 :
    Artifact.instructionPC 4065 = 5321 := slowRefPC4065

@[simp] private theorem slowRefPC4066 :
    Artifact.submissionArtifact.instructionPC 4066 = 5322 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide +kernel

@[simp] private theorem slowPC4066 :
    Artifact.instructionPC 4066 = 5322 := slowRefPC4066

@[simp] private theorem slowRefPC4067 :
    Artifact.submissionArtifact.instructionPC 4067 = 5324 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide +kernel

@[simp] private theorem slowPC4067 :
    Artifact.instructionPC 4067 = 5324 := slowRefPC4067

@[simp] private theorem slowRefPC4068 :
    Artifact.submissionArtifact.instructionPC 4068 = 5325 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide +kernel

@[simp] private theorem slowPC4068 :
    Artifact.instructionPC 4068 = 5325 := slowRefPC4068

@[simp] private theorem slowRefPC4069 :
    Artifact.submissionArtifact.instructionPC 4069 = 5326 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide +kernel

@[simp] private theorem slowPC4069 :
    Artifact.instructionPC 4069 = 5326 := slowRefPC4069

@[simp] private theorem slowRefPC4070 :
    Artifact.submissionArtifact.instructionPC 4070 = 5327 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide +kernel

@[simp] private theorem slowPC4070 :
    Artifact.instructionPC 4070 = 5327 := slowRefPC4070

@[simp] private theorem slowRefPC4071 :
    Artifact.submissionArtifact.instructionPC 4071 = 5328 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide +kernel

@[simp] private theorem slowPC4071 :
    Artifact.instructionPC 4071 = 5328 := slowRefPC4071

@[simp] private theorem slowRefPC4072 :
    Artifact.submissionArtifact.instructionPC 4072 = 5329 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide +kernel

@[simp] private theorem slowPC4072 :
    Artifact.instructionPC 4072 = 5329 := slowRefPC4072

@[simp] private theorem slowRefPC4073 :
    Artifact.submissionArtifact.instructionPC 4073 = 5330 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide +kernel

@[simp] private theorem slowPC4073 :
    Artifact.instructionPC 4073 = 5330 := slowRefPC4073

@[simp] private theorem slowRefPC4074 :
    Artifact.submissionArtifact.instructionPC 4074 = 5332 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide +kernel

@[simp] private theorem slowPC4074 :
    Artifact.instructionPC 4074 = 5332 := slowRefPC4074

@[simp] private theorem slowRefPC4075 :
    Artifact.submissionArtifact.instructionPC 4075 = 5333 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide +kernel

@[simp] private theorem slowPC4075 :
    Artifact.instructionPC 4075 = 5333 := slowRefPC4075

@[simp] private theorem slowRefPC4076 :
    Artifact.submissionArtifact.instructionPC 4076 = 5334 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide +kernel

@[simp] private theorem slowPC4076 :
    Artifact.instructionPC 4076 = 5334 := slowRefPC4076

@[simp] private theorem slowRefPC4077 :
    Artifact.submissionArtifact.instructionPC 4077 = 5336 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide +kernel

@[simp] private theorem slowPC4077 :
    Artifact.instructionPC 4077 = 5336 := slowRefPC4077

@[simp] private theorem slowRefPC4078 :
    Artifact.submissionArtifact.instructionPC 4078 = 5337 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide +kernel

@[simp] private theorem slowPC4078 :
    Artifact.instructionPC 4078 = 5337 := slowRefPC4078

@[simp] private theorem slowRefPC4079 :
    Artifact.submissionArtifact.instructionPC 4079 = 5338 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide +kernel

@[simp] private theorem slowPC4079 :
    Artifact.instructionPC 4079 = 5338 := slowRefPC4079

@[simp] private theorem slowRefPC4080 :
    Artifact.submissionArtifact.instructionPC 4080 = 5339 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide +kernel

@[simp] private theorem slowPC4080 :
    Artifact.instructionPC 4080 = 5339 := slowRefPC4080

@[simp] private theorem slowRefPC4081 :
    Artifact.submissionArtifact.instructionPC 4081 = 5342 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide +kernel

@[simp] private theorem slowPC4081 :
    Artifact.instructionPC 4081 = 5342 := slowRefPC4081

@[simp] private theorem slowRefPC4082 :
    Artifact.submissionArtifact.instructionPC 4082 = 5343 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide +kernel

@[simp] private theorem slowPC4082 :
    Artifact.instructionPC 4082 = 5343 := slowRefPC4082

@[simp] private theorem slowRefPC4083 :
    Artifact.submissionArtifact.instructionPC 4083 = 5344 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide +kernel

@[simp] private theorem slowPC4083 :
    Artifact.instructionPC 4083 = 5344 := slowRefPC4083

@[simp] private theorem slowRefPC4084 :
    Artifact.submissionArtifact.instructionPC 4084 = 5345 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide +kernel

@[simp] private theorem slowPC4084 :
    Artifact.instructionPC 4084 = 5345 := slowRefPC4084

@[simp] private theorem slowRefPC4085 :
    Artifact.submissionArtifact.instructionPC 4085 = 5346 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide +kernel

@[simp] private theorem slowPC4085 :
    Artifact.instructionPC 4085 = 5346 := slowRefPC4085

def pushedReturn (input : ByteArray) : State :=
  { Main.initializedState input with
    pc := (Main.initializedState input).pc + UInt256.ofNat 3
    stack := UInt256.ofNat 0x1c4 :: (Main.initializedState input).stack }

def padEntry (input : ByteArray) : State :=
  pushedReturn input

@[simp] private theorem padEntry_halt (input : ByteArray) :
    (padEntry input).halt = .Running := by rfl

@[simp] private theorem padEntry_fork (input : ByteArray) :
    (padEntry input).fork = .Osaka := by rfl

@[simp] private theorem padEntry_code (input : ByteArray) :
    (padEntry input).executionEnv.code = submissionBytecode := by rfl

@[simp] private theorem padEntry_calldata (input : ByteArray) :
    (padEntry input).executionEnv.calldata = input := by rfl

@[simp] private theorem initializedPC764 :
    Artifact.instructionPC 199 = 0x179 := by rfl

@[simp] private theorem initializedCalldata (input : ByteArray) :
    (Main.initializedState input).executionEnv.calldata = input := by rfl

def enterPath : List
    (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  Artifact.padEnterPath

set_option maxHeartbeats 200000 in
private theorem run_enter (input : ByteArray) :
    Challenge.EvmProof.Stepper.runLocatedBlock enterPath
      (Main.initializedState input) = some (padEntry input) := by
  simp [enterPath, Artifact.padEnterPath, Challenge.EvmProof.Stepper.runLocatedBlock,
    Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
    pushedReturn, padEntry]

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
    pc := UInt256.ofNat (Artifact.instructionPC 207)
    stack := [UInt256.ofNat input.size, Padding.paddedWord input,
      UInt256.ofNat 0x1c4] }

@[simp] private theorem padLengthReady_halt (input : ByteArray) :
    (padLengthReady input).halt = .Running := by rfl

@[simp] private theorem padLengthReady_fork (input : ByteArray) :
    (padLengthReady input).fork = .Osaka := by rfl

@[simp] private theorem padLengthReady_code (input : ByteArray) :
    (padLengthReady input).executionEnv.code = submissionBytecode := by rfl

@[simp] private theorem padLengthReady_calldata (input : ByteArray) :
    (padLengthReady input).executionEnv.calldata = input := by rfl

@[simp] private theorem padLengthReady_pcToNat (input : ByteArray) :
    (padLengthReady input).pc.toNat = 0x185 := by rfl

@[simp] private theorem padLengthReady_pc (input : ByteArray) :
    (padLengthReady input).pc = UInt256.ofNat 0x185 := by rfl

@[simp] private theorem padLengthReady_pcSucc (input : ByteArray) :
    (padLengthReady input).pc.succ = UInt256.ofNat 0x186 := by
  rw [padLengthReady_pc, Challenge.EvmProof.Word.succ_ofNat (by norm_num)]

@[simp] private theorem padLengthReady_stack (input : ByteArray) :
    (padLengthReady input).stack =
      [UInt256.ofNat input.size, Padding.paddedWord input, UInt256.ofNat 0x1c4] := by
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
    padEntry, pushedReturn, padLengthReady,
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
  Padding.paddedWord input + UInt256.ofNat 0x118

def padCopied (input : ByteArray) : State :=
  { padLengthReady input with
    pc := UInt256.ofNat (Artifact.instructionPC 211)
    memory := MachineState.writeBytes (padLengthReady input).memory
      (MachineState.readPadded input 0 input.size) Padding.messageOffset
    activeWords := (padLengthReady input).activeWordsAfterUInt256
      Padding.messageOffset input.size }

def padSentinel (input : ByteArray) : State :=
  { padCopied input with
    pc := UInt256.ofNat (Artifact.instructionPC 216)
    stack := [UInt256.ofNat input.size, Padding.paddedWord input,
      UInt256.ofNat 0x1c4]
    memory := MachineState.writeBytes (padCopied input).memory
      (ByteArray.mk #[0x80]) (Padding.messageOffset + input.size)
    activeWords := (padCopied input).activeWordsAfterUInt256
      (Padding.messageOffset + input.size) 1 }

def padFullCopied (input : ByteArray) : State :=
  { padLengthReady input with
    pc := UInt256.ofNat (Artifact.instructionPC 211)
    memory := MachineState.writeBytes (padLengthReady input).memory
      (MachineState.readPadded input 0 (Padding.paddedLength input.size)) Padding.messageOffset
    activeWords := (padLengthReady input).activeWordsAfterUInt256
      Padding.messageOffset (Padding.paddedLength input.size) }

def padFullSentinel (input : ByteArray) : State :=
  { padFullCopied input with
    pc := UInt256.ofNat (Artifact.instructionPC 216)
    stack := [UInt256.ofNat input.size, Padding.paddedWord input,
      UInt256.ofNat 0x1c4]
    memory := MachineState.writeBytes (padFullCopied input).memory
      (ByteArray.mk #[0x80]) (Padding.messageOffset + input.size)
    activeWords := (padFullCopied input).activeWordsAfterUInt256
      (Padding.messageOffset + input.size) 1 }

@[simp] private theorem padCopied_halt (input : ByteArray) :
    (padCopied input).halt = .Running := by rfl

@[simp] private theorem padCopied_pcToNat (input : ByteArray) :
    (padCopied input).pc.toNat = 0x18b := by rfl

@[simp] private theorem padCopied_pc (input : ByteArray) :
    (padCopied input).pc = UInt256.ofNat 0x18b := by rfl

@[simp] private theorem padCopied_stack (input : ByteArray) :
    (padCopied input).stack =
      [UInt256.ofNat input.size, Padding.paddedWord input, UInt256.ofNat 0x1c4] := by
  rfl

@[simp] private theorem padCopied_calldata (input : ByteArray) :
    (padCopied input).executionEnv.calldata = input := by rfl

@[simp] private theorem padSentinel_halt (input : ByteArray) :
    (padSentinel input).halt = .Running := by rfl

@[simp] private theorem padSentinel_pcToNat (input : ByteArray) :
    (padSentinel input).pc.toNat = 0x193 := by rfl

@[simp] private theorem padSentinel_pc (input : ByteArray) :
    (padSentinel input).pc = UInt256.ofNat 0x193 := by rfl

@[simp] private theorem padSentinel_pcSucc (input : ByteArray) :
    (padSentinel input).pc.succ = UInt256.ofNat 0x194 := by
  rw [padSentinel_pc, Challenge.EvmProof.Word.succ_ofNat (by norm_num)]

@[simp] private theorem padSentinel_stack (input : ByteArray) :
    (padSentinel input).stack =
      [UInt256.ofNat input.size, Padding.paddedWord input, UInt256.ofNat 0x1c4] := by
  rfl

def lengthSetupPath : List
    (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  Artifact.padSetupPath

def lengthCopyPath := lengthSetupPath.take 4
def lengthSentinelPath := (lengthSetupPath.drop 4).take 5
def lengthFooterSetupPath : List
    (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [⟨4056, .op .JUMPDEST, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨4057, .push ⟨1, by decide⟩ (UInt256.ofNat 195), by rfl, by decide⟩,
   ⟨4058, .op .SHL, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨4059, .push ⟨1, by decide⟩ (UInt256.ofNat 192), by rfl, by decide⟩,
   ⟨4060, .op .SHR, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨4061, .push ⟨2, by decide⟩ (UInt256.ofNat 280), by rfl, by decide⟩,
   ⟨4062, .op (.Dup ⟨2, by decide⟩), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨4063, .op .ADD, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨4064, .push ⟨0, by decide⟩ ⟨0⟩, by rfl, by decide⟩,
   ⟨4065, .op (.Dup ⟨1, by decide⟩), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨4066, .push ⟨1, by decide⟩ (UInt256.ofNat 7), by rfl, by decide⟩,
   ⟨4067, .op .ADD, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨4068, .op .MSTORE8, by rfl, wfOp (by decide) trivial rfl⟩]
def shortGuardPath : List
    (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [⟨216, .op (.Dup ⟨0, by decide⟩), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨217, .push ⟨1, by decide⟩ (UInt256.ofNat 13), by rfl, by decide⟩,
   ⟨218, .op .SHR, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨219, .push ⟨2, by decide⟩ (UInt256.ofNat 5308), by rfl, by decide⟩,
   ⟨220, .op .JUMPI, by rfl, wfOp (by decide) trivial rfl⟩]

def shortBodyPath : List
    (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [⟨221, .op (.Dup ⟨1, by decide⟩), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨222, .push ⟨2, by decide⟩ (UInt256.ofNat 280), by rfl, by decide⟩,
   ⟨223, .op .ADD, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨224, .op (.Dup ⟨1, by decide⟩), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨225, .push ⟨1, by decide⟩ (UInt256.ofNat 3), by rfl, by decide⟩,
   ⟨226, .op .SHL, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨227, .op (.Dup ⟨1, by decide⟩), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨228, .op .MSTORE8, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨229, .push ⟨1, by decide⟩ (UInt256.ofNat 1), by rfl, by decide⟩,
   ⟨230, .op .ADD, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨231, .op (.Swap ⟨0, by decide⟩), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨232, .push ⟨1, by decide⟩ (UInt256.ofNat 5), by rfl, by decide⟩,
   ⟨233, .op .SHR, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨234, .op (.Swap ⟨0, by decide⟩), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨235, .op .MSTORE8, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨236, .push ⟨0, by decide⟩ ⟨0⟩, by rfl, by decide⟩,
   ⟨237, .op (.Swap ⟨0, by decide⟩), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨238, .op (.Swap ⟨1, by decide⟩), by rfl, wfOp (by decide) trivial rfl⟩]

def shortReturnPath : List
    (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [⟨239, .op .JUMP, by rfl, wfOp (by decide) trivial rfl⟩]

def lengthSentinelAddressPath := lengthSentinelPath.take 4
def lengthSentinelStorePath := lengthSentinelPath.drop 4

def padSentinelAddressReady (input : ByteArray) : State :=
  { padFullCopied input with
    pc := UInt256.ofNat (Artifact.instructionPC 215)
    stack := [UInt256.ofNat Padding.messageOffset + UInt256.ofNat input.size,
      UInt256.ofNat 128, UInt256.ofNat input.size, Padding.paddedWord input,
      UInt256.ofNat 0x1c4] }

def padSentinelStored (input : ByteArray) : State :=
  { padSentinelAddressReady input with
    pc := UInt256.ofNat (Artifact.instructionPC 216)
    stack := [UInt256.ofNat input.size, Padding.paddedWord input,
      UInt256.ofNat 0x1c4]
    memory := MachineState.writeBytes (padSentinelAddressReady input).memory
      (ByteArray.mk #[0x80])
      (UInt256.ofNat Padding.messageOffset + UInt256.ofNat input.size).toNat
    activeWords := (padSentinelAddressReady input).activeWordsAfterUInt256
      (UInt256.ofNat Padding.messageOffset + UInt256.ofNat input.size).toNat 1 }

@[simp] private theorem padSentinelAddressReady_halt (input : ByteArray) :
    (padSentinelAddressReady input).halt = .Running := by rfl

@[simp] private theorem padSentinelAddressReady_pc (input : ByteArray) :
    (padSentinelAddressReady input).pc = UInt256.ofNat 0x192 := by rfl

@[simp] private theorem padSentinelAddressReady_stack (input : ByteArray) :
    (padSentinelAddressReady input).stack =
      [UInt256.ofNat Padding.messageOffset + UInt256.ofNat input.size,
        UInt256.ofNat 128, UInt256.ofNat input.size, Padding.paddedWord input,
        UInt256.ofNat 0x1c4] := by rfl

@[simp] private theorem padSentinelAddressReady_memory (input : ByteArray) :
    (padSentinelAddressReady input).memory = (padFullCopied input).memory := by rfl

@[simp] private theorem padSentinelAddressReady_activeWords (input : ByteArray) :
    (padSentinelAddressReady input).activeWords = (padFullCopied input).activeWords := by rfl

set_option maxHeartbeats 200000 in
private theorem run_lengthCopy (input : ByteArray) (hfit : CalldataFits input) :
    Challenge.EvmProof.Stepper.runLocatedBlock lengthCopyPath
      (padLengthReady input) = some (padFullCopied input) := by
  have hpad : Padding.paddedLength input.size < 2 ^ 256 := by
    have := Padding.paddedLength_lt input.size
    unfold CalldataFits at hfit
    norm_num at hfit ⊢
    omega
  have hpadWord : (Padding.paddedWord input).toNat = Padding.paddedLength input.size := by
    rw [Padding.paddedWord_eq input hfit, Challenge.EvmProof.Word.word_toNat_ofNat,
      Nat.mod_eq_of_lt hpad]
  have hzero : (⟨0⟩ : UInt256) = UInt256.ofNat 0 := by rfl
  simp [lengthCopyPath, lengthSetupPath, Artifact.padSetupPath,
    Challenge.EvmProof.Stepper.runLocatedBlock,
    Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
    padFullCopied, padLengthReady, State.activeWordsAfterUInt256, Padding.messageOffset,
    hpadWord, hzero]

set_option maxHeartbeats 200000 in
private theorem run_lengthSentinelAddress (input : ByteArray) :
    Challenge.EvmProof.Stepper.runLocatedBlock lengthSentinelAddressPath
      (padFullCopied input) = some (padSentinelAddressReady input) := by
  simp [lengthSentinelAddressPath, lengthSentinelPath, lengthSetupPath,
    Artifact.padSetupPath, Challenge.EvmProof.Stepper.runLocatedBlock,
    Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
    padSentinelAddressReady, padFullCopied, padLengthReady, Padding.messageOffset]

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
    (hfit : CalldataFits input) : padSentinelStored input = padFullSentinel input := by
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
  unfold padSentinelStored padFullSentinel padSentinelAddressReady
  rw [show (UInt256.ofNat Padding.messageOffset +
    UInt256.ofNat input.size).toNat = Padding.messageOffset + input.size by
      exact haddNat]
  generalize padFullCopied input = s
  cases s
  rfl
/-! ## Little-endian footer loop

The artifact masks the bit length to 64 bits, writes the most significant
footer byte first (which also fixes the final `activeWords`), and then walks
the remaining bytes least-significant first, stopping as soon as the residual
length is zero.  Bytes it does not write are already zero, because
`MachineState.writeBytes` grows memory with zeros and the top-byte store
covers the whole footer window. -/

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

def topByteMemory (input : ByteArray) : ByteArray :=
  MachineState.writeBytes (padSentinel input).memory
    (ByteArray.mk #[0]) (topByteAddr input).toNat

def topByteActiveWords (input : ByteArray) : UInt256 :=
  UInt256.ofNat (MachineState.activeWordsAfter
    (padSentinel input).activeWords.toNat (topByteAddr input).toNat 1)

def lengthLoopMemory (input : ByteArray) : Nat → ByteArray
  | 0 => topByteMemory input
  | i + 1 => MachineState.writeBytes (lengthLoopMemory input i)
      (ByteArray.mk #[UInt8.ofNat ((lengthShift input i).toNat % 256)])
      (lengthAddr input i).toNat

/-- The footer window is covered by the top-byte store, so `activeWords` is
already final when the loop starts and never moves again. -/
def lengthLoopState (input : ByteArray) (i : Nat) : State :=
  { padSentinel input with
    pc := UInt256.ofNat (Artifact.instructionPC 4069)
    stack := [lengthAddr input i, lengthShift input i,
      Padding.paddedWord input, UInt256.ofNat 0x1c4]
    memory := lengthLoopMemory input i
    activeWords := topByteActiveWords input }

def lengthIterationPath : List
    (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [⟨4069, .op .JUMPDEST, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨4070, .op (.Dup ⟨1, by decide⟩), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨4071, .op (.Dup ⟨1, by decide⟩), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨4072, .op .MSTORE8, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨4073, .push ⟨1, by decide⟩ (UInt256.ofNat 1), by rfl, by decide⟩,
   ⟨4074, .op .ADD, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨4075, .op (.Swap ⟨0, by decide⟩), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨4076, .push ⟨1, by decide⟩ (UInt256.ofNat 8), by rfl, by decide⟩,
   ⟨4077, .op .SHR, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨4078, .op (.Swap ⟨0, by decide⟩), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨4079, .op (.Dup ⟨1, by decide⟩), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨4080, .push ⟨2, by decide⟩ (UInt256.ofNat 5326), by rfl, by decide⟩,
   ⟨4081, .op .JUMPI, by rfl, wfOp (by decide) trivial rfl⟩]

def lengthBodyPath := lengthIterationPath.take 10
def lengthBranchPath := lengthIterationPath.drop 10

@[simp] private theorem lengthLoopState_halt (input : ByteArray) (i : Nat) :
    (lengthLoopState input i).halt = .Running := by rfl

@[simp] private theorem lengthLoopState_fork (input : ByteArray) (i : Nat) :
    (lengthLoopState input i).fork = .Osaka := by rfl

@[simp] private theorem lengthLoopState_code (input : ByteArray) (i : Nat) :
    (lengthLoopState input i).executionEnv.code = submissionBytecode := by rfl

@[simp] private theorem lengthLoopState_pc (input : ByteArray) (i : Nat) :
    (lengthLoopState input i).pc = UInt256.ofNat 0x14ce := by rfl

@[simp] private theorem lengthLoopState_stack (input : ByteArray) (i : Nat) :
    (lengthLoopState input i).stack =
      [lengthAddr input i, lengthShift input i,
        Padding.paddedWord input, UInt256.ofNat 0x1c4] := by rfl

@[simp] private theorem padSentinel_code (input : ByteArray) :
    (padSentinel input).executionEnv.code = submissionBytecode := by rfl

/-- State after one low-byte store and both register updates. -/
def lengthSteppedState (input : ByteArray) (i : Nat) : State :=
  { lengthLoopState input i with
    pc := UInt256.ofNat (Artifact.instructionPC 4079)
    stack := [lengthAddr input (i + 1), lengthShift input (i + 1),
      Padding.paddedWord input, UInt256.ofNat 0x1c4]
    memory := lengthLoopMemory input (i + 1) }

def lengthBranchReady (input : ByteArray) (i : Nat) : State :=
  { lengthSteppedState input i with
    pc := UInt256.ofNat (Artifact.instructionPC 4081)
    stack := [UInt256.ofNat 0x14ce, lengthShift input (i + 1)] ++
      (lengthSteppedState input i).stack }

def lengthBackReturned (input : ByteArray) (i : Nat) : State :=
  { lengthBranchReady input i with
    pc := UInt256.ofNat 0x14ce
    stack := (lengthSteppedState input i).stack }

def lengthExitPending (input : ByteArray) (i : Nat) : State :=
  { lengthBranchReady input i with
    pc := UInt256.ofNat (Artifact.instructionPC 4082)
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
    (lengthSteppedState input i).pc = UInt256.ofNat 0x14da := by rfl

@[simp] private theorem lengthBranchReady_halt (input : ByteArray) (i : Nat) :
    (lengthBranchReady input i).halt = .Running := by rfl

@[simp] private theorem lengthBranchReady_pc (input : ByteArray) (i : Nat) :
    (lengthBranchReady input i).pc = UInt256.ofNat 0x14de := by rfl

@[simp] private theorem lengthSteppedState_code (input : ByteArray) (i : Nat) :
    (lengthSteppedState input i).executionEnv.code = submissionBytecode := by rfl

@[simp] private theorem lengthBranchReady_code (input : ByteArray) (i : Nat) :
    (lengthBranchReady input i).executionEnv.code = submissionBytecode := by rfl

@[simp] private theorem validLengthLoopHead :
    Decode.isValidJumpDest submissionBytecode 0x14ce = true := by
  have hpc : Artifact.submissionArtifact.instructionPC 4069 = 0x14ce := by rfl
  rw [← hpc]
  exact Artifact.submissionArtifact.isValidJumpDest_index 4069 (by rfl)

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

theorem lengthOffsetWord_eq (input : ByteArray) (hfit : CalldataFits input) :
    (lengthOffsetWord input).toNat =
      Padding.messageOffset + Padding.paddedLength input.size - 8 := by
  have hlt := Padding.paddedLength_lt input.size
  have hsum : Padding.paddedLength input.size + 0x118 < 2 ^ 256 := by
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

private theorem topByteActiveWords_toNat (input : ByteArray)
    (hfit : CalldataFits input) :
    (topByteActiveWords input).toNat =
      Nat.max (padSentinel input).activeWords.toNat
        ((Padding.messageOffset + Padding.paddedLength input.size - 8 + 7) / 32 + 1) := by
  have hlt := Padding.paddedLength_lt input.size
  have hcur : (padSentinel input).activeWords.toNat < 2 ^ 256 :=
    (padSentinel input).activeWords.val.isLt
  have hsize : input.size < 2 ^ 256 := Nat.lt_trans hfit (by norm_num)
  have hdiv : (Padding.messageOffset + Padding.paddedLength input.size - 8 + 7) / 32
      ≤ Padding.messageOffset + Padding.paddedLength input.size - 8 + 7 :=
    Nat.div_le_self _ _
  have hbig : Padding.messageOffset + Padding.paddedLength input.size - 8 + 7 + 1
      < 2 ^ 256 := by
    unfold CalldataFits at hfit
    unfold Padding.messageOffset
    norm_num at hfit ⊢
    omega
  rw [topByteActiveWords, Challenge.EvmProof.Word.word_toNat_ofNat,
    topByteAddr_toNat input hfit]
  unfold MachineState.activeWordsAfter
  rw [if_neg (by decide : (1 : Nat) ≠ 0)]
  dsimp only
  refine Nat.mod_eq_of_lt ?_
  simp only [Nat.add_sub_cancel]
  rw [Nat.max_lt]
  exact ⟨hcur, by omega⟩

private theorem lengthLoopActiveWords_stable (input : ByteArray)
    (hfit : CalldataFits input) (i : Nat) (hi : i < 8) :
    UInt256.ofNat (MachineState.activeWordsAfter (topByteActiveWords input).toNat
      (lengthAddr input i).toNat 1) = topByteActiveWords input := by
  have hmono : (Padding.messageOffset + Padding.paddedLength input.size - 8 + i + 1 - 1) / 32
      ≤ (Padding.messageOffset + Padding.paddedLength input.size - 8 + 7) / 32 :=
    Nat.div_le_div_right (by omega)
  have hbase := topByteActiveWords_toNat input hfit
  rw [lengthAddr_toNat input hfit i (by omega)]
  unfold MachineState.activeWordsAfter
  rw [if_neg (by decide : (1 : Nat) ≠ 0)]
  dsimp only
  have hle : (Padding.messageOffset + Padding.paddedLength input.size - 8 + i + 1 - 1) / 32 + 1
      ≤ (topByteActiveWords input).toNat := by
    rw [hbase]
    exact Nat.le_trans (Nat.succ_le_succ hmono) (Nat.le_max_right _ _)
  have hmaxeq : Nat.max (topByteActiveWords input).toNat
      ((Padding.messageOffset + Padding.paddedLength input.size - 8 + i + 1 - 1) / 32 + 1)
      = (topByteActiveWords input).toNat := Nat.max_eq_left hle
  rw [hmaxeq]
  exact (Challenge.EvmProof.Word.word_eq_ofNat_toNat (topByteActiveWords input)).symm

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

private theorem run_lengthBody (input : ByteArray) (hfit : CalldataFits input)
    (i : Nat) (hi : i < 8) :
    Challenge.EvmProof.Stepper.runLocatedBlock lengthBodyPath
      (lengthLoopState input i) = some (lengthSteppedState input i) := by
  have haw := lengthLoopActiveWords_stable input hfit i hi
  simp [lengthBodyPath, lengthIterationPath,
    Challenge.EvmProof.Stepper.runLocatedBlock,
    Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
    lengthSteppedState, lengthLoopState, lengthLoopMemory, lengthAddr,
    lengthShift, List.exchange, State.activeWordsAfterUInt256, haw]

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
  Padding.paddedMemory (padLengthReady input).memory input

def padReturned (input : ByteArray) : State :=
  { lengthLoopState input 0 with
    pc := UInt256.ofNat 0x1c4
    stack := [UInt256.ofNat 0, Padding.paddedWord input]
    memory := padFinalMemory input }

@[simp] theorem padReturned_pc (input : ByteArray) :
    (padReturned input).pc = UInt256.ofNat 0x1c4 := by rfl

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
  [⟨4082, .op .POP, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨4083, .op (.Swap ⟨0, by decide⟩), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨4084, .op (.Swap ⟨1, by decide⟩), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨4085, .op .JUMP, by rfl, wfOp (by decide) trivial rfl⟩]

@[simp] private theorem validPadReturn :
    Decode.isValidJumpDest submissionBytecode 0x1c4 = true := by
  have hpc : Artifact.submissionArtifact.instructionPC 253 = 0x1c4 := by rfl
  rw [← hpc]
  exact Artifact.submissionArtifact.isValidJumpDest_index 253 (by rfl)

def lengthExitPopPath := lengthExitPath.take 3
def lengthExitJumpPath := lengthExitPath.drop 3

def lengthExitEntered (input : ByteArray) (i : Nat) : State :=
  { lengthLoopState input i with pc := UInt256.ofNat 0x14df }

private theorem lengthExitPending_eq (input : ByteArray) (i : Nat) :
    lengthExitPending input i = lengthExitEntered input (i + 1) := by
  unfold lengthExitPending lengthBranchReady lengthSteppedState
    lengthExitEntered lengthLoopState
  generalize padSentinel input = s
  cases s
  rfl

def lengthExitSwapped (input : ByteArray) (i : Nat) : State :=
  { lengthExitEntered input i with
    pc := UInt256.ofNat (Artifact.instructionPC 4085)
    stack := [UInt256.ofNat 0x1c4, lengthShift input i, Padding.paddedWord input] }

def lengthExitReturned (input : ByteArray) (i : Nat) : State :=
  { lengthExitSwapped input i with
    pc := UInt256.ofNat 0x1c4
    stack := [lengthShift input i, Padding.paddedWord input] }

@[simp] private theorem lengthExitEntered_halt (input : ByteArray) (i : Nat) :
    (lengthExitEntered input i).halt = .Running := by rfl

@[simp] private theorem lengthExitEntered_pc (input : ByteArray) (i : Nat) :
    (lengthExitEntered input i).pc = UInt256.ofNat 0x14df := by rfl

@[simp] private theorem lengthExitEntered_code (input : ByteArray) (i : Nat) :
    (lengthExitEntered input i).executionEnv.code = submissionBytecode := by rfl

@[simp] private theorem lengthExitSwapped_halt (input : ByteArray) (i : Nat) :
    (lengthExitSwapped input i).halt = .Running := by rfl

@[simp] private theorem lengthExitSwapped_pc (input : ByteArray) (i : Nat) :
    (lengthExitSwapped input i).pc = UInt256.ofNat 0x14e2 := by rfl

private theorem run_lengthExitPop (input : ByteArray) (i : Nat) :
    Challenge.EvmProof.Stepper.runLocatedBlock lengthExitPopPath
      (lengthExitEntered input i) = some (lengthExitSwapped input i) := by
  simp [lengthExitPopPath, lengthExitPath,
    Challenge.EvmProof.Stepper.runLocatedBlock,
    Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
    lengthExitEntered, lengthExitSwapped, lengthLoopState, List.exchange]

private theorem run_lengthExitJump (input : ByteArray) (i : Nat) :
    Challenge.EvmProof.Stepper.runLocatedBlock lengthExitJumpPath
      (lengthExitSwapped input i) = some (lengthExitReturned input i) := by
  simp [lengthExitJumpPath, lengthExitPath,
    Challenge.EvmProof.Stepper.runLocatedBlock,
    Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
    lengthExitSwapped, lengthExitReturned]

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

private theorem applyInitStore_size_le (s : State) (w : Artifact.InitStore)
    (hs : s.memory.size ≤ Padding.messageOffset) (hw : w ∈ Artifact.initStores) :
    (Main.applyInitStore s w).memory.size ≤ Padding.messageOffset := by
  have hoff : w.offset.toNat + 32 ≤ Padding.messageOffset := by
    simp only [Artifact.initStores, List.mem_cons, List.not_mem_nil, or_false] at hw
    rcases hw with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      decide
  rw [Main.applyInitStore, MachineState.writeBytes_size]
  split
  · exact hs
  · have h32 : (Data.Bytes.natToBytesPadded w.value.toNat 32).size = 32 := by
      simp [Data.Bytes.natToBytesPadded, ByteArray.size]
    rw [h32]
    omega

private theorem padLengthReady_size_le (input : ByteArray) :
    (padLengthReady input).memory.size ≤ Padding.messageOffset := by
  have hfold : ∀ (ws : List Artifact.InitStore) (s : State),
      (∀ w, w ∈ ws → w ∈ Artifact.initStores) →
      s.memory.size ≤ Padding.messageOffset →
      (ws.foldl Main.applyInitStore s).memory.size ≤ Padding.messageOffset := by
    intro ws
    induction ws with
    | nil => intro s _ hs; simpa using hs
    | cons w ws ih =>
        intro s hmem hs
        simp only [List.foldl_cons]
        exact ih _ (fun x hx => hmem x (by simp [hx]))
          (applyInitStore_size_le s w hs (hmem w (by simp)))
  have hmain : (Main.initializedState input).memory.size ≤ Padding.messageOffset := by
    apply hfold Artifact.initStores (Execution.mainStart input) (fun _ hw => hw)
    exact Nat.le_trans
      (Nat.le_of_eq (rfl : (Execution.mainStart input).memory.size = 0))
      (Nat.zero_le _)
  exact hmain


private theorem padFullSentinel_memory (input : ByteArray) (hfit : CalldataFits input) :
    (padFullSentinel input).memory = topByteMemory input := by
  have haddr := topByteAddr_toNat input hfit
  have hlen := Padding.input_and_footer_fit input.size
  have htop : (topByteAddr input).toNat =
      Padding.messageOffset + Padding.paddedLength input.size - 1 := by omega
  unfold padFullSentinel padFullCopied topByteMemory
  rw [htop, ShortPaddingMemory.fullCopySentinel_eq_topByte _ _
    (padLengthReady_size_le input)]
  simp [padSentinel, padCopied, Padding.sentinelMemory, Padding.copiedMemory,
    Challenge.EvmProof.Memory.readPadded_zero_size]

private theorem activeWordsAfter_lt (active offset size : Nat)
    (ha : active < 2 ^ 256) (hb : offset + size < 2 ^ 256) :
    MachineState.activeWordsAfter active offset size < 2 ^ 256 := by
  unfold MachineState.activeWordsAfter
  split
  · exact ha
  · dsimp only
    rw [Nat.max_lt]
    constructor
    · exact ha
    · have := Nat.div_le_self (offset + size - 1) 32
      omega

private theorem activeWordsAfter_toNat (active offset size : Nat)
    (ha : active < 2 ^ 256) (hb : offset + size < 2 ^ 256) :
    (UInt256.ofNat (MachineState.activeWordsAfter active offset size)).toNat =
      MachineState.activeWordsAfter active offset size := by
  rw [Challenge.EvmProof.Word.word_toNat_ofNat,
    Nat.mod_eq_of_lt (activeWordsAfter_lt active offset size ha hb)]

private theorem padFullSentinel_activeWords (input : ByteArray) (hfit : CalldataFits input) :
    (padFullSentinel input).activeWords = topByteActiveWords input := by
  have ha : (padLengthReady input).activeWords.toNat < 2 ^ 256 :=
    (padLengthReady input).activeWords.val.isLt
  have hp := Padding.paddedLength_lt input.size
  have hn : Padding.messageOffset + input.size < 2 ^ 256 := by
    unfold CalldataFits at hfit
    norm_num [Padding.messageOffset] at hfit ⊢
    omega
  have hn1 : Padding.messageOffset + input.size + 1 < 2 ^ 256 := by
    unfold CalldataFits at hfit
    norm_num [Padding.messageOffset] at hfit ⊢
    omega
  have hpad : Padding.messageOffset + Padding.paddedLength input.size < 2 ^ 256 := by
    unfold CalldataFits at hfit
    norm_num [Padding.messageOffset] at hfit ⊢
    omega
  have haddr := topByteAddr_toNat input hfit
  have hlen := Padding.input_and_footer_fit input.size
  have htop : (topByteAddr input).toNat =
      Padding.messageOffset + Padding.paddedLength input.size - 1 := by omega
  have hcopy := activeWordsAfter_lt _ _ _ ha hn
  unfold padFullSentinel padFullCopied topByteActiveWords padSentinel padCopied
  simp only [State.activeWordsAfterUInt256, activeWordsAfter_toNat _ _ _ ha hpad,
    activeWordsAfter_toNat _ _ _ ha hn,
    activeWordsAfter_toNat _ _ _ hcopy hn1, htop]
  exact congrArg UInt256.ofNat
    (ShortPaddingMemory.fullCopySentinel_activeWords _ input)

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
      else if a = (Padding.messageOffset + Padding.paddedLength input.size - 8) + 7 then
        0
      else (padSentinel input).memory[a]?.getD 0 := by
  induction i with
  | zero =>
      rw [lengthLoopMemory, topByteMemory,
        MachineState.writeBytes_getElem?_getD, topByteAddr_toNat input hfit]
      simp only [oneByte_size]
      by_cases h : a = (Padding.messageOffset + Padding.paddedLength input.size - 8) + 7
      · rw [if_pos (by omega), if_neg (by omega), if_pos h, h, Nat.sub_self]
        rfl
      · rw [if_neg (by omega), if_neg (by omega), if_neg h]
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
  have hsentinel : (padSentinel input).memory =
      Padding.sentinelMemory (padLengthReady input).memory input := by
    simp [padSentinel, padCopied, Padding.sentinelMemory,
      Padding.copiedMemory, Challenge.EvmProof.Memory.readPadded_zero_size]
  rw [padFinalMemory, Padding.paddedMemory,
    MachineState.writeBytes_getElem?_getD, hsentinel]
  simp only [Padding.lengthBytes_size]

theorem lengthLoopMemory_size (input : ByteArray) (hfit : CalldataFits input)
    (i : Nat) (hi : i ≤ 8) :
    (lengthLoopMemory input i).size = (Padding.messageOffset + Padding.paddedLength input.size - 8) + 8 := by
  have hs := sentinel_size_le input hfit
  induction i with
  | zero =>
      rw [lengthLoopMemory, topByteMemory, MachineState.writeBytes_size,
        topByteAddr_toNat input hfit]
      simp only [oneByte_size, if_neg (by decide : ¬ (1 = 0))]
      omega
  | succ i ih =>
      rw [lengthLoopMemory, MachineState.writeBytes_size,
        lengthAddr_toNat input hfit i (by omega), ih (by omega)]
      simp only [oneByte_size, if_neg (by decide : ¬ (1 = 0))]
      omega

theorem padFinalMemory_size (input : ByteArray) (hfit : CalldataFits input) :
    (padFinalMemory input).size = (Padding.messageOffset + Padding.paddedLength input.size - 8) + 8 := by
  have hs := sentinel_size_le input hfit
  have hsentinel : (padSentinel input).memory =
      Padding.sentinelMemory (padLengthReady input).memory input := by
    simp [padSentinel, padCopied, Padding.sentinelMemory,
      Padding.copiedMemory, Challenge.EvmProof.Memory.readPadded_zero_size]
  rw [padFinalMemory, Padding.paddedMemory, MachineState.writeBytes_size,
    ← hsentinel]
  simp only [Padding.lengthBytes_size, if_neg (by decide : ¬ (8 = 0))]
  omega

theorem lengthLoopMemory_final (input : ByteArray) (hfit : CalldataFits input)
    (i : Nat) (hi : i ≤ 8) (hz : lengthShift input i = ⟨0⟩) :
    lengthLoopMemory input i = padFinalMemory input := by
  have hs := sentinel_size_le input hfit
  apply ByteArray.ext_getElem
  · rw [lengthLoopMemory_size input hfit i hi, padFinalMemory_size input hfit]
  · intro a h₁ h₂
    rw [← Challenge.EvmProof.Memory.getD0_eq_getElem _ _ h₁,
      ← Challenge.EvmProof.Memory.getD0_eq_getElem _ _ h₂,
      lengthLoopMemory_getD input hfit i hi a, padFinalMemory_getD input hfit a]
    by_cases hin : (Padding.messageOffset + Padding.paddedLength input.size - 8) ≤ a ∧ a < (Padding.messageOffset + Padding.paddedLength input.size - 8) + i
    · rw [if_pos hin, if_pos ⟨hin.1, by omega⟩]
    · rw [if_neg hin]
      by_cases htop : a = (Padding.messageOffset + Padding.paddedLength input.size - 8) + 7
      · rw [if_pos htop, if_pos (by omega)]
        have h7 : a - (Padding.messageOffset + Padding.paddedLength input.size - 8) = 7 := by
          omega
        rw [h7, lengthBytes_of_shift_zero input hfit i 7 (by omega)
          (by norm_num) hz]
      · rw [if_neg htop]
        by_cases hwin : (Padding.messageOffset + Padding.paddedLength input.size - 8) ≤ a ∧ a < (Padding.messageOffset + Padding.paddedLength input.size - 8) + 8
        · rw [if_pos hwin]
          have hge : i ≤ a - (Padding.messageOffset + Padding.paddedLength input.size - 8) := by omega
          rw [lengthBytes_of_shift_zero input hfit i (a - (Padding.messageOffset + Padding.paddedLength input.size - 8)) hge
            (by omega) hz]
          exact (Challenge.EvmProof.Memory.getElem?_getD_eq_zero_of_size_le
            (padSentinel input).memory a (by omega)).symm ▸ rfl
        · rw [if_neg hwin]

private theorem lengthExitReturned_eq (input : ByteArray) (hfit : CalldataFits input)
    (i : Nat) (hi : i ≤ 8) (hz : lengthShift input i = ⟨0⟩) :
    lengthExitReturned input i = padReturned input := by
  unfold lengthExitReturned lengthExitSwapped lengthExitEntered padReturned
  unfold lengthLoopState
  simp only [lengthLoopMemory_final input hfit i hi hz, hz]
  rfl

def gasSteps_lengthExitEntered (input : ByteArray) (hfit : CalldataFits input)
    (i : Nat) (hi : i ≤ 8) (hz : lengthShift input i = ⟨0⟩) :
    Challenge.EvmProof.GasSteps (lengthExitEntered input i) (padReturned input) := by
  have g₁ := Challenge.EvmProof.Stepper.runLocatedBlock_sound
    Artifact.submissionArtifact .Osaka lengthExitPopPath (by rfl) (by rfl)
    (run_lengthExitPop input i) (by rfl) (by rfl)
  have g2raw := Challenge.EvmProof.Stepper.runLocatedBlock_sound
    Artifact.submissionArtifact .Osaka lengthExitJumpPath (by rfl) (by rfl)
    (run_lengthExitJump input i) (by rfl) (by rfl)
  have g₂ := Challenge.EvmProof.GasSteps.cast g2raw rfl
    (lengthExitReturned_eq input hfit i hi hz)
  exact g₁.trans g₂

def gasSteps_lengthIterationExit (input : ByteArray) (hfit : CalldataFits input)
    (i : Nat) (hi : i < 8) (hz : lengthShift input (i + 1) = ⟨0⟩) :
    Challenge.EvmProof.GasSteps (lengthLoopState input i) (padReturned input) := by
  have g₁ := Challenge.EvmProof.Stepper.runLocatedBlock_sound
    Artifact.submissionArtifact .Osaka lengthBodyPath (by rfl) (by rfl)
    (run_lengthBody input hfit i hi) (by rfl) (by rfl)
  have g2raw := Challenge.EvmProof.Stepper.runLocatedBlock_sound
    Artifact.submissionArtifact .Osaka lengthBranchPath (by rfl) (by rfl)
    (run_lengthBranchExit input i hz) (by rfl) (by rfl)
  have g₂ := Challenge.EvmProof.GasSteps.cast g2raw rfl
    (lengthExitPending_eq input i)
  exact g₁.trans (g₂.trans
    (gasSteps_lengthExitEntered input hfit (i + 1) (by omega) hz))

/-- Run the footer loop from a known nonzero residual with bounded shifts left. -/
noncomputable def gasSteps_lengthLoopFrom (input : ByteArray)
    (hfit : CalldataFits input) :
    (fuel i : Nat) → i + fuel = 8 → lengthShift input i ≠ ⟨0⟩ →
    Challenge.EvmProof.GasSteps (lengthLoopState input i) (padReturned input)
  | 0, i, hsum, hne => by
      have hi : i = 8 := by omega
      subst hi
      exact False.elim (hne (lengthShift_eight input hfit))
  | fuel + 1, i, hsum, _hne =>
      if hz : lengthShift input (i + 1) = ⟨0⟩ then
        gasSteps_lengthIterationExit input hfit i (by omega) hz
      else
        (gasSteps_lengthIteration input hfit i (by omega) hz).trans
          (gasSteps_lengthLoopFrom input hfit fuel (i + 1) (by omega) hz)

noncomputable def gasSteps_lengthLoop (input : ByteArray) (hfit : CalldataFits input) :
    Challenge.EvmProof.GasSteps (lengthLoopState input 0) (padReturned input) :=
  if hz : lengthShift input 1 = ⟨0⟩ then
    gasSteps_lengthIterationExit input hfit 0 (by norm_num) hz
  else
    (gasSteps_lengthIteration input hfit 0 (by norm_num) hz).trans
      (gasSteps_lengthLoopFrom input hfit 7 1 (by norm_num) hz)


private theorem writeBytes_same_twice (memory bytes : ByteArray) (offset : Nat) :
    MachineState.writeBytes (MachineState.writeBytes memory bytes offset) bytes offset =
      MachineState.writeBytes memory bytes offset := by
  apply ByteArray.ext_getElem
  · simp only [MachineState.writeBytes_size]
    split <;> simp_all
  · intro i hi hj
    rw [← Challenge.EvmProof.Memory.getD0_eq_getElem _ _ hi,
      ← Challenge.EvmProof.Memory.getD0_eq_getElem _ _ hj]
    simp only [MachineState.writeBytes_getElem?_getD]
    split <;> simp_all

private theorem topByteMemory_store_same (input : ByteArray) :
    MachineState.writeBytes (topByteMemory input) (ByteArray.mk #[0])
      (topByteAddr input).toNat = topByteMemory input := by
  exact writeBytes_same_twice _ _ _

private theorem topByteActiveWords_store_same (input : ByteArray)
    (hfit : CalldataFits input) :
    UInt256.ofNat (MachineState.activeWordsAfter (topByteActiveWords input).toNat
      (topByteAddr input).toNat 1) = topByteActiveWords input := by
  have h := lengthLoopActiveWords_stable input hfit 7 (by decide)
  simpa only [topByteAddr_toNat input hfit, lengthAddr_toNat input hfit 7 (by decide)]
    using h

def padGeneralEntry (input : ByteArray) : State :=
  { padFullSentinel input with pc := UInt256.ofNat 0x14bc }

def padShortEntry (input : ByteArray) : State :=
  { padFullSentinel input with pc := UInt256.ofNat 0x19b }


private theorem short_low_eq (input : ByteArray) (hfit : CalldataFits input)
    (hshort : input.size < 8192) :
    (UInt256.ofNat input.size).shiftLeft 3 = lengthShift input 0 := by
  have hn : input.size < 2 ^ 256 := Nat.lt_trans hfit (by norm_num)
  have hbit : input.size * 8 < 2 ^ 64 := by omega
  have hbit256 : input.size * 8 < 2 ^ 256 := by omega
  apply Challenge.EvmProof.Word.word_ext
  change ((UInt256.ofNat input.size).shiftLeft (UInt256.ofNat 3)).toNat = _
  rw [shiftLeft_ofNat_wrap hn (by norm_num : 3 < 256),
    Challenge.EvmProof.Word.word_toNat_ofNat, lengthShift_toNat input hfit 0]
  norm_num
  norm_num at hbit hbit256
  omega

private theorem short_second_eq (input : ByteArray) (hfit : CalldataFits input)
    (hshort : input.size < 8192) :
    (UInt256.ofNat input.size).shiftRight 5 = lengthShift input 1 := by
  have hn : input.size < 2 ^ 256 := Nat.lt_trans hfit (by norm_num)
  have hbit : input.size * 8 < 2 ^ 64 := by omega
  apply Challenge.EvmProof.Word.word_ext
  change ((UInt256.ofNat input.size).shiftRight (UInt256.ofNat 5)).toNat = _
  rw [Challenge.EvmProof.Word.shiftRight_toNat _ (by norm_num : 5 < 256),
    Challenge.EvmProof.Word.word_toNat_ofNat, Nat.mod_eq_of_lt hn,
    lengthShift_toNat input hfit 1, Nat.mod_eq_of_lt hbit,
    Nat.shiftRight_eq_div_pow]
  norm_num
  omega

private theorem short_shift_two (input : ByteArray) (hfit : CalldataFits input)
    (hshort : input.size < 8192) : lengthShift input 2 = ⟨0⟩ := by
  apply Challenge.EvmProof.Word.word_ext
  rw [lengthShift_toNat input hfit 2]
  change input.size * 8 % 2 ^ 64 / 2 ^ (8 * 2) = 0
  have hm := Nat.mod_le (input.size * 8) (2 ^ 64)
  norm_num at *
  omega

private theorem short_address (input : ByteArray) :
    ShortFooter.address (Padding.paddedWord input) = lengthAddr input 0 := by
  change UInt256.ofNat 280 + Padding.paddedWord input =
    Padding.paddedWord input + UInt256.ofNat 280
  exact Challenge.EvmProof.Word.word_add_comm _ _

def padShortReady (input : ByteArray) : State :=
  { padReturned input with
    pc := UInt256.ofNat 0x1b2
    stack := [UInt256.ofNat 0x1c4, UInt256.ofNat 0, Padding.paddedWord input] }

private theorem short_expected_eq (input : ByteArray) (hfit : CalldataFits input)
    (hshort : input.size < 8192) :
    ShortFooter.expected (padFullSentinel input) (UInt256.ofNat input.size)
      (Padding.paddedWord input) (UInt256.ofNat 0x1c4) [] = padShortReady input := by
  have hm : ShortFooter.writeByte
      (ShortFooter.writeByte (padFullSentinel input).memory
        (ShortFooter.address (Padding.paddedWord input))
        ((UInt256.ofNat input.size).shiftLeft 3))
      (UInt256.add 1 (ShortFooter.address (Padding.paddedWord input)))
      ((UInt256.ofNat input.size).shiftRight 5) = padFinalMemory input := by
    rw [short_address, short_low_eq input hfit hshort, short_second_eq input hfit hshort,
      padFullSentinel_memory input hfit]
    change lengthLoopMemory input 2 = padFinalMemory input
    exact lengthLoopMemory_final input hfit 2 (by decide)
      (short_shift_two input hfit hshort)
  have ha : UInt256.ofNat (MachineState.activeWordsAfter
      ((padFullSentinel input).activeWordsAfterUInt256
        (ShortFooter.address (Padding.paddedWord input)).toNat 1).toNat
      (UInt256.add 1 (ShortFooter.address (Padding.paddedWord input))).toNat 1)
      = topByteActiveWords input := by
    rw [short_address]
    simp only [State.activeWordsAfterUInt256, padFullSentinel_activeWords input hfit]
    rw [lengthLoopActiveWords_stable input hfit 0 (by decide)]
    exact lengthLoopActiveWords_stable input hfit 1 (by decide)
  unfold ShortFooter.expected
  simp only [hm, ha, List.append_nil]
  unfold padShortReady padReturned lengthLoopState padFullSentinel padFullCopied padSentinel padCopied
  rfl

private theorem run_shortGuard (input : ByteArray) (hfit : CalldataFits input)
    (hshort : input.size < 8192) :
    Challenge.EvmProof.Stepper.runLocatedBlock shortGuardPath (padFullSentinel input) =
      some (padShortEntry input) := by
  have hn : (UInt256.ofNat input.size).toNat < 8192 := by
    rw [Challenge.EvmProof.Word.word_toNat_ofNat,
      Nat.mod_eq_of_lt (Nat.lt_trans hfit (by norm_num))]
    exact hshort
  have hcond : (UInt256.ofNat input.size).shiftRight (UInt256.ofNat 13) =
      UInt256.ofNat 0 := ShortFooter.short_condition _ hn
  simp [shortGuardPath, Challenge.EvmProof.Stepper.runLocatedBlock,
    Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
    padShortEntry, padFullSentinel, padFullCopied, padLengthReady,
    hcond, UInt256.isTrue]

private theorem run_generalGuard (input : ByteArray) (hfit : CalldataFits input)
    (hlarge : ¬ input.size < 8192) :
    Challenge.EvmProof.Stepper.runLocatedBlock shortGuardPath (padFullSentinel input) =
      some (padGeneralEntry input) := by
  have hn : (UInt256.ofNat input.size).toNat = input.size := by
    rw [Challenge.EvmProof.Word.word_toNat_ofNat,
      Nat.mod_eq_of_lt (Nat.lt_trans hfit (by norm_num))]
  have htrue : UInt256.isTrue ((UInt256.ofNat input.size).shiftRight (UInt256.ofNat 13)) := by
    unfold UInt256.isTrue
    rw [Challenge.EvmProof.Word.shiftRight_toNat _ (by norm_num : 13 < 256), hn,
      Nat.shiftRight_eq_div_pow]
    norm_num
    omega
  simp [shortGuardPath, Challenge.EvmProof.Stepper.runLocatedBlock,
    Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
    padGeneralEntry, padFullSentinel, padFullCopied, padLengthReady, htrue,
    Artifact.validJumpDest_14bc]

private theorem run_shortBody (input : ByteArray) :
    Challenge.EvmProof.Stepper.runLocatedBlock shortBodyPath (padShortEntry input) =
      some (ShortFooter.expected (padFullSentinel input) (UInt256.ofNat input.size)
        (Padding.paddedWord input) (UInt256.ofNat 0x1c4) []) := by
  simp [shortBodyPath, Challenge.EvmProof.Stepper.runLocatedBlock,
    Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
    padShortEntry, ShortFooter.expected, ShortFooter.address, ShortFooter.writeByte,
    padFullSentinel, padFullCopied, padLengthReady, List.exchange,
    State.activeWordsAfterUInt256]
  exact ⟨⟨rfl, rfl⟩, ⟨rfl, rfl⟩⟩

private theorem run_shortReturn (input : ByteArray) :
    Challenge.EvmProof.Stepper.runLocatedBlock shortReturnPath (padShortReady input) =
      some (padReturned input) := by
  simp [shortReturnPath, Challenge.EvmProof.Stepper.runLocatedBlock,
    Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
    padShortReady]
  rfl

private def padGeneralReady (input : ByteArray) : State :=
  { padGeneralEntry input with
    pc := UInt256.ofNat (Artifact.instructionPC 4069)
    stack := [lengthAddr input 0, lengthShift input 0,
      Padding.paddedWord input, UInt256.ofNat 0x1c4]
    memory := MachineState.writeBytes (padFullSentinel input).memory
      (ByteArray.mk #[0]) (topByteAddr input).toNat
    activeWords := (padFullSentinel input).activeWordsAfterUInt256
      (topByteAddr input).toNat 1 }

set_option maxHeartbeats 400000 in
private theorem padGeneralReady_eq (input : ByteArray) (hfit : CalldataFits input) :
    padGeneralReady input = lengthLoopState input 0 := by
  have hm : MachineState.writeBytes (padFullSentinel input).memory
      (ByteArray.mk #[0]) (topByteAddr input).toNat = topByteMemory input := by
    rw [padFullSentinel_memory input hfit]
    exact topByteMemory_store_same input
  have ha : (padFullSentinel input).activeWordsAfterUInt256
      (topByteAddr input).toNat 1 = topByteActiveWords input := by
    simp only [State.activeWordsAfterUInt256, padFullSentinel_activeWords input hfit]
    exact topByteActiveWords_store_same input hfit
  unfold padGeneralReady padGeneralEntry
  rw [hm, ha]
  unfold lengthLoopState lengthLoopMemory padFullSentinel padFullCopied padSentinel padCopied
  rfl

set_option maxHeartbeats 400000 in
private theorem run_lengthFooterSetup_raw (input : ByteArray) :
    Challenge.EvmProof.Stepper.runLocatedBlock lengthFooterSetupPath
      (padGeneralEntry input) = some (padGeneralReady input) := by
  simp [lengthFooterSetupPath,
    Challenge.EvmProof.Stepper.runLocatedBlock,
    Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
    padGeneralReady, padGeneralEntry, lengthAddr, lengthShift,
    topByteAddr, lengthOffsetWord, bitLengthWord, State.activeWordsAfterUInt256,
    padFullSentinel, padFullCopied, padLengthReady]

private theorem run_lengthFooterSetup (input : ByteArray) (hfit : CalldataFits input) :
    Challenge.EvmProof.Stepper.runLocatedBlock lengthFooterSetupPath
      (padGeneralEntry input) = some (lengthLoopState input 0) := by
  rw [← padGeneralReady_eq input hfit]
  exact run_lengthFooterSetup_raw input

def gasSteps_fullCopy (input : ByteArray) (hfit : CalldataFits input) :
    Challenge.EvmProof.GasSteps (padLengthReady input)
      (padFullSentinel input) := by
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
  exact g₁.trans (g₂ₐ.trans g2b)

def gasSteps_shortFooter (input : ByteArray) (hfit : CalldataFits input)
    (hshort : input.size < 8192) :
    Challenge.EvmProof.GasSteps (padFullSentinel input) (padReturned input) := by
  have g₁ := Challenge.EvmProof.Stepper.runLocatedBlock_sound
    Artifact.submissionArtifact .Osaka shortGuardPath (by rfl) (by rfl)
    (run_shortGuard input hfit hshort) (by rfl) deployAddress_not_precompile
  have g₂ := Challenge.EvmProof.Stepper.runLocatedBlock_sound
    Artifact.submissionArtifact .Osaka shortBodyPath (by rfl) (by rfl)
    (run_shortBody input) (by rfl) deployAddress_not_precompile
  have g₃ := Challenge.EvmProof.Stepper.runLocatedBlock_sound
    Artifact.submissionArtifact .Osaka shortReturnPath (by rfl) (by rfl)
    (run_shortReturn input) (by rfl) deployAddress_not_precompile
  exact g₁.trans ((Challenge.EvmProof.GasSteps.cast g₂ rfl
    (short_expected_eq input hfit hshort)).trans g₃)

def gasSteps_lengthSetup (input : ByteArray) (hfit : CalldataFits input)
    (hlarge : ¬ input.size < 8192) :
    Challenge.EvmProof.GasSteps (padFullSentinel input)
      (lengthLoopState input 0) := by
  have g₁ := Challenge.EvmProof.Stepper.runLocatedBlock_sound
    Artifact.submissionArtifact .Osaka shortGuardPath (by rfl) (by rfl)
    (run_generalGuard input hfit hlarge) (by rfl) deployAddress_not_precompile
  have g₂ := Challenge.EvmProof.Stepper.runLocatedBlock_sound
    Artifact.submissionArtifact .Osaka lengthFooterSetupPath (by rfl) (by rfl)
    (run_lengthFooterSetup input hfit) (by rfl) deployAddress_not_precompile
  exact g₁.trans g₂

/-- Complete certified execution from the challenge initial state through the
RIPEMD-160 padding function. -/
private def gasSteps_padPrefix (input : ByteArray)
    (entryPrefix : Challenge.EvmProof.GasSteps (initialState submissionBytecode input 0)
      (Execution.atPC input 0x154)) :
    Challenge.EvmProof.GasSteps (initialState submissionBytecode input 0)
      (padLengthReady input) :=
  (Main.gasSteps_initialize input entryPrefix).trans
    ((gasSteps_enterPad input).trans (gasSteps_paddedLength input))

noncomputable def gasSteps_padBody (input : ByteArray) (hfit : CalldataFits input) :
    Challenge.EvmProof.GasSteps (padLengthReady input) (padReturned input) :=
  (gasSteps_fullCopy input hfit).trans <|
    if hshort : input.size < 8192 then
      gasSteps_shortFooter input hfit hshort
    else
      (gasSteps_lengthSetup input hfit hshort).trans (gasSteps_lengthLoop input hfit)

noncomputable def gasSteps_pad (input : ByteArray) (hfit : CalldataFits input)
    (entryPrefix : Challenge.EvmProof.GasSteps (initialState submissionBytecode input 0)
      (Execution.atPC input 0x154)) :
    Challenge.EvmProof.GasSteps (initialState submissionBytecode input 0)
      (padReturned input) :=
  (gasSteps_padPrefix input entryPrefix).trans (gasSteps_padBody input hfit)

theorem padReturned_memory (input : ByteArray) (_hfit : CalldataFits input) :
    (padReturned input).memory =
      Padding.paddedMemory (padLengthReady input).memory input := by
  rfl

#print axioms gasSteps_pad

end Challenge.Ripemd160.Submission.Proofs.Bytecode.PaddingTrace
