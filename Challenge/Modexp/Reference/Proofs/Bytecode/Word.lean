import Challenge.Modexp.Reference.Proofs.Algorithm
import Challenge.Modexp.Reference.Proofs.Bytecode.Accessors
import Challenge.Modexp.Reference.Proofs.Bytecode.Dispatch
import Challenge.EvmProof.Bytes
set_option warningAsError true
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000
/-!
# One-word MODEXP path

This module certifies the entry of the `MULMOD` fast path and names its loop
invariants.  Operand widths and offsets are expressed with the same padded
byte decoder as the challenge specification.
-/

namespace Challenge.Modexp.Reference.Proofs.Bytecode.Word

open EvmSemantics
open EvmSemantics.EVM

private def wfOp {op : Operation}
    (hopcode : Decode.opcodeOf (YulEvmCompiler.Instr.opByte op) = some op)
    (hplain : YulEvmCompiler.plainOp op)
    (havailable : op.availableInFork .Osaka = true) :
    Challenge.EvmProof.Stepper.WellFormed .Osaka (.op op) :=
  ⟨hopcode, hplain, havailable⟩

def startPath :
    List (Challenge.EvmProof.Stepper.Located Artifact.referenceArtifact .Osaka) :=
  [⟨415, .op .JUMPDEST, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨416, .op (.Dup ⟨5, by decide⟩), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨417, .op .CALLDATALOAD, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨418, .op (.Dup ⟨3, by decide⟩), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨419, .push ⟨1, by decide⟩ 32, by rfl, by decide⟩,
   ⟨420, .op .SUB, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨421, .push ⟨1, by decide⟩ 3, by rfl, by decide⟩,
   ⟨422, .op .SHL, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨423, .op .SHR, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨424, .op (.Dup ⟨0, by decide⟩), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨425, .push ⟨2, by decide⟩ 538, by rfl, by decide⟩,
   ⟨426, .op .JUMPI, by rfl, wfOp (by decide) trivial rfl⟩]

def zeroTailPath :
    List (Challenge.EvmProof.Stepper.Located Artifact.referenceArtifact .Osaka) :=
  [⟨427, .op (.Dup ⟨3, by decide⟩), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨428, .push ⟨2, by decide⟩ 6144, by rfl, by decide⟩,
   ⟨429, .op .RETURN, by rfl, wfOp (by decide) trivial rfl⟩]

def zeroModulusPath :
    List (Challenge.EvmProof.Stepper.Located Artifact.referenceArtifact .Osaka) :=
  startPath ++ zeroTailPath

def expOffset (input : ByteArray) : Nat := 96 + baseSize input
def modulusOffset (input : ByteArray) : Nat := expOffset input + exponentSize input

def modulusValue (input : ByteArray) : Nat :=
  Precompile.bytesToNatPadded input (modulusOffset input) (modulusSize input)

def callerRest (input : ByteArray) : List UInt256 :=
  [UInt256.ofNat (modulusOffset input), UInt256.ofNat (expOffset input),
    UInt256.ofNat (modulusSize input), UInt256.ofNat (exponentSize input),
    UInt256.ofNat (baseSize input)]

def nonzeroState (input : ByteArray) : State :=
  { Dispatch.wordEntryState input with
    pc := UInt256.ofNat 538
    stack := [UInt256.ofNat (modulusValue input),
      UInt256.ofNat (baseSize input), UInt256.ofNat (exponentSize input),
      UInt256.ofNat (modulusSize input), UInt256.ofNat 96,
      UInt256.ofNat (expOffset input), UInt256.ofNat (modulusOffset input),
      UInt256.ofNat 1267] ++ callerRest input }

def zeroModulusFinalState (input : ByteArray) : State :=
  { Dispatch.wordEntryState input with
    pc := UInt256.ofNat 537
    stack := [UInt256.ofNat 0, UInt256.ofNat (baseSize input),
      UInt256.ofNat (exponentSize input), UInt256.ofNat (modulusSize input),
      UInt256.ofNat 96, UInt256.ofNat (expOffset input),
      UInt256.ofNat (modulusOffset input), UInt256.ofNat 1267] ++ callerRest input
    halt := .Returned
    hReturn := MachineState.readPadded ByteArray.empty 6144 (modulusSize input)
    activeWords := (Dispatch.wordEntryState input).activeWordsAfterUInt256
      6144 (modulusSize input) }

@[simp] private theorem startPCs (i : Nat) (hi : 415 ≤ i) (hii : i ≤ 426) :
    Artifact.referenceArtifact.instructionPC i =
      [517, 518, 519, 520, 521, 523, 524, 526, 527, 528, 529, 532][i - 415]! := by
  interval_cases i <;> decide

@[simp] private theorem jump538 :
    Decode.isValidJumpDest referenceBytecode 538 = true :=
  Artifact.isValidJumpDest_index 430 (by rfl)

set_option linter.unusedSimpArgs false in
theorem run_start (input : ByteArray) (hvalid : ValidInput input)
    (hmsize : 0 < modulusSize input) (hword : modulusSize input ≤ 32)
    (hmodulus : 0 < modulusValue input) :
    Challenge.EvmProof.Stepper.runLocatedBlock startPath
      (Dispatch.wordEntryState input) = some (nonzeroState input) := by
  rcases hvalid with ⟨_, hb, he, hm⟩
  have hsub := Challenge.EvmProof.Word.ofNat_sub_ofNat hword
    (by norm_num : 32 < 2 ^ 256)
  have hshift :
      UInt256.shiftLeft (UInt256.ofNat (32 - modulusSize input))
          (UInt256.ofNat 3) =
        UInt256.ofNat ((32 - modulusSize input) * 8) := by
    rw [Challenge.EvmProof.Word.shiftLeft_ofNat]
    · congr 1
      simp [Nat.shiftLeft_eq]
    · omega
    · omega
  have hslice := Challenge.EvmProof.Bytes.shiftRight_readWord input
    (modulusOffset input) (modulusSize input) hmsize hword
  have hmodlt : modulusValue input < 2 ^ 256 :=
    (Challenge.EvmProof.Bytes.bytesToNatPadded_lt_pow input
      (modulusOffset input) (modulusSize input)).trans_le (by
        have : 256 ^ modulusSize input ≤ 256 ^ 32 :=
          Nat.pow_le_pow_right₀ (by omega) hword
        exact this.trans (by norm_num))
  simp (config := { maxSteps := 300000 })
    [startPath, Challenge.EvmProof.Stepper.runLocatedBlock,
      Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
      Dispatch.wordEntryState, Main.headerState, nonzeroState, callerRest,
      expOffset, modulusOffset, modulusValue, startPCs, hsub, hshift, hslice,
      hmodulus, hmodlt, UInt256.isTrue,
      Challenge.EvmProof.Word.word_toNat_ofNat, Nat.mod_eq_of_lt]

set_option linter.unusedSimpArgs false in
theorem run_zeroModulus (input : ByteArray) (hvalid : ValidInput input)
    (hmsize : 0 < modulusSize input) (hword : modulusSize input ≤ 32)
    (hmodulus : modulusValue input = 0) :
    Challenge.EvmProof.Stepper.runLocatedBlock zeroModulusPath
      (Dispatch.wordEntryState input) = some (zeroModulusFinalState input) := by
  rcases hvalid with ⟨_, hb, he, hm⟩
  have hsub := Challenge.EvmProof.Word.ofNat_sub_ofNat hword
    (by norm_num : 32 < 2 ^ 256)
  have hshift :
      UInt256.shiftLeft (UInt256.ofNat (32 - modulusSize input))
          (UInt256.ofNat 3) =
        UInt256.ofNat ((32 - modulusSize input) * 8) := by
    rw [Challenge.EvmProof.Word.shiftLeft_ofNat]
    · congr 1
      simp [Nat.shiftLeft_eq]
    · omega
    · omega
  have hslice := Challenge.EvmProof.Bytes.shiftRight_readWord input
    (modulusOffset input) (modulusSize input) hmsize hword
  simp (config := { maxSteps := 400000 })
    [zeroModulusPath, startPath, zeroTailPath,
      Challenge.EvmProof.Stepper.runLocatedBlock,
      Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
      Dispatch.wordEntryState, Main.headerState, zeroModulusFinalState,
      callerRest, expOffset, modulusOffset, modulusValue, startPCs, hsub, hshift,
      hslice, hmodulus, UInt256.isTrue,
      Challenge.EvmProof.Word.word_toNat_ofNat]

def gasSteps_start (input : ByteArray) (hvalid : ValidInput input)
    (hmsize : 0 < modulusSize input) (hword : modulusSize input ≤ 32)
    (hmodulus : 0 < modulusValue input) :
    Challenge.EvmProof.GasSteps (Dispatch.wordEntryState input)
      (nonzeroState input) := by
  apply Challenge.EvmProof.Stepper.runLocatedBlock_sound
    Artifact.referenceArtifact .Osaka startPath
  · rfl
  · rfl
  · exact run_start input hvalid hmsize hword hmodulus
  · rfl
  · exact deployAddress_not_precompile

def gasSteps_zeroModulus (input : ByteArray) (hvalid : ValidInput input)
    (hmsize : 0 < modulusSize input) (hword : modulusSize input ≤ 32)
    (hmodulus : modulusValue input = 0) :
    Challenge.EvmProof.GasSteps (Dispatch.wordEntryState input)
      (zeroModulusFinalState input) := by
  apply Challenge.EvmProof.Stepper.runLocatedBlock_sound
    Artifact.referenceArtifact .Osaka zeroModulusPath
  · rfl
  · rfl
  · exact run_zeroModulus input hvalid hmsize hword hmodulus
  · rfl
  · exact deployAddress_not_precompile

def gasSteps_zeroModulus_total (input : ByteArray) (hvalid : ValidInput input)
    (hmsize : 0 < modulusSize input) (hword : modulusSize input ≤ 32)
    (hmodulus : modulusValue input = 0) :
    Challenge.EvmProof.GasSteps (initialState referenceBytecode input 0)
      (zeroModulusFinalState input) :=
  ((Main.gasSteps_header input hvalid).trans
    (Dispatch.gasSteps_wordEntry input hvalid hmsize hword)).trans
      (gasSteps_zeroModulus input hvalid hmsize hword hmodulus)

@[simp] theorem zeroModulusFinalState_isDone (input : ByteArray) :
    (zeroModulusFinalState input).isDone = true := by
  rfl

theorem zeroModulusFinalState_result (input : ByteArray)
    (hmsize : 0 < modulusSize input) (hmodulus : modulusValue input = 0) :
    (zeroModulusFinalState input).toResult = .returned (spec input) := by
  rw [show (zeroModulusFinalState input).toResult =
      .returned (Precompile.natToBytes 0 (modulusSize input)) by
    simp [zeroModulusFinalState, Algorithm.zeroBytes]]
  simp [spec, Nat.ne_of_gt hmsize, modulusValue, modulusOffset, expOffset,
    hmodulus, Precompile.modPow]

end Challenge.Modexp.Reference.Proofs.Bytecode.Word
