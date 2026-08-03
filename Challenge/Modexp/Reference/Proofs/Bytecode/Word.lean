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

private def opAt (index : Nat) (op : Operation)
    (hget : Artifact.referenceInstructions[index]? = some (.op op) := by rfl)
    (hwf : Challenge.EvmProof.Stepper.WellFormed .Osaka (.op op) := by decide) :
    Challenge.EvmProof.Stepper.Located Artifact.referenceArtifact .Osaka :=
  ⟨index, .op op, hget, hwf⟩

private def pushAt (index : Nat) (width : Fin 33) (value : UInt256)
    (hget : Artifact.referenceInstructions[index]? = some (.push width value) := by rfl)
    (hwf : Challenge.EvmProof.Stepper.WellFormed .Osaka (.push width value) := by decide) :
    Challenge.EvmProof.Stepper.Located Artifact.referenceArtifact .Osaka :=
  ⟨index, .push width value, hget, hwf⟩

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

def baseSetupPath :
    List (Challenge.EvmProof.Stepper.Located Artifact.referenceArtifact .Osaka) :=
  [opAt 430 .JUMPDEST, pushAt 431 0 0, pushAt 432 0 0]

def baseIterationPath :
    List (Challenge.EvmProof.Stepper.Located Artifact.referenceArtifact .Osaka) :=
  [opAt 433 .JUMPDEST, opAt 434 (.Dup ⟨3, by decide⟩),
   opAt 435 (.Dup ⟨1, by decide⟩), opAt 436 .LT, opAt 437 .ISZERO,
   pushAt 438 2 582, opAt 439 .JUMPI,
   opAt 440 (.Dup ⟨2, by decide⟩), pushAt 441 2 562, pushAt 442 0 0,
   opAt 443 (.Dup ⟨3, by decide⟩), opAt 444 (.Dup ⟨10, by decide⟩),
   opAt 445 .ADD, pushAt 446 2 4, opAt 447 .JUMP] ++
  Accessors.calldataBytePath ++
  [opAt 448 .JUMPDEST, opAt 449 (.Dup ⟨4, by decide⟩), pushAt 450 2 256,
   opAt 451 (.Dup ⟨5, by decide⟩), opAt 452 .MULMOD, opAt 453 .ADDMOD,
   opAt 454 (.Swap ⟨1, by decide⟩), opAt 455 .POP, pushAt 456 1 1,
   opAt 457 (.Dup ⟨1, by decide⟩), opAt 458 .ADD,
   opAt 459 (.Swap ⟨0, by decide⟩), opAt 460 .POP,
   pushAt 461 2 541, opAt 462 .JUMP]

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

def byteWord (input : ByteArray) (offset : Nat) : UInt256 :=
  Accessors.calldataByteValue (Dispatch.wordEntryState input) (UInt256.ofNat offset)

def baseStep (input : ByteArray) (i : Nat) (base : UInt256) : UInt256 :=
  UInt256.addMod
    (UInt256.mulMod base (UInt256.ofNat 256) (UInt256.ofNat (modulusValue input)))
    (byteWord input (96 + i)) (UInt256.ofNat (modulusValue input))

def baseAfter (input : ByteArray) : Nat → UInt256
  | 0 => 0
  | i + 1 => baseStep input i (baseAfter input i)

def baseLoopState (input : ByteArray) (i : Nat) (base : UInt256) : State :=
  { nonzeroState input with
    pc := UInt256.ofNat 541
    stack := [UInt256.ofNat i, base, UInt256.ofNat (modulusValue input),
      UInt256.ofNat (baseSize input), UInt256.ofNat (exponentSize input),
      UInt256.ofNat (modulusSize input), UInt256.ofNat 96,
      UInt256.ofNat (expOffset input), UInt256.ofNat (modulusOffset input),
      UInt256.ofNat 1267] ++ callerRest input }

theorem byteWord_eq (input : ByteArray) (offset : Nat)
    (hoffset : offset < 2 ^ 256) :
    byteWord input offset = UInt256.ofNat
      (YulSemantics.EVM.byteFrom input.toList offset).toNat := by
  unfold byteWord Accessors.calldataByteValue
  rw [Challenge.EvmProof.Word.word_toNat_ofNat,
    Nat.mod_eq_of_lt hoffset]
  change UInt256.byteAt ⟨0⟩ (MachineState.readWord input offset) = _
  exact Challenge.EvmProof.Bytes.byteAt_zero_readWord input offset

theorem baseStep_spec (input : ByteArray) (i prefix modulus : Nat)
    (hmodulus : modulusValue input = modulus) (hmodpos : 0 < modulus)
    (hmodlt : modulus < 2 ^ 256) (hoffset : 96 + i < 2 ^ 256) :
    baseStep input i (UInt256.ofNat (prefix % modulus)) =
      UInt256.ofNat
        (Precompile.bytesToNatPadded input 96 (i + 1) % modulus) := by
  have hbase : prefix % modulus < modulus := Nat.mod_lt _ hmodpos
  have hbase256 : prefix % modulus < 2 ^ 256 := hbase.trans hmodlt
  have hbyte := byteWord_eq input (96 + i) hoffset
  have hmword : (UInt256.ofNat modulus).val.val ≠ 0 := by
    change (UInt256.ofNat modulus).toNat ≠ 0
    rw [Challenge.EvmProof.Word.word_toNat_ofNat, Nat.mod_eq_of_lt hmodlt]
    omega
  have hmul : (prefix % modulus * 256) % modulus < modulus :=
    Nat.mod_lt _ hmodpos
  have hmul256 : (prefix % modulus * 256) % modulus < 2 ^ 256 :=
    hmul.trans hmodlt
  have hbyte256 :
      (YulSemantics.EVM.byteFrom input.toList (96 + i)).toNat < 2 ^ 256 :=
    (YulSemantics.EVM.byteFrom input.toList (96 + i)).toNat_lt.trans (by norm_num)
  unfold baseStep
  rw [hmodulus, hbyte]
  unfold UInt256.mulMod UInt256.addMod
  rw [if_neg hmword, if_neg hmword]
  rw [Challenge.EvmProof.Word.word_toNat_ofNat,
    Nat.mod_eq_of_lt hbase256,
    Challenge.EvmProof.Word.word_toNat_ofNat,
    Nat.mod_eq_of_lt (by norm_num : 256 < 2 ^ 256),
    Challenge.EvmProof.Word.word_toNat_ofNat,
    Nat.mod_eq_of_lt hmodlt,
    Challenge.EvmProof.Word.word_toNat_ofNat,
    Nat.mod_eq_of_lt hmul256,
    Challenge.EvmProof.Word.word_toNat_ofNat,
    Nat.mod_eq_of_lt hbyte256,
    Challenge.EvmProof.Word.word_toNat_ofNat,
    Nat.mod_eq_of_lt hmodlt]
  congr 1
  rw [Challenge.EvmProof.Bytes.bytesToNatPadded_succ]
  let p := Precompile.bytesToNatPadded input 96 i
  let b := (YulSemantics.EVM.byteFrom input.toList (96 + i)).toNat
  change (((prefix % modulus * 256) % modulus + b) % modulus) =
    (p * 256 + b) % modulus
  rw [Nat.mod_add_mod]
  rw [← Nat.mod_add_mod (p * 256) modulus b]
  congr 2
  rw [Nat.mod_mul_mod]
  rfl

theorem baseAfter_correct (input : ByteArray) (count : Nat)
    (hmodpos : 0 < modulusValue input)
    (hmodlt : modulusValue input < 2 ^ 256)
    (hbaseSize : baseSize input ≤ 1024)
    (hcount : count ≤ baseSize input) :
    baseAfter input count = UInt256.ofNat
      (Precompile.bytesToNatPadded input 96 count % modulusValue input) := by
  induction count with
  | zero =>
      simp [baseAfter, Challenge.EvmProof.Bytes.bytesToNatPadded_zero_width]
  | succ count ih =>
      rw [baseAfter, ih (by omega)]
      exact baseStep_spec input count
        (Precompile.bytesToNatPadded input 96 count) (modulusValue input)
        rfl hmodpos hmodlt (by omega)

@[simp] private theorem startPCs (i : Nat) (hi : 415 ≤ i) (hii : i ≤ 426) :
    Artifact.referenceArtifact.instructionPC i =
      [517, 518, 519, 520, 521, 523, 524, 526, 527, 528, 529, 532][i - 415]! := by
  interval_cases i <;> decide

@[simp] private theorem jump538 :
    Decode.isValidJumpDest referenceBytecode 538 = true :=
  Artifact.isValidJumpDest_index 430 (by rfl)

@[simp] private theorem wordPCs (i : Nat) (hi : 430 ≤ i) (hii : i ≤ 462) :
    Artifact.referenceArtifact.instructionPC i =
      [538, 539, 540, 541, 542, 543, 544, 545, 546, 549, 550,
       551, 554, 555, 556, 557, 558, 561, 562, 563, 564, 567,
       568, 569, 570, 571, 572, 574, 575, 576, 577, 578, 581][i - 430]! := by
  interval_cases i <;> decide

@[simp] private theorem jump582 :
    Decode.isValidJumpDest referenceBytecode 582 = true :=
  Artifact.isValidJumpDest_index 463 (by rfl)

@[simp] private theorem jump562 :
    Decode.isValidJumpDest referenceBytecode 562 = true :=
  Artifact.isValidJumpDest_index 448 (by rfl)

@[simp] private theorem jump4 :
    Decode.isValidJumpDest referenceBytecode 4 = true :=
  Artifact.isValidJumpDest_index 2 (by rfl)

@[simp] private theorem jump541 :
    Decode.isValidJumpDest referenceBytecode 541 = true :=
  Artifact.isValidJumpDest_index 433 (by rfl)

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

set_option linter.unusedSimpArgs false in
theorem run_baseSetup (input : ByteArray) :
    Challenge.EvmProof.Stepper.runLocatedBlock baseSetupPath
      (nonzeroState input) = some (baseLoopState input 0 0) := by
  simp (config := { maxSteps := 100000 })
    [baseSetupPath, opAt, pushAt,
      Challenge.EvmProof.Stepper.runLocatedBlock,
      Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
      nonzeroState, baseLoopState, wordPCs]

set_option linter.unusedSimpArgs false in
theorem run_baseIteration (input : ByteArray) (i : Nat) (base : UInt256)
    (hvalid : ValidInput input) (hi : i < baseSize input) :
    Challenge.EvmProof.Stepper.runLocatedBlock baseIterationPath
      (baseLoopState input i base) =
        some (baseLoopState input (i + 1) (baseStep input i base)) := by
  rcases hvalid with ⟨_, hb, he, hm⟩
  have hi256 : i < 2 ^ 256 := by omega
  have hb256 : baseSize input < 2 ^ 256 := by omega
  have hoff : 96 + i < 2 ^ 256 := by omega
  have hadd := Challenge.EvmProof.Word.ofNat_add_ofNat
    (a := i) (b := 96) (by omega : i + 96 < 2 ^ 256)
  have hisucc := Challenge.EvmProof.Word.ofNat_add_ofNat
    (a := 1) (b := i) (by omega : 1 + i < 2 ^ 256)
  simp (config := { maxSteps := 700000 })
    [baseIterationPath, opAt, pushAt, Accessors.calldataBytePath,
      Challenge.EvmProof.Stepper.runLocatedBlock,
      Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
      baseLoopState, baseStep, byteWord, Accessors.calldataByteValue,
      nonzeroState, callerRest, wordPCs, List.exchange,
      UInt256.isTrue, UInt256.lt, Challenge.EvmProof.Word.word_toNat_ofNat,
      Nat.mod_eq_of_lt, hi, hi256, hb256, hoff, hadd, hisucc]

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

def gasSteps_baseSetup (input : ByteArray) :
    Challenge.EvmProof.GasSteps (nonzeroState input)
      (baseLoopState input 0 0) := by
  apply Challenge.EvmProof.Stepper.runLocatedBlock_sound
    Artifact.referenceArtifact .Osaka baseSetupPath
  · rfl
  · rfl
  · exact run_baseSetup input
  · rfl
  · exact deployAddress_not_precompile

def gasSteps_baseIteration (input : ByteArray) (i : Nat) (base : UInt256)
    (hvalid : ValidInput input) (hi : i < baseSize input) :
    Challenge.EvmProof.GasSteps (baseLoopState input i base)
      (baseLoopState input (i + 1) (baseStep input i base)) := by
  apply Challenge.EvmProof.Stepper.runLocatedBlock_sound
    Artifact.referenceArtifact .Osaka baseIterationPath
  · rfl
  · rfl
  · exact run_baseIteration input i base hvalid hi
  · rfl
  · exact deployAddress_not_precompile

def gasSteps_baseLoop (input : ByteArray) (hvalid : ValidInput input) :
    Challenge.EvmProof.GasSteps (baseLoopState input 0 0)
      (baseLoopState input (baseSize input) (baseAfter input (baseSize input))) := by
  exact Challenge.EvmProof.GasSteps.iterateBounded (baseSize input)
    (fun i hi => gasSteps_baseIteration input i (baseAfter input i) hvalid hi)

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
