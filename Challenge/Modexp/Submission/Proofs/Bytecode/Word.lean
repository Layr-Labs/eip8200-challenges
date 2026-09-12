import Challenge.Modexp.Submission.Proofs.Algorithm
import Challenge.Modexp.Submission.Proofs.Bytecode.Accessors
import Challenge.Modexp.Submission.Proofs.Bytecode.Dispatch
import Challenge.EvmProof.Bytes
import Challenge.Modexp.Submission.Proofs.Bytecode.WordEnds
set_option warningAsError true
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000
set_option maxErrors 1
/-!
# One-word MODEXP path

This module certifies the entry of the `MULMOD` fast path and names its loop
invariants.  Operand widths and offsets are expressed with the same padded
byte decoder as the challenge specification.
-/

namespace Challenge.Modexp.Submission.Proofs.Bytecode.Word

open EvmSemantics
open EvmSemantics.EVM

attribute [local simp] Challenge.EvmProof.Word.ofNat_add_mod
  Challenge.EvmProof.Word.succ_ofNat_mod

def wfOp {op : Operation}
    (hopcode : Decode.opcodeOf (YulEvmCompiler.Instr.opByte op) = some op)
    (hplain : YulEvmCompiler.plainOp op)
    (havailable : op.availableInFork .Osaka = true) :
    Challenge.EvmProof.Stepper.WellFormed .Osaka (.op op) :=
  ⟨hopcode, hplain, havailable⟩

def opAt (index : Nat) (op : Operation)
    (hget : Artifact.submissionInstructions[index]? = some (.op op) := by rfl)
    (hopcode : Decode.opcodeOf (YulEvmCompiler.Instr.opByte op) = some op := by decide)
    (hplain : YulEvmCompiler.plainOp op := by trivial)
    (havailable : op.availableInFork .Osaka = true := by rfl) :
    Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka :=
  ⟨index, .op op, hget, wfOp hopcode hplain havailable⟩

def pushAt (index : Nat) (width : Fin 33) (value : UInt256)
    (hget : Artifact.submissionInstructions[index]? = some (.push width value) := by rfl)
    (hwf : Challenge.EvmProof.Stepper.WellFormed .Osaka (.push width value) := by decide) :
    Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka :=
  ⟨index, .push width value, hget, hwf⟩

def startPath :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 435 .JUMPDEST, opAt 436 (.Dup ⟨5, by decide⟩),
   opAt 437 .CALLDATALOAD, opAt 438 (.Dup ⟨3, by decide⟩),
   pushAt 439 1 32, opAt 440 .SUB, pushAt 441 1 3,
   opAt 442 .SHL, opAt 443 .SHR, opAt 444 (.Dup ⟨0, by decide⟩),
   pushAt 445 2 543, opAt 446 .JUMPI]

def zeroTailPath :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 447 (.Dup ⟨3, by decide⟩), pushAt 448 0 0,
   opAt 449 .RETURN]

def zeroModulusPath :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  startPath ++ zeroTailPath

def startLoadPath := startPath.take 11
def startJumpPath := [opAt 446 .JUMPI]

def baseSetupPath :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 450 .JUMPDEST, pushAt 451 0 0, pushAt 452 0 0]

def baseGuardPath :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 453 .JUMPDEST, opAt 454 (.Dup ⟨3, by decide⟩),
   opAt 455 (.Dup ⟨1, by decide⟩), opAt 456 .LT, opAt 457 .ISZERO,
   pushAt 458 2 583, opAt 459 .JUMPI]

def baseCallPath :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 460 (.Dup ⟨2, by decide⟩), pushAt 461 2 566, pushAt 462 0 0,
   opAt 463 (.Dup ⟨3, by decide⟩), opAt 464 (.Dup ⟨10, by decide⟩),
   opAt 465 .ADD, pushAt 466 1 55, opAt 467 .JUMP]

def baseTailHeadPath :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 468 .JUMPDEST, opAt 469 (.Dup ⟨4, by decide⟩), pushAt 470 2 256,
   opAt 471 (.Dup ⟨5, by decide⟩), opAt 472 .MULMOD, opAt 473 .ADDMOD,
  ]

def baseTailSwapPath :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 474 (.Swap ⟨1, by decide⟩)]

def baseTailPopPath :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 475 .POP]

def baseTailFinishPath :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 476 1 1,
   opAt 477 .ADD, pushAt 478 2 546, opAt 479 .JUMP]

def baseTailPath :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  baseTailHeadPath ++ baseTailSwapPath ++ baseTailPopPath ++ baseTailFinishPath

def baseFinishTailPath :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 480 .JUMPDEST, opAt 481 .POP, opAt 482 (.Dup ⟨1, by decide⟩),
   pushAt 483 1 1, opAt 484 .MOD, pushAt 485 0 0]

def expGuardPath :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 486 .JUMPDEST, opAt 487 (.Dup ⟨5, by decide⟩),
   opAt 488 (.Dup ⟨1, by decide⟩), opAt 489 .EQ,
   pushAt 490 2 621, opAt 491 .JUMPI]

def expLoadPath :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 492 (.Dup ⟨0, by decide⟩), opAt 493 (.Dup ⟨9, by decide⟩),
   opAt 494 .ADD, opAt 495 (.Dup ⟨0, by decide⟩), opAt 496 .CALLDATALOAD,
   pushAt 497 0 0, opAt 498 .BYTE, pushAt 499 0 0]

def bitJumpPath :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 501 .JUMP]

/-- The head of the unrolled block derives `base - 1` for the eight copies. -/
def bitHeadPath :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2304 .JUMPDEST, pushAt 2305 1 1,
   opAt 2306 (.Dup ⟨6, by decide⟩), opAt 2307 .SUB]

/-- Its tail drops `base - 1` and rejoins the byte loop. -/
def bitExitPath :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2442 .POP, pushAt 2443 2 610, opAt 2444 .JUMP]

/-- Byte offset of the copy of the unrolled body that handles exponent bit `j`. -/
def bitPC (j : Nat) : Nat := if j = 8 then 3147 else 2990 + 20 * j

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
    pc := UInt256.ofNat 543
    stack := [UInt256.ofNat (modulusValue input),
      UInt256.ofNat (baseSize input), UInt256.ofNat (exponentSize input),
      UInt256.ofNat (modulusSize input), UInt256.ofNat 96,
      UInt256.ofNat (expOffset input), UInt256.ofNat (modulusOffset input),
      UInt256.ofNat 1186] ++ callerRest input }

def loadedState (input : ByteArray) : State :=
  { nonzeroState input with
    pc := UInt256.ofNat 539
    stack := (543 : UInt256) :: UInt256.ofNat (modulusValue input) ::
      (nonzeroState input).stack }

def zeroDispatchState (input : ByteArray) : State :=
  { nonzeroState input with pc := UInt256.ofNat 540 }

def zeroModulusFinalState (input : ByteArray) : State :=
  { Dispatch.wordEntryState input with
    pc := UInt256.ofNat 542
    stack := [UInt256.ofNat 0, UInt256.ofNat (baseSize input),
      UInt256.ofNat (exponentSize input), UInt256.ofNat (modulusSize input),
      UInt256.ofNat 96, UInt256.ofNat (expOffset input),
      UInt256.ofNat (modulusOffset input), UInt256.ofNat 1186] ++ callerRest input
    halt := .Returned
    hReturn := MachineState.readPadded ByteArray.empty 0 (modulusSize input)
    activeWords := (Dispatch.wordEntryState input).activeWordsAfterUInt256
      0 (modulusSize input) }

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
    pc := UInt256.ofNat 546
    stack := [UInt256.ofNat i, base, UInt256.ofNat (modulusValue input),
      UInt256.ofNat (baseSize input), UInt256.ofNat (exponentSize input),
      UInt256.ofNat (modulusSize input), UInt256.ofNat 96,
      UInt256.ofNat (expOffset input), UInt256.ofNat (modulusOffset input),
      UInt256.ofNat 1186] ++ callerRest input }

def baseGuardState (input : ByteArray) (i : Nat) (base : UInt256) : State :=
  { baseLoopState input i base with pc := UInt256.ofNat 555 }

def baseRest (input : ByteArray) (i : Nat) (base : UInt256) : List UInt256 :=
  [UInt256.ofNat (modulusValue input), UInt256.ofNat i, base,
    UInt256.ofNat (modulusValue input), UInt256.ofNat (baseSize input),
    UInt256.ofNat (exponentSize input), UInt256.ofNat (modulusSize input),
    UInt256.ofNat 96, UInt256.ofNat (expOffset input),
    UInt256.ofNat (modulusOffset input), UInt256.ofNat 1186] ++ callerRest input

def baseCallState (input : ByteArray) (i : Nat) (base : UInt256) : State :=
  Accessors.calldataByteEntry (baseLoopState input i base)
    (UInt256.ofNat (96 + i)) 0 566 (baseRest input i base)

def baseReturnedState (input : ByteArray) (i : Nat) (base : UInt256) : State :=
  Accessors.calldataByteReturned (baseLoopState input i base)
    (UInt256.ofNat (96 + i)) 566 (baseRest input i base)

def baseTailMidState (input : ByteArray) (i : Nat) (base : UInt256) : State :=
  { baseLoopState input i base with
    pc := UInt256.ofNat 574
    stack := baseStep input i base :: UInt256.ofNat i :: base ::
      UInt256.ofNat (modulusValue input) ::
      UInt256.ofNat (baseSize input) :: UInt256.ofNat (exponentSize input) ::
      UInt256.ofNat (modulusSize input) :: UInt256.ofNat 96 ::
      UInt256.ofNat (expOffset input) :: UInt256.ofNat (modulusOffset input) ::
      UInt256.ofNat 1186 :: callerRest input }

def baseTailSwappedState (input : ByteArray) (i : Nat) (base : UInt256) : State :=
  { baseLoopState input i base with
    pc := UInt256.ofNat 575
    stack := base :: UInt256.ofNat i :: baseStep input i base ::
      UInt256.ofNat (modulusValue input) ::
      UInt256.ofNat (baseSize input) :: UInt256.ofNat (exponentSize input) ::
      UInt256.ofNat (modulusSize input) :: UInt256.ofNat 96 ::
      UInt256.ofNat (expOffset input) :: UInt256.ofNat (modulusOffset input) ::
      UInt256.ofNat 1186 :: callerRest input }

def baseTailPoppedState (input : ByteArray) (i : Nat) (base : UInt256) : State :=
  { baseLoopState input i base with
    pc := UInt256.ofNat 576
    stack := UInt256.ofNat i :: baseStep input i base ::
      UInt256.ofNat (modulusValue input) ::
      UInt256.ofNat (baseSize input) :: UInt256.ofNat (exponentSize input) ::
      UInt256.ofNat (modulusSize input) :: UInt256.ofNat 96 ::
      UInt256.ofNat (expOffset input) :: UInt256.ofNat (modulusOffset input) ::
      UInt256.ofNat 1186 :: callerRest input }

def baseFinishDispatchState (input : ByteArray) (base : UInt256) : State :=
  { baseLoopState input (baseSize input) base with pc := UInt256.ofNat 583 }

def expLoopState (input : ByteArray) (i : Nat) (acc base : UInt256) : State :=
  { nonzeroState input with
    pc := UInt256.ofNat 590
    stack := [UInt256.ofNat i, acc, base, UInt256.ofNat (modulusValue input),
      UInt256.ofNat (baseSize input), UInt256.ofNat (exponentSize input),
      UInt256.ofNat (modulusSize input), UInt256.ofNat 96,
      UInt256.ofNat (expOffset input), UInt256.ofNat (modulusOffset input),
      UInt256.ofNat 1186] ++ callerRest input }

def expGuardState (input : ByteArray) (i : Nat) (acc base : UInt256) : State :=
  { expLoopState input i acc base with pc := UInt256.ofNat 598 }

/-- The frame the unrolled block never touches, kept as one list so the copies
can leave it opaque. -/
def bitTail (input : ByteArray) : List UInt256 :=
  [UInt256.ofNat (baseSize input), UInt256.ofNat (exponentSize input),
    UInt256.ofNat (modulusSize input), UInt256.ofNat 96,
    UInt256.ofNat (expOffset input), UInt256.ofNat (modulusOffset input),
    UInt256.ofNat 1186] ++ callerRest input

def bitLoopState (input : ByteArray) (outer j : Nat) (byte offset : UInt256)
    (acc base : UInt256) : State :=
  { nonzeroState input with
    pc := UInt256.ofNat 606
    stack := [UInt256.ofNat j, byte, offset, UInt256.ofNat outer, acc, base,
      UInt256.ofNat (modulusValue input)] ++ bitTail input }

theorem bitFrame (input : ByteArray) (outer : Nat) (byte offset acc base : UInt256) :
    WordStep.Frame (bitLoopState input outer 0 byte offset acc base) :=
  ⟨rfl, rfl, rfl, deployAddress_not_precompile⟩

/-- The copies carry `base - 1` above the loop frame. -/
def bitUnrollState (input : ByteArray) (outer j : Nat) (byte offset : UInt256)
    (acc base : UInt256) : State :=
  WordStep.stW (bitLoopState input outer 0 byte offset acc base) (bitPC j)
    ([base - UInt256.ofNat 1, UInt256.ofNat 0, byte, offset, UInt256.ofNat outer,
      acc, base, UInt256.ofNat (modulusValue input)] ++ bitTail input)

def bitPushState (input : ByteArray) (outer : Nat) (byte offset : UInt256)
    (acc base : UInt256) : State :=
  let s := bitLoopState input outer 0 byte offset acc base
  { s with pc := UInt256.ofNat 609, stack := UInt256.ofNat 3295 :: s.stack }

def bitHeadState (input : ByteArray) (outer : Nat) (byte offset : UInt256)
    (acc base : UInt256) : State :=
  WordStep.stW (bitLoopState input outer 0 byte offset acc base) 2985
    ([UInt256.ofNat 0, byte, offset, UInt256.ofNat outer, acc, base,
      UInt256.ofNat (modulusValue input)] ++ bitTail input)

theorem jump3695 : Decode.isValidJumpDest submissionBytecode 2985 = true :=
  Artifact.isValidJumpDest_index 2304 (by rfl)

/-- The loop head jumps into the unrolled block. -/
def gasSteps_bitEntry (input : ByteArray) (outer : Nat)
    (byte offset acc base : UInt256) :
    Challenge.EvmProof.GasSteps (bitLoopState input outer 0 byte offset acc base)
      (bitHeadState input outer byte offset acc base) :=
  WordEnds.gasSteps_bitEntry_sym (bitLoopState input outer 0 byte offset acc base)
    (bitTail input) (UInt256.ofNat 0) byte offset (UInt256.ofNat outer) acc base
    (UInt256.ofNat (modulusValue input))
    (bitFrame input outer byte offset acc base) (by simp [bitTail, callerRest])
    (by exact jump3695)

/-- The head of the block derives `base - 1` for the eight copies. -/
def gasSteps_bitHead (input : ByteArray) (outer : Nat)
    (byte offset acc base : UInt256) :
    Challenge.EvmProof.GasSteps (bitHeadState input outer byte offset acc base)
      (bitUnrollState input outer 0 byte offset acc base) :=
  WordEnds.gasSteps_bitHead_sym (bitLoopState input outer 0 byte offset acc base)
    (bitTail input) (UInt256.ofNat 0) byte offset (UInt256.ofNat outer) acc base
    (UInt256.ofNat (modulusValue input))
    (bitFrame input outer byte offset acc base) (by simp [bitTail, callerRest])

def exponentBit (byte : UInt256) (j : Nat) : UInt256 :=
  UInt256.land
    (UInt256.shiftRight byte (UInt256.ofNat (7 - j))) (UInt256.ofNat 1)

def bitStep (input : ByteArray) (byte : UInt256) (j : Nat)
    (acc base : UInt256) : UInt256 :=
  let modulus := UInt256.ofNat (modulusValue input)
  let bit := exponentBit byte j
  let square := UInt256.mulMod acc acc modulus
  let product := UInt256.mulMod square base modulus
  let mask := UInt256.ofNat 0 - bit
  UInt256.xor square (UInt256.land (UInt256.xor square product) mask)

/-- The multiplier the unrolled copy uses: `1` when the bit is clear and the
base when it is set. -/
def bitStepSel (input : ByteArray) (byte : UInt256) (j : Nat)
    (acc base : UInt256) : UInt256 :=
  let modulus := UInt256.ofNat (modulusValue input)
  UInt256.mulMod (UInt256.mulMod acc acc modulus)
    (UInt256.ofNat 1 + (base - UInt256.ofNat 1) * exponentBit byte j) modulus

theorem byteWord_eq (input : ByteArray) (offset : Nat)
    (hoffset : offset < 2 ^ 256) :
    byteWord input offset = UInt256.ofNat
      (YulSemantics.EVM.byteFrom input.toList offset).toNat := by
  unfold byteWord Accessors.calldataByteValue
  rw [Challenge.EvmProof.Word.word_toNat_ofNat,
    Nat.mod_eq_of_lt hoffset]
  change UInt256.byteAt ⟨0⟩ (MachineState.readWord input offset) = _
  exact Challenge.EvmProof.Bytes.byteAt_zero_readWord input offset

theorem baseStep_spec (input : ByteArray) (i modulus : Nat)
    (hmodulus : modulusValue input = modulus) (hmodpos : 0 < modulus)
    (hmodlt : modulus < 2 ^ 256) (hoffset : 96 + i < 2 ^ 256) :
    baseStep input i (UInt256.ofNat
      (Precompile.bytesToNatPadded input 96 i % modulus)) =
      UInt256.ofNat
        (Precompile.bytesToNatPadded input 96 (i + 1) % modulus) := by
  let p := Precompile.bytesToNatPadded input 96 i
  have hbase : p % modulus < modulus := Nat.mod_lt _ hmodpos
  have hbase256 : p % modulus < 2 ^ 256 := hbase.trans hmodlt
  have hbyte := byteWord_eq input (96 + i) hoffset
  have hmword : (UInt256.ofNat modulus).val.val ≠ 0 := by
    change (UInt256.ofNat modulus).toNat ≠ 0
    rw [Challenge.EvmProof.Word.word_toNat_ofNat, Nat.mod_eq_of_lt hmodlt]
    omega
  have hmul : (p % modulus * 256) % modulus < modulus :=
    Nat.mod_lt _ hmodpos
  have hmul256 : (p % modulus * 256) % modulus < 2 ^ 256 :=
    hmul.trans hmodlt
  have hbyte256 :
      (YulSemantics.EVM.byteFrom input.toList (96 + i)).toNat < 2 ^ 256 :=
    (YulSemantics.EVM.byteFrom input.toList (96 + i)).toNat_lt.trans (by norm_num)
  unfold baseStep
  rw [hmodulus, hbyte]
  unfold UInt256.mulMod UInt256.addMod
  rw [if_neg hmword, if_neg hmword]
  simp only [Challenge.EvmProof.Word.word_toNat_ofNat]
  rw [Nat.mod_eq_of_lt hbase256,
    Nat.mod_eq_of_lt (by norm_num : 256 < 2 ^ 256),
    Nat.mod_eq_of_lt hmodlt, Nat.mod_eq_of_lt hmul256,
    Nat.mod_eq_of_lt hbyte256]
  apply congrArg UInt256.ofNat
  rw [Challenge.EvmProof.Bytes.bytesToNatPadded_succ]
  simp [p, Nat.add_mod, Nat.mul_mod]

theorem baseAfter_correct (input : ByteArray) (count : Nat)
    (hmodpos : 0 < modulusValue input)
    (hmodlt : modulusValue input < 2 ^ 256)
    (hbaseSize : baseSize input ≤ 1024)
    (hcount : count ≤ baseSize input) :
    baseAfter input count = UInt256.ofNat
      (Precompile.bytesToNatPadded input 96 count % modulusValue input) := by
  induction count with
  | zero =>
      rw [baseAfter, Challenge.EvmProof.Bytes.bytesToNatPadded_zero_width,
        Nat.zero_mod]
      decide
  | succ count ih =>
      rw [baseAfter, ih (by omega)]
      exact baseStep_spec input count (modulusValue input)
        rfl hmodpos hmodlt (by omega)

@[simp] private theorem startPCs (i : Nat)
    (hi : 435 ≤ i) (hii : i ≤ 449) :
    Artifact.submissionArtifact.instructionPC i =
      ([524,525,526,527,528,530,531,533,534,535,536,539,540,541,542] : List Nat)[i - 435]! := by
  interval_cases i <;> decide

@[simp] private theorem jump538 :
    Decode.isValidJumpDest submissionBytecode 543 = true :=
  Artifact.isValidJumpDest_index 450 (by rfl)

@[simp] theorem wordPCs (i : Nat)
    (hi : 450 ≤ i) (hii : i ≤ 479) :
    Artifact.submissionArtifact.instructionPC i =
      ([543,544,545,546,547,548,549,550,551,554,555,556,559,560,561,562,563,565,566,567,568,571,572,573,574,575,576,578,579,582] : List Nat)[i - 450]! := by
  interval_cases i <;> decide

@[simp] theorem jump582 :
    Decode.isValidJumpDest submissionBytecode 583 = true :=
  Artifact.isValidJumpDest_index 480 (by rfl)

@[simp] theorem jump562 :
    Decode.isValidJumpDest submissionBytecode 566 = true :=
  Artifact.isValidJumpDest_index 468 (by rfl)

@[simp] theorem jump4 :
    Decode.isValidJumpDest submissionBytecode 55 = true :=
  Artifact.isValidJumpDest_index 40 (by rfl)

@[simp] theorem jump541 :
    Decode.isValidJumpDest submissionBytecode 546 = true :=
  Artifact.isValidJumpDest_index 453 (by rfl)

@[simp] theorem baseFinishPCs (i : Nat)
    (hi : 480 ≤ i) (hii : i ≤ 485) :
    Artifact.submissionArtifact.instructionPC i =
      ([583,584,585,586,588,589] : List Nat)[i - 480]! := by
  interval_cases i <;> decide

@[simp] theorem expPCs (i : Nat)
    (hi : 486 ≤ i) (hii : i ≤ 509) :
    Artifact.submissionArtifact.instructionPC i =
      ([590,591,592,593,594,597,598,599,600,601,602,603,604,605,606,609,610,611,612,613,614,616,617,620] : List Nat)[i - 486]! := by
  interval_cases i <;> decide

@[simp] theorem jump669 :
    Decode.isValidJumpDest submissionBytecode 621 = true :=
  Artifact.isValidJumpDest_index 510 (by rfl)

@[simp] theorem jump655 :
    Decode.isValidJumpDest submissionBytecode 610 = true :=
  Artifact.isValidJumpDest_index 502 (by rfl)

@[simp] theorem jump589 :
    Decode.isValidJumpDest submissionBytecode 590 = true :=
  Artifact.isValidJumpDest_index 486 (by rfl)

set_option linter.unusedSimpArgs false in
theorem run_startLoad (input : ByteArray) (hvalid : ValidInput input)
    (hmsize : 0 < modulusSize input) (hword : modulusSize input ≤ 32) :
    Challenge.EvmProof.Stepper.runLocatedBlock startLoadPath
      (Dispatch.wordEntryState input) = some (loadedState input) := by
  rcases hvalid with ⟨_, hb, he, hm⟩
  have hsub := Challenge.EvmProof.Word.ofNat_sub_ofNat hword
    (by norm_num : 32 < 2 ^ 256)
  have hshift :
      UInt256.shiftLeft (UInt256.ofNat (32 - modulusSize input))
          (UInt256.ofNat 3) =
        UInt256.ofNat ((32 - modulusSize input) * 8) := by
    rw [Challenge.EvmProof.Word.shiftLeft_ofNat] <;>
      norm_num [Nat.shiftLeft_eq] <;> omega
  have hslice := Challenge.EvmProof.Bytes.shiftRight_readWord input
    (modulusOffset input) (modulusSize input) hmsize hword
  have hmodOff : modulusOffset input < 2 ^ 256 := by
    simp only [modulusOffset, expOffset]
    omega
  have hshiftBound : (32 - modulusSize input) * 2 ^ 3 < 2 ^ 256 := by
    norm_num
    omega
  have hloaded :
      (MachineState.readWord input
        ((96 + baseSize input + exponentSize input) % 2 ^ 256)).shiftRight
          (((32 : UInt256) - UInt256.ofNat (modulusSize input)).shiftLeft 3) =
        UInt256.ofNat (modulusValue input) := by
    change (MachineState.readWord input
      ((modulusOffset input) % 2 ^ 256)).shiftRight _ = _
    rw [Nat.mod_eq_of_lt hmodOff,
      show (32 : UInt256) = UInt256.ofNat 32 by decide, hsub,
      show (3 : UInt256) = UInt256.ofNat 3 by decide, hshift, hslice]
    rfl
  norm_num at hloaded
  simp (config := { maxSteps := 300000 })
    [startLoadPath, startPath, opAt, pushAt,
      Challenge.EvmProof.Stepper.runLocatedBlock,
      Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
      Dispatch.wordEntryState, Main.headerState, initialState, loadedState,
      nonzeroState, callerRest,
      expOffset, modulusOffset, startPCs, hsub, hshift, hslice,
      hmodOff, hshiftBound, UInt256.isTrue,
      Challenge.EvmProof.Word.word_toNat_ofNat, Nat.mod_eq_of_lt,
      Challenge.EvmProof.Word.ofNat_add_mod,
      Challenge.EvmProof.Word.succ_ofNat_mod]
  rw [hloaded]
set_option linter.unusedSimpArgs false in
theorem run_startJump_nonzero (input : ByteArray)
    (hmodulus : 0 < modulusValue input)
    (hmodlt : modulusValue input < 2 ^ 256) :
    Challenge.EvmProof.Stepper.runLocatedBlock startJumpPath
      (loadedState input) = some (nonzeroState input) := by
  have hmodNat : modulusValue input % 2 ^ 256 = modulusValue input :=
    Nat.mod_eq_of_lt hmodlt
  have hcondition : modulusValue input % 2 ^ 256 ≠ 0 := by
    rw [hmodNat]
    omega
  have h538 : (543 : UInt256).toNat = 543 := by decide
  have h538Word : (543 : UInt256) = UInt256.ofNat 543 := by decide
  simp [startJumpPath, opAt, Challenge.EvmProof.Stepper.runLocatedBlock,
    Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
    loadedState, nonzeroState, callerRest, Dispatch.wordEntryState,
    Main.headerState, initialState, jump538, UInt256.isTrue,
    Challenge.EvmProof.Word.word_toNat_ofNat, hmodNat, hcondition,
    hmodulus, h538, h538Word, jump538]
  simp_all [hcondition, h538, h538Word, jump538]

set_option linter.unusedSimpArgs false in
theorem run_startJump_zero (input : ByteArray)
    (hmodulus : modulusValue input = 0) :
    Challenge.EvmProof.Stepper.runLocatedBlock startJumpPath
      (loadedState input) = some (zeroDispatchState input) := by
  simp [startJumpPath, opAt, Challenge.EvmProof.Stepper.runLocatedBlock,
    Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
    loadedState, zeroDispatchState, nonzeroState, callerRest,
    Dispatch.wordEntryState, Main.headerState, initialState,
    UInt256.isTrue, hmodulus,
    Challenge.EvmProof.Word.word_toNat_ofNat]

set_option linter.unusedSimpArgs false in
theorem run_zeroTail (input : ByteArray) (hvalid : ValidInput input)
    (hmodulus : modulusValue input = 0) :
    Challenge.EvmProof.Stepper.runLocatedBlock zeroTailPath
      (zeroDispatchState input) = some (zeroModulusFinalState input) := by
  rcases hvalid with ⟨_, _, _, hm⟩
  have hm' : modulusSize input < 2 ^ 256 := by omega
  have hmmod : modulusSize input % 2 ^ 256 = modulusSize input :=
    Nat.mod_eq_of_lt hm'
  have hmmodLiteral : modulusSize input %
      115792089237316195423570985008687907853269984665640564039457584007913129639936 =
        modulusSize input := by
    exact Nat.mod_eq_of_lt (by norm_num at hm'; exact hm')
  have h0 : (0 : UInt256).toNat = 0 := by decide
  simp [zeroTailPath, opAt, pushAt,
    Challenge.EvmProof.Stepper.runLocatedBlock,
    Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
    zeroDispatchState, zeroModulusFinalState, nonzeroState, callerRest,
    Dispatch.wordEntryState, Main.headerState, initialState, startPCs,
    Challenge.EvmProof.Word.word_toNat_ofNat, hmmod, hmmodLiteral,
    Nat.mod_eq_of_lt hm', h0, hmodulus]
  have hzeroRecord : ({ val := 0 } : UInt256).toNat = 0 := by decide
  simp_all [State.activeWordsAfterUInt256, MachineState.activeWordsAfter, hzeroRecord]

set_option linter.unusedSimpArgs false in
theorem run_baseSetup (input : ByteArray) :
    Challenge.EvmProof.Stepper.runLocatedBlock baseSetupPath
      (nonzeroState input) = some (baseLoopState input 0 0) := by
  have hzeroWord : UInt256.ofNat 0 = (0 : UInt256) := by decide
  simp (config := { maxSteps := 100000 })
    [baseSetupPath, opAt, pushAt,
      Challenge.EvmProof.Stepper.runLocatedBlock,
      Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
      nonzeroState, baseLoopState, callerRest, Dispatch.wordEntryState, Main.headerState,
      initialState, wordPCs, hzeroWord]
  decide

set_option linter.unusedSimpArgs false in
theorem run_baseGuard (input : ByteArray) (i : Nat) (base : UInt256)
    (hvalid : ValidInput input) (hi : i < baseSize input) :
    Challenge.EvmProof.Stepper.runLocatedBlock baseGuardPath
      (baseLoopState input i base) = some (baseGuardState input i base) := by
  rcases hvalid with ⟨_, hb, he, hm⟩
  have hi256 : i < 2 ^ 256 := by omega
  have hb256 : baseSize input < 2 ^ 256 := by omega
  have himod : i % 2 ^ 256 = i := Nat.mod_eq_of_lt hi256
  have hbmod : baseSize input % 2 ^ 256 = baseSize input :=
    Nat.mod_eq_of_lt hb256
  have hilt : i % 2 ^ 256 < baseSize input % 2 ^ 256 := by
    rw [himod, hbmod]
    exact hi
  have hisZero : (UInt256.ofNat 1).isZero.toNat = 0 := by decide
  have hcond :
      (if i % 2 ^ 256 < baseSize input % 2 ^ 256 then UInt256.ofNat 1
        else UInt256.ofNat 0).isZero.toNat = 0 := by
    rw [if_pos hilt]
    exact hisZero
  have hcondLiteral :
      (if i %
          115792089237316195423570985008687907853269984665640564039457584007913129639936 <
          baseSize input %
          115792089237316195423570985008687907853269984665640564039457584007913129639936
        then UInt256.ofNat 1 else UInt256.ofNat 0).isZero.toNat = 0 := by
    exact hcond
  have h550 : (555 : UInt256).toNat = 555 := by decide
  simp (config := { maxSteps := 150000 })
    [baseGuardPath, opAt, pushAt,
      Challenge.EvmProof.Stepper.runLocatedBlock,
      Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
      baseLoopState, baseGuardState, nonzeroState, callerRest,
      Dispatch.wordEntryState, Main.headerState, initialState, wordPCs,
      UInt256.isTrue, UInt256.lt, Challenge.EvmProof.Word.word_toNat_ofNat,
      hi, hi256, hb256, himod, hbmod, hilt, hisZero, hcond, hcondLiteral,
      h550]

set_option linter.unusedSimpArgs false in
theorem run_baseCall (input : ByteArray) (i : Nat) (base : UInt256)
    (hvalid : ValidInput input) (hi : i < baseSize input) :
    Challenge.EvmProof.Stepper.runLocatedBlock baseCallPath
      (baseGuardState input i base) = some (baseCallState input i base) := by
  rcases hvalid with ⟨_, hb, he, hm⟩
  have h4 : (55 : UInt256).toNat = 55 := by decide
  have h4Word : (55 : UInt256) = UInt256.ofNat 55 := by decide
  have hoff : 96 + i < 2 ^ 256 := by omega
  have hadd := Challenge.EvmProof.Word.ofNat_add_ofNat
    (a := i) (b := 96) (by omega : i + 96 < 2 ^ 256)
  have hzeroWord : ({ val := 0 } : UInt256) = 0 := by decide
  simp (config := { maxSteps := 150000 })
    [baseCallPath, opAt, pushAt,
      Challenge.EvmProof.Stepper.runLocatedBlock,
      Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
      baseGuardState, baseCallState, baseRest, baseLoopState,
      Accessors.calldataByteEntry, nonzeroState, callerRest,
      Dispatch.wordEntryState, Main.headerState, initialState, wordPCs,
      Challenge.EvmProof.Word.word_toNat_ofNat, h4, h4Word, hzeroWord,
      jump4, hoff, hadd]

set_option linter.unusedSimpArgs false in
theorem run_baseFinishGuard (input : ByteArray) (base : UInt256)
    (hvalid : ValidInput input) :
    Challenge.EvmProof.Stepper.runLocatedBlock baseGuardPath
      (baseLoopState input (baseSize input) base) =
        some (baseFinishDispatchState input base) := by
  rcases hvalid with ⟨_, hb, he, hm⟩
  have hb256 : baseSize input < 2 ^ 256 := by omega
  have hbmod : baseSize input % 2 ^ 256 = baseSize input :=
    Nat.mod_eq_of_lt hb256
  have h582 : (583 : UInt256).toNat = 583 := by decide
  have h582Word : (583 : UInt256) = UInt256.ofNat 583 := by decide
  have hzeroFalse : ¬(UInt256.ofNat 0).isZero.toNat = 0 := by decide
  simp (config := { maxSteps := 150000 })
    [baseGuardPath, opAt, pushAt,
      Challenge.EvmProof.Stepper.runLocatedBlock,
      Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
      baseLoopState, baseFinishDispatchState, nonzeroState, callerRest,
      Dispatch.wordEntryState, Main.headerState, initialState, wordPCs,
      UInt256.isTrue, UInt256.lt, Challenge.EvmProof.Word.word_toNat_ofNat,
      hb256, hbmod, hzeroFalse, h582, h582Word, jump582]

/- The exponent trace declarations live in `WordExpRuns` so their large
   proof terms are elaborated in a bounded module. -/
/-
set_option linter.unusedSimpArgs false in
theorem run_expGuard (input : ByteArray) (i : Nat) (acc base : UInt256)
    (hvalid : ValidInput input) (hi : i < exponentSize input) :
    Challenge.EvmProof.Stepper.runLocatedBlock expGuardPath
      (expLoopState input i acc base) = some (expGuardState input i acc base) := by
  rcases hvalid with ⟨_, hb, he, hm⟩
  have hi256 : i < 2 ^ 256 := by omega
  have he256 : exponentSize input < 2 ^ 256 := by omega
  have himod : i % 2 ^ 256 = i := Nat.mod_eq_of_lt hi256
  have hemod : exponentSize input % 2 ^ 256 = exponentSize input :=
    Nat.mod_eq_of_lt he256
  have hne : i ≠ exponentSize input := Nat.ne_of_lt hi
  have heq : UInt256.eq (UInt256.ofNat i) (UInt256.ofNat (exponentSize input)) =
      UInt256.ofNat 0 := by
    rw [UInt256.eq, Challenge.EvmProof.Word.word_toNat_ofNat,
      Challenge.EvmProof.Word.word_toNat_ofNat, himod, hemod, if_neg hne]
  have h598 : (576 : UInt256).toNat = 576 := by decide
  have hzeroNat : (UInt256.ofNat 0).toNat = 0 := by decide
  simp (config := { maxSteps := 150000 })
    [expGuardPath, opAt, pushAt,
      Challenge.EvmProof.Stepper.runLocatedBlock,
      Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
      expLoopState, expGuardState, nonzeroState, callerRest,
      Dispatch.wordEntryState, Main.headerState, initialState, expPCs,
      UInt256.isTrue, Challenge.EvmProof.Word.word_toNat_ofNat,
      hi, hi256, he256, himod, hemod, hne, heq, hzeroNat, h598]

set_option linter.unusedSimpArgs false in
theorem run_expLoad (input : ByteArray) (i : Nat) (acc base : UInt256)
    (hvalid : ValidInput input) (hi : i < exponentSize input) :
    Challenge.EvmProof.Stepper.runLocatedBlock expLoadPath
      (expGuardState input i acc base) =
        some (bitLoopState input i 0 (byteWord input (expOffset input + i))
          (UInt256.ofNat (expOffset input + i)) acc base) := by
  rcases hvalid with ⟨_, hb, he, hm⟩
  have hoff : expOffset input + i < 2 ^ 256 := by
    simp only [expOffset]
    omega
  have hadd := Challenge.EvmProof.Word.ofNat_add_ofNat
    (a := expOffset input) (b := i) hoff
  have hzeroWord : UInt256.ofNat 0 = (0 : UInt256) := by decide
  have hzeroRaw : ({ val := 0 } : UInt256) = 0 := by decide
  simp (config := { maxSteps := 175000 })
    [expLoadPath, opAt, pushAt,
      Challenge.EvmProof.Stepper.runLocatedBlock,
      Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
      expGuardState, expLoopState, bitLoopState, bitTail, byteWord,
      Accessors.calldataByteValue,
      nonzeroState, callerRest, Dispatch.wordEntryState, Main.headerState,
      initialState, expPCs, Challenge.EvmProof.Word.word_toNat_ofNat,
      hoff, hadd, hzeroWord, hzeroRaw]

-/

@[simp] theorem zeroModulusFinalState_isDone (input : ByteArray) :
    (zeroModulusFinalState input).isDone = true := by
  rfl

theorem zeroModulusFinalState_result (input : ByteArray)
    (hmsize : 0 < modulusSize input) (hmodulus : modulusValue input = 0) :
    (zeroModulusFinalState input).toResult = .returned (spec input) := by
  rw [show (zeroModulusFinalState input).toResult =
      .returned (Precompile.natToBytes 0 (modulusSize input)) by
    simp [zeroModulusFinalState, Algorithm.zeroBytes]]
  have hmodulus' :
      Precompile.bytesToNatPadded input
        (96 + baseSize input + exponentSize input) (modulusSize input) = 0 := by
    simpa [modulusValue, modulusOffset, expOffset, Nat.add_assoc] using hmodulus
  simp [spec, Nat.ne_of_gt hmsize, hmodulus', Precompile.modPow]

end Challenge.Modexp.Submission.Proofs.Bytecode.Word
