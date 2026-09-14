import Challenge.Modexp.Submission.Proofs.Bytecode.PCFast
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
  [opAt 88 .JUMPDEST,
   opAt 89 (.Dup ⟨5, by decide⟩),
   opAt 90 .CALLDATALOAD,
   opAt 91 (.Dup ⟨3, by decide⟩),
   pushAt 92 1 32,
   opAt 93 .SUB,
   pushAt 94 1 3,
   opAt 95 .SHL,
   opAt 96 .SHR,
   opAt 97 (.Dup ⟨0, by decide⟩),
   pushAt 98 1 162,
   opAt 99 .JUMPI]

def zeroTailPath :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 100 (.Dup ⟨3, by decide⟩),
   pushAt 101 0 0,
   opAt 102 .RETURN]

def zeroModulusPath :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  startPath ++ zeroTailPath

def startLoadPath := startPath.take 11
def startJumpPath := [opAt 99 .JUMPI]

def baseSetupPath :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 103 .JUMPDEST,
   pushAt 104 0 0,
   pushAt 105 0 0]

def baseGuardPath :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 106 .JUMPDEST,
   opAt 107 (.Dup ⟨3, by decide⟩),
   opAt 108 (.Dup ⟨1, by decide⟩),
   opAt 109 .LT,
   opAt 110 .ISZERO,
   pushAt 111 1 199,
   opAt 112 .JUMPI]

def baseCallPath :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 113 (.Dup ⟨2, by decide⟩),
   pushAt 114 1 183,
   pushAt 115 0 0,
   opAt 116 (.Dup ⟨3, by decide⟩),
   opAt 117 (.Dup ⟨10, by decide⟩),
   opAt 118 .ADD,
   pushAt 119 1 134,
   opAt 120 .JUMP]

def baseTailHeadPath :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 121 .JUMPDEST, opAt 122 (.Dup ⟨4, by decide⟩), pushAt 123 2 256,
   opAt 124 (.Dup ⟨5, by decide⟩), opAt 125 .MULMOD, opAt 126 .ADDMOD,
  ]

def baseTailSwapPath :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 127 (.Swap ⟨1, by decide⟩)]

def baseTailPopPath :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 128 .POP]

def baseTailFinishPath :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 129 1 1,
   opAt 130 .ADD,
   pushAt 131 1 165,
   opAt 132 .JUMP]

def baseTailPath :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  baseTailHeadPath ++ baseTailSwapPath ++ baseTailPopPath ++ baseTailFinishPath

def baseFinishTailPath :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 133 .JUMPDEST,
   opAt 134 .POP,
   opAt 135 (.Dup ⟨1, by decide⟩),
   pushAt 136 1 1,
   opAt 137 .LT,
   pushAt 138 0 0]

def expGuardPath :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 139 .JUMPDEST,
   opAt 140 (.Dup ⟨5, by decide⟩),
   opAt 141 (.Dup ⟨1, by decide⟩),
   opAt 142 .EQ,
   pushAt 143 1 235,
   opAt 144 .JUMPI]

def expLoadPath :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 145 (.Dup ⟨0, by decide⟩),
   opAt 146 (.Dup ⟨9, by decide⟩),
   opAt 147 .ADD,
   opAt 148 (.Dup ⟨0, by decide⟩),
   opAt 149 .CALLDATALOAD,
   pushAt 150 0 0,
   opAt 151 .BYTE,
   pushAt 152 0 0]

def bitJumpPath :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 154 .JUMP]

/-- The head of the unrolled block derives `base - 1` for the eight copies. -/
def bitHeadPath :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1885 .JUMPDEST,
   pushAt 1886 1 1,
   opAt 1887 (.Dup ⟨6, by decide⟩),
   opAt 1888 .SUB]

/-- Its tail drops `base - 1` and rejoins the byte loop. -/
def bitExitPath :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1974 .POP,
   pushAt 1975 1 225,
   opAt 1976 .JUMP]

/-- Byte offset of the copy of the unrolled body that handles exponent bit `j`. -/
def bitPC (j : Nat) : Nat :=
  match j with
  | 0 | 4 => 2505
  | 1 | 5 => 2528
  | 2 | 6 => 2550
  | 3 | 7 => 2572
  | _ => 2605

def bitCounter (j : Nat) : Nat := if j < 4 then 0 else if j < 8 then 4 else 8

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
    pc := UInt256.ofNat 162
    stack := [UInt256.ofNat (modulusValue input),
      UInt256.ofNat (baseSize input), UInt256.ofNat (exponentSize input),
      UInt256.ofNat (modulusSize input), UInt256.ofNat 96,
      UInt256.ofNat (expOffset input), UInt256.ofNat (modulusOffset input),
      UInt256.ofNat 1186] ++ callerRest input }

def loadedState (input : ByteArray) : State :=
  { nonzeroState input with
    pc := UInt256.ofNat 158
    stack := (162 : UInt256) :: UInt256.ofNat (modulusValue input) ::
      (nonzeroState input).stack }

def zeroDispatchState (input : ByteArray) : State :=
  { nonzeroState input with pc := UInt256.ofNat 159 }

def zeroModulusFinalState (input : ByteArray) : State :=
  { Dispatch.wordEntryState input with
    pc := UInt256.ofNat 161
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
    pc := UInt256.ofNat 165
    stack := [UInt256.ofNat i, base, UInt256.ofNat (modulusValue input),
      UInt256.ofNat (baseSize input), UInt256.ofNat (exponentSize input),
      UInt256.ofNat (modulusSize input), UInt256.ofNat 96,
      UInt256.ofNat (expOffset input), UInt256.ofNat (modulusOffset input),
      UInt256.ofNat 1186] ++ callerRest input }

def baseGuardState (input : ByteArray) (i : Nat) (base : UInt256) : State :=
  { baseLoopState input i base with pc := UInt256.ofNat 173 }

def baseRest (input : ByteArray) (i : Nat) (base : UInt256) : List UInt256 :=
  [UInt256.ofNat (modulusValue input), UInt256.ofNat i, base,
    UInt256.ofNat (modulusValue input), UInt256.ofNat (baseSize input),
    UInt256.ofNat (exponentSize input), UInt256.ofNat (modulusSize input),
    UInt256.ofNat 96, UInt256.ofNat (expOffset input),
    UInt256.ofNat (modulusOffset input), UInt256.ofNat 1186] ++ callerRest input

def baseCallState (input : ByteArray) (i : Nat) (base : UInt256) : State :=
  Accessors.calldataByteEntry (baseLoopState input i base)
    (UInt256.ofNat (96 + i)) 0 183 (baseRest input i base)

def baseReturnedState (input : ByteArray) (i : Nat) (base : UInt256) : State :=
  Accessors.calldataByteReturned (baseLoopState input i base)
    (UInt256.ofNat (96 + i)) 183 (baseRest input i base)

def baseTailMidState (input : ByteArray) (i : Nat) (base : UInt256) : State :=
  { baseLoopState input i base with
    pc := UInt256.ofNat 191
    stack := baseStep input i base :: UInt256.ofNat i :: base ::
      UInt256.ofNat (modulusValue input) ::
      UInt256.ofNat (baseSize input) :: UInt256.ofNat (exponentSize input) ::
      UInt256.ofNat (modulusSize input) :: UInt256.ofNat 96 ::
      UInt256.ofNat (expOffset input) :: UInt256.ofNat (modulusOffset input) ::
      UInt256.ofNat 1186 :: callerRest input }

def baseTailSwappedState (input : ByteArray) (i : Nat) (base : UInt256) : State :=
  { baseLoopState input i base with
    pc := UInt256.ofNat 192
    stack := base :: UInt256.ofNat i :: baseStep input i base ::
      UInt256.ofNat (modulusValue input) ::
      UInt256.ofNat (baseSize input) :: UInt256.ofNat (exponentSize input) ::
      UInt256.ofNat (modulusSize input) :: UInt256.ofNat 96 ::
      UInt256.ofNat (expOffset input) :: UInt256.ofNat (modulusOffset input) ::
      UInt256.ofNat 1186 :: callerRest input }

def baseTailPoppedState (input : ByteArray) (i : Nat) (base : UInt256) : State :=
  { baseLoopState input i base with
    pc := UInt256.ofNat 193
    stack := UInt256.ofNat i :: baseStep input i base ::
      UInt256.ofNat (modulusValue input) ::
      UInt256.ofNat (baseSize input) :: UInt256.ofNat (exponentSize input) ::
      UInt256.ofNat (modulusSize input) :: UInt256.ofNat 96 ::
      UInt256.ofNat (expOffset input) :: UInt256.ofNat (modulusOffset input) ::
      UInt256.ofNat 1186 :: callerRest input }

def baseFinishDispatchState (input : ByteArray) (base : UInt256) : State :=
  { baseLoopState input (baseSize input) base with pc := UInt256.ofNat 199 }

def expLoopState (input : ByteArray) (i : Nat) (acc base : UInt256) : State :=
  { nonzeroState input with
    pc := UInt256.ofNat 206
    stack := [UInt256.ofNat i, acc, base, UInt256.ofNat (modulusValue input),
      UInt256.ofNat (baseSize input), UInt256.ofNat (exponentSize input),
      UInt256.ofNat (modulusSize input), UInt256.ofNat 96,
      UInt256.ofNat (expOffset input), UInt256.ofNat (modulusOffset input),
      UInt256.ofNat 1186] ++ callerRest input }

def expGuardState (input : ByteArray) (i : Nat) (acc base : UInt256) : State :=
  { expLoopState input i acc base with pc := UInt256.ofNat 213 }

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
    pc := UInt256.ofNat 221
    stack := [UInt256.ofNat j, byte, offset, UInt256.ofNat outer, acc, base,
      UInt256.ofNat (modulusValue input)] ++ bitTail input }

theorem bitFrame (input : ByteArray) (outer : Nat) (byte offset acc base : UInt256) :
    WordStep.Frame (bitLoopState input outer 0 byte offset acc base) :=
  ⟨rfl, rfl, rfl, deployAddress_not_precompile⟩

/-- The copies carry `base - 1` above the loop frame. -/
def bitUnrollState (input : ByteArray) (outer j : Nat) (byte offset : UInt256)
    (acc base : UInt256) : State :=
  WordStep.stW (bitLoopState input outer 0 byte offset acc base) (bitPC j)
    ([base - UInt256.ofNat 1, UInt256.ofNat (bitCounter j), byte, offset, UInt256.ofNat outer,
      acc, base, UInt256.ofNat (modulusValue input)] ++ bitTail input)

def bitPushState (input : ByteArray) (outer : Nat) (byte offset : UInt256)
    (acc base : UInt256) : State :=
  let s := bitLoopState input outer 0 byte offset acc base
  { s with pc := UInt256.ofNat 224, stack := UInt256.ofNat 2500 :: s.stack }

def bitHeadState (input : ByteArray) (outer : Nat) (byte offset : UInt256)
    (acc base : UInt256) : State :=
  WordStep.stW (bitLoopState input outer 0 byte offset acc base) 2500
    ([UInt256.ofNat 0, byte, offset, UInt256.ofNat outer, acc, base,
      UInt256.ofNat (modulusValue input)] ++ bitTail input)

theorem jump3695 : Decode.isValidJumpDest submissionBytecode 2500 = true :=
  Artifact.isValidJumpDest_index 1885 (by rfl)

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
    (hi : 88 ≤ i) (hii : i ≤ 102) :
    Artifact.submissionArtifact.instructionPC i =
      ([144,145,146,147,148,150,151,153,154,155,156,158,159,160,161] : List Nat)[i - 88]! := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  interval_cases i <;> rfl

@[simp] private theorem jump538 :
    Decode.isValidJumpDest submissionBytecode 162 = true :=
  Artifact.isValidJumpDest_index 103 (by rfl)

@[simp] theorem wordPCs (i : Nat)
    (hi : 103 ≤ i) (hii : i ≤ 132) :
    Artifact.submissionArtifact.instructionPC i =
      ([162,163,164,165,166,167,168,169,170,172,173,174,176,177,178,179,180,182,183,184,185,188,189,190,191,192,193,195,196,198] : List Nat)[i - 103]! := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  interval_cases i <;> rfl

@[simp] theorem jump582 :
    Decode.isValidJumpDest submissionBytecode 199 = true :=
  Artifact.isValidJumpDest_index 133 (by rfl)

@[simp] theorem jump562 :
    Decode.isValidJumpDest submissionBytecode 183 = true :=
  Artifact.isValidJumpDest_index 121 (by rfl)

@[simp] theorem jump4 :
    Decode.isValidJumpDest submissionBytecode 134 = true :=
  Artifact.isValidJumpDest_index 78 (by rfl)

@[simp] theorem jump541 :
    Decode.isValidJumpDest submissionBytecode 165 = true :=
  Artifact.isValidJumpDest_index 106 (by rfl)

@[simp] theorem baseFinishPCs (i : Nat)
    (hi : 133 ≤ i) (hii : i ≤ 138) :
    Artifact.submissionArtifact.instructionPC i =
      ([199,200,201,202,204,205] : List Nat)[i - 133]! := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  interval_cases i <;> rfl

@[simp] theorem expPCs (i : Nat)
    (hi : 139 ≤ i) (hii : i ≤ 162) :
    Artifact.submissionArtifact.instructionPC i =
      ([206,207,208,209,210,212,213,214,215,216,217,218,219,220,221,224,225,226,227,228,229,231,232,234] : List Nat)[i - 139]! := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  interval_cases i <;> rfl

@[simp] theorem jump669 :
    Decode.isValidJumpDest submissionBytecode 235 = true :=
  Artifact.isValidJumpDest_index 163 (by rfl)

@[simp] theorem jump655 :
    Decode.isValidJumpDest submissionBytecode 225 = true :=
  Artifact.isValidJumpDest_index 155 (by rfl)

@[simp] theorem jump589 :
    Decode.isValidJumpDest submissionBytecode 206 = true :=
  Artifact.isValidJumpDest_index 139 (by rfl)

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
  have h538 : (162 : UInt256).toNat = 162 := by decide
  have h538Word : (162 : UInt256) = UInt256.ofNat 162 := by decide
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
  have h550 : (176 : UInt256).toNat = 176 := by decide
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
  have h4 : (134 : UInt256).toNat = 134 := by decide
  have h4Word : (134 : UInt256) = UInt256.ofNat 134 := by decide
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
  have h582 : (199 : UInt256).toNat = 199 := by decide
  have h582Word : (199 : UInt256) = UInt256.ofNat 199 := by decide
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
