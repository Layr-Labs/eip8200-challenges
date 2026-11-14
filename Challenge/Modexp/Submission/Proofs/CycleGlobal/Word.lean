import Challenge.Modexp.Submission.Proofs.Prepared.StackArgs
import Challenge.Modexp.Submission.Proofs.CycleGlobal.Binding
import Challenge.Modexp.Submission.Proofs.Bytecode.PCFast
import Challenge.Modexp.Submission.Proofs.Algorithm
import Challenge.Modexp.Submission.Proofs.Bytecode.Accessors
import Challenge.Modexp.Submission.Proofs.CycleGlobal.Dispatch
import Challenge.EvmProof.Bytes
import Challenge.Modexp.Submission.Proofs.CycleGlobal.WordEnds
open CycleSubmission.SharedStackArgs
noncomputable section
set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 1000000
set_option maxErrors 1
namespace CycleSubmission.Global.Word
open Challenge.Modexp
open Challenge.Modexp.Submission.Proofs
open Challenge.Modexp.Submission.Proofs.Bytecode
open EvmSemantics
open EvmSemantics.EVM
attribute [local simp] Challenge.EvmProof.Word.ofNat_add_mod
  Challenge.EvmProof.Word.succ_ofNat_mod
def wfOp {op : Operation}
    (hopcode : Decode.opcodeOf (YulEvmCompiler.Instr.opByte op) = some op)
    (hplain : YulEvmCompiler.plainOp op)
    (havailable : op.availableInFork .Osaka = true) :
    Challenge.EvmProof.Stepper.WellFormed .Osaka (.op op) :=
  ⟨hopcode,hplain,havailable⟩
def opAt (index : Nat) (op : Operation)
    (hget : CycleSubmission.Artifact.instructions[index]? = some (.op op) := by rfl)
    (hopcode : Decode.opcodeOf (YulEvmCompiler.Instr.opByte op) = some op := by decide)
    (hplain : YulEvmCompiler.plainOp op := by trivial)
    (havailable : op.availableInFork .Osaka = true := by rfl) :
    Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka :=
  ⟨index,.op op,hget,wfOp hopcode hplain havailable⟩
def pushAt (index : Nat) (width : Fin 33) (value : UInt256)
    (hget : CycleSubmission.Artifact.instructions[index]? = some (.push width value) := by rfl)
    (hwf : Challenge.EvmProof.Stepper.WellFormed .Osaka (.push width value) := by decide) :
    Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka :=
  ⟨index,.push width value,hget,hwf⟩
def startPath :
    List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [opAt 70 .JUMPDEST,
   opAt 71 (.Dup dA5),
   opAt 72 .CALLDATALOAD,
   opAt 73 (.Dup dA3),
   pushAt 74 1 32,
   opAt 75 .SUB,
   pushAt 76 1 3,
   opAt 77 .SHL,
   opAt 78 .SHR,
   opAt 79 (.Dup dA0),
   pushAt 80 1 149,
   opAt 81 .JUMPI]
def zeroTailPath :
    List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [opAt 82 (.Dup dA3),
   pushAt 83 0 0,
   opAt 84 .RETURN]
def zeroModulusPath :
    List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  startPath++zeroTailPath
def startLoadPath := startPath.take 11
def startJumpPath := [opAt 81 .JUMPI]
def baseSetupPath :
    List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [opAt 85 .JUMPDEST,
   pushAt 86 0 0,
   pushAt 87 0 0]
def baseGuardPath :
    List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [opAt 88 .JUMPDEST,
   opAt 89 (.Dup dA3),
   opAt 90 (.Dup dA1),
   opAt 91 .EQ,
   pushAt 92 1 180,
   opAt 93 .JUMPI]
def baseCallPath :
    List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [opAt 94 (.Dup dA2),
   opAt 95 (.Dup dA1),
   opAt 96 (.Dup dA8),
   opAt 97 .ADD,
   opAt 98 .CALLDATALOAD,
   pushAt 99 0 0,
   opAt 100 .BYTE]
def baseTailPath :
    List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [opAt 101 (.Dup dA4),
   pushAt 102 2 256,
   pushAt 103 1 1,
   opAt 104 (.Swap sA5),
   opAt 105 .MULMOD,
   opAt 106 .ADDMOD,
   opAt 107 (.Swap sA1),
   opAt 108 .ADD,
   pushAt 109 1 152,
   opAt 110 .JUMP]
def baseFinishTailPath :
    List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [opAt 111 .JUMPDEST,
   opAt 112 .POP,
   opAt 113 (.Dup dA1),
   pushAt 114 0 0,
   opAt 115 .ISZERO,
   opAt 116 .LT,
   pushAt 117 0 0]
def expGuardPath :
    List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [opAt 118 .JUMPDEST,
   opAt 119 (.Dup dA5),
   opAt 120 (.Dup dA1),
   opAt 121 .EQ,
   pushAt 122 2 10418,
   opAt 123 .JUMPI]
def expLoadPath :
    List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [opAt 124 (.Dup dA0),
   opAt 125 (.Dup dA9),
   opAt 126 .ADD,
   opAt 127 (.Dup dA0),
   opAt 128 .CALLDATALOAD,
   pushAt 129 0 0,
   opAt 130 .BYTE,
   pushAt 131 0 0]
def bitJumpPath :
    List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [opAt 133 .JUMP]
def bitHeadPath :
    List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [opAt 8023 .JUMPDEST,
   pushAt 8024 1 1,
   opAt 8025 (.Dup dA6),
   opAt 8026 .SUB]
def bitExitPath :
    List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [opAt 8055 .POP,
   pushAt 8056 2 10408,
   opAt 8057 .JUMP]
def bitPC (j : Nat) : Nat :=
  match j with
  | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 => 10439
  | _ => 10474
def bitCounter (j : Nat) : Nat := if j < 8 then j else 8
def expOffset (input : ByteArray) : Nat := 96 + baseSize input
def modulusOffset (input : ByteArray) : Nat := expOffset input + exponentSize input
def modulusValue (input : ByteArray) : Nat :=
  Precompile.bytesToNatPadded input (modulusOffset input) (modulusSize input)
def callerRest (input : ByteArray) : List UInt256 :=
  [UInt256.ofNat (modulusOffset input),UInt256.ofNat (expOffset input),
    UInt256.ofNat (modulusSize input),UInt256.ofNat (exponentSize input),
    UInt256.ofNat (baseSize input)]
def nonzeroState (input : ByteArray) : State :=
  { Dispatch.wordEntryState input with
    pc := UInt256.ofNat 149
    stack := [UInt256.ofNat (modulusValue input),
      UInt256.ofNat (baseSize input),UInt256.ofNat (exponentSize input),
      UInt256.ofNat (modulusSize input),UInt256.ofNat 96,
      UInt256.ofNat (expOffset input),UInt256.ofNat (modulusOffset input),
      UInt256.ofNat 1186]++callerRest input }
def loadedState (input : ByteArray) : State :=
  { nonzeroState input with
    pc := UInt256.ofNat 145
    stack := (149 : UInt256)::UInt256.ofNat (modulusValue input) ::
      (nonzeroState input).stack }
def zeroDispatchState (input : ByteArray) : State :=
  { nonzeroState input with pc := UInt256.ofNat 146 }
def zeroModulusFinalState (input : ByteArray) : State :=
  { Dispatch.wordEntryState input with
    pc := UInt256.ofNat 148
    stack := [UInt256.ofNat 0,UInt256.ofNat (baseSize input),
      UInt256.ofNat (exponentSize input),UInt256.ofNat (modulusSize input),
      UInt256.ofNat 96,UInt256.ofNat (expOffset input),
      UInt256.ofNat (modulusOffset input),UInt256.ofNat 1186]++callerRest input
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
    pc := UInt256.ofNat 152
    stack := [UInt256.ofNat i,base,UInt256.ofNat (modulusValue input),
      UInt256.ofNat (baseSize input),UInt256.ofNat (exponentSize input),
      UInt256.ofNat (modulusSize input),UInt256.ofNat 96,
      UInt256.ofNat (expOffset input),UInt256.ofNat (modulusOffset input),
      UInt256.ofNat 1186]++callerRest input }
def baseGuardState (input : ByteArray) (i : Nat) (base : UInt256) : State :=
  { baseLoopState input i base with pc := UInt256.ofNat 159 }
def baseRest (input : ByteArray) (i : Nat) (base : UInt256) : List UInt256 :=
  [UInt256.ofNat (modulusValue input),UInt256.ofNat i,base,
    UInt256.ofNat (modulusValue input),UInt256.ofNat (baseSize input),
    UInt256.ofNat (exponentSize input),UInt256.ofNat (modulusSize input),
    UInt256.ofNat 96,UInt256.ofNat (expOffset input),
    UInt256.ofNat (modulusOffset input),UInt256.ofNat 1186]++callerRest input
def baseReturnedState (input : ByteArray) (i : Nat) (base : UInt256) : State :=
  Accessors.calldataByteReturned (baseLoopState input i base)
    (UInt256.ofNat (96 + i)) 166 (baseRest input i base)
def baseTailMidState (input : ByteArray) (i : Nat) (base : UInt256) : State :=
  { baseLoopState input i base with
    pc := UInt256.ofNat 172
    stack := baseStep input i base::UInt256.ofNat i::base ::
      UInt256.ofNat (modulusValue input) ::
      UInt256.ofNat (baseSize input)::UInt256.ofNat (exponentSize input) ::
      UInt256.ofNat (modulusSize input)::UInt256.ofNat 96 ::
      UInt256.ofNat (expOffset input)::UInt256.ofNat (modulusOffset input) ::
      UInt256.ofNat 1186::callerRest input }
def baseTailSwappedState (input : ByteArray) (i : Nat) (base : UInt256) : State :=
  { baseLoopState input i base with
    pc := UInt256.ofNat 173
    stack := base::UInt256.ofNat i::baseStep input i base ::
      UInt256.ofNat (modulusValue input) ::
      UInt256.ofNat (baseSize input)::UInt256.ofNat (exponentSize input) ::
      UInt256.ofNat (modulusSize input)::UInt256.ofNat 96 ::
      UInt256.ofNat (expOffset input)::UInt256.ofNat (modulusOffset input) ::
      UInt256.ofNat 1186::callerRest input }
def baseTailPoppedState (input : ByteArray) (i : Nat) (base : UInt256) : State :=
  { baseLoopState input i base with
    pc := UInt256.ofNat 174
    stack := UInt256.ofNat i::baseStep input i base ::
      UInt256.ofNat (modulusValue input) ::
      UInt256.ofNat (baseSize input)::UInt256.ofNat (exponentSize input) ::
      UInt256.ofNat (modulusSize input)::UInt256.ofNat 96 ::
      UInt256.ofNat (expOffset input)::UInt256.ofNat (modulusOffset input) ::
      UInt256.ofNat 1186::callerRest input }
def baseFinishDispatchState (input : ByteArray) (base : UInt256) : State :=
  { baseLoopState input (baseSize input) base with pc := UInt256.ofNat 180 }
def expLoopState (input : ByteArray) (i : Nat) (acc base : UInt256) : State :=
  { nonzeroState input with
    pc := UInt256.ofNat 187
    stack := [UInt256.ofNat i,acc,base,UInt256.ofNat (modulusValue input),
      UInt256.ofNat (baseSize input),UInt256.ofNat (exponentSize input),
      UInt256.ofNat (modulusSize input),UInt256.ofNat 96,
      UInt256.ofNat (expOffset input),UInt256.ofNat (modulusOffset input),
      UInt256.ofNat 1186]++callerRest input }
def expGuardState (input : ByteArray) (i : Nat) (acc base : UInt256) : State :=
  { expLoopState input i acc base with pc := UInt256.ofNat 195 }
def bitTail (input : ByteArray) : List UInt256 :=
  [UInt256.ofNat (baseSize input),UInt256.ofNat (exponentSize input),
    UInt256.ofNat (modulusSize input),UInt256.ofNat 96,
    UInt256.ofNat (expOffset input),UInt256.ofNat (modulusOffset input),
    UInt256.ofNat 1186]++callerRest input
def bitLoopState (input : ByteArray) (outer j : Nat) (byte offset : UInt256)
    (acc base : UInt256) : State :=
  { nonzeroState input with
    pc := UInt256.ofNat 203
    stack := [UInt256.ofNat j,byte,offset,UInt256.ofNat outer,acc,base,
      UInt256.ofNat (modulusValue input)]++bitTail input }
theorem bitFrame (input : ByteArray) (outer : Nat) (byte offset acc base : UInt256) :
    WordStep.Frame (bitLoopState input outer 0 byte offset acc base) :=
  ⟨rfl,rfl,rfl,deployAddress_not_precompile⟩
def bitUnrollState (input : ByteArray) (outer j : Nat) (byte offset : UInt256)
    (acc base : UInt256) : State :=
  WordStep.stW (bitLoopState input outer 0 byte offset acc base) (bitPC j)
    ([base - UInt256.ofNat 1,UInt256.ofNat (bitCounter j),byte,offset,UInt256.ofNat outer,
      acc,base,UInt256.ofNat (modulusValue input)]++bitTail input)
def bitPushState (input : ByteArray) (outer : Nat) (byte offset : UInt256)
    (acc base : UInt256) : State :=
  let s := bitLoopState input outer 0 byte offset acc base
  { s with pc := UInt256.ofNat 206,stack := UInt256.ofNat 10434::s.stack }
def bitHeadState (input : ByteArray) (outer : Nat) (byte offset : UInt256)
    (acc base : UInt256) : State :=
  WordStep.stW (bitLoopState input outer 0 byte offset acc base) 10434
    ([UInt256.ofNat 0,byte,offset,UInt256.ofNat outer,acc,base,
      UInt256.ofNat (modulusValue input)]++bitTail input)
theorem jump3695 : Decode.isValidJumpDest CycleSubmission.Artifact.bytecode 10434 = true :=
  CycleSubmission.Global.Binding.jumpDest 8023 (by rfl)
def gasSteps_bitEntry (input : ByteArray) (outer : Nat)
    (byte offset acc base : UInt256) :
    Challenge.EvmProof.GasSteps (bitLoopState input outer 0 byte offset acc base)
      (bitHeadState input outer byte offset acc base) :=
  WordEnds.gasSteps_bitEntry_sym (bitLoopState input outer 0 byte offset acc base)
    (bitTail input) (UInt256.ofNat 0) byte offset (UInt256.ofNat outer) acc base
    (UInt256.ofNat (modulusValue input))
    (bitFrame input outer byte offset acc base) (by simp [bitTail,callerRest])
    (by exact jump3695)
def gasSteps_bitHead (input : ByteArray) (outer : Nat)
    (byte offset acc base : UInt256) :
    Challenge.EvmProof.GasSteps (bitHeadState input outer byte offset acc base)
      (bitUnrollState input outer 0 byte offset acc base) :=
  WordEnds.gasSteps_bitHead_sym (bitLoopState input outer 0 byte offset acc base)
    (bitTail input) (UInt256.ofNat 0) byte offset (UInt256.ofNat outer) acc base
    (UInt256.ofNat (modulusValue input))
    (bitFrame input outer byte offset acc base) (by simp [bitTail,callerRest])
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
    rw [Challenge.EvmProof.Word.word_toNat_ofNat,Nat.mod_eq_of_lt hmodlt]
    omega
  have hmul : (p % modulus * 256) % modulus < modulus :=
    Nat.mod_lt _ hmodpos
  have hmul256 : (p % modulus * 256) % modulus < 2 ^ 256 :=
    hmul.trans hmodlt
  have hbyte256 :
      (YulSemantics.EVM.byteFrom input.toList (96 + i)).toNat < 2 ^ 256 :=
    (YulSemantics.EVM.byteFrom input.toList (96 + i)).toNat_lt.trans (by norm_num)
  unfold baseStep
  rw [hmodulus,hbyte]
  unfold UInt256.mulMod UInt256.addMod
  rw [if_neg hmword,if_neg hmword]
  simp only [Challenge.EvmProof.Word.word_toNat_ofNat]
  rw [Nat.mod_eq_of_lt hbase256,
    Nat.mod_eq_of_lt (by norm_num : 256 < 2 ^ 256),
    Nat.mod_eq_of_lt hmodlt,Nat.mod_eq_of_lt hmul256,
    Nat.mod_eq_of_lt hbyte256]
  apply congrArg UInt256.ofNat
  rw [Challenge.EvmProof.Bytes.bytesToNatPadded_succ]
  simp [p,Nat.add_mod,Nat.mul_mod]
theorem baseAfter_correct (input : ByteArray) (count : Nat)
    (hmodpos : 0 < modulusValue input)
    (hmodlt : modulusValue input < 2 ^ 256)
    (hbaseSize : baseSize input ≤ 1024)
    (hcount : count ≤ baseSize input) :
    baseAfter input count = UInt256.ofNat
      (Precompile.bytesToNatPadded input 96 count % modulusValue input) := by
  induction count with
  | zero =>
      rw [baseAfter,Challenge.EvmProof.Bytes.bytesToNatPadded_zero_width,
        Nat.zero_mod]
      decide
  | succ count ih =>
      rw [baseAfter,ih (by omega)]
      exact baseStep_spec input count (modulusValue input)
        rfl hmodpos hmodlt (by omega)
@[simp] theorem startPCs (i : Nat) (hi : 70 ≤ i) (hii : i ≤ 84) :
    CycleSubmission.Artifact.artifact.instructionPC i =
      ([131,132,133,134,135,137,138,140,141,142,143,145,146,147,148] : List Nat)[i - 70]! := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  interval_cases i <;> rfl
@[simp] private theorem jump538 :
    Decode.isValidJumpDest CycleSubmission.Artifact.bytecode 149 = true :=
  CycleSubmission.Global.Binding.jumpDest 85 (by rfl)
@[simp] theorem wordPCs (i : Nat) (hi : 85 ≤ i) (hii : i ≤ 110) :
    CycleSubmission.Artifact.artifact.instructionPC i =
      ([149,150,151,152,153,154,155,156,158,159,160,161,162,163,164,165,166,167,170,172,173,174,175,176,177,179] : List Nat)[i - 85]! := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  interval_cases i <;> rfl
@[simp] theorem jump582 :
    Decode.isValidJumpDest CycleSubmission.Artifact.bytecode 180 = true :=
  CycleSubmission.Global.Binding.jumpDest 111 (by rfl)
@[simp] theorem jump541 :
    Decode.isValidJumpDest CycleSubmission.Artifact.bytecode 152 = true :=
  CycleSubmission.Global.Binding.jumpDest 88 (by rfl)
@[simp] theorem baseFinishPCs (i : Nat) (hi : 111 ≤ i) (hii : i ≤ 117) :
    CycleSubmission.Artifact.artifact.instructionPC i =
      ([180,181,182,183,184,185,186] : List Nat)[i - 111]! := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  interval_cases i <;> rfl
@[simp] theorem expPCs (i : Nat) (hi : 118 ≤ i) (hii : i ≤ 133) :
    CycleSubmission.Artifact.artifact.instructionPC i =
      ([187,188,189,190,191,194,195,196,197,198,199,200,201,202,203,206] : List Nat)[i - 118]! := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  interval_cases i <;> rfl
@[simp] theorem expTailPCs (i : Nat) (hi : 8001 ≤ i) (hii : i ≤ 8008) :
    CycleSubmission.Artifact.artifact.instructionPC i =
      ([10408,10409,10410,10411,10412,10414,10415,10417] : List Nat)[i - 8001]! := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  interval_cases i <;> rfl
@[simp] theorem jump669 :
    Decode.isValidJumpDest CycleSubmission.Artifact.bytecode 10418 = true :=
  CycleSubmission.Global.Binding.jumpDest 8009 (by rfl)
@[simp] theorem jump655 :
    Decode.isValidJumpDest CycleSubmission.Artifact.bytecode 10408 = true :=
  CycleSubmission.Global.Binding.jumpDest 8001 (by rfl)
@[simp] theorem jump589 :
    Decode.isValidJumpDest CycleSubmission.Artifact.bytecode 187 = true :=
  CycleSubmission.Global.Binding.jumpDest 118 (by rfl)
set_option linter.unusedSimpArgs false in
theorem run_startLoad (input : ByteArray) (hvalid : ValidInput input)
    (hmsize : 0 < modulusSize input) (hword : modulusSize input ≤ 32) :
    Challenge.EvmProof.Stepper.runLocatedBlock startLoadPath
      (Dispatch.wordEntryState input) = some (loadedState input) := by
  rcases hvalid with ⟨_,hb,he,hm⟩
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
    simp only [modulusOffset,expOffset]
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
      show (32 : UInt256) = UInt256.ofNat 32 by decide,hsub,
      show (3 : UInt256) = UInt256.ofNat 3 by decide,hshift,hslice]
    rfl
  norm_num at hloaded
  simp (config := { maxSteps := 300000 })
    [startLoadPath,startPath,opAt,pushAt,
      Challenge.EvmProof.Stepper.runLocatedBlock,
      Challenge.EvmProof.Stepper.runLocated,Challenge.EvmProof.Stepper.runInstr,
      Dispatch.wordEntryState,Main.headerState,initialState,loadedState,
      nonzeroState,callerRest,
      expOffset,modulusOffset,startPCs,hsub,hshift,hslice,
      hmodOff,hshiftBound,UInt256.isTrue,
      Challenge.EvmProof.Word.word_toNat_ofNat,Nat.mod_eq_of_lt,
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
  have h538 : (149 : UInt256).toNat = 149 := by decide
  have h538Word : (149 : UInt256) = UInt256.ofNat 149 := by decide
  simp [startJumpPath,opAt,Challenge.EvmProof.Stepper.runLocatedBlock,
    Challenge.EvmProof.Stepper.runLocated,Challenge.EvmProof.Stepper.runInstr,
    loadedState,nonzeroState,callerRest,Dispatch.wordEntryState,
    Main.headerState,initialState,jump538,UInt256.isTrue,
    Challenge.EvmProof.Word.word_toNat_ofNat,hmodNat,hcondition,
    hmodulus,h538,h538Word,jump538]
  simp_all [hcondition,h538,h538Word,jump538]
set_option linter.unusedSimpArgs false in
theorem run_startJump_zero (input : ByteArray)
    (hmodulus : modulusValue input = 0) :
    Challenge.EvmProof.Stepper.runLocatedBlock startJumpPath
      (loadedState input) = some (zeroDispatchState input) := by
  simp [startJumpPath,opAt,Challenge.EvmProof.Stepper.runLocatedBlock,
    Challenge.EvmProof.Stepper.runLocated,Challenge.EvmProof.Stepper.runInstr,
    loadedState,zeroDispatchState,nonzeroState,callerRest,
    Dispatch.wordEntryState,Main.headerState,initialState,
    UInt256.isTrue,hmodulus,
    Challenge.EvmProof.Word.word_toNat_ofNat]
set_option linter.unusedSimpArgs false in
theorem run_zeroTail (input : ByteArray) (hvalid : ValidInput input)
    (hmodulus : modulusValue input = 0) :
    Challenge.EvmProof.Stepper.runLocatedBlock zeroTailPath
      (zeroDispatchState input) = some (zeroModulusFinalState input) := by
  rcases hvalid with ⟨_,_,_,hm⟩
  have hm' : modulusSize input < 2 ^ 256 := by omega
  have hmmod : modulusSize input % 2 ^ 256 = modulusSize input :=
    Nat.mod_eq_of_lt hm'
  have hmmodLiteral : modulusSize input %
      115792089237316195423570985008687907853269984665640564039457584007913129639936 =
        modulusSize input := by
    exact Nat.mod_eq_of_lt (by norm_num at hm'; exact hm')
  have h0 : (0 : UInt256).toNat = 0 := by decide
  simp [zeroTailPath,opAt,pushAt,
    Challenge.EvmProof.Stepper.runLocatedBlock,
    Challenge.EvmProof.Stepper.runLocated,Challenge.EvmProof.Stepper.runInstr,
    zeroDispatchState,zeroModulusFinalState,nonzeroState,callerRest,
    Dispatch.wordEntryState,Main.headerState,initialState,startPCs,
    Challenge.EvmProof.Word.word_toNat_ofNat,hmmod,hmmodLiteral,
    Nat.mod_eq_of_lt hm',h0,hmodulus]
  have hzeroRecord : ({ val := 0 } : UInt256).toNat = 0 := by decide
  simp_all [State.activeWordsAfterUInt256,MachineState.activeWordsAfter,hzeroRecord]
set_option linter.unusedSimpArgs false in
theorem run_baseSetup (input : ByteArray) :
    Challenge.EvmProof.Stepper.runLocatedBlock baseSetupPath
      (nonzeroState input) = some (baseLoopState input 0 0) := by
  have hzeroWord : UInt256.ofNat 0 = (0 : UInt256) := by decide
  simp (config := { maxSteps := 100000 })
    [baseSetupPath,opAt,pushAt,
      Challenge.EvmProof.Stepper.runLocatedBlock,
      Challenge.EvmProof.Stepper.runLocated,Challenge.EvmProof.Stepper.runInstr,
      nonzeroState,baseLoopState,callerRest,Dispatch.wordEntryState,Main.headerState,
      initialState,wordPCs,hzeroWord]
  decide
set_option linter.unusedSimpArgs false in
theorem run_baseGuard (input : ByteArray) (i : Nat) (base : UInt256)
    (hvalid : ValidInput input) (hi : i < baseSize input) :
    Challenge.EvmProof.Stepper.runLocatedBlock baseGuardPath
      (baseLoopState input i base) = some (baseGuardState input i base) := by
  rcases hvalid with ⟨_,hb,he,hm⟩
  have hi256 : i < 2 ^ 256 := by omega
  have hb256 : baseSize input < 2 ^ 256 := by omega
  have himod : i % 2 ^ 256 = i := Nat.mod_eq_of_lt hi256
  have hbmod : baseSize input % 2 ^ 256 = baseSize input :=
    Nat.mod_eq_of_lt hb256
  have hilt : i % 2 ^ 256 < baseSize input % 2 ^ 256 := by
    rw [himod,hbmod]
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
  have hne : i % 2 ^ 256 ≠ baseSize input % 2 ^ 256 := by
    rw [himod,hbmod]
    omega
  have hneLiteral :
      i % 115792089237316195423570985008687907853269984665640564039457584007913129639936 ≠
      baseSize input % 115792089237316195423570985008687907853269984665640564039457584007913129639936 := hne
  have h550 : (177 : UInt256).toNat = 177 := by decide
  simp (config := { maxSteps := 150000 })
    [baseGuardPath,opAt,pushAt,
      Challenge.EvmProof.Stepper.runLocatedBlock,
      Challenge.EvmProof.Stepper.runLocated,Challenge.EvmProof.Stepper.runInstr,
      baseLoopState,baseGuardState,nonzeroState,callerRest,
      Dispatch.wordEntryState,Main.headerState,initialState,wordPCs,
      UInt256.isTrue,UInt256.eq,Challenge.EvmProof.Word.word_toNat_ofNat,
      hi,hi256,hb256,himod,hbmod,hilt,hisZero,hcond,hcondLiteral,
      hne,hneLiteral,h550]
set_option linter.unusedSimpArgs false in
theorem run_baseCall (input : ByteArray) (i : Nat) (base : UInt256)
    (hvalid : ValidInput input) (hi : i < baseSize input) :
    Challenge.EvmProof.Stepper.runLocatedBlock baseCallPath
      (baseGuardState input i base) = some (baseReturnedState input i base) := by
  rcases hvalid with ⟨_,hb,he,hm⟩
  have hoff : 96 + i < 2 ^ 256 := by omega
  have hadd := Challenge.EvmProof.Word.ofNat_add_ofNat
    (a := i) (b := 96) (by omega : i + 96 < 2 ^ 256)
  have hzeroWord : ({ val := 0 } : UInt256) = 0 := by decide
  have hzeroNat : UInt256.ofNat 0 = (0 : UInt256) := by decide
  have h169 : (166 : UInt256) = UInt256.ofNat 166 := by decide
  simp (config := { maxSteps := 150000 })
    [baseCallPath,opAt,pushAt,
      Challenge.EvmProof.Stepper.runLocatedBlock,
      Challenge.EvmProof.Stepper.runLocated,Challenge.EvmProof.Stepper.runInstr,
      baseGuardState,baseReturnedState,baseRest,baseLoopState,
      Accessors.calldataByteReturned,Accessors.calldataByteValue,
      nonzeroState,callerRest,List.exchange,
      Dispatch.wordEntryState,Main.headerState,initialState,wordPCs,
      Challenge.EvmProof.Word.word_toNat_ofNat,hzeroWord,hzeroNat,h169,
      hoff,hadd]
set_option linter.unusedSimpArgs false in
theorem run_baseFinishGuard (input : ByteArray) (base : UInt256)
    (hvalid : ValidInput input) :
    Challenge.EvmProof.Stepper.runLocatedBlock baseGuardPath
      (baseLoopState input (baseSize input) base) =
        some (baseFinishDispatchState input base) := by
  rcases hvalid with ⟨_,hb,he,hm⟩
  have hb256 : baseSize input < 2 ^ 256 := by omega
  have hbmod : baseSize input % 2 ^ 256 = baseSize input :=
    Nat.mod_eq_of_lt hb256
  have h582 : (180 : UInt256).toNat = 180 := by decide
  have h582Word : (180 : UInt256) = UInt256.ofNat 180 := by decide
  have hzeroFalse : ¬(UInt256.ofNat 0).isZero.toNat = 0 := by decide
  simp (config := { maxSteps := 150000 })
    [baseGuardPath,opAt,pushAt,
      Challenge.EvmProof.Stepper.runLocatedBlock,
      Challenge.EvmProof.Stepper.runLocated,Challenge.EvmProof.Stepper.runInstr,
      baseLoopState,baseFinishDispatchState,nonzeroState,callerRest,
      Dispatch.wordEntryState,Main.headerState,initialState,wordPCs,
      UInt256.isTrue,UInt256.eq,Challenge.EvmProof.Word.word_toNat_ofNat,
      hb256,hbmod,hzeroFalse,h582,h582Word,jump582]
@[simp] theorem zeroModulusFinalState_isDone (input : ByteArray) :
    (zeroModulusFinalState input).isDone = true := by
  rfl
theorem zeroModulusFinalState_result (input : ByteArray)
    (hmsize : 0 < modulusSize input) (hmodulus : modulusValue input = 0) :
    (zeroModulusFinalState input).toResult = .returned (spec input) := by
  rw [show (zeroModulusFinalState input).toResult =
      .returned (Precompile.natToBytes 0 (modulusSize input)) by
    simp [zeroModulusFinalState,Algorithm.zeroBytes]]
  have hmodulus' :
      Precompile.bytesToNatPadded input
        (96 + baseSize input + exponentSize input) (modulusSize input) = 0 := by
    simpa [modulusValue,modulusOffset,expOffset,Nat.add_assoc] using hmodulus
  simp [spec,Nat.ne_of_gt hmsize,hmodulus',Precompile.modPow]
end CycleSubmission.Global.Word
