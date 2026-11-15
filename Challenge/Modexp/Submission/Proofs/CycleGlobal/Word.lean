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
  [opAt 67 .JUMPDEST,
   opAt 68 (.Dup ⟨5,by decide⟩),
   opAt 69 .CALLDATALOAD,
   opAt 70 (.Dup ⟨3,by decide⟩),
   pushAt 71 1 32,
   opAt 72 .SUB,
   pushAt 73 1 3,
   opAt 74 .SHL,
   opAt 75 .SHR,
   opAt 76 (.Dup ⟨0,by decide⟩),
   pushAt 77 1 114,
   opAt 78 .JUMPI]
def zeroTailPath :
    List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [opAt 79 (.Dup ⟨3,by decide⟩),
   pushAt 80 0 0,
   opAt 81 .RETURN]
def zeroModulusPath :
    List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  startPath++zeroTailPath
def startLoadPath := startPath.take 11
def startJumpPath := [opAt 78 .JUMPI]
def baseSetupPath :
    List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [opAt 82 .JUMPDEST,
   pushAt 83 0 0,
   pushAt 84 0 0]
def baseGuardPath :
    List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [opAt 85 .JUMPDEST,
   opAt 86 (.Dup ⟨3,by decide⟩),
   opAt 87 (.Dup ⟨1,by decide⟩),
   opAt 88 .EQ,
   pushAt 89 1 145,
   opAt 90 .JUMPI]
def baseCallPath :
    List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [opAt 91 (.Dup ⟨2,by decide⟩),
   opAt 92 (.Dup ⟨1,by decide⟩),
   opAt 93 (.Dup ⟨8,by decide⟩),
   opAt 94 .ADD,
   opAt 95 .CALLDATALOAD,
   pushAt 96 0 0,
   opAt 97 .BYTE]
def baseTailPath :
    List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [opAt 98 (.Dup ⟨4,by decide⟩),
   pushAt 99 2 256,
   pushAt 100 1 1,
   opAt 101 (.Swap ⟨5,by decide⟩),
   opAt 102 .MULMOD,
   opAt 103 .ADDMOD,
   opAt 104 (.Swap ⟨1,by decide⟩),
   opAt 105 .ADD,
   pushAt 106 1 117,
   opAt 107 .JUMP]
def baseFinishTailPath :
    List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [opAt 108 .JUMPDEST,
   opAt 109 .POP,
   opAt 110 (.Dup ⟨1,by decide⟩),
   pushAt 111 0 0,
   opAt 112 .ISZERO,
   opAt 113 .LT,
   pushAt 114 0 0]
def expGuardPath :
    List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [opAt 115 .JUMPDEST,
   opAt 116 (.Dup ⟨5,by decide⟩),
   opAt 117 (.Dup ⟨1,by decide⟩),
   opAt 118 .EQ,
   pushAt 119 2 10693,
   opAt 120 .JUMPI]
def expLoadPath :
    List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [opAt 121 (.Dup ⟨0,by decide⟩),
   opAt 122 (.Dup ⟨9,by decide⟩),
   opAt 123 .ADD,
   opAt 124 (.Dup ⟨0,by decide⟩),
   opAt 125 .CALLDATALOAD,
   pushAt 126 0 0,
   opAt 127 .BYTE,
   pushAt 128 0 0]
def bitJumpPath :
    List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [opAt 130 .JUMP]
def bitHeadPath :
    List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [opAt 8087 .JUMPDEST,
   pushAt 8088 1 1,
   opAt 8089 (.Dup ⟨6,by decide⟩),
   opAt 8090 .SUB]
def bitExitPath :
    List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [opAt 8119 .POP,
   pushAt 8120 2 10683,
   opAt 8121 .JUMP]
def bitPC (j : Nat) : Nat :=
  match j with
  | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 => 10714
  | _ => 10749
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
    pc := UInt256.ofNat 114
    stack := [UInt256.ofNat (modulusValue input),
      UInt256.ofNat (baseSize input),UInt256.ofNat (exponentSize input),
      UInt256.ofNat (modulusSize input),UInt256.ofNat 96,
      UInt256.ofNat (expOffset input),UInt256.ofNat (modulusOffset input),
      UInt256.ofNat 1186]++callerRest input }
def loadedState (input : ByteArray) : State :=
  { nonzeroState input with
    pc := UInt256.ofNat 110
    stack := (114 : UInt256)::UInt256.ofNat (modulusValue input) ::
      (nonzeroState input).stack }
def zeroDispatchState (input : ByteArray) : State :=
  { nonzeroState input with pc := UInt256.ofNat 111 }
def zeroModulusFinalState (input : ByteArray) : State :=
  { Dispatch.wordEntryState input with
    pc := UInt256.ofNat 113
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
    pc := UInt256.ofNat 117
    stack := [UInt256.ofNat i,base,UInt256.ofNat (modulusValue input),
      UInt256.ofNat (baseSize input),UInt256.ofNat (exponentSize input),
      UInt256.ofNat (modulusSize input),UInt256.ofNat 96,
      UInt256.ofNat (expOffset input),UInt256.ofNat (modulusOffset input),
      UInt256.ofNat 1186]++callerRest input }
def baseGuardState (input : ByteArray) (i : Nat) (base : UInt256) : State :=
  { baseLoopState input i base with pc := UInt256.ofNat 124 }
def baseRest (input : ByteArray) (i : Nat) (base : UInt256) : List UInt256 :=
  [UInt256.ofNat (modulusValue input),UInt256.ofNat i,base,
    UInt256.ofNat (modulusValue input),UInt256.ofNat (baseSize input),
    UInt256.ofNat (exponentSize input),UInt256.ofNat (modulusSize input),
    UInt256.ofNat 96,UInt256.ofNat (expOffset input),
    UInt256.ofNat (modulusOffset input),UInt256.ofNat 1186]++callerRest input
def baseReturnedState (input : ByteArray) (i : Nat) (base : UInt256) : State :=
  Accessors.calldataByteReturned (baseLoopState input i base)
    (UInt256.ofNat (96 + i)) 131 (baseRest input i base)
def baseTailMidState (input : ByteArray) (i : Nat) (base : UInt256) : State :=
  { baseLoopState input i base with
    pc := UInt256.ofNat 137
    stack := baseStep input i base::UInt256.ofNat i::base ::
      UInt256.ofNat (modulusValue input) ::
      UInt256.ofNat (baseSize input)::UInt256.ofNat (exponentSize input) ::
      UInt256.ofNat (modulusSize input)::UInt256.ofNat 96 ::
      UInt256.ofNat (expOffset input)::UInt256.ofNat (modulusOffset input) ::
      UInt256.ofNat 1186::callerRest input }
def baseTailSwappedState (input : ByteArray) (i : Nat) (base : UInt256) : State :=
  { baseLoopState input i base with
    pc := UInt256.ofNat 138
    stack := base::UInt256.ofNat i::baseStep input i base ::
      UInt256.ofNat (modulusValue input) ::
      UInt256.ofNat (baseSize input)::UInt256.ofNat (exponentSize input) ::
      UInt256.ofNat (modulusSize input)::UInt256.ofNat 96 ::
      UInt256.ofNat (expOffset input)::UInt256.ofNat (modulusOffset input) ::
      UInt256.ofNat 1186::callerRest input }
def baseTailPoppedState (input : ByteArray) (i : Nat) (base : UInt256) : State :=
  { baseLoopState input i base with
    pc := UInt256.ofNat 139
    stack := UInt256.ofNat i::baseStep input i base ::
      UInt256.ofNat (modulusValue input) ::
      UInt256.ofNat (baseSize input)::UInt256.ofNat (exponentSize input) ::
      UInt256.ofNat (modulusSize input)::UInt256.ofNat 96 ::
      UInt256.ofNat (expOffset input)::UInt256.ofNat (modulusOffset input) ::
      UInt256.ofNat 1186::callerRest input }
def baseFinishDispatchState (input : ByteArray) (base : UInt256) : State :=
  { baseLoopState input (baseSize input) base with pc := UInt256.ofNat 145 }
def expLoopState (input : ByteArray) (i : Nat) (acc base : UInt256) : State :=
  { nonzeroState input with
    pc := UInt256.ofNat 152
    stack := [UInt256.ofNat i,acc,base,UInt256.ofNat (modulusValue input),
      UInt256.ofNat (baseSize input),UInt256.ofNat (exponentSize input),
      UInt256.ofNat (modulusSize input),UInt256.ofNat 96,
      UInt256.ofNat (expOffset input),UInt256.ofNat (modulusOffset input),
      UInt256.ofNat 1186]++callerRest input }
def expGuardState (input : ByteArray) (i : Nat) (acc base : UInt256) : State :=
  { expLoopState input i acc base with pc := UInt256.ofNat 160 }
def bitTail (input : ByteArray) : List UInt256 :=
  [UInt256.ofNat (baseSize input),UInt256.ofNat (exponentSize input),
    UInt256.ofNat (modulusSize input),UInt256.ofNat 96,
    UInt256.ofNat (expOffset input),UInt256.ofNat (modulusOffset input),
    UInt256.ofNat 1186]++callerRest input
def bitLoopState (input : ByteArray) (outer j : Nat) (byte offset : UInt256)
    (acc base : UInt256) : State :=
  { nonzeroState input with
    pc := UInt256.ofNat 168
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
  { s with pc := UInt256.ofNat 171,stack := UInt256.ofNat 10709::s.stack }
def bitHeadState (input : ByteArray) (outer : Nat) (byte offset : UInt256)
    (acc base : UInt256) : State :=
  WordStep.stW (bitLoopState input outer 0 byte offset acc base) 10709
    ([UInt256.ofNat 0,byte,offset,UInt256.ofNat outer,acc,base,
      UInt256.ofNat (modulusValue input)]++bitTail input)
theorem jump3695 : Decode.isValidJumpDest CycleSubmission.Artifact.bytecode 10709 = true :=
  CycleSubmission.Global.Binding.jumpDest 8087 (by rfl)
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
@[simp] theorem startPCs (i : Nat) (hi : 67 ≤ i) (hii : i ≤ 81) :
    CycleSubmission.Artifact.artifact.instructionPC i =
      ([96,97,98,99,100,102,103,105,106,107,108,110,111,112,113] : List Nat)[i - 67]! := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  interval_cases i <;> rfl
@[simp] private theorem jump538 :
    Decode.isValidJumpDest CycleSubmission.Artifact.bytecode 114 = true :=
  CycleSubmission.Global.Binding.jumpDest 82 (by rfl)
@[simp] theorem wordPCs (i : Nat) (hi : 82 ≤ i) (hii : i ≤ 107) :
    CycleSubmission.Artifact.artifact.instructionPC i =
      ([114,115,116,117,118,119,120,121,123,124,125,126,127,128,129,130,131,132,135,137,138,139,140,141,142,144] : List Nat)[i - 82]! := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  interval_cases i <;> rfl
@[simp] theorem jump582 :
    Decode.isValidJumpDest CycleSubmission.Artifact.bytecode 145 = true :=
  CycleSubmission.Global.Binding.jumpDest 108 (by rfl)
@[simp] theorem jump541 :
    Decode.isValidJumpDest CycleSubmission.Artifact.bytecode 117 = true :=
  CycleSubmission.Global.Binding.jumpDest 85 (by rfl)
@[simp] theorem baseFinishPCs (i : Nat) (hi : 108 ≤ i) (hii : i ≤ 114) :
    CycleSubmission.Artifact.artifact.instructionPC i =
      ([145,146,147,148,149,150,151] : List Nat)[i - 108]! := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  interval_cases i <;> rfl
@[simp] theorem expPCs (i : Nat) (hi : 115 ≤ i) (hii : i ≤ 130) :
    CycleSubmission.Artifact.artifact.instructionPC i =
      ([152,153,154,155,156,159,160,161,162,163,164,165,166,167,168,171] : List Nat)[i - 115]! := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  interval_cases i <;> rfl
@[simp] theorem expTailPCs (i : Nat) (hi : 8065 ≤ i) (hii : i ≤ 8072) :
    CycleSubmission.Artifact.artifact.instructionPC i =
      ([10683,10684,10685,10686,10687,10689,10690,10692] : List Nat)[i - 8065]! := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  interval_cases i <;> rfl
@[simp] theorem jump669 :
    Decode.isValidJumpDest CycleSubmission.Artifact.bytecode 10693 = true :=
  CycleSubmission.Global.Binding.jumpDest 8073 (by rfl)
@[simp] theorem jump655 :
    Decode.isValidJumpDest CycleSubmission.Artifact.bytecode 10683 = true :=
  CycleSubmission.Global.Binding.jumpDest 8065 (by rfl)
@[simp] theorem jump589 :
    Decode.isValidJumpDest CycleSubmission.Artifact.bytecode 152 = true :=
  CycleSubmission.Global.Binding.jumpDest 115 (by rfl)
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
  have h538 : (114 : UInt256).toNat = 114 := by decide
  have h538Word : (114 : UInt256) = UInt256.ofNat 114 := by decide
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
  have h169 : (131 : UInt256) = UInt256.ofNat 131 := by decide
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
  have h582 : (145 : UInt256).toNat = 145 := by decide
  have h582Word : (145 : UInt256) = UInt256.ofNat 145 := by decide
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
