import Challenge.Ripemd160.Submission.Proofs.Bytecode.StackRoundTrace
import Challenge.EvmProof.Meter
import YulEvmCompiler.Instr

set_option warningAsError true
set_option maxRecDepth 30000
set_option maxHeartbeats 4000000

/-!
# Dense two-word schedule templates

The dense helper keeps both packed message words on the stack only until the
two endian stages finish.  It then stores one packed word at each dense
address.  The reachable helper has 52 instructions including its return
`JUMP`. The artifact window has 52 instructions and 199 bytes, with no
padding after the return.
-/

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.DenseScheduleTemplate

open EvmSemantics
open EvmSemantics.EVM
open YulEvmCompiler
open Challenge.EvmProof

def op (operation : Operation) : Instr := .op operation

def push1 (value : UInt256) : Instr :=
  .push ⟨1, by decide⟩ value

def push2 (value : UInt256) : Instr :=
  .push ⟨2, by decide⟩ value

def push3 (value : UInt256) : Instr :=
  .push ⟨3, by decide⟩ value

def push32 (value : UInt256) : Instr :=
  .push ⟨32, by decide⟩ value

def dup1 : Instr := .op (.Dup ⟨0, by decide⟩)

def swap1 : Instr := .op (.Swap ⟨0, by decide⟩)

def mask8 : UInt256 :=
  UInt256.ofNat 0x00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff

def mask16 : UInt256 :=
  UInt256.ofNat 0x0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff

def denseStoreAddress (half : Nat) : Nat := 672 + 32 * half

def denseStoreOffset (half : Nat) : Nat :=
  (UInt256.ofNat (denseStoreAddress half)).toNat

def initialTemplate : List Instr :=
  [ op .JUMPDEST, dup1, op .MLOAD, swap1, push1 (UInt256.ofNat 32), op .ADD,
    op .MLOAD ]

def endianFactor (shift : Nat) : UInt256 :=
  UInt256.ofNat (2 ^ shift + 1)

def endianFactorPush (shift : Nat) : Instr :=
  if shift = 8 then push2 (endianFactor shift) else push3 (endianFactor shift)

/-- If `t = ((value >>> shift) XOR value) AND mask`, the masks used below
put `t` and `t <<< shift` in disjoint lanes.  Multiplication by
`1 + 2^shift` therefore combines the two copies without a carry. -/
def endianStage (shift : Nat) (mask : UInt256) : List Instr :=
  [ dup1, dup1, push1 (UInt256.ofNat shift), op .SHR, op .XOR,
    push32 mask, op .AND, endianFactorPush shift, op .MUL, op .XOR ]

def endianStage8 : List Instr := endianStage 8 mask8

def endianStage16 : List Instr := endianStage 16 mask16

def denseHalfTemplate (half : Nat) : List Instr :=
  endianStage8 ++ endianStage16 ++
    [ push2 (UInt256.ofNat (denseStoreAddress half)), op .MSTORE ]

def denseBeforeJumpTemplate : List Instr :=
  initialTemplate ++ denseHalfTemplate 1 ++ denseHalfTemplate 0

def finalJumpTemplate : List Instr := [op .JUMP]

def denseFullTemplate : List Instr :=
  denseBeforeJumpTemplate ++ finalJumpTemplate

/-- No padding remains after the helper return. -/
def paddingTemplate : List Instr := []

def denseWindowTemplate : List Instr := denseFullTemplate ++ paddingTemplate

@[simp] theorem initialTemplate_length : initialTemplate.length = 7 := by
  rfl

@[simp] theorem endianStage_length (shift : Nat) (mask : UInt256) :
    (endianStage shift mask).length = 10 := by
  rfl

@[simp] theorem denseHalfTemplate_length (half : Nat) :
    (denseHalfTemplate half).length = 22 := by
  rfl

@[simp] theorem denseBeforeJumpTemplate_length :
    denseBeforeJumpTemplate.length = 51 := by
  rfl

@[simp] theorem denseFullTemplate_length :
    denseFullTemplate.length = 52 := by
  rfl

@[simp] theorem paddingTemplate_length : paddingTemplate.length = 0 := by rfl

@[simp] theorem denseWindowTemplate_length : denseWindowTemplate.length = 52 := by rfl

theorem assembleBytes_length (instructions : List Instr) :
    (assembleBytes instructions).length =
      (instructions.map Instr.size).sum := by
  induction instructions with
  | nil => rfl
  | cons instruction rest ih =>
      simp only [assembleBytes_cons, List.length_append, List.map_cons,
        List.sum_cons]
      change instruction.bytes.length + (assembleBytes rest).length =
        instruction.bytes.length + (rest.map Instr.size).sum
      rw [ih]

theorem denseHalfTemplate_byteLength (half : Nat) :
    (assembleBytes (denseHalfTemplate half)).length = 95 := by
  rw [assembleBytes_length]
  simp [denseHalfTemplate, endianStage8, endianStage16, endianStage,
    endianFactorPush, endianFactor, op, push1, push2, push3, push32, dup1,
    denseStoreAddress]

theorem denseBeforeJumpTemplate_byteLength :
    (assembleBytes denseBeforeJumpTemplate).length = 198 := by
  rw [denseBeforeJumpTemplate, assembleBytes_append, List.length_append,
    assembleBytes_length]
  simp [denseHalfTemplate, initialTemplate, endianStage8, endianStage16,
    endianStage, endianFactorPush, endianFactor, op, push1, push2, push3,
    push32, dup1, swap1, denseStoreAddress]

theorem denseFullTemplate_byteLength :
    (assembleBytes denseFullTemplate).length = 199 := by
  rw [denseFullTemplate, assembleBytes_append, List.length_append,
    denseBeforeJumpTemplate_byteLength]
  rfl

theorem paddingTemplate_byteLength :
    (assembleBytes paddingTemplate).length = 0 := by
  rfl

theorem denseWindowTemplate_byteLength :
    (assembleBytes denseWindowTemplate).length = 199 := by
  rw [denseWindowTemplate, assembleBytes_append, List.length_append,
    denseFullTemplate_byteLength, paddingTemplate_byteLength]

def staticGas (instructions : List Instr) : Nat :=
  (instructions.map
    (Challenge.EvmProof.Meter.instrStaticCost .Osaka)).sum

theorem denseFullTemplate_staticGas :
    staticGas denseFullTemplate = 167 := by
  norm_num [staticGas, denseFullTemplate, denseBeforeJumpTemplate,
    denseHalfTemplate, initialTemplate, endianStage8, endianStage16,
    endianStage, endianFactorPush, endianFactor, op, push1, push2, push3,
    push32, dup1, swap1,
    Challenge.EvmProof.Meter.instrStaticCost, Gas.baseCost]
  rfl

def packedStage (value : UInt256) (shift : Nat) (mask : UInt256) : UInt256 :=
  UInt256.lor
    (UInt256.shiftLeft (UInt256.land value mask) (UInt256.ofNat shift))
    (UInt256.land
      (UInt256.shiftRight value (UInt256.ofNat shift)) mask)

def endianDelta (value : UInt256) (shift : Nat) (mask : UInt256) : UInt256 :=
  UInt256.land
    (UInt256.xor (UInt256.shiftRight value (UInt256.ofNat shift)) value) mask

def multipliedStage (value : UInt256) (shift : Nat) (mask : UInt256) : UInt256 :=
  UInt256.xor
    (UInt256.mul (endianFactor shift) (endianDelta value shift mask)) value

def packedWord (value : UInt256) : UInt256 :=
  packedStage (packedStage value 8 mask8) 16 mask16

def inputWord0 (s : State) (messageOffset : UInt256) : UInt256 :=
  MachineState.readWord s.memory messageOffset.toNat

def inputWord1 (s : State) (messageOffset : UInt256) : UInt256 :=
  MachineState.readWord s.memory
    (messageOffset + UInt256.ofNat 32).toNat

def packedInput0 (s : State) (messageOffset : UInt256) : UInt256 :=
  packedWord (inputWord0 s messageOffset)

def packedInput1 (s : State) (messageOffset : UInt256) : UInt256 :=
  packedWord (inputWord1 s messageOffset)

def wordBytes (value : UInt256) : ByteArray :=
  Data.Bytes.natToBytesPadded value.toNat 32

def writeDenseWord (memory : ByteArray) (address : Nat)
    (value : UInt256) : ByteArray :=
  MachineState.writeBytes memory (wordBytes value) address

def denseExpectedMemory (s : State) (messageOffset : UInt256) : ByteArray :=
  writeDenseWord
    (writeDenseWord s.memory (denseStoreOffset 1)
      (packedInput1 s messageOffset))
    (denseStoreOffset 0) (packedInput0 s messageOffset)

def activeAfterWord (current : UInt256) (offset : UInt256) : UInt256 :=
  UInt256.ofNat
    (MachineState.activeWordsAfter current.toNat offset.toNat 32)

def loadedActiveWords (s : State) (messageOffset : UInt256) : UInt256 :=
  let a0 := activeAfterWord s.activeWords messageOffset
  activeAfterWord a0 (messageOffset + UInt256.ofNat 32)

def denseStoreAddresses : List Nat := [denseStoreOffset 0, denseStoreOffset 1]

def denseStoreActiveWords (current : UInt256) (addresses : List Nat) : UInt256 :=
  addresses.foldl
    (fun current address =>
      UInt256.ofNat (MachineState.activeWordsAfter current.toNat address 32)) current

def denseExpectedActiveWords (s : State) (messageOffset : UInt256) : UInt256 :=
  denseStoreActiveWords
    (denseStoreActiveWords (loadedActiveWords s messageOffset)
      [denseStoreOffset 1]) [denseStoreOffset 0]

def scheduleEntry (s : State) (startPC messageOffset returnPC : UInt256)
    (rest : List UInt256) : State :=
  { s with pc := startPC, stack := [messageOffset, returnPC] ++ rest }

def afterInitial (s : State) (startPC messageOffset returnPC : UInt256)
    (rest : List UInt256) : State :=
  { s with
    pc := Challenge.Ripemd160.Submission.Proofs.Bytecode.StackRoundTrace.pcAfter
      startPC initialTemplate
    stack := [inputWord1 s messageOffset, inputWord0 s messageOffset, returnPC] ++ rest
    activeWords := loadedActiveWords s messageOffset }

def afterDenseHalf (s : State) (startPC : UInt256) (half : Nat)
    (value : UInt256) (rest : List UInt256) : State :=
  { s with
    pc := Challenge.Ripemd160.Submission.Proofs.Bytecode.StackRoundTrace.pcAfter
      startPC (denseHalfTemplate half)
    stack := rest
    memory := writeDenseWord s.memory (denseStoreOffset half) value
    activeWords := denseStoreActiveWords s.activeWords
      [denseStoreOffset half] }

def denseExpectedState (s : State) (startPC messageOffset returnPC : UInt256)
    (rest : List UInt256) : State :=
  { s with
    pc := Challenge.Ripemd160.Submission.Proofs.Bytecode.StackRoundTrace.pcAfter
      (Challenge.Ripemd160.Submission.Proofs.Bytecode.StackRoundTrace.pcAfter
        (Challenge.Ripemd160.Submission.Proofs.Bytecode.StackRoundTrace.pcAfter
          startPC initialTemplate) (denseHalfTemplate 1))
        (denseHalfTemplate 0)
    stack := [returnPC] ++ rest
    memory := denseExpectedMemory s messageOffset
    activeWords := denseExpectedActiveWords s messageOffset }

def denseStaticGas : Nat := 171

end Challenge.Ripemd160.Submission.Proofs.Bytecode.DenseScheduleTemplate
