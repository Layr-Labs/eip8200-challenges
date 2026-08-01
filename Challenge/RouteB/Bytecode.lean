import EvmSemantics.EVM.Decode
set_option warningAsError true
/-!
# Raw bytecode, without a compiler provenance assumption

Route B starts from bytes supplied by a participant. `disassemble` splits such
a byte array at EVM instruction boundaries while preserving opcode immediates,
including truncated immediates at the end of code. `assemble` merely joins the
chunks again. The round-trip theorem therefore applies to every `ByteArray`,
including malformed code; it does not assume that a compiler produced it.

`RawInstr` retains the original opcode byte instead of replacing it with an
`Operation`. This matters for invalid opcodes and makes the round trip honest.
Proofs can inspect `RawInstr.opcodeOperation?` to classify a valid opcode and
use `Decode.decodeAt` when they need its full immediate-bearing semantics.
-/

namespace Challenge.RouteB

open EvmSemantics
open EvmSemantics.EVM

/-- One raw instruction chunk: its opcode byte and the immediate bytes present
in the artifact. A truncated final immediate is retained at its actual length. -/
structure RawInstr where
  opcode : UInt8
  immediate : List UInt8
  deriving DecidableEq, Repr

namespace RawInstr

/-- Reassemble one raw instruction exactly as it appeared. -/
def bytes (i : RawInstr) : List UInt8 := i.opcode :: i.immediate

@[simp] theorem bytes_ne_nil (i : RawInstr) : i.bytes ≠ [] := by
  simp [bytes]

/-- Decode the opcode byte through the pinned EVM semantics. Invalid opcode
bytes remain `none`; PUSH and EIP-8024 immediates are kept separately. -/
def opcodeOperation? (i : RawInstr) : Option Operation := Decode.opcodeOf i.opcode

end RawInstr

namespace Bytecode

/-- Immediate width of an opcode. PUSH1..PUSH32 carry 1..32 bytes. The Osaka
EIP-8024 opcodes DUPN/SWAPN/EXCHANGE carry one byte. The classification comes
from the pinned EVM decoder rather than a second opcode table. -/
def immediateWidth (opcode : UInt8) : Nat :=
  match Decode.opcodeOf opcode with
  | some (.Push p) => p.width.val
  | some (.DupN _) | some (.SwapN _) | some (.Exchange _) => 1
  | _ => 0

/-- Fuelled worker for `disassembleList`. One unit is enough for each input
byte because every emitted chunk consumes at least its opcode byte. -/
def disassembleList.go : Nat → List UInt8 → List RawInstr
  | 0, _ => []
  | _, [] => []
  | fuel + 1, opcode :: rest =>
      let width := immediateWidth opcode
      { opcode, immediate := rest.take width } ::
        disassembleList.go fuel (rest.drop width)

/-- Split a byte list into raw instruction chunks. Invalid opcodes occupy one
byte. A final immediate is truncated to the bytes actually present. -/
def disassembleList (bytes : List UInt8) : List RawInstr :=
  disassembleList.go bytes.length bytes

/-- Join raw instruction chunks into bytes. -/
def assembleList : List RawInstr → List UInt8
  | [] => []
  | i :: is => i.bytes ++ assembleList is

/-- Disassemble a submitted byte array. -/
def disassemble (code : ByteArray) : List RawInstr := disassembleList code.data.toList

/-- Assemble raw instruction chunks. -/
def assemble (is : List RawInstr) : ByteArray := ByteArray.mk (assembleList is).toArray

/-- Enough fuel makes the worker byte preserving. -/
private theorem assembleList_go (bytes : List UInt8) (fuel : Nat)
    (h : bytes.length ≤ fuel) :
    assembleList (disassembleList.go fuel bytes) = bytes := by
  induction fuel generalizing bytes with
  | zero =>
      have : bytes = [] := by simpa using h
      subst bytes
      rfl
  | succ fuel ih =>
      cases bytes with
      | nil => rfl
      | cons opcode rest =>
          simp only [disassembleList.go, assembleList, RawInstr.bytes]
          rw [ih]
          · simpa only [List.cons_append] using
              congrArg (List.cons opcode) (List.take_append_drop (immediateWidth opcode) rest)
          · calc
              (rest.drop (immediateWidth opcode)).length ≤ rest.length := by simp
              _ ≤ fuel := by simpa using h

/-- The raw disassembler loses no bytes, even for invalid opcodes and
truncated final immediates. -/
theorem assembleList_disassembleList (bytes : List UInt8) :
    assembleList (disassembleList bytes) = bytes := by
  exact assembleList_go bytes bytes.length (Nat.le_refl _)

/-- Verified raw-bytecode round trip: disassembling then assembling any
participant submission returns the exact submitted bytes. -/
theorem assemble_disassemble (code : ByteArray) : assemble (disassemble code) = code := by
  cases code with
  | mk data =>
      simp only [assemble, disassemble, assembleList_disassembleList,
        Array.toArray_toList]

/-- Regression case: a truncated PUSH2 remains one chunk and retains its one
available immediate byte. -/
example : disassembleList [0x61, 0xaa] =
    [{ opcode := 0x61, immediate := [0xaa] }] := by decide

/-- Regression case: invalid opcodes are preserved as one-byte chunks. -/
example : assembleList (disassembleList [0x0c, 0xfe]) = [0x0c, 0xfe] := by decide

end Bytecode
end Challenge.RouteB
