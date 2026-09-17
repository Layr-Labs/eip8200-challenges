import EvmSemantics.EVM.Decode

set_option warningAsError true

/-!
# Local decoder-window preservation

The pinned decoder observes only a bounded byte window at one program counter:

* out of range: no bytes; the result is implicit `STOP`;
* ordinary or invalid opcode: one byte;
* `PUSHn`: the opcode plus `n` immediate bytes, with `ByteArray.extract`
  truncation at end of code;
* EIP-8024 `DUPN`/`SWAPN`/`EXCHANGE`: the opcode plus one immediate byte,
  zero-filled when that byte is out of range.

`checkAt left right pc` is a finite executable certificate for equality of
exactly those observations. It does not assume `Decode.decodeAt` equality.
-/

namespace Challenge.Modexp.Submission.LocalPatch.LocalDecode

open EvmSemantics
open EvmSemantics.EVM

/-- Total opcode-byte observation, retaining the distinction between an
in-range zero byte and an out-of-range implicit STOP. -/
def opcodeByte (code : ByteArray) (pc : Nat) : Option UInt8 :=
  if h : pc < code.size then some code[pc] else none

/-- Total one-byte read used by EIP-8024 decoding. -/
def byteAtZero (code : ByteArray) (pc : Nat) : UInt8 :=
  if h : pc < code.size then code[pc] else 0

/-- The immediate material actually consumed by `Decode.decodeAt`. -/
inductive ImmediateWindow where
  | none
  | push (bytes : ByteArray)
  | eip8024 (byte : UInt8)
  deriving DecidableEq

/-- Number of immediate bytes conceptually inspected at `pc`.
For a truncated final PUSH this remains the declared width; `extract` supplies
only the bytes physically present. -/
def immediateLength (code : ByteArray) (pc : Nat) : Nat :=
  match opcodeByte code pc with
  | none => 0
  | some opcode =>
      match Decode.opcodeOf opcode with
      | some (.Push p) => p.width.val
      | some (.DupN _) => 1
      | some (.SwapN _) => 1
      | some (.Exchange _) => 1
      | _ => 0

/-- Exact conceptual decode-window length: 0 out of range, otherwise one opcode
byte plus `immediateLength`. -/
def windowLength (code : ByteArray) (pc : Nat) : Nat :=
  match opcodeByte code pc with
  | none => 0
  | some _ => 1 + immediateLength code pc

def immediateWindow (code : ByteArray) (pc : Nat) : ImmediateWindow :=
  match opcodeByte code pc with
  | none => .none
  | some opcode =>
      match Decode.opcodeOf opcode with
      | some (.Push p) =>
          .push (code.extract (pc + 1) (pc + 1 + p.width.val))
      | some (.DupN _) => .eip8024 (byteAtZero code (pc + 1))
      | some (.SwapN _) => .eip8024 (byteAtZero code (pc + 1))
      | some (.Exchange _) => .eip8024 (byteAtZero code (pc + 1))
      | _ => .none

/-- The weakest practical local facts used by the proof.
No global size equality is required: both codes need only make the same local
opcode observation and the same decoder-consumed immediate observation. -/
abbrev SameWindow (left right : ByteArray) (pc : Nat) : Prop :=
  opcodeByte left pc = opcodeByte right pc ∧
    immediateWindow left pc = immediateWindow right pc

/-- Mechanically checkable local certificate. -/
def checkAt (left right : ByteArray) (pc : Nat) : Bool :=
  decide (SameWindow left right pc)

def checkMany (left right : ByteArray) (pcs : List Nat) : Bool :=
  pcs.all (fun pc => checkAt left right pc)

theorem sameWindow_of_checkAt {left right : ByteArray} {pc : Nat}
    (hcheck : checkAt left right pc = true) :
    SameWindow left right pc := by
  unfold checkAt at hcheck
  exact of_decide_eq_true hcheck

@[simp] theorem checkAt_refl (code : ByteArray) (pc : Nat) :
    checkAt code code pc = true := by
  simp [checkAt, SameWindow]

@[simp] theorem checkMany_refl (code : ByteArray) (pcs : List Nat) :
    checkMany code code pcs = true := by
  simp [checkMany]

private theorem decodeAt_eq_of_sameWindow {left right : ByteArray} {pc : Nat}
    (hwindow : SameWindow left right pc) :
    Decode.decodeAt left pc = Decode.decodeAt right pc := by
  rcases hwindow with ⟨hopcodeWindow, himmediateWindow⟩
  by_cases hleft : pc < left.size
  · by_cases hright : pc < right.size
    · have hopcodeByte : left[pc] = right[pc] := by
        simpa [opcodeByte, hleft, hright] using hopcodeWindow
      have hopcodeRight :
          Decode.opcodeOf right[pc] = Decode.opcodeOf left[pc] := by
        rw [← hopcodeByte]
      cases hopcode : Decode.opcodeOf left[pc] with
      | none =>
          simp [Decode.decodeAt, hleft, hright, hopcode, hopcodeRight]
      | some op =>
          cases op with
          | StopArith op =>
              simp [Decode.decodeAt, hleft, hright, hopcode, hopcodeRight]
          | CompBit op =>
              simp [Decode.decodeAt, hleft, hright, hopcode, hopcodeRight]
          | Keccak op =>
              simp [Decode.decodeAt, hleft, hright, hopcode, hopcodeRight]
          | Env op =>
              simp [Decode.decodeAt, hleft, hright, hopcode, hopcodeRight]
          | Block op =>
              simp [Decode.decodeAt, hleft, hright, hopcode, hopcodeRight]
          | StackMemFlow op =>
              simp [Decode.decodeAt, hleft, hright, hopcode, hopcodeRight]
          | Push push =>
              cases push with
              | mk width =>
                  have hpayload :
                      left.extract (pc + 1) (pc + 1 + width.val) =
                        right.extract (pc + 1) (pc + 1 + width.val) := by
                    simpa [immediateWindow, opcodeByte, hleft, hright,
                      hopcode, hopcodeRight] using himmediateWindow
                  simp [Decode.decodeAt, hleft, hright, hopcode,
                    hopcodeRight, hpayload]
          | Dup op =>
              simp [Decode.decodeAt, hleft, hright, hopcode, hopcodeRight]
          | Swap op =>
              simp [Decode.decodeAt, hleft, hright, hopcode, hopcodeRight]
          | DupN op =>
              have himmediate :
                  byteAtZero left (pc + 1) =
                    byteAtZero right (pc + 1) := by
                simpa [immediateWindow, opcodeByte, hleft, hright,
                  hopcode, hopcodeRight] using himmediateWindow
              by_cases hnextLeft : pc + 1 < left.size <;>
                by_cases hnextRight : pc + 1 < right.size <;>
                simp [byteAtZero, hnextLeft, hnextRight] at himmediate <;>
                simp [Decode.decodeAt, hleft, hright, hopcode,
                  hopcodeRight, hnextLeft, hnextRight, himmediate]
          | SwapN op =>
              have himmediate :
                  byteAtZero left (pc + 1) =
                    byteAtZero right (pc + 1) := by
                simpa [immediateWindow, opcodeByte, hleft, hright,
                  hopcode, hopcodeRight] using himmediateWindow
              by_cases hnextLeft : pc + 1 < left.size <;>
                by_cases hnextRight : pc + 1 < right.size <;>
                simp [byteAtZero, hnextLeft, hnextRight] at himmediate <;>
                simp [Decode.decodeAt, hleft, hright, hopcode,
                  hopcodeRight, hnextLeft, hnextRight, himmediate]
          | Exchange op =>
              have himmediate :
                  byteAtZero left (pc + 1) =
                    byteAtZero right (pc + 1) := by
                simpa [immediateWindow, opcodeByte, hleft, hright,
                  hopcode, hopcodeRight] using himmediateWindow
              by_cases hnextLeft : pc + 1 < left.size <;>
                by_cases hnextRight : pc + 1 < right.size <;>
                simp [byteAtZero, hnextLeft, hnextRight] at himmediate <;>
                simp [Decode.decodeAt, hleft, hright, hopcode,
                  hopcodeRight, hnextLeft, hnextRight, himmediate]
          | Log op =>
              simp [Decode.decodeAt, hleft, hright, hopcode, hopcodeRight]
          | System op =>
              simp [Decode.decodeAt, hleft, hright, hopcode, hopcodeRight]
    · simp [opcodeByte, hleft, hright] at hopcodeWindow
  · have hright : ¬pc < right.size := by
      intro hright
      simp [opcodeByte, hleft, hright] at hopcodeWindow
    simp [Decode.decodeAt, hleft, hright]

/-- Main single-PC theorem. -/
theorem decodeAt_eq_of_checkAt {left right : ByteArray} {pc : Nat}
    (hcheck : checkAt left right pc = true) :
    Decode.decodeAt left pc = Decode.decodeAt right pc :=
  decodeAt_eq_of_sameWindow (sameWindow_of_checkAt hcheck)

/-- Finite executable binding for a list of ordinary instruction PCs. -/
theorem decodeAt_eq_of_checkMany {left right : ByteArray} {pcs : List Nat}
    (hcheck : checkMany left right pcs = true) {pc : Nat}
    (hpc : pc ∈ pcs) :
    Decode.decodeAt left pc = Decode.decodeAt right pc := by
  have hat : checkAt left right pc = true :=
    (List.all_eq_true.mp hcheck) pc hpc
  exact decodeAt_eq_of_checkAt hat

end Challenge.Modexp.Submission.LocalPatch.LocalDecode
