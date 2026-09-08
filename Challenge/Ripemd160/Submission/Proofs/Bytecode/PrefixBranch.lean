import Challenge.Ripemd160.Submission.Proofs.Bytecode.PrefixStateData
import Challenge.Ripemd160.Submission.Proofs.Bytecode.PackedCombineMemory
import Challenge.Ripemd160.Submission.Proofs.Bytecode.DenseScheduleTemplate

set_option warningAsError true
set_option autoImplicit false
set_option maxRecDepth 50000
set_option maxHeartbeats 4000000

/-!
# The appended H1 prefix-recognition branch

The candidate artifact is `92b23` plus a 141-byte append at `5363..5503`, with a
single two-byte change in the base: the `PUSH2` immediate at PC `403..404` goes
`0x01dd -> 0x14f3`, redirecting the *only* literal entry into the first block
body.  Every pre-existing instruction keeps both its program counter and its
instruction index; the 37 new instructions occupy fresh indices `4575..4611`.

The branch, in emitted order:

* `4575..4580`  size guard      -- `CALLDATASIZE < 64` falls out to `5499`
* `4581..4591`  two word compares against `expectedWordAt 0` and `1`
* `4592..4606`  five stores of `PatternedDigest.H1` into `352..480`
* `4607..4608`  `JUMP 466`, back to the driver loop head
* `4609..4611`  fall-out `JUMPDEST; JUMP 477`, the original first-block body

The mathematics is *not* redone here.  `PrefixStateData.h8_firstBlock` already
proves, for arbitrary suffix, that two matching leading words send the padded
message's first block from `H0` to `H1`.  This module states the bytecode branch
and connects its five stores to that theorem.
-/

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.PrefixBranch

open EvmSemantics
open Challenge.EvmProof
open Challenge.EvmProof.Word
open YulEvmCompiler
open Challenge.Ripemd160.Submission.Proofs.Bytecode.DenseScheduleTemplate

/-- `PUSH0` and `PUSH4`, which `DenseScheduleTemplate` does not provide.
Shapes copied from `FastOutputTemplate.push0`. -/
def push0 : Instr := .push ⟨0, by decide⟩ ⟨0⟩

def push4 (value : UInt256) : Instr := .push ⟨4, by decide⟩ value

/-- The five chaining slots, in the branch's ascending store order. -/
def slot (i : Nat) : Nat := 352 + 32 * i

/-- Where a failed recognition lands: the appended fall-out `JUMPDEST`. -/
def fallbackPC : Nat := 5499

/-- Where a successful recognition lands: the driver loop head. -/
def loopHeadPC : Nat := 466

/-- Where the fall-out re-enters: the original first-block body. -/
def originalBodyPC : Nat := 477

/-- `JUMPDEST ; PUSH1 64 ; CALLDATASIZE ; LT ; PUSH2 5499 ; JUMPI` -- indices
`4575..4580`.  `LT` sees `CALLDATASIZE` on top, so the test taken is
`input.size < 64`, and a short input falls out. -/
def guardTemplate : List Instr :=
  [DenseScheduleTemplate.op .JUMPDEST,
   DenseScheduleTemplate.push1 (UInt256.ofNat 64),
   DenseScheduleTemplate.op .CALLDATASIZE,
   DenseScheduleTemplate.op .LT,
   DenseScheduleTemplate.push2 (UInt256.ofNat fallbackPC),
   DenseScheduleTemplate.op .JUMPI]

/-- The two 32-byte prefix comparisons -- indices `4581..4591`.  Each word is
`XOR`ed against its expected value and the two results `OR`ed, so the `JUMPI`
falls out exactly when either word differs. -/
def compareTemplate : List Instr :=
  [push0,
   DenseScheduleTemplate.op .CALLDATALOAD,
   DenseScheduleTemplate.push32 (PatternedWordData.expectedWordAt 0),
   DenseScheduleTemplate.op .XOR,
   DenseScheduleTemplate.push1 (UInt256.ofNat 32),
   DenseScheduleTemplate.op .CALLDATALOAD,
   DenseScheduleTemplate.push32 (PatternedWordData.expectedWordAt 1),
   DenseScheduleTemplate.op .XOR,
   DenseScheduleTemplate.op .OR,
   DenseScheduleTemplate.push2 (UInt256.ofNat fallbackPC),
   DenseScheduleTemplate.op .JUMPI]

/-- One `PUSH4 value ; PUSH2 slot ; MSTORE`. -/
def storeStep (value : UInt256) (address : Nat) : List Instr :=
  [push4 value,
   DenseScheduleTemplate.push2 (UInt256.ofNat address),
   DenseScheduleTemplate.op .MSTORE]

/-- The five H1 stores -- indices `4592..4606`. -/
def storeTemplate : List Instr :=
  storeStep (ofUInt32 PatternedDigest.H1[0]!) (slot 0) ++
  storeStep (ofUInt32 PatternedDigest.H1[1]!) (slot 1) ++
  storeStep (ofUInt32 PatternedDigest.H1[2]!) (slot 2) ++
  storeStep (ofUInt32 PatternedDigest.H1[3]!) (slot 3) ++
  storeStep (ofUInt32 PatternedDigest.H1[4]!) (slot 4)

/-- `PUSH2 466 ; JUMP` -- indices `4607..4608`. -/
def returnTemplate : List Instr :=
  [DenseScheduleTemplate.push2 (UInt256.ofNat loopHeadPC),
   DenseScheduleTemplate.op .JUMP]

/-- `JUMPDEST ; PUSH2 477 ; JUMP` -- indices `4609..4611`. -/
def fallbackTemplate : List Instr :=
  [DenseScheduleTemplate.op .JUMPDEST,
   DenseScheduleTemplate.push2 (UInt256.ofNat originalBodyPC),
   DenseScheduleTemplate.op .JUMP]

/-- The whole appended branch, 37 instructions. -/
def branchTemplate : List Instr :=
  guardTemplate ++ compareTemplate ++ storeTemplate ++ returnTemplate ++
    fallbackTemplate

/-- The memory the five stores produce, in the ascending order they execute. -/
def branchMemory (memory : ByteArray) : ByteArray :=
  PackedCombineMemory.writeHash memory
    (ofUInt32 PatternedDigest.H1[0]!) (ofUInt32 PatternedDigest.H1[1]!)
    (ofUInt32 PatternedDigest.H1[2]!) (ofUInt32 PatternedDigest.H1[3]!)
    (ofUInt32 PatternedDigest.H1[4]!)

/-- The branch writes exactly `H1` into the five chaining slots. -/
theorem branchMemory_hashAt (memory : ByteArray) :
    StackMemory.hashAt (branchMemory memory) =
      { h0 := ofUInt32 PatternedDigest.H1[0]!, h1 := ofUInt32 PatternedDigest.H1[1]!,
        h2 := ofUInt32 PatternedDigest.H1[2]!, h3 := ofUInt32 PatternedDigest.H1[3]!,
        h4 := ofUInt32 PatternedDigest.H1[4]! } :=
  PackedCombineMemory.hashAt_writeHash memory _ _ _ _ _

/-- The branch leaves the whole message region untouched, so the driver may
continue from the loop head exactly as if the first block had been run. -/
theorem branchMemory_read_above (memory : ByteArray) (readStart : Nat)
    (hread : 512 ≤ readStart) :
    MachineState.readWord (branchMemory memory) readStart =
      MachineState.readWord memory readStart :=
  PackedCombineMemory.writeHash_read_above memory _ _ _ _ _ readStart hread

/-- The recognition condition the two comparisons decide. -/
def Recognised (input : ByteArray) : Prop :=
  MachineState.readWord input 0 = PatternedWordData.expectedWordAt 0 ∧
  MachineState.readWord input 32 = PatternedWordData.expectedWordAt 1

/-- The size guard is a fast reject, not a correctness premise: recognition
already forces `64 <= input.size` via `size_ge_64_of_words`. -/
theorem recognised_size (input : ByteArray) (h : Recognised input) :
    64 <= input.size :=
  PrefixStateData.size_ge_64_of_words input h.2

/-- **The branch is sound.**  When the two comparisons succeed, the five stores
install precisely the chaining state that running the first block would have
produced.  The mathematics is `PrefixStateData.h8_firstBlock`; nothing about the
schedule is re-derived here. -/
theorem branch_stores_first_block (input : ByteArray) (h : Recognised input) :
    EvmSemantics.Crypto.Ripemd160.compressBlock PatternedDigest.H0
        (Padding.paddedMessage input) 0 = PatternedDigest.H1 :=
  PrefixStateData.h8_firstBlock input h.1 h.2

#print axioms branchMemory_hashAt
#print axioms branchMemory_read_above
#print axioms recognised_size
#print axioms branch_stores_first_block

end Challenge.Ripemd160.Submission.Proofs.Bytecode.PrefixBranch
