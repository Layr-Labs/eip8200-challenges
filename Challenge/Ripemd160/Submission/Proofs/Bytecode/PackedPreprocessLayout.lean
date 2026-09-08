import Challenge.Ripemd160.Submission.Proofs.Bytecode.Artifact
import Challenge.Ripemd160.Submission.Proofs.Bytecode.PackedGapInvariant
import Challenge.Ripemd160.Submission.Proofs.Bytecode.PackedScheduleMath

set_option warningAsError true
set_option autoImplicit false
set_option maxRecDepth 10000

/-!
# Exact packed preprocessing layout

The frozen packed runtime stores its two byte-swapped input words at addresses
`320` and `288`.  It then executes sixteen six-instruction groups in descending
word order.  Group `n` reads at `260 + 4*n`, keeps the low 32 bits, and performs
an EVM word store at `16*n`.  Thus the groups write word 15 first and word 0
last, exactly the recursion order of `PackedGapInvariant.spreadWords`.

This module freezes that instruction layout and the pure memory model.  It does
not claim that the EVM trace has executed the model; that is the next located
trace obligation.
-/

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.PackedPreprocessLayout

open Challenge.Ripemd160 Challenge.EvmProof
open EvmSemantics EvmSemantics.EVM YulEvmCompiler

def op (operation : Operation) : Instr := .op operation

def push0 : Instr := .push ⟨0, by decide⟩ (UInt256.ofNat 0)

def push1 (value : Nat) : Instr :=
  .push ⟨1, by decide⟩ (UInt256.ofNat value)

def push2 (value : Nat) : Instr :=
  .push ⟨2, by decide⟩ (UInt256.ofNat value)

def push4 (value : Nat) : Instr :=
  .push ⟨4, by decide⟩ (UInt256.ofNat value)

def dup2 : Instr := .op (.Dup ⟨1, by decide⟩)

def mask32 : Nat := 0xffffffff

def sourceAddress (n : Nat) : Nat := 260 + 4 * n

def destinationAddress (n : Nat) : Nat := 16 * n

def destinationPush (n : Nat) : Instr :=
  if n = 0 then push0 else push1 (destinationAddress n)

/-- One exact `PUSH2; MLOAD; DUP2; AND; PUSH; MSTORE` group. -/
def spreadStoreTemplate (n : Nat) : List Instr :=
  [push2 (sourceAddress n), op .MLOAD, dup2, op .AND,
    destinationPush n, op .MSTORE]

/-- Exact artifact instructions 362 through 459 inclusive. -/
def spreadTemplate : List Instr :=
  [push4 mask32] ++
    (List.range 16).reverse.flatMap spreadStoreTemplate ++
    [op .POP]

@[simp] theorem spreadStoreTemplate_length (n : Nat) :
    (spreadStoreTemplate n).length = 6 := by
  rfl

@[simp] theorem spreadTemplate_length : spreadTemplate.length = 98 := by
  rfl

theorem artifact_spread_slice :
    (Artifact.submissionArtifact.instructions.drop 362).take 98 =
      spreadTemplate := by
  rfl

/-- Start index of the group that stores word `n`, for `n < 16`. -/
def spreadStartIndex (n : Nat) : Nat := 363 + 6 * (15 - n)

/-- Start PC of the group that stores word `n`, for `n < 16`. -/
def spreadStartPC (n : Nat) : Nat := 640 + 9 * (15 - n)

theorem source_tail_address (n : Nat) :
    sourceAddress n + 28 = 288 + 4 * n := by
  unfold sourceAddress
  omega

theorem destination_end_le_gap (n : Nat) (hn : n < 16) :
    destinationAddress n + 32 ≤ 272 := by
  unfold destinationAddress
  omega

/-- Every spread store ends before the four source bytes selected by `AND`.
The full 32-byte source `MLOAD` may overlap an earlier destination store, but
its low four bytes never do. -/
theorem destination_before_source_tail (n k : Nat) (hn : n < 16)
    (hk : k < 16) :
    destinationAddress k + 32 ≤ sourceAddress n + 28 := by
  rw [source_tail_address]
  exact (destination_end_le_gap k hk).trans (by omega)

/-- The word placed by group `n`, frozen against the memory at loop entry. -/
def spreadValue (memory : ByteArray) (n : Nat) : UInt256 :=
  UInt256.land (MachineState.readWord memory (sourceAddress n))
    (UInt256.ofNat mask32)

/-- Pure postcondition of the descending sixteen-store loop. -/
def spreadMemory (memory : ByteArray) : ByteArray :=
  PackedGapInvariant.spreadWords (spreadValue memory) 16 memory

theorem spreadMemory_first_store (memory : ByteArray) :
    spreadMemory memory =
      PackedGapInvariant.spreadWords (spreadValue memory) 15
        (PackedGapInvariant.storeWord memory 240 (spreadValue memory 15)) := by
  rfl

theorem spreadMemory_gap (memory : ByteArray)
    (hgap : PackedGapInvariant.GapZero memory) :
    PackedGapInvariant.GapZero (spreadMemory memory) := by
  exact PackedGapInvariant.spreadWords_gap (spreadValue memory) 16
    (Nat.le_refl 16) memory hgap

/-- Memory just before the descending loop, after the two byte-swap stores. -/
def packedBaseMemory (memory : ByteArray) (word0 word1 : UInt256) : ByteArray :=
  PackedGapInvariant.storeWord
    (PackedGapInvariant.storeWord memory 320 (PackedScheduleMath.packed word1))
    288 (PackedScheduleMath.packed word0)

end Challenge.Ripemd160.Submission.Proofs.Bytecode.PackedPreprocessLayout
