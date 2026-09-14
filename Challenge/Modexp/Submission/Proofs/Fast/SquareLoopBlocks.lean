import Challenge.Modexp.Submission.Proofs.Fast.SquareRows

set_option warningAsError true
set_option linter.unusedSimpArgs false
set_option maxRecDepth 40000
set_option maxHeartbeats 2000000

/-!
Located square-loop control blocks for the submitted runtime. The exit at 4362
stores the decremented counter at memory word 2624. Conditional subtraction keeps
the square frame and returns either to H2 at 4409 or to the fused product at 3657.
The eight-limb restart at 4419 clears the cached carry and scratch accumulator;
the four-limb H2 branch enters R4 at 4809. A retained frame carries its explicit
TN value until one of those real reset instructions executes.
-/

namespace Challenge.Modexp.Submission.Proofs.Fast.SquareLoopBlocks

open EvmSemantics EvmSemantics.EVM YulEvmCompiler
open Challenge.Modexp.Submission.Proofs.Bytecode WindowNibbleKernel WindowTwentyOneBinding
open Challenge.Modexp.Submission.Proofs.Fast
open Monpro CiosCached SquareRow CarryRowModel SquareRows

/-! ## The loop's program counters

Named so that a rider restack relocates them once, in the regenerator's `def pcX : Nat := N`
form, instead of once per use site. -/

def pcNx : Nat := 4306
def pcSqExit : Nat := 4362
def pcLast : Nat := 4384
def pcAgain : Nat := 4419
/-- H2：CSUB 返回点（R4 挂钩）。 -/
def pcH2 : Nat := 4409

/-! ## The retained frame -/

/-- The 16-slot row frame of a square (`pb = pa = 2048`, `hd = sq_row`), as it stands at
the kernel exit and through the whole loop. -/
def frameStack (n : Nat) (pbi ent tl inv m0 m96 m64 m32 aprev pdst ret : UInt256)
    (rest : List UInt256) (tn : UInt256 := UInt256.ofNat 0) : List UInt256 :=
  [pbi, UInt256.ofNat 4471, UInt256.ofNat (2368 - 32), ent, tn, allOnes, l2Target n,
    inv, m0, tl, m96, m64, m32, aprev, pdst, ret] ++ rest

/-- The loop's states differ only in the program counter and the memory. -/
def frameAt (pc : Nat) (s : State) (mem : ByteArray) (n : Nat)
    (pbi ent tl inv m0 m96 m64 m32 aprev pdst ret : UInt256) (rest : List UInt256) (tn : UInt256 := UInt256.ofNat 0) : State :=
  { s with pc := UInt256.ofNat pc
           stack := frameStack n pbi ent tl inv m0 m96 m64 m32 aprev pdst ret rest tn
           memory := mem }

/-! ## Programs -/

/-- `sq_exit`: push the CSUB call's `[pdst, again]`, load the counter, decrement, store it
back, and call the CSUB directly while rounds remain. -/
def sqExitProgram : List Instr :=
  [.op .JUMPDEST, .push 2 4409, .push 2 2368, .push 2 2624, .op .MLOAD,
   .op (.Dup ⟨8, by decide⟩), .op .ADD,
   .op (.Dup ⟨0, by decide⟩), .push 2 2624, .op .MSTORE, .push 2 4389, .op .JUMPI]

/-- `last`: drop the unused call pair, then call the CSUB as a subroutine returning to the
post-loop block. -/
def lastProgram : List Instr :=
  [.push 2 3657, .op (.Swap ⟨1, by decide⟩), .op .POP]

/-- The R4 hook admits only n = 8 here. Constants preserve the width and
clear its fixed 320-byte accumulator before resetting the row frame. -/
def againProgram : List Instr :=
  [.push 0 0, .op (.Swap ⟨4, by decide⟩), .op .POP,
   .push 2 256, .push 2 320, .op .CALLDATASIZE, .push 2 2048, .op .CALLDATACOPY,
   .op .ADD, .push 2 283, .op (.Dup ⟨7, by decide⟩), .op .SUB,
   .op (.Swap ⟨3, by decide⟩), .op .POP]

/-! ## Located blocks -/

def sqExitBlock : Block Artifact.submissionArtifact .Osaka 4362 sqExitProgram :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3302 12 4362 sqExitProgram
    (by decide) (by rfl) (by rfl) (by decide)

def lastBlock : Block Artifact.submissionArtifact .Osaka 4384 lastProgram :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3314 3 4384 lastProgram
    (by decide) (by rfl) (by rfl) (by decide)

def againBlock : Block Artifact.submissionArtifact .Osaka 4419 againProgram :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3335 14 4419 againProgram
    (by decide) (by rfl) (by rfl) (by decide)

/-! ## Jump destinations of the loop -/

theorem jumpDest4683 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 4320 = true :=
  Artifact.isValidJumpDest_index 3275 (by rfl)

/-! ## The counter word -/

/-- The memory after `sq_exit`'s `MSTORE`: the counter word 2624 holds `c`. -/
theorem jumpDestLazy :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 4389 = true :=
  Artifact.isValidJumpDest_index 3317 (by rfl)

def countMem (mem : ByteArray) (c : Nat) : ByteArray :=
  MachineState.writeBytes mem (Data.Bytes.natToBytesPadded c 32) 2624

theorem readWord_countMem (mem : ByteArray) (c : Nat) (hc : c < 2 ^ 256) :
    MachineState.readWord (countMem mem c) 2624 = UInt256.ofNat c := by
  have h : (UInt256.ofNat c).toNat = c := by
    rw [Challenge.EvmProof.Word.word_toNat_ofNat, Nat.mod_eq_of_lt hc]
  calc MachineState.readWord (countMem mem c) 2624
      = MachineState.readWord
          (MachineState.writeBytes mem
            (Data.Bytes.natToBytesPadded (UInt256.ofNat c).toNat 32) 2624) 2624 := by
        rw [countMem, h]
    _ = UInt256.ofNat c := Challenge.EvmProof.Memory.readWord_writeWord mem 2624 (UInt256.ofNat c)

theorem readWord_countMem_disjoint (mem : ByteArray) (c addr : Nat)
    (hd : addr + 32 ≤ 2624 ∨ 2656 ≤ addr) :
    MachineState.readWord (countMem mem c) addr = MachineState.readWord mem addr := by
  simp only [countMem]
  apply Challenge.EvmProof.Memory.readWord_writeBytes_disjoint
  rw [show (Data.Bytes.natToBytesPadded c 32).size = 32 by
    simp [Data.Bytes.natToBytesPadded, ByteArray.size]]
  omega

end Challenge.Modexp.Submission.Proofs.Fast.SquareLoopBlocks
