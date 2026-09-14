import Challenge.Modexp.Submission.Proofs.Fast.SquareRows

set_option warningAsError true
set_option linter.unusedSimpArgs false
set_option maxRecDepth 40000
set_option maxHeartbeats 2000000

/-!
# Located blocks of the in-kernel squaring loop

The square exit decrements the counter in memory word 2624. Further rounds
use the lazy subtraction gate with H2 as their return address. The final
round replaces that address with 3666 and falls through into the moved gate.
The repeated staging block resets the pointer and chain entry, then falls
through into the relocated eight-limb row-zero helper.
-/

namespace Challenge.Modexp.Submission.Proofs.Fast.SquareLoopBlocks

open EvmSemantics EvmSemantics.EVM YulEvmCompiler
open Challenge.Modexp.Submission.Proofs.Bytecode WindowNibbleKernel WindowTwentyOneBinding
open Challenge.Modexp.Submission.Proofs.Fast
open Monpro CiosCached CarryRowBlocks CarryRowModel SquareRows

/-! ## The loop's program counters

Named so that a rider restack relocates them once, in the regenerator's `def pcX : Nat := N`
form, instead of once per use site. -/

def pcNx : Nat := 4316
def pcSqExit : Nat := 4372
def pcLast : Nat := 4394
def pcAgain : Nat := 4432
/-- H2：CSUB 返回点（R4 挂钩）。 -/
def pcH2 : Nat := 4422

/-! ## The retained frame -/

/-- The 16-slot row frame of a square (`pb = pa = 2048`, `hd = sq_row`), as it stands at
the kernel exit and through the whole loop. -/
def frameStack (n : Nat) (pbi ent tl inv m0 m96 m64 m32 aprev pdst ret : UInt256) :
    List UInt256 → List UInt256 := fun rest =>
  [pbi, UInt256.ofNat 4483, UInt256.ofNat (2368 - 32), ent, negative32, allOnes, l2Target n,
    inv, m0, tl, m96, m64, m32, aprev, pdst, ret] ++ rest

/-- The loop's states differ only in the program counter and the memory. -/
def frameAt (pc : Nat) (s : State) (mem : ByteArray) (n : Nat)
    (pbi ent tl inv m0 m96 m64 m32 aprev pdst ret : UInt256) (rest : List UInt256) : State :=
  { s with pc := UInt256.ofNat pc
           stack := frameStack n pbi ent tl inv m0 m96 m64 m32 aprev pdst ret rest
           memory := mem }

/-- `sq_exit`'s entry is the dispatch's target state. -/
theorem frameAt_eq_sqExitState (s : State) (mem : ByteArray) (n : Nat)
    (pbi ent tl inv m0 m96 m64 m32 aprev pdst ret : UInt256) (rest : List UInt256) :
    frameAt pcSqExit s mem n pbi ent tl inv m0 m96 m64 m32 aprev pdst ret rest =
      CiosCachedTailDefs.sqExitState s mem pbi 2368 n (UInt256.ofNat 4483) ent inv m0
        (tl :: m96 :: m64 :: m32 :: aprev :: pdst :: ret :: rest) := rfl

/-- The `nx` `JUMPDEST` state of the last square. -/
theorem frameAt_eq_nxJdState (s : State) (mem : ByteArray) (n : Nat)
    (pbi ent tl inv m0 m96 m64 m32 aprev pdst ret : UInt256) (rest : List UInt256) :
    frameAt pcNx s mem n pbi ent tl inv m0 m96 m64 m32 aprev pdst ret rest =
      CiosCachedTailDefs.nxJdState s mem pbi 2368 n (UInt256.ofNat 4483) ent inv m0
        (tl :: m96 :: m64 :: m32 :: aprev :: pdst :: ret :: rest) := rfl

/-! ## Programs -/

/-- `sq_exit`: push the CSUB call's `[pdst, again]`, load the counter, decrement, store it
back, and call the CSUB directly while rounds remain. -/
def sqExitProgram : List Instr :=
  [.op .JUMPDEST, .push 2 4422, .push 2 2368, .push 2 2624, .op .MLOAD,
   .op (.Dup ⟨8, by decide⟩), .op .ADD,
   .op (.Dup ⟨0, by decide⟩), .push 2 2624, .op .MSTORE, .push 2 4402, .op .JUMPI]

/-- `last`: drop the unused call pair, then call the CSUB as a subroutine returning to the
post-loop block. -/
def lastProgram : List Instr :=
  [.push 5 3666, .op (.Swap ⟨1, by decide⟩), .op .POP]

/-- `again` (4988): re-stage, re-zero, reset three frame slots, fall into `sq_row`. -/
def againProgram : List Instr :=
  [.push 2 2688, .op .MLOAD, .op (.Dup ⟨0, by decide⟩), .push 1 64, .op .ADD, .op .CALLDATASIZE, .push 2 2048,
   .op .CALLDATACOPY,
   .op .ADD, .push 2 289, .op (.Dup ⟨7, by decide⟩), .op .SUB,
   .op (.Swap ⟨3, by decide⟩), .op .POP]

/-! ## Located blocks -/

def sqExitBlock : Block Artifact.submissionArtifact .Osaka 4372 sqExitProgram :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3313 12 4372 sqExitProgram
    (by decide) (by rfl) (by rfl) (by decide)

def lastBlock : Block Artifact.submissionArtifact .Osaka 4394 lastProgram :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3325 3 4394 lastProgram
    (by decide) (by rfl) (by rfl) (by decide)

def againBlock : Block Artifact.submissionArtifact .Osaka 4432 againProgram :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3346 14 4432 againProgram
    (by decide) (by rfl) (by rfl) (by decide)

/-! ## Jump destinations of the loop -/

theorem jumpDest4683 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 4330 = true :=
  Artifact.isValidJumpDest_index 3286 (by rfl)

/-! ## The counter word -/

/-- The memory after `sq_exit`'s `MSTORE`: the counter word 2624 holds `c`. -/
theorem jumpDestLazy :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 4402 = true :=
  Artifact.isValidJumpDest_index 3328 (by rfl)

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
