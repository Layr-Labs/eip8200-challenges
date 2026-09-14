import Challenge.Modexp.Submission.Proofs.Fast.SquareRows

set_option warningAsError true
set_option linter.unusedSimpArgs false
set_option maxRecDepth 40000
set_option maxHeartbeats 2000000

/-!
# Located blocks of the in-kernel squaring loop (`sq_exit` / `more` / `again`)

The R0 artifact keeps the square's row frame at the kernel exit: the dispatch at 4846
sends a square to `sq_exit` (4912), which

* decrements the square counter in memory word 2624 (`0x2440`, written by the caller) and
  stores it back;
* if it is still non-zero, jumps to `more` (2400), which calls the unchanged final
  conditional subtraction as a **subroutine** (`PUSH2 again DUP16 PUSH2 guard JUMP`, so the
  CSUB sees only `[pdst, again]` above the retained frame) and comes back at `again` (4988);
* `again` (4988) re-stages the operand (`MCOPY 0x800 → 0x2300`), re-zeroes the accumulator
  (`CALLDATACOPY` of the calldata tail) and resets the frame's pointer, first-loop entry and
  previous-limb slots, then falls into `sq_row` (2496) — exactly the row-0 state that
  `Cios2Dispatch.gasSteps_commonSetupInput` produces for a fresh call;
* if the counter reached zero, `last` (4929) overwrites the frame's `ret` slot with
  `after_sq` (3360) and leaves through `nx` (4855), the 14 `POP`s and the CSUB.
-/

namespace Challenge.Modexp.Submission.Proofs.Fast.SquareLoopBlocks

open EvmSemantics EvmSemantics.EVM YulEvmCompiler
open Challenge.Modexp.Submission.Proofs.Bytecode WindowNibbleKernel WindowTwentyOneBinding
open Challenge.Modexp.Submission.Proofs.Fast
open Monpro CiosCached CarryRowBlocks CarryRowModel SquareRows

/-! ## The loop's program counters

Named so that a rider restack relocates them once, in the regenerator's `def pcX : Nat := N`
form, instead of once per use site. -/

def pcNx : Nat := 4118
def pcSqExit : Nat := 4174
def pcLast : Nat := 4196
def pcAgain : Nat := 4218
/-- H2：CSUB 返回点（R4 挂钩）。 -/
def pcH2 : Nat := 4208

/-! ## The retained frame -/

/-- The 16-slot row frame of a square (`pb = pa = 2048`, `hd = sq_row`), as it stands at
the kernel exit and through the whole loop. -/
def frameStack (n : Nat) (pbi ent tl inv m0 m96 m64 m32 aprev pdst ret : UInt256) :
    List UInt256 → List UInt256 := fun rest =>
  [pbi, UInt256.ofNat 4234, UInt256.ofNat (2368 - 32), ent, negative32, allOnes, l2Target n,
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
      CiosCachedTailDefs.sqExitState s mem pbi 2368 n (UInt256.ofNat 4234) ent inv m0
        (tl :: m96 :: m64 :: m32 :: aprev :: pdst :: ret :: rest) := rfl

/-- The `nx` `JUMPDEST` state of the last square. -/
theorem frameAt_eq_nxJdState (s : State) (mem : ByteArray) (n : Nat)
    (pbi ent tl inv m0 m96 m64 m32 aprev pdst ret : UInt256) (rest : List UInt256) :
    frameAt pcNx s mem n pbi ent tl inv m0 m96 m64 m32 aprev pdst ret rest =
      CiosCachedTailDefs.nxJdState s mem pbi 2368 n (UInt256.ofNat 4234) ent inv m0
        (tl :: m96 :: m64 :: m32 :: aprev :: pdst :: ret :: rest) := rfl

/-! ## Programs -/

/-- `sq_exit`: push the CSUB call's `[pdst, again]`, load the counter, decrement, store it
back, and call the CSUB directly while rounds remain. -/
def sqExitProgram : List Instr :=
  [.op .JUMPDEST, .push 2 4208, .push 2 2368, .push 2 2624, .op .MLOAD,
   .op (.Dup ⟨8, by decide⟩), .op .ADD,
   .op (.Dup ⟨0, by decide⟩), .push 2 2624, .op .MSTORE, .push 2 4535, .op .JUMPI]

/-- `last`: drop the unused call pair, then call the CSUB as a subroutine returning to the
post-loop block. -/
def lastProgram : List Instr :=
  [.op .POP, .op .POP, .push 2 3469, .push 2 2368, .push 2 4535, .op .JUMP]

/-- `again` (4214): reload the width word, reset three frame slots and jump to the
row-zero entry.  The accumulator is no longer cleared here: the new first row writes
every word of `T` before reading it. -/
def againProgram : List Instr :=
  [.push 2 2688, .op .MLOAD,
   .op .ADD, .push 2 288, .op (.Dup ⟨7, by decide⟩), .op .SUB,
   .op (.Swap ⟨3, by decide⟩), .op .POP,
   .push 2 5091, .op .JUMP]

/-! ## Located blocks -/

def sqExitBlock : Block Artifact.submissionArtifact .Osaka 4174 sqExitProgram :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3163 12 4174 sqExitProgram
    (by decide) (by rfl) (by rfl) (by decide)

def lastBlock : Block Artifact.submissionArtifact .Osaka 4196 lastProgram :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3175 6 4196 lastProgram
    (by decide) (by rfl) (by rfl) (by decide)

def againBlock : Block Artifact.submissionArtifact .Osaka 4218 againProgram :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3187 10 4218 againProgram
    (by decide) (by rfl) (by rfl) (by decide)

/-! ## Jump destinations of the loop -/

theorem jumpDest4683 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 4132 = true :=
  Artifact.isValidJumpDest_index 3136 (by rfl)

/-! ## The counter word -/

/-- The memory after `sq_exit`'s `MSTORE`: the counter word 2624 holds `c`. -/
theorem jumpDestLazy :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 4535 = true :=
  Artifact.isValidJumpDest_index 3425 (by rfl)

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
