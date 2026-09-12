import Challenge.Modexp.Submission.Proofs.Fast.SquareRows

set_option warningAsError true
set_option linter.unusedSimpArgs false
set_option maxRecDepth 40000
set_option maxHeartbeats 2000000

/-!
# Located blocks of the in-kernel squaring loop (`sq_exit` / `more` / `again`)

The R0 artifact keeps the square's row frame at the kernel exit: the dispatch at 4589
sends a square to `sq_exit` (4656), which

* decrements the square counter in memory word 9280 (`0x2440`, written by the caller) and
  stores it back;
* if it is still non-zero, jumps to `more` (4728), which calls the unchanged final
  conditional subtraction as a **subroutine** (`PUSH2 again DUP16 PUSH2 guard JUMP`, so the
  CSUB sees only `[pdst, again]` above the retained frame) and comes back at `again` (4737);
* `again` (4737) re-stages the operand (`MCOPY 0x800 → 0x2300`), re-zeroes the accumulator
  (`CALLDATACOPY` of the calldata tail) and resets the frame's pointer, first-loop entry and
  previous-limb slots, then falls into `sq_row` (4731) — exactly the row-0 state that
  `Cios2Dispatch.gasSteps_commonSetupInput` produces for a fresh call;
* if the counter reached zero, `last` (4673) overwrites the frame's `ret` slot with
  `after_sq` (3234) and leaves through `nx` (4598), the 14 `POP`s and the CSUB.
-/

namespace Challenge.Modexp.Submission.Proofs.Fast.SquareLoopBlocks

open EvmSemantics EvmSemantics.EVM YulEvmCompiler
open Challenge.Modexp.Submission.Proofs.Bytecode WindowNibbleKernel WindowTwentyOneBinding
open Challenge.Modexp.Submission.Proofs.Fast
open Monpro CiosCached CarryRowBlocks CarryRowModel SquareRows

/-! ## The loop's program counters

Named so that a rider restack relocates them once, in the regenerator's `def pcX : Nat := N`
form, instead of once per use site. -/

def pcNx : Nat := 4609
def pcSqExit : Nat := 4667
def pcLast : Nat := 4683
def pcMore : Nat := 4692
def pcAgain : Nat := 4701

/-! ## The retained frame -/

/-- The 16-slot row frame of a square (`pb = pa = 2048`, `hd = sq_row`), as it stands at
the kernel exit and through the whole loop. -/
def frameStack (n : Nat) (pbi ent tl inv m0 m96 m64 m32 aprev pdst ret : UInt256) :
    List UInt256 → List UInt256 := fun rest =>
  [pbi, UInt256.ofNat 4734, UInt256.ofNat (2048 - 32), ent, negative32, allOnes, l2Target n,
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
      CiosCachedTailDefs.sqExitState s mem pbi 2048 n (UInt256.ofNat 4734) ent inv m0
        (tl :: m96 :: m64 :: m32 :: aprev :: pdst :: ret :: rest) := rfl

/-- The `nx` `JUMPDEST` state of the last square. -/
theorem frameAt_eq_nxJdState (s : State) (mem : ByteArray) (n : Nat)
    (pbi ent tl inv m0 m96 m64 m32 aprev pdst ret : UInt256) (rest : List UInt256) :
    frameAt pcNx s mem n pbi ent tl inv m0 m96 m64 m32 aprev pdst ret rest =
      CiosCachedTailDefs.nxJdState s mem pbi 2048 n (UInt256.ofNat 4734) ent inv m0
        (tl :: m96 :: m64 :: m32 :: aprev :: pdst :: ret :: rest) := rfl

/-! ## Programs -/

/-- `sq_exit` (4656): load the counter, decrement, store it back, branch to `more`. -/
def sqExitProgram : List Instr :=
  [.op .JUMPDEST, .push 2 9280, .op .MLOAD, .op (.Dup ⟨6, by decide⟩), .op .ADD,
   .op (.Dup ⟨0, by decide⟩), .push 2 9280, .op .MSTORE, .push 2 4692, .op .JUMPI]

/-- `last` (4673): the frame's `ret` slot becomes `after_sq`, then leave through `nx`. -/
def lastProgram : List Instr :=
  [.push 2 3222, .op (.Swap ⟨15, by decide⟩), .op .POP, .push 2 4609, .op .JUMP]

/-- `more` (4728): call the CSUB as a subroutine returning to `again`. -/
def moreProgram : List Instr :=
  [.op .JUMPDEST, .push 2 4701, .op (.Dup ⟨15, by decide⟩), .push 2 4624, .op .JUMP]

/-- `again` (4737): re-stage, re-zero, reset three frame slots, fall into `sq_row`. -/
def againProgram : List Instr :=
  [.op .JUMPDEST, .push 2 9344, .op .MLOAD, .op (.Dup ⟨0, by decide⟩), .push 2 2048,
   .push 2 8960, .op .MCOPY,
   .op (.Dup ⟨0, by decide⟩), .push 1 64, .op .ADD, .op .CALLDATASIZE, .push 2 8192,
   .op .CALLDATACOPY,
   .op .ADD, .push 2 299, .op (.Dup ⟨7, by decide⟩), .op .SUB,
   .op (.Swap ⟨3, by decide⟩), .op .POP,
   .push 0 0, .op (.Swap ⟨13, by decide⟩), .op .POP]

/-! ## Located blocks -/

def sqExitBlock : Block Artifact.submissionArtifact .Osaka 4667 sqExitProgram :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3582 10 4667 sqExitProgram
    (by decide) (by rfl) (by rfl) (by decide)

def lastBlock : Block Artifact.submissionArtifact .Osaka 4683 lastProgram :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3592 5 4683 lastProgram
    (by decide) (by rfl) (by rfl) (by decide)

def moreBlock : Block Artifact.submissionArtifact .Osaka 4692 moreProgram :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3597 5 4692 moreProgram
    (by decide) (by rfl) (by rfl) (by decide)

def againBlock : Block Artifact.submissionArtifact .Osaka 4701 againProgram :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3602 22 4701 againProgram
    (by decide) (by rfl) (by rfl) (by decide)

/-! ## Jump destinations of the loop -/

theorem jumpDest4753 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 4692 = true :=
  Artifact.isValidJumpDest_index 3597 (by rfl)

theorem jumpDest4762 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 4701 = true :=
  Artifact.isValidJumpDest_index 3602 (by rfl)

theorem jumpDest3272 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3222 = true :=
  Artifact.isValidJumpDest_index 2481 (by rfl)

theorem jumpDest4683 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 4624 = true :=
  Artifact.isValidJumpDest_index 3554 (by rfl)

/-! ## The counter word -/

/-- The memory after `sq_exit`'s `MSTORE`: the counter word 9280 holds `c`. -/
def countMem (mem : ByteArray) (c : Nat) : ByteArray :=
  MachineState.writeBytes mem (Data.Bytes.natToBytesPadded c 32) 9280

theorem readWord_countMem (mem : ByteArray) (c : Nat) (hc : c < 2 ^ 256) :
    MachineState.readWord (countMem mem c) 9280 = UInt256.ofNat c := by
  have h : (UInt256.ofNat c).toNat = c := by
    rw [Challenge.EvmProof.Word.word_toNat_ofNat, Nat.mod_eq_of_lt hc]
  calc MachineState.readWord (countMem mem c) 9280
      = MachineState.readWord
          (MachineState.writeBytes mem
            (Data.Bytes.natToBytesPadded (UInt256.ofNat c).toNat 32) 9280) 9280 := by
        rw [countMem, h]
    _ = UInt256.ofNat c := Challenge.EvmProof.Memory.readWord_writeWord mem 9280 (UInt256.ofNat c)

theorem readWord_countMem_disjoint (mem : ByteArray) (c addr : Nat)
    (hd : addr + 32 ≤ 9280 ∨ 9312 ≤ addr) :
    MachineState.readWord (countMem mem c) addr = MachineState.readWord mem addr := by
  simp only [countMem]
  apply Challenge.EvmProof.Memory.readWord_writeBytes_disjoint
  rw [show (Data.Bytes.natToBytesPadded c 32).size = 32 by
    simp [Data.Bytes.natToBytesPadded, ByteArray.size]]
  omega

end Challenge.Modexp.Submission.Proofs.Fast.SquareLoopBlocks
