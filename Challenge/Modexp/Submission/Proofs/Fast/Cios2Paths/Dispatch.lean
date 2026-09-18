import Challenge.Modexp.Submission.Proofs.Fast.CiosInverseGuard
import Challenge.Modexp.Submission.Proofs.Fast.Defs
import Challenge.Modexp.Submission.Proofs.Bytecode.WindowTwentyOneSlice
set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000

/-!
# The kernel's `mul entry` and shared `common` width guard (sqCP1m)

* `mul entry` (instruction 3190, pc 4013 = 0x0f50): `JUMPDEST; PUSH2 0x0fc5` pushes the
  multiply row head `hd = 4261` and falls through into `common`.
* `common` (instruction 3190, pc 4104 = 0x0f54, also entered directly by the square call
  with `hd = 2464`): `JUMPDEST; PUSH2 0x2480; MLOAD; DUP1; PUSH1 0x80; EQ; SWAP1;
  PUSH2 0x100; EQ; OR; PUSH2 0x0f6c; JUMPI` — widths of four and eight limbs jump to the
  kernel `setup` (pc 4123).
* fallback (instruction 3190, pc 3899): `POP; PUSH2 0x0683; JUMP` drops `hd` and enters the
  generic `MONPRO` at pc 1746.
-/

namespace Challenge.Modexp.Submission.Proofs.Fast.Cios2Paths.Dispatch

open EvmSemantics EvmSemantics.EVM YulEvmCompiler
open Challenge.Modexp.Submission.Proofs.Bytecode
open Challenge.Modexp.Submission.Proofs.Fast
open WindowTwentyOneBinding

-- `mulEntryProgram` and `mulEntry` are DELETED, not renumbered.  They asserted a block
-- `[JUMPDEST, PUSH2 <mul row head>]` at instruction 2386 / pc 3209.  Every part of that is
-- false in this artifact, measured four independent ways:
--   * instruction 2386 is pc 2919 (`MULMOD`), not pc 3209;
--   * pc 3209 decodes to `ISZERO`, so it is not a jump destination at all;
--   * `JUMPDEST; PUSH2 3465` occurs ZERO times -- 3465, the multiply row head, is pushed
--     EXACTLY ONCE in the whole 5,428-byte program, at instruction 2766, INSIDE THE FUSED
--     FRAME PROGRAM at pc 3414..3454.  The entry's `PUSH2` was hoisted there; there is no
--     entry block left to give a new number to.
--   * `common` (pc 3327) is jumped to from exactly ONE site in the artifact --
--     `PUSH2 800; PUSH2 512; DUP1; DUP1; PUSH2 4480; PUSH2 3327; JUMP` -- and that site is
--     the SQUARE call.  Nothing enters `common` as a multiply.
-- This is absence of code, not a wrong constant, so relocating was impossible rather than
-- merely unknown.  Its cone -- Cios2Dispatch.{dispatchState, jumpDest4012, run_mulEntry,
-- gasSteps_mulEntry, gasSteps_dispatch4/8, gasSteps_mulSetup} ->
-- CarryIface.EntryLemmas.gasSteps_mulEntry -> CarryFullSpecializedFour/Eight ->
-- CarryFullFast -> ExpSubs.subsMonpro -> Exp.Subroutines.monpro -- terminates in ZERO
-- consumers tree-wide, so nothing downstream loses a fact it was using.
-- `commonGuard` below is CORRECT and stays: instruction 2696 IS pc 3327.

/-- The thirteen-instruction inverse/width guard is gone: the rewritten entry test decides both
conditions before the fast path is entered, so `common` now falls straight through into `setup`. -/
def commonGuardProgram : List Instr := [.op .JUMPDEST]


def commonGuard : Block Artifact.submissionArtifact .Osaka 3327 commonGuardProgram :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 2652 1 3327 commonGuardProgram
    (by decide) (by rfl) (by rfl) (by decide)


end Challenge.Modexp.Submission.Proofs.Fast.Cios2Paths.Dispatch
