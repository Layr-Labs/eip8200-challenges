import Challenge.Modexp.Submission.Proofs.Fast.M9MacPrograms
import Challenge.Modexp.Submission.Proofs.Bytecode.Artifact
import Challenge.Modexp.Submission.Proofs.Bytecode.WindowTwentyOneSlice

set_option warningAsError true
set_option maxRecDepth 40000

/-!
# M9: located certificates of the eight straight MAC blocks, the exit and the E6 entry
(regenerated from `TnM128CandidateArtifact.submissionInstructions`; do not edit by hand)

Every certificate is `WindowTwentyOneSlice.block Artifact.allWellFormed <index> <count> <pc> <program>`,
the shape of `KernelChainBlocks.l1Block1..7`: the instruction slice at `<index>` decodes to `<program>` (`rfl`),
`instructionPC <index> = <pc>` (`rfl`), and the program is linear except possibly its last instruction.

Phase 9/10 chunk mirroring: blocks 0–6 no longer `MLOAD` their `-N` limb — the limb rides
in one of the seventeen window slots (`Dup 11` .. `Dup 5`); block 7 (`0x500`) is not a riding
slot and keeps `loadProgram 1280`.  E6 jumps through the scratch slot (`Dup 5`) instead of
the `0x6a2` cache word.

## Assumed from the tree (artifact-side; the port tree must carry the M9-T13 artifact,
raw sha256 ad60d3dac181092e39562b72c2003578a87e3734cffecc962593cd33f56332f7, 3981 instruction rows)
* `Challenge.Modexp.Submission.Proofs.Bytecode.Artifact.submissionArtifact : Challenge.EvmProof.ProgramArtifact`,
  `Artifact.submissionInstructions : List Instr` (3981 rows), `Artifact.allWellFormed`,
  `Artifact.isValidJumpDest_index (index) (hget : submissionInstructions[index]? = some (.op .JUMPDEST))`.
* `Challenge.Modexp.submissionBytecode : ByteArray` (= the 5165 M9-T13 bytes).
* `Challenge.Modexp.Submission.Proofs.Bytecode.WindowTwentyOneBinding.Block (artifact) (fork) (pc : Nat) (instructions)`
  and `WindowTwentyOneSlice.block` (`Proofs/Bytecode/WindowTwentyOneSlice.lean`).
-/

namespace Challenge.Modexp.Submission.Proofs.Fast.M9Mac

open EvmSemantics EvmSemantics.EVM YulEvmCompiler
open Challenge.Modexp.Submission.Proofs.Bytecode WindowTwentyOneBinding

/-- Block 0: instructions 2329..2358, pc 2899..2932 (JUMPDEST included),
`-N` limb riding in slot 7 (`Dup 12`, address 1504 = 0x5e0), `t` limb at 2336 (0x920).

Block 0 carries the `PUSH0` schedule (`rideZeroProgram`): it is the row head of every chain
that reaches it, so its incoming carry is the literal zero `entryProgram` pushes.  Block 4
keeps the fused schedule — pc 3032 is both jumped to (four limbs, carry zero) and fallen into
from block 3 (carry nonzero). -/
def block0 : Block Artifact.submissionArtifact .Osaka 2899 ([.op .JUMPDEST] ++ rideZeroProgram 11 2336) :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 2329 30 2899 ([.op .JUMPDEST] ++ rideZeroProgram 11 2336)
    (by decide) (by rfl) (by rfl) (by decide)

/-- Block 1: instructions 2359..2387, pc 2933..2965,
`-N` limb riding in slot 6 (`Dup 11`, address 1472 = 0x5c0), `t` limb at 2304. -/
def block1 : Block Artifact.submissionArtifact .Osaka 2933 (rideProgram 10 2304) :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 2359 29 2933 (rideProgram 10 2304)
    (by decide) (by rfl) (by rfl) (by decide)

/-- Block 2: instructions 2388..2416, pc 2966..2998,
`-N` limb riding in slot 5 (`Dup 10`, address 1440 = 0x5a0), `t` limb at 2272. -/
def block2 : Block Artifact.submissionArtifact .Osaka 2966 (rideProgram 9 2272) :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 2388 29 2966 (rideProgram 9 2272)
    (by decide) (by rfl) (by rfl) (by decide)

/-- Block 3: instructions 2417..2445, pc 2999..3031,
`-N` limb riding in slot 4 (`Dup 9`, address 1408 = 0x580), `t` limb at 2240. -/
def block3 : Block Artifact.submissionArtifact .Osaka 2999 (rideProgram 8 2240) :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 2417 29 2999 (rideProgram 8 2240)
    (by decide) (by rfl) (by rfl) (by decide)

/-- Block 4: instructions 2446..2475, pc 3032..3065 (JUMPDEST included),
`-N` limb riding in slot 3 (`Dup 8`, address 1376 = 0x560), `t` limb at 2208. -/
def block4 : Block Artifact.submissionArtifact .Osaka 3032 ([.op .JUMPDEST] ++ rideProgram 7 2208) :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 2446 30 3032 ([.op .JUMPDEST] ++ rideProgram 7 2208)
    (by decide) (by rfl) (by rfl) (by decide)

/-- Block 5: instructions 2476..2504, pc 3066..3098,
`-N` limb riding in slot 2 (`Dup 7`, address 1344 = 0x540), `t` limb at 2176. -/
def block5 : Block Artifact.submissionArtifact .Osaka 3066 (rideProgram 6 2176) :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 2476 29 3066 (rideProgram 6 2176)
    (by decide) (by rfl) (by rfl) (by decide)

/-- Block 6: instructions 2505..2533, pc 3099..3131,
`-N` limb riding in slot 1 (`Dup 6`, address 1312 = 0x520), `t` limb at 2144. -/
def block6 : Block Artifact.submissionArtifact .Osaka 3099 (rideProgram 5 2144) :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 2505 29 3099 (rideProgram 5 2144)
    (by decide) (by rfl) (by rfl) (by decide)

/-- Block 7: instructions 2534..2563, pc 3132..3167 — the one `MLOAD` block left:
`0x500 = 1280` is not a riding slot, `t` limb at 2112 (0x840). -/
def block7 : Block Artifact.submissionArtifact .Osaka 3132 (blockProgram 1280 2112) :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 2534 30 3132 (blockProgram 1280 2112)
    (by decide) (by rfl) (by rfl) (by decide)

/-- The exit `SWAP1 SWAP2 POP`: instructions 2564..2566, pc 3168..3170; falls into pc 3171. -/
def exitBlock : Block Artifact.submissionArtifact .Osaka 3168 exitProgram :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 2564 3 3168 exitProgram
    (by decide) (by rfl) (by rfl) (by decide)

/-- E6, the section entry: instructions 2323..2328, pc 2893..2898 (`Dup 5` = the scratch slot). -/
def entryBlock : Block Artifact.submissionArtifact .Osaka 2893 entryProgram :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 2323 6 2893 entryProgram
    (by decide) (by rfl) (by rfl) (by decide)

/-- The eight-limb entry (block 0's `JUMPDEST`, instruction 2329). -/
theorem jumpDest2899 : Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 2899 = true :=
  Artifact.isValidJumpDest_index 2329 (by rfl)

/-- The four-limb entry (block 4's `JUMPDEST`, instruction 2446, = 2899 + 133). -/
theorem jumpDest3032 : Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3032 = true :=
  Artifact.isValidJumpDest_index 2446 (by rfl)

end Challenge.Modexp.Submission.Proofs.Fast.M9Mac

#print axioms Challenge.Modexp.Submission.Proofs.Fast.M9Mac.block0
#print axioms Challenge.Modexp.Submission.Proofs.Fast.M9Mac.block7
#print axioms Challenge.Modexp.Submission.Proofs.Fast.M9Mac.exitBlock
#print axioms Challenge.Modexp.Submission.Proofs.Fast.M9Mac.entryBlock
#print axioms Challenge.Modexp.Submission.Proofs.Fast.M9Mac.jumpDest2899
#print axioms Challenge.Modexp.Submission.Proofs.Fast.M9Mac.jumpDest3032
