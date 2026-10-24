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

def block0 : Block Artifact.submissionArtifact .Osaka 2785 ([.op .JUMPDEST] ++ rideTopProgram 10 2336) :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 2157 18 2785 ([.op .JUMPDEST] ++ rideTopProgram 10 2336)
    (by decide) (by rfl) (by rfl) (by decide)

def block1 : Block Artifact.submissionArtifact .Osaka 2805 (rideProgram 10 2304) :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 2175 28 2805 (rideProgram 10 2304)
    (by decide) (by rfl) (by rfl) (by decide)

def block2 : Block Artifact.submissionArtifact .Osaka 2837 (rideProgram 9 2272) :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 2203 28 2837 (rideProgram 9 2272)
    (by decide) (by rfl) (by rfl) (by decide)

def block3 : Block Artifact.submissionArtifact .Osaka 2869 (rideProgram 8 2240) :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 2231 28 2869 (rideProgram 8 2240)
    (by decide) (by rfl) (by rfl) (by decide)

def block4 : Block Artifact.submissionArtifact .Osaka 2901 ([.op .JUMPDEST] ++ rideProgram 7 2208) :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 2259 29 2901 ([.op .JUMPDEST] ++ rideProgram 7 2208)
    (by decide) (by rfl) (by rfl) (by decide)

def block5 : Block Artifact.submissionArtifact .Osaka 2934 (rideProgram 6 2176) :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 2288 28 2934 (rideProgram 6 2176)
    (by decide) (by rfl) (by rfl) (by decide)

def block6 : Block Artifact.submissionArtifact .Osaka 2966 (rideProgram 5 2144) :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 2316 28 2966 (rideProgram 5 2144)
    (by decide) (by rfl) (by rfl) (by decide)

def block7 : Block Artifact.submissionArtifact .Osaka 2998 (blockProgram 1280 2112) :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 2344 30 2998 (blockProgram 1280 2112)
    (by decide) (by rfl) (by rfl) (by decide)

def exitBlock : Block Artifact.submissionArtifact .Osaka 3034 exitProgram :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 2374 0 3034 exitProgram
    (by decide) (by rfl) (by rfl) (by decide)

def entryBlock : Block Artifact.submissionArtifact .Osaka 2782 entryProgram :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 2154 3 2782 entryProgram
    (by decide) (by rfl) (by rfl) (by decide)

theorem jumpDest2899 : Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 2785 = true :=
  Artifact.isValidJumpDest_index 2157 (by rfl)

theorem jumpDest3032 : Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 2901 = true :=
  Artifact.isValidJumpDest_index 2259 (by rfl)

end Challenge.Modexp.Submission.Proofs.Fast.M9Mac

