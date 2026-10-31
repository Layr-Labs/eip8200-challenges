import Challenge.Modexp.Submission.Proofs.CycleGlobal.Binding
import Challenge.Modexp.Submission.Proofs.Fast.M9MacPrograms
import Challenge.Modexp.Submission.Proofs.Fast.M9MacRun
import Challenge.Modexp.Submission.Proofs.Bytecode.Artifact
import Challenge.Modexp.Submission.Proofs.Bytecode.WindowTwentyOneSlice

noncomputable section
set_option warningAsError true
set_option maxRecDepth 40000

/-!
# M9: located certificates of the eight straight MAC blocks, the exit and the E6 entry
(regenerated from `TnM128CandidateArtifact.submissionInstructions`; do not edit by hand)

Every certificate is `WindowTwentyOneSlice.block CycleSubmission.Artifact.wellFormed <index> <count> <pc> <program>`,
the shape of `KernelChainBlocks.l1Block1..7`: the instruction slice at `<index>` decodes to `<program>` (`rfl`),
`instructionPC <index> = <pc>` (`rfl`), and the program is linear except possibly its last instruction.

Phase 9/10 chunk mirroring: blocks 0–6 no longer `MLOAD` their `-N` limb — the limb rides
in one of the seventeen window slots (`Dup 11` .. `Dup 5`); block 7 (`0x500`) is not a riding
slot and keeps `loadProgram 1280`.  E6 jumps through the scratch slot (`Dup 5`) instead of
the `0x6a2` cache word.

## Assumed from the tree (artifact-side; the port tree must carry the M9-T13 artifact,
raw sha256 ad60d3dac181092e39562b72c2003578a87e3734cffecc962593cd33f56332f7, 3981 instruction rows)
* `Challenge.Modexp.Submission.Proofs.Bytecode.Artifact.submissionArtifact : Challenge.EvmProof.ProgramArtifact`,
  `CycleSubmission.Artifact.instructions : List Instr` (3981 rows), `CycleSubmission.Artifact.wellFormed`,
  `CycleSubmission.Global.Binding.jumpDest (index) (hget : submissionInstructions[index]? = some (.op .JUMPDEST))`.
* `CycleSubmission.Artifact.bytecode : ByteArray` (= the 5165 M9-T13 bytes).
* `Challenge.Modexp.Submission.Proofs.Bytecode.WindowTwentyOneBinding.Block (artifact) (fork) (pc : Nat) (instructions)`
  and `WindowTwentyOneSlice.block` (`Proofs/Bytecode/WindowTwentyOneSlice.lean`).
-/

namespace CycleSubmission.Global.Fast.M9Mac
open Challenge.Modexp
open Challenge.Modexp.Submission.Proofs
open Challenge.Modexp.Submission.Proofs.Bytecode
open Challenge.Modexp.Submission.Proofs.Fast
open CycleSubmission.Global.Fast
open Challenge.Modexp.Submission.Proofs.Fast.M9Mac


open EvmSemantics EvmSemantics.EVM YulEvmCompiler
open Challenge.Modexp.Submission.Proofs.Bytecode WindowTwentyOneBinding

/-- Block 0: instructions 2329..2358, pc 2899..2932 (JUMPDEST included),
`-N` limb riding in slot 7 (`Dup 12`, address 1504 = 0x5e0), `t` limb at 2336 (0x920).

Block 0 carries the top-word schedule (`rideTopProgram`): it is the row head of every chain
that reaches it, so its incoming carry is the literal zero `entryProgram` pushes and the
accumulator word it reads (`0x920`) is the limb the shift just zeroed.  It pops the carry, so
the limb rides in `Dup 10`.  Block 4 keeps the fused schedule — pc 3032 is both jumped to
(four limbs, carry zero) and fallen into from block 3 (carry nonzero). -/
def block0 : Block CycleSubmission.Artifact.artifact .Osaka 2787 (rideTopProgramNP 10 2336) :=
  WindowTwentyOneSlice.block CycleSubmission.Artifact.wellFormed 2147 16 2787 (rideTopProgramNP 10 2336)
    (by decide) (by rfl) (by rfl) (by decide)

/-- Block 1: instructions 2347..2374, pc 2933..2965,
`-N` limb riding in slot 6 (`Dup 11`, address 1472 = 0x5c0), `t` limb at 2304. -/
def block1 : Block CycleSubmission.Artifact.artifact .Osaka 2805 (rideProgram 10 2304) :=
  WindowTwentyOneSlice.block CycleSubmission.Artifact.wellFormed 2163 28 2805 (rideProgram 10 2304)
    (by decide) (by rfl) (by rfl) (by decide)

/-- Block 2: instructions 2375..2402, pc 2966..2998,
`-N` limb riding in slot 5 (`Dup 10`, address 1440 = 0x5a0), `t` limb at 2272. -/
def block2 : Block CycleSubmission.Artifact.artifact .Osaka 2837 (rideProgram 9 2272) :=
  WindowTwentyOneSlice.block CycleSubmission.Artifact.wellFormed 2191 28 2837 (rideProgram 9 2272)
    (by decide) (by rfl) (by rfl) (by decide)

/-- Block 3: instructions 2403..2430, pc 2999..3031,
`-N` limb riding in slot 4 (`Dup 9`, address 1408 = 0x580), `t` limb at 2240. -/
def block3 : Block CycleSubmission.Artifact.artifact .Osaka 2869 (rideProgram 8 2240) :=
  WindowTwentyOneSlice.block CycleSubmission.Artifact.wellFormed 2219 28 2869 (rideProgram 8 2240)
    (by decide) (by rfl) (by rfl) (by decide)

/-- Block 4: instructions 2247..2274, pc 2901..2932 (eight limbs only; the four-limb head runs
its own zero-carry copy), `-N` limb riding in slot 3 (`Dup 8`, address 1376 = 0x560), `t` limb at 2208. -/
def block4 : Block CycleSubmission.Artifact.artifact .Osaka 2901 (rideProgram 7 2208) :=
  WindowTwentyOneSlice.block CycleSubmission.Artifact.wellFormed 2247 28 2901 (rideProgram 7 2208)
    (by decide) (by rfl) (by rfl) (by decide)

/-- Block 5: instructions 2460..2487, pc 3066..3098,
`-N` limb riding in slot 2 (`Dup 7`, address 1344 = 0x540), `t` limb at 2176. -/
def block5 : Block CycleSubmission.Artifact.artifact .Osaka 2933 (rideProgramW3 6 2176) :=
  WindowTwentyOneSlice.block CycleSubmission.Artifact.wellFormed 2275 28 2933 (rideProgramW3 6 2176)
    (by decide) (by rfl) (by rfl) (by decide)

/-- Block 6: instructions 2488..2515, pc 3099..3131,
`-N` limb riding in slot 1 (`Dup 6`, address 1312 = 0x520), `t` limb at 2144. -/
def block6 : Block CycleSubmission.Artifact.artifact .Osaka 2966 (rideProgram 5 2144) :=
  WindowTwentyOneSlice.block CycleSubmission.Artifact.wellFormed 2303 28 2966 (rideProgram 5 2144)
    (by decide) (by rfl) (by rfl) (by decide)

/-- Block 7: instructions 2516..2545, pc 3132..3167 — the one `MLOAD` block left:
`0x500 = 1280` is not a riding slot, `t` limb at 2112 (0x840). -/
def block7 : Block CycleSubmission.Artifact.artifact .Osaka 2998 (blockProgram 1280 2112) :=
  WindowTwentyOneSlice.block CycleSubmission.Artifact.wellFormed 2331 30 2998 (blockProgram 1280 2112)
    (by decide) (by rfl) (by rfl) (by decide)

/-- The exit: empty program at pc 3168. -/
def exitBlock : Block CycleSubmission.Artifact.artifact .Osaka 3034 exitProgram :=
  WindowTwentyOneSlice.block CycleSubmission.Artifact.wellFormed 2361 0 3034 exitProgram
    (by decide) (by rfl) (by rfl) (by decide)

/-- E6, the section entry: instructions 2325..2328, pc 2895..2898 (`Dup 5` = the scratch slot). -/
def zero4Block : Block CycleSubmission.Artifact.artifact .Osaka 10827 (rideTopProgramNP 6 2208) :=
  WindowTwentyOneSlice.block CycleSubmission.Artifact.wellFormed 8600 16 10827 (rideTopProgramNP 6 2208)
    (by decide) (by rfl) (by rfl) (by decide)

set_option maxHeartbeats 4000000 in
/-- The four-limb private copies of blocks 5..7 (instructions 8622.., pc 10845..10944). -/
def block5c : Block CycleSubmission.Artifact.artifact .Osaka 10845 (rideProgram 6 2176) :=
  WindowTwentyOneSlice.block CycleSubmission.Artifact.wellFormed 8616 28 10845 (rideProgram 6 2176)
    (by decide) (by rfl) (by rfl) (by decide)

set_option maxHeartbeats 4000000 in
def block6c : Block CycleSubmission.Artifact.artifact .Osaka 10877 (rideProgram 5 2144) :=
  WindowTwentyOneSlice.block CycleSubmission.Artifact.wellFormed 8644 28 10877 (rideProgram 5 2144)
    (by decide) (by rfl) (by rfl) (by decide)

set_option maxHeartbeats 4000000 in
def block7c : Block CycleSubmission.Artifact.artifact .Osaka 10909 (blockProgram 1280 2112) :=
  WindowTwentyOneSlice.block CycleSubmission.Artifact.wellFormed 8672 30 10909 (blockProgram 1280 2112)
    (by decide) (by rfl) (by rfl) (by decide)

end CycleSubmission.Global.Fast.M9Mac

