import Challenge.Modexp.Submission.Proofs.Fast.Paths.P4
set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000
/-!
# Located paths for the full-width-base helper

The helper is appended after the fixed-window and direct-RR helpers. Its miss
path reproduces the original base-head computation before jumping to the
unchanged base loop at pc 1668.
-/

namespace Challenge.Modexp.Submission.Proofs.Fast

open EvmSemantics
open EvmSemantics.EVM
open Challenge.Modexp.Submission.Proofs.Bytecode

/-- Located block in the selected full-width-base helper. -/
def blkFullBaseGuard :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2399 .JUMPDEST,
   opAt 2400 (.Dup ⟨0, by decide⟩),
   opAt 2401 (.Dup ⟨3, by decide⟩),
   opAt 2402 .EQ,
   pushAt 2403 0 0,
   opAt 2404 .MLOAD,
   pushAt 2405 1 255,
   opAt 2406 .SHR,
   opAt 2407 .AND,
   opAt 2408 .ISZERO,
   pushAt 2409 2 3184,
   opAt 2410 .JUMPI]

/-- Located block in the selected full-width-base helper. -/
def blkFullBaseCopyAdd :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2411 (.Dup ⟨0, by decide⟩),
   pushAt 2412 1 96,
   pushAt 2413 2 1024,
   opAt 2414 .CALLDATACOPY,
   pushAt 2415 2 1697,
   pushAt 2416 2 2048,
   pushAt 2417 2 1024,
   pushAt 2418 2 6144,
   pushAt 2419 2 4137,
   opAt 2420 .JUMP]

/-- Located block in the selected full-width-base helper. -/
def blkFullBaseFallback :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2421 .JUMPDEST,
   opAt 2422 (.Dup ⟨2, by decide⟩),
   pushAt 2423 1 31,
   opAt 2424 .ADD,
   pushAt 2425 1 5,
   opAt 2426 .SHR,
   opAt 2427 (.Dup ⟨3, by decide⟩),
   opAt 2428 (.Dup ⟨1, by decide⟩),
   pushAt 2429 1 5,
   opAt 2430 .SHL,
   opAt 2431 .SUB,
   pushAt 2432 1 3,
   opAt 2433 .SHL,
   pushAt 2434 1 96,
   opAt 2435 .CALLDATALOAD,
   opAt 2436 (.Swap ⟨0, by decide⟩),
   opAt 2437 .SHR,
   opAt 2438 (.Dup ⟨2, by decide⟩),
   pushAt 2439 2 992,
   opAt 2440 .ADD,
   opAt 2441 .MSTORE,
   pushAt 2442 1 1,
   pushAt 2443 2 1611,
   opAt 2444 .JUMP]

end Challenge.Modexp.Submission.Proofs.Fast
