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

/-- pc 3650..3664, indices 2392..2403: size/top-bit guard. -/
def blkFullBaseGuard :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2392 .JUMPDEST,
   opAt 2393 (.Dup ⟨0, by decide⟩),
   opAt 2394 (.Dup ⟨3, by decide⟩),
   opAt 2395 .EQ,
   pushAt 2396 0 0,
   opAt 2397 .MLOAD,
   pushAt 2398 1 255,
   opAt 2399 .SHR,
   opAt 2400 .AND,
   opAt 2401 .ISZERO,
   pushAt 2402 2 3705,
   opAt 2403 .JUMPI]

/-- pc 3665..3687, indices 2404..2413: copy the base to ACC and call
the existing add-mod routine with ZERO as its second operand. -/
def blkFullBaseCopyAdd :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2404 (.Dup ⟨0, by decide⟩),
   pushAt 2405 1 96,
   pushAt 2406 2 1024,
   opAt 2407 .CALLDATACOPY,
   pushAt 2408 2 3688,
   pushAt 2409 2 1024,
   pushAt 2410 2 3072,
   pushAt 2411 2 1024,
   pushAt 2412 2 2511,
   opAt 2413 .JUMP]

/-- pc 3688..3704, indices 2414..2420: after add-mod, convert ACC to the
Montgomery BASE block and rejoin at pc 1755. -/
def blkFullBaseAfterAdd :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2414 .JUMPDEST,
   pushAt 2415 2 1755,
   pushAt 2416 2 2048,
   pushAt 2417 2 6144,
   pushAt 2418 2 1024,
   pushAt 2419 2 1939,
   opAt 2420 .JUMP]

/-- pc 3705..3738, indices 2421..2444: relocated original base-head
computation and the jump to the unchanged loop head. -/
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
   pushAt 2443 2 1668,
   opAt 2444 .JUMP]

end Challenge.Modexp.Submission.Proofs.Fast
