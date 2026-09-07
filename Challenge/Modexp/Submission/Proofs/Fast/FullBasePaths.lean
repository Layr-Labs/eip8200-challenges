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

/-- pc 3635..3649, indices 2386..2397: size/top-bit guard. -/
def blkFullBaseGuard :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2386 .JUMPDEST,
   opAt 2387 (.Dup ⟨0, by decide⟩),
   opAt 2388 (.Dup ⟨3, by decide⟩),
   opAt 2389 .EQ,
   pushAt 2390 0 0,
   opAt 2391 .MLOAD,
   pushAt 2392 1 255,
   opAt 2393 .SHR,
   opAt 2394 .AND,
   opAt 2395 .ISZERO,
   pushAt 2396 2 3690,
   opAt 2397 .JUMPI]

/-- pc 3650..3672, indices 2398..2407: copy the base to ACC and call
the existing add-mod routine with ZERO as its second operand. -/
def blkFullBaseCopyAdd :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2398 (.Dup ⟨0, by decide⟩),
   pushAt 2399 1 96,
   pushAt 2400 2 1024,
   opAt 2401 .CALLDATACOPY,
   pushAt 2402 2 3673,
   pushAt 2403 2 1024,
   pushAt 2404 2 3072,
   pushAt 2405 2 1024,
   pushAt 2406 2 2496,
   opAt 2407 .JUMP]

/-- pc 3673..3689, indices 2408..2414: after add-mod, convert ACC to the
Montgomery BASE block and rejoin at pc 1755. -/
def blkFullBaseAfterAdd :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2408 .JUMPDEST,
   pushAt 2409 2 1755,
   pushAt 2410 2 2048,
   pushAt 2411 2 6144,
   pushAt 2412 2 1024,
   pushAt 2413 2 1939,
   opAt 2414 .JUMP]

/-- pc 3690..3723, indices 2415..2438: relocated original base-head
computation and the jump to the unchanged loop head. -/
def blkFullBaseFallback :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2415 .JUMPDEST,
   opAt 2416 (.Dup ⟨2, by decide⟩),
   pushAt 2417 1 31,
   opAt 2418 .ADD,
   pushAt 2419 1 5,
   opAt 2420 .SHR,
   opAt 2421 (.Dup ⟨3, by decide⟩),
   opAt 2422 (.Dup ⟨1, by decide⟩),
   pushAt 2423 1 5,
   opAt 2424 .SHL,
   opAt 2425 .SUB,
   pushAt 2426 1 3,
   opAt 2427 .SHL,
   pushAt 2428 1 96,
   opAt 2429 .CALLDATALOAD,
   opAt 2430 (.Swap ⟨0, by decide⟩),
   opAt 2431 .SHR,
   opAt 2432 (.Dup ⟨2, by decide⟩),
   pushAt 2433 2 992,
   opAt 2434 .ADD,
   opAt 2435 .MSTORE,
   pushAt 2436 1 1,
   pushAt 2437 2 1668,
   opAt 2438 .JUMP]

end Challenge.Modexp.Submission.Proofs.Fast
