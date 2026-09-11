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
  [opAt 2354 .JUMPDEST,
   opAt 2355 (.Dup ⟨0, by decide⟩),
   opAt 2356 (.Dup ⟨3, by decide⟩),
   opAt 2357 .EQ,
   pushAt 2358 0 0,
   opAt 2359 .MLOAD,
   pushAt 2360 1 255,
   opAt 2361 .SHR,
   opAt 2362 .AND,
   opAt 2363 .ISZERO,
   pushAt 2364 2 3096,
   opAt 2365 .JUMPI]

/-- Located block in the selected full-width-base helper. -/
def blkFullBaseCopyAdd :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2366 (.Dup ⟨0, by decide⟩),
   pushAt 2367 1 96,
   pushAt 2368 2 1024,
   opAt 2369 .CALLDATACOPY,
   pushAt 2370 2 1616,
   pushAt 2371 2 2048,
   pushAt 2372 2 1024,
   pushAt 2373 2 6144,
   pushAt 2374 2 4049,
   opAt 2375 .JUMP]

/-- Located block in the selected full-width-base helper. -/
def blkFullBaseFallback :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2376 .JUMPDEST,
   opAt 2377 (.Dup ⟨2, by decide⟩),
   pushAt 2378 1 31,
   opAt 2379 .ADD,
   pushAt 2380 1 5,
   opAt 2381 .SHR,
   opAt 2382 (.Dup ⟨3, by decide⟩),
   opAt 2383 (.Dup ⟨1, by decide⟩),
   pushAt 2384 1 5,
   opAt 2385 .SHL,
   opAt 2386 .SUB,
   pushAt 2387 1 3,
   opAt 2388 .SHL,
   pushAt 2389 1 96,
   opAt 2390 .CALLDATALOAD,
   opAt 2391 (.Swap ⟨0, by decide⟩),
   opAt 2392 .SHR,
   opAt 2393 (.Dup ⟨2, by decide⟩),
   pushAt 2394 2 992,
   opAt 2395 .ADD,
   opAt 2396 .MSTORE,
   pushAt 2397 1 1,
   pushAt 2398 2 1530,
   opAt 2399 .JUMP]

end Challenge.Modexp.Submission.Proofs.Fast
