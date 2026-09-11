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
  [opAt 2352 .JUMPDEST,
   opAt 2353 (.Dup ⟨0, by decide⟩),
   opAt 2354 (.Dup ⟨3, by decide⟩),
   opAt 2355 .EQ,
   pushAt 2356 0 0,
   opAt 2357 .MLOAD,
   pushAt 2358 1 255,
   opAt 2359 .SHR,
   opAt 2360 .AND,
   opAt 2361 .ISZERO,
   pushAt 2362 2 3096,
   opAt 2363 .JUMPI]

/-- Located block in the selected full-width-base helper. -/
def blkFullBaseCopyAdd :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2364 (.Dup ⟨0, by decide⟩),
   pushAt 2365 1 96,
   pushAt 2366 2 1024,
   opAt 2367 .CALLDATACOPY,
   pushAt 2368 2 1616,
   pushAt 2369 2 2048,
   pushAt 2370 2 1024,
   pushAt 2371 2 6144,
   pushAt 2372 2 4053,
   opAt 2373 .JUMP]

/-- Located block in the selected full-width-base helper. -/
def blkFullBaseFallback :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2374 .JUMPDEST,
   opAt 2375 (.Dup ⟨2, by decide⟩),
   pushAt 2376 1 31,
   opAt 2377 .ADD,
   pushAt 2378 1 5,
   opAt 2379 .SHR,
   opAt 2380 (.Dup ⟨3, by decide⟩),
   opAt 2381 (.Dup ⟨1, by decide⟩),
   pushAt 2382 1 5,
   opAt 2383 .SHL,
   opAt 2384 .SUB,
   pushAt 2385 1 3,
   opAt 2386 .SHL,
   pushAt 2387 1 96,
   opAt 2388 .CALLDATALOAD,
   opAt 2389 (.Swap ⟨0, by decide⟩),
   opAt 2390 .SHR,
   opAt 2391 (.Dup ⟨2, by decide⟩),
   pushAt 2392 2 992,
   opAt 2393 .ADD,
   opAt 2394 .MSTORE,
   pushAt 2395 1 1,
   pushAt 2396 2 1530,
   opAt 2397 .JUMP]

end Challenge.Modexp.Submission.Proofs.Fast
