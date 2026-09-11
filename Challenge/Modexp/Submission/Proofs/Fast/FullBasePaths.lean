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
  [opAt 2350 .JUMPDEST,
   opAt 2351 (.Dup ⟨0, by decide⟩),
   opAt 2352 (.Dup ⟨3, by decide⟩),
   opAt 2353 .EQ,
   pushAt 2354 0 0,
   opAt 2355 .MLOAD,
   pushAt 2356 1 255,
   opAt 2357 .SHR,
   opAt 2358 .AND,
   opAt 2359 .ISZERO,
   pushAt 2360 2 3096,
   opAt 2361 .JUMPI]

/-- Located block in the selected full-width-base helper. -/
def blkFullBaseCopyAdd :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2362 (.Dup ⟨0, by decide⟩),
   pushAt 2363 1 96,
   pushAt 2364 2 1024,
   opAt 2365 .CALLDATACOPY,
   pushAt 2366 2 1616,
   pushAt 2367 2 2048,
   pushAt 2368 2 1024,
   pushAt 2369 2 6144,
   pushAt 2370 2 4049,
   opAt 2371 .JUMP]

/-- Located block in the selected full-width-base helper. -/
def blkFullBaseFallback :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2372 .JUMPDEST,
   opAt 2373 (.Dup ⟨2, by decide⟩),
   pushAt 2374 1 31,
   opAt 2375 .ADD,
   pushAt 2376 1 5,
   opAt 2377 .SHR,
   opAt 2378 (.Dup ⟨3, by decide⟩),
   opAt 2379 (.Dup ⟨1, by decide⟩),
   pushAt 2380 1 5,
   opAt 2381 .SHL,
   opAt 2382 .SUB,
   pushAt 2383 1 3,
   opAt 2384 .SHL,
   pushAt 2385 1 96,
   opAt 2386 .CALLDATALOAD,
   opAt 2387 (.Swap ⟨0, by decide⟩),
   opAt 2388 .SHR,
   opAt 2389 (.Dup ⟨2, by decide⟩),
   pushAt 2390 2 992,
   opAt 2391 .ADD,
   opAt 2392 .MSTORE,
   pushAt 2393 1 1,
   pushAt 2394 2 1530,
   opAt 2395 .JUMP]

end Challenge.Modexp.Submission.Proofs.Fast
