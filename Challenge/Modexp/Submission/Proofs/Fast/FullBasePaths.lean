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

/-- pc 3606..3620, indices 2361..2372: size/top-bit guard. -/
def blkFullBaseGuard :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2361 .JUMPDEST,
   opAt 2362 (.Dup ⟨0, by decide⟩),
   opAt 2363 (.Dup ⟨3, by decide⟩),
   opAt 2364 .EQ,
   pushAt 2365 0 0,
   opAt 2366 .MLOAD,
   pushAt 2367 1 255,
   opAt 2368 .SHR,
   opAt 2369 .AND,
   opAt 2370 .ISZERO,
   pushAt 2371 2 3661,
   opAt 2372 .JUMPI]

/-- pc 3621..3643, indices 2373..2382: copy the base to ACC and call
the existing add-mod routine with ZERO as its second operand. -/
def blkFullBaseCopyAdd :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2373 (.Dup ⟨0, by decide⟩),
   pushAt 2374 1 96,
   pushAt 2375 2 1024,
   opAt 2376 .CALLDATACOPY,
   pushAt 2377 2 3644,
   pushAt 2378 2 1024,
   pushAt 2379 2 3072,
   pushAt 2380 2 1024,
   pushAt 2381 2 3695,
   opAt 2382 .JUMP]

/-- pc 3644..3660, indices 2383..2389: after add-mod, convert ACC to the
Montgomery BASE block and rejoin at pc 1755. -/
def blkFullBaseAfterAdd :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2383 .JUMPDEST,
   pushAt 2384 2 1755,
   pushAt 2385 2 2048,
   pushAt 2386 2 6144,
   pushAt 2387 2 1024,
   pushAt 2388 2 1939,
   opAt 2389 .JUMP]

/-! The appended base-top-bit dispatcher. -/
def blkFullBaseDispatch :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2414 .JUMPDEST,
   pushAt 2415 2 1024,
   opAt 2416 .MLOAD,
   pushAt 2417 1 255,
   opAt 2418 .SHR,
   opAt 2419 .ISZERO,
   pushAt 2420 2 3712,
   opAt 2421 .JUMPI,
   pushAt 2422 2 2467,
   opAt 2423 .JUMP]

def blkFullBaseSkip :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2414 .JUMPDEST,
   pushAt 2415 2 1024,
   opAt 2416 .MLOAD,
   pushAt 2417 1 255,
   opAt 2418 .SHR,
   opAt 2419 .ISZERO,
   pushAt 2420 2 3712,
   opAt 2421 .JUMPI,
   opAt 2424 .JUMPDEST,
   opAt 2425 .POP,
   opAt 2426 .POP,
   opAt 2427 .POP,
   opAt 2428 .POP,
   pushAt 2429 2 3644,
   opAt 2430 .JUMP]

/-- pc 3661..3694, indices 2390..2413: relocated original base-head
computation and the jump to the unchanged loop head. -/
def blkFullBaseFallback :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2390 .JUMPDEST,
   opAt 2391 (.Dup ⟨2, by decide⟩),
   pushAt 2392 1 31,
   opAt 2393 .ADD,
   pushAt 2394 1 5,
   opAt 2395 .SHR,
   opAt 2396 (.Dup ⟨3, by decide⟩),
   opAt 2397 (.Dup ⟨1, by decide⟩),
   pushAt 2398 1 5,
   opAt 2399 .SHL,
   opAt 2400 .SUB,
   pushAt 2401 1 3,
   opAt 2402 .SHL,
   pushAt 2403 1 96,
   opAt 2404 .CALLDATALOAD,
   opAt 2405 (.Swap ⟨0, by decide⟩),
   opAt 2406 .SHR,
   opAt 2407 (.Dup ⟨2, by decide⟩),
   pushAt 2408 2 992,
   opAt 2409 .ADD,
   opAt 2410 .MSTORE,
   pushAt 2411 1 1,
   pushAt 2412 2 1668,
   opAt 2413 .JUMP]

end Challenge.Modexp.Submission.Proofs.Fast

