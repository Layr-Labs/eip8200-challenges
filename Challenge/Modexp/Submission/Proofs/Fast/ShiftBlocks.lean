import Challenge.Modexp.Submission.Proofs.Fast.ShiftPaths
set_option warningAsError false
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000
/-! Loop-body blocks of the shift-reduce routine split before their exit tests, so
that each block reduction stays small enough for the kernel. -/

namespace Challenge.Modexp.Submission.Proofs.Fast

open EvmSemantics
open EvmSemantics.EVM
open Challenge.Modexp.Submission.Proofs.Bytecode

/-- The negation loop body up to its exit test (`blk2896` instructions 0..14). -/
def blk2896a :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2046 .JUMPDEST,
   opAt 2047 (.Dup ⟨0, by decide⟩),
   opAt 2048 .MLOAD,
   opAt 2049 .NOT,
   opAt 2050 (.Dup ⟨2, by decide⟩),
   opAt 2051 .ADD,
   opAt 2052 (.Dup ⟨0, by decide⟩),
   opAt 2053 (.Swap ⟨2, by decide⟩),
   opAt 2054 .GT,
   opAt 2055 (.Swap ⟨1, by decide⟩),
   opAt 2056 (.Dup ⟨1, by decide⟩),
   pushAt 2057 2 1280,
   opAt 2058 .ADD,
   opAt 2059 .MSTORE]

/-- The rotated exit test of the negation loop body: `p - 32` stays on the stack, the
jump back to the loop head is taken on the old pointer `p`, and `p = 0` falls into `NEG_DONE`. -/
def blk2896b :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2060 (.Dup ⟨0, by decide⟩),
   pushAt 2061 1 31,
   opAt 2062 .NOT,
   opAt 2063 .ADD,
   opAt 2064 (.Swap ⟨0, by decide⟩),
   pushAt 2065 2 2523,
   opAt 2066 .JUMPI]



/-- The add-round body up to its store (`blk3157` instructions 0..22). -/
def blk3157a :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2529 .JUMPDEST,
   opAt 2530 (.Dup ⟨0, by decide⟩),
   opAt 2531 .MLOAD,
   pushAt 2532 3 2112,
   opAt 2533 (.Dup ⟨2, by decide⟩),
   opAt 2534 .SUB,
   opAt 2535 .MLOAD,
   opAt 2536 (.Dup ⟨1, by decide⟩),
   opAt 2537 .ADD,
   opAt 2538 (.Swap ⟨0, by decide⟩),
   opAt 2539 (.Dup ⟨1, by decide⟩),
   opAt 2540 .LT,
   opAt 2541 (.Swap ⟨0, by decide⟩),
   opAt 2542 (.Dup ⟨3, by decide⟩),
   opAt 2543 .ADD,
   opAt 2544 (.Swap ⟨2, by decide⟩),
   opAt 2545 (.Dup ⟨3, by decide⟩),
   opAt 2546 .LT,
   opAt 2547 .OR,
   opAt 2548 (.Swap ⟨1, by decide⟩),
   opAt 2549 (.Dup ⟨1, by decide⟩),
   opAt 2550 .MSTORE]

/-- The exit test of the add-round body (`blk3157` instructions 23..30). -/
def blk3157b :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 2551 1 31,
   opAt 2552 .NOT,
   opAt 2553 .ADD,
   pushAt 2554 2 2111,
   opAt 2555 (.Dup ⟨1, by decide⟩),
   opAt 2556 .GT,
   pushAt 2557 2 3142,
   opAt 2558 .JUMPI]

/-- The five padding `JUMPDEST`s on the add-round fall-through (indices 2413 to 2417). -/
def blk3157c :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2559 .JUMPDEST,
   opAt 2560 .JUMPDEST,
   opAt 2561 .JUMPDEST,
   opAt 2562 .JUMPDEST,
   opAt 2563 .JUMPDEST]

/-- The subtract-round body up to its exit test (`blk3213` instructions 0..22). -/
def blk3213a :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2588 .JUMPDEST,
   opAt 2589 (.Dup ⟨0, by decide⟩),
   opAt 2590 .MLOAD,
   pushAt 2591 2 2112,
   opAt 2592 (.Dup ⟨2, by decide⟩),
   opAt 2593 .SUB,
   opAt 2594 .MLOAD,
   opAt 2595 (.Dup ⟨1, by decide⟩),
   opAt 2596 (.Dup ⟨1, by decide⟩),
   opAt 2597 .GT,
   opAt 2598 (.Swap ⟨1, by decide⟩),
   opAt 2599 .SUB,
   opAt 2600 (.Dup ⟨3, by decide⟩),
   opAt 2601 (.Dup ⟨1, by decide⟩),
   opAt 2602 .LT,
   opAt 2603 (.Swap ⟨0, by decide⟩),
   opAt 2604 (.Dup ⟨4, by decide⟩),
   opAt 2605 (.Swap ⟨0, by decide⟩),
   opAt 2606 .SUB,
   opAt 2607 (.Dup ⟨3, by decide⟩),
   opAt 2608 .MSTORE,
   opAt 2609 .OR]

/-- The exit test of the subtract-round body (`blk3213` instructions 23..31). -/
def blk3213b :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2610 (.Swap ⟨1, by decide⟩),
   opAt 2611 .POP,
   pushAt 2612 1 31,
   opAt 2613 .NOT,
   opAt 2614 .ADD,
   pushAt 2615 2 2111,
   opAt 2616 (.Dup ⟨1, by decide⟩),
   opAt 2617 .GT,
   pushAt 2618 2 3221,
   opAt 2619 .JUMPI]

end Challenge.Modexp.Submission.Proofs.Fast
