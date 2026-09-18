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
  [opAt 2047 .JUMPDEST,
   opAt 2048 (.Dup ⟨0, by decide⟩),
   opAt 2049 .MLOAD,
   opAt 2050 .NOT,
   opAt 2051 (.Dup ⟨2, by decide⟩),
   opAt 2052 .ADD,
   opAt 2053 (.Dup ⟨0, by decide⟩),
   opAt 2054 (.Swap ⟨2, by decide⟩),
   opAt 2055 .GT,
   opAt 2056 (.Swap ⟨1, by decide⟩),
   opAt 2057 (.Dup ⟨1, by decide⟩),
   pushAt 2058 2 1280,
   opAt 2059 .ADD,
   opAt 2060 .MSTORE]

/-- The rotated exit test of the negation loop body: `p - 32` stays on the stack, the
jump back to the loop head is taken on the old pointer `p`, and `p = 0` falls into `NEG_DONE`. -/
def blk2896b :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2061 (.Dup ⟨0, by decide⟩),
   pushAt 2062 1 31,
   opAt 2063 .NOT,
   opAt 2064 .ADD,
   opAt 2065 (.Swap ⟨0, by decide⟩),
   pushAt 2066 2 2523,
   opAt 2067 .JUMPI]



/-- The add-round body up to its store (`blk3157` instructions 0..22). -/
def blk3157a :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2530 .JUMPDEST,
   opAt 2531 (.Dup ⟨0, by decide⟩),
   opAt 2532 .MLOAD,
   pushAt 2533 3 2112,
   opAt 2534 (.Dup ⟨2, by decide⟩),
   opAt 2535 .SUB,
   opAt 2536 .MLOAD,
   opAt 2537 (.Dup ⟨1, by decide⟩),
   opAt 2538 .ADD,
   opAt 2539 (.Swap ⟨0, by decide⟩),
   opAt 2540 (.Dup ⟨1, by decide⟩),
   opAt 2541 .LT,
   opAt 2542 (.Swap ⟨0, by decide⟩),
   opAt 2543 (.Dup ⟨3, by decide⟩),
   opAt 2544 .ADD,
   opAt 2545 (.Swap ⟨2, by decide⟩),
   opAt 2546 (.Dup ⟨3, by decide⟩),
   opAt 2547 .LT,
   opAt 2548 .OR,
   opAt 2549 (.Swap ⟨1, by decide⟩),
   opAt 2550 (.Dup ⟨1, by decide⟩),
   opAt 2551 .MSTORE]

/-- The exit test of the add-round body (`blk3157` instructions 23..30). -/
def blk3157b :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 2552 1 31,
   opAt 2553 .NOT,
   opAt 2554 .ADD,
   pushAt 2555 2 2111,
   opAt 2556 (.Dup ⟨1, by decide⟩),
   opAt 2557 .GT,
   pushAt 2558 2 3142,
   opAt 2559 .JUMPI]

/-- The five padding `JUMPDEST`s on the add-round fall-through (indices 2413 to 2417). -/
def blk3157c :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2560 .JUMPDEST,
   opAt 2561 .JUMPDEST,
   opAt 2562 .JUMPDEST,
   opAt 2563 .JUMPDEST,
   opAt 2564 .JUMPDEST]

/-- The subtract-round body up to its exit test (`blk3213` instructions 0..22). -/
def blk3213a :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2589 .JUMPDEST,
   opAt 2590 (.Dup ⟨0, by decide⟩),
   opAt 2591 .MLOAD,
   pushAt 2592 2 2112,
   opAt 2593 (.Dup ⟨2, by decide⟩),
   opAt 2594 .SUB,
   opAt 2595 .MLOAD,
   opAt 2596 (.Dup ⟨1, by decide⟩),
   opAt 2597 (.Dup ⟨1, by decide⟩),
   opAt 2598 .GT,
   opAt 2599 (.Swap ⟨1, by decide⟩),
   opAt 2600 .SUB,
   opAt 2601 (.Dup ⟨3, by decide⟩),
   opAt 2602 (.Dup ⟨1, by decide⟩),
   opAt 2603 .LT,
   opAt 2604 (.Swap ⟨0, by decide⟩),
   opAt 2605 (.Dup ⟨4, by decide⟩),
   opAt 2606 (.Swap ⟨0, by decide⟩),
   opAt 2607 .SUB,
   opAt 2608 (.Dup ⟨3, by decide⟩),
   opAt 2609 .MSTORE,
   opAt 2610 .OR]

/-- The exit test of the subtract-round body (`blk3213` instructions 23..31). -/
def blk3213b :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2611 (.Swap ⟨1, by decide⟩),
   opAt 2612 .POP,
   pushAt 2613 1 31,
   opAt 2614 .NOT,
   opAt 2615 .ADD,
   pushAt 2616 2 2111,
   opAt 2617 (.Dup ⟨1, by decide⟩),
   opAt 2618 .GT,
   pushAt 2619 2 3221,
   opAt 2620 .JUMPI]

end Challenge.Modexp.Submission.Proofs.Fast
