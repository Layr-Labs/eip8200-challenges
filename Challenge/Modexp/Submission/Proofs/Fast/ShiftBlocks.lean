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
  [opAt 2048 .JUMPDEST,
   opAt 2049 (.Dup ⟨0, by decide⟩),
   opAt 2050 .MLOAD,
   opAt 2051 .NOT,
   opAt 2052 (.Dup ⟨2, by decide⟩),
   opAt 2053 .ADD,
   opAt 2054 (.Dup ⟨0, by decide⟩),
   opAt 2055 (.Swap ⟨2, by decide⟩),
   opAt 2056 .GT,
   opAt 2057 (.Swap ⟨1, by decide⟩),
   opAt 2058 (.Dup ⟨1, by decide⟩),
   pushAt 2059 2 1280,
   opAt 2060 .ADD,
   opAt 2061 .MSTORE]

/-- The rotated exit test of the negation loop body: `p - 32` stays on the stack, the
jump back to the loop head is taken on the old pointer `p`, and `p = 0` falls into `NEG_DONE`. -/
def blk2896b :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2062 (.Dup ⟨0, by decide⟩),
   pushAt 2063 1 31,
   opAt 2064 .NOT,
   opAt 2065 .ADD,
   opAt 2066 (.Swap ⟨0, by decide⟩),
   pushAt 2067 2 2523,
   opAt 2068 .JUMPI]



/-- The add-round body up to its store (`blk3157` instructions 0..22). -/
def blk3157a :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2531 .JUMPDEST,
   opAt 2532 (.Dup ⟨0, by decide⟩),
   opAt 2533 .MLOAD,
   pushAt 2534 3 2112,
   opAt 2535 (.Dup ⟨2, by decide⟩),
   opAt 2536 .SUB,
   opAt 2537 .MLOAD,
   opAt 2538 (.Dup ⟨1, by decide⟩),
   opAt 2539 .ADD,
   opAt 2540 (.Swap ⟨0, by decide⟩),
   opAt 2541 (.Dup ⟨1, by decide⟩),
   opAt 2542 .LT,
   opAt 2543 (.Swap ⟨0, by decide⟩),
   opAt 2544 (.Dup ⟨3, by decide⟩),
   opAt 2545 .ADD,
   opAt 2546 (.Swap ⟨2, by decide⟩),
   opAt 2547 (.Dup ⟨3, by decide⟩),
   opAt 2548 .LT,
   opAt 2549 .OR,
   opAt 2550 (.Swap ⟨1, by decide⟩),
   opAt 2551 (.Dup ⟨1, by decide⟩),
   opAt 2552 .MSTORE]

/-- The exit test of the add-round body (`blk3157` instructions 23..30). -/
def blk3157b :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 2553 1 31,
   opAt 2554 .NOT,
   opAt 2555 .ADD,
   pushAt 2556 2 2111,
   opAt 2557 (.Dup ⟨1, by decide⟩),
   opAt 2558 .GT,
   pushAt 2559 2 3142,
   opAt 2560 .JUMPI]

/-- The five padding `JUMPDEST`s on the add-round fall-through (indices 2413 to 2417). -/
def blk3157c :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2561 .JUMPDEST,
   opAt 2562 .JUMPDEST,
   opAt 2563 .JUMPDEST,
   opAt 2564 .JUMPDEST,
   opAt 2565 .JUMPDEST]

/-- The subtract-round body up to its exit test (`blk3213` instructions 0..22). -/
def blk3213a :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2590 .JUMPDEST,
   opAt 2591 (.Dup ⟨0, by decide⟩),
   opAt 2592 .MLOAD,
   pushAt 2593 2 2112,
   opAt 2594 (.Dup ⟨2, by decide⟩),
   opAt 2595 .SUB,
   opAt 2596 .MLOAD,
   opAt 2597 (.Dup ⟨1, by decide⟩),
   opAt 2598 (.Dup ⟨1, by decide⟩),
   opAt 2599 .GT,
   opAt 2600 (.Swap ⟨1, by decide⟩),
   opAt 2601 .SUB,
   opAt 2602 (.Dup ⟨3, by decide⟩),
   opAt 2603 (.Dup ⟨1, by decide⟩),
   opAt 2604 .LT,
   opAt 2605 (.Swap ⟨0, by decide⟩),
   opAt 2606 (.Dup ⟨4, by decide⟩),
   opAt 2607 (.Swap ⟨0, by decide⟩),
   opAt 2608 .SUB,
   opAt 2609 (.Dup ⟨3, by decide⟩),
   opAt 2610 .MSTORE,
   opAt 2611 .OR]

/-- The exit test of the subtract-round body (`blk3213` instructions 23..31). -/
def blk3213b :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2612 (.Swap ⟨1, by decide⟩),
   opAt 2613 .POP,
   pushAt 2614 1 31,
   opAt 2615 .NOT,
   opAt 2616 .ADD,
   pushAt 2617 2 2111,
   opAt 2618 (.Dup ⟨1, by decide⟩),
   opAt 2619 .GT,
   pushAt 2620 2 3221,
   opAt 2621 .JUMPI]

end Challenge.Modexp.Submission.Proofs.Fast
