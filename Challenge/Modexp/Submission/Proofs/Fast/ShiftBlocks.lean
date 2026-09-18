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
  [opAt 2528 .JUMPDEST,
   opAt 2529 (.Dup ⟨0, by decide⟩),
   opAt 2530 .MLOAD,
   pushAt 2531 3 2112,
   opAt 2532 (.Dup ⟨2, by decide⟩),
   opAt 2533 .SUB,
   opAt 2534 .MLOAD,
   opAt 2535 (.Dup ⟨1, by decide⟩),
   opAt 2536 .ADD,
   opAt 2537 (.Swap ⟨0, by decide⟩),
   opAt 2538 (.Dup ⟨1, by decide⟩),
   opAt 2539 .LT,
   opAt 2540 (.Swap ⟨0, by decide⟩),
   opAt 2541 (.Dup ⟨3, by decide⟩),
   opAt 2542 .ADD,
   opAt 2543 (.Swap ⟨2, by decide⟩),
   opAt 2544 (.Dup ⟨3, by decide⟩),
   opAt 2545 .LT,
   opAt 2546 .OR,
   opAt 2547 (.Swap ⟨1, by decide⟩),
   opAt 2548 (.Dup ⟨1, by decide⟩),
   opAt 2549 .MSTORE]

/-- The exit test of the add-round body (`blk3157` instructions 23..30). -/
def blk3157b :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 2550 1 31,
   opAt 2551 .NOT,
   opAt 2552 .ADD,
   pushAt 2553 2 2111,
   opAt 2554 (.Dup ⟨1, by decide⟩),
   opAt 2555 .GT,
   pushAt 2556 2 3142,
   opAt 2557 .JUMPI]

/-- The add-round fall-through padding.  The five `JUMPDEST`s that used to sit here were
folded into the immediate of the `PUSH7 0x820` that follows the tail's `POP`; the block is
now empty and the add exit test falls straight into the tail. -/
def blk3157c :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  []

/-- The subtract-round body up to its exit test (`blk3213` instructions 0..22). -/
def blk3213a :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2582 .JUMPDEST,
   opAt 2583 (.Dup ⟨0, by decide⟩),
   opAt 2584 .MLOAD,
   pushAt 2585 2 2112,
   opAt 2586 (.Dup ⟨2, by decide⟩),
   opAt 2587 .SUB,
   opAt 2588 .MLOAD,
   opAt 2589 (.Dup ⟨1, by decide⟩),
   opAt 2590 (.Dup ⟨1, by decide⟩),
   opAt 2591 .GT,
   opAt 2592 (.Swap ⟨1, by decide⟩),
   opAt 2593 .SUB,
   opAt 2594 (.Dup ⟨3, by decide⟩),
   opAt 2595 (.Dup ⟨1, by decide⟩),
   opAt 2596 .LT,
   opAt 2597 (.Swap ⟨0, by decide⟩),
   opAt 2598 (.Dup ⟨4, by decide⟩),
   opAt 2599 (.Swap ⟨0, by decide⟩),
   opAt 2600 .SUB,
   opAt 2601 (.Dup ⟨3, by decide⟩),
   opAt 2602 .MSTORE,
   opAt 2603 .OR]

/-- The exit test of the subtract-round body (`blk3213` instructions 23..31). -/
def blk3213b :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2604 (.Swap ⟨1, by decide⟩),
   opAt 2605 .POP,
   pushAt 2606 1 31,
   opAt 2607 .NOT,
   opAt 2608 .ADD,
   pushAt 2609 2 2111,
   opAt 2610 (.Dup ⟨1, by decide⟩),
   opAt 2611 .GT,
   pushAt 2612 2 3221,
   opAt 2613 .JUMPI]

end Challenge.Modexp.Submission.Proofs.Fast
