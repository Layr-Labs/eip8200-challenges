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
  [opAt 2061 .JUMPDEST,
   opAt 2062 (.Dup ⟨0, by decide⟩),
   opAt 2063 .MLOAD,
   opAt 2064 .NOT,
   opAt 2065 (.Dup ⟨2, by decide⟩),
   opAt 2066 .ADD,
   opAt 2067 (.Dup ⟨0, by decide⟩),
   opAt 2068 (.Swap ⟨2, by decide⟩),
   opAt 2069 .GT,
   opAt 2070 (.Swap ⟨1, by decide⟩),
   opAt 2071 (.Dup ⟨1, by decide⟩),
   pushAt 2072 2 1280,
   opAt 2073 .ADD,
   opAt 2074 .MSTORE]

/-- The rotated exit test of the negation loop body: `p - 32` stays on the stack, the
jump back to the loop head is taken on the old pointer `p`, and `p = 0` falls into `NEG_DONE`. -/
def blk2896b :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2075 (.Dup ⟨0, by decide⟩),
   pushAt 2076 1 31,
   opAt 2077 .NOT,
   opAt 2078 .ADD,
   opAt 2079 (.Swap ⟨0, by decide⟩),
   pushAt 2080 2 2523,
   opAt 2081 .JUMPI]



/-- The add-round body up to its store (`blk3157` instructions 0..22). -/
def blk3157a :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2544 .JUMPDEST,
   opAt 2545 (.Dup ⟨0, by decide⟩),
   opAt 2546 .MLOAD,
   pushAt 2547 3 2112,
   opAt 2548 (.Dup ⟨2, by decide⟩),
   opAt 2549 .SUB,
   opAt 2550 .MLOAD,
   opAt 2551 (.Dup ⟨1, by decide⟩),
   opAt 2552 .ADD,
   opAt 2553 (.Swap ⟨0, by decide⟩),
   opAt 2554 (.Dup ⟨1, by decide⟩),
   opAt 2555 .LT,
   opAt 2556 (.Swap ⟨0, by decide⟩),
   opAt 2557 (.Dup ⟨3, by decide⟩),
   opAt 2558 .ADD,
   opAt 2559 (.Swap ⟨2, by decide⟩),
   opAt 2560 (.Dup ⟨3, by decide⟩),
   opAt 2561 .LT,
   opAt 2562 .OR,
   opAt 2563 (.Swap ⟨1, by decide⟩),
   opAt 2564 (.Dup ⟨1, by decide⟩),
   opAt 2565 .MSTORE]

/-- The exit test of the add-round body (`blk3157` instructions 23..30). -/
def blk3157b :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 2566 1 31,
   opAt 2567 .NOT,
   opAt 2568 .ADD,
   pushAt 2569 2 2111,
   opAt 2570 (.Dup ⟨1, by decide⟩),
   opAt 2571 .GT,
   pushAt 2572 2 3142,
   opAt 2573 .JUMPI]

/-- The five padding `JUMPDEST`s on the add-round fall-through (indices 2413 to 2417). -/
def blk3157c :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2574 .JUMPDEST,
   opAt 2575 .JUMPDEST,
   opAt 2576 .JUMPDEST,
   opAt 2577 .JUMPDEST,
   opAt 2578 .JUMPDEST]

/-- The subtract-round body up to its exit test (`blk3213` instructions 0..22). -/
def blk3213a :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2603 .JUMPDEST,
   opAt 2604 (.Dup ⟨0, by decide⟩),
   opAt 2605 .MLOAD,
   pushAt 2606 2 2112,
   opAt 2607 (.Dup ⟨2, by decide⟩),
   opAt 2608 .SUB,
   opAt 2609 .MLOAD,
   opAt 2610 (.Dup ⟨1, by decide⟩),
   opAt 2611 (.Dup ⟨1, by decide⟩),
   opAt 2612 .GT,
   opAt 2613 (.Swap ⟨1, by decide⟩),
   opAt 2614 .SUB,
   opAt 2615 (.Dup ⟨3, by decide⟩),
   opAt 2616 (.Dup ⟨1, by decide⟩),
   opAt 2617 .LT,
   opAt 2618 (.Swap ⟨0, by decide⟩),
   opAt 2619 (.Dup ⟨4, by decide⟩),
   opAt 2620 (.Swap ⟨0, by decide⟩),
   opAt 2621 .SUB,
   opAt 2622 (.Dup ⟨3, by decide⟩),
   opAt 2623 .MSTORE,
   opAt 2624 .OR]

/-- The exit test of the subtract-round body (`blk3213` instructions 23..31). -/
def blk3213b :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2625 (.Swap ⟨1, by decide⟩),
   opAt 2626 .POP,
   pushAt 2627 1 31,
   opAt 2628 .NOT,
   opAt 2629 .ADD,
   pushAt 2630 2 2111,
   opAt 2631 (.Dup ⟨1, by decide⟩),
   opAt 2632 .GT,
   pushAt 2633 2 3221,
   opAt 2634 .JUMPI]

end Challenge.Modexp.Submission.Proofs.Fast
