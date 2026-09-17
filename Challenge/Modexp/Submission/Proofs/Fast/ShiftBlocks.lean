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
  [opAt 2080 .JUMPDEST,
   opAt 2081 (.Dup ⟨0, by decide⟩),
   opAt 2082 .MLOAD,
   opAt 2083 .NOT,
   opAt 2084 (.Dup ⟨2, by decide⟩),
   opAt 2085 .ADD,
   opAt 2086 (.Dup ⟨0, by decide⟩),
   opAt 2087 (.Swap ⟨2, by decide⟩),
   opAt 2088 .GT,
   opAt 2089 (.Swap ⟨1, by decide⟩),
   opAt 2090 (.Dup ⟨1, by decide⟩),
   pushAt 2091 2 1280,
   opAt 2092 .ADD,
   opAt 2093 .MSTORE]

/-- The rotated exit test of the negation loop body: `p - 32` stays on the stack, the
jump back to the loop head is taken on the old pointer `p`, and `p = 0` falls into `NEG_DONE`. -/
def blk2896b :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2094 (.Dup ⟨0, by decide⟩),
   pushAt 2095 1 31,
   opAt 2096 .NOT,
   opAt 2097 .ADD,
   opAt 2098 (.Swap ⟨0, by decide⟩),
   pushAt 2099 2 2523,
   opAt 2100 .JUMPI]



/-- The add-round body up to its store (`blk3157` instructions 0..22). -/
def blk3157a :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2563 .JUMPDEST,
   opAt 2564 (.Dup ⟨0, by decide⟩),
   opAt 2565 .MLOAD,
   pushAt 2566 3 2112,
   opAt 2567 (.Dup ⟨2, by decide⟩),
   opAt 2568 .SUB,
   opAt 2569 .MLOAD,
   opAt 2570 (.Dup ⟨1, by decide⟩),
   opAt 2571 .ADD,
   opAt 2572 (.Swap ⟨0, by decide⟩),
   opAt 2573 (.Dup ⟨1, by decide⟩),
   opAt 2574 .LT,
   opAt 2575 (.Swap ⟨0, by decide⟩),
   opAt 2576 (.Dup ⟨3, by decide⟩),
   opAt 2577 .ADD,
   opAt 2578 (.Swap ⟨2, by decide⟩),
   opAt 2579 (.Dup ⟨3, by decide⟩),
   opAt 2580 .LT,
   opAt 2581 .OR,
   opAt 2582 (.Swap ⟨1, by decide⟩),
   opAt 2583 (.Dup ⟨1, by decide⟩),
   opAt 2584 .MSTORE]

/-- The exit test of the add-round body (`blk3157` instructions 23..30). -/
def blk3157b :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 2585 1 31,
   opAt 2586 .NOT,
   opAt 2587 .ADD,
   pushAt 2588 2 2111,
   opAt 2589 (.Dup ⟨1, by decide⟩),
   opAt 2590 .GT,
   pushAt 2591 2 3142,
   opAt 2592 .JUMPI]

/-- The five padding `JUMPDEST`s on the add-round fall-through (indices 2413 to 2417). -/
def blk3157c :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2593 .JUMPDEST,
   opAt 2594 .JUMPDEST,
   opAt 2595 .JUMPDEST,
   opAt 2596 .JUMPDEST,
   opAt 2597 .JUMPDEST]

/-- The subtract-round body up to its exit test (`blk3213` instructions 0..22). -/
def blk3213a :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2622 .JUMPDEST,
   opAt 2623 (.Dup ⟨0, by decide⟩),
   opAt 2624 .MLOAD,
   pushAt 2625 2 2112,
   opAt 2626 (.Dup ⟨2, by decide⟩),
   opAt 2627 .SUB,
   opAt 2628 .MLOAD,
   opAt 2629 (.Dup ⟨1, by decide⟩),
   opAt 2630 (.Dup ⟨1, by decide⟩),
   opAt 2631 .GT,
   opAt 2632 (.Swap ⟨1, by decide⟩),
   opAt 2633 .SUB,
   opAt 2634 (.Dup ⟨3, by decide⟩),
   opAt 2635 (.Dup ⟨1, by decide⟩),
   opAt 2636 .LT,
   opAt 2637 (.Swap ⟨0, by decide⟩),
   opAt 2638 (.Dup ⟨4, by decide⟩),
   opAt 2639 (.Swap ⟨0, by decide⟩),
   opAt 2640 .SUB,
   opAt 2641 (.Dup ⟨3, by decide⟩),
   opAt 2642 .MSTORE,
   opAt 2643 .OR]

/-- The exit test of the subtract-round body (`blk3213` instructions 23..31). -/
def blk3213b :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2644 (.Swap ⟨1, by decide⟩),
   opAt 2645 .POP,
   pushAt 2646 1 31,
   opAt 2647 .NOT,
   opAt 2648 .ADD,
   pushAt 2649 2 2111,
   opAt 2650 (.Dup ⟨1, by decide⟩),
   opAt 2651 .GT,
   pushAt 2652 2 3221,
   opAt 2653 .JUMPI]

end Challenge.Modexp.Submission.Proofs.Fast
