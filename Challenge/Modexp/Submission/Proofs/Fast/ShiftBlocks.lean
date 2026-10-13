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

/-- The negation loop body: store limb `j` of `NEG` as `NOT m_j + flag`, then push the
cleared flag (`blk2896` instructions 0..9). -/
def blk2896a :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2060 .JUMPDEST,
   opAt 2061 (.Dup ⟨1, by decide⟩),
   opAt 2062 .MLOAD,
   opAt 2063 .NOT,
   opAt 2064 .ADD,
   opAt 2065 (.Dup ⟨1, by decide⟩),
   pushAt 2066 2 1280,
   opAt 2067 .ADD,
   opAt 2068 .MSTORE,
   pushAt 2069 0 0]

/-- The rotated exit test of the negation loop body: `p - 32` goes under the flag, the
jump back to the loop head is taken on the old pointer `p`, and `p = 0` falls into the
`NEG_DONE` padding. -/
def blk2896b :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2070 (.Dup ⟨1, by decide⟩),
   pushAt 2071 1 31,
   opAt 2072 .NOT,
   opAt 2073 .ADD,
   opAt 2074 (.Swap ⟨1, by decide⟩),
   pushAt 2075 2 2636,
   opAt 2076 .JUMPI]



/-- The add-round body up to its store (`blk3157` instructions 0..22). -/
def blk3157a :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2540 .JUMPDEST,
   opAt 2541 (.Dup ⟨0, by decide⟩),
   opAt 2542 .MLOAD,
   pushAt 2543 2 2112,
   opAt 2544 (.Dup ⟨2, by decide⟩),
   opAt 2545 .SUB,
   opAt 2546 .MLOAD,
   opAt 2547 (.Dup ⟨1, by decide⟩),
   opAt 2548 .ADD,
   opAt 2549 (.Swap ⟨0, by decide⟩),
   opAt 2550 (.Dup ⟨1, by decide⟩),
   opAt 2551 .LT,
   opAt 2552 (.Swap ⟨0, by decide⟩),
   opAt 2553 (.Dup ⟨3, by decide⟩),
   opAt 2554 .ADD,
   opAt 2555 (.Swap ⟨2, by decide⟩),
   opAt 2556 (.Dup ⟨3, by decide⟩),
   opAt 2557 .LT,
   opAt 2558 .OR,
   opAt 2559 (.Swap ⟨1, by decide⟩),
   opAt 2560 (.Dup ⟨1, by decide⟩),
   opAt 2561 .MSTORE]

/-- The exit test of the add-round body (`blk3157` instructions 23..30). -/
def blk3157b :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 2562 1 31,
   opAt 2563 .NOT,
   opAt 2564 .ADD,
   pushAt 2565 2 2111,
   opAt 2566 (.Dup ⟨1, by decide⟩),
   opAt 2567 .GT,
   pushAt 2568 2 3240,
   opAt 2569 .JUMPI]

/-- The five padding `JUMPDEST`s on the add-round fall-through (indices 2413 to 2417). -/
def blk3157c :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  []

/-- The subtract-round body up to its exit test (`blk3213` instructions 0..22). -/
def blk3213a :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2594 .JUMPDEST,
   opAt 2595 (.Dup ⟨0, by decide⟩),
   opAt 2596 .MLOAD,
   pushAt 2597 2 2112,
   opAt 2598 (.Dup ⟨2, by decide⟩),
   opAt 2599 .SUB,
   opAt 2600 .MLOAD,
   opAt 2601 (.Dup ⟨1, by decide⟩),
   opAt 2602 (.Dup ⟨1, by decide⟩),
   opAt 2603 .GT,
   opAt 2604 (.Swap ⟨1, by decide⟩),
   opAt 2605 .SUB,
   opAt 2606 (.Dup ⟨3, by decide⟩),
   opAt 2607 (.Dup ⟨1, by decide⟩),
   opAt 2608 .LT,
   opAt 2609 (.Swap ⟨0, by decide⟩),
   opAt 2610 (.Dup ⟨4, by decide⟩),
   opAt 2611 (.Swap ⟨0, by decide⟩),
   opAt 2612 .SUB,
   opAt 2613 (.Dup ⟨3, by decide⟩),
   opAt 2614 .MSTORE,
   opAt 2615 .OR]

/-- The exit test of the subtract-round body (`blk3213` instructions 23..31). -/
def blk3213b :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2616 (.Swap ⟨1, by decide⟩),
   opAt 2617 .POP,
   pushAt 2618 1 31,
   opAt 2619 .NOT,
   opAt 2620 .ADD,
   pushAt 2621 2 2111,
   opAt 2622 (.Dup ⟨1, by decide⟩),
   opAt 2623 .GT,
   pushAt 2624 2 3284,
   opAt 2625 .JUMPI]

end Challenge.Modexp.Submission.Proofs.Fast
