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
  [opAt 2544 .JUMPDEST,
   opAt 2545 (.Dup ⟨0, by decide⟩),
   opAt 2546 .MLOAD,
   pushAt 2547 2 2112,
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
   pushAt 2572 2 3244,
   opAt 2573 .JUMPI]

/-- The five padding `JUMPDEST`s on the add-round fall-through (indices 2413 to 2417). -/
def blk3157c :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  []

/-- The subtract-round body up to its exit test (`blk3213` instructions 0..22). -/
def blk3213a :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2598 .JUMPDEST,
   opAt 2599 (.Dup ⟨0, by decide⟩),
   opAt 2600 .MLOAD,
   pushAt 2601 2 2112,
   opAt 2602 (.Dup ⟨2, by decide⟩),
   opAt 2603 .SUB,
   opAt 2604 .MLOAD,
   opAt 2605 (.Dup ⟨1, by decide⟩),
   opAt 2606 (.Dup ⟨1, by decide⟩),
   opAt 2607 .GT,
   opAt 2608 (.Swap ⟨1, by decide⟩),
   opAt 2609 .SUB,
   opAt 2610 (.Dup ⟨3, by decide⟩),
   opAt 2611 (.Dup ⟨1, by decide⟩),
   opAt 2612 .LT,
   opAt 2613 (.Swap ⟨0, by decide⟩),
   opAt 2614 (.Dup ⟨4, by decide⟩),
   opAt 2615 (.Swap ⟨0, by decide⟩),
   opAt 2616 .SUB,
   opAt 2617 (.Dup ⟨3, by decide⟩),
   opAt 2618 .MSTORE,
   opAt 2619 .OR]

/-- The exit test of the subtract-round body (`blk3213` instructions 23..31). -/
def blk3213b :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2620 (.Swap ⟨1, by decide⟩),
   opAt 2621 .POP,
   pushAt 2622 1 31,
   opAt 2623 .NOT,
   opAt 2624 .ADD,
   pushAt 2625 2 2111,
   opAt 2626 (.Dup ⟨1, by decide⟩),
   opAt 2627 .GT,
   pushAt 2628 2 3284,
   opAt 2629 .JUMPI]

end Challenge.Modexp.Submission.Proofs.Fast
