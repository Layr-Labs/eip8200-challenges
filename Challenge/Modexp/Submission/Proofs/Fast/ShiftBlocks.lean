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
  [opAt 2621 .JUMPDEST,
   opAt 2622 (.Dup ⟨0, by decide⟩),
   opAt 2623 .MLOAD,
   opAt 2624 .NOT,
   opAt 2625 (.Dup ⟨2, by decide⟩),
   opAt 2626 .ADD,
   opAt 2627 (.Dup ⟨2, by decide⟩),
   opAt 2628 (.Dup ⟨1, by decide⟩),
   opAt 2629 .LT,
   opAt 2630 (.Swap ⟨2, by decide⟩),
   opAt 2631 .POP,
   opAt 2632 (.Dup ⟨1, by decide⟩),
   pushAt 2633 2 1280,
   opAt 2634 .ADD,
   opAt 2635 .MSTORE]

/-- The exit test of the negation loop body (`blk2896` instructions 15..18). -/
def blk2896b :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2636 (.Dup ⟨0, by decide⟩),
   opAt 2637 .ISZERO,
   pushAt 2638 2 3536,
   opAt 2639 .JUMPI]

/-- The limb-pass body up to its exit test (`blk3077` instructions 0..42). -/
def blk3077a :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  mac2PathA

/-- The second identical MAC body, entered for an odd number of remaining limbs. -/
def blkMacSecond :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  mac2PathB

/-- The exit test of the limb-pass body (`blk3077` instructions 43..47). -/
def blk3077b :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  mac2PathTail

/-- The add-round body up to its exit test (`blk3157` instructions 0..26). -/
def blk3157a :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2938 .JUMPDEST,
   opAt 2939 (.Dup ⟨0, by decide⟩),
   opAt 2940 .MLOAD,
   opAt 2941 (.Dup ⟨1, by decide⟩),
   pushAt 2942 2 4160,
   opAt 2943 (.Swap ⟨0, by decide⟩),
   opAt 2944 .SUB,
   opAt 2945 .MLOAD,
   opAt 2946 (.Dup ⟨1, by decide⟩),
   opAt 2947 .ADD,
   opAt 2948 (.Dup ⟨0, by decide⟩),
   opAt 2949 (.Dup ⟨2, by decide⟩),
   opAt 2950 .GT,
   opAt 2951 (.Swap ⟨1, by decide⟩),
   opAt 2952 .POP,
   opAt 2953 (.Dup ⟨3, by decide⟩),
   opAt 2954 .ADD,
   opAt 2955 (.Dup ⟨0, by decide⟩),
   opAt 2956 (.Dup ⟨4, by decide⟩),
   opAt 2957 .GT,
   opAt 2958 (.Swap ⟨3, by decide⟩),
   opAt 2959 .POP,
   opAt 2960 (.Dup ⟨2, by decide⟩),
   opAt 2961 .MSTORE,
   opAt 2962 (.Swap ⟨0, by decide⟩),
   opAt 2963 (.Swap ⟨1, by decide⟩),
   opAt 2964 .OR]

/-- The exit test of the add-round body (`blk3157` instructions 27..34). -/
def blk3157b :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2965 (.Swap ⟨0, by decide⟩),
   pushAt 2966 1 31,
   opAt 2967 .NOT,
   opAt 2968 .ADD,
   pushAt 2969 2 4159,
   opAt 2970 (.Dup ⟨1, by decide⟩),
   opAt 2971 .GT,
   pushAt 2972 2 3901,
   opAt 2973 .JUMPI]

/-- The subtract-round body up to its exit test (`blk3213` instructions 0..22). -/
def blk3213a :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2995 .JUMPDEST,
   opAt 2996 (.Dup ⟨0, by decide⟩),
   opAt 2997 .MLOAD,
   pushAt 2998 2 4160,
   opAt 2999 (.Dup ⟨2, by decide⟩),
   opAt 3000 .SUB,
   opAt 3001 .MLOAD,
   opAt 3002 (.Dup ⟨1, by decide⟩),
   opAt 3003 (.Dup ⟨1, by decide⟩),
   opAt 3004 .GT,
   opAt 3005 (.Swap ⟨1, by decide⟩),
   opAt 3006 .SUB,
   opAt 3007 (.Dup ⟨3, by decide⟩),
   opAt 3008 (.Dup ⟨1, by decide⟩),
   opAt 3009 .LT,
   opAt 3010 (.Swap ⟨0, by decide⟩),
   opAt 3011 (.Dup ⟨4, by decide⟩),
   opAt 3012 (.Swap ⟨0, by decide⟩),
   opAt 3013 .SUB,
   opAt 3014 (.Dup ⟨3, by decide⟩),
   opAt 3015 .MSTORE,
   opAt 3016 .OR]

/-- The exit test of the subtract-round body (`blk3213` instructions 23..31). -/
def blk3213b :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 3017 (.Swap ⟨1, by decide⟩),
   opAt 3018 .POP,
   pushAt 3019 1 31,
   opAt 3020 .NOT,
   opAt 3021 .ADD,
   pushAt 3022 2 4159,
   opAt 3023 (.Dup ⟨1, by decide⟩),
   opAt 3024 .GT,
   pushAt 3025 2 3977,
   opAt 3026 .JUMPI]

end Challenge.Modexp.Submission.Proofs.Fast
