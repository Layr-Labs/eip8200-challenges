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
  [opAt 2595 .JUMPDEST,
   opAt 2596 (.Dup ⟨0, by decide⟩),
   opAt 2597 .MLOAD,
   opAt 2598 .NOT,
   opAt 2599 (.Dup ⟨2, by decide⟩),
   opAt 2600 .ADD,
   opAt 2601 (.Dup ⟨2, by decide⟩),
   opAt 2602 (.Dup ⟨1, by decide⟩),
   opAt 2603 .LT,
   opAt 2604 (.Swap ⟨2, by decide⟩),
   opAt 2605 .POP,
   opAt 2606 (.Dup ⟨1, by decide⟩),
   pushAt 2607 2 5120,
   opAt 2608 .ADD,
   opAt 2609 .MSTORE]

/-- The exit test of the negation loop body (`blk2896` instructions 15..18). -/
def blk2896b :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2610 (.Dup ⟨0, by decide⟩),
   opAt 2611 .ISZERO,
   pushAt 2612 2 3436,
   opAt 2613 .JUMPI]

/-- The limb-pass body up to its exit test (`blk3077` instructions 0..42). -/
def blk3077a :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2802 .JUMPDEST,
   opAt 2803 (.Dup ⟨0, by decide⟩),
   opAt 2804 .MLOAD,
   pushAt 2805 0 0,
   opAt 2806 .NOT,
   opAt 2807 (.Dup ⟨6, by decide⟩),
   opAt 2808 (.Dup ⟨2, by decide⟩),
   opAt 2809 .MUL,
   opAt 2810 (.Swap ⟨1, by decide⟩),
   opAt 2811 (.Dup ⟨7, by decide⟩),
   opAt 2812 .MULMOD,
   opAt 2813 (.Dup ⟨1, by decide⟩),
   opAt 2814 (.Dup ⟨1, by decide⟩),
   opAt 2815 .LT,
   opAt 2816 .SUB,
   opAt 2817 (.Dup ⟨5, by decide⟩),
   opAt 2818 (.Dup ⟨2, by decide⟩),
   opAt 2819 .ADD,
   opAt 2820 (.Dup ⟨0, by decide⟩),
   opAt 2821 (.Swap ⟨6, by decide⟩),
   opAt 2822 .GT,
   opAt 2823 .SUB,
   opAt 2824 .SUB,
   opAt 2825 (.Dup ⟨4, by decide⟩),
   opAt 2826 (.Dup ⟨3, by decide⟩),
   opAt 2827 .MLOAD,
   opAt 2828 .ADD,
   opAt 2829 (.Dup ⟨0, by decide⟩),
   opAt 2830 (.Swap ⟨5, by decide⟩),
   opAt 2831 .GT,
   opAt 2832 .ADD,
   opAt 2833 (.Swap ⟨3, by decide⟩),
   opAt 2834 (.Dup ⟨2, by decide⟩),
   opAt 2835 (.Dup ⟨4, by decide⟩),
   opAt 2836 .ADD,
   opAt 2837 (.Swap ⟨2, by decide⟩),
   opAt 2838 .MSTORE,
   opAt 2839 (.Dup ⟨2, by decide⟩),
   opAt 2840 .ADD]

/-- The exit test of the limb-pass body (`blk3077` instructions 43..47). -/
def blk3077b :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 2958 2 8224,
   opAt 2959 (.Dup ⟨2, by decide⟩),
   opAt 2960 .GT,
   pushAt 2961 2 3684,
   opAt 2962 .JUMPI]

/-- The add-round body up to its exit test (`blk3157` instructions 0..26). -/
def blk3157a :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2996 .JUMPDEST,
   opAt 2997 (.Dup ⟨0, by decide⟩),
   opAt 2998 .MLOAD,
   opAt 2999 (.Dup ⟨1, by decide⟩),
   pushAt 3000 2 8256,
   opAt 3001 (.Swap ⟨0, by decide⟩),
   opAt 3002 .SUB,
   opAt 3003 .MLOAD,
   opAt 3004 (.Dup ⟨1, by decide⟩),
   opAt 3005 .ADD,
   opAt 3006 (.Dup ⟨0, by decide⟩),
   opAt 3007 (.Dup ⟨2, by decide⟩),
   opAt 3008 .GT,
   opAt 3009 (.Swap ⟨1, by decide⟩),
   opAt 3010 .POP,
   opAt 3011 (.Dup ⟨3, by decide⟩),
   opAt 3012 .ADD,
   opAt 3013 (.Dup ⟨0, by decide⟩),
   opAt 3014 (.Dup ⟨4, by decide⟩),
   opAt 3015 .GT,
   opAt 3016 (.Swap ⟨3, by decide⟩),
   opAt 3017 .POP,
   opAt 3018 (.Dup ⟨2, by decide⟩),
   opAt 3019 .MSTORE,
   opAt 3020 (.Swap ⟨0, by decide⟩),
   opAt 3021 (.Swap ⟨1, by decide⟩),
   opAt 3022 .OR]

/-- The exit test of the add-round body (`blk3157` instructions 27..34). -/
def blk3157b :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 3023 (.Swap ⟨0, by decide⟩),
   pushAt 3024 1 31,
   opAt 3025 .NOT,
   opAt 3026 .ADD,
   pushAt 3027 2 8255,
   opAt 3028 (.Dup ⟨1, by decide⟩),
   opAt 3029 .GT,
   pushAt 3030 2 3890,
   opAt 3031 .JUMPI]

/-- The subtract-round body up to its exit test (`blk3213` instructions 0..22). -/
def blk3213a :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 3053 .JUMPDEST,
   opAt 3054 (.Dup ⟨0, by decide⟩),
   opAt 3055 .MLOAD,
   pushAt 3056 2 8256,
   opAt 3057 (.Dup ⟨2, by decide⟩),
   opAt 3058 .SUB,
   opAt 3059 .MLOAD,
   opAt 3060 (.Dup ⟨1, by decide⟩),
   opAt 3061 (.Dup ⟨1, by decide⟩),
   opAt 3062 .GT,
   opAt 3063 (.Swap ⟨1, by decide⟩),
   opAt 3064 .SUB,
   opAt 3065 (.Dup ⟨3, by decide⟩),
   opAt 3066 (.Dup ⟨1, by decide⟩),
   opAt 3067 .LT,
   opAt 3068 (.Swap ⟨0, by decide⟩),
   opAt 3069 (.Dup ⟨4, by decide⟩),
   opAt 3070 (.Swap ⟨0, by decide⟩),
   opAt 3071 .SUB,
   opAt 3072 (.Dup ⟨3, by decide⟩),
   opAt 3073 .MSTORE,
   opAt 3074 .OR]

/-- The exit test of the subtract-round body (`blk3213` instructions 23..31). -/
def blk3213b :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 3075 (.Swap ⟨1, by decide⟩),
   opAt 3076 .POP,
   pushAt 3077 1 31,
   opAt 3078 .NOT,
   opAt 3079 .ADD,
   pushAt 3080 2 8255,
   opAt 3081 (.Dup ⟨1, by decide⟩),
   opAt 3082 .GT,
   pushAt 3083 2 3966,
   opAt 3084 .JUMPI]

end Challenge.Modexp.Submission.Proofs.Fast
