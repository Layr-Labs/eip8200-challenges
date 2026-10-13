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
  [opAt 2019 .JUMPDEST,
   opAt 2020 (.Dup ⟨1, by decide⟩),
   opAt 2021 .MLOAD,
   opAt 2022 .NOT,
   opAt 2023 .ADD,
   opAt 2024 (.Dup ⟨1, by decide⟩),
   pushAt 2025 2 1280,
   opAt 2026 .ADD,
   opAt 2027 .MSTORE,
   pushAt 2028 0 0]

/-- The rotated exit test of the negation loop body: `p - 32` goes under the flag, the
jump back to the loop head is taken on the old pointer `p`, and `p = 0` falls into the
`NEG_DONE` padding. -/
def blk2896b :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2029 (.Dup ⟨1, by decide⟩),
   pushAt 2030 1 31,
   opAt 2031 .NOT,
   opAt 2032 .ADD,
   opAt 2033 (.Swap ⟨1, by decide⟩),
   pushAt 2034 2 2589,
   opAt 2035 .JUMPI]



/-- The add-round body up to its store (`blk3157` instructions 0..22). -/
def blk3157a :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2503 .JUMPDEST,
   opAt 2504 (.Dup ⟨0, by decide⟩),
   opAt 2505 .MLOAD,
   pushAt 2506 2 2112,
   opAt 2507 (.Dup ⟨2, by decide⟩),
   opAt 2508 .SUB,
   opAt 2509 .MLOAD,
   opAt 2510 (.Dup ⟨1, by decide⟩),
   opAt 2511 .ADD,
   opAt 2512 (.Swap ⟨0, by decide⟩),
   opAt 2513 (.Dup ⟨1, by decide⟩),
   opAt 2514 .LT,
   opAt 2515 (.Swap ⟨0, by decide⟩),
   opAt 2516 (.Dup ⟨3, by decide⟩),
   opAt 2517 .ADD,
   opAt 2518 (.Swap ⟨2, by decide⟩),
   opAt 2519 (.Dup ⟨3, by decide⟩),
   opAt 2520 .LT,
   opAt 2521 .OR,
   opAt 2522 (.Swap ⟨1, by decide⟩),
   opAt 2523 (.Dup ⟨1, by decide⟩),
   opAt 2524 .MSTORE]

/-- The exit test of the add-round body (`blk3157` instructions 23..30). -/
def blk3157b :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 2525 1 31,
   opAt 2526 .NOT,
   opAt 2527 .ADD,
   pushAt 2528 2 2111,
   opAt 2529 (.Dup ⟨1, by decide⟩),
   opAt 2530 .GT,
   pushAt 2531 2 3220,
   opAt 2532 .JUMPI]

/-- The five padding `JUMPDEST`s on the add-round fall-through (indices 2413 to 2417). -/
def blk3157c :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  []

/-- The subtract-round body up to its exit test (`blk3213` instructions 0..22). -/
def blk3213a :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2557 .JUMPDEST,
   opAt 2558 (.Dup ⟨0, by decide⟩),
   opAt 2559 .MLOAD,
   pushAt 2560 2 2112,
   opAt 2561 (.Dup ⟨2, by decide⟩),
   opAt 2562 .SUB,
   opAt 2563 .MLOAD,
   opAt 2564 (.Dup ⟨1, by decide⟩),
   opAt 2565 (.Dup ⟨1, by decide⟩),
   opAt 2566 .GT,
   opAt 2567 (.Swap ⟨1, by decide⟩),
   opAt 2568 .SUB,
   opAt 2569 (.Dup ⟨3, by decide⟩),
   opAt 2570 (.Dup ⟨1, by decide⟩),
   opAt 2571 .LT,
   opAt 2572 (.Swap ⟨0, by decide⟩),
   opAt 2573 (.Dup ⟨4, by decide⟩),
   opAt 2574 (.Swap ⟨0, by decide⟩),
   opAt 2575 .SUB,
   opAt 2576 (.Dup ⟨3, by decide⟩),
   opAt 2577 .MSTORE,
   opAt 2578 .OR]

/-- The exit test of the subtract-round body (`blk3213` instructions 23..31). -/
def blk3213b :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2579 (.Swap ⟨1, by decide⟩),
   opAt 2580 .POP,
   pushAt 2581 1 31,
   opAt 2582 .NOT,
   opAt 2583 .ADD,
   pushAt 2584 2 2111,
   opAt 2585 (.Dup ⟨1, by decide⟩),
   opAt 2586 .GT,
   pushAt 2587 2 3284,
   opAt 2588 .JUMPI]

end Challenge.Modexp.Submission.Proofs.Fast
