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
  [opAt 2502 .JUMPDEST,
   opAt 2503 (.Dup ⟨0, by decide⟩),
   opAt 2504 .MLOAD,
   pushAt 2505 2 2112,
   opAt 2506 (.Dup ⟨2, by decide⟩),
   opAt 2507 .SUB,
   opAt 2508 .MLOAD,
   opAt 2509 (.Dup ⟨1, by decide⟩),
   opAt 2510 .ADD,
   opAt 2511 (.Swap ⟨0, by decide⟩),
   opAt 2512 (.Dup ⟨1, by decide⟩),
   opAt 2513 .LT,
   opAt 2514 (.Swap ⟨0, by decide⟩),
   opAt 2515 (.Dup ⟨3, by decide⟩),
   opAt 2516 .ADD,
   opAt 2517 (.Swap ⟨2, by decide⟩),
   opAt 2518 (.Dup ⟨3, by decide⟩),
   opAt 2519 .LT,
   opAt 2520 .OR,
   opAt 2521 (.Swap ⟨1, by decide⟩),
   opAt 2522 (.Dup ⟨1, by decide⟩),
   opAt 2523 .MSTORE]

/-- The exit test of the add-round body (`blk3157` instructions 23..30). -/
def blk3157b :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 2524 1 31,
   opAt 2525 .NOT,
   opAt 2526 .ADD,
   pushAt 2527 2 2111,
   opAt 2528 (.Dup ⟨1, by decide⟩),
   opAt 2529 .GT,
   pushAt 2530 2 3220,
   opAt 2531 .JUMPI]

/-- The five padding `JUMPDEST`s on the add-round fall-through (indices 2413 to 2417). -/
def blk3157c :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  []

/-- The subtract-round body up to its exit test (`blk3213` instructions 0..22). -/
def blk3213a :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2556 .JUMPDEST,
   opAt 2557 (.Dup ⟨0, by decide⟩),
   opAt 2558 .MLOAD,
   pushAt 2559 2 2112,
   opAt 2560 (.Dup ⟨2, by decide⟩),
   opAt 2561 .SUB,
   opAt 2562 .MLOAD,
   opAt 2563 (.Dup ⟨1, by decide⟩),
   opAt 2564 (.Dup ⟨1, by decide⟩),
   opAt 2565 .GT,
   opAt 2566 (.Swap ⟨1, by decide⟩),
   opAt 2567 .SUB,
   opAt 2568 (.Dup ⟨3, by decide⟩),
   opAt 2569 (.Dup ⟨1, by decide⟩),
   opAt 2570 .LT,
   opAt 2571 (.Swap ⟨0, by decide⟩),
   opAt 2572 (.Dup ⟨4, by decide⟩),
   opAt 2573 (.Swap ⟨0, by decide⟩),
   opAt 2574 .SUB,
   opAt 2575 (.Dup ⟨3, by decide⟩),
   opAt 2576 .MSTORE,
   opAt 2577 .OR]

/-- The exit test of the subtract-round body (`blk3213` instructions 23..31). -/
def blk3213b :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2578 (.Swap ⟨1, by decide⟩),
   opAt 2579 .POP,
   pushAt 2580 1 31,
   opAt 2581 .NOT,
   opAt 2582 .ADD,
   pushAt 2583 2 2111,
   opAt 2584 (.Dup ⟨1, by decide⟩),
   opAt 2585 .GT,
   pushAt 2586 2 3284,
   opAt 2587 .JUMPI]

end Challenge.Modexp.Submission.Proofs.Fast
