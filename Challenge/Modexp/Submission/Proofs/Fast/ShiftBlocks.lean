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

/-- The add-round body up to its store (`blk3157` instructions 0..22). -/
def blk3157a :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2411 .JUMPDEST,
   opAt 2412 (.Dup ⟨0, by decide⟩),
   opAt 2413 .MLOAD,
   pushAt 2414 2 2112,
   opAt 2415 (.Dup ⟨2, by decide⟩),
   opAt 2416 .SUB,
   opAt 2417 .MLOAD,
   opAt 2418 (.Dup ⟨1, by decide⟩),
   opAt 2419 .ADD,
   opAt 2420 (.Swap ⟨0, by decide⟩),
   opAt 2421 (.Dup ⟨1, by decide⟩),
   opAt 2422 .LT,
   opAt 2423 (.Swap ⟨0, by decide⟩),
   opAt 2424 (.Dup ⟨3, by decide⟩),
   opAt 2425 .ADD,
   opAt 2426 (.Swap ⟨2, by decide⟩),
   opAt 2427 (.Dup ⟨3, by decide⟩),
   opAt 2428 .LT,
   opAt 2429 .OR,
   opAt 2430 (.Swap ⟨1, by decide⟩),
   opAt 2431 (.Dup ⟨1, by decide⟩),
   opAt 2432 .MSTORE]

/-- The exit test of the add-round body (`blk3157` instructions 23..30). -/
def blk3157b :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 2433 1 31,
   opAt 2434 .NOT,
   opAt 2435 .ADD,
   pushAt 2436 2 2111,
   opAt 2437 (.Dup ⟨1, by decide⟩),
   opAt 2438 .GT,
   pushAt 2439 2 3081,
   opAt 2440 .JUMPI]

/-- The five padding `JUMPDEST`s on the add-round fall-through (indices 2413 to 2417). -/
def blk3157c :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  []

end Challenge.Modexp.Submission.Proofs.Fast
