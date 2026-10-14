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
  [opAt 1965 .JUMPDEST,
   opAt 1966 (.Dup ⟨1, by decide⟩),
   opAt 1967 .MLOAD,
   opAt 1968 .NOT,
   opAt 1969 .ADD,
   opAt 1970 (.Dup ⟨1, by decide⟩),
   pushAt 1971 2 1280,
   opAt 1972 .ADD,
   opAt 1973 .MSTORE,
   pushAt 1974 0 0]

/-- The rotated exit test of the negation loop body: `p - 32` goes under the flag, the
jump back to the loop head is taken on the old pointer `p`, and `p = 0` falls into the
`NEG_DONE` padding. -/
def blk2896b :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1975 (.Dup ⟨1, by decide⟩),
   pushAt 1976 1 31,
   opAt 1977 .NOT,
   opAt 1978 .ADD,
   opAt 1979 (.Swap ⟨1, by decide⟩),
   pushAt 1980 2 2509,
   opAt 1981 .JUMPI]



/-- The add-round body up to its store (`blk3157` instructions 0..22). -/
def blk3157a :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2422 .JUMPDEST,
   opAt 2423 (.Dup ⟨0, by decide⟩),
   opAt 2424 .MLOAD,
   pushAt 2425 2 2112,
   opAt 2426 (.Dup ⟨2, by decide⟩),
   opAt 2427 .SUB,
   opAt 2428 .MLOAD,
   opAt 2429 (.Dup ⟨1, by decide⟩),
   opAt 2430 .ADD,
   opAt 2431 (.Swap ⟨0, by decide⟩),
   opAt 2432 (.Dup ⟨1, by decide⟩),
   opAt 2433 .LT,
   opAt 2434 (.Swap ⟨0, by decide⟩),
   opAt 2435 (.Dup ⟨3, by decide⟩),
   opAt 2436 .ADD,
   opAt 2437 (.Swap ⟨2, by decide⟩),
   opAt 2438 (.Dup ⟨3, by decide⟩),
   opAt 2439 .LT,
   opAt 2440 .OR,
   opAt 2441 (.Swap ⟨1, by decide⟩),
   opAt 2442 (.Dup ⟨1, by decide⟩),
   opAt 2443 .MSTORE]

/-- The exit test of the add-round body (`blk3157` instructions 23..30). -/
def blk3157b :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 2444 1 31,
   opAt 2445 .NOT,
   opAt 2446 .ADD,
   pushAt 2447 2 2111,
   opAt 2448 (.Dup ⟨1, by decide⟩),
   opAt 2449 .GT,
   pushAt 2450 2 3088,
   opAt 2451 .JUMPI]

/-- The five padding `JUMPDEST`s on the add-round fall-through (indices 2413 to 2417). -/
def blk3157c :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  []

end Challenge.Modexp.Submission.Proofs.Fast
