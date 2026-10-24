import Challenge.Modexp.Submission.Proofs.Fast.Defs
set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000
/-! Basic-block instruction paths, group 0 (instructions 977..1027). -/

namespace Challenge.Modexp.Submission.Proofs.Fast

open EvmSemantics
open EvmSemantics.EVM
open Challenge.Modexp.Submission.Proofs.Bytecode

def blk977 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 404 .JUMPDEST,
   pushAt 405 1 64,
   opAt 406 .CALLDATALOAD,
   pushAt 407 1 33,
   opAt 408 (.Dup ⟨1, by decide⟩),
   opAt 409 .SUB,
   pushAt 410 1 223,
   opAt 411 .LT,
   pushAt 412 2 697,
   opAt 413 .JUMPI]

def blk986 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 414 1 32,
   opAt 415 .CALLDATALOAD,
   pushAt 416 0 0,
   opAt 417 .CALLDATALOAD]

def blk1003 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 418 1 31,
   opAt 419 (.Dup ⟨3, by decide⟩),
   opAt 420 .ADD,
   pushAt 421 1 5,
   opAt 422 .SHR,
   opAt 423 (.Dup ⟨0, by decide⟩),
   pushAt 424 1 5,
   opAt 425 .SHL,
   pushAt 426 1 96,
   opAt 427 (.Dup ⟨3, by decide⟩),
   opAt 428 .ADD,
   opAt 429 (.Dup ⟨4, by decide⟩),
   opAt 430 .ADD,
   opAt 431 (.Dup ⟨0, by decide⟩),
   opAt 432 .CALLDATALOAD,
   pushAt 433 1 255,
   opAt 434 .SHR,
   opAt 435 .ISZERO,
   pushAt 436 1 219,
   opAt 437 .JUMPI]

end Challenge.Modexp.Submission.Proofs.Fast
