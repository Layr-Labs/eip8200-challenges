import Challenge.Modexp.Submission.Proofs.Fast.Defs
set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000
/-! Basic-block instruction paths for the appended `LZBASE` shortcut.

The byte-zero arm of `LZ` reaches instruction 2338 (pc 3571) with
`[mask, w, i] ++ OUTER`.  A nonzero byte copies `BASE` to `ACC` and resumes
at the mask shift; a zero byte rejoins the ordinary bit-loop head. -/

namespace Challenge.Modexp.Submission.Proofs.Fast
open EvmSemantics
open EvmSemantics.EVM
open Challenge.Modexp.Submission.Proofs.Bytecode

/-- `LZBASE`'s zero test, indices 2338..2342, pc 3571..3577. -/
def blk2338 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2338 .JUMPDEST,
   opAt 2339 (.Dup ⟨1, by decide⟩),
   opAt 2340 .ISZERO,
   pushAt 2341 2 3593,
   opAt 2342 .JUMPI]

/-- `LZBASE`'s copy-and-resume arm, indices 2343..2349, pc 3578..3592. -/
def blk2343 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 2343 2 9344,
   opAt 2344 .MLOAD,
   pushAt 2345 2 2048,
   pushAt 2346 2 1024,
   opAt 2347 .MCOPY,
   pushAt 2348 2 1832,
   opAt 2349 .JUMP]

/-- `LZBASE`'s zero-byte arm, indices 2350..2352, pc 3593..3597. -/
def blk2350 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2350 .JUMPDEST,
   pushAt 2351 2 1789,
   opAt 2352 .JUMP]

end Challenge.Modexp.Submission.Proofs.Fast
