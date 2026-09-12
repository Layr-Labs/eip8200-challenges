import Challenge.Modexp.Submission.Proofs.Fast.Paths.P4
set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000
/-!
# Located paths for the full-width-base helper

The helper is appended after the fixed-window and direct-RR helpers. Its miss
path reproduces the original base-head computation before jumping to the
unchanged base loop at pc 1668.
-/

namespace Challenge.Modexp.Submission.Proofs.Fast

open EvmSemantics
open EvmSemantics.EVM
open Challenge.Modexp.Submission.Proofs.Bytecode

/-- Located block in the selected full-width-base helper. -/
def blkFullBaseGuard :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2304 .JUMPDEST,
   opAt 2305 (.Dup ⟨0, by decide⟩),
   opAt 2306 (.Dup ⟨3, by decide⟩),
   opAt 2307 .EQ,
   pushAt 2308 0 0,
   opAt 2309 .MLOAD,
   pushAt 2310 1 255,
   opAt 2311 .SHR,
   opAt 2312 .AND,
   opAt 2313 .ISZERO,
   pushAt 2314 2 3045,
   opAt 2315 .JUMPI]

/-- Located block in the selected full-width-base helper. -/
def blkFullBaseCopyAdd :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2316 (.Dup ⟨0, by decide⟩),
   pushAt 2317 1 96,
   pushAt 2318 2 256,
   opAt 2319 .CALLDATACOPY,
   pushAt 2320 2 1604,
   pushAt 2321 2 512,
   pushAt 2322 2 256,
   pushAt 2323 2 1536,
   pushAt 2324 2 4047,
   opAt 2325 .JUMP]

/-- Located block in the selected full-width-base helper. -/
def blkFullBaseFallback :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2326 .JUMPDEST,
   opAt 2327 (.Dup ⟨2, by decide⟩),
   pushAt 2328 1 31,
   opAt 2329 .ADD,
   pushAt 2330 1 5,
   opAt 2331 .SHR,
   opAt 2332 (.Dup ⟨3, by decide⟩),
   opAt 2333 (.Dup ⟨1, by decide⟩),
   pushAt 2334 1 5,
   opAt 2335 .SHL,
   opAt 2336 .SUB,
   pushAt 2337 1 3,
   opAt 2338 .SHL,
   pushAt 2339 1 96,
   opAt 2340 .CALLDATALOAD,
   opAt 2341 (.Swap ⟨0, by decide⟩),
   opAt 2342 .SHR,
   opAt 2343 (.Dup ⟨2, by decide⟩),
   pushAt 2344 2 224,
   opAt 2345 .ADD,
   opAt 2346 .MSTORE,
   pushAt 2347 1 1,
   pushAt 2348 2 1518,
   opAt 2349 .JUMP]

end Challenge.Modexp.Submission.Proofs.Fast
