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
  [opAt 2303 .JUMPDEST,
   opAt 2304 (.Dup ⟨0, by decide⟩),
   opAt 2305 (.Dup ⟨3, by decide⟩),
   opAt 2306 .EQ,
   pushAt 2307 0 0,
   opAt 2308 .MLOAD,
   pushAt 2309 1 255,
   opAt 2310 .SHR,
   opAt 2311 .AND,
   opAt 2312 .ISZERO,
   pushAt 2313 2 3045,
   opAt 2314 .JUMPI]

/-- Located block in the selected full-width-base helper. -/
def blkFullBaseCopyAdd :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2315 (.Dup ⟨0, by decide⟩),
   pushAt 2316 1 96,
   pushAt 2317 2 1024,
   opAt 2318 .CALLDATACOPY,
   pushAt 2319 2 1604,
   pushAt 2320 2 2048,
   pushAt 2321 2 1024,
   pushAt 2322 2 6144,
   pushAt 2323 2 4047,
   opAt 2324 .JUMP]

/-- Located block in the selected full-width-base helper. -/
def blkFullBaseFallback :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2325 .JUMPDEST,
   opAt 2326 (.Dup ⟨2, by decide⟩),
   pushAt 2327 1 31,
   opAt 2328 .ADD,
   pushAt 2329 1 5,
   opAt 2330 .SHR,
   opAt 2331 (.Dup ⟨3, by decide⟩),
   opAt 2332 (.Dup ⟨1, by decide⟩),
   pushAt 2333 1 5,
   opAt 2334 .SHL,
   opAt 2335 .SUB,
   pushAt 2336 1 3,
   opAt 2337 .SHL,
   pushAt 2338 1 96,
   opAt 2339 .CALLDATALOAD,
   opAt 2340 (.Swap ⟨0, by decide⟩),
   opAt 2341 .SHR,
   opAt 2342 (.Dup ⟨2, by decide⟩),
   pushAt 2343 2 992,
   opAt 2344 .ADD,
   opAt 2345 .MSTORE,
   pushAt 2346 1 1,
   pushAt 2347 2 1518,
   opAt 2348 .JUMP]

end Challenge.Modexp.Submission.Proofs.Fast
