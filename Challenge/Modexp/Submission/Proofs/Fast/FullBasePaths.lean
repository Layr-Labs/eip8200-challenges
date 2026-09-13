import Challenge.Modexp.Submission.Proofs.Fast.Paths.P4
set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000
/-!
# Located paths for the full-width-base helper

The helper is appended after the fixed-window and direct-RR helpers. Its miss
path reproduces the original base-head computation before jumping to the
unchanged base loop at pc 1795.
-/

namespace Challenge.Modexp.Submission.Proofs.Fast

open EvmSemantics
open EvmSemantics.EVM
open Challenge.Modexp.Submission.Proofs.Bytecode

/-- Located block in the selected full-width-base helper. -/
def blkFullBaseGuard :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2284 .JUMPDEST,
   opAt 2285 (.Dup ⟨0, by decide⟩),
   opAt 2286 (.Dup ⟨3, by decide⟩),
   opAt 2287 .EQ,
   pushAt 2288 0 0,
   opAt 2289 .MLOAD,
   pushAt 2290 1 255,
   opAt 2291 .SHR,
   opAt 2292 .AND,
   opAt 2293 .ISZERO,
   pushAt 2294 2 3045,
   opAt 2295 .JUMPI]

/-- Located block in the selected full-width-base helper. -/
def blkFullBaseCopyAdd :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2296 (.Dup ⟨0, by decide⟩),
   pushAt 2297 1 96,
   pushAt 2298 2 256,
   opAt 2299 .CALLDATACOPY,
   pushAt 2300 2 3216,
   pushAt 2301 2 512,
   pushAt 2302 2 256,
   pushAt 2303 2 1536,
   pushAt 2304 2 4086,
   opAt 2305 .JUMP]

/-- Located block in the selected full-width-base helper. -/
def blkFullBaseFallback :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2306 .JUMPDEST,
   opAt 2307 (.Dup ⟨2, by decide⟩),
   pushAt 2308 1 31,
   opAt 2309 .ADD,
   pushAt 2310 1 5,
   opAt 2311 .SHR,
   opAt 2312 (.Dup ⟨3, by decide⟩),
   opAt 2313 (.Dup ⟨1, by decide⟩),
   pushAt 2314 1 5,
   opAt 2315 .SHL,
   opAt 2316 .SUB,
   pushAt 2317 1 3,
   opAt 2318 .SHL,
   pushAt 2319 1 96,
   opAt 2320 .CALLDATALOAD,
   opAt 2321 (.Swap ⟨0, by decide⟩),
   opAt 2322 .SHR,
   opAt 2323 (.Dup ⟨2, by decide⟩),
   pushAt 2324 1 224,
   opAt 2325 .ADD,
   opAt 2326 .MSTORE,
   pushAt 2327 1 1,
   pushAt 2328 2 1513,
   opAt 2329 .JUMP]

end Challenge.Modexp.Submission.Proofs.Fast
