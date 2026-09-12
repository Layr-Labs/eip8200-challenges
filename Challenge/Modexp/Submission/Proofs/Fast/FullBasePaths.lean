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
  [opAt 2279 .JUMPDEST,
   opAt 2280 (.Dup ⟨0, by decide⟩),
   opAt 2281 (.Dup ⟨3, by decide⟩),
   opAt 2282 .EQ,
   pushAt 2283 0 0,
   opAt 2284 .MLOAD,
   pushAt 2285 1 255,
   opAt 2286 .SHR,
   opAt 2287 .AND,
   opAt 2288 .ISZERO,
   pushAt 2289 2 3045,
   opAt 2290 .JUMPI]

/-- Located block in the selected full-width-base helper. -/
def blkFullBaseCopyAdd :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2291 (.Dup ⟨0, by decide⟩),
   pushAt 2292 1 96,
   pushAt 2293 2 256,
   opAt 2294 .CALLDATACOPY,
   pushAt 2295 2 1604,
   pushAt 2296 2 512,
   pushAt 2297 2 256,
   pushAt 2298 2 1536,
   pushAt 2299 2 4047,
   opAt 2300 .JUMP]

/-- Located block in the selected full-width-base helper. -/
def blkFullBaseFallback :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2301 .JUMPDEST,
   opAt 2302 (.Dup ⟨2, by decide⟩),
   pushAt 2303 1 31,
   opAt 2304 .ADD,
   pushAt 2305 1 5,
   opAt 2306 .SHR,
   opAt 2307 (.Dup ⟨3, by decide⟩),
   opAt 2308 (.Dup ⟨1, by decide⟩),
   pushAt 2309 1 5,
   opAt 2310 .SHL,
   opAt 2311 .SUB,
   pushAt 2312 1 3,
   opAt 2313 .SHL,
   pushAt 2314 1 96,
   opAt 2315 .CALLDATALOAD,
   opAt 2316 (.Swap ⟨0, by decide⟩),
   opAt 2317 .SHR,
   opAt 2318 (.Dup ⟨2, by decide⟩),
   pushAt 2319 2 224,
   opAt 2320 .ADD,
   opAt 2321 .MSTORE,
   pushAt 2322 1 1,
   pushAt 2323 2 1518,
   opAt 2324 .JUMP]

end Challenge.Modexp.Submission.Proofs.Fast
