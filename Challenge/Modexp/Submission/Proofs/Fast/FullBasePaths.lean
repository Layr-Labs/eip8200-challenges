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
  [opAt 2277 .JUMPDEST,
   opAt 2278 (.Dup ⟨0, by decide⟩),
   opAt 2279 (.Dup ⟨3, by decide⟩),
   opAt 2280 .EQ,
   pushAt 2281 0 0,
   opAt 2282 .MLOAD,
   pushAt 2283 1 255,
   opAt 2284 .SHR,
   opAt 2285 .AND,
   opAt 2286 .ISZERO,
   pushAt 2287 2 3045,
   opAt 2288 .JUMPI]

/-- Located block in the selected full-width-base helper. -/
def blkFullBaseCopyAdd :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2289 (.Dup ⟨0, by decide⟩),
   pushAt 2290 1 96,
   pushAt 2291 2 256,
   opAt 2292 .CALLDATACOPY,
   pushAt 2293 2 3216,
   pushAt 2294 2 512,
   pushAt 2295 2 256,
   pushAt 2296 2 1536,
   pushAt 2297 2 4092,
   opAt 2298 .JUMP]

/-- Located block in the selected full-width-base helper. -/
def blkFullBaseFallback :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2299 .JUMPDEST,
   opAt 2300 (.Dup ⟨2, by decide⟩),
   pushAt 2301 1 31,
   opAt 2302 .ADD,
   pushAt 2303 1 5,
   opAt 2304 .SHR,
   opAt 2305 (.Dup ⟨3, by decide⟩),
   opAt 2306 (.Dup ⟨1, by decide⟩),
   pushAt 2307 1 5,
   opAt 2308 .SHL,
   opAt 2309 .SUB,
   pushAt 2310 1 3,
   opAt 2311 .SHL,
   pushAt 2312 1 96,
   opAt 2313 .CALLDATALOAD,
   opAt 2314 (.Swap ⟨0, by decide⟩),
   opAt 2315 .SHR,
   opAt 2316 (.Dup ⟨2, by decide⟩),
   pushAt 2317 1 224,
   opAt 2318 .ADD,
   opAt 2319 .MSTORE,
   pushAt 2320 1 1,
   pushAt 2321 2 1513,
   opAt 2322 .JUMP]

end Challenge.Modexp.Submission.Proofs.Fast
