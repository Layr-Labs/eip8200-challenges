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
  [opAt 2278 .JUMPDEST,
   opAt 2279 (.Dup ⟨0, by decide⟩),
   opAt 2280 (.Dup ⟨3, by decide⟩),
   opAt 2281 .EQ,
   pushAt 2282 0 0,
   opAt 2283 .MLOAD,
   pushAt 2284 1 255,
   opAt 2285 .SHR,
   opAt 2286 .AND,
   opAt 2287 .ISZERO,
   pushAt 2288 2 3045,
   opAt 2289 .JUMPI]

/-- Located block in the selected full-width-base helper. -/
def blkFullBaseCopyAdd :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2290 (.Dup ⟨0, by decide⟩),
   pushAt 2291 1 96,
   pushAt 2292 2 256,
   opAt 2293 .CALLDATACOPY,
   pushAt 2294 2 3216,
   pushAt 2295 2 512,
   pushAt 2296 2 256,
   pushAt 2297 2 1536,
   pushAt 2298 2 4092,
   opAt 2299 .JUMP]

/-- Located block in the selected full-width-base helper. -/
def blkFullBaseFallback :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2300 .JUMPDEST,
   opAt 2301 (.Dup ⟨2, by decide⟩),
   pushAt 2302 1 31,
   opAt 2303 .ADD,
   pushAt 2304 1 5,
   opAt 2305 .SHR,
   opAt 2306 (.Dup ⟨3, by decide⟩),
   opAt 2307 (.Dup ⟨1, by decide⟩),
   pushAt 2308 1 5,
   opAt 2309 .SHL,
   opAt 2310 .SUB,
   pushAt 2311 1 3,
   opAt 2312 .SHL,
   pushAt 2313 1 96,
   opAt 2314 .CALLDATALOAD,
   opAt 2315 (.Swap ⟨0, by decide⟩),
   opAt 2316 .SHR,
   opAt 2317 (.Dup ⟨2, by decide⟩),
   pushAt 2318 1 224,
   opAt 2319 .ADD,
   opAt 2320 .MSTORE,
   pushAt 2321 1 1,
   pushAt 2322 2 1513,
   opAt 2323 .JUMP]

end Challenge.Modexp.Submission.Proofs.Fast
