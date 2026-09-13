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
  [opAt 2282 .JUMPDEST,
   opAt 2283 (.Dup ⟨0, by decide⟩),
   opAt 2284 (.Dup ⟨3, by decide⟩),
   opAt 2285 .EQ,
   pushAt 2286 0 0,
   opAt 2287 .MLOAD,
   pushAt 2288 1 255,
   opAt 2289 .SHR,
   opAt 2290 .AND,
   opAt 2291 .ISZERO,
   pushAt 2292 2 3045,
   opAt 2293 .JUMPI]

/-- Located block in the selected full-width-base helper. -/
def blkFullBaseCopyAdd :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2294 (.Dup ⟨0, by decide⟩),
   pushAt 2295 1 96,
   pushAt 2296 2 256,
   opAt 2297 .CALLDATACOPY,
   pushAt 2298 2 3216,
   pushAt 2299 2 512,
   pushAt 2300 2 256,
   pushAt 2301 2 1536,
   pushAt 2302 2 4092,
   opAt 2303 .JUMP]

/-- Located block in the selected full-width-base helper. -/
def blkFullBaseFallback :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2304 .JUMPDEST,
   opAt 2305 (.Dup ⟨2, by decide⟩),
   pushAt 2306 1 31,
   opAt 2307 .ADD,
   pushAt 2308 1 5,
   opAt 2309 .SHR,
   opAt 2310 (.Dup ⟨3, by decide⟩),
   opAt 2311 (.Dup ⟨1, by decide⟩),
   pushAt 2312 1 5,
   opAt 2313 .SHL,
   opAt 2314 .SUB,
   pushAt 2315 1 3,
   opAt 2316 .SHL,
   pushAt 2317 1 96,
   opAt 2318 .CALLDATALOAD,
   opAt 2319 (.Swap ⟨0, by decide⟩),
   opAt 2320 .SHR,
   opAt 2321 (.Dup ⟨2, by decide⟩),
   pushAt 2322 1 224,
   opAt 2323 .ADD,
   opAt 2324 .MSTORE,
   pushAt 2325 1 1,
   pushAt 2326 2 1513,
   opAt 2327 .JUMP]

end Challenge.Modexp.Submission.Proofs.Fast
