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
  [opAt 2281 .JUMPDEST,
   opAt 2282 (.Dup ⟨0, by decide⟩),
   opAt 2283 (.Dup ⟨3, by decide⟩),
   opAt 2284 .EQ,
   pushAt 2285 0 0,
   opAt 2286 .MLOAD,
   pushAt 2287 1 255,
   opAt 2288 .SHR,
   opAt 2289 .AND,
   opAt 2290 .ISZERO,
   pushAt 2291 2 3045,
   opAt 2292 .JUMPI]

/-- Located block in the selected full-width-base helper. -/
def blkFullBaseCopyAdd :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2293 (.Dup ⟨0, by decide⟩),
   pushAt 2294 1 96,
   pushAt 2295 2 256,
   opAt 2296 .CALLDATACOPY,
   pushAt 2297 2 1604,
   pushAt 2298 2 512,
   pushAt 2299 2 256,
   pushAt 2300 2 1536,
   pushAt 2301 2 4047,
   opAt 2302 .JUMP]

/-- Located block in the selected full-width-base helper. -/
def blkFullBaseFallback :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2303 .JUMPDEST,
   opAt 2304 (.Dup ⟨2, by decide⟩),
   pushAt 2305 1 31,
   opAt 2306 .ADD,
   pushAt 2307 1 5,
   opAt 2308 .SHR,
   opAt 2309 (.Dup ⟨3, by decide⟩),
   opAt 2310 (.Dup ⟨1, by decide⟩),
   pushAt 2311 1 5,
   opAt 2312 .SHL,
   opAt 2313 .SUB,
   pushAt 2314 1 3,
   opAt 2315 .SHL,
   pushAt 2316 1 96,
   opAt 2317 .CALLDATALOAD,
   opAt 2318 (.Swap ⟨0, by decide⟩),
   opAt 2319 .SHR,
   opAt 2320 (.Dup ⟨2, by decide⟩),
   pushAt 2321 2 224,
   opAt 2322 .ADD,
   opAt 2323 .MSTORE,
   pushAt 2324 1 1,
   pushAt 2325 2 1518,
   opAt 2326 .JUMP]

end Challenge.Modexp.Submission.Proofs.Fast
