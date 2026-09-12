import Challenge.Modexp.Submission.Proofs.Fast.Paths.P4
set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000
/-!
# Located paths for the full-width-base helper

The helper is appended after the fixed-window and direct-RR helpers. Its miss
path reproduces the original base-head computation before jumping to the
unchanged base loop at pc 1798.
-/

namespace Challenge.Modexp.Submission.Proofs.Fast

open EvmSemantics
open EvmSemantics.EVM
open Challenge.Modexp.Submission.Proofs.Bytecode

/-- Located block in the selected full-width-base helper. -/
def blkFullBaseGuard :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2285 .JUMPDEST,
   opAt 2286 (.Dup ⟨0, by decide⟩),
   opAt 2287 (.Dup ⟨3, by decide⟩),
   opAt 2288 .EQ,
   pushAt 2289 0 0,
   opAt 2290 .MLOAD,
   pushAt 2291 1 255,
   opAt 2292 .SHR,
   opAt 2293 .AND,
   opAt 2294 .ISZERO,
   pushAt 2295 2 3048,
   opAt 2296 .JUMPI]

/-- Located block in the selected full-width-base helper. -/
def blkFullBaseCopyAdd :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2297 (.Dup ⟨0, by decide⟩),
   pushAt 2298 1 96,
   pushAt 2299 2 256,
   opAt 2300 .CALLDATACOPY,
   pushAt 2301 2 3275,
   pushAt 2302 2 512,
   pushAt 2303 2 256,
   pushAt 2304 2 1536,
   pushAt 2305 2 4151,
   opAt 2306 .JUMP]

/-- Located block in the selected full-width-base helper. -/
def blkFullBaseFallback :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2307 .JUMPDEST,
   opAt 2308 (.Dup ⟨2, by decide⟩),
   pushAt 2309 1 31,
   opAt 2310 .ADD,
   pushAt 2311 1 5,
   opAt 2312 .SHR,
   opAt 2313 (.Dup ⟨3, by decide⟩),
   opAt 2314 (.Dup ⟨1, by decide⟩),
   pushAt 2315 1 5,
   opAt 2316 .SHL,
   opAt 2317 .SUB,
   pushAt 2318 1 3,
   opAt 2319 .SHL,
   pushAt 2320 1 96,
   opAt 2321 .CALLDATALOAD,
   opAt 2322 (.Swap ⟨0, by decide⟩),
   opAt 2323 .SHR,
   opAt 2324 (.Dup ⟨2, by decide⟩),
   pushAt 2325 1 224,
   opAt 2326 .ADD,
   opAt 2327 .MSTORE,
   pushAt 2328 1 1,
   pushAt 2329 2 1513,
   opAt 2330 .JUMP]

end Challenge.Modexp.Submission.Proofs.Fast
