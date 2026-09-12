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
  [opAt 2296 .JUMPDEST,
   opAt 2297 (.Dup ⟨0, by decide⟩),
   opAt 2298 (.Dup ⟨3, by decide⟩),
   opAt 2299 .EQ,
   pushAt 2300 0 0,
   opAt 2301 .MLOAD,
   pushAt 2302 1 255,
   opAt 2303 .SHR,
   opAt 2304 .AND,
   opAt 2305 .ISZERO,
   pushAt 2306 2 3033,
   opAt 2307 .JUMPI]

/-- Located block in the selected full-width-base helper. -/
def blkFullBaseCopyAdd :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2308 (.Dup ⟨0, by decide⟩),
   pushAt 2309 1 96,
   pushAt 2310 2 256,
   opAt 2311 .CALLDATACOPY,
   pushAt 2312 2 1599,
   pushAt 2313 2 512,
   pushAt 2314 2 256,
   pushAt 2315 2 1536,
   pushAt 2316 2 4137,
   opAt 2317 .JUMP]

/-- Located block in the selected full-width-base helper. -/
def blkFullBaseFallback :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2318 .JUMPDEST,
   opAt 2319 (.Dup ⟨2, by decide⟩),
   pushAt 2320 1 31,
   opAt 2321 .ADD,
   pushAt 2322 1 5,
   opAt 2323 .SHR,
   opAt 2324 (.Dup ⟨3, by decide⟩),
   opAt 2325 (.Dup ⟨1, by decide⟩),
   pushAt 2326 1 5,
   opAt 2327 .SHL,
   opAt 2328 .SUB,
   pushAt 2329 1 3,
   opAt 2330 .SHL,
   pushAt 2331 1 96,
   opAt 2332 .CALLDATALOAD,
   opAt 2333 (.Swap ⟨0, by decide⟩),
   opAt 2334 .SHR,
   opAt 2335 (.Dup ⟨2, by decide⟩),
   pushAt 2336 2 224,
   opAt 2337 .ADD,
   opAt 2338 .MSTORE,
   pushAt 2339 1 1,
   pushAt 2340 2 1513,
   opAt 2341 .JUMP]

end Challenge.Modexp.Submission.Proofs.Fast
