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

/-- pc 3606..3620, indices 2289..2300: size/top-bit guard. -/
def blkFullBaseGuard :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2289 .JUMPDEST,
   opAt 2290 (.Dup ⟨0, by decide⟩),
   opAt 2291 (.Dup ⟨3, by decide⟩),
   opAt 2292 .EQ,
   pushAt 2293 0 0,
   opAt 2294 .MLOAD,
   pushAt 2295 1 255,
   opAt 2296 .SHR,
   opAt 2297 .AND,
   opAt 2298 .ISZERO,
   pushAt 2299 2 3661,
   opAt 2300 .JUMPI]

/-- pc 3621..3643, indices 2301..2310: copy the base to ACC and call
the existing add-mod routine with ZERO as its second operand. -/
def blkFullBaseCopyAdd :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2301 (.Dup ⟨0, by decide⟩),
   pushAt 2302 1 96,
   pushAt 2303 2 1024,
   opAt 2304 .CALLDATACOPY,
   pushAt 2305 2 1755,
   pushAt 2306 2 2048,
   pushAt 2307 2 1024,
   pushAt 2308 2 6144,
   pushAt 2309 2 1939,
   opAt 2310 .JUMP]

/-- pc 3644..3660, indices 2311..2317: after add-mod, convert ACC to the
Montgomery BASE block and rejoin at pc 1755. -/
def blkFullBaseAfterAdd :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2311 .JUMPDEST,
   pushAt 2312 2 1755,
   pushAt 2313 2 2048,
   pushAt 2314 2 6144,
   pushAt 2315 2 1024,
   pushAt 2316 2 1939,
   opAt 2317 .JUMP]

/-- pc 3661..3694, indices 2318..2341: relocated original base-head
computation and the jump to the unchanged loop head. -/
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
   pushAt 2336 2 992,
   opAt 2337 .ADD,
   opAt 2338 .MSTORE,
   pushAt 2339 1 1,
   pushAt 2340 2 1668,
   opAt 2341 .JUMP]

end Challenge.Modexp.Submission.Proofs.Fast
