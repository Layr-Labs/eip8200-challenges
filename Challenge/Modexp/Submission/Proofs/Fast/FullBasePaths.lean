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

/-- pc 3606..3620, indices 2361..2372: size/top-bit guard. -/
def blkFullBaseGuard :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2237 .JUMPDEST,
   opAt 2238 (.Dup ⟨0, by decide⟩),
   opAt 2239 (.Dup ⟨3, by decide⟩),
   opAt 2240 .EQ,
   pushAt 2241 0 0,
   opAt 2242 .MLOAD,
   pushAt 2243 1 255,
   opAt 2244 .SHR,
   opAt 2245 .AND,
   opAt 2246 .ISZERO,
   pushAt 2247 2 3656,
   opAt 2248 .JUMPI]

/-- pc 3621..3643, indices 2373..2382: copy the base to ACC and call
the existing add-mod routine with ZERO as its second operand. -/
def blkFullBaseCopyAdd :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2249 (.Dup ⟨0, by decide⟩),
   pushAt 2250 1 96,
   pushAt 2251 2 1024,
   opAt 2252 .CALLDATACOPY,
   pushAt 2253 2 1755,
   pushAt 2254 2 2048,
   pushAt 2255 2 1024,
   pushAt 2256 2 6144,
   pushAt 2257 2 1939,
   opAt 2258 .JUMP]

/-- pc 3644..3660, indices 2383..2389: after add-mod, convert ACC to the
Montgomery BASE block and rejoin at pc 1755. -/
def blkFullBaseAfterAdd :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2259 .JUMPDEST,
   pushAt 2260 2 1755,
   pushAt 2261 2 2048,
   pushAt 2262 2 6144,
   pushAt 2263 2 1024,
   pushAt 2264 2 1939,
   opAt 2265 .JUMP]

/-- pc 3661..3694, indices 2390..2413: relocated original base-head
computation and the jump to the unchanged loop head. -/
def blkFullBaseFallback :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2266 .JUMPDEST,
   opAt 2267 (.Dup ⟨2, by decide⟩),
   pushAt 2268 1 31,
   opAt 2269 .ADD,
   pushAt 2270 1 5,
   opAt 2271 .SHR,
   opAt 2272 (.Dup ⟨3, by decide⟩),
   opAt 2273 (.Dup ⟨1, by decide⟩),
   pushAt 2274 1 5,
   opAt 2275 .SHL,
   opAt 2276 .SUB,
   pushAt 2277 1 3,
   opAt 2278 .SHL,
   pushAt 2279 1 96,
   opAt 2280 .CALLDATALOAD,
   opAt 2281 (.Swap ⟨0, by decide⟩),
   opAt 2282 .SHR,
   opAt 2283 (.Dup ⟨2, by decide⟩),
   pushAt 2284 2 992,
   opAt 2285 .ADD,
   opAt 2286 .MSTORE,
   pushAt 2287 1 1,
   pushAt 2288 2 1668,
   opAt 2289 .JUMP]

end Challenge.Modexp.Submission.Proofs.Fast
