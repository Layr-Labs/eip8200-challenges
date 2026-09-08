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
  [opAt 2229 .JUMPDEST,
   opAt 2230 (.Dup ⟨0, by decide⟩),
   opAt 2231 (.Dup ⟨3, by decide⟩),
   opAt 2232 .EQ,
   pushAt 2233 0 0,
   opAt 2234 .MLOAD,
   pushAt 2235 1 255,
   opAt 2236 .SHR,
   opAt 2237 .AND,
   opAt 2238 .ISZERO,
   pushAt 2239 2 3656,
   opAt 2240 .JUMPI]

/-- pc 3621..3643, indices 2373..2382: copy the base to ACC and call
the existing add-mod routine with ZERO as its second operand. -/
def blkFullBaseCopyAdd :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2241 (.Dup ⟨0, by decide⟩),
   pushAt 2242 1 96,
   pushAt 2243 2 1024,
   opAt 2244 .CALLDATACOPY,
   pushAt 2245 2 1755,
   pushAt 2246 2 2048,
   pushAt 2247 2 1024,
   pushAt 2248 2 6144,
   pushAt 2249 2 1939,
   opAt 2250 .JUMP]

/-- pc 3644..3660, indices 2383..2389: after add-mod, convert ACC to the
Montgomery BASE block and rejoin at pc 1755. -/
def blkFullBaseAfterAdd :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2251 .JUMPDEST,
   pushAt 2252 2 1755,
   pushAt 2253 2 2048,
   pushAt 2254 2 6144,
   pushAt 2255 2 1024,
   pushAt 2256 2 1939,
   opAt 2257 .JUMP]

/-- pc 3661..3694, indices 2390..2413: relocated original base-head
computation and the jump to the unchanged loop head. -/
def blkFullBaseFallback :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2258 .JUMPDEST,
   opAt 2259 (.Dup ⟨2, by decide⟩),
   pushAt 2260 1 31,
   opAt 2261 .ADD,
   pushAt 2262 1 5,
   opAt 2263 .SHR,
   opAt 2264 (.Dup ⟨3, by decide⟩),
   opAt 2265 (.Dup ⟨1, by decide⟩),
   pushAt 2266 1 5,
   opAt 2267 .SHL,
   opAt 2268 .SUB,
   pushAt 2269 1 3,
   opAt 2270 .SHL,
   pushAt 2271 1 96,
   opAt 2272 .CALLDATALOAD,
   opAt 2273 (.Swap ⟨0, by decide⟩),
   opAt 2274 .SHR,
   opAt 2275 (.Dup ⟨2, by decide⟩),
   pushAt 2276 2 992,
   opAt 2277 .ADD,
   opAt 2278 .MSTORE,
   pushAt 2279 1 1,
   pushAt 2280 2 1668,
   opAt 2281 .JUMP]

end Challenge.Modexp.Submission.Proofs.Fast
