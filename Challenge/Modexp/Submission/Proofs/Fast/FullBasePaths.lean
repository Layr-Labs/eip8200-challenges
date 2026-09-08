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
  [opAt 2226 .JUMPDEST,
   opAt 2227 (.Dup ⟨0, by decide⟩),
   opAt 2228 (.Dup ⟨3, by decide⟩),
   opAt 2229 .EQ,
   pushAt 2230 0 0,
   opAt 2231 .MLOAD,
   pushAt 2232 1 255,
   opAt 2233 .SHR,
   opAt 2234 .AND,
   opAt 2235 .ISZERO,
   pushAt 2236 2 3510,
   opAt 2237 .JUMPI]

/-- pc 3621..3643, indices 2373..2382: copy the base to ACC and call
the existing add-mod routine with ZERO as its second operand. -/
def blkFullBaseCopyAdd :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2238 (.Dup ⟨0, by decide⟩),
   pushAt 2239 1 96,
   pushAt 2240 2 1024,
   opAt 2241 .CALLDATACOPY,
   pushAt 2242 2 1729,
   pushAt 2243 2 2048,
   pushAt 2244 2 1024,
   pushAt 2245 2 6144,
   pushAt 2246 2 1908,
   opAt 2247 .JUMP]

/-- pc 3644..3660, indices 2383..2389: after add-mod, convert ACC to the
Montgomery BASE block and rejoin at pc 1755. -/
def blkFullBaseAfterAdd :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2248 .JUMPDEST,
   pushAt 2249 2 1729,
   pushAt 2250 2 2048,
   pushAt 2251 2 6144,
   pushAt 2252 2 1024,
   pushAt 2253 2 1908,
   opAt 2254 .JUMP]

/-- pc 3661..3694, indices 2390..2413: relocated original base-head
computation and the jump to the unchanged loop head. -/
def blkFullBaseFallback :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2255 .JUMPDEST,
   opAt 2256 (.Dup ⟨2, by decide⟩),
   pushAt 2257 1 31,
   opAt 2258 .ADD,
   pushAt 2259 1 5,
   opAt 2260 .SHR,
   opAt 2261 (.Dup ⟨3, by decide⟩),
   opAt 2262 (.Dup ⟨1, by decide⟩),
   pushAt 2263 1 5,
   opAt 2264 .SHL,
   opAt 2265 .SUB,
   pushAt 2266 1 3,
   opAt 2267 .SHL,
   pushAt 2268 1 96,
   opAt 2269 .CALLDATALOAD,
   opAt 2270 (.Swap ⟨0, by decide⟩),
   opAt 2271 .SHR,
   opAt 2272 (.Dup ⟨2, by decide⟩),
   pushAt 2273 2 992,
   opAt 2274 .ADD,
   opAt 2275 .MSTORE,
   pushAt 2276 1 1,
   pushAt 2277 2 1643,
   opAt 2278 .JUMP]

end Challenge.Modexp.Submission.Proofs.Fast
