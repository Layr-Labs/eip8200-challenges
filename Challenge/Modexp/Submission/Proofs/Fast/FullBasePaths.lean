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

/-- pc 3114..3620, indices 2361..2372: size/top-bit guard. -/
def blkFullBaseGuard :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2223 .JUMPDEST,
   opAt 2224 (.Dup ⟨0, by decide⟩),
   opAt 2225 (.Dup ⟨3, by decide⟩),
   opAt 2226 .EQ,
   pushAt 2227 0 0,
   opAt 2228 .MLOAD,
   pushAt 2229 1 255,
   opAt 2230 .SHR,
   opAt 2231 .AND,
   opAt 2232 .ISZERO,
   pushAt 2233 2 3164,
   opAt 2234 .JUMPI]

/-- pc 3621..3151, indices 2373..2169: copy the base to ACC and call
the existing add-mod routine with ZERO as its second operand. -/
def blkFullBaseCopyAdd :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2235 (.Dup ⟨0, by decide⟩),
   pushAt 2236 1 96,
   pushAt 2237 2 1024,
   opAt 2238 .CALLDATACOPY,
   pushAt 2239 2 1755,
   pushAt 2240 2 2048,
   pushAt 2241 2 1024,
   pushAt 2242 2 6144,
   pushAt 2243 2 4202,
   opAt 2244 .JUMP]

/-- pc 3644..3168, indices 2170..2176: after add-mod, convert ACC to the
Montgomery BASE block and rejoin at pc 1755. -/
def blkFullBaseAfterAdd :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2245 .JUMPDEST,
   pushAt 2246 2 1755,
   pushAt 2247 2 2048,
   pushAt 2248 2 6144,
   pushAt 2249 2 1024,
   pushAt 2250 2 4202,
   opAt 2251 .JUMP]

/-- pc 3169..3202, indices 2177..2200: relocated original base-head
computation and the jump to the unchanged loop head. -/
def blkFullBaseFallback :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2252 .JUMPDEST,
   opAt 2253 (.Dup ⟨2, by decide⟩),
   pushAt 2254 1 31,
   opAt 2255 .ADD,
   pushAt 2256 1 5,
   opAt 2257 .SHR,
   opAt 2258 (.Dup ⟨3, by decide⟩),
   opAt 2259 (.Dup ⟨1, by decide⟩),
   pushAt 2260 1 5,
   opAt 2261 .SHL,
   opAt 2262 .SUB,
   pushAt 2263 1 3,
   opAt 2264 .SHL,
   pushAt 2265 1 96,
   opAt 2266 .CALLDATALOAD,
   opAt 2267 (.Swap ⟨0, by decide⟩),
   opAt 2268 .SHR,
   opAt 2269 (.Dup ⟨2, by decide⟩),
   pushAt 2270 2 992,
   opAt 2271 .ADD,
   opAt 2272 .MSTORE,
   pushAt 2273 1 1,
   pushAt 2274 2 1668,
   opAt 2275 .JUMP]

end Challenge.Modexp.Submission.Proofs.Fast
