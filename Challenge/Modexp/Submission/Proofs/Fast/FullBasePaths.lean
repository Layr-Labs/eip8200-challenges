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
  [opAt 2210 .JUMPDEST,
   opAt 2211 (.Dup ⟨0, by decide⟩),
   opAt 2212 (.Dup ⟨3, by decide⟩),
   opAt 2213 .EQ,
   pushAt 2214 0 0,
   opAt 2215 .MLOAD,
   pushAt 2216 1 255,
   opAt 2217 .SHR,
   opAt 2218 .AND,
   opAt 2219 .ISZERO,
   pushAt 2220 2 3575,
   opAt 2221 .JUMPI]

/-- pc 3621..3643, indices 2373..2382: copy the base to ACC and call
the existing add-mod routine with ZERO as its second operand. -/
def blkFullBaseCopyAdd :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2222 (.Dup ⟨0, by decide⟩),
   pushAt 2223 1 96,
   pushAt 2224 2 1024,
   opAt 2225 .CALLDATACOPY,
   pushAt 2226 2 1755,
   pushAt 2227 2 2048,
   pushAt 2228 2 1024,
   pushAt 2229 2 6144,
   pushAt 2230 2 1939,
   opAt 2231 .JUMP]

/-- pc 3644..3660, indices 2383..2389: after add-mod, convert ACC to the
Montgomery BASE block and rejoin at pc 1755. -/
def blkFullBaseAfterAdd :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2232 .JUMPDEST,
   pushAt 2233 2 1755,
   pushAt 2234 2 2048,
   pushAt 2235 2 6144,
   pushAt 2236 2 1024,
   pushAt 2237 2 1939,
   opAt 2238 .JUMP]

/-- pc 3661..3694, indices 2390..2413: relocated original base-head
computation and the jump to the unchanged loop head. -/
def blkFullBaseFallback :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2239 .JUMPDEST,
   opAt 2240 (.Dup ⟨2, by decide⟩),
   pushAt 2241 1 31,
   opAt 2242 .ADD,
   pushAt 2243 1 5,
   opAt 2244 .SHR,
   opAt 2245 (.Dup ⟨3, by decide⟩),
   opAt 2246 (.Dup ⟨1, by decide⟩),
   pushAt 2247 1 5,
   opAt 2248 .SHL,
   opAt 2249 .SUB,
   pushAt 2250 1 3,
   opAt 2251 .SHL,
   pushAt 2252 1 96,
   opAt 2253 .CALLDATALOAD,
   opAt 2254 (.Swap ⟨0, by decide⟩),
   opAt 2255 .SHR,
   opAt 2256 (.Dup ⟨2, by decide⟩),
   pushAt 2257 2 992,
   opAt 2258 .ADD,
   opAt 2259 .MSTORE,
   pushAt 2260 1 1,
   pushAt 2261 2 1668,
   opAt 2262 .JUMP]

end Challenge.Modexp.Submission.Proofs.Fast
