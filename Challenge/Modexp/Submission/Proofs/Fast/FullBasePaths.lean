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
  [opAt 2207 .JUMPDEST,
   opAt 2208 (.Dup ⟨0, by decide⟩),
   opAt 2209 (.Dup ⟨3, by decide⟩),
   opAt 2210 .EQ,
   pushAt 2211 0 0,
   opAt 2212 .MLOAD,
   pushAt 2213 1 255,
   opAt 2214 .SHR,
   opAt 2215 .AND,
   opAt 2216 .ISZERO,
   pushAt 2217 2 3164,
   opAt 2218 .JUMPI]

/-- pc 3621..3151, indices 2373..2169: copy the base to ACC and call
the existing add-mod routine with ZERO as its second operand. -/
def blkFullBaseCopyAdd :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2219 (.Dup ⟨0, by decide⟩),
   pushAt 2220 1 96,
   pushAt 2221 2 1024,
   opAt 2222 .CALLDATACOPY,
   pushAt 2223 2 1755,
   pushAt 2224 2 2048,
   pushAt 2225 2 1024,
   pushAt 2226 2 6144,
   pushAt 2227 2 4202,
   opAt 2228 .JUMP]

/-- pc 3644..3168, indices 2170..2176: after add-mod, convert ACC to the
Montgomery BASE block and rejoin at pc 1755. -/
def blkFullBaseAfterAdd :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2229 .JUMPDEST,
   pushAt 2230 2 1755,
   pushAt 2231 2 2048,
   pushAt 2232 2 6144,
   pushAt 2233 2 1024,
   pushAt 2234 2 4202,
   opAt 2235 .JUMP]

/-- pc 3169..3202, indices 2177..2200: relocated original base-head
computation and the jump to the unchanged loop head. -/
def blkFullBaseFallback :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2236 .JUMPDEST,
   opAt 2237 (.Dup ⟨2, by decide⟩),
   pushAt 2238 1 31,
   opAt 2239 .ADD,
   pushAt 2240 1 5,
   opAt 2241 .SHR,
   opAt 2242 (.Dup ⟨3, by decide⟩),
   opAt 2243 (.Dup ⟨1, by decide⟩),
   pushAt 2244 1 5,
   opAt 2245 .SHL,
   opAt 2246 .SUB,
   pushAt 2247 1 3,
   opAt 2248 .SHL,
   pushAt 2249 1 96,
   opAt 2250 .CALLDATALOAD,
   opAt 2251 (.Swap ⟨0, by decide⟩),
   opAt 2252 .SHR,
   opAt 2253 (.Dup ⟨2, by decide⟩),
   pushAt 2254 2 992,
   opAt 2255 .ADD,
   opAt 2256 .MSTORE,
   pushAt 2257 1 1,
   pushAt 2258 2 1668,
   opAt 2259 .JUMP]

end Challenge.Modexp.Submission.Proofs.Fast
