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

/-- pc 3601..3629, indices 2213..2224: size/top-bit guard. -/
def blkFullBaseGuard :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2213 .JUMPDEST,
   opAt 2214 (.Dup ⟨0, by decide⟩),
   opAt 2215 (.Dup ⟨3, by decide⟩),
   opAt 2216 .EQ,
   pushAt 2217 0 0,
   opAt 2218 .MLOAD,
   pushAt 2219 1 255,
   opAt 2220 .SHR,
   opAt 2221 .AND,
   opAt 2222 .ISZERO,
   pushAt 2223 2 3656,
   opAt 2224 .JUMPI]

/-- pc 3632..3638, indices 2225..2234: copy the base to ACC and call
the existing add-mod routine with ZERO as its second operand. -/
def blkFullBaseCopyAdd :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2225 (.Dup ⟨0, by decide⟩),
   pushAt 2226 1 96,
   pushAt 2227 2 1024,
   opAt 2228 .CALLDATACOPY,
   pushAt 2229 2 1755,
   pushAt 2230 2 2048,
   pushAt 2231 2 1024,
   pushAt 2232 2 6144,
   pushAt 2233 2 1939,
   opAt 2234 .JUMP]

/-- pc 3639..3655, indices 2235..2241: after add-mod, convert ACC to the
Montgomery BASE block and rejoin at pc 1755. -/
def blkFullBaseAfterAdd :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2235 .JUMPDEST,
   pushAt 2236 2 1755,
   pushAt 2237 2 2048,
   pushAt 2238 2 6144,
   pushAt 2239 2 1024,
   pushAt 2240 2 1939,
   opAt 2241 .JUMP]

/-- pc 3656..3689, indices 2242..2265: relocated original base-head
computation and the jump to the unchanged loop head. -/
def blkFullBaseFallback :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2242 .JUMPDEST,
   opAt 2243 (.Dup ⟨2, by decide⟩),
   pushAt 2244 1 31,
   opAt 2245 .ADD,
   pushAt 2246 1 5,
   opAt 2247 .SHR,
   opAt 2248 (.Dup ⟨3, by decide⟩),
   opAt 2249 (.Dup ⟨1, by decide⟩),
   pushAt 2250 1 5,
   opAt 2251 .SHL,
   opAt 2252 .SUB,
   pushAt 2253 1 3,
   opAt 2254 .SHL,
   pushAt 2255 1 96,
   opAt 2256 .CALLDATALOAD,
   opAt 2257 (.Swap ⟨0, by decide⟩),
   opAt 2258 .SHR,
   opAt 2259 (.Dup ⟨2, by decide⟩),
   pushAt 2260 2 992,
   opAt 2261 .ADD,
   opAt 2262 .MSTORE,
   pushAt 2263 1 1,
   pushAt 2264 2 1668,
   opAt 2265 .JUMP]

end Challenge.Modexp.Submission.Proofs.Fast
