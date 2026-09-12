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

/-- Located block in the selected full-width-base helper. -/
def blkFullBaseGuard :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2228 .JUMPDEST,
   opAt 2229 (.Dup ⟨0, by decide⟩),
   opAt 2230 (.Dup ⟨3, by decide⟩),
   opAt 2231 .EQ,
   pushAt 2232 0 0,
   opAt 2233 .MLOAD,
   pushAt 2234 1 255,
   opAt 2235 .SHR,
   opAt 2236 .AND,
   opAt 2237 .ISZERO,
   pushAt 2238 2 2910,
   opAt 2239 .JUMPI]

/-- Located block in the selected full-width-base helper. -/
def blkFullBaseCopyAdd :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2240 (.Dup ⟨0, by decide⟩),
   pushAt 2241 1 96,
   pushAt 2242 2 1024,
   opAt 2243 .CALLDATACOPY,
   pushAt 2244 2 3138,
   pushAt 2245 2 2048,
   pushAt 2246 2 1024,
   pushAt 2247 2 6144,
   pushAt 2248 2 3912,
   opAt 2249 .JUMP]

/-- Located block in the selected full-width-base helper. -/
def blkFullBaseFallback :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2250 .JUMPDEST,
   opAt 2251 (.Dup ⟨2, by decide⟩),
   pushAt 2252 1 31,
   opAt 2253 .ADD,
   pushAt 2254 1 5,
   opAt 2255 .SHR,
   opAt 2256 (.Dup ⟨3, by decide⟩),
   opAt 2257 (.Dup ⟨1, by decide⟩),
   pushAt 2258 1 5,
   opAt 2259 .SHL,
   opAt 2260 .SUB,
   pushAt 2261 1 3,
   opAt 2262 .SHL,
   pushAt 2263 1 96,
   opAt 2264 .CALLDATALOAD,
   opAt 2265 (.Swap ⟨0, by decide⟩),
   opAt 2266 .SHR,
   opAt 2267 (.Dup ⟨2, by decide⟩),
   pushAt 2268 2 992,
   opAt 2269 .ADD,
   opAt 2270 .MSTORE,
   pushAt 2271 1 1,
   pushAt 2272 2 1383,
   opAt 2273 .JUMP]

end Challenge.Modexp.Submission.Proofs.Fast
