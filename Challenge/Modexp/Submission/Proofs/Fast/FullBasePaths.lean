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
   pushAt 2236 2 2906,
   opAt 2237 .JUMPI]

/-- Located block in the selected full-width-base helper. -/
def blkFullBaseCopyAdd :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2238 (.Dup ⟨0, by decide⟩),
   pushAt 2239 1 96,
   pushAt 2240 2 1024,
   opAt 2241 .CALLDATACOPY,
   pushAt 2242 2 1469,
   pushAt 2243 2 2048,
   pushAt 2244 2 1024,
   pushAt 2245 2 6144,
   pushAt 2246 2 3873,
   opAt 2247 .JUMP]

/-- Located block in the selected full-width-base helper. -/
def blkFullBaseFallback :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2248 .JUMPDEST,
   opAt 2249 (.Dup ⟨2, by decide⟩),
   pushAt 2250 1 31,
   opAt 2251 .ADD,
   pushAt 2252 1 5,
   opAt 2253 .SHR,
   opAt 2254 (.Dup ⟨3, by decide⟩),
   opAt 2255 (.Dup ⟨1, by decide⟩),
   pushAt 2256 1 5,
   opAt 2257 .SHL,
   opAt 2258 .SUB,
   pushAt 2259 1 3,
   opAt 2260 .SHL,
   pushAt 2261 1 96,
   opAt 2262 .CALLDATALOAD,
   opAt 2263 (.Swap ⟨0, by decide⟩),
   opAt 2264 .SHR,
   opAt 2265 (.Dup ⟨2, by decide⟩),
   pushAt 2266 2 992,
   opAt 2267 .ADD,
   opAt 2268 .MSTORE,
   pushAt 2269 1 1,
   pushAt 2270 2 1383,
   opAt 2271 .JUMP]

end Challenge.Modexp.Submission.Proofs.Fast
