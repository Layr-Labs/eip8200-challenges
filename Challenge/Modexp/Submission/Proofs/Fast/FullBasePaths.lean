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
  [opAt 2224 .JUMPDEST,
   opAt 2225 (.Dup ⟨0, by decide⟩),
   opAt 2226 (.Dup ⟨3, by decide⟩),
   opAt 2227 .EQ,
   pushAt 2228 0 0,
   opAt 2229 .MLOAD,
   pushAt 2230 1 255,
   opAt 2231 .SHR,
   opAt 2232 .AND,
   opAt 2233 .ISZERO,
   pushAt 2234 2 2902,
   opAt 2235 .JUMPI]

/-- Located block in the selected full-width-base helper. -/
def blkFullBaseCopyAdd :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2236 (.Dup ⟨0, by decide⟩),
   pushAt 2237 1 96,
   pushAt 2238 2 1024,
   opAt 2239 .CALLDATACOPY,
   pushAt 2240 2 1465,
   pushAt 2241 2 2048,
   pushAt 2242 2 1024,
   pushAt 2243 2 6144,
   pushAt 2244 2 3900,
   opAt 2245 .JUMP]

/-- Located block in the selected full-width-base helper. -/
def blkFullBaseFallback :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2246 .JUMPDEST,
   opAt 2247 (.Dup ⟨2, by decide⟩),
   pushAt 2248 1 31,
   opAt 2249 .ADD,
   pushAt 2250 1 5,
   opAt 2251 .SHR,
   opAt 2252 (.Dup ⟨3, by decide⟩),
   opAt 2253 (.Dup ⟨1, by decide⟩),
   pushAt 2254 1 5,
   opAt 2255 .SHL,
   opAt 2256 .SUB,
   pushAt 2257 1 3,
   opAt 2258 .SHL,
   pushAt 2259 1 96,
   opAt 2260 .CALLDATALOAD,
   opAt 2261 (.Swap ⟨0, by decide⟩),
   opAt 2262 .SHR,
   opAt 2263 (.Dup ⟨2, by decide⟩),
   pushAt 2264 2 992,
   opAt 2265 .ADD,
   opAt 2266 .MSTORE,
   pushAt 2267 1 1,
   pushAt 2268 2 1379,
   opAt 2269 .JUMP]

end Challenge.Modexp.Submission.Proofs.Fast
