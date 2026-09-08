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
  [opAt 2202 .JUMPDEST,
   opAt 2203 (.Dup ⟨0, by decide⟩),
   opAt 2204 (.Dup ⟨3, by decide⟩),
   opAt 2205 .EQ,
   pushAt 2206 0 0,
   opAt 2207 .MLOAD,
   pushAt 2208 1 255,
   opAt 2209 .SHR,
   opAt 2210 .AND,
   opAt 2211 .ISZERO,
   pushAt 2212 2 3446,
   opAt 2213 .JUMPI]

/-- pc 3621..3643, indices 2373..2382: copy the base to ACC and call
the existing add-mod routine with ZERO as its second operand. -/
def blkFullBaseCopyAdd :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2214 (.Dup ⟨0, by decide⟩),
   pushAt 2215 1 96,
   pushAt 2216 2 1024,
   opAt 2217 .CALLDATACOPY,
   pushAt 2218 2 1755,
   pushAt 2219 2 2048,
   pushAt 2220 2 1024,
   pushAt 2221 2 6144,
   pushAt 2222 2 1939,
   opAt 2223 .JUMP]

/-- pc 3644..3660, indices 2383..2389: after add-mod, convert ACC to the
Montgomery BASE block and rejoin at pc 1755. -/
def blkFullBaseAfterAdd :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2224 .JUMPDEST,
   pushAt 2225 2 1755,
   pushAt 2226 2 2048,
   pushAt 2227 2 6144,
   pushAt 2228 2 1024,
   pushAt 2229 2 1939,
   opAt 2230 .JUMP]

/-- pc 3661..3694, indices 2390..2413: relocated original base-head
computation and the jump to the unchanged loop head. -/
def blkFullBaseFallback :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2231 .JUMPDEST,
   opAt 2232 (.Dup ⟨2, by decide⟩),
   pushAt 2233 1 31,
   opAt 2234 .ADD,
   pushAt 2235 1 5,
   opAt 2236 .SHR,
   opAt 2237 (.Dup ⟨3, by decide⟩),
   opAt 2238 (.Dup ⟨1, by decide⟩),
   pushAt 2239 1 5,
   opAt 2240 .SHL,
   opAt 2241 .SUB,
   pushAt 2242 1 3,
   opAt 2243 .SHL,
   pushAt 2244 1 96,
   opAt 2245 .CALLDATALOAD,
   opAt 2246 (.Swap ⟨0, by decide⟩),
   opAt 2247 .SHR,
   opAt 2248 (.Dup ⟨2, by decide⟩),
   pushAt 2249 2 992,
   opAt 2250 .ADD,
   opAt 2251 .MSTORE,
   pushAt 2252 1 1,
   pushAt 2253 2 1668,
   opAt 2254 .JUMP]

end Challenge.Modexp.Submission.Proofs.Fast
