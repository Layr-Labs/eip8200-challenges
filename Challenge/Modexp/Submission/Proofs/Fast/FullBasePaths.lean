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
  [opAt 2203 .JUMPDEST,
   opAt 2204 (.Dup ⟨0, by decide⟩),
   opAt 2205 (.Dup ⟨3, by decide⟩),
   opAt 2206 .EQ,
   pushAt 2207 0 0,
   opAt 2208 .MLOAD,
   pushAt 2209 1 255,
   opAt 2210 .SHR,
   opAt 2211 .AND,
   opAt 2212 .ISZERO,
   pushAt 2213 2 3656,
   opAt 2214 .JUMPI]

/-- pc 3621..3643, indices 2373..2382: copy the base to ACC and call
the existing add-mod routine with ZERO as its second operand. -/
def blkFullBaseCopyAdd :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2215 (.Dup ⟨0, by decide⟩),
   pushAt 2216 1 96,
   pushAt 2217 2 1024,
   opAt 2218 .CALLDATACOPY,
   pushAt 2219 2 1755,
   pushAt 2220 2 2048,
   pushAt 2221 2 1024,
   pushAt 2222 2 6144,
   pushAt 2223 2 1939,
   opAt 2224 .JUMP]

/-- pc 3644..3660, indices 2383..2389: after add-mod, convert ACC to the
Montgomery BASE block and rejoin at pc 1755. -/
def blkFullBaseAfterAdd :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2225 .JUMPDEST,
   pushAt 2226 2 1755,
   pushAt 2227 2 2048,
   pushAt 2228 2 6144,
   pushAt 2229 2 1024,
   pushAt 2230 2 1939,
   opAt 2231 .JUMP]

/-- pc 3661..3694, indices 2390..2413: relocated original base-head
computation and the jump to the unchanged loop head. -/
def blkFullBaseFallback :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2232 .JUMPDEST,
   opAt 2233 (.Dup ⟨2, by decide⟩),
   pushAt 2234 1 31,
   opAt 2235 .ADD,
   pushAt 2236 1 5,
   opAt 2237 .SHR,
   opAt 2238 (.Dup ⟨3, by decide⟩),
   opAt 2239 (.Dup ⟨1, by decide⟩),
   pushAt 2240 1 5,
   opAt 2241 .SHL,
   opAt 2242 .SUB,
   pushAt 2243 1 3,
   opAt 2244 .SHL,
   pushAt 2245 1 96,
   opAt 2246 .CALLDATALOAD,
   opAt 2247 (.Swap ⟨0, by decide⟩),
   opAt 2248 .SHR,
   opAt 2249 (.Dup ⟨2, by decide⟩),
   pushAt 2250 2 992,
   opAt 2251 .ADD,
   opAt 2252 .MSTORE,
   pushAt 2253 1 1,
   pushAt 2254 2 1668,
   opAt 2255 .JUMP]

end Challenge.Modexp.Submission.Proofs.Fast
