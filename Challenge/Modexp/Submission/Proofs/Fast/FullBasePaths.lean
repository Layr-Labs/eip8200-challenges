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
  [opAt 2195 .JUMPDEST,
   opAt 2196 (.Dup ⟨0, by decide⟩),
   opAt 2197 (.Dup ⟨3, by decide⟩),
   opAt 2198 .EQ,
   pushAt 2199 0 0,
   opAt 2200 .MLOAD,
   pushAt 2201 1 255,
   opAt 2202 .SHR,
   opAt 2203 .AND,
   opAt 2204 .ISZERO,
   pushAt 2205 2 3656,
   opAt 2206 .JUMPI]

/-- pc 3621..3643, indices 2373..2382: copy the base to ACC and call
the existing add-mod routine with ZERO as its second operand. -/
def blkFullBaseCopyAdd :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2207 (.Dup ⟨0, by decide⟩),
   pushAt 2208 1 96,
   pushAt 2209 2 1024,
   opAt 2210 .CALLDATACOPY,
   pushAt 2211 2 1755,
   pushAt 2212 2 2048,
   pushAt 2213 2 1024,
   pushAt 2214 2 6144,
   pushAt 2215 2 4785,
   opAt 2216 .JUMP]

/-- pc 3644..3660, indices 2383..2389: after add-mod, convert ACC to the
Montgomery BASE block and rejoin at pc 1755. -/
def blkFullBaseAfterAdd :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2217 .JUMPDEST,
   pushAt 2218 2 1755,
   pushAt 2219 2 2048,
   pushAt 2220 2 6144,
   pushAt 2221 2 1024,
   pushAt 2222 2 4785,
   opAt 2223 .JUMP]

/-- pc 3661..3694, indices 2390..2413: relocated original base-head
computation and the jump to the unchanged loop head. -/
def blkFullBaseFallback :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2224 .JUMPDEST,
   opAt 2225 (.Dup ⟨2, by decide⟩),
   pushAt 2226 1 31,
   opAt 2227 .ADD,
   pushAt 2228 1 5,
   opAt 2229 .SHR,
   opAt 2230 (.Dup ⟨3, by decide⟩),
   opAt 2231 (.Dup ⟨1, by decide⟩),
   pushAt 2232 1 5,
   opAt 2233 .SHL,
   opAt 2234 .SUB,
   pushAt 2235 1 3,
   opAt 2236 .SHL,
   pushAt 2237 1 96,
   opAt 2238 .CALLDATALOAD,
   opAt 2239 (.Swap ⟨0, by decide⟩),
   opAt 2240 .SHR,
   opAt 2241 (.Dup ⟨2, by decide⟩),
   pushAt 2242 2 992,
   opAt 2243 .ADD,
   opAt 2244 .MSTORE,
   pushAt 2245 1 1,
   pushAt 2246 2 1668,
   opAt 2247 .JUMP]

end Challenge.Modexp.Submission.Proofs.Fast
