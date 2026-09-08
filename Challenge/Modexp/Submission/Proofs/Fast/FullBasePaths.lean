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
  [opAt 2194 .JUMPDEST,
   opAt 2195 (.Dup ⟨0, by decide⟩),
   opAt 2196 (.Dup ⟨3, by decide⟩),
   opAt 2197 .EQ,
   pushAt 2198 0 0,
   opAt 2199 .MLOAD,
   pushAt 2200 1 255,
   opAt 2201 .SHR,
   opAt 2202 .AND,
   opAt 2203 .ISZERO,
   pushAt 2204 2 3656,
   opAt 2205 .JUMPI]

/-- pc 3621..3643, indices 2373..2382: copy the base to ACC and call
the existing add-mod routine with ZERO as its second operand. -/
def blkFullBaseCopyAdd :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2206 (.Dup ⟨0, by decide⟩),
   pushAt 2207 1 96,
   pushAt 2208 2 1024,
   opAt 2209 .CALLDATACOPY,
   pushAt 2210 2 1755,
   pushAt 2211 2 2048,
   pushAt 2212 2 1024,
   pushAt 2213 2 6144,
   pushAt 2214 2 1939,
   opAt 2215 .JUMP]

/-- pc 3644..3660, indices 2383..2389: after add-mod, convert ACC to the
Montgomery BASE block and rejoin at pc 1755. -/
def blkFullBaseAfterAdd :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2216 .JUMPDEST,
   pushAt 2217 2 1755,
   pushAt 2218 2 2048,
   pushAt 2219 2 6144,
   pushAt 2220 2 1024,
   pushAt 2221 2 1939,
   opAt 2222 .JUMP]

/-- pc 3661..3694, indices 2390..2413: relocated original base-head
computation and the jump to the unchanged loop head. -/
def blkFullBaseFallback :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2223 .JUMPDEST,
   opAt 2224 (.Dup ⟨2, by decide⟩),
   pushAt 2225 1 31,
   opAt 2226 .ADD,
   pushAt 2227 1 5,
   opAt 2228 .SHR,
   opAt 2229 (.Dup ⟨3, by decide⟩),
   opAt 2230 (.Dup ⟨1, by decide⟩),
   pushAt 2231 1 5,
   opAt 2232 .SHL,
   opAt 2233 .SUB,
   pushAt 2234 1 3,
   opAt 2235 .SHL,
   pushAt 2236 1 96,
   opAt 2237 .CALLDATALOAD,
   opAt 2238 (.Swap ⟨0, by decide⟩),
   opAt 2239 .SHR,
   opAt 2240 (.Dup ⟨2, by decide⟩),
   pushAt 2241 2 992,
   opAt 2242 .ADD,
   opAt 2243 .MSTORE,
   pushAt 2244 1 1,
   pushAt 2245 2 1668,
   opAt 2246 .JUMP]

end Challenge.Modexp.Submission.Proofs.Fast
