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
  [opAt 2179 .JUMPDEST,
   opAt 2180 (.Dup ⟨0, by decide⟩),
   opAt 2181 (.Dup ⟨3, by decide⟩),
   opAt 2182 .EQ,
   pushAt 2183 0 0,
   opAt 2184 .MLOAD,
   pushAt 2185 1 255,
   opAt 2186 .SHR,
   opAt 2187 .AND,
   opAt 2188 .ISZERO,
   pushAt 2189 2 3623,
   opAt 2190 .JUMPI]

/-- pc 3621..3643, indices 2373..2382: copy the base to ACC and call
the existing add-mod routine with ZERO as its second operand. -/
def blkFullBaseCopyAdd :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2191 (.Dup ⟨0, by decide⟩),
   pushAt 2192 1 96,
   pushAt 2193 2 1024,
   opAt 2194 .CALLDATACOPY,
   pushAt 2195 2 1736,
   pushAt 2196 2 2048,
   pushAt 2197 2 1024,
   pushAt 2198 2 6144,
   pushAt 2199 2 4751,
   opAt 2200 .JUMP]

/-- pc 3644..3660, indices 2383..2389: after add-mod, convert ACC to the
Montgomery BASE block and rejoin at pc 1755. -/
def blkFullBaseAfterAdd :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2201 .JUMPDEST,
   pushAt 2202 2 1736,
   pushAt 2203 2 2048,
   pushAt 2204 2 6144,
   pushAt 2205 2 1024,
   pushAt 2206 2 4751,
   opAt 2207 .JUMP]

/-- pc 3661..3694, indices 2390..2413: relocated original base-head
computation and the jump to the unchanged loop head. -/
def blkFullBaseFallback :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2208 .JUMPDEST,
   opAt 2209 (.Dup ⟨2, by decide⟩),
   pushAt 2210 1 31,
   opAt 2211 .ADD,
   pushAt 2212 1 5,
   opAt 2213 .SHR,
   opAt 2214 (.Dup ⟨3, by decide⟩),
   opAt 2215 (.Dup ⟨1, by decide⟩),
   pushAt 2216 1 5,
   opAt 2217 .SHL,
   opAt 2218 .SUB,
   pushAt 2219 1 3,
   opAt 2220 .SHL,
   pushAt 2221 1 96,
   opAt 2222 .CALLDATALOAD,
   opAt 2223 (.Swap ⟨0, by decide⟩),
   opAt 2224 .SHR,
   opAt 2225 (.Dup ⟨2, by decide⟩),
   pushAt 2226 2 992,
   opAt 2227 .ADD,
   opAt 2228 .MSTORE,
   pushAt 2229 1 1,
   pushAt 2230 2 1650,
   opAt 2231 .JUMP]

end Challenge.Modexp.Submission.Proofs.Fast
