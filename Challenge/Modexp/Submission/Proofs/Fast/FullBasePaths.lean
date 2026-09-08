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
   pushAt 2213 2 3143,
   opAt 2214 .JUMPI]

/-- pc 3621..3151, indices 2373..2169: copy the base to ACC and call
the existing add-mod routine with ZERO as its second operand. -/
def blkFullBaseCopyAdd :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2215 (.Dup ⟨0, by decide⟩),
   pushAt 2216 1 96,
   pushAt 2217 2 1024,
   opAt 2218 .CALLDATACOPY,
   pushAt 2219 2 1747,
   pushAt 2220 2 2048,
   pushAt 2221 2 1024,
   pushAt 2222 2 6144,
   pushAt 2223 2 4176,
   opAt 2224 .JUMP]

/-- pc 3644..3168, indices 2170..2176: after add-mod, convert ACC to the
Montgomery BASE block and rejoin at pc 1755. -/
def blkFullBaseAfterAdd :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [
   pushAt 2225 2 1747,
   pushAt 2226 2 2048,
   pushAt 2227 2 6144,
   pushAt 2228 2 1024,
   pushAt 2229 2 4176,
   opAt 2230 .JUMP]

/-- pc 3169..3202, indices 2177..2200: relocated original base-head
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
   pushAt 2253 2 1661,
   opAt 2254 .JUMP]

end Challenge.Modexp.Submission.Proofs.Fast
