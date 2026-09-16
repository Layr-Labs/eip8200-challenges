import Challenge.Modexp.Submission.Proofs.Fast.ShiftPaths
set_option warningAsError false
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000
/-! Loop-body blocks of the shift-reduce routine split before their exit tests, so
that each block reduction stays small enough for the kernel. -/

namespace Challenge.Modexp.Submission.Proofs.Fast

open EvmSemantics
open EvmSemantics.EVM
open Challenge.Modexp.Submission.Proofs.Bytecode

/-- The negation loop body up to its exit test (`blk2896` instructions 0..14). -/
def blk2896a :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1768 .JUMPDEST,
   opAt 1769 (.Dup ⟨0, by decide⟩),
   opAt 1770 .MLOAD,
   opAt 1771 .NOT,
   opAt 1772 (.Dup ⟨2, by decide⟩),
   opAt 1773 .ADD,
   opAt 1774 (.Dup ⟨0, by decide⟩),
   opAt 1775 (.Swap ⟨2, by decide⟩),
   opAt 1776 .GT,
   opAt 1777 (.Swap ⟨1, by decide⟩),
   opAt 1778 (.Dup ⟨1, by decide⟩),
   pushAt 1779 2 1280,
   opAt 1780 .ADD,
   opAt 1781 .MSTORE]

/-- The rotated exit test of the negation loop body: `p - 32` stays on the stack, the
jump back to the loop head is taken on the old pointer `p`, and `p = 0` falls into `NEG_DONE`. -/
def blk2896b :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1782 (.Dup ⟨0, by decide⟩),
   pushAt 1783 1 31,
   opAt 1784 .NOT,
   opAt 1785 .ADD,
   opAt 1786 (.Swap ⟨0, by decide⟩),
   pushAt 1787 2 2405,
   opAt 1788 .JUMPI]



/-- The add-round body up to its store (`blk3157` instructions 0..22). -/
def blk3157a :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2251 .JUMPDEST,
   opAt 2252 (.Dup ⟨0, by decide⟩),
   opAt 2253 .MLOAD,
   pushAt 2254 3 2112,
   opAt 2255 (.Dup ⟨2, by decide⟩),
   opAt 2256 .SUB,
   opAt 2257 .MLOAD,
   opAt 2258 (.Dup ⟨1, by decide⟩),
   opAt 2259 .ADD,
   opAt 2260 (.Swap ⟨0, by decide⟩),
   opAt 2261 (.Dup ⟨1, by decide⟩),
   opAt 2262 .LT,
   opAt 2263 (.Swap ⟨0, by decide⟩),
   opAt 2264 (.Dup ⟨3, by decide⟩),
   opAt 2265 .ADD,
   opAt 2266 (.Swap ⟨2, by decide⟩),
   opAt 2267 (.Dup ⟨3, by decide⟩),
   opAt 2268 .LT,
   opAt 2269 .OR,
   opAt 2270 (.Swap ⟨1, by decide⟩),
   opAt 2271 (.Dup ⟨1, by decide⟩),
   opAt 2272 .MSTORE]

/-- The exit test of the add-round body (`blk3157` instructions 23..30). -/
def blk3157b :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 2273 1 31,
   opAt 2274 .NOT,
   opAt 2275 .ADD,
   pushAt 2276 2 2111,
   opAt 2277 (.Dup ⟨1, by decide⟩),
   opAt 2278 .GT,
   pushAt 2279 2 3024,
   opAt 2280 .JUMPI]

/-- The five padding `JUMPDEST`s on the add-round fall-through (indices 2413 to 2417). -/
def blk3157c :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2281 .JUMPDEST,
   opAt 2282 .JUMPDEST,
   opAt 2283 .JUMPDEST,
   opAt 2284 .JUMPDEST,
   opAt 2285 .JUMPDEST]

/-- The subtract-round body up to its exit test (`blk3213` instructions 0..22). -/
def blk3213a :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2310 .JUMPDEST,
   opAt 2311 (.Dup ⟨0, by decide⟩),
   opAt 2312 .MLOAD,
   pushAt 2313 2 2112,
   opAt 2314 (.Dup ⟨2, by decide⟩),
   opAt 2315 .SUB,
   opAt 2316 .MLOAD,
   opAt 2317 (.Dup ⟨1, by decide⟩),
   opAt 2318 (.Dup ⟨1, by decide⟩),
   opAt 2319 .GT,
   opAt 2320 (.Swap ⟨1, by decide⟩),
   opAt 2321 .SUB,
   opAt 2322 (.Dup ⟨3, by decide⟩),
   opAt 2323 (.Dup ⟨1, by decide⟩),
   opAt 2324 .LT,
   opAt 2325 (.Swap ⟨0, by decide⟩),
   opAt 2326 (.Dup ⟨4, by decide⟩),
   opAt 2327 (.Swap ⟨0, by decide⟩),
   opAt 2328 .SUB,
   opAt 2329 (.Dup ⟨3, by decide⟩),
   opAt 2330 .MSTORE,
   opAt 2331 .OR]

/-- The exit test of the subtract-round body (`blk3213` instructions 23..31). -/
def blk3213b :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2332 (.Swap ⟨1, by decide⟩),
   opAt 2333 .POP,
   pushAt 2334 1 31,
   opAt 2335 .NOT,
   opAt 2336 .ADD,
   pushAt 2337 2 2111,
   opAt 2338 (.Dup ⟨1, by decide⟩),
   opAt 2339 .GT,
   pushAt 2340 2 3103,
   opAt 2341 .JUMPI]

end Challenge.Modexp.Submission.Proofs.Fast
