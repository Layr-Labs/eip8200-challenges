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
  [opAt 1770 .JUMPDEST,
   opAt 1771 (.Dup ⟨0, by decide⟩),
   opAt 1772 .MLOAD,
   opAt 1773 .NOT,
   opAt 1774 (.Dup ⟨2, by decide⟩),
   opAt 1775 .ADD,
   opAt 1776 (.Dup ⟨0, by decide⟩),
   opAt 1777 (.Swap ⟨2, by decide⟩),
   opAt 1778 .GT,
   opAt 1779 (.Swap ⟨1, by decide⟩),
   opAt 1780 (.Dup ⟨1, by decide⟩),
   pushAt 1781 2 1280,
   opAt 1782 .ADD,
   opAt 1783 .MSTORE]

/-- The rotated exit test of the negation loop body: `p - 32` stays on the stack, the
jump back to the loop head is taken on the old pointer `p`, and `p = 0` falls into `NEG_DONE`. -/
def blk2896b :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1784 (.Dup ⟨0, by decide⟩),
   pushAt 1785 1 31,
   opAt 1786 .NOT,
   opAt 1787 .ADD,
   opAt 1788 (.Swap ⟨0, by decide⟩),
   pushAt 1789 2 2405,
   opAt 1790 .JUMPI]



/-- The add-round body up to its store (`blk3157` instructions 0..22). -/
def blk3157a :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2255 .JUMPDEST,
   opAt 2256 (.Dup ⟨0, by decide⟩),
   opAt 2257 .MLOAD,
   pushAt 2258 3 2112,
   opAt 2259 (.Dup ⟨2, by decide⟩),
   opAt 2260 .SUB,
   opAt 2261 .MLOAD,
   opAt 2262 (.Dup ⟨1, by decide⟩),
   opAt 2263 .ADD,
   opAt 2264 (.Swap ⟨0, by decide⟩),
   opAt 2265 (.Dup ⟨1, by decide⟩),
   opAt 2266 .LT,
   opAt 2267 (.Swap ⟨0, by decide⟩),
   opAt 2268 (.Dup ⟨3, by decide⟩),
   opAt 2269 .ADD,
   opAt 2270 (.Swap ⟨2, by decide⟩),
   opAt 2271 (.Dup ⟨3, by decide⟩),
   opAt 2272 .LT,
   opAt 2273 .OR,
   opAt 2274 (.Swap ⟨1, by decide⟩),
   opAt 2275 (.Dup ⟨1, by decide⟩),
   opAt 2276 .MSTORE]

/-- The exit test of the add-round body (`blk3157` instructions 23..30). -/
def blk3157b :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 2277 1 31,
   opAt 2278 .NOT,
   opAt 2279 .ADD,
   pushAt 2280 2 2111,
   opAt 2281 (.Dup ⟨1, by decide⟩),
   opAt 2282 .GT,
   pushAt 2283 2 3024,
   opAt 2284 .JUMPI]

/-- The five padding `JUMPDEST`s on the add-round fall-through (indices 2413 to 2417). -/
def blk3157c :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2285 .JUMPDEST,
   opAt 2286 .JUMPDEST,
   opAt 2287 .JUMPDEST,
   opAt 2288 .JUMPDEST,
   opAt 2289 .JUMPDEST]

/-- The subtract-round body up to its exit test (`blk3213` instructions 0..22). -/
def blk3213a :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2314 .JUMPDEST,
   opAt 2315 (.Dup ⟨0, by decide⟩),
   opAt 2316 .MLOAD,
   pushAt 2317 2 2112,
   opAt 2318 (.Dup ⟨2, by decide⟩),
   opAt 2319 .SUB,
   opAt 2320 .MLOAD,
   opAt 2321 (.Dup ⟨1, by decide⟩),
   opAt 2322 (.Dup ⟨1, by decide⟩),
   opAt 2323 .GT,
   opAt 2324 (.Swap ⟨1, by decide⟩),
   opAt 2325 .SUB,
   opAt 2326 (.Dup ⟨3, by decide⟩),
   opAt 2327 (.Dup ⟨1, by decide⟩),
   opAt 2328 .LT,
   opAt 2329 (.Swap ⟨0, by decide⟩),
   opAt 2330 (.Dup ⟨4, by decide⟩),
   opAt 2331 (.Swap ⟨0, by decide⟩),
   opAt 2332 .SUB,
   opAt 2333 (.Dup ⟨3, by decide⟩),
   opAt 2334 .MSTORE,
   opAt 2335 .OR]

/-- The exit test of the subtract-round body (`blk3213` instructions 23..31). -/
def blk3213b :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2336 (.Swap ⟨1, by decide⟩),
   opAt 2337 .POP,
   pushAt 2338 1 31,
   opAt 2339 .NOT,
   opAt 2340 .ADD,
   pushAt 2341 2 2111,
   opAt 2342 (.Dup ⟨1, by decide⟩),
   opAt 2343 .GT,
   pushAt 2344 2 3103,
   opAt 2345 .JUMPI]

end Challenge.Modexp.Submission.Proofs.Fast
