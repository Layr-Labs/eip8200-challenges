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
  [opAt 2257 .JUMPDEST,
   opAt 2258 (.Dup ⟨0, by decide⟩),
   opAt 2259 .MLOAD,
   pushAt 2260 3 2112,
   opAt 2261 (.Dup ⟨2, by decide⟩),
   opAt 2262 .SUB,
   opAt 2263 .MLOAD,
   opAt 2264 (.Dup ⟨1, by decide⟩),
   opAt 2265 .ADD,
   opAt 2266 (.Swap ⟨0, by decide⟩),
   opAt 2267 (.Dup ⟨1, by decide⟩),
   opAt 2268 .LT,
   opAt 2269 (.Swap ⟨0, by decide⟩),
   opAt 2270 (.Dup ⟨3, by decide⟩),
   opAt 2271 .ADD,
   opAt 2272 (.Swap ⟨2, by decide⟩),
   opAt 2273 (.Dup ⟨3, by decide⟩),
   opAt 2274 .LT,
   opAt 2275 .OR,
   opAt 2276 (.Swap ⟨1, by decide⟩),
   opAt 2277 (.Dup ⟨1, by decide⟩),
   opAt 2278 .MSTORE]

/-- The exit test of the add-round body (`blk3157` instructions 23..30). -/
def blk3157b :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 2279 1 31,
   opAt 2280 .NOT,
   opAt 2281 .ADD,
   pushAt 2282 2 2111,
   opAt 2283 (.Dup ⟨1, by decide⟩),
   opAt 2284 .GT,
   pushAt 2285 2 3024,
   opAt 2286 .JUMPI]

/-- The five padding `JUMPDEST`s on the add-round fall-through (indices 2413 to 2417). -/
def blk3157c :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2287 .JUMPDEST,
   opAt 2288 .JUMPDEST,
   opAt 2289 .JUMPDEST,
   opAt 2290 .JUMPDEST,
   opAt 2291 .JUMPDEST]

/-- The subtract-round body up to its exit test (`blk3213` instructions 0..22). -/
def blk3213a :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2316 .JUMPDEST,
   opAt 2317 (.Dup ⟨0, by decide⟩),
   opAt 2318 .MLOAD,
   pushAt 2319 2 2112,
   opAt 2320 (.Dup ⟨2, by decide⟩),
   opAt 2321 .SUB,
   opAt 2322 .MLOAD,
   opAt 2323 (.Dup ⟨1, by decide⟩),
   opAt 2324 (.Dup ⟨1, by decide⟩),
   opAt 2325 .GT,
   opAt 2326 (.Swap ⟨1, by decide⟩),
   opAt 2327 .SUB,
   opAt 2328 (.Dup ⟨3, by decide⟩),
   opAt 2329 (.Dup ⟨1, by decide⟩),
   opAt 2330 .LT,
   opAt 2331 (.Swap ⟨0, by decide⟩),
   opAt 2332 (.Dup ⟨4, by decide⟩),
   opAt 2333 (.Swap ⟨0, by decide⟩),
   opAt 2334 .SUB,
   opAt 2335 (.Dup ⟨3, by decide⟩),
   opAt 2336 .MSTORE,
   opAt 2337 .OR]

/-- The exit test of the subtract-round body (`blk3213` instructions 23..31). -/
def blk3213b :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2338 (.Swap ⟨1, by decide⟩),
   opAt 2339 .POP,
   pushAt 2340 1 31,
   opAt 2341 .NOT,
   opAt 2342 .ADD,
   pushAt 2343 2 2111,
   opAt 2344 (.Dup ⟨1, by decide⟩),
   opAt 2345 .GT,
   pushAt 2346 2 3103,
   opAt 2347 .JUMPI]

end Challenge.Modexp.Submission.Proofs.Fast
