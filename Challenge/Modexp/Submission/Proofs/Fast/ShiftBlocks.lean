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
  [opAt 1979 .JUMPDEST,
   opAt 1980 (.Dup ⟨0, by decide⟩),
   opAt 1981 .MLOAD,
   opAt 1982 .NOT,
   opAt 1983 (.Dup ⟨2, by decide⟩),
   opAt 1984 .ADD,
   opAt 1985 (.Dup ⟨0, by decide⟩),
   opAt 1986 (.Swap ⟨2, by decide⟩),
   opAt 1987 .GT,
   opAt 1988 (.Swap ⟨1, by decide⟩),
   opAt 1989 (.Dup ⟨1, by decide⟩),
   pushAt 1990 2 1280,
   opAt 1991 .ADD,
   opAt 1992 .MSTORE]

/-- The rotated exit test of the negation loop body: `p - 32` stays on the stack, the
jump back to the loop head is taken on the old pointer `p`, and `p = 0` falls into `NEG_DONE`. -/
def blk2896b :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1993 (.Dup ⟨0, by decide⟩),
   pushAt 1994 1 31,
   opAt 1995 .NOT,
   opAt 1996 .ADD,
   opAt 1997 (.Swap ⟨0, by decide⟩),
   pushAt 1998 2 2666,
   opAt 1999 .JUMPI]

/-- The limb-pass body up to its exit test (`blk3077` instructions 0..42). -/
def blk3077a :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2191 .JUMPDEST,
   pushAt 2192 2 832,
   opAt 2193 (.Dup ⟨1, by decide⟩),
   opAt 2194 .SUB,
   opAt 2195 .MLOAD,
   opAt 2196 (.Dup ⟨2, by decide⟩),
   opAt 2197 (.Dup ⟨6, by decide⟩),
   opAt 2198 (.Dup ⟨2, by decide⟩),
   opAt 2199 .MUL,
   opAt 2200 (.Swap ⟨1, by decide⟩),
   opAt 2201 (.Dup ⟨7, by decide⟩),
   opAt 2202 .MULMOD,
   opAt 2203 (.Dup ⟨1, by decide⟩),
   opAt 2204 (.Dup ⟨1, by decide⟩),
   opAt 2205 .LT,
   opAt 2206 .SUB,
   opAt 2207 (.Dup ⟨5, by decide⟩),
   opAt 2208 (.Dup ⟨2, by decide⟩),
   opAt 2209 .ADD,
   opAt 2210 (.Dup ⟨0, by decide⟩),
   opAt 2211 (.Swap ⟨6, by decide⟩),
   opAt 2212 .GT,
   opAt 2213 .SUB,
   opAt 2214 .SUB,
   opAt 2215 (.Dup ⟨4, by decide⟩),
   opAt 2216 (.Dup ⟨2, by decide⟩),
   opAt 2217 .MLOAD,
   opAt 2218 .ADD,
   opAt 2219 (.Dup ⟨0, by decide⟩),
   opAt 2220 (.Swap ⟨5, by decide⟩),
   opAt 2221 .GT,
   opAt 2222 .ADD,
   opAt 2223 (.Swap ⟨3, by decide⟩),
   opAt 2224 (.Dup ⟨1, by decide⟩),
   opAt 2225 .MSTORE,
   opAt 2226 (.Dup ⟨2, by decide⟩),
   opAt 2227 .ADD]

/-- The exit test of the limb-pass body (`blk3077` instructions 43..47). -/
def blk3077b :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 2339 2 2080,
   opAt 2340 (.Dup ⟨1, by decide⟩),
   opAt 2341 .GT,
   pushAt 2342 2 2951,
   opAt 2343 .JUMPI]

/-- The add-round body up to its exit test (`blk3157` instructions 0..26). -/
def blk3157a :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2382 .JUMPDEST,
   opAt 2383 (.Dup ⟨0, by decide⟩),
   opAt 2384 .MLOAD,
   opAt 2385 (.Dup ⟨1, by decide⟩),
   pushAt 2386 2 2112,
   opAt 2387 (.Swap ⟨0, by decide⟩),
   opAt 2388 .SUB,
   opAt 2389 .MLOAD,
   opAt 2390 (.Dup ⟨1, by decide⟩),
   opAt 2391 .ADD,
   opAt 2392 (.Dup ⟨0, by decide⟩),
   opAt 2393 (.Dup ⟨2, by decide⟩),
   opAt 2394 .GT,
   opAt 2395 (.Swap ⟨1, by decide⟩),
   opAt 2396 .POP,
   opAt 2397 (.Dup ⟨3, by decide⟩),
   opAt 2398 .ADD,
   opAt 2399 (.Dup ⟨0, by decide⟩),
   opAt 2400 (.Dup ⟨4, by decide⟩),
   opAt 2401 .GT,
   opAt 2402 (.Swap ⟨3, by decide⟩),
   opAt 2403 .POP,
   opAt 2404 (.Dup ⟨2, by decide⟩),
   opAt 2405 .MSTORE,
   opAt 2406 (.Swap ⟨0, by decide⟩),
   opAt 2407 (.Swap ⟨1, by decide⟩),
   opAt 2408 .OR]

/-- The exit test of the add-round body (`blk3157` instructions 27..34). -/
def blk3157b :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2409 (.Swap ⟨0, by decide⟩),
   pushAt 2410 1 31,
   opAt 2411 .NOT,
   opAt 2412 .ADD,
   pushAt 2413 2 2111,
   opAt 2414 (.Dup ⟨1, by decide⟩),
   opAt 2415 .GT,
   pushAt 2416 2 3168,
   opAt 2417 .JUMPI]

/-- The subtract-round body up to its exit test (`blk3213` instructions 0..22). -/
def blk3213a :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2442 .JUMPDEST,
   opAt 2443 (.Dup ⟨0, by decide⟩),
   opAt 2444 .MLOAD,
   pushAt 2445 2 2112,
   opAt 2446 (.Dup ⟨2, by decide⟩),
   opAt 2447 .SUB,
   opAt 2448 .MLOAD,
   opAt 2449 (.Dup ⟨1, by decide⟩),
   opAt 2450 (.Dup ⟨1, by decide⟩),
   opAt 2451 .GT,
   opAt 2452 (.Swap ⟨1, by decide⟩),
   opAt 2453 .SUB,
   opAt 2454 (.Dup ⟨3, by decide⟩),
   opAt 2455 (.Dup ⟨1, by decide⟩),
   opAt 2456 .LT,
   opAt 2457 (.Swap ⟨0, by decide⟩),
   opAt 2458 (.Dup ⟨4, by decide⟩),
   opAt 2459 (.Swap ⟨0, by decide⟩),
   opAt 2460 .SUB,
   opAt 2461 (.Dup ⟨3, by decide⟩),
   opAt 2462 .MSTORE,
   opAt 2463 .OR]

/-- The exit test of the subtract-round body (`blk3213` instructions 23..31). -/
def blk3213b :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2464 (.Swap ⟨1, by decide⟩),
   opAt 2465 .POP,
   pushAt 2466 1 31,
   opAt 2467 .NOT,
   opAt 2468 .ADD,
   pushAt 2469 2 2111,
   opAt 2470 (.Dup ⟨1, by decide⟩),
   opAt 2471 .GT,
   pushAt 2472 2 3247,
   opAt 2473 .JUMPI]

end Challenge.Modexp.Submission.Proofs.Fast
