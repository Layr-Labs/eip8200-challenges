import Challenge.Modexp.Submission.Proofs.Fast.Defs

set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000

/-! Located direct RR helper: indices 2499..2521, bytes 3234..3263. -/

namespace Challenge.Modexp.Submission.Proofs.Bytecode.RrLeadingPaths

open EvmSemantics
open EvmSemantics.EVM
open YulEvmCompiler
open Challenge.Modexp.Submission.Proofs.Fast

private theorem instructionPC_add
    (p : Challenge.EvmProof.ProgramArtifact) (base count : Nat) :
    p.instructionPC (base + count) =
      p.instructionPC base +
        (assembleBytes ((p.instructions.drop base).take count)).length := by
  simp only [Challenge.EvmProof.ProgramArtifact.instructionPC, List.take_add,
    assembleBytes_append, List.length_append]

private theorem helperPCAnchor :
    Artifact.submissionArtifact.instructionPC 2273 = 2960 := by rfl

@[simp] theorem helperPC (i : Nat) (hlo : 2273 ≤ i) (hhi : i ≤ 2295) :
    Artifact.submissionArtifact.instructionPC i =
      ([2960,2961,2964,2965,2968,2971,2972,2973,2975,2976,2977,2979,2980,2981,2983,2984,2985,2987,2988,2989,2990,2991,2994] : List Nat)[i - 2273]! := by
  interval_cases i <;> decide


def helperPath :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2273 .JUMPDEST,
   pushAt 2274 2 5248,
   opAt 2275 .MLOAD,
   pushAt 2276 2 1280,
   pushAt 2277 2 1536,
   opAt 2278 .MCOPY,
   opAt 2279 (.Dup ⟨1, by decide⟩),
   pushAt 2280 1 3,
   opAt 2281 .LT,
   opAt 2282 (.Dup ⟨2, by decide⟩),
   pushAt 2283 1 7,
   opAt 2284 .LT,
   opAt 2285 (.Dup ⟨3, by decide⟩),
   pushAt 2286 1 15,
   opAt 2287 .LT,
   opAt 2288 (.Dup ⟨4, by decide⟩),
   pushAt 2289 1 31,
   opAt 2290 .LT,
   opAt 2291 .ADD,
   opAt 2292 .ADD,
   opAt 2293 .ADD,
   pushAt 2294 2 1452,
   opAt 2295 .JUMP]

@[simp] theorem jump1569 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 1452 = true :=
  jumpDest1548

end Challenge.Modexp.Submission.Proofs.Bytecode.RrLeadingPaths
