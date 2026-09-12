import Challenge.Modexp.Submission.Proofs.Fast.Defs

set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000

/-! Located direct RR helper: indices 2376..2398, bytes 3111..3145. -/

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
    Artifact.submissionArtifact.instructionPC 2280 = 2972 := by rfl

@[simp] theorem helperPC (i : Nat) (hlo : 2280 ≤ i) (hhi : i ≤ 2302) :
    Artifact.submissionArtifact.instructionPC i =
      ([2972,2973,2976,2977,2980,2983,2984,2985,2987,2988,2989,2991,2992,2993,2995,2996,2997,2999,3000,3001,3002,3003,3006] : List Nat)[i - 2280]! := by
  interval_cases i <;> decide


def helperPath :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2280 .JUMPDEST,
   pushAt 2281 2 9344,
   opAt 2282 .MLOAD,
   pushAt 2283 2 5120,
   pushAt 2284 2 6144,
   opAt 2285 .MCOPY,
   opAt 2286 (.Dup ⟨1, by decide⟩),
   pushAt 2287 1 3,
   opAt 2288 .LT,
   opAt 2289 (.Dup ⟨2, by decide⟩),
   pushAt 2290 1 7,
   opAt 2291 .LT,
   opAt 2292 (.Dup ⟨3, by decide⟩),
   pushAt 2293 1 15,
   opAt 2294 .LT,
   opAt 2295 (.Dup ⟨4, by decide⟩),
   pushAt 2296 1 31,
   opAt 2297 .LT,
   opAt 2298 .ADD,
   opAt 2299 .ADD,
   opAt 2300 .ADD,
   pushAt 2301 2 1457,
   opAt 2302 .JUMP]

@[simp] theorem jump1569 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 1457 = true :=
  jumpDest1548

end Challenge.Modexp.Submission.Proofs.Bytecode.RrLeadingPaths
