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
    Artifact.submissionArtifact.instructionPC 2258 = 2972 := by rfl

@[simp] theorem helperPC (i : Nat) (hlo : 2258 ≤ i) (hhi : i ≤ 2280) :
    Artifact.submissionArtifact.instructionPC i =
      ([2972,2973,2976,2977,2980,2983,2984,2985,2987,2988,2989,2991,2992,2993,2995,2996,2997,2999,3000,3001,3002,3003,3006] : List Nat)[i - 2258]! := by
  interval_cases i <;> decide


def helperPath :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2258 .JUMPDEST,
   pushAt 2259 2 5248,
   opAt 2260 .MLOAD,
   pushAt 2261 2 1280,
   pushAt 2262 2 1536,
   opAt 2263 .MCOPY,
   opAt 2264 (.Dup ⟨1, by decide⟩),
   pushAt 2265 1 3,
   opAt 2266 .LT,
   opAt 2267 (.Dup ⟨2, by decide⟩),
   pushAt 2268 1 7,
   opAt 2269 .LT,
   opAt 2270 (.Dup ⟨3, by decide⟩),
   pushAt 2271 1 15,
   opAt 2272 .LT,
   opAt 2273 (.Dup ⟨4, by decide⟩),
   pushAt 2274 1 31,
   opAt 2275 .LT,
   opAt 2276 .ADD,
   opAt 2277 .ADD,
   opAt 2278 .ADD,
   pushAt 2279 2 1457,
   opAt 2280 .JUMP]

@[simp] theorem jump1569 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 1457 = true :=
  jumpDest1548

end Challenge.Modexp.Submission.Proofs.Bytecode.RrLeadingPaths
