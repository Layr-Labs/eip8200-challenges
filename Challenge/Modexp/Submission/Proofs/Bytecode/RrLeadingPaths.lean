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
    Artifact.submissionArtifact.instructionPC 2322 = 3014 := by rfl

@[simp] theorem helperPC (i : Nat) (hlo : 2322 ≤ i) (hhi : i ≤ 2344) :
    Artifact.submissionArtifact.instructionPC i =
      ([3014,3015,3018,3019,3022,3025,3026,3027,3029,3030,3031,3033,3034,3035,3037,3038,3039,3041,3042,3043,3044,3045,3048] : List Nat)[i - 2322]! := by
  interval_cases i <;> decide


def helperPath :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2322 .JUMPDEST,
   pushAt 2323 2 9344,
   opAt 2324 .MLOAD,
   pushAt 2325 2 5120,
   pushAt 2326 2 6144,
   opAt 2327 .MCOPY,
   opAt 2328 (.Dup ⟨1, by decide⟩),
   pushAt 2329 1 3,
   opAt 2330 .LT,
   opAt 2331 (.Dup ⟨2, by decide⟩),
   pushAt 2332 1 7,
   opAt 2333 .LT,
   opAt 2334 (.Dup ⟨3, by decide⟩),
   pushAt 2335 1 15,
   opAt 2336 .LT,
   opAt 2337 (.Dup ⟨4, by decide⟩),
   pushAt 2338 1 31,
   opAt 2339 .LT,
   opAt 2340 .ADD,
   opAt 2341 .ADD,
   opAt 2342 .ADD,
   pushAt 2343 2 1467,
   opAt 2344 .JUMP]

@[simp] theorem jump1569 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 1467 = true :=
  jumpDest1548

end Challenge.Modexp.Submission.Proofs.Bytecode.RrLeadingPaths
