import Challenge.Modexp.Submission.Proofs.Fast.Defs

set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000

/-!
# Located direct RR-leading helper

The appended helper occupies instruction indices 2338..2360 and bytes
3571..3605. It copies CC to RR, computes the remaining RR counter from the
limb count, and rejoins the unchanged RR loop at byte 1569.
-/

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
    Artifact.submissionArtifact.instructionPC 2256 = 3571 := by
  rfl

@[simp] theorem helperPC (i : Nat)
    (hlo : 2256 ≤ i) (hhi : i ≤ 2278) :
    Artifact.submissionArtifact.instructionPC i =
      ([3571,3572,3575,3576,3579,3582,3583,3584,3586,3587,3588,3590,3591,3592,3594,3595,3596,3598,3599,3600,3601,3602,3605] : List Nat)[i - 2256]! := by
  interval_cases i <;> decide

def helperPath :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2256 .JUMPDEST,
   pushAt 2257 2 9344,
   opAt 2258 .MLOAD,
   pushAt 2259 2 5120,
   pushAt 2260 2 6144,
   opAt 2261 .MCOPY,
   opAt 2262 (.Dup ⟨1, by decide⟩),
   pushAt 2263 1 3,
   opAt 2264 .LT,
   opAt 2265 (.Dup ⟨2, by decide⟩),
   pushAt 2266 1 7,
   opAt 2267 .LT,
   opAt 2268 (.Dup ⟨3, by decide⟩),
   pushAt 2269 1 15,
   opAt 2270 .LT,
   opAt 2271 (.Dup ⟨4, by decide⟩),
   pushAt 2272 1 31,
   opAt 2273 .LT,
   opAt 2274 .ADD,
   opAt 2275 .ADD,
   opAt 2276 .ADD,
   pushAt 2277 2 1569,
   opAt 2278 .JUMP]

@[simp] theorem jump1569 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 1569 = true :=
  jumpDest1569

end Challenge.Modexp.Submission.Proofs.Bytecode.RrLeadingPaths
