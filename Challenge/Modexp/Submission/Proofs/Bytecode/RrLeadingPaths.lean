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
    Artifact.submissionArtifact.instructionPC 2229 = 2878 := by rfl

@[simp] theorem helperPC (i : Nat) (hlo : 2229 ≤ i) (hhi : i ≤ 2251) :
    Artifact.submissionArtifact.instructionPC i =
      ([2878,2879,2882,2883,2886,2889,2890,2891,2893,2894,2895,2897,2898,2899,2901,2902,2903,2905,2906,2907,2908,2909,2912] : List Nat)[i - 2229]! := by
  interval_cases i <;> decide


def helperPath :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2229 .JUMPDEST,
   pushAt 2230 2 9344,
   opAt 2231 .MLOAD,
   pushAt 2232 2 5120,
   pushAt 2233 2 6144,
   opAt 2234 .MCOPY,
   opAt 2235 (.Dup ⟨1, by decide⟩),
   pushAt 2236 1 3,
   opAt 2237 .LT,
   opAt 2238 (.Dup ⟨2, by decide⟩),
   pushAt 2239 1 7,
   opAt 2240 .LT,
   opAt 2241 (.Dup ⟨3, by decide⟩),
   pushAt 2242 1 15,
   opAt 2243 .LT,
   opAt 2244 (.Dup ⟨4, by decide⟩),
   pushAt 2245 1 31,
   opAt 2246 .LT,
   opAt 2247 .ADD,
   opAt 2248 .ADD,
   opAt 2249 .ADD,
   pushAt 2250 2 1355,
   opAt 2251 .JUMP]

@[simp] theorem jump1569 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 1355 = true :=
  jumpDest1548

end Challenge.Modexp.Submission.Proofs.Bytecode.RrLeadingPaths
