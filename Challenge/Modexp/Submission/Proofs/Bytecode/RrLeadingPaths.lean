import Challenge.Modexp.Submission.Proofs.Fast.Defs

set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000

/-!
# Located direct RR-leading helper

The appended helper occupies instruction indices 2338..2360 and bytes
3079..3113. It copies CC to RR, computes the remaining RR counter from the
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
    Artifact.submissionArtifact.instructionPC 2200 = 3074 := by
  rfl

@[simp] theorem helperPC (i : Nat)
    (hlo : 2200 ≤ i) (hhi : i ≤ 2222) :
    Artifact.submissionArtifact.instructionPC i =
      ([3074,3075,3078,3079,3082,3085,3086,3087,3089,3090,3091,3093,3094,3095,3097,3098,3099,3101,3102,3103,3104,3105,3108] : List Nat)[i - 2200]! := by
  interval_cases i <;> decide

def helperPath :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2200 .JUMPDEST,
   pushAt 2201 2 9344,
   opAt 2202 .MLOAD,
   pushAt 2203 2 5120,
   pushAt 2204 2 6144,
   opAt 2205 .MCOPY,
   opAt 2206 (.Dup ⟨1, by decide⟩),
   pushAt 2207 1 3,
   opAt 2208 .LT,
   opAt 2209 (.Dup ⟨2, by decide⟩),
   pushAt 2210 1 7,
   opAt 2211 .LT,
   opAt 2212 (.Dup ⟨3, by decide⟩),
   pushAt 2213 1 15,
   opAt 2214 .LT,
   opAt 2215 (.Dup ⟨4, by decide⟩),
   pushAt 2216 1 31,
   opAt 2217 .LT,
   opAt 2218 .ADD,
   opAt 2219 .ADD,
   opAt 2220 .ADD,
   pushAt 2221 2 1569,
   opAt 2222 .JUMP]

@[simp] theorem jump1569 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 1569 = true :=
  jumpDest1569

end Challenge.Modexp.Submission.Proofs.Bytecode.RrLeadingPaths
