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
    Artifact.submissionArtifact.instructionPC 2184 = 3074 := by
  rfl

@[simp] theorem helperPC (i : Nat)
    (hlo : 2184 ≤ i) (hhi : i ≤ 2206) :
    Artifact.submissionArtifact.instructionPC i =
      ([3074,3075,3078,3079,3082,3085,3086,3087,3089,3090,3091,3093,3094,3095,3097,3098,3099,3101,3102,3103,3104,3105,3108] : List Nat)[i - 2184]! := by
  interval_cases i <;> decide

def helperPath :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2184 .JUMPDEST,
   pushAt 2185 2 9344,
   opAt 2186 .MLOAD,
   pushAt 2187 2 5120,
   pushAt 2188 2 6144,
   opAt 2189 .MCOPY,
   opAt 2190 (.Dup ⟨1, by decide⟩),
   pushAt 2191 1 3,
   opAt 2192 .LT,
   opAt 2193 (.Dup ⟨2, by decide⟩),
   pushAt 2194 1 7,
   opAt 2195 .LT,
   opAt 2196 (.Dup ⟨3, by decide⟩),
   pushAt 2197 1 15,
   opAt 2198 .LT,
   opAt 2199 (.Dup ⟨4, by decide⟩),
   pushAt 2200 1 31,
   opAt 2201 .LT,
   opAt 2202 .ADD,
   opAt 2203 .ADD,
   opAt 2204 .ADD,
   pushAt 2205 2 1569,
   opAt 2206 .JUMP]

@[simp] theorem jump1569 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 1569 = true :=
  jumpDest1569

end Challenge.Modexp.Submission.Proofs.Bytecode.RrLeadingPaths
