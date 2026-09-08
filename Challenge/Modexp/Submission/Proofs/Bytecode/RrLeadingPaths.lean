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
    Artifact.submissionArtifact.instructionPC 2179 = 3356 := by
  rfl

@[simp] theorem helperPC (i : Nat)
    (hlo : 2179 ≤ i) (hhi : i ≤ 2201) :
    Artifact.submissionArtifact.instructionPC i =
      ([3356,3357,3360,3361,3364,3367,3368,3369,3371,3372,3373,3375,3376,3377,3379,3380,3381,3383,3384,3385,3386,3387,3390] : List Nat)[i - 2179]! := by
  interval_cases i <;> decide

def helperPath :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2179 .JUMPDEST,
   pushAt 2180 2 9344,
   opAt 2181 .MLOAD,
   pushAt 2182 2 5120,
   pushAt 2183 2 6144,
   opAt 2184 .MCOPY,
   opAt 2185 (.Dup ⟨1, by decide⟩),
   pushAt 2186 1 3,
   opAt 2187 .LT,
   opAt 2188 (.Dup ⟨2, by decide⟩),
   pushAt 2189 1 7,
   opAt 2190 .LT,
   opAt 2191 (.Dup ⟨3, by decide⟩),
   pushAt 2192 1 15,
   opAt 2193 .LT,
   opAt 2194 (.Dup ⟨4, by decide⟩),
   pushAt 2195 1 31,
   opAt 2196 .LT,
   opAt 2197 .ADD,
   opAt 2198 .ADD,
   opAt 2199 .ADD,
   pushAt 2200 2 1569,
   opAt 2201 .JUMP]

@[simp] theorem jump1569 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 1569 = true :=
  jumpDest1569

end Challenge.Modexp.Submission.Proofs.Bytecode.RrLeadingPaths
