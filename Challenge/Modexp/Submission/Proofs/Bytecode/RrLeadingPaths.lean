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
    Artifact.submissionArtifact.instructionPC 2180 = 3566 := by
  rfl

@[simp] theorem helperPC (i : Nat)
    (hlo : 2180 ≤ i) (hhi : i ≤ 2202) :
    Artifact.submissionArtifact.instructionPC i =
      ([3566,3567,3570,3571,3574,3577,3578,3579,3581,3582,3583,3585,3586,3587,3589,3590,3591,3593,3594,3595,3596,3597,3600] : List Nat)[i - 2180]! := by
  interval_cases i <;> decide

def helperPath :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2180 .JUMPDEST,
   pushAt 2181 2 9344,
   opAt 2182 .MLOAD,
   pushAt 2183 2 5120,
   pushAt 2184 2 6144,
   opAt 2185 .MCOPY,
   opAt 2186 (.Dup ⟨1, by decide⟩),
   pushAt 2187 1 3,
   opAt 2188 .LT,
   opAt 2189 (.Dup ⟨2, by decide⟩),
   pushAt 2190 1 7,
   opAt 2191 .LT,
   opAt 2192 (.Dup ⟨3, by decide⟩),
   pushAt 2193 1 15,
   opAt 2194 .LT,
   opAt 2195 (.Dup ⟨4, by decide⟩),
   pushAt 2196 1 31,
   opAt 2197 .LT,
   opAt 2198 .ADD,
   opAt 2199 .ADD,
   opAt 2200 .ADD,
   pushAt 2201 2 1569,
   opAt 2202 .JUMP]

@[simp] theorem jump1569 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 1569 = true :=
  jumpDest1569

end Challenge.Modexp.Submission.Proofs.Bytecode.RrLeadingPaths
