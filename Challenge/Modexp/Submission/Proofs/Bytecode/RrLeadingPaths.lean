import Challenge.Modexp.Submission.Proofs.Fast.Defs

set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000

/-!
# Located direct RR-leading helper

The appended helper occupies instruction indices 2190..2212 and bytes
3566..3600. It copies CC to RR, computes the remaining RR counter from the
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
    Artifact.submissionArtifact.instructionPC 2190 = 3566 := by
  rfl

@[simp] theorem helperPC (i : Nat)
    (hlo : 2190 ≤ i) (hhi : i ≤ 2212) :
    Artifact.submissionArtifact.instructionPC i =
      ([3566,3567,3570,3571,3574,3577,3578,3579,3581,3582,3583,3585,3586,3587,3589,3590,3591,3593,3594,3595,3596,3597,3600] : List Nat)[i - 2190]! := by
  interval_cases i <;> decide

def helperPath :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2190 .JUMPDEST,
   pushAt 2191 2 9344,
   opAt 2192 .MLOAD,
   pushAt 2193 2 5120,
   pushAt 2194 2 6144,
   opAt 2195 .MCOPY,
   opAt 2196 (.Dup ⟨1, by decide⟩),
   pushAt 2197 1 3,
   opAt 2198 .LT,
   opAt 2199 (.Dup ⟨2, by decide⟩),
   pushAt 2200 1 7,
   opAt 2201 .LT,
   opAt 2202 (.Dup ⟨3, by decide⟩),
   pushAt 2203 1 15,
   opAt 2204 .LT,
   opAt 2205 (.Dup ⟨4, by decide⟩),
   pushAt 2206 1 31,
   opAt 2207 .LT,
   opAt 2208 .ADD,
   opAt 2209 .ADD,
   opAt 2210 .ADD,
   pushAt 2211 2 1569,
   opAt 2212 .JUMP]

@[simp] theorem jump1569 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 1569 = true :=
  jumpDest1569

end Challenge.Modexp.Submission.Proofs.Bytecode.RrLeadingPaths
