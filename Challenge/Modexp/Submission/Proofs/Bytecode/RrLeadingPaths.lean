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
    Artifact.submissionArtifact.instructionPC 2203 = 3420 := by
  rfl

@[simp] theorem helperPC (i : Nat)
    (hlo : 2230 ≤ i) (hhi : i ≤ 2252) :
    Artifact.submissionArtifact.instructionPC i =
      ([3566,3567,3570,3571,3574,3577,3578,3579,3581,3582,3583,3585,3586,3587,3589,3590,3591,3593,3594,3595,3596,3597,3600] : List Nat)[i - 2230]! := by
  interval_cases i <;> decide

def helperPath :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2203 .JUMPDEST,
   pushAt 2204 2 9344,
   opAt 2205 .MLOAD,
   pushAt 2206 2 5120,
   pushAt 2207 2 6144,
   opAt 2208 .MCOPY,
   opAt 2209 (.Dup ⟨1, by decide⟩),
   pushAt 2210 1 3,
   opAt 2211 .LT,
   opAt 2212 (.Dup ⟨2, by decide⟩),
   pushAt 2213 1 7,
   opAt 2214 .LT,
   opAt 2215 (.Dup ⟨3, by decide⟩),
   pushAt 2216 1 15,
   opAt 2217 .LT,
   opAt 2218 (.Dup ⟨4, by decide⟩),
   pushAt 2219 1 31,
   opAt 2220 .LT,
   opAt 2221 .ADD,
   opAt 2222 .ADD,
   opAt 2223 .ADD,
   pushAt 2224 2 1556,
   opAt 2225 .JUMP]

@[simp] theorem jump1569 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 1569 = true :=
  jumpDest1569

end Challenge.Modexp.Submission.Proofs.Bytecode.RrLeadingPaths
