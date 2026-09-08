import Challenge.Modexp.Submission.Proofs.Fast.Defs

set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000

/-!
# Located direct RR-leading helper

The appended helper occupies instruction indices 2240..2262 and bytes
3489..3523. It copies CC to RR, computes the remaining RR counter from the
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
    Artifact.submissionArtifact.instructionPC 2187 = 3485 := by
  rfl

@[simp] theorem helperPC (i : Nat) (hlo : 2187 ≤ i) (hhi : i ≤ 2209) :
    Artifact.submissionArtifact.instructionPC i =
      [3485, 3486, 3489, 3490, 3493, 3496, 3497, 3498,
       3500, 3501, 3502, 3504, 3505, 3506, 3508, 3509,
       3510, 3512, 3513, 3514, 3515, 3516, 3519][i - 2187]! := by
  calc
    Artifact.submissionArtifact.instructionPC i =
        Artifact.submissionArtifact.instructionPC (2187 + (i - 2187)) := by
      rw [Nat.add_sub_of_le hlo]
    _ = Artifact.submissionArtifact.instructionPC 2187 +
          (assembleBytes
            ((Artifact.submissionArtifact.instructions.drop 2187).take
              (i - 2187))).length :=
      instructionPC_add Artifact.submissionArtifact 2187 (i - 2187)
    _ = _ := by
      rw [helperPCAnchor]
      interval_cases i <;> rfl

def helperPath :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2187 .JUMPDEST,
   pushAt 2188 2 9344,
   opAt 2189 .MLOAD,
   pushAt 2190 2 5120,
   pushAt 2191 2 6144,
   opAt 2192 .MCOPY,
   opAt 2193 (.Dup ⟨1, by decide⟩),
   pushAt 2194 1 3,
   opAt 2195 .LT,
   opAt 2196 (.Dup ⟨2, by decide⟩),
   pushAt 2197 1 7,
   opAt 2198 .LT,
   opAt 2199 (.Dup ⟨3, by decide⟩),
   pushAt 2200 1 15,
   opAt 2201 .LT,
   opAt 2202 (.Dup ⟨4, by decide⟩),
   pushAt 2203 1 31,
   opAt 2204 .LT,
   opAt 2205 .ADD,
   opAt 2206 .ADD,
   opAt 2207 .ADD,
   pushAt 2208 2 1569,
   opAt 2209 .JUMP]

@[simp] theorem jump1569 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 1569 = true :=
  jumpDest1569

end Challenge.Modexp.Submission.Proofs.Bytecode.RrLeadingPaths
