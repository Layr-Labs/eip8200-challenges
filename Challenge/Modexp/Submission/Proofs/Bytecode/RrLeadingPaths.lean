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
    Artifact.submissionArtifact.instructionPC 2240 = 3489 := by
  rfl

@[simp] theorem helperPC (i : Nat) (hlo : 2240 ≤ i) (hhi : i ≤ 2262) :
    Artifact.submissionArtifact.instructionPC i =
      [3489, 3490, 3493, 3494, 3497, 3500, 3501, 3502,
       3504, 3505, 3506, 3508, 3509, 3510, 3512, 3513,
       3514, 3516, 3517, 3518, 3519, 3520, 3523][i - 2240]! := by
  calc
    Artifact.submissionArtifact.instructionPC i =
        Artifact.submissionArtifact.instructionPC (2240 + (i - 2240)) := by
      rw [Nat.add_sub_of_le hlo]
    _ = Artifact.submissionArtifact.instructionPC 2240 +
          (assembleBytes
            ((Artifact.submissionArtifact.instructions.drop 2240).take
              (i - 2240))).length :=
      instructionPC_add Artifact.submissionArtifact 2240 (i - 2240)
    _ = _ := by
      rw [helperPCAnchor]
      interval_cases i <;> rfl

def helperPath :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2240 .JUMPDEST,
   pushAt 2241 2 9344,
   opAt 2242 .MLOAD,
   pushAt 2243 2 5120,
   pushAt 2244 2 6144,
   opAt 2245 .MCOPY,
   opAt 2246 (.Dup ⟨1, by decide⟩),
   pushAt 2247 1 3,
   opAt 2248 .LT,
   opAt 2249 (.Dup ⟨2, by decide⟩),
   pushAt 2250 1 7,
   opAt 2251 .LT,
   opAt 2252 (.Dup ⟨3, by decide⟩),
   pushAt 2253 1 15,
   opAt 2254 .LT,
   opAt 2255 (.Dup ⟨4, by decide⟩),
   pushAt 2256 1 31,
   opAt 2257 .LT,
   opAt 2258 .ADD,
   opAt 2259 .ADD,
   opAt 2260 .ADD,
   pushAt 2261 2 1569,
   opAt 2262 .JUMP]

@[simp] theorem jump1569 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 1569 = true :=
  jumpDest1569

end Challenge.Modexp.Submission.Proofs.Bytecode.RrLeadingPaths
