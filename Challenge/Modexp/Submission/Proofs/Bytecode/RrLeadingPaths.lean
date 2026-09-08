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
    Artifact.submissionArtifact.instructionPC 2156 = 3533 := by
  rfl

@[simp] theorem helperPC (i : Nat)
    (hlo : 2156 ≤ i) (hhi : i ≤ 2178) :
    Artifact.submissionArtifact.instructionPC i =
      [3533,3534,3537,3538,3541,3544,3545,3546,3548,3549,3550,3552,3553,3554,3556,3557,3558,3560,3561,3562,3563,3564,3567][i - 2156]! := by
  interval_cases i <;> decide

def helperPath :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2156 .JUMPDEST,
   pushAt 2157 2 9344,
   opAt 2158 .MLOAD,
   pushAt 2159 2 5120,
   pushAt 2160 2 6144,
   opAt 2161 .MCOPY,
   opAt 2162 (.Dup ⟨1, by decide⟩),
   pushAt 2163 1 3,
   opAt 2164 .LT,
   opAt 2165 (.Dup ⟨2, by decide⟩),
   pushAt 2166 1 7,
   opAt 2167 .LT,
   opAt 2168 (.Dup ⟨3, by decide⟩),
   pushAt 2169 1 15,
   opAt 2170 .LT,
   opAt 2171 (.Dup ⟨4, by decide⟩),
   pushAt 2172 1 31,
   opAt 2173 .LT,
   opAt 2174 .ADD,
   opAt 2175 .ADD,
   opAt 2176 .ADD,
   pushAt 2177 2 1563,
   opAt 2178 .JUMP]

@[simp] theorem jump1569 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 1563 = true :=
  jumpDest1569

end Challenge.Modexp.Submission.Proofs.Bytecode.RrLeadingPaths
