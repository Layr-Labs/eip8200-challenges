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
    Artifact.submissionArtifact.instructionPC 2210 = 2849 := by rfl

@[simp] theorem helperPC (i : Nat) (hlo : 2210 ≤ i) (hhi : i ≤ 2232) :
    Artifact.submissionArtifact.instructionPC i =
      ([2849,2850,2853,2854,2857,2860,2861,2862,2864,2865,2866,2868,2869,2870,2872,2873,2874,2876,2877,2878,2879,2880,2883] : List Nat)[i - 2210]! := by
  interval_cases i <;> decide


def helperPath :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2210 .JUMPDEST,
   pushAt 2211 2 9344,
   opAt 2212 .MLOAD,
   pushAt 2213 2 5120,
   pushAt 2214 2 6144,
   opAt 2215 .MCOPY,
   opAt 2216 (.Dup ⟨1, by decide⟩),
   pushAt 2217 1 3,
   opAt 2218 .LT,
   opAt 2219 (.Dup ⟨2, by decide⟩),
   pushAt 2220 1 7,
   opAt 2221 .LT,
   opAt 2222 (.Dup ⟨3, by decide⟩),
   pushAt 2223 1 15,
   opAt 2224 .LT,
   opAt 2225 (.Dup ⟨4, by decide⟩),
   pushAt 2226 1 31,
   opAt 2227 .LT,
   opAt 2228 .ADD,
   opAt 2229 .ADD,
   opAt 2230 .ADD,
   pushAt 2231 2 1334,
   opAt 2232 .JUMP]

@[simp] theorem jump1569 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 1334 = true :=
  jumpDest1548

end Challenge.Modexp.Submission.Proofs.Bytecode.RrLeadingPaths
