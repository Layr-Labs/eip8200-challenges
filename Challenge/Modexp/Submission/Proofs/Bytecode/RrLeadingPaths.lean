import Challenge.Modexp.Submission.Proofs.Fast.Defs

set_option warningAsError true
set_option maxRecDepth 160000
set_option maxHeartbeats 16000000

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
    Artifact.submissionArtifact.instructionPC 2201 = 2829 := by rfl

@[simp] theorem helperPC (i : Nat) (hlo : 2205 ≤ i) (hhi : i ≤ 2227) :
    Artifact.submissionArtifact.instructionPC i =
      ([2837,2838,2841,2842,2845,2848,2849,2850,2852,2853,2854,2856,2857,2858,2860,2861,2862,2864,2865,2866,2867,2868,2871] : List Nat)[i - 2205]! := by
  interval_cases i <;> decide


def helperPath :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2201 .JUMPDEST,
   pushAt 2202 2 9344,
   opAt 2203 .MLOAD,
   pushAt 2204 2 5120,
   pushAt 2205 2 6144,
   opAt 2206 .MCOPY,
   opAt 2207 (.Dup ⟨1, by decide⟩),
   pushAt 2208 1 3,
   opAt 2209 .LT,
   opAt 2210 (.Dup ⟨2, by decide⟩),
   pushAt 2211 1 7,
   opAt 2212 .LT,
   opAt 2213 (.Dup ⟨3, by decide⟩),
   pushAt 2214 1 15,
   opAt 2215 .LT,
   opAt 2216 (.Dup ⟨4, by decide⟩),
   pushAt 2217 1 31,
   opAt 2218 .LT,
   opAt 2219 .ADD,
   opAt 2220 .ADD,
   opAt 2221 .ADD,
   pushAt 2222 2 1318,
   opAt 2223 .JUMP]

@[simp] theorem jump1569 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 1318 = true :=
  jumpDest1548

end Challenge.Modexp.Submission.Proofs.Bytecode.RrLeadingPaths
