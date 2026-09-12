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
    Artifact.submissionArtifact.instructionPC 2205 = 2837 := by rfl

@[simp] theorem helperPC (i : Nat) (hlo : 2205 ≤ i) (hhi : i ≤ 2227) :
    Artifact.submissionArtifact.instructionPC i =
      ([2837,2838,2841,2842,2845,2848,2849,2850,2852,2853,2854,2856,2857,2858,2860,2861,2862,2864,2865,2866,2867,2868,2871] : List Nat)[i - 2205]! := by
  interval_cases i <;> decide


def helperPath :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2205 .JUMPDEST,
   pushAt 2206 2 5248,
   opAt 2207 .MLOAD,
   pushAt 2208 2 1280,
   pushAt 2209 2 1536,
   opAt 2210 .MCOPY,
   opAt 2211 (.Dup ⟨1, by decide⟩),
   pushAt 2212 1 3,
   opAt 2213 .LT,
   opAt 2214 (.Dup ⟨2, by decide⟩),
   pushAt 2215 1 7,
   opAt 2216 .LT,
   opAt 2217 (.Dup ⟨3, by decide⟩),
   pushAt 2218 1 15,
   opAt 2219 .LT,
   opAt 2220 (.Dup ⟨4, by decide⟩),
   pushAt 2221 1 31,
   opAt 2222 .LT,
   opAt 2223 .ADD,
   opAt 2224 .ADD,
   opAt 2225 .ADD,
   pushAt 2226 2 1322,
   opAt 2227 .JUMP]

@[simp] theorem jump1569 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 1322 = true :=
  jumpDest1548

end Challenge.Modexp.Submission.Proofs.Bytecode.RrLeadingPaths
