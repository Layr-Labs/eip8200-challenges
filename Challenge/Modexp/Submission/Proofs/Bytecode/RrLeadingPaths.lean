import Challenge.Modexp.Submission.Proofs.Fast.Defs

set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000

/-! Located direct RR helper: indices 2372..2394, bytes 3107..3141. -/

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
    Artifact.submissionArtifact.instructionPC 2208 = 2845 := by rfl

@[simp] theorem helperPC (i : Nat) (hlo : 2208 ≤ i) (hhi : i ≤ 2230) :
    Artifact.submissionArtifact.instructionPC i =
      ([2845,2846,2849,2850,2853,2856,2857,2858,2860,2861,2862,2864,2865,2866,2868,2869,2870,2872,2873,2874,2875,2876,2879] : List Nat)[i - 2208]! := by
  interval_cases i <;> decide


def helperPath :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2208 .JUMPDEST,
   pushAt 2209 2 9344,
   opAt 2210 .MLOAD,
   pushAt 2211 2 5120,
   pushAt 2212 2 6144,
   opAt 2213 .MCOPY,
   opAt 2214 (.Dup ⟨1, by decide⟩),
   pushAt 2215 1 3,
   opAt 2216 .LT,
   opAt 2217 (.Dup ⟨2, by decide⟩),
   pushAt 2218 1 7,
   opAt 2219 .LT,
   opAt 2220 (.Dup ⟨3, by decide⟩),
   pushAt 2221 1 15,
   opAt 2222 .LT,
   opAt 2223 (.Dup ⟨4, by decide⟩),
   pushAt 2224 1 31,
   opAt 2225 .LT,
   opAt 2226 .ADD,
   opAt 2227 .ADD,
   opAt 2228 .ADD,
   pushAt 2229 2 1334,
   opAt 2230 .JUMP]

@[simp] theorem jump1569 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 1334 = true :=
  jumpDest1548

end Challenge.Modexp.Submission.Proofs.Bytecode.RrLeadingPaths
