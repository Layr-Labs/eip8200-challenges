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
    Artifact.submissionArtifact.instructionPC 2101 = 2704 := by rfl

@[simp] theorem helperPC (i : Nat) (hlo : 2205 ≤ i) (hhi : i ≤ 2227) :
    Artifact.submissionArtifact.instructionPC i =
      ([2837,2838,2841,2842,2845,2848,2849,2850,2852,2853,2854,2856,2857,2858,2860,2861,2862,2864,2865,2866,2867,2868,2871] : List Nat)[i - 2205]! := by
  interval_cases i <;> decide


def helperPath :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2101 .JUMPDEST,
   pushAt 2102 2 9344,
   opAt 2103 .MLOAD,
   pushAt 2104 2 5120,
   pushAt 2105 2 6144,
   opAt 2106 .MCOPY,
   opAt 2107 (.Dup ⟨1, by decide⟩),
   pushAt 2108 1 3,
   opAt 2109 .LT,
   opAt 2110 (.Dup ⟨2, by decide⟩),
   pushAt 2111 1 7,
   opAt 2112 .LT,
   opAt 2113 (.Dup ⟨3, by decide⟩),
   pushAt 2114 1 15,
   opAt 2115 .LT,
   opAt 2116 (.Dup ⟨4, by decide⟩),
   pushAt 2117 1 31,
   opAt 2118 .LT,
   opAt 2119 .ADD,
   opAt 2120 .ADD,
   opAt 2121 .ADD,
   pushAt 2122 2 1189,
   opAt 2123 .JUMP]

@[simp] theorem jump1569 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 1189 = true :=
  jumpDest1548

end Challenge.Modexp.Submission.Proofs.Bytecode.RrLeadingPaths
