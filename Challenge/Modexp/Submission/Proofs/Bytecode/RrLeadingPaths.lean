import Challenge.Modexp.Submission.Proofs.Bytecode.PCFast
import Challenge.Modexp.Submission.Proofs.Fast.Defs

set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000

/-! Located direct RR helper: indices 2511..2533, bytes 3194..3218. -/

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
    Artifact.submissionArtifact.instructionPC 1521 = 2009 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem helperPC (i : Nat) (hlo : 1521 ≤ i) (hhi : i ≤ 1543) :
    Artifact.submissionArtifact.instructionPC i =
      ([2009,2010,2013,2014,2017,2020,2021,2022,2024,2025,2026,2028,2029,2030,2032,2033,2034,2036,2037,2038,2039,2040,2043] : List Nat)[i - 1521]! := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  interval_cases i <;> rfl


def helperPath :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1517 .JUMPDEST,
   pushAt 1518 2 2688,
   opAt 1519 .MLOAD,
   pushAt 1520 2 1280,
   pushAt 1521 2 1536,
   opAt 1522 .MCOPY,
   opAt 1523 (.Dup ⟨1, by decide⟩),
   pushAt 1524 1 3,
   opAt 1525 .LT,
   opAt 1526 (.Dup ⟨2, by decide⟩),
   pushAt 1527 1 7,
   opAt 1528 .LT,
   opAt 1529 (.Dup ⟨3, by decide⟩),
   pushAt 1530 1 15,
   opAt 1531 .LT,
   opAt 1532 (.Dup ⟨4, by decide⟩),
   pushAt 1533 1 31,
   opAt 1534 .LT,
   opAt 1535 .ADD,
   opAt 1536 .ADD,
   opAt 1537 .ADD,
   pushAt 1538 2 804,
   opAt 1539 .JUMP]

@[simp] theorem jump1569 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 804 = true :=
  jumpDest1548

end Challenge.Modexp.Submission.Proofs.Bytecode.RrLeadingPaths
