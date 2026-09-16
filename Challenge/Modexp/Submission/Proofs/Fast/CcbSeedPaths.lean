import Challenge.Modexp.Submission.Proofs.Bytecode.PCFast
import Challenge.Modexp.Submission.Proofs.Fast.Defs
set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000

namespace Challenge.Modexp.Submission.Proofs.Fast.CcbSeed

open EvmSemantics EvmSemantics.EVM YulEvmCompiler
open Challenge.Modexp.Submission.Proofs.Bytecode
open Challenge.Modexp.Submission.Proofs.Fast

def callPath : List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1713 .JUMPDEST,
   pushAt 1714 2 2322,
   opAt 1715 (.Dup ⟨3, by decide⟩),
   opAt 1716 (.Dup ⟨0, by decide⟩),
   opAt 1717 (.Dup ⟨0, by decide⟩),
   pushAt 1718 2 1097,
   opAt 1719 .JUMP]

def entryPath : List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1704 .JUMPDEST,
   pushAt 1705 2 2688,
   opAt 1706 .MLOAD,
   pushAt 1707 1 128,
   opAt 1708 .LT,
   opAt 1709 (.Dup ⟨0, by decide⟩),
   pushAt 1710 1 8,
   opAt 1711 (.Swap ⟨0, by decide⟩),
   opAt 1712 .SHL]

def finishPath : List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1727 .POP,
   pushAt 1728 1 5,
   opAt 1729 .SUB,
   pushAt 1730 2 1255,
   opAt 1731 .JUMP]

def retPath : List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1720 .JUMPDEST,
   pushAt 1721 0 0,
   opAt 1722 .NOT,
   opAt 1723 .ADD,
   opAt 1724 (.Dup ⟨0, by decide⟩),
   pushAt 1725 2 2311,
   opAt 1726 .JUMPI]

private theorem instructionPC_add (p : Challenge.EvmProof.ProgramArtifact) (base count : Nat) :
    p.instructionPC (base + count) = p.instructionPC base +
      (assembleBytes ((p.instructions.drop base).take count)).length := by
  simp only [Challenge.EvmProof.ProgramArtifact.instructionPC, List.take_add,
    assembleBytes_append, List.length_append]

private theorem seedPCAnchor :
    Artifact.submissionArtifact.instructionPC 1704 = 2298 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem seedPC (i : Nat)
    (hi : 1704 ≤ i) (hii : i ≤ 1731) :
    Artifact.submissionArtifact.instructionPC i =
      ([2298,2299,2302,2303,2305,2306,2307,2309,2310,2311,2312,2315,2316,2317,2318,2321,2322,2323,2324,2325,2326,2327,2330,2331,2332,2334,2335,2338] : List Nat)[i - 1704]! := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  interval_cases i <;> rfl

theorem jumpDest3973 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 2298 = true :=
  Artifact.isValidJumpDest_index 1704 (by rfl)

theorem jumpDest4029 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 2311 = true :=
  Artifact.isValidJumpDest_index 1713 (by rfl)

theorem jumpDest4040 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 2322 = true :=
  Artifact.isValidJumpDest_index 1720 (by rfl)

end Challenge.Modexp.Submission.Proofs.Fast.CcbSeed
