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
  [opAt 1711 .JUMPDEST,
   pushAt 1712 2 2322,
   opAt 1713 (.Dup ⟨3, by decide⟩),
   opAt 1714 (.Dup ⟨0, by decide⟩),
   opAt 1715 (.Dup ⟨0, by decide⟩),
   pushAt 1716 2 1097,
   opAt 1717 .JUMP]

def entryPath : List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1702 .JUMPDEST,
   pushAt 1703 2 2688,
   opAt 1704 .MLOAD,
   pushAt 1705 1 128,
   opAt 1706 .LT,
   opAt 1707 (.Dup ⟨0, by decide⟩),
   pushAt 1708 1 8,
   opAt 1709 (.Swap ⟨0, by decide⟩),
   opAt 1710 .SHL]

def finishPath : List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1725 .POP,
   pushAt 1726 1 5,
   opAt 1727 .SUB,
   pushAt 1728 2 1255,
   opAt 1729 .JUMP]

def retPath : List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1718 .JUMPDEST,
   pushAt 1719 0 0,
   opAt 1720 .NOT,
   opAt 1721 .ADD,
   opAt 1722 (.Dup ⟨0, by decide⟩),
   pushAt 1723 2 2311,
   opAt 1724 .JUMPI]

private theorem instructionPC_add (p : Challenge.EvmProof.ProgramArtifact) (base count : Nat) :
    p.instructionPC (base + count) = p.instructionPC base +
      (assembleBytes ((p.instructions.drop base).take count)).length := by
  simp only [Challenge.EvmProof.ProgramArtifact.instructionPC, List.take_add,
    assembleBytes_append, List.length_append]

private theorem seedPCAnchor :
    Artifact.submissionArtifact.instructionPC 1702 = 2298 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem seedPC (i : Nat)
    (hi : 1702 ≤ i) (hii : i ≤ 1729) :
    Artifact.submissionArtifact.instructionPC i =
      ([2298,2299,2302,2303,2305,2306,2307,2309,2310,2311,2312,2315,2316,2317,2318,2321,2322,2323,2324,2325,2326,2327,2330,2331,2332,2334,2335,2338] : List Nat)[i - 1702]! := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  interval_cases i <;> rfl

theorem jumpDest3973 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 2298 = true :=
  Artifact.isValidJumpDest_index 1702 (by rfl)

theorem jumpDest4029 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 2311 = true :=
  Artifact.isValidJumpDest_index 1711 (by rfl)

theorem jumpDest4040 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 2322 = true :=
  Artifact.isValidJumpDest_index 1718 (by rfl)

end Challenge.Modexp.Submission.Proofs.Fast.CcbSeed
