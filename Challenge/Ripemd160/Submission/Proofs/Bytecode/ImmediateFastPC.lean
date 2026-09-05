import Challenge.Ripemd160.Submission.Proofs.Bytecode.ImmediateSiteCertificates
import Challenge.Ripemd160.Submission.Proofs.Bytecode.ImmediateLaneTrace

set_option warningAsError true
set_option maxRecDepth 50000
set_option maxHeartbeats 500000

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.ImmediateFastPC

open EvmSemantics EvmSemantics.EVM YulEvmCompiler Challenge.EvmProof
open ImmediateIteration

theorem instructionPC_succ (artifact : ProgramArtifact) (i : Nat) (instruction : Instr)
    (hget : artifact.instructions[i]? = some instruction) :
    artifact.instructionPC (i + 1) = artifact.instructionPC i + instruction.size := by
  unfold ProgramArtifact.instructionPC
  rw [List.take_add_one, hget]
  simp [assembleBytes_append, Instr.size]

theorem leftNextPC (i : Fin 80) :
    (leftSite i).ret.succ = UInt256.ofNat
      (Artifact.submissionArtifact.instructionPC (leftSite (i.val + 1)).startIndex) := by
  have hc := ImmediateSiteCertificates.leftCertificate80 i
  have hp := instructionPC_succ Artifact.submissionArtifact
    (997 + 9 * i.val + 8) (.op .JUMPDEST) hc.returnInstr
  change (UInt256.ofNat (Artifact.submissionArtifact.instructionPC
    (997 + 9 * i.val + 8))).succ = UInt256.ofNat
      (Artifact.submissionArtifact.instructionPC (997 + 9 * (i.val + 1)))
  rw [Word.succ_ofNat_mod]
  have hindex : 997 + 9 * i.val + 8 + 1 = 997 + 9 * (i.val + 1) := by omega
  simpa only [Instr.size_op, hindex] using (congrArg UInt256.ofNat hp).symm

theorem rightNextPC (i : Fin 79) :
    (rightSite i).ret.succ = UInt256.ofNat
      (Artifact.submissionArtifact.instructionPC
        (ImmediateLaneTrace.rightRegularSite (i.val + 1)).startIndex) := by
  have hc := ImmediateSiteCertificates.rightCertificate79 i
  have hi : i.val ≠ 79 := by omega
  have hget : Artifact.submissionArtifact.instructions[1717 + 9 * i.val + 8]? =
      some (.op .JUMPDEST) := by
    simpa only [ImmediateSites.rightData, if_neg hi] using hc.returnInstr
  have hp := instructionPC_succ Artifact.submissionArtifact
    (1717 + 9 * i.val + 8) (.op .JUMPDEST) hget
  change (rightSite i).ret.succ = UInt256.ofNat
    (Artifact.submissionArtifact.instructionPC (1717 + 9 * (i.val + 1)))
  simp only [rightSite, if_neg hi, mkImmediateSite]
  rw [Word.succ_ofNat_mod]
  have hindex : 1717 + 9 * i.val + 8 + 1 = 1717 + 9 * (i.val + 1) := by omega
  simpa only [Instr.size_op, hindex] using (congrArg UInt256.ofNat hp).symm

end Challenge.Ripemd160.Submission.Proofs.Bytecode.ImmediateFastPC
