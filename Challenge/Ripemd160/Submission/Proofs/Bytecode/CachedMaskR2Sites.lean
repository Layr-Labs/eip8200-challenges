import Challenge.Ripemd160.Submission.Proofs.Bytecode.CachedMaskR2Inline
import Challenge.Ripemd160.Submission.Proofs.Bytecode.QuadSitesBase

set_option warningAsError true
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.CachedMaskR2Sites

open EvmSemantics EvmSemantics.EVM YulEvmCompiler Challenge.EvmProof
open StackRoundTemplate
open CachedMaskR2Inline

abbrev A := QuadSites.Artifact

-- The retained R1 return JUMPDEST is at index 2511. R2 starts after it.
theorem r2_slice :
    (A.instructions.drop 2512).take r2Code.length = r2Code := by rfl

def site : GenericRoundSite A .Osaka r2Code :=
  StackSiteBuilder.ofSlice _ 2512 r2_slice
    (by
      change 2512 + r2Code.length ≤ Artifact.submissionInstructions.length
      rw [Artifact.referenceInstructions_count, r2Code_length]
      decide)
    QuadLayout.code_bound
    (StackRoundData.templateWellFormed_mem (by decide))
    (by intro h; have hlen := r2Code_length; simp [h] at hlen)

theorem start_pc : site.startPC = UInt256.ofNat 3773 := by
  change UInt256.ofNat (A.instructionPC 2512) = _
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

theorem end_pc : site.endPC = UInt256.ofNat 4333 := by
  have h := StackRoundTrace.endPC_eq_pcAfter_sites site.sites site.startPC site.endPC
    site.head_eq site.end_eq site.contiguous
  rw [site.instruction_eq, start_pc] at h
  exact h.trans (by decide)

theorem start_rightPC : site.startPC = QuadSites.rightPC 8 := by
  rw [start_pc]
  change UInt256.ofNat 3773 = UInt256.ofNat (A.instructionPC _)
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

theorem end_rightPC : site.endPC = QuadSites.rightPC 12 := by
  rw [end_pc]
  change UInt256.ofNat 4333 = UInt256.ofNat (A.instructionPC _)
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

#print axioms r2_slice
#print axioms start_rightPC
#print axioms end_rightPC

end Challenge.Ripemd160.Submission.Proofs.Bytecode.CachedMaskR2Sites
