import Challenge.Modexp.Submission.LocalPatch.PointerStates
import Challenge.Modexp.Submission.Proofs.Bytecode.ShiftPCs

set_option warningAsError true
set_option linter.unusedSimpArgs false

/-!
# Exact frontier64 patch-site decoder facts

This module is the only new dependency on the frozen concrete ProgramArtifact.
It reuses the already-compiled instruction-index and PC certificates instead of
reducing the 5,439-byte `Submission.Bytes` append provider.
-/

namespace Challenge.Modexp.Submission.LocalPatch.PointerSub32.ReferenceArtifactFacts

open EvmSemantics EvmSemantics.EVM
open Challenge.Modexp.Submission.Proofs.Bytecode
open Challenge.Modexp.Submission.LocalPatch.PointerSub32

abbrev code : ByteArray := Challenge.Modexp.submissionBytecode

set_option maxRecDepth 40000 in
set_option maxHeartbeats 2000000 in
def oldCode : OldCode code where
  d0 := by
    simpa only [Artifact.instructionPC, ShiftPCs.pc2911] using
      (Artifact.decodeAt_op_index 2094 (.Dup ⟨0, by decide⟩)
        (by rfl) (by decide) (by trivial))
  d1 := by
    simpa only [Artifact.instructionPC, ShiftPCs.pc2912] using
      (Artifact.decodeAt_push_index 2095 ⟨1, by decide⟩
        (UInt256.ofNat 31) (by rfl) (by decide))
  d2 := by
    simpa only [Artifact.instructionPC, ShiftPCs.pc2913] using
      (Artifact.decodeAt_op_index 2096 .NOT
        (by rfl) (by decide) (by trivial))
  d3 := by
    simpa only [Artifact.instructionPC, ShiftPCs.pc2914] using
      (Artifact.decodeAt_op_index 2097 .ADD
        (by rfl) (by decide) (by trivial))
  d4 := by
    simpa only [Artifact.instructionPC, ShiftPCs.pc2915] using
      (Artifact.decodeAt_op_index 2098 (.Swap ⟨0, by decide⟩)
        (by rfl) (by decide) (by trivial))

end Challenge.Modexp.Submission.LocalPatch.PointerSub32.ReferenceArtifactFacts
