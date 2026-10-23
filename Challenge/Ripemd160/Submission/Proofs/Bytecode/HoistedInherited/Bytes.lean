import Challenge.Ripemd160.Submission.Proofs.Bytecode.FoldedCandidateArtifact
set_option warningAsError true
set_option maxRecDepth 100000

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.HoistedInherited

/-- The exact byte array certified by `FoldedCandidateArtifact`. -/
abbrev submissionBytes : ByteArray := FoldedCandidateArtifact.code

@[simp] theorem referenceBytes_size : submissionBytes.size = 9742 :=
  FoldedCandidateArtifact.code_size

@[simp] theorem referenceBytes_get_zero : submissionBytes[0] = 0x64 := by
  rfl

@[simp] theorem referenceBytes_extract_entry :
    submissionBytes.extract 1 6 = ByteArray.mk #[0x10, 0x8c, 0x86, 0x82, 0x1c] := by
  rfl

end Challenge.Ripemd160.Submission.Proofs.Bytecode.HoistedInherited
