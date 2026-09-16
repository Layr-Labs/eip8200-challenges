import Challenge.Modexp.Submission.Proofs.Fast.TnR4Reduction
import Challenge.Modexp.Submission.Proofs.Fast.TnR8Reduction
import Challenge.Modexp.Submission.Proofs.Fast.TnM128R4Reduction
import Challenge.Modexp.Submission.Proofs.Fast.TnM128R8Reduction
import Challenge.Modexp.Submission.Proofs.Fast.TnM128R8FirstRow
import Challenge.Modexp.Submission.Proofs.Fast.TnMod128Invariant

set_option warningAsError true

/-!
Research component audit, September 16, 2026.

TnCandidateArtifact: 5310 bytes, SHA256 17c5f4a03d36... (carry cache only).
TnM128CandidateArtifact: 5314 bytes, SHA256 af761a7b3051... (preferred candidate).

These declarations certify assembly, block bindings, and conditional execution
of specific kernel regions. They do NOT establish Challenge.Modexp.Correct for
either complete candidate. The main submission bytecode and Solution still
refer to the original promoted baseline.
-/

open Challenge.Modexp.Submission.Proofs.Fast

#print axioms TnM128CandidateArtifact.assemble_submissionInstructions
#print axioms TnM128CandidateArtifact.allWellFormed
#print axioms TnM128CandidateBlocks.l2Eight
#print axioms TnM128CandidateBlocks.l2Four
#print axioms TnM128CandidateBlocks.cachedCell
#print axioms TnM128CandidateBlocks.middle
#print axioms TnM128CandidateBlocks.middleCopy
#print axioms TnM128CandidateBlocks.tail
#print axioms TnM128CandidateBlocks.flush
#print axioms TnM128CandidateBlocks.afterSquareReset
#print axioms TnM128CandidateBlocks.againReset
#print axioms TnM128R4Reduction.reduction_steps
#print axioms TnM128R8Reduction.reduction_steps
#print axioms TnM128R8FirstRow.run_program
#print axioms TnM128R8FirstRow.block
#print axioms TnMod128Invariant.rows_read
#print axioms TnMod128Invariant.squareRows_read
#print axioms TnMod128Invariant.firstProduct_read
#print axioms TnCacheRowModel.rows_lift
#print axioms TnCacheSquareModel.squareRows_lift
