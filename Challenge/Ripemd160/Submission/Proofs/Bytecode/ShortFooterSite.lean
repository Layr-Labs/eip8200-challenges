import Challenge.Ripemd160.Submission.Proofs.Bytecode.Artifact
import Challenge.Ripemd160.Submission.Proofs.Bytecode.ShortFooter

set_option warningAsError true
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.ShortFooterSite

open EvmSemantics EvmSemantics.EVM YulEvmCompiler Challenge.EvmProof

theorem guard_slice :
    (Artifact.submissionArtifact.instructions.drop 216).take 5 = ShortFooter.guard := by
  rfl

theorem body_slice :
    (Artifact.submissionArtifact.instructions.drop 221).take 18 = ShortFooter.body := by
  rfl

theorem guard_gas :
    (ShortFooter.guard.map (Meter.instrStaticCost .Osaka)).sum = 22 := by
  decide

theorem body_gas :
    (ShortFooter.body.map (Meter.instrStaticCost .Osaka)).sum = 53 := by
  decide

theorem return_instruction :
    Artifact.submissionArtifact.instructions[239]? = some (.op .JUMP) := by
  rfl

#print axioms guard_slice
#print axioms body_slice
#print axioms guard_gas
#print axioms body_gas
#print axioms return_instruction

end Challenge.Ripemd160.Submission.Proofs.Bytecode.ShortFooterSite
