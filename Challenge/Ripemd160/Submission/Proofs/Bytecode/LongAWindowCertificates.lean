import Challenge.Ripemd160.Submission.Proofs.Bytecode.DataStepper
import Challenge.Ripemd160.Submission.Proofs.Bytecode.Artifact
set_option warningAsError true
set_option maxRecDepth 10000
namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.LongAWindowCertificates
open EvmSemantics EvmSemantics.EVM YulEvmCompiler Challenge.EvmProof
-- Artifact-bound starting point for the outside-compressor recognizer search.
theorem window : (Artifact.submissionArtifact.instructions.drop 26).take 26 =
  [Artifact.op 0x5b, .push 1 32, Artifact.op 0x82, Artifact.op 0x03,
   Artifact.op 0x35, Artifact.op 0x83, Artifact.op 0x18, Artifact.op 0x17,
   .push 1 64, Artifact.op 0x82, Artifact.op 0x03, Artifact.op 0x35,
   Artifact.op 0x83, Artifact.op 0x18, Artifact.op 0x17,
   .push 1 96, Artifact.op 0x82, Artifact.op 0x03, Artifact.op 0x91,
   Artifact.op 0x35, Artifact.op 0x83, Artifact.op 0x18, Artifact.op 0x17,
   Artifact.op 0x81, .push 1 44, Artifact.op 0x57] := by rfl
end Challenge.Ripemd160.Submission.Proofs.Bytecode.LongAWindowCertificates
