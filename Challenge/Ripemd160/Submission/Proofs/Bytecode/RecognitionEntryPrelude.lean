import Challenge.Ripemd160.Submission.Proofs.Bytecode.Artifact
import Challenge.Ripemd160.ProofSupport.InitialState
import Challenge.EvmProof.Stepper
import Challenge.EvmProof.Word
import Challenge.EvmProof.Bytes

set_option warningAsError true

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.PatternedScan
open Challenge.Ripemd160 EvmSemantics EvmSemantics.EVM Challenge.EvmProof

abbrev Located := Stepper.Located Artifact.submissionArtifact .Osaka

def patternedEntry (input : ByteArray) : State :=
  { initialState submissionBytecode input 0 with pc := UInt256.ofNat 108 }

end Challenge.Ripemd160.Submission.Proofs.Bytecode.PatternedScan
