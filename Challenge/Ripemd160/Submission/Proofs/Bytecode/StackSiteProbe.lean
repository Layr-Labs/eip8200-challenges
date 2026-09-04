import Challenge.Ripemd160.Submission.Proofs.Bytecode.Artifact
import Challenge.Ripemd160.Submission.Proofs.Bytecode.StackRoundTemplate

set_option warningAsError true
set_option maxRecDepth 50000
set_option maxHeartbeats 200000

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.StackSiteProbe
open EvmSemantics EvmSemantics.EVM StackRoundTemplate

theorem firstSlice :
    (Artifact.submissionArtifact.instructions.drop 996).take 42 =
      f0Template (UInt256.ofNat (672 + 32 * Crypto.Ripemd160.r[0]!))
        Crypto.Ripemd160.s[0]! := by rfl

theorem lastLeftSlice :
    (Artifact.submissionArtifact.instructions.drop 4597).take 47 =
      f4Template (UInt256.ofNat (672 + 32 * Crypto.Ripemd160.r[79]!))
        Crypto.Ripemd160.s[79]! (UInt256.ofNat 0xa953fd4e) := by rfl

theorem lastRightSlice :
    (Artifact.submissionArtifact.instructions.drop 8260).take 42 =
      f0Template (UInt256.ofNat (672 + 32 * Crypto.Ripemd160.rP[79]!))
        Crypto.Ripemd160.sP[79]! := by rfl

theorem firstPC : Artifact.submissionArtifact.instructionPC 996 = 0x740 := by decide

end Challenge.Ripemd160.Submission.Proofs.Bytecode.StackSiteProbe
