import Challenge.Modexp.Submission.Proofs.Bytecode.MonproKNArtifactPathsRow
import Challenge.Modexp.Submission.Proofs.Bytecode.MonproKNArtifactPathsL1
import Challenge.Modexp.Submission.Proofs.Bytecode.MonproKNArtifactPathsL2

set_option warningAsError true
set_option maxRecDepth 20000
set_option maxHeartbeats 2000000

namespace Challenge.Modexp.Submission.Proofs.Bytecode.MonproKNArtifactPaths

open EvmSemantics EvmSemantics.EVM
open Challenge.EvmProof WindowNineBinding

def rowPaths : MonproKNRowPaths.RowPaths Artifact.submissionArtifact .Osaka :=
  MonproKNArtifactPathsRow.rowPaths

def l1Paths : MonproKNLoopPaths.L1Paths Artifact.submissionArtifact .Osaka :=
  MonproKNArtifactPathsL1.l1Paths

def l2Paths : MonproKNLoopPaths.L2Paths Artifact.submissionArtifact .Osaka :=
  MonproKNArtifactPathsL2.l2Paths

#print axioms rowPaths
#print axioms l1Paths
#print axioms l2Paths

end Challenge.Modexp.Submission.Proofs.Bytecode.MonproKNArtifactPaths
