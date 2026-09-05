import Challenge.Modexp.Submission.Proofs.Memo.PCs

set_option warningAsError true
set_option maxRecDepth 50000
set_option maxHeartbeats 5000000
set_option linter.unusedSimpArgs false

namespace Challenge.Modexp.Submission.Proofs.Memo.V3.Paths

open EvmSemantics
open EvmSemantics.EVM
open Challenge.Modexp
open Challenge.Modexp.Submission.Proofs.Bytecode
open Challenge.Modexp.Submission.Proofs.Memo

def preludePath :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [
   Main.opAt 1087 (EvmSemantics.Operation.StackMemFlow (EvmSemantics.Operation.StackMemFlowOps.JUMPDEST)),
   Main.pushAt 1088 1 1,
   Main.pushAt 1089 0 0,
   Main.opAt 1090 (EvmSemantics.Operation.Env (EvmSemantics.Operation.EnvOps.CALLDATALOAD)),
   Main.opAt 1091 (EvmSemantics.Operation.CompBit (EvmSemantics.Operation.CompareBitwiseOps.XOR))
  ]

def chunk0Path :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [
   Main.pushAt 1092 1 1,
   Main.pushAt 1093 1 32,
   Main.opAt 1094 (EvmSemantics.Operation.Env (EvmSemantics.Operation.EnvOps.CALLDATALOAD)),
   Main.opAt 1095 (EvmSemantics.Operation.CompBit (EvmSemantics.Operation.CompareBitwiseOps.XOR)),
   Main.opAt 1096 (EvmSemantics.Operation.CompBit (EvmSemantics.Operation.CompareBitwiseOps.OR)),
   Main.opAt 1097 (EvmSemantics.Operation.StackMemFlow (EvmSemantics.Operation.StackMemFlowOps.JUMPDEST)),
   Main.pushAt 1098 1 64,
   Main.opAt 1099 (EvmSemantics.Operation.Env (EvmSemantics.Operation.EnvOps.CALLDATALOAD)),
   Main.opAt 1100 (EvmSemantics.Operation.StackMemFlow (EvmSemantics.Operation.StackMemFlowOps.JUMPDEST)),
   Main.opAt 1101 (EvmSemantics.Operation.CompBit (EvmSemantics.Operation.CompareBitwiseOps.OR)),
   Main.pushAt 1102 32 19009507569950637001986697810493060311787899246484784370430361119707296169984,
   Main.pushAt 1103 1 96,
   Main.opAt 1104 (EvmSemantics.Operation.Env (EvmSemantics.Operation.EnvOps.CALLDATALOAD)),
   Main.opAt 1105 (EvmSemantics.Operation.CompBit (EvmSemantics.Operation.CompareBitwiseOps.XOR)),
   Main.opAt 1106 (EvmSemantics.Operation.CompBit (EvmSemantics.Operation.CompareBitwiseOps.OR))
  ]

def branchPath :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [
   Main.opAt 1107 (EvmSemantics.Operation.CompBit (EvmSemantics.Operation.CompareBitwiseOps.ISZERO)),
   Main.pushAt 1108 2 1619,
   Main.opAt 1109 (EvmSemantics.Operation.StackMemFlow (EvmSemantics.Operation.StackMemFlowOps.JUMPI))
  ]

def branchPrefixPath :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [
   Main.opAt 1107 (EvmSemantics.Operation.CompBit (EvmSemantics.Operation.CompareBitwiseOps.ISZERO)),
   Main.pushAt 1108 2 1619
  ]

def fallbackPrefixPath :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [
   Main.pushAt 1110 2 1196
  ]

def returnPath :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [
   Main.opAt 1112 (EvmSemantics.Operation.StackMemFlow (EvmSemantics.Operation.StackMemFlowOps.JUMPDEST)),
   Main.pushAt 1113 0 0,
   Main.pushAt 1114 0 0,
   Main.opAt 1115 (EvmSemantics.Operation.System (EvmSemantics.Operation.SystemOps.RETURN))
  ]

end Challenge.Modexp.Submission.Proofs.Memo.V3.Paths
