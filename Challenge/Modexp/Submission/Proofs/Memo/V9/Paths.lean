import Challenge.Modexp.Submission.Proofs.Memo.PCs

set_option warningAsError true
set_option maxRecDepth 50000
set_option maxHeartbeats 5000000
set_option linter.unusedSimpArgs false

namespace Challenge.Modexp.Submission.Proofs.Memo.V9.Paths

open EvmSemantics
open EvmSemantics.EVM
open Challenge.Modexp
open Challenge.Modexp.Submission.Proofs.Bytecode
open Challenge.Modexp.Submission.Proofs.Memo

def preludePath :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [
   Main.pushAt 1484 1 32,
   Main.pushAt 1485 0 0,
   Main.opAt 1486 (EvmSemantics.Operation.Env (EvmSemantics.Operation.EnvOps.CALLDATALOAD)),
   Main.opAt 1487 (EvmSemantics.Operation.CompBit (EvmSemantics.Operation.CompareBitwiseOps.XOR))
  ]

def pretestPath :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [
   Main.opAt 1477 (EvmSemantics.Operation.StackMemFlow (EvmSemantics.Operation.StackMemFlowOps.JUMPDEST)),
   Main.pushAt 1478 1 96,
   Main.opAt 1479 (EvmSemantics.Operation.Env (EvmSemantics.Operation.EnvOps.CALLDATALOAD)),
   Main.pushAt 1480 32 73247641362558725300106169323372519318985509881989093824173738694050148637181,
   Main.opAt 1481 (EvmSemantics.Operation.CompBit (EvmSemantics.Operation.CompareBitwiseOps.EQ)),
   Main.pushAt 1482 2 2656
  ]

def pretestJumpPath :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [
   Main.opAt 1483 (EvmSemantics.Operation.StackMemFlow (EvmSemantics.Operation.StackMemFlowOps.JUMPI))
  ]

def chunk0Path :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [
   Main.pushAt 1488 1 32,
   Main.pushAt 1489 1 32,
   Main.opAt 1490 (EvmSemantics.Operation.Env (EvmSemantics.Operation.EnvOps.CALLDATALOAD)),
   Main.opAt 1491 (EvmSemantics.Operation.CompBit (EvmSemantics.Operation.CompareBitwiseOps.XOR)),
   Main.opAt 1492 (EvmSemantics.Operation.CompBit (EvmSemantics.Operation.CompareBitwiseOps.OR)),
   Main.pushAt 1493 1 32,
   Main.pushAt 1494 1 64,
   Main.opAt 1495 (EvmSemantics.Operation.Env (EvmSemantics.Operation.EnvOps.CALLDATALOAD)),
   Main.opAt 1496 (EvmSemantics.Operation.CompBit (EvmSemantics.Operation.CompareBitwiseOps.XOR)),
   Main.opAt 1497 (EvmSemantics.Operation.CompBit (EvmSemantics.Operation.CompareBitwiseOps.OR)),
   Main.pushAt 1498 32 5964364953636342908918930162962566239787286640968493902593843747347131818633,
   Main.pushAt 1499 1 96,
   Main.opAt 1500 (EvmSemantics.Operation.Env (EvmSemantics.Operation.EnvOps.CALLDATALOAD)),
   Main.opAt 1501 (EvmSemantics.Operation.CompBit (EvmSemantics.Operation.CompareBitwiseOps.XOR)),
   Main.opAt 1502 (EvmSemantics.Operation.CompBit (EvmSemantics.Operation.CompareBitwiseOps.OR)),
   Main.pushAt 1503 32 21888242871839275222246405745257275088696311157297823662689037894645226208581,
   Main.pushAt 1504 1 128,
   Main.opAt 1505 (EvmSemantics.Operation.Env (EvmSemantics.Operation.EnvOps.CALLDATALOAD)),
   Main.opAt 1506 (EvmSemantics.Operation.CompBit (EvmSemantics.Operation.CompareBitwiseOps.XOR)),
   Main.opAt 1507 (EvmSemantics.Operation.CompBit (EvmSemantics.Operation.CompareBitwiseOps.OR))
  ]

def chunk1Path :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [
   Main.pushAt 1508 32 21888242871839275222246405745257275088696311157297823662689037894645226208583,
   Main.pushAt 1509 1 160,
   Main.opAt 1510 (EvmSemantics.Operation.Env (EvmSemantics.Operation.EnvOps.CALLDATALOAD)),
   Main.opAt 1511 (EvmSemantics.Operation.CompBit (EvmSemantics.Operation.CompareBitwiseOps.XOR)),
   Main.opAt 1512 (EvmSemantics.Operation.CompBit (EvmSemantics.Operation.CompareBitwiseOps.OR))
  ]

def branchPath :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [
   Main.opAt 1513 (EvmSemantics.Operation.CompBit (EvmSemantics.Operation.CompareBitwiseOps.ISZERO)),
   Main.pushAt 1514 2 2616,
   Main.opAt 1515 (EvmSemantics.Operation.StackMemFlow (EvmSemantics.Operation.StackMemFlowOps.JUMPI))
  ]

def branchPrefixPath :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [
   Main.opAt 1513 (EvmSemantics.Operation.CompBit (EvmSemantics.Operation.CompareBitwiseOps.ISZERO)),
   Main.pushAt 1514 2 2616
  ]

def fallbackPrefixPath :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [
   Main.pushAt 1516 2 1196
  ]

def returnPath :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [
   Main.opAt 1518 (EvmSemantics.Operation.StackMemFlow (EvmSemantics.Operation.StackMemFlowOps.JUMPDEST)),
   Main.pushAt 1519 32 6720979588572738974916628410083100159223021409556719026881700545747062357561,
   Main.pushAt 1520 0 0,
   Main.opAt 1521 (EvmSemantics.Operation.StackMemFlow (EvmSemantics.Operation.StackMemFlowOps.MSTORE)),
   Main.pushAt 1522 1 32,
   Main.pushAt 1523 0 0,
   Main.opAt 1524 (EvmSemantics.Operation.System (EvmSemantics.Operation.SystemOps.RETURN))
  ]

end Challenge.Modexp.Submission.Proofs.Memo.V9.Paths
