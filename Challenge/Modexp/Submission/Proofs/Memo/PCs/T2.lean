import Challenge.Modexp.Submission.Proofs.Bytecode.MainDefs
set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000

namespace Challenge.Modexp.Submission.Proofs.Memo.PCs

open Challenge.Modexp.Submission.Proofs.Bytecode

@[simp] theorem pc2 (i : Nat) (hlo : 1047 ≤ i) (hhi : i ≤ 1081) :
    Artifact.submissionArtifact.instructionPC i =
      [1469,1470,1471,1472,1473,1474,1476,1477,1478,1479,1480,1482,1483,1484,1485,1487,1489,1490,1491,1492,1525,1527,1528,1529,1530,1531,1534,1535,1538,1539,1540,1542,1543,1544,1546][i - 1047]! := by
  interval_cases i <;> decide +kernel

end Challenge.Modexp.Submission.Proofs.Memo.PCs
