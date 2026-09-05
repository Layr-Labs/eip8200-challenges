import Challenge.Modexp.Submission.Proofs.Bytecode.MainDefs
set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000

namespace Challenge.Modexp.Submission.Proofs.Memo.PCs

open Challenge.Modexp.Submission.Proofs.Bytecode

@[simp] theorem pc3 (i : Nat) (hlo : 1082 ≤ i) (hhi : i ≤ 1116) :
    Artifact.submissionArtifact.instructionPC i =
      [1495,1496,1497,1498,1499,1502,1503,1506,1507,1508,1510,1511,1512,1514,1516,1517,1518,1519,1520,1521,1522,1523,1524,1525,1526,1527,1528,1529,1530,1531,1532,1533,1534,1535,1536][i - 1082]! := by
  interval_cases i <;> decide +kernel

end Challenge.Modexp.Submission.Proofs.Memo.PCs
