import Challenge.Modexp.Submission.Proofs.Bytecode.MainDefs
set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000

namespace Challenge.Modexp.Submission.Proofs.Memo.PCs

open Challenge.Modexp.Submission.Proofs.Bytecode

@[simp] theorem pc3 (i : Nat) (hlo : 1082 ≤ i) (hhi : i ≤ 1116) :
    Artifact.submissionArtifact.instructionPC i =
      [1494,1496,1497,1498,1500,1502,1503,1504,1505,1507,1508,1510,1511,1514,1515,1517,1518,1519,1520,1521,1523,1524,1525,1526,1558,1560,1561,1562,1563,1566,1567,1569,1570,1571,1573][i - 1082]! := by
  interval_cases i <;> decide +kernel

end Challenge.Modexp.Submission.Proofs.Memo.PCs
