import Challenge.Modexp.Submission.Proofs.Bytecode.MainDefs
set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000

namespace Challenge.Modexp.Submission.Proofs.Memo.PCs

open Challenge.Modexp.Submission.Proofs.Bytecode

@[simp] theorem pc4 (i : Nat) (hlo : 1117 ≤ i) (hhi : i ≤ 1151) :
    Artifact.submissionArtifact.instructionPC i =
      [1537,1539,1540,1542,1543,1546,1547,1549,1550,1551,1552,1553,1555,1556,1557,1558,1560,1562,1563,1564,1565,1598,1600,1601,1602,1603,1604,1607,1608,1611,1612,1613,1615,1616,1617][i - 1117]! := by
  interval_cases i <;> decide +kernel

end Challenge.Modexp.Submission.Proofs.Memo.PCs
