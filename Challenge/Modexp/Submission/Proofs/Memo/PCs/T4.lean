import Challenge.Modexp.Submission.Proofs.Bytecode.MainDefs
set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000

namespace Challenge.Modexp.Submission.Proofs.Memo.PCs

open Challenge.Modexp.Submission.Proofs.Bytecode

@[simp] theorem pc4 (i : Nat) (hlo : 1117 ≤ i) (hhi : i ≤ 1151) :
    Artifact.submissionArtifact.instructionPC i =
      [1624,1625,1626,1627,1628,1629,1630,1631,1632,1633,1634,1636,1637,1638,1639,1641,1643,1644,1645,1646,1648,1650,1651,1652,1653,1686,1688,1689,1690,1691,1692,1695,1696,1699,1700][i - 1117]! := by
  interval_cases i <;> decide +kernel

end Challenge.Modexp.Submission.Proofs.Memo.PCs
