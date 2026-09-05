import Challenge.Modexp.Submission.Proofs.Bytecode.MainDefs
set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000

namespace Challenge.Modexp.Submission.Proofs.Memo.PCs

open Challenge.Modexp.Submission.Proofs.Bytecode

@[simp] theorem pc5 (i : Nat) (hlo : 1152 ≤ i) (hhi : i ≤ 1186) :
    Artifact.submissionArtifact.instructionPC i =
      [1619,1621,1622,1623,1624,1625,1626,1627,1628,1629,1630,1631,1632,1633,1635,1636,1637,1638,1640,1642,1643,1644,1645,1646,1648,1649,1650,1651,1684,1686,1687,1688,1689,1690,1693][i - 1152]! := by
  interval_cases i <;> decide +kernel

end Challenge.Modexp.Submission.Proofs.Memo.PCs
