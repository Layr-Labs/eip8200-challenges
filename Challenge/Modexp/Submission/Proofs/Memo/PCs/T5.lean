import Challenge.Modexp.Submission.Proofs.Bytecode.MainDefs
set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000

namespace Challenge.Modexp.Submission.Proofs.Memo.PCs

open Challenge.Modexp.Submission.Proofs.Bytecode

@[simp] theorem pc5 (i : Nat) (hlo : 1152 ≤ i) (hhi : i ≤ 1186) :
    Artifact.submissionArtifact.instructionPC i =
      [1613,1644,1646,1647,1648,1649,1652,1653,1654,1655,1656,1657,1658,1659,1660,1661,1662,1663,1664,1665,1667,1668,1669,1670,1672,1674,1675,1676,1677,1709,1711,1712,1713,1714,1717][i - 1152]! := by
  interval_cases i <;> decide +kernel

end Challenge.Modexp.Submission.Proofs.Memo.PCs
