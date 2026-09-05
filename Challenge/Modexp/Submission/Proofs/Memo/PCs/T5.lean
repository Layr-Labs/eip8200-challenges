import Challenge.Modexp.Submission.Proofs.Bytecode.MainDefs
set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000

namespace Challenge.Modexp.Submission.Proofs.Memo.PCs

open Challenge.Modexp.Submission.Proofs.Bytecode

@[simp] theorem pc5 (i : Nat) (hlo : 1152 ≤ i) (hhi : i ≤ 1186) :
    Artifact.submissionArtifact.instructionPC i =
      [1701,1703,1705,1706,1707,1708,1709,1710,1711,1712,1713,1714,1716,1717,1718,1719,1721,1723,1724,1725,1726,1728,1730,1731,1732,1733,1766,1768,1769,1770,1771,1804,1806,1807,1808][i - 1152]! := by
  interval_cases i <;> decide +kernel

end Challenge.Modexp.Submission.Proofs.Memo.PCs
