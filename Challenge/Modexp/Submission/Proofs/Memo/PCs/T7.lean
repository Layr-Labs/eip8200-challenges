import Challenge.Modexp.Submission.Proofs.Bytecode.MainDefs
set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000

namespace Challenge.Modexp.Submission.Proofs.Memo.PCs

open Challenge.Modexp.Submission.Proofs.Bytecode

@[simp] theorem pc7 (i : Nat) (hlo : 1222 ≤ i) (hhi : i ≤ 1256) :
    Artifact.submissionArtifact.instructionPC i =
      [1732,1733,1734,1736,1738,1739,1740,1741,1743,1745,1746,1747,1748,1781,1783,1784,1785,1786,1787,1790,1791,1794,1795,1796,1798,1800,1801,1802,1803,1804,1805,1806,1807,1808,1809][i - 1222]! := by
  interval_cases i <;> decide +kernel

end Challenge.Modexp.Submission.Proofs.Memo.PCs
