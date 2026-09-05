import Challenge.Modexp.Submission.Proofs.Bytecode.MainDefs
set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000

namespace Challenge.Modexp.Submission.Proofs.Memo.PCs

open Challenge.Modexp.Submission.Proofs.Bytecode

@[simp] theorem pc6 (i : Nat) (hlo : 1187 ≤ i) (hhi : i ≤ 1221) :
    Artifact.submissionArtifact.instructionPC i =
      [1718,1720,1722,1723,1724,1725,1726,1727,1728,1729,1731,1732,1733,1734,1736,1738,1739,1740,1741,1773,1775,1776,1777,1778,1811,1813,1814,1815,1816,1849,1851,1852,1853,1854,1857][i - 1187]! := by
  interval_cases i <;> decide +kernel

end Challenge.Modexp.Submission.Proofs.Memo.PCs
