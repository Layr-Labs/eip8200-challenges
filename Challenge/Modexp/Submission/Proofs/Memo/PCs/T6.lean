import Challenge.Modexp.Submission.Proofs.Bytecode.MainDefs
set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000

namespace Challenge.Modexp.Submission.Proofs.Memo.PCs

open Challenge.Modexp.Submission.Proofs.Bytecode

@[simp] theorem pc6 (i : Nat) (hlo : 1187 ≤ i) (hhi : i ≤ 1221) :
    Artifact.submissionArtifact.instructionPC i =
      [1809,1842,1844,1845,1846,1847,1848,1851,1852,1855,1856,1857,1859,1860,1861,1863,1864,1865,1866,1867,1868,1869,1870,1871,1872,1873,1874,1875,1876,1877,1878,1880,1882,1883,1884][i - 1187]! := by
  interval_cases i <;> decide +kernel

end Challenge.Modexp.Submission.Proofs.Memo.PCs
