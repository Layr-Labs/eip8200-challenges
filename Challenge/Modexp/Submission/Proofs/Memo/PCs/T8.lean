import Challenge.Modexp.Submission.Proofs.Bytecode.MainDefs
set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000

namespace Challenge.Modexp.Submission.Proofs.Memo.PCs

open Challenge.Modexp.Submission.Proofs.Bytecode

@[simp] theorem pc8 (i : Nat) (hlo : 1257 ≤ i) (hhi : i ≤ 1291) :
    Artifact.submissionArtifact.instructionPC i =
      [1810,1811,1812,1813,1814,1815,1816,1817,1818,1819,1820,1821,1822,1823,1824,1825,1827,1828,1829,1830,1832,1834,1835,1836,1837,1839,1841,1842,1843,1844,1877,1879,1880,1881,1882][i - 1257]! := by
  interval_cases i <;> decide +kernel

end Challenge.Modexp.Submission.Proofs.Memo.PCs
