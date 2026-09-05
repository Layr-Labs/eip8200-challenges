import Challenge.Modexp.Submission.Proofs.Bytecode.MainDefs
set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000

namespace Challenge.Modexp.Submission.Proofs.Memo.PCs

open Challenge.Modexp.Submission.Proofs.Bytecode

@[simp] theorem pc11 (i : Nat) (hlo : 1362 ≤ i) (hhi : i ≤ 1396) :
    Artifact.submissionArtifact.instructionPC i =
      [2100,2101,2102,2103,2104,2105,2106,2107,2108,2109,2110,2111,2112,2113,2115,2116,2117,2118,2120,2122,2123,2124,2125,2127,2129,2130,2131,2132,2165,2167,2168,2169,2170,2171,2173][i - 1362]! := by
  interval_cases i <;> decide +kernel

end Challenge.Modexp.Submission.Proofs.Memo.PCs
