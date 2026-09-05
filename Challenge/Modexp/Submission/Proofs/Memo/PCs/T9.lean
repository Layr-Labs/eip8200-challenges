import Challenge.Modexp.Submission.Proofs.Bytecode.MainDefs
set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000

namespace Challenge.Modexp.Submission.Proofs.Memo.PCs

open Challenge.Modexp.Submission.Proofs.Bytecode

@[simp] theorem pc9 (i : Nat) (hlo : 1292 ≤ i) (hhi : i ≤ 1326) :
    Artifact.submissionArtifact.instructionPC i =
      [2104,2105,2106,2107,2108,2109,2110,2111,2112,2113,2114,2116,2117,2118,2119,2121,2123,2124,2125,2126,2128,2130,2131,2132,2133,2166,2168,2169,2170,2171,2204,2206,2207,2208,2209][i - 1292]! := by
  interval_cases i <;> decide +kernel

end Challenge.Modexp.Submission.Proofs.Memo.PCs
