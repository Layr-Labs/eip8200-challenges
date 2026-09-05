import Challenge.Modexp.Submission.Proofs.Bytecode.MainDefs
set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000

namespace Challenge.Modexp.Submission.Proofs.Memo.PCs

open Challenge.Modexp.Submission.Proofs.Bytecode

@[simp] theorem pc12 (i : Nat) (hlo : 1397 ≤ i) (hhi : i ≤ 1431) :
    Artifact.submissionArtifact.instructionPC i =
      [2174,2175,2176,2177,2180,2181,2184,2185,2186,2219,2220,2221,2223,2224,2225,2226,2227,2228,2229,2230,2231,2232,2233,2234,2235,2236,2237,2238,2239,2240,2241,2243,2244,2245,2246][i - 1397]! := by
  interval_cases i <;> decide +kernel

end Challenge.Modexp.Submission.Proofs.Memo.PCs
