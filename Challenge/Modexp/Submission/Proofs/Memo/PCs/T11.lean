import Challenge.Modexp.Submission.Proofs.Bytecode.MainDefs
set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000

namespace Challenge.Modexp.Submission.Proofs.Memo.PCs

open Challenge.Modexp.Submission.Proofs.Bytecode

@[simp] theorem pc11 (i : Nat) (hlo : 1362 ≤ i) (hhi : i ≤ 1396) :
    Artifact.submissionArtifact.instructionPC i =
      [2171,2172,2173,2174,2175,2176,2177,2179,2180,2181,2182,2184,2186,2187,2188,2189,2221,2223,2224,2225,2226,2257,2259,2260,2261,2262,2291,2293,2294,2295,2296,2299,2300,2333,2335][i - 1362]! := by
  interval_cases i <;> decide +kernel

end Challenge.Modexp.Submission.Proofs.Memo.PCs
