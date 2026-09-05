import Challenge.Modexp.Submission.Proofs.Bytecode.MainDefs
set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000

namespace Challenge.Modexp.Submission.Proofs.Memo.PCs

open Challenge.Modexp.Submission.Proofs.Bytecode

@[simp] theorem pc10 (i : Nat) (hlo : 1327 ≤ i) (hhi : i ≤ 1361) :
    Artifact.submissionArtifact.instructionPC i =
      [2240,2242,2243,2244,2245,2246,2249,2250,2253,2254,2255,2288,2290,2291,2293,2295,2296,2297,2298,2299,2300,2301,2302,2303,2304,2305,2306,2308,2309,2310,2311,2313,2315,2316,2317][i - 1327]! := by
  interval_cases i <;> decide +kernel

end Challenge.Modexp.Submission.Proofs.Memo.PCs
