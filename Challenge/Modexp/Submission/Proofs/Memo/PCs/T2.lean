import Challenge.Modexp.Submission.Proofs.Bytecode.MainDefs
set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000

namespace Challenge.Modexp.Submission.Proofs.Memo.PCs

open Challenge.Modexp.Submission.Proofs.Bytecode

@[simp] theorem pc2 (i : Nat) (hlo : 1047 ≤ i) (hhi : i ≤ 1081) :
    Artifact.submissionArtifact.instructionPC i =
      [1422,1423,1424,1425,1426,1427,1428,1429,1430,1431,1432,1433,1434,1435,1436,1437,1438,1439,1440,1441,1443,1444,1445,1446,1448,1450,1451,1452,1453,1485,1487,1488,1489,1490,1493][i - 1047]! := by
  interval_cases i <;> decide +kernel

end Challenge.Modexp.Submission.Proofs.Memo.PCs
