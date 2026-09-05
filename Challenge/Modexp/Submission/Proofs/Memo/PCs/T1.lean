import Challenge.Modexp.Submission.Proofs.Bytecode.MainDefs
set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000

namespace Challenge.Modexp.Submission.Proofs.Memo.PCs

open Challenge.Modexp.Submission.Proofs.Bytecode

@[simp] theorem pc1 (i : Nat) (hlo : 1012 ≤ i) (hhi : i ≤ 1046) :
    Artifact.submissionArtifact.instructionPC i =
      [1389,1390,1391,1392,1393,1394,1396,1397,1398,1399,1401,1403,1404,1405,1406,1408,1410,1411,1412,1413,1446,1448,1449,1450,1451,1452,1455,1456,1459,1460,1461,1463,1464,1465,1467][i - 1012]! := by
  interval_cases i <;> decide +kernel

end Challenge.Modexp.Submission.Proofs.Memo.PCs
