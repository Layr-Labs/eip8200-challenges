import Challenge.Modexp.Submission.Proofs.CRT.CRTColumnExecution0
import Challenge.Modexp.Submission.Proofs.CRT.CRTColumnExecution1
import Challenge.Modexp.Submission.Proofs.CRT.CRTColumnExecution2
import Challenge.Modexp.Submission.Proofs.CRT.CRTColumnExecution3
import Challenge.Modexp.Submission.Proofs.CRT.CRTColumnExecution4
import Challenge.Modexp.Submission.Proofs.CRT.CRTColumnExecution5
import Challenge.Modexp.Submission.Proofs.CRT.CRTColumnExecution6
import Challenge.Modexp.Submission.Proofs.CRT.CRTColumnExecution7
import Challenge.Modexp.Submission.Proofs.CRT.CRTColumnExecution8
import Challenge.Modexp.Submission.Proofs.CRT.CRTColumnExecution9
import Challenge.Modexp.Submission.Proofs.CRT.CRTColumnExecution10
import Challenge.Modexp.Submission.Proofs.CRT.CRTColumnExecution11
import Challenge.Modexp.Submission.Proofs.CRT.CRTColumnExecution12
import Challenge.Modexp.Submission.Proofs.CRT.CRTColumnExecution13
import Challenge.Modexp.Submission.Proofs.CRT.CRTColumnExecution14
import Challenge.Modexp.Submission.Proofs.CRT.CRTColumnExecution15
import Challenge.Modexp.Submission.Proofs.CRT.CRTColumnExecution16
import Challenge.Modexp.Submission.Proofs.CRT.CRTMaskElision
import Challenge.Modexp.Submission.Proofs.CRT.CRTMemoryBounds
import Challenge.Modexp.Submission.Proofs.Bytecode.WindowNibbleDefs
set_option warningAsError true
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option maxRecDepth 40000
set_option maxHeartbeats 8000000
namespace HistoricalSearch.GeneratedColumns
open EvmSemantics EvmSemantics.EVM YulEvmCompiler
open HistoricalSearch.LifetimeCache
open Challenge.Modexp.Submission.Proofs.Bytecode.WindowNibbleKernel

structure ColumnWords where
  high : UInt256
  low : UInt256
  carry : UInt256
  cancel : UInt256
  digit : UInt256

def col0Words (carry P mask minv : UInt256) (a n q : Nat → UInt256) : ColumnWords :=
  let v0 : UInt256 := a 0
  let v1 : UInt256 := v0 * v0
  let v2 : UInt256 := a 0
  let v3 : UInt256 := UInt256.mulMod v2 v2 P
  let v4 : UInt256 := UInt256.land mask v1
  let v5 : UInt256 := minv * v4
  let v6 : UInt256 := UInt256.land mask v5
  let v8 : UInt256 := (n 0) * v6
  let v9 : UInt256 := v8 + v1
  let v10 : UInt256 := UInt256.mulMod (n 0) v6 P
  let v11 : UInt256 := v10 + v3
  let v19 : UInt256 := UInt256.mulMod v11 (UInt256.ofNat 128) P
  {high := v11, low := v9, carry := v19, cancel := v6, digit := UInt256.ofNat 0}

def col0High (carry P mask minv : UInt256) (a n q : Nat → UInt256) : UInt256 := (col0Words carry P mask minv a n q).high

def col0Low (carry P mask minv : UInt256) (a n q : Nat → UInt256) : UInt256 := (col0Words carry P mask minv a n q).low

def col0Carry (carry P mask minv : UInt256) (a n q : Nat → UInt256) : UInt256 := (col0Words carry P mask minv a n q).carry

def col0Cancel (carry P mask minv : UInt256) (a n q : Nat → UInt256) : UInt256 := (col0Words carry P mask minv a n q).cancel

def col0Digit (carry P mask minv : UInt256) (a n q : Nat → UInt256) : UInt256 := (col0Words carry P mask minv a n q).digit

theorem col0_stack (s : State) (P n0 n1 n2 n3 n4 n5 n6 n7 n8 mask minv : UInt256) (rest : List UInt256) :
    (col0Model s P n0 n1 n2 n3 n4 n5 n6 n7 n8 mask minv rest).stack =
      (col0Words (UInt256.ofNat 0) P mask minv (fun i => MachineState.readWord s.memory (768+32*i)) (fun i => match i with | 0 => n0 | 1 => n1 | 2 => n2 | 3 => n3 | 4 => n4 | 5 => n5 | 6 => n6 | 7 => n7 | _ => n8) (fun i => MachineState.readWord s.memory (1056+32*i))).carry :: P :: n0 :: n1 :: n2 :: n3 :: n4 :: n5 :: n6 :: n7 :: n8 :: mask :: minv :: rest := by rfl

#print axioms col0_stack

def col1Words (carry P mask minv : UInt256) (a n q : Nat → UInt256) : ColumnWords :=
  let v0 : UInt256 := a 1
  let v1 : UInt256 := a 0
  let v2 : UInt256 := UInt256.mulMod v0 v1 P
  let v3 : UInt256 := v0 * v1
  let v4 : UInt256 := v3 + v3
  let v5 : UInt256 := v2 + v2
  let v6 : UInt256 := carry + v5
  let v7 : UInt256 := carry + v4
  let v8 : UInt256 := q 0
  let v9 : UInt256 := UInt256.mulMod (n 1) v8 P
  let v10 : UInt256 := v9 + v6
  let v11 : UInt256 := q 0
  let v12 : UInt256 := (n 1) * v11
  let v13 : UInt256 := v12 + v7
  let v14 : UInt256 := UInt256.land mask v13
  let v15 : UInt256 := minv * v14
  let v16 : UInt256 := UInt256.land mask v15
  let v18 : UInt256 := (n 0) * v16
  let v19 : UInt256 := v18 + v13
  let v20 : UInt256 := UInt256.mulMod (n 0) v16 P
  let v21 : UInt256 := v20 + v10
  let v29 : UInt256 := UInt256.mulMod v21 (UInt256.ofNat 128) P
  {high := v21, low := v19, carry := v29, cancel := v16, digit := UInt256.ofNat 0}

def col1High (carry P mask minv : UInt256) (a n q : Nat → UInt256) : UInt256 := (col1Words carry P mask minv a n q).high

def col1Low (carry P mask minv : UInt256) (a n q : Nat → UInt256) : UInt256 := (col1Words carry P mask minv a n q).low

def col1Carry (carry P mask minv : UInt256) (a n q : Nat → UInt256) : UInt256 := (col1Words carry P mask minv a n q).carry

def col1Cancel (carry P mask minv : UInt256) (a n q : Nat → UInt256) : UInt256 := (col1Words carry P mask minv a n q).cancel

def col1Digit (carry P mask minv : UInt256) (a n q : Nat → UInt256) : UInt256 := (col1Words carry P mask minv a n q).digit

theorem col1_stack (s : State) (carry P n0 n1 n2 n3 n4 n5 n6 n7 n8 mask minv : UInt256) (rest : List UInt256) :
    (col1Model s carry P n0 n1 n2 n3 n4 n5 n6 n7 n8 mask minv rest).stack =
      (col1Words carry P mask minv (fun i => MachineState.readWord s.memory (768+32*i)) (fun i => match i with | 0 => n0 | 1 => n1 | 2 => n2 | 3 => n3 | 4 => n4 | 5 => n5 | 6 => n6 | 7 => n7 | _ => n8) (fun i => MachineState.readWord s.memory (1056+32*i))).carry :: P :: n0 :: n1 :: n2 :: n3 :: n4 :: n5 :: n6 :: n7 :: n8 :: mask :: minv :: rest := by rfl

#print axioms col1_stack

def col2Words (carry P mask minv : UInt256) (a n q : Nat → UInt256) : ColumnWords :=
  let v0 : UInt256 := a 2
  let v1 : UInt256 := a 0
  let v2 : UInt256 := UInt256.mulMod v0 v1 P
  let v3 : UInt256 := v0 * v1
  let v4 : UInt256 := v3 + v3
  let v5 : UInt256 := v2 + v2
  let v6 : UInt256 := carry + v5
  let v7 : UInt256 := carry + v4
  let v8 : UInt256 := a 1
  let v9 : UInt256 := UInt256.mulMod v8 v8 P
  let v10 : UInt256 := v9 + v6
  let v11 : UInt256 := q 0
  let v12 : UInt256 := UInt256.mulMod (n 2) v11 P
  let v13 : UInt256 := v12 + v10
  let v14 : UInt256 := q 1
  let v15 : UInt256 := UInt256.mulMod (n 1) v14 P
  let v16 : UInt256 := v15 + v13
  let v17 : UInt256 := a 1
  let v18 : UInt256 := v17 * v17
  let v19 : UInt256 := v18 + v7
  let v20 : UInt256 := q 0
  let v21 : UInt256 := (n 2) * v20
  let v22 : UInt256 := v21 + v19
  let v23 : UInt256 := q 1
  let v24 : UInt256 := (n 1) * v23
  let v25 : UInt256 := v24 + v22
  let v26 : UInt256 := UInt256.land mask v25
  let v27 : UInt256 := minv * v26
  let v28 : UInt256 := UInt256.land mask v27
  let v30 : UInt256 := (n 0) * v28
  let v31 : UInt256 := v30 + v25
  let v32 : UInt256 := UInt256.mulMod (n 0) v28 P
  let v33 : UInt256 := v32 + v16
  let v41 : UInt256 := UInt256.mulMod v33 (UInt256.ofNat 128) P
  {high := v33, low := v31, carry := v41, cancel := v28, digit := UInt256.ofNat 0}

def col2High (carry P mask minv : UInt256) (a n q : Nat → UInt256) : UInt256 := (col2Words carry P mask minv a n q).high

def col2Low (carry P mask minv : UInt256) (a n q : Nat → UInt256) : UInt256 := (col2Words carry P mask minv a n q).low

def col2Carry (carry P mask minv : UInt256) (a n q : Nat → UInt256) : UInt256 := (col2Words carry P mask minv a n q).carry

def col2Cancel (carry P mask minv : UInt256) (a n q : Nat → UInt256) : UInt256 := (col2Words carry P mask minv a n q).cancel

def col2Digit (carry P mask minv : UInt256) (a n q : Nat → UInt256) : UInt256 := (col2Words carry P mask minv a n q).digit

theorem col2_stack (s : State) (carry P n0 n1 n2 n3 n4 n5 n6 n7 n8 mask minv : UInt256) (rest : List UInt256) :
    (col2Model s carry P n0 n1 n2 n3 n4 n5 n6 n7 n8 mask minv rest).stack =
      (col2Words carry P mask minv (fun i => MachineState.readWord s.memory (768+32*i)) (fun i => match i with | 0 => n0 | 1 => n1 | 2 => n2 | 3 => n3 | 4 => n4 | 5 => n5 | 6 => n6 | 7 => n7 | _ => n8) (fun i => MachineState.readWord s.memory (1056+32*i))).carry :: P :: n0 :: n1 :: n2 :: n3 :: n4 :: n5 :: n6 :: n7 :: n8 :: mask :: minv :: rest := by rfl

#print axioms col2_stack

def col3Words (carry P mask minv : UInt256) (a n q : Nat → UInt256) : ColumnWords :=
  let v0 : UInt256 := a 3
  let v1 : UInt256 := a 0
  let v2 : UInt256 := UInt256.mulMod v0 v1 P
  let v3 : UInt256 := v0 * v1
  let v4 : UInt256 := a 2
  let v5 : UInt256 := a 1
  let v6 : UInt256 := UInt256.mulMod v5 v4 P
  let v7 : UInt256 := v6 + v2
  let v8 : UInt256 := a 2
  let v9 : UInt256 := a 1
  let v10 : UInt256 := v9 * v8
  let v11 : UInt256 := v10 + v3
  let v12 : UInt256 := v11 + v11
  let v13 : UInt256 := v7 + v7
  let v14 : UInt256 := carry + v13
  let v15 : UInt256 := carry + v12
  let v16 : UInt256 := q 0
  let v17 : UInt256 := UInt256.mulMod (n 3) v16 P
  let v18 : UInt256 := v17 + v14
  let v19 : UInt256 := q 1
  let v20 : UInt256 := UInt256.mulMod (n 2) v19 P
  let v21 : UInt256 := v20 + v18
  let v22 : UInt256 := q 2
  let v23 : UInt256 := UInt256.mulMod (n 1) v22 P
  let v24 : UInt256 := v23 + v21
  let v25 : UInt256 := q 0
  let v26 : UInt256 := (n 3) * v25
  let v27 : UInt256 := v26 + v15
  let v28 : UInt256 := q 1
  let v29 : UInt256 := (n 2) * v28
  let v30 : UInt256 := v29 + v27
  let v31 : UInt256 := q 2
  let v32 : UInt256 := (n 1) * v31
  let v33 : UInt256 := v32 + v30
  let v34 : UInt256 := UInt256.land mask v33
  let v35 : UInt256 := minv * v34
  let v36 : UInt256 := UInt256.land mask v35
  let v38 : UInt256 := (n 0) * v36
  let v39 : UInt256 := v38 + v33
  let v40 : UInt256 := UInt256.mulMod (n 0) v36 P
  let v41 : UInt256 := v40 + v24
  let v49 : UInt256 := UInt256.mulMod v41 (UInt256.ofNat 128) P
  {high := v41, low := v39, carry := v49, cancel := v36, digit := UInt256.ofNat 0}

def col3High (carry P mask minv : UInt256) (a n q : Nat → UInt256) : UInt256 := (col3Words carry P mask minv a n q).high

def col3Low (carry P mask minv : UInt256) (a n q : Nat → UInt256) : UInt256 := (col3Words carry P mask minv a n q).low

def col3Carry (carry P mask minv : UInt256) (a n q : Nat → UInt256) : UInt256 := (col3Words carry P mask minv a n q).carry

def col3Cancel (carry P mask minv : UInt256) (a n q : Nat → UInt256) : UInt256 := (col3Words carry P mask minv a n q).cancel

def col3Digit (carry P mask minv : UInt256) (a n q : Nat → UInt256) : UInt256 := (col3Words carry P mask minv a n q).digit

theorem col3_stack (s : State) (carry P n0 n1 n2 n3 n4 n5 n6 n7 n8 mask minv : UInt256) (rest : List UInt256) :
    (col3Model s carry P n0 n1 n2 n3 n4 n5 n6 n7 n8 mask minv rest).stack =
      (col3Words carry P mask minv (fun i => MachineState.readWord s.memory (768+32*i)) (fun i => match i with | 0 => n0 | 1 => n1 | 2 => n2 | 3 => n3 | 4 => n4 | 5 => n5 | 6 => n6 | 7 => n7 | _ => n8) (fun i => MachineState.readWord s.memory (1056+32*i))).carry :: P :: n0 :: n1 :: n2 :: n3 :: n4 :: n5 :: n6 :: n7 :: n8 :: mask :: minv :: rest := by rfl

#print axioms col3_stack

def col4Words (carry P mask minv : UInt256) (a n q : Nat → UInt256) : ColumnWords :=
  let v0 : UInt256 := a 4
  let v1 : UInt256 := a 0
  let v2 : UInt256 := UInt256.mulMod v0 v1 P
  let v3 : UInt256 := v0 * v1
  let v4 : UInt256 := a 3
  let v5 : UInt256 := a 1
  let v6 : UInt256 := UInt256.mulMod v5 v4 P
  let v7 : UInt256 := v6 + v2
  let v8 : UInt256 := a 3
  let v9 : UInt256 := a 1
  let v10 : UInt256 := v9 * v8
  let v11 : UInt256 := v10 + v3
  let v12 : UInt256 := v11 + v11
  let v13 : UInt256 := v7 + v7
  let v14 : UInt256 := carry + v13
  let v15 : UInt256 := carry + v12
  let v16 : UInt256 := a 2
  let v17 : UInt256 := UInt256.mulMod v16 v16 P
  let v18 : UInt256 := v17 + v14
  let v19 : UInt256 := q 0
  let v20 : UInt256 := UInt256.mulMod (n 4) v19 P
  let v21 : UInt256 := v20 + v18
  let v22 : UInt256 := q 1
  let v23 : UInt256 := UInt256.mulMod (n 3) v22 P
  let v24 : UInt256 := v23 + v21
  let v25 : UInt256 := q 2
  let v26 : UInt256 := UInt256.mulMod (n 2) v25 P
  let v27 : UInt256 := v26 + v24
  let v28 : UInt256 := q 3
  let v29 : UInt256 := UInt256.mulMod (n 1) v28 P
  let v30 : UInt256 := v29 + v27
  let v31 : UInt256 := a 2
  let v32 : UInt256 := v31 * v31
  let v33 : UInt256 := v32 + v15
  let v34 : UInt256 := q 0
  let v35 : UInt256 := (n 4) * v34
  let v36 : UInt256 := v35 + v33
  let v37 : UInt256 := q 1
  let v38 : UInt256 := (n 3) * v37
  let v39 : UInt256 := v38 + v36
  let v40 : UInt256 := q 2
  let v41 : UInt256 := (n 2) * v40
  let v42 : UInt256 := v41 + v39
  let v43 : UInt256 := q 3
  let v44 : UInt256 := (n 1) * v43
  let v45 : UInt256 := v44 + v42
  let v46 : UInt256 := UInt256.land mask v45
  let v47 : UInt256 := minv * v46
  let v48 : UInt256 := UInt256.land mask v47
  let v50 : UInt256 := (n 0) * v48
  let v51 : UInt256 := v50 + v45
  let v52 : UInt256 := UInt256.mulMod (n 0) v48 P
  let v53 : UInt256 := v52 + v30
  let v61 : UInt256 := UInt256.mulMod v53 (UInt256.ofNat 128) P
  {high := v53, low := v51, carry := v61, cancel := v48, digit := UInt256.ofNat 0}

def col4High (carry P mask minv : UInt256) (a n q : Nat → UInt256) : UInt256 := (col4Words carry P mask minv a n q).high

def col4Low (carry P mask minv : UInt256) (a n q : Nat → UInt256) : UInt256 := (col4Words carry P mask minv a n q).low

def col4Carry (carry P mask minv : UInt256) (a n q : Nat → UInt256) : UInt256 := (col4Words carry P mask minv a n q).carry

def col4Cancel (carry P mask minv : UInt256) (a n q : Nat → UInt256) : UInt256 := (col4Words carry P mask minv a n q).cancel

def col4Digit (carry P mask minv : UInt256) (a n q : Nat → UInt256) : UInt256 := (col4Words carry P mask minv a n q).digit

theorem col4_stack (s : State) (carry P n0 n1 n2 n3 n4 n5 n6 n7 n8 mask minv : UInt256) (rest : List UInt256) :
    (col4Model s carry P n0 n1 n2 n3 n4 n5 n6 n7 n8 mask minv rest).stack =
      (col4Words carry P mask minv (fun i => MachineState.readWord s.memory (768+32*i)) (fun i => match i with | 0 => n0 | 1 => n1 | 2 => n2 | 3 => n3 | 4 => n4 | 5 => n5 | 6 => n6 | 7 => n7 | _ => n8) (fun i => MachineState.readWord s.memory (1056+32*i))).carry :: P :: n0 :: n1 :: n2 :: n3 :: n4 :: n5 :: n6 :: n7 :: n8 :: mask :: minv :: rest := by rfl

#print axioms col4_stack

def col5Words (carry P mask minv : UInt256) (a n q : Nat → UInt256) : ColumnWords :=
  let v0 : UInt256 := a 5
  let v1 : UInt256 := a 0
  let v2 : UInt256 := UInt256.mulMod v0 v1 P
  let v3 : UInt256 := v0 * v1
  let v4 : UInt256 := a 4
  let v5 : UInt256 := a 1
  let v6 : UInt256 := UInt256.mulMod v5 v4 P
  let v7 : UInt256 := v6 + v2
  let v8 : UInt256 := a 3
  let v9 : UInt256 := a 2
  let v10 : UInt256 := UInt256.mulMod v9 v8 P
  let v11 : UInt256 := v10 + v7
  let v12 : UInt256 := a 4
  let v13 : UInt256 := a 1
  let v14 : UInt256 := v13 * v12
  let v15 : UInt256 := v14 + v3
  let v16 : UInt256 := a 3
  let v17 : UInt256 := a 2
  let v18 : UInt256 := v17 * v16
  let v19 : UInt256 := v18 + v15
  let v20 : UInt256 := v19 + v19
  let v21 : UInt256 := v11 + v11
  let v22 : UInt256 := carry + v21
  let v23 : UInt256 := carry + v20
  let v24 : UInt256 := q 0
  let v25 : UInt256 := UInt256.mulMod (n 5) v24 P
  let v26 : UInt256 := v25 + v22
  let v27 : UInt256 := q 1
  let v28 : UInt256 := UInt256.mulMod (n 4) v27 P
  let v29 : UInt256 := v28 + v26
  let v30 : UInt256 := q 2
  let v31 : UInt256 := UInt256.mulMod (n 3) v30 P
  let v32 : UInt256 := v31 + v29
  let v33 : UInt256 := q 3
  let v34 : UInt256 := UInt256.mulMod (n 2) v33 P
  let v35 : UInt256 := v34 + v32
  let v36 : UInt256 := q 4
  let v37 : UInt256 := UInt256.mulMod (n 1) v36 P
  let v38 : UInt256 := v37 + v35
  let v39 : UInt256 := q 0
  let v40 : UInt256 := (n 5) * v39
  let v41 : UInt256 := v40 + v23
  let v42 : UInt256 := q 1
  let v43 : UInt256 := (n 4) * v42
  let v44 : UInt256 := v43 + v41
  let v45 : UInt256 := q 2
  let v46 : UInt256 := (n 3) * v45
  let v47 : UInt256 := v46 + v44
  let v48 : UInt256 := q 3
  let v49 : UInt256 := (n 2) * v48
  let v50 : UInt256 := v49 + v47
  let v51 : UInt256 := q 4
  let v52 : UInt256 := (n 1) * v51
  let v53 : UInt256 := v52 + v50
  let v54 : UInt256 := UInt256.land mask v53
  let v55 : UInt256 := minv * v54
  let v56 : UInt256 := UInt256.land mask v55
  let v58 : UInt256 := (n 0) * v56
  let v59 : UInt256 := v58 + v53
  let v60 : UInt256 := UInt256.mulMod (n 0) v56 P
  let v61 : UInt256 := v60 + v38
  let v69 : UInt256 := UInt256.mulMod v61 (UInt256.ofNat 128) P
  {high := v61, low := v59, carry := v69, cancel := v56, digit := UInt256.ofNat 0}

def col5High (carry P mask minv : UInt256) (a n q : Nat → UInt256) : UInt256 := (col5Words carry P mask minv a n q).high

def col5Low (carry P mask minv : UInt256) (a n q : Nat → UInt256) : UInt256 := (col5Words carry P mask minv a n q).low

def col5Carry (carry P mask minv : UInt256) (a n q : Nat → UInt256) : UInt256 := (col5Words carry P mask minv a n q).carry

def col5Cancel (carry P mask minv : UInt256) (a n q : Nat → UInt256) : UInt256 := (col5Words carry P mask minv a n q).cancel

def col5Digit (carry P mask minv : UInt256) (a n q : Nat → UInt256) : UInt256 := (col5Words carry P mask minv a n q).digit

theorem col5_stack (s : State) (carry P n0 n1 n2 n3 n4 n5 n6 n7 n8 mask minv : UInt256) (rest : List UInt256) :
    (col5Model s carry P n0 n1 n2 n3 n4 n5 n6 n7 n8 mask minv rest).stack =
      (col5Words carry P mask minv (fun i => MachineState.readWord s.memory (768+32*i)) (fun i => match i with | 0 => n0 | 1 => n1 | 2 => n2 | 3 => n3 | 4 => n4 | 5 => n5 | 6 => n6 | 7 => n7 | _ => n8) (fun i => MachineState.readWord s.memory (1056+32*i))).carry :: P :: n0 :: n1 :: n2 :: n3 :: n4 :: n5 :: n6 :: n7 :: n8 :: mask :: minv :: rest := by rfl

#print axioms col5_stack

def col6Words (carry P mask minv : UInt256) (a n q : Nat → UInt256) : ColumnWords :=
  let v0 : UInt256 := a 6
  let v1 : UInt256 := a 0
  let v2 : UInt256 := UInt256.mulMod v0 v1 P
  let v3 : UInt256 := v0 * v1
  let v4 : UInt256 := a 5
  let v5 : UInt256 := a 1
  let v6 : UInt256 := UInt256.mulMod v5 v4 P
  let v7 : UInt256 := v6 + v2
  let v8 : UInt256 := a 4
  let v9 : UInt256 := a 2
  let v10 : UInt256 := UInt256.mulMod v9 v8 P
  let v11 : UInt256 := v10 + v7
  let v12 : UInt256 := a 5
  let v13 : UInt256 := a 1
  let v14 : UInt256 := v13 * v12
  let v15 : UInt256 := v14 + v3
  let v16 : UInt256 := a 4
  let v17 : UInt256 := a 2
  let v18 : UInt256 := v17 * v16
  let v19 : UInt256 := v18 + v15
  let v20 : UInt256 := v19 + v19
  let v21 : UInt256 := v11 + v11
  let v22 : UInt256 := carry + v21
  let v23 : UInt256 := carry + v20
  let v24 : UInt256 := a 3
  let v25 : UInt256 := UInt256.mulMod v24 v24 P
  let v26 : UInt256 := v25 + v22
  let v27 : UInt256 := q 0
  let v28 : UInt256 := UInt256.mulMod (n 6) v27 P
  let v29 : UInt256 := v28 + v26
  let v30 : UInt256 := q 1
  let v31 : UInt256 := UInt256.mulMod (n 5) v30 P
  let v32 : UInt256 := v31 + v29
  let v33 : UInt256 := q 2
  let v34 : UInt256 := UInt256.mulMod (n 4) v33 P
  let v35 : UInt256 := v34 + v32
  let v36 : UInt256 := q 3
  let v37 : UInt256 := UInt256.mulMod (n 3) v36 P
  let v38 : UInt256 := v37 + v35
  let v39 : UInt256 := q 4
  let v40 : UInt256 := UInt256.mulMod (n 2) v39 P
  let v41 : UInt256 := v40 + v38
  let v42 : UInt256 := q 5
  let v43 : UInt256 := UInt256.mulMod (n 1) v42 P
  let v44 : UInt256 := v43 + v41
  let v45 : UInt256 := a 3
  let v46 : UInt256 := v45 * v45
  let v47 : UInt256 := v46 + v23
  let v48 : UInt256 := q 0
  let v49 : UInt256 := (n 6) * v48
  let v50 : UInt256 := v49 + v47
  let v51 : UInt256 := q 1
  let v52 : UInt256 := (n 5) * v51
  let v53 : UInt256 := v52 + v50
  let v54 : UInt256 := q 2
  let v55 : UInt256 := (n 4) * v54
  let v56 : UInt256 := v55 + v53
  let v57 : UInt256 := q 3
  let v58 : UInt256 := (n 3) * v57
  let v59 : UInt256 := v58 + v56
  let v60 : UInt256 := q 4
  let v61 : UInt256 := (n 2) * v60
  let v62 : UInt256 := v61 + v59
  let v63 : UInt256 := q 5
  let v64 : UInt256 := (n 1) * v63
  let v65 : UInt256 := v64 + v62
  let v66 : UInt256 := UInt256.land mask v65
  let v67 : UInt256 := minv * v66
  let v68 : UInt256 := UInt256.land mask v67
  let v70 : UInt256 := (n 0) * v68
  let v71 : UInt256 := v70 + v65
  let v72 : UInt256 := UInt256.mulMod (n 0) v68 P
  let v73 : UInt256 := v72 + v44
  let v81 : UInt256 := UInt256.mulMod v73 (UInt256.ofNat 128) P
  {high := v73, low := v71, carry := v81, cancel := v68, digit := UInt256.ofNat 0}

def col6High (carry P mask minv : UInt256) (a n q : Nat → UInt256) : UInt256 := (col6Words carry P mask minv a n q).high

def col6Low (carry P mask minv : UInt256) (a n q : Nat → UInt256) : UInt256 := (col6Words carry P mask minv a n q).low

def col6Carry (carry P mask minv : UInt256) (a n q : Nat → UInt256) : UInt256 := (col6Words carry P mask minv a n q).carry

def col6Cancel (carry P mask minv : UInt256) (a n q : Nat → UInt256) : UInt256 := (col6Words carry P mask minv a n q).cancel

def col6Digit (carry P mask minv : UInt256) (a n q : Nat → UInt256) : UInt256 := (col6Words carry P mask minv a n q).digit

theorem col6_stack (s : State) (carry P n0 n1 n2 n3 n4 n5 n6 n7 n8 mask minv : UInt256) (rest : List UInt256) :
    (col6Model s carry P n0 n1 n2 n3 n4 n5 n6 n7 n8 mask minv rest).stack =
      (col6Words carry P mask minv (fun i => MachineState.readWord s.memory (768+32*i)) (fun i => match i with | 0 => n0 | 1 => n1 | 2 => n2 | 3 => n3 | 4 => n4 | 5 => n5 | 6 => n6 | 7 => n7 | _ => n8) (fun i => MachineState.readWord s.memory (1056+32*i))).carry :: P :: n0 :: n1 :: n2 :: n3 :: n4 :: n5 :: n6 :: n7 :: n8 :: mask :: minv :: rest := by rfl

#print axioms col6_stack

def col7Words (carry P mask minv : UInt256) (a n q : Nat → UInt256) : ColumnWords :=
  let v0 : UInt256 := a 7
  let v1 : UInt256 := a 0
  let v2 : UInt256 := UInt256.mulMod v0 v1 P
  let v3 : UInt256 := v0 * v1
  let v4 : UInt256 := a 6
  let v5 : UInt256 := a 1
  let v6 : UInt256 := UInt256.mulMod v5 v4 P
  let v7 : UInt256 := v6 + v2
  let v8 : UInt256 := a 5
  let v9 : UInt256 := a 2
  let v10 : UInt256 := UInt256.mulMod v9 v8 P
  let v11 : UInt256 := v10 + v7
  let v12 : UInt256 := a 4
  let v13 : UInt256 := a 3
  let v14 : UInt256 := UInt256.mulMod v13 v12 P
  let v15 : UInt256 := v14 + v11
  let v16 : UInt256 := a 6
  let v17 : UInt256 := a 1
  let v18 : UInt256 := v17 * v16
  let v19 : UInt256 := v18 + v3
  let v20 : UInt256 := a 5
  let v21 : UInt256 := a 2
  let v22 : UInt256 := v21 * v20
  let v23 : UInt256 := v22 + v19
  let v24 : UInt256 := a 4
  let v25 : UInt256 := a 3
  let v26 : UInt256 := v25 * v24
  let v27 : UInt256 := v26 + v23
  let v28 : UInt256 := v27 + v27
  let v29 : UInt256 := v15 + v15
  let v30 : UInt256 := carry + v29
  let v31 : UInt256 := carry + v28
  let v32 : UInt256 := q 0
  let v33 : UInt256 := UInt256.mulMod (n 7) v32 P
  let v34 : UInt256 := v33 + v30
  let v35 : UInt256 := q 1
  let v36 : UInt256 := UInt256.mulMod (n 6) v35 P
  let v37 : UInt256 := v36 + v34
  let v38 : UInt256 := q 2
  let v39 : UInt256 := UInt256.mulMod (n 5) v38 P
  let v40 : UInt256 := v39 + v37
  let v41 : UInt256 := q 3
  let v42 : UInt256 := UInt256.mulMod (n 4) v41 P
  let v43 : UInt256 := v42 + v40
  let v44 : UInt256 := q 4
  let v45 : UInt256 := UInt256.mulMod (n 3) v44 P
  let v46 : UInt256 := v45 + v43
  let v47 : UInt256 := q 5
  let v48 : UInt256 := UInt256.mulMod (n 2) v47 P
  let v49 : UInt256 := v48 + v46
  let v50 : UInt256 := q 6
  let v51 : UInt256 := UInt256.mulMod (n 1) v50 P
  let v52 : UInt256 := v51 + v49
  let v53 : UInt256 := q 0
  let v54 : UInt256 := (n 7) * v53
  let v55 : UInt256 := v54 + v31
  let v56 : UInt256 := q 1
  let v57 : UInt256 := (n 6) * v56
  let v58 : UInt256 := v57 + v55
  let v59 : UInt256 := q 2
  let v60 : UInt256 := (n 5) * v59
  let v61 : UInt256 := v60 + v58
  let v62 : UInt256 := q 3
  let v63 : UInt256 := (n 4) * v62
  let v64 : UInt256 := v63 + v61
  let v65 : UInt256 := q 4
  let v66 : UInt256 := (n 3) * v65
  let v67 : UInt256 := v66 + v64
  let v68 : UInt256 := q 5
  let v69 : UInt256 := (n 2) * v68
  let v70 : UInt256 := v69 + v67
  let v71 : UInt256 := q 6
  let v72 : UInt256 := (n 1) * v71
  let v73 : UInt256 := v72 + v70
  let v74 : UInt256 := UInt256.land mask v73
  let v75 : UInt256 := minv * v74
  let v76 : UInt256 := UInt256.land mask v75
  let v78 : UInt256 := (n 0) * v76
  let v79 : UInt256 := v78 + v73
  let v80 : UInt256 := UInt256.mulMod (n 0) v76 P
  let v81 : UInt256 := v80 + v52
  let v89 : UInt256 := UInt256.mulMod v81 (UInt256.ofNat 128) P
  {high := v81, low := v79, carry := v89, cancel := v76, digit := UInt256.ofNat 0}

def col7High (carry P mask minv : UInt256) (a n q : Nat → UInt256) : UInt256 := (col7Words carry P mask minv a n q).high

def col7Low (carry P mask minv : UInt256) (a n q : Nat → UInt256) : UInt256 := (col7Words carry P mask minv a n q).low

def col7Carry (carry P mask minv : UInt256) (a n q : Nat → UInt256) : UInt256 := (col7Words carry P mask minv a n q).carry

def col7Cancel (carry P mask minv : UInt256) (a n q : Nat → UInt256) : UInt256 := (col7Words carry P mask minv a n q).cancel

def col7Digit (carry P mask minv : UInt256) (a n q : Nat → UInt256) : UInt256 := (col7Words carry P mask minv a n q).digit

theorem col7_stack (s : State) (carry P n0 n1 n2 n3 n4 n5 n6 n7 n8 mask minv : UInt256) (rest : List UInt256) :
    (col7Model s carry P n0 n1 n2 n3 n4 n5 n6 n7 n8 mask minv rest).stack =
      (col7Words carry P mask minv (fun i => MachineState.readWord s.memory (768+32*i)) (fun i => match i with | 0 => n0 | 1 => n1 | 2 => n2 | 3 => n3 | 4 => n4 | 5 => n5 | 6 => n6 | 7 => n7 | _ => n8) (fun i => MachineState.readWord s.memory (1056+32*i))).carry :: P :: n0 :: n1 :: n2 :: n3 :: n4 :: n5 :: n6 :: n7 :: n8 :: mask :: minv :: rest := by rfl

#print axioms col7_stack

def col8Words (carry P mask minv : UInt256) (a n q : Nat → UInt256) : ColumnWords :=
  let v0 : UInt256 := a 8
  let v1 : UInt256 := a 0
  let v2 : UInt256 := UInt256.mulMod v0 v1 P
  let v3 : UInt256 := v0 * v1
  let v4 : UInt256 := a 7
  let v5 : UInt256 := a 1
  let v6 : UInt256 := UInt256.mulMod v5 v4 P
  let v7 : UInt256 := v6 + v2
  let v8 : UInt256 := a 6
  let v9 : UInt256 := a 2
  let v10 : UInt256 := UInt256.mulMod v9 v8 P
  let v11 : UInt256 := v10 + v7
  let v12 : UInt256 := a 5
  let v13 : UInt256 := a 3
  let v14 : UInt256 := UInt256.mulMod v13 v12 P
  let v15 : UInt256 := v14 + v11
  let v16 : UInt256 := a 7
  let v17 : UInt256 := a 1
  let v18 : UInt256 := v17 * v16
  let v19 : UInt256 := v18 + v3
  let v20 : UInt256 := a 6
  let v21 : UInt256 := a 2
  let v22 : UInt256 := v21 * v20
  let v23 : UInt256 := v22 + v19
  let v24 : UInt256 := a 5
  let v25 : UInt256 := a 3
  let v26 : UInt256 := v25 * v24
  let v27 : UInt256 := v26 + v23
  let v28 : UInt256 := v27 + v27
  let v29 : UInt256 := v15 + v15
  let v30 : UInt256 := carry + v29
  let v31 : UInt256 := carry + v28
  let v32 : UInt256 := a 4
  let v33 : UInt256 := UInt256.mulMod v32 v32 P
  let v34 : UInt256 := v33 + v30
  let v35 : UInt256 := q 0
  let v36 : UInt256 := UInt256.mulMod (n 8) v35 P
  let v37 : UInt256 := v36 + v34
  let v38 : UInt256 := q 1
  let v39 : UInt256 := UInt256.mulMod (n 7) v38 P
  let v40 : UInt256 := v39 + v37
  let v41 : UInt256 := q 2
  let v42 : UInt256 := UInt256.mulMod (n 6) v41 P
  let v43 : UInt256 := v42 + v40
  let v44 : UInt256 := q 3
  let v45 : UInt256 := UInt256.mulMod (n 5) v44 P
  let v46 : UInt256 := v45 + v43
  let v47 : UInt256 := q 4
  let v48 : UInt256 := UInt256.mulMod (n 4) v47 P
  let v49 : UInt256 := v48 + v46
  let v50 : UInt256 := q 5
  let v51 : UInt256 := UInt256.mulMod (n 3) v50 P
  let v52 : UInt256 := v51 + v49
  let v53 : UInt256 := q 6
  let v54 : UInt256 := UInt256.mulMod (n 2) v53 P
  let v55 : UInt256 := v54 + v52
  let v56 : UInt256 := q 7
  let v57 : UInt256 := UInt256.mulMod (n 1) v56 P
  let v58 : UInt256 := v57 + v55
  let v59 : UInt256 := a 4
  let v60 : UInt256 := v59 * v59
  let v61 : UInt256 := v60 + v31
  let v62 : UInt256 := q 0
  let v63 : UInt256 := (n 8) * v62
  let v64 : UInt256 := v63 + v61
  let v65 : UInt256 := q 1
  let v66 : UInt256 := (n 7) * v65
  let v67 : UInt256 := v66 + v64
  let v68 : UInt256 := q 2
  let v69 : UInt256 := (n 6) * v68
  let v70 : UInt256 := v69 + v67
  let v71 : UInt256 := q 3
  let v72 : UInt256 := (n 5) * v71
  let v73 : UInt256 := v72 + v70
  let v74 : UInt256 := q 4
  let v75 : UInt256 := (n 4) * v74
  let v76 : UInt256 := v75 + v73
  let v77 : UInt256 := q 5
  let v78 : UInt256 := (n 3) * v77
  let v79 : UInt256 := v78 + v76
  let v80 : UInt256 := q 6
  let v81 : UInt256 := (n 2) * v80
  let v82 : UInt256 := v81 + v79
  let v83 : UInt256 := q 7
  let v84 : UInt256 := (n 1) * v83
  let v85 : UInt256 := v84 + v82
  let v86 : UInt256 := UInt256.land mask v85
  let v87 : UInt256 := minv * v86
  let v88 : UInt256 := UInt256.land (UInt256.ofNat 79228162514264337593543950335) v87
  let v90 : UInt256 := (n 0) * v88
  let v91 : UInt256 := v90 + v85
  let v92 : UInt256 := UInt256.mulMod (n 0) v88 P
  let v93 : UInt256 := v92 + v58
  let v97 : UInt256 := UInt256.addMod v93 (UInt256.lnot v91) P
  let v98 : UInt256 := UInt256.shiftRight v97 (UInt256.ofNat 5)
  let v99 : UInt256 := UInt256.land mask v91
  let v101 : UInt256 := UInt256.shiftLeft v98 (UInt256.ofNat 12)
  let v102 : UInt256 := UInt256.shiftRight v91 (UInt256.ofNat 244)
  let v103 : UInt256 := v102 + v101
  {high := v93, low := v91, carry := v103, cancel := v88, digit := v99}

def col8High (carry P mask minv : UInt256) (a n q : Nat → UInt256) : UInt256 := (col8Words carry P mask minv a n q).high

def col8Low (carry P mask minv : UInt256) (a n q : Nat → UInt256) : UInt256 := (col8Words carry P mask minv a n q).low

def col8Carry (carry P mask minv : UInt256) (a n q : Nat → UInt256) : UInt256 := (col8Words carry P mask minv a n q).carry

def col8Cancel (carry P mask minv : UInt256) (a n q : Nat → UInt256) : UInt256 := (col8Words carry P mask minv a n q).cancel

def col8Digit (carry P mask minv : UInt256) (a n q : Nat → UInt256) : UInt256 := (col8Words carry P mask minv a n q).digit

theorem col8_stack (s : State) (carry P n0 n1 n2 n3 n4 n5 n6 n7 n8 mask minv : UInt256) (rest : List UInt256) :
    (col8Model s carry P n0 n1 n2 n3 n4 n5 n6 n7 n8 mask minv rest).stack =
      (col8Words carry P mask minv (fun i => MachineState.readWord s.memory (768+32*i)) (fun i => match i with | 0 => n0 | 1 => n1 | 2 => n2 | 3 => n3 | 4 => n4 | 5 => n5 | 6 => n6 | 7 => n7 | _ => n8) (fun i => MachineState.readWord s.memory (1056+32*i))).carry :: P :: n0 :: n1 :: n2 :: n3 :: n4 :: n5 :: n6 :: n7 :: n8 :: mask :: minv :: rest := by rfl

#print axioms col8_stack

def col9Words (carry P mask minv : UInt256) (a n q : Nat → UInt256) : ColumnWords :=
  let v0 : UInt256 := a 8
  let v1 : UInt256 := a 1
  let v2 : UInt256 := UInt256.mulMod v0 v1 P
  let v3 : UInt256 := v0 * v1
  let v4 : UInt256 := a 7
  let v5 : UInt256 := a 2
  let v6 : UInt256 := UInt256.mulMod v5 v4 P
  let v7 : UInt256 := v6 + v2
  let v8 : UInt256 := a 6
  let v9 : UInt256 := a 3
  let v10 : UInt256 := UInt256.mulMod v9 v8 P
  let v11 : UInt256 := v10 + v7
  let v12 : UInt256 := a 5
  let v13 : UInt256 := a 4
  let v14 : UInt256 := UInt256.mulMod v13 v12 P
  let v15 : UInt256 := v14 + v11
  let v16 : UInt256 := a 7
  let v17 : UInt256 := a 2
  let v18 : UInt256 := v17 * v16
  let v19 : UInt256 := v18 + v3
  let v20 : UInt256 := a 6
  let v21 : UInt256 := a 3
  let v22 : UInt256 := v21 * v20
  let v23 : UInt256 := v22 + v19
  let v24 : UInt256 := a 5
  let v25 : UInt256 := a 4
  let v26 : UInt256 := v25 * v24
  let v27 : UInt256 := v26 + v23
  let v28 : UInt256 := v27 + v27
  let v29 : UInt256 := v15 + v15
  let v30 : UInt256 := carry + v29
  let v31 : UInt256 := carry + v28
  let v32 : UInt256 := q 1
  let v33 : UInt256 := UInt256.mulMod (n 8) v32 P
  let v34 : UInt256 := v33 + v30
  let v35 : UInt256 := q 2
  let v36 : UInt256 := UInt256.mulMod (n 7) v35 P
  let v37 : UInt256 := v36 + v34
  let v38 : UInt256 := q 3
  let v39 : UInt256 := UInt256.mulMod (n 6) v38 P
  let v40 : UInt256 := v39 + v37
  let v41 : UInt256 := q 4
  let v42 : UInt256 := UInt256.mulMod (n 5) v41 P
  let v43 : UInt256 := v42 + v40
  let v44 : UInt256 := q 5
  let v45 : UInt256 := UInt256.mulMod (n 4) v44 P
  let v46 : UInt256 := v45 + v43
  let v47 : UInt256 := q 6
  let v48 : UInt256 := UInt256.mulMod (n 3) v47 P
  let v49 : UInt256 := v48 + v46
  let v50 : UInt256 := q 7
  let v51 : UInt256 := UInt256.mulMod (n 2) v50 P
  let v52 : UInt256 := v51 + v49
  let v53 : UInt256 := q 8
  let v54 : UInt256 := UInt256.mulMod (n 1) v53 P
  let v55 : UInt256 := v54 + v52
  let v56 : UInt256 := q 1
  let v57 : UInt256 := (n 8) * v56
  let v58 : UInt256 := v57 + v31
  let v59 : UInt256 := q 2
  let v60 : UInt256 := (n 7) * v59
  let v61 : UInt256 := v60 + v58
  let v62 : UInt256 := q 3
  let v63 : UInt256 := (n 6) * v62
  let v64 : UInt256 := v63 + v61
  let v65 : UInt256 := q 4
  let v66 : UInt256 := (n 5) * v65
  let v67 : UInt256 := v66 + v64
  let v68 : UInt256 := q 5
  let v69 : UInt256 := (n 4) * v68
  let v70 : UInt256 := v69 + v67
  let v71 : UInt256 := q 6
  let v72 : UInt256 := (n 3) * v71
  let v73 : UInt256 := v72 + v70
  let v74 : UInt256 := q 7
  let v75 : UInt256 := (n 2) * v74
  let v76 : UInt256 := v75 + v73
  let v77 : UInt256 := q 8
  let v78 : UInt256 := (n 1) * v77
  let v79 : UInt256 := v78 + v76
  let v83 : UInt256 := UInt256.addMod v55 (UInt256.lnot v79) P
  let v84 : UInt256 := UInt256.shiftRight v83 (UInt256.ofNat 5)
  let v85 : UInt256 := UInt256.land mask v79
  let v87 : UInt256 := UInt256.shiftLeft v84 (UInt256.ofNat 12)
  let v88 : UInt256 := UInt256.shiftRight v79 (UInt256.ofNat 244)
  let v89 : UInt256 := v88 + v87
  {high := v55, low := v79, carry := v89, cancel := UInt256.ofNat 0, digit := v85}

def col9High (carry P mask minv : UInt256) (a n q : Nat → UInt256) : UInt256 := (col9Words carry P mask minv a n q).high

def col9Low (carry P mask minv : UInt256) (a n q : Nat → UInt256) : UInt256 := (col9Words carry P mask minv a n q).low

def col9Carry (carry P mask minv : UInt256) (a n q : Nat → UInt256) : UInt256 := (col9Words carry P mask minv a n q).carry

def col9Cancel (carry P mask minv : UInt256) (a n q : Nat → UInt256) : UInt256 := (col9Words carry P mask minv a n q).cancel

def col9Digit (carry P mask minv : UInt256) (a n q : Nat → UInt256) : UInt256 := (col9Words carry P mask minv a n q).digit

theorem col9_stack (s : State) (carry P n0 n1 n2 n3 n4 n5 n6 n7 n8 mask minv : UInt256) (rest : List UInt256) :
    (col9Model s carry P n0 n1 n2 n3 n4 n5 n6 n7 n8 mask minv rest).stack =
      (col9Words carry P mask minv (fun i => MachineState.readWord s.memory (768+32*i)) (fun i => match i with | 0 => n0 | 1 => n1 | 2 => n2 | 3 => n3 | 4 => n4 | 5 => n5 | 6 => n6 | 7 => n7 | _ => n8) (fun i => MachineState.readWord s.memory (1056+32*i))).carry :: P :: n0 :: n1 :: n2 :: n3 :: n4 :: n5 :: n6 :: n7 :: n8 :: mask :: minv :: rest := by rfl

#print axioms col9_stack

def col10Words (carry P mask minv : UInt256) (a n q : Nat → UInt256) : ColumnWords :=
  let v0 : UInt256 := a 8
  let v1 : UInt256 := a 2
  let v2 : UInt256 := UInt256.mulMod v0 v1 P
  let v3 : UInt256 := v0 * v1
  let v4 : UInt256 := a 7
  let v5 : UInt256 := a 3
  let v6 : UInt256 := UInt256.mulMod v5 v4 P
  let v7 : UInt256 := v6 + v2
  let v8 : UInt256 := a 6
  let v9 : UInt256 := a 4
  let v10 : UInt256 := UInt256.mulMod v9 v8 P
  let v11 : UInt256 := v10 + v7
  let v12 : UInt256 := a 7
  let v13 : UInt256 := a 3
  let v14 : UInt256 := v13 * v12
  let v15 : UInt256 := v14 + v3
  let v16 : UInt256 := a 6
  let v17 : UInt256 := a 4
  let v18 : UInt256 := v17 * v16
  let v19 : UInt256 := v18 + v15
  let v20 : UInt256 := v19 + v19
  let v21 : UInt256 := v11 + v11
  let v22 : UInt256 := carry + v21
  let v23 : UInt256 := carry + v20
  let v24 : UInt256 := a 5
  let v25 : UInt256 := UInt256.mulMod v24 v24 P
  let v26 : UInt256 := v25 + v22
  let v27 : UInt256 := q 2
  let v28 : UInt256 := UInt256.mulMod (n 8) v27 P
  let v29 : UInt256 := v28 + v26
  let v30 : UInt256 := q 3
  let v31 : UInt256 := UInt256.mulMod (n 7) v30 P
  let v32 : UInt256 := v31 + v29
  let v33 : UInt256 := q 4
  let v34 : UInt256 := UInt256.mulMod (n 6) v33 P
  let v35 : UInt256 := v34 + v32
  let v36 : UInt256 := q 5
  let v37 : UInt256 := UInt256.mulMod (n 5) v36 P
  let v38 : UInt256 := v37 + v35
  let v39 : UInt256 := q 6
  let v40 : UInt256 := UInt256.mulMod (n 4) v39 P
  let v41 : UInt256 := v40 + v38
  let v42 : UInt256 := q 7
  let v43 : UInt256 := UInt256.mulMod (n 3) v42 P
  let v44 : UInt256 := v43 + v41
  let v45 : UInt256 := q 8
  let v46 : UInt256 := UInt256.mulMod (n 2) v45 P
  let v47 : UInt256 := v46 + v44
  let v48 : UInt256 := a 5
  let v49 : UInt256 := v48 * v48
  let v50 : UInt256 := v49 + v23
  let v51 : UInt256 := q 2
  let v52 : UInt256 := (n 8) * v51
  let v53 : UInt256 := v52 + v50
  let v54 : UInt256 := q 3
  let v55 : UInt256 := (n 7) * v54
  let v56 : UInt256 := v55 + v53
  let v57 : UInt256 := q 4
  let v58 : UInt256 := (n 6) * v57
  let v59 : UInt256 := v58 + v56
  let v60 : UInt256 := q 5
  let v61 : UInt256 := (n 5) * v60
  let v62 : UInt256 := v61 + v59
  let v63 : UInt256 := q 6
  let v64 : UInt256 := (n 4) * v63
  let v65 : UInt256 := v64 + v62
  let v66 : UInt256 := q 7
  let v67 : UInt256 := (n 3) * v66
  let v68 : UInt256 := v67 + v65
  let v69 : UInt256 := q 8
  let v70 : UInt256 := (n 2) * v69
  let v71 : UInt256 := v70 + v68
  let v75 : UInt256 := UInt256.addMod v47 (UInt256.lnot v71) P
  let v76 : UInt256 := UInt256.shiftRight v75 (UInt256.ofNat 5)
  let v77 : UInt256 := UInt256.land mask v71
  let v79 : UInt256 := UInt256.shiftLeft v76 (UInt256.ofNat 12)
  let v80 : UInt256 := UInt256.shiftRight v71 (UInt256.ofNat 244)
  let v81 : UInt256 := v80 + v79
  {high := v47, low := v71, carry := v81, cancel := UInt256.ofNat 0, digit := v77}

def col10High (carry P mask minv : UInt256) (a n q : Nat → UInt256) : UInt256 := (col10Words carry P mask minv a n q).high

def col10Low (carry P mask minv : UInt256) (a n q : Nat → UInt256) : UInt256 := (col10Words carry P mask minv a n q).low

def col10Carry (carry P mask minv : UInt256) (a n q : Nat → UInt256) : UInt256 := (col10Words carry P mask minv a n q).carry

def col10Cancel (carry P mask minv : UInt256) (a n q : Nat → UInt256) : UInt256 := (col10Words carry P mask minv a n q).cancel

def col10Digit (carry P mask minv : UInt256) (a n q : Nat → UInt256) : UInt256 := (col10Words carry P mask minv a n q).digit

theorem col10_stack (s : State) (carry P n0 n1 n2 n3 n4 n5 n6 n7 n8 mask minv : UInt256) (rest : List UInt256) :
    (col10Model s carry P n0 n1 n2 n3 n4 n5 n6 n7 n8 mask minv rest).stack =
      (col10Words carry P mask minv (fun i => MachineState.readWord s.memory (768+32*i)) (fun i => match i with | 0 => n0 | 1 => n1 | 2 => n2 | 3 => n3 | 4 => n4 | 5 => n5 | 6 => n6 | 7 => n7 | _ => n8) (fun i => MachineState.readWord s.memory (1056+32*i))).carry :: P :: n0 :: n1 :: n2 :: n3 :: n4 :: n5 :: n6 :: n7 :: n8 :: mask :: minv :: rest := by rfl

#print axioms col10_stack

def col11Words (carry P mask minv : UInt256) (a n q : Nat → UInt256) : ColumnWords :=
  let v0 : UInt256 := a 8
  let v1 : UInt256 := a 3
  let v2 : UInt256 := UInt256.mulMod v0 v1 P
  let v3 : UInt256 := v0 * v1
  let v4 : UInt256 := a 7
  let v5 : UInt256 := a 4
  let v6 : UInt256 := UInt256.mulMod v5 v4 P
  let v7 : UInt256 := v6 + v2
  let v8 : UInt256 := a 6
  let v9 : UInt256 := a 5
  let v10 : UInt256 := UInt256.mulMod v9 v8 P
  let v11 : UInt256 := v10 + v7
  let v12 : UInt256 := a 7
  let v13 : UInt256 := a 4
  let v14 : UInt256 := v13 * v12
  let v15 : UInt256 := v14 + v3
  let v16 : UInt256 := a 6
  let v17 : UInt256 := a 5
  let v18 : UInt256 := v17 * v16
  let v19 : UInt256 := v18 + v15
  let v20 : UInt256 := v19 + v19
  let v21 : UInt256 := v11 + v11
  let v22 : UInt256 := carry + v21
  let v23 : UInt256 := carry + v20
  let v24 : UInt256 := q 3
  let v25 : UInt256 := UInt256.mulMod (n 8) v24 P
  let v26 : UInt256 := v25 + v22
  let v27 : UInt256 := q 4
  let v28 : UInt256 := UInt256.mulMod (n 7) v27 P
  let v29 : UInt256 := v28 + v26
  let v30 : UInt256 := q 5
  let v31 : UInt256 := UInt256.mulMod (n 6) v30 P
  let v32 : UInt256 := v31 + v29
  let v33 : UInt256 := q 6
  let v34 : UInt256 := UInt256.mulMod (n 5) v33 P
  let v35 : UInt256 := v34 + v32
  let v36 : UInt256 := q 7
  let v37 : UInt256 := UInt256.mulMod (n 4) v36 P
  let v38 : UInt256 := v37 + v35
  let v39 : UInt256 := q 8
  let v40 : UInt256 := UInt256.mulMod (n 3) v39 P
  let v41 : UInt256 := v40 + v38
  let v42 : UInt256 := q 3
  let v43 : UInt256 := (n 8) * v42
  let v44 : UInt256 := v43 + v23
  let v45 : UInt256 := q 4
  let v46 : UInt256 := (n 7) * v45
  let v47 : UInt256 := v46 + v44
  let v48 : UInt256 := q 5
  let v49 : UInt256 := (n 6) * v48
  let v50 : UInt256 := v49 + v47
  let v51 : UInt256 := q 6
  let v52 : UInt256 := (n 5) * v51
  let v53 : UInt256 := v52 + v50
  let v54 : UInt256 := q 7
  let v55 : UInt256 := (n 4) * v54
  let v56 : UInt256 := v55 + v53
  let v57 : UInt256 := q 8
  let v58 : UInt256 := (n 3) * v57
  let v59 : UInt256 := v58 + v56
  let v63 : UInt256 := UInt256.addMod v41 (UInt256.lnot v59) P
  let v64 : UInt256 := UInt256.shiftRight v63 (UInt256.ofNat 5)
  let v65 : UInt256 := UInt256.land mask v59
  let v67 : UInt256 := UInt256.shiftLeft v64 (UInt256.ofNat 12)
  let v68 : UInt256 := UInt256.shiftRight v59 (UInt256.ofNat 244)
  let v69 : UInt256 := v68 + v67
  {high := v41, low := v59, carry := v69, cancel := UInt256.ofNat 0, digit := v65}

def col11High (carry P mask minv : UInt256) (a n q : Nat → UInt256) : UInt256 := (col11Words carry P mask minv a n q).high

def col11Low (carry P mask minv : UInt256) (a n q : Nat → UInt256) : UInt256 := (col11Words carry P mask minv a n q).low

def col11Carry (carry P mask minv : UInt256) (a n q : Nat → UInt256) : UInt256 := (col11Words carry P mask minv a n q).carry

def col11Cancel (carry P mask minv : UInt256) (a n q : Nat → UInt256) : UInt256 := (col11Words carry P mask minv a n q).cancel

def col11Digit (carry P mask minv : UInt256) (a n q : Nat → UInt256) : UInt256 := (col11Words carry P mask minv a n q).digit

theorem col11_stack (s : State) (carry P n0 n1 n2 n3 n4 n5 n6 n7 n8 mask minv : UInt256) (rest : List UInt256) :
    (col11Model s carry P n0 n1 n2 n3 n4 n5 n6 n7 n8 mask minv rest).stack =
      (col11Words carry P mask minv (fun i => MachineState.readWord s.memory (768+32*i)) (fun i => match i with | 0 => n0 | 1 => n1 | 2 => n2 | 3 => n3 | 4 => n4 | 5 => n5 | 6 => n6 | 7 => n7 | _ => n8) (fun i => MachineState.readWord s.memory (1056+32*i))).carry :: P :: n0 :: n1 :: n2 :: n3 :: n4 :: n5 :: n6 :: n7 :: n8 :: mask :: minv :: rest := by rfl

#print axioms col11_stack

def col12Words (carry P mask minv : UInt256) (a n q : Nat → UInt256) : ColumnWords :=
  let v0 : UInt256 := a 8
  let v1 : UInt256 := a 4
  let v2 : UInt256 := UInt256.mulMod v0 v1 P
  let v3 : UInt256 := v0 * v1
  let v4 : UInt256 := a 7
  let v5 : UInt256 := a 5
  let v6 : UInt256 := UInt256.mulMod v5 v4 P
  let v7 : UInt256 := v6 + v2
  let v8 : UInt256 := a 7
  let v9 : UInt256 := a 5
  let v10 : UInt256 := v9 * v8
  let v11 : UInt256 := v10 + v3
  let v12 : UInt256 := v11 + v11
  let v13 : UInt256 := v7 + v7
  let v14 : UInt256 := carry + v13
  let v15 : UInt256 := carry + v12
  let v16 : UInt256 := a 6
  let v17 : UInt256 := UInt256.mulMod v16 v16 P
  let v18 : UInt256 := v17 + v14
  let v19 : UInt256 := q 4
  let v20 : UInt256 := UInt256.mulMod (n 8) v19 P
  let v21 : UInt256 := v20 + v18
  let v22 : UInt256 := q 5
  let v23 : UInt256 := UInt256.mulMod (n 7) v22 P
  let v24 : UInt256 := v23 + v21
  let v25 : UInt256 := q 6
  let v26 : UInt256 := UInt256.mulMod (n 6) v25 P
  let v27 : UInt256 := v26 + v24
  let v28 : UInt256 := q 7
  let v29 : UInt256 := UInt256.mulMod (n 5) v28 P
  let v30 : UInt256 := v29 + v27
  let v31 : UInt256 := q 8
  let v32 : UInt256 := UInt256.mulMod (n 4) v31 P
  let v33 : UInt256 := v32 + v30
  let v34 : UInt256 := a 6
  let v35 : UInt256 := v34 * v34
  let v36 : UInt256 := v35 + v15
  let v37 : UInt256 := q 4
  let v38 : UInt256 := (n 8) * v37
  let v39 : UInt256 := v38 + v36
  let v40 : UInt256 := q 5
  let v41 : UInt256 := (n 7) * v40
  let v42 : UInt256 := v41 + v39
  let v43 : UInt256 := q 6
  let v44 : UInt256 := (n 6) * v43
  let v45 : UInt256 := v44 + v42
  let v46 : UInt256 := q 7
  let v47 : UInt256 := (n 5) * v46
  let v48 : UInt256 := v47 + v45
  let v49 : UInt256 := q 8
  let v50 : UInt256 := (n 4) * v49
  let v51 : UInt256 := v50 + v48
  let v55 : UInt256 := UInt256.addMod v33 (UInt256.lnot v51) P
  let v56 : UInt256 := UInt256.shiftRight v55 (UInt256.ofNat 5)
  let v57 : UInt256 := UInt256.land mask v51
  let v59 : UInt256 := UInt256.shiftLeft v56 (UInt256.ofNat 12)
  let v60 : UInt256 := UInt256.shiftRight v51 (UInt256.ofNat 244)
  let v61 : UInt256 := v60 + v59
  {high := v33, low := v51, carry := v61, cancel := UInt256.ofNat 0, digit := v57}

def col12High (carry P mask minv : UInt256) (a n q : Nat → UInt256) : UInt256 := (col12Words carry P mask minv a n q).high

def col12Low (carry P mask minv : UInt256) (a n q : Nat → UInt256) : UInt256 := (col12Words carry P mask minv a n q).low

def col12Carry (carry P mask minv : UInt256) (a n q : Nat → UInt256) : UInt256 := (col12Words carry P mask minv a n q).carry

def col12Cancel (carry P mask minv : UInt256) (a n q : Nat → UInt256) : UInt256 := (col12Words carry P mask minv a n q).cancel

def col12Digit (carry P mask minv : UInt256) (a n q : Nat → UInt256) : UInt256 := (col12Words carry P mask minv a n q).digit

theorem col12_stack (s : State) (carry P n0 n1 n2 n3 n4 n5 n6 n7 n8 mask minv : UInt256) (rest : List UInt256) :
    (col12Model s carry P n0 n1 n2 n3 n4 n5 n6 n7 n8 mask minv rest).stack =
      (col12Words carry P mask minv (fun i => MachineState.readWord s.memory (768+32*i)) (fun i => match i with | 0 => n0 | 1 => n1 | 2 => n2 | 3 => n3 | 4 => n4 | 5 => n5 | 6 => n6 | 7 => n7 | _ => n8) (fun i => MachineState.readWord s.memory (1056+32*i))).carry :: P :: n0 :: n1 :: n2 :: n3 :: n4 :: n5 :: n6 :: n7 :: n8 :: mask :: minv :: rest := by rfl

#print axioms col12_stack

def col13Words (carry P mask minv : UInt256) (a n q : Nat → UInt256) : ColumnWords :=
  let v0 : UInt256 := a 8
  let v1 : UInt256 := a 5
  let v2 : UInt256 := UInt256.mulMod v0 v1 P
  let v3 : UInt256 := v0 * v1
  let v4 : UInt256 := a 7
  let v5 : UInt256 := a 6
  let v6 : UInt256 := UInt256.mulMod v5 v4 P
  let v7 : UInt256 := v6 + v2
  let v8 : UInt256 := a 7
  let v9 : UInt256 := a 6
  let v10 : UInt256 := v9 * v8
  let v11 : UInt256 := v10 + v3
  let v12 : UInt256 := v11 + v11
  let v13 : UInt256 := v7 + v7
  let v14 : UInt256 := carry + v13
  let v15 : UInt256 := carry + v12
  let v16 : UInt256 := q 5
  let v17 : UInt256 := UInt256.mulMod (n 8) v16 P
  let v18 : UInt256 := v17 + v14
  let v19 : UInt256 := q 6
  let v20 : UInt256 := UInt256.mulMod (n 7) v19 P
  let v21 : UInt256 := v20 + v18
  let v22 : UInt256 := q 7
  let v23 : UInt256 := UInt256.mulMod (n 6) v22 P
  let v24 : UInt256 := v23 + v21
  let v25 : UInt256 := q 8
  let v26 : UInt256 := UInt256.mulMod (n 5) v25 P
  let v27 : UInt256 := v26 + v24
  let v28 : UInt256 := q 5
  let v29 : UInt256 := (n 8) * v28
  let v30 : UInt256 := v29 + v15
  let v31 : UInt256 := q 6
  let v32 : UInt256 := (n 7) * v31
  let v33 : UInt256 := v32 + v30
  let v34 : UInt256 := q 7
  let v35 : UInt256 := (n 6) * v34
  let v36 : UInt256 := v35 + v33
  let v37 : UInt256 := q 8
  let v38 : UInt256 := (n 5) * v37
  let v39 : UInt256 := v38 + v36
  let v43 : UInt256 := UInt256.addMod v27 (UInt256.lnot v39) P
  let v44 : UInt256 := UInt256.shiftRight v43 (UInt256.ofNat 5)
  let v45 : UInt256 := UInt256.land mask v39
  let v47 : UInt256 := UInt256.shiftLeft v44 (UInt256.ofNat 12)
  let v48 : UInt256 := UInt256.shiftRight v39 (UInt256.ofNat 244)
  let v49 : UInt256 := v48 + v47
  {high := v27, low := v39, carry := v49, cancel := UInt256.ofNat 0, digit := v45}

def col13High (carry P mask minv : UInt256) (a n q : Nat → UInt256) : UInt256 := (col13Words carry P mask minv a n q).high

def col13Low (carry P mask minv : UInt256) (a n q : Nat → UInt256) : UInt256 := (col13Words carry P mask minv a n q).low

def col13Carry (carry P mask minv : UInt256) (a n q : Nat → UInt256) : UInt256 := (col13Words carry P mask minv a n q).carry

def col13Cancel (carry P mask minv : UInt256) (a n q : Nat → UInt256) : UInt256 := (col13Words carry P mask minv a n q).cancel

def col13Digit (carry P mask minv : UInt256) (a n q : Nat → UInt256) : UInt256 := (col13Words carry P mask minv a n q).digit

theorem col13_stack (s : State) (carry P n0 n1 n2 n3 n4 n5 n6 n7 n8 mask minv : UInt256) (rest : List UInt256) :
    (col13Model s carry P n0 n1 n2 n3 n4 n5 n6 n7 n8 mask minv rest).stack =
      (col13Words carry P mask minv (fun i => MachineState.readWord s.memory (768+32*i)) (fun i => match i with | 0 => n0 | 1 => n1 | 2 => n2 | 3 => n3 | 4 => n4 | 5 => n5 | 6 => n6 | 7 => n7 | _ => n8) (fun i => MachineState.readWord s.memory (1056+32*i))).carry :: P :: n0 :: n1 :: n2 :: n3 :: n4 :: n5 :: n6 :: n7 :: n8 :: mask :: minv :: rest := by rfl

#print axioms col13_stack

def col14Words (carry P mask minv : UInt256) (a n q : Nat → UInt256) : ColumnWords :=
  let v0 : UInt256 := a 8
  let v1 : UInt256 := a 6
  let v2 : UInt256 := UInt256.mulMod v0 v1 P
  let v3 : UInt256 := v0 * v1
  let v4 : UInt256 := v3 + v3
  let v5 : UInt256 := v2 + v2
  let v6 : UInt256 := carry + v5
  let v7 : UInt256 := carry + v4
  let v8 : UInt256 := a 7
  let v9 : UInt256 := UInt256.mulMod v8 v8 P
  let v10 : UInt256 := v9 + v6
  let v11 : UInt256 := q 6
  let v12 : UInt256 := UInt256.mulMod (n 8) v11 P
  let v13 : UInt256 := v12 + v10
  let v14 : UInt256 := q 7
  let v15 : UInt256 := UInt256.mulMod (n 7) v14 P
  let v16 : UInt256 := v15 + v13
  let v17 : UInt256 := q 8
  let v18 : UInt256 := UInt256.mulMod (n 6) v17 P
  let v19 : UInt256 := v18 + v16
  let v20 : UInt256 := a 7
  let v21 : UInt256 := v20 * v20
  let v22 : UInt256 := v21 + v7
  let v23 : UInt256 := q 6
  let v24 : UInt256 := (n 8) * v23
  let v25 : UInt256 := v24 + v22
  let v26 : UInt256 := q 7
  let v27 : UInt256 := (n 7) * v26
  let v28 : UInt256 := v27 + v25
  let v29 : UInt256 := q 8
  let v30 : UInt256 := (n 6) * v29
  let v31 : UInt256 := v30 + v28
  let v35 : UInt256 := UInt256.addMod v19 (UInt256.lnot v31) P
  let v36 : UInt256 := UInt256.shiftRight v35 (UInt256.ofNat 5)
  let v37 : UInt256 := UInt256.land mask v31
  let v39 : UInt256 := UInt256.shiftLeft v36 (UInt256.ofNat 12)
  let v40 : UInt256 := UInt256.shiftRight v31 (UInt256.ofNat 244)
  let v41 : UInt256 := v40 + v39
  {high := v19, low := v31, carry := v41, cancel := UInt256.ofNat 0, digit := v37}

def col14High (carry P mask minv : UInt256) (a n q : Nat → UInt256) : UInt256 := (col14Words carry P mask minv a n q).high

def col14Low (carry P mask minv : UInt256) (a n q : Nat → UInt256) : UInt256 := (col14Words carry P mask minv a n q).low

def col14Carry (carry P mask minv : UInt256) (a n q : Nat → UInt256) : UInt256 := (col14Words carry P mask minv a n q).carry

def col14Cancel (carry P mask minv : UInt256) (a n q : Nat → UInt256) : UInt256 := (col14Words carry P mask minv a n q).cancel

def col14Digit (carry P mask minv : UInt256) (a n q : Nat → UInt256) : UInt256 := (col14Words carry P mask minv a n q).digit

theorem col14_stack (s : State) (carry P n0 n1 n2 n3 n4 n5 n6 n7 n8 mask minv : UInt256) (rest : List UInt256) :
    (col14Model s carry P n0 n1 n2 n3 n4 n5 n6 n7 n8 mask minv rest).stack =
      (col14Words carry P mask minv (fun i => MachineState.readWord s.memory (768+32*i)) (fun i => match i with | 0 => n0 | 1 => n1 | 2 => n2 | 3 => n3 | 4 => n4 | 5 => n5 | 6 => n6 | 7 => n7 | _ => n8) (fun i => MachineState.readWord s.memory (1056+32*i))).carry :: P :: n0 :: n1 :: n2 :: n3 :: n4 :: n5 :: n6 :: n7 :: n8 :: mask :: minv :: rest := by rfl

#print axioms col14_stack

def col15Words (carry P mask minv : UInt256) (a n q : Nat → UInt256) : ColumnWords :=
  let v0 : UInt256 := a 8
  let v1 : UInt256 := a 7
  let v2 : UInt256 := UInt256.mulMod v0 v1 P
  let v3 : UInt256 := v0 * v1
  let v4 : UInt256 := v3 + v3
  let v5 : UInt256 := v2 + v2
  let v6 : UInt256 := carry + v5
  let v7 : UInt256 := carry + v4
  let v8 : UInt256 := q 7
  let v9 : UInt256 := UInt256.mulMod (n 8) v8 P
  let v10 : UInt256 := v9 + v6
  let v11 : UInt256 := q 8
  let v12 : UInt256 := UInt256.mulMod (n 7) v11 P
  let v13 : UInt256 := v12 + v10
  let v14 : UInt256 := q 7
  let v15 : UInt256 := (n 8) * v14
  let v16 : UInt256 := v15 + v7
  let v17 : UInt256 := q 8
  let v18 : UInt256 := (n 7) * v17
  let v19 : UInt256 := v18 + v16
  let v23 : UInt256 := UInt256.addMod v13 (UInt256.lnot v19) P
  let v24 : UInt256 := UInt256.shiftRight v23 (UInt256.ofNat 5)
  let v25 : UInt256 := UInt256.land mask v19
  let v27 : UInt256 := UInt256.shiftLeft v24 (UInt256.ofNat 12)
  let v28 : UInt256 := UInt256.shiftRight v19 (UInt256.ofNat 244)
  let v29 : UInt256 := v28 + v27
  {high := v13, low := v19, carry := v29, cancel := UInt256.ofNat 0, digit := v25}

def col15High (carry P mask minv : UInt256) (a n q : Nat → UInt256) : UInt256 := (col15Words carry P mask minv a n q).high

def col15Low (carry P mask minv : UInt256) (a n q : Nat → UInt256) : UInt256 := (col15Words carry P mask minv a n q).low

def col15Carry (carry P mask minv : UInt256) (a n q : Nat → UInt256) : UInt256 := (col15Words carry P mask minv a n q).carry

def col15Cancel (carry P mask minv : UInt256) (a n q : Nat → UInt256) : UInt256 := (col15Words carry P mask minv a n q).cancel

def col15Digit (carry P mask minv : UInt256) (a n q : Nat → UInt256) : UInt256 := (col15Words carry P mask minv a n q).digit

theorem col15_stack (s : State) (carry P n0 n1 n2 n3 n4 n5 n6 n7 n8 mask minv : UInt256) (rest : List UInt256) :
    (col15Model s carry P n0 n1 n2 n3 n4 n5 n6 n7 n8 mask minv rest).stack =
      (col15Words carry P mask minv (fun i => MachineState.readWord s.memory (768+32*i)) (fun i => match i with | 0 => n0 | 1 => n1 | 2 => n2 | 3 => n3 | 4 => n4 | 5 => n5 | 6 => n6 | 7 => n7 | _ => n8) (fun i => MachineState.readWord s.memory (1056+32*i))).carry :: P :: n0 :: n1 :: n2 :: n3 :: n4 :: n5 :: n6 :: n7 :: n8 :: mask :: minv :: rest := by rfl

#print axioms col15_stack

def col16Words (carry P mask minv : UInt256) (a n q : Nat → UInt256) : ColumnWords :=
  let v0 : UInt256 := a 8
  let v1 : UInt256 := v0 * v0
  let v2 : UInt256 := v1 + carry
  let v3 : UInt256 := q 8
  let v4 : UInt256 := (n 8) * v3
  let v5 : UInt256 := v4 + v2
  {high := UInt256.ofNat 0, low := v5, carry := UInt256.ofNat 0, cancel := UInt256.ofNat 0, digit := v5}

def col16High (carry P mask minv : UInt256) (a n q : Nat → UInt256) : UInt256 := (col16Words carry P mask minv a n q).high

def col16Low (carry P mask minv : UInt256) (a n q : Nat → UInt256) : UInt256 := (col16Words carry P mask minv a n q).low

def col16Carry (carry P mask minv : UInt256) (a n q : Nat → UInt256) : UInt256 := (col16Words carry P mask minv a n q).carry

def col16Cancel (carry P mask minv : UInt256) (a n q : Nat → UInt256) : UInt256 := (col16Words carry P mask minv a n q).cancel

def col16Digit (carry P mask minv : UInt256) (a n q : Nat → UInt256) : UInt256 := (col16Words carry P mask minv a n q).digit

theorem col16_stack (s : State) (carry P n0 n1 n2 n3 n4 n5 n6 n7 n8 mask minv : UInt256) (rest : List UInt256) :
    (col16Model s carry P n0 n1 n2 n3 n4 n5 n6 n7 n8 mask minv rest).stack =
      P :: n0 :: n1 :: n2 :: n3 :: n4 :: n5 :: n6 :: n7 :: n8 :: mask :: minv :: rest := by rfl

#print axioms col16_stack

def entrypart0Program : List Instr :=
  [.op .JUMPDEST,
   .op (.Dup ⟨14, by decide⟩),
   .push 2 1728,
   .op .MSTORE,
   .push 2 3643,
   .op (.Swap ⟨3, by decide⟩),
   .op .POP,
   .push 0 0]

def entrypart0Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 : UInt256) (rest : List UInt256) : State :=
  let v0 : ByteArray := MachineState.writeBytes s.memory (Data.Bytes.natToBytesPadded x14.toNat 32) 1728
  {s with pc := UInt256.ofNat 5627, memory := v0, stack := (UInt256.ofNat 0) :: x0 :: x1 :: x2 :: (UInt256.ofNat 3643) :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: rest}

theorem entrypart0_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 982) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions entrypart0Program {s with pc := UInt256.ofNat 5615, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: rest} =
      some (entrypart0Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 rest) := by
  have hz : ({val := 0} : UInt256) = UInt256.ofNat 0 := rfl
  have hzn : ({val := 0} : UInt256).toNat = 0 := rfl
  have hc0 : rest.length + 0 < 1024 := by omega
  have hc1 : rest.length + 1 < 1024 := by omega
  have hc2 : rest.length + 2 < 1024 := by omega
  have hc3 : rest.length + 3 < 1024 := by omega
  have hc4 : rest.length + 4 < 1024 := by omega
  have hc5 : rest.length + 5 < 1024 := by omega
  have hc6 : rest.length + 6 < 1024 := by omega
  have hc7 : rest.length + 7 < 1024 := by omega
  have hc8 : rest.length + 8 < 1024 := by omega
  have hc9 : rest.length + 9 < 1024 := by omega
  have hc10 : rest.length + 10 < 1024 := by omega
  have hc11 : rest.length + 11 < 1024 := by omega
  have hc12 : rest.length + 12 < 1024 := by omega
  have hc13 : rest.length + 13 < 1024 := by omega
  have hc14 : rest.length + 14 < 1024 := by omega
  have hc15 : rest.length + 15 < 1024 := by omega
  have hc16 : rest.length + 16 < 1024 := by omega
  have hc17 : rest.length + 17 < 1024 := by omega
  have hc18 : rest.length + 18 < 1024 := by omega
  have ha1728 : (1728 : UInt256).toNat = 1728 := rfl
  have hf1728 := HistoricalSearch.CRTMemoryBounds.activeWords_fix s 1728 32 (by decide) (by norm_num) hact
  simp [hz, hzn, entrypart0Program, entrypart0Model, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, Challenge.EvmProof.Word.literal_eq_ofNat, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8, hc9, hc10, hc11, hc12, hc13, hc14, hc15, hc16, hc17, hc18, ha1728, hf1728]

#print axioms entrypart0_run

def entrypart1Program : List Instr :=
  [.op (.Swap ⟨0, by decide⟩),
   .op .POP,
   .push 2 2720,
   .op .MLOAD,
   .push 31 28269553036454149273332760011886696253239742350009903329945699220681916415,
   .push 2 2592,
   .op .MLOAD,
   .op (.Dup ⟨1, by decide⟩)]

def entrypart1Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 : UInt256) (rest : List UInt256) : State :=
  let v0 : UInt256 := MachineState.readWord s.memory 2720
  let v1 : UInt256 := MachineState.readWord s.memory 2592
  {s with pc := UInt256.ofNat 5670, memory := s.memory, stack := (UInt256.ofNat 28269553036454149273332760011886696253239742350009903329945699220681916415) :: v1 :: (UInt256.ofNat 28269553036454149273332760011886696253239742350009903329945699220681916415) :: v0 :: x0 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: rest}

theorem entrypart1_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 982) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions entrypart1Program {s with pc := UInt256.ofNat 5627, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: rest} =
      some (entrypart1Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 rest) := by
  have hz : ({val := 0} : UInt256) = UInt256.ofNat 0 := rfl
  have hzn : ({val := 0} : UInt256).toNat = 0 := rfl
  have hc0 : rest.length + 0 < 1024 := by omega
  have hc1 : rest.length + 1 < 1024 := by omega
  have hc2 : rest.length + 2 < 1024 := by omega
  have hc3 : rest.length + 3 < 1024 := by omega
  have hc4 : rest.length + 4 < 1024 := by omega
  have hc5 : rest.length + 5 < 1024 := by omega
  have hc6 : rest.length + 6 < 1024 := by omega
  have hc7 : rest.length + 7 < 1024 := by omega
  have hc8 : rest.length + 8 < 1024 := by omega
  have hc9 : rest.length + 9 < 1024 := by omega
  have hc10 : rest.length + 10 < 1024 := by omega
  have hc11 : rest.length + 11 < 1024 := by omega
  have hc12 : rest.length + 12 < 1024 := by omega
  have hc13 : rest.length + 13 < 1024 := by omega
  have hc14 : rest.length + 14 < 1024 := by omega
  have hc15 : rest.length + 15 < 1024 := by omega
  have hc16 : rest.length + 16 < 1024 := by omega
  have hc17 : rest.length + 17 < 1024 := by omega
  have hc18 : rest.length + 18 < 1024 := by omega
  have hc19 : rest.length + 19 < 1024 := by omega
  have hc20 : rest.length + 20 < 1024 := by omega
  have ha2592 : (2592 : UInt256).toNat = 2592 := rfl
  have hf2592 := HistoricalSearch.CRTMemoryBounds.activeWords_fix s 2592 32 (by decide) (by norm_num) hact
  have ha2720 : (2720 : UInt256).toNat = 2720 := rfl
  have hf2720 := HistoricalSearch.CRTMemoryBounds.activeWords_fix s 2720 32 (by decide) (by norm_num) hact
  simp [hz, hzn, entrypart1Program, entrypart1Model, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, Challenge.EvmProof.Word.literal_eq_ofNat, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8, hc9, hc10, hc11, hc12, hc13, hc14, hc15, hc16, hc17, hc18, hc19, hc20, ha2592, hf2592, ha2720, hf2720]

#print axioms entrypart1_run

def entrypart2Program : List Instr :=
  [.op .AND,
   .push 2 768,
   .op .MSTORE,
   .push 2 2562,
   .op .MLOAD,
   .push 1 4,
   .op .SHR,
   .op (.Dup ⟨1, by decide⟩)]

def entrypart2Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 : UInt256) (rest : List UInt256) : State :=
  let v0 : UInt256 := UInt256.land x0 x1
  let v1 : ByteArray := MachineState.writeBytes s.memory (Data.Bytes.natToBytesPadded v0.toNat 32) 768
  let v2 : UInt256 := MachineState.readWord v1 2562
  let v3 : UInt256 := UInt256.shiftRight v2 (UInt256.ofNat 4)
  {s with pc := UInt256.ofNat 5683, memory := v1, stack := x2 :: v3 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: x18 :: x19 :: rest}

theorem entrypart2_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 982) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions entrypart2Program {s with pc := UInt256.ofNat 5670, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: x18 :: x19 :: rest} =
      some (entrypart2Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 rest) := by
  have hz : ({val := 0} : UInt256) = UInt256.ofNat 0 := rfl
  have hzn : ({val := 0} : UInt256).toNat = 0 := rfl
  have hc0 : rest.length + 0 < 1024 := by omega
  have hc1 : rest.length + 1 < 1024 := by omega
  have hc2 : rest.length + 2 < 1024 := by omega
  have hc3 : rest.length + 3 < 1024 := by omega
  have hc4 : rest.length + 4 < 1024 := by omega
  have hc5 : rest.length + 5 < 1024 := by omega
  have hc6 : rest.length + 6 < 1024 := by omega
  have hc7 : rest.length + 7 < 1024 := by omega
  have hc8 : rest.length + 8 < 1024 := by omega
  have hc9 : rest.length + 9 < 1024 := by omega
  have hc10 : rest.length + 10 < 1024 := by omega
  have hc11 : rest.length + 11 < 1024 := by omega
  have hc12 : rest.length + 12 < 1024 := by omega
  have hc13 : rest.length + 13 < 1024 := by omega
  have hc14 : rest.length + 14 < 1024 := by omega
  have hc15 : rest.length + 15 < 1024 := by omega
  have hc16 : rest.length + 16 < 1024 := by omega
  have hc17 : rest.length + 17 < 1024 := by omega
  have hc18 : rest.length + 18 < 1024 := by omega
  have hc19 : rest.length + 19 < 1024 := by omega
  have hc20 : rest.length + 20 < 1024 := by omega
  have ha768 : (768 : UInt256).toNat = 768 := rfl
  have hf768 := HistoricalSearch.CRTMemoryBounds.activeWords_fix s 768 32 (by decide) (by norm_num) hact
  have ha2562 : (2562 : UInt256).toNat = 2562 := rfl
  have hf2562 := HistoricalSearch.CRTMemoryBounds.activeWords_fix s 2562 32 (by decide) (by norm_num) hact
  simp [hz, hzn, entrypart2Program, entrypart2Model, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, Challenge.EvmProof.Word.literal_eq_ofNat, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8, hc9, hc10, hc11, hc12, hc13, hc14, hc15, hc16, hc17, hc18, hc19, hc20, ha768, hf768, ha2562, hf2562]

#print axioms entrypart2_run

def entrypart3Program : List Instr :=
  [.op .AND,
   .push 2 800,
   .op .MSTORE,
   .push 2 2531,
   .op .MLOAD,
   .op (.Dup ⟨1, by decide⟩),
   .op .AND,
   .push 2 832,
   .op .MSTORE]

def entrypart3Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 : UInt256) (rest : List UInt256) : State :=
  let v0 : UInt256 := UInt256.land x0 x1
  let v1 : ByteArray := MachineState.writeBytes s.memory (Data.Bytes.natToBytesPadded v0.toNat 32) 800
  let v2 : UInt256 := MachineState.readWord v1 2531
  let v3 : UInt256 := UInt256.land x2 v2
  let v4 : ByteArray := MachineState.writeBytes v1 (Data.Bytes.natToBytesPadded v3.toNat 32) 832
  {s with pc := UInt256.ofNat 5698, memory := v4, stack := x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: x18 :: x19 :: rest}

theorem entrypart3_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 982) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions entrypart3Program {s with pc := UInt256.ofNat 5683, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: x18 :: x19 :: rest} =
      some (entrypart3Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 rest) := by
  have hz : ({val := 0} : UInt256) = UInt256.ofNat 0 := rfl
  have hzn : ({val := 0} : UInt256).toNat = 0 := rfl
  have hc0 : rest.length + 0 < 1024 := by omega
  have hc1 : rest.length + 1 < 1024 := by omega
  have hc2 : rest.length + 2 < 1024 := by omega
  have hc3 : rest.length + 3 < 1024 := by omega
  have hc4 : rest.length + 4 < 1024 := by omega
  have hc5 : rest.length + 5 < 1024 := by omega
  have hc6 : rest.length + 6 < 1024 := by omega
  have hc7 : rest.length + 7 < 1024 := by omega
  have hc8 : rest.length + 8 < 1024 := by omega
  have hc9 : rest.length + 9 < 1024 := by omega
  have hc10 : rest.length + 10 < 1024 := by omega
  have hc11 : rest.length + 11 < 1024 := by omega
  have hc12 : rest.length + 12 < 1024 := by omega
  have hc13 : rest.length + 13 < 1024 := by omega
  have hc14 : rest.length + 14 < 1024 := by omega
  have hc15 : rest.length + 15 < 1024 := by omega
  have hc16 : rest.length + 16 < 1024 := by omega
  have hc17 : rest.length + 17 < 1024 := by omega
  have hc18 : rest.length + 18 < 1024 := by omega
  have hc19 : rest.length + 19 < 1024 := by omega
  have hc20 : rest.length + 20 < 1024 := by omega
  have ha800 : (800 : UInt256).toNat = 800 := rfl
  have hf800 := HistoricalSearch.CRTMemoryBounds.activeWords_fix s 800 32 (by decide) (by norm_num) hact
  have ha832 : (832 : UInt256).toNat = 832 := rfl
  have hf832 := HistoricalSearch.CRTMemoryBounds.activeWords_fix s 832 32 (by decide) (by norm_num) hact
  have ha2531 : (2531 : UInt256).toNat = 2531 := rfl
  have hf2531 := HistoricalSearch.CRTMemoryBounds.activeWords_fix s 2531 32 (by decide) (by norm_num) hact
  simp [hz, hzn, entrypart3Program, entrypart3Model, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, Challenge.EvmProof.Word.literal_eq_ofNat, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8, hc9, hc10, hc11, hc12, hc13, hc14, hc15, hc16, hc17, hc18, hc19, hc20, ha800, hf800, ha832, hf832, ha2531, hf2531]

#print axioms entrypart3_run

def entrypart4Program : List Instr :=
  [.push 2 2501,
   .op .MLOAD,
   .push 1 4,
   .op .SHR,
   .op (.Dup ⟨1, by decide⟩),
   .op .AND,
   .push 2 864,
   .op .MSTORE]

def entrypart4Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 : UInt256) (rest : List UInt256) : State :=
  let v0 : UInt256 := MachineState.readWord s.memory 2501
  let v1 : UInt256 := UInt256.shiftRight v0 (UInt256.ofNat 4)
  let v2 : UInt256 := UInt256.land x0 v1
  let v3 : ByteArray := MachineState.writeBytes s.memory (Data.Bytes.natToBytesPadded v2.toNat 32) 864
  {s with pc := UInt256.ofNat 5711, memory := v3, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: rest}

theorem entrypart4_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 982) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions entrypart4Program {s with pc := UInt256.ofNat 5698, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: rest} =
      some (entrypart4Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 rest) := by
  have hz : ({val := 0} : UInt256) = UInt256.ofNat 0 := rfl
  have hzn : ({val := 0} : UInt256).toNat = 0 := rfl
  have hc0 : rest.length + 0 < 1024 := by omega
  have hc1 : rest.length + 1 < 1024 := by omega
  have hc2 : rest.length + 2 < 1024 := by omega
  have hc3 : rest.length + 3 < 1024 := by omega
  have hc4 : rest.length + 4 < 1024 := by omega
  have hc5 : rest.length + 5 < 1024 := by omega
  have hc6 : rest.length + 6 < 1024 := by omega
  have hc7 : rest.length + 7 < 1024 := by omega
  have hc8 : rest.length + 8 < 1024 := by omega
  have hc9 : rest.length + 9 < 1024 := by omega
  have hc10 : rest.length + 10 < 1024 := by omega
  have hc11 : rest.length + 11 < 1024 := by omega
  have hc12 : rest.length + 12 < 1024 := by omega
  have hc13 : rest.length + 13 < 1024 := by omega
  have hc14 : rest.length + 14 < 1024 := by omega
  have hc15 : rest.length + 15 < 1024 := by omega
  have hc16 : rest.length + 16 < 1024 := by omega
  have hc17 : rest.length + 17 < 1024 := by omega
  have hc18 : rest.length + 18 < 1024 := by omega
  have hc19 : rest.length + 19 < 1024 := by omega
  have hc20 : rest.length + 20 < 1024 := by omega
  have ha864 : (864 : UInt256).toNat = 864 := rfl
  have hf864 := HistoricalSearch.CRTMemoryBounds.activeWords_fix s 864 32 (by decide) (by norm_num) hact
  have ha2501 : (2501 : UInt256).toNat = 2501 := rfl
  have hf2501 := HistoricalSearch.CRTMemoryBounds.activeWords_fix s 2501 32 (by decide) (by norm_num) hact
  simp [hz, hzn, entrypart4Program, entrypart4Model, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, Challenge.EvmProof.Word.literal_eq_ofNat, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8, hc9, hc10, hc11, hc12, hc13, hc14, hc15, hc16, hc17, hc18, hc19, hc20, ha864, hf864, ha2501, hf2501]

#print axioms entrypart4_run

def entrypart5Program : List Instr :=
  [.push 2 2470,
   .op .MLOAD,
   .op (.Dup ⟨1, by decide⟩),
   .op .AND,
   .push 2 896,
   .op .MSTORE,
   .push 2 2440,
   .op .MLOAD]

def entrypart5Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 : UInt256) (rest : List UInt256) : State :=
  let v0 : UInt256 := MachineState.readWord s.memory 2470
  let v1 : UInt256 := UInt256.land x0 v0
  let v2 : ByteArray := MachineState.writeBytes s.memory (Data.Bytes.natToBytesPadded v1.toNat 32) 896
  let v3 : UInt256 := MachineState.readWord v2 2440
  {s with pc := UInt256.ofNat 5725, memory := v2, stack := v3 :: x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: rest}

theorem entrypart5_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 982) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions entrypart5Program {s with pc := UInt256.ofNat 5711, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: rest} =
      some (entrypart5Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 rest) := by
  have hz : ({val := 0} : UInt256) = UInt256.ofNat 0 := rfl
  have hzn : ({val := 0} : UInt256).toNat = 0 := rfl
  have hc0 : rest.length + 0 < 1024 := by omega
  have hc1 : rest.length + 1 < 1024 := by omega
  have hc2 : rest.length + 2 < 1024 := by omega
  have hc3 : rest.length + 3 < 1024 := by omega
  have hc4 : rest.length + 4 < 1024 := by omega
  have hc5 : rest.length + 5 < 1024 := by omega
  have hc6 : rest.length + 6 < 1024 := by omega
  have hc7 : rest.length + 7 < 1024 := by omega
  have hc8 : rest.length + 8 < 1024 := by omega
  have hc9 : rest.length + 9 < 1024 := by omega
  have hc10 : rest.length + 10 < 1024 := by omega
  have hc11 : rest.length + 11 < 1024 := by omega
  have hc12 : rest.length + 12 < 1024 := by omega
  have hc13 : rest.length + 13 < 1024 := by omega
  have hc14 : rest.length + 14 < 1024 := by omega
  have hc15 : rest.length + 15 < 1024 := by omega
  have hc16 : rest.length + 16 < 1024 := by omega
  have hc17 : rest.length + 17 < 1024 := by omega
  have hc18 : rest.length + 18 < 1024 := by omega
  have hc19 : rest.length + 19 < 1024 := by omega
  have hc20 : rest.length + 20 < 1024 := by omega
  have ha896 : (896 : UInt256).toNat = 896 := rfl
  have hf896 := HistoricalSearch.CRTMemoryBounds.activeWords_fix s 896 32 (by decide) (by norm_num) hact
  have ha2440 : (2440 : UInt256).toNat = 2440 := rfl
  have hf2440 := HistoricalSearch.CRTMemoryBounds.activeWords_fix s 2440 32 (by decide) (by norm_num) hact
  have ha2470 : (2470 : UInt256).toNat = 2470 := rfl
  have hf2470 := HistoricalSearch.CRTMemoryBounds.activeWords_fix s 2470 32 (by decide) (by norm_num) hact
  simp [hz, hzn, entrypart5Program, entrypart5Model, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, Challenge.EvmProof.Word.literal_eq_ofNat, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8, hc9, hc10, hc11, hc12, hc13, hc14, hc15, hc16, hc17, hc18, hc19, hc20, ha896, hf896, ha2440, hf2440, ha2470, hf2470]

#print axioms entrypart5_run

def entrypart6Program : List Instr :=
  [.push 1 4,
   .op .SHR,
   .op (.Dup ⟨1, by decide⟩),
   .op .AND,
   .push 2 928,
   .op .MSTORE,
   .push 2 2409,
   .op .MLOAD]

def entrypart6Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 : UInt256) (rest : List UInt256) : State :=
  let v0 : UInt256 := UInt256.shiftRight x0 (UInt256.ofNat 4)
  let v1 : UInt256 := UInt256.land x1 v0
  let v2 : ByteArray := MachineState.writeBytes s.memory (Data.Bytes.natToBytesPadded v1.toNat 32) 928
  let v3 : UInt256 := MachineState.readWord v2 2409
  {s with pc := UInt256.ofNat 5738, memory := v2, stack := v3 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: x18 :: rest}

theorem entrypart6_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 982) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions entrypart6Program {s with pc := UInt256.ofNat 5725, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: x18 :: rest} =
      some (entrypart6Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 rest) := by
  have hz : ({val := 0} : UInt256) = UInt256.ofNat 0 := rfl
  have hzn : ({val := 0} : UInt256).toNat = 0 := rfl
  have hc0 : rest.length + 0 < 1024 := by omega
  have hc1 : rest.length + 1 < 1024 := by omega
  have hc2 : rest.length + 2 < 1024 := by omega
  have hc3 : rest.length + 3 < 1024 := by omega
  have hc4 : rest.length + 4 < 1024 := by omega
  have hc5 : rest.length + 5 < 1024 := by omega
  have hc6 : rest.length + 6 < 1024 := by omega
  have hc7 : rest.length + 7 < 1024 := by omega
  have hc8 : rest.length + 8 < 1024 := by omega
  have hc9 : rest.length + 9 < 1024 := by omega
  have hc10 : rest.length + 10 < 1024 := by omega
  have hc11 : rest.length + 11 < 1024 := by omega
  have hc12 : rest.length + 12 < 1024 := by omega
  have hc13 : rest.length + 13 < 1024 := by omega
  have hc14 : rest.length + 14 < 1024 := by omega
  have hc15 : rest.length + 15 < 1024 := by omega
  have hc16 : rest.length + 16 < 1024 := by omega
  have hc17 : rest.length + 17 < 1024 := by omega
  have hc18 : rest.length + 18 < 1024 := by omega
  have hc19 : rest.length + 19 < 1024 := by omega
  have hc20 : rest.length + 20 < 1024 := by omega
  have ha928 : (928 : UInt256).toNat = 928 := rfl
  have hf928 := HistoricalSearch.CRTMemoryBounds.activeWords_fix s 928 32 (by decide) (by norm_num) hact
  have ha2409 : (2409 : UInt256).toNat = 2409 := rfl
  have hf2409 := HistoricalSearch.CRTMemoryBounds.activeWords_fix s 2409 32 (by decide) (by norm_num) hact
  simp [hz, hzn, entrypart6Program, entrypart6Model, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, Challenge.EvmProof.Word.literal_eq_ofNat, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8, hc9, hc10, hc11, hc12, hc13, hc14, hc15, hc16, hc17, hc18, hc19, hc20, ha928, hf928, ha2409, hf2409]

#print axioms entrypart6_run

def entrypart7Program : List Instr :=
  [.op (.Dup ⟨1, by decide⟩),
   .op .AND,
   .push 2 960,
   .op .MSTORE,
   .push 2 2379,
   .op .MLOAD,
   .push 1 4,
   .op .SHR]

def entrypart7Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 : UInt256) (rest : List UInt256) : State :=
  let v0 : UInt256 := UInt256.land x1 x0
  let v1 : ByteArray := MachineState.writeBytes s.memory (Data.Bytes.natToBytesPadded v0.toNat 32) 960
  let v2 : UInt256 := MachineState.readWord v1 2379
  let v3 : UInt256 := UInt256.shiftRight v2 (UInt256.ofNat 4)
  {s with pc := UInt256.ofNat 5751, memory := v1, stack := v3 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: x18 :: rest}

theorem entrypart7_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 982) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions entrypart7Program {s with pc := UInt256.ofNat 5738, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: x18 :: rest} =
      some (entrypart7Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 rest) := by
  have hz : ({val := 0} : UInt256) = UInt256.ofNat 0 := rfl
  have hzn : ({val := 0} : UInt256).toNat = 0 := rfl
  have hc0 : rest.length + 0 < 1024 := by omega
  have hc1 : rest.length + 1 < 1024 := by omega
  have hc2 : rest.length + 2 < 1024 := by omega
  have hc3 : rest.length + 3 < 1024 := by omega
  have hc4 : rest.length + 4 < 1024 := by omega
  have hc5 : rest.length + 5 < 1024 := by omega
  have hc6 : rest.length + 6 < 1024 := by omega
  have hc7 : rest.length + 7 < 1024 := by omega
  have hc8 : rest.length + 8 < 1024 := by omega
  have hc9 : rest.length + 9 < 1024 := by omega
  have hc10 : rest.length + 10 < 1024 := by omega
  have hc11 : rest.length + 11 < 1024 := by omega
  have hc12 : rest.length + 12 < 1024 := by omega
  have hc13 : rest.length + 13 < 1024 := by omega
  have hc14 : rest.length + 14 < 1024 := by omega
  have hc15 : rest.length + 15 < 1024 := by omega
  have hc16 : rest.length + 16 < 1024 := by omega
  have hc17 : rest.length + 17 < 1024 := by omega
  have hc18 : rest.length + 18 < 1024 := by omega
  have hc19 : rest.length + 19 < 1024 := by omega
  have hc20 : rest.length + 20 < 1024 := by omega
  have ha960 : (960 : UInt256).toNat = 960 := rfl
  have hf960 := HistoricalSearch.CRTMemoryBounds.activeWords_fix s 960 32 (by decide) (by norm_num) hact
  have ha2379 : (2379 : UInt256).toNat = 2379 := rfl
  have hf2379 := HistoricalSearch.CRTMemoryBounds.activeWords_fix s 2379 32 (by decide) (by norm_num) hact
  simp [hz, hzn, entrypart7Program, entrypart7Model, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, Challenge.EvmProof.Word.literal_eq_ofNat, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8, hc9, hc10, hc11, hc12, hc13, hc14, hc15, hc16, hc17, hc18, hc19, hc20, ha960, hf960, ha2379, hf2379]

#print axioms entrypart7_run

def entrypart8Program : List Instr :=
  [.op (.Dup ⟨1, by decide⟩),
   .op .AND,
   .push 2 992,
   .op .MSTORE,
   .push 2 2368,
   .op .MLOAD,
   .push 1 160,
   .op .SHR]

def entrypart8Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 : UInt256) (rest : List UInt256) : State :=
  let v0 : UInt256 := UInt256.land x1 x0
  let v1 : ByteArray := MachineState.writeBytes s.memory (Data.Bytes.natToBytesPadded v0.toNat 32) 992
  let v2 : UInt256 := MachineState.readWord v1 2368
  let v3 : UInt256 := UInt256.shiftRight v2 (UInt256.ofNat 160)
  {s with pc := UInt256.ofNat 5764, memory := v1, stack := v3 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: x18 :: rest}

theorem entrypart8_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 982) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions entrypart8Program {s with pc := UInt256.ofNat 5751, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: x18 :: rest} =
      some (entrypart8Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 rest) := by
  have hz : ({val := 0} : UInt256) = UInt256.ofNat 0 := rfl
  have hzn : ({val := 0} : UInt256).toNat = 0 := rfl
  have hc0 : rest.length + 0 < 1024 := by omega
  have hc1 : rest.length + 1 < 1024 := by omega
  have hc2 : rest.length + 2 < 1024 := by omega
  have hc3 : rest.length + 3 < 1024 := by omega
  have hc4 : rest.length + 4 < 1024 := by omega
  have hc5 : rest.length + 5 < 1024 := by omega
  have hc6 : rest.length + 6 < 1024 := by omega
  have hc7 : rest.length + 7 < 1024 := by omega
  have hc8 : rest.length + 8 < 1024 := by omega
  have hc9 : rest.length + 9 < 1024 := by omega
  have hc10 : rest.length + 10 < 1024 := by omega
  have hc11 : rest.length + 11 < 1024 := by omega
  have hc12 : rest.length + 12 < 1024 := by omega
  have hc13 : rest.length + 13 < 1024 := by omega
  have hc14 : rest.length + 14 < 1024 := by omega
  have hc15 : rest.length + 15 < 1024 := by omega
  have hc16 : rest.length + 16 < 1024 := by omega
  have hc17 : rest.length + 17 < 1024 := by omega
  have hc18 : rest.length + 18 < 1024 := by omega
  have hc19 : rest.length + 19 < 1024 := by omega
  have hc20 : rest.length + 20 < 1024 := by omega
  have ha992 : (992 : UInt256).toNat = 992 := rfl
  have hf992 := HistoricalSearch.CRTMemoryBounds.activeWords_fix s 992 32 (by decide) (by norm_num) hact
  have ha2368 : (2368 : UInt256).toNat = 2368 := rfl
  have hf2368 := HistoricalSearch.CRTMemoryBounds.activeWords_fix s 2368 32 (by decide) (by norm_num) hact
  simp [hz, hzn, entrypart8Program, entrypart8Model, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, Challenge.EvmProof.Word.literal_eq_ofNat, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8, hc9, hc10, hc11, hc12, hc13, hc14, hc15, hc16, hc17, hc18, hc19, hc20, ha992, hf992, ha2368, hf2368]

#print axioms entrypart8_run

def entrypart9Program : List Instr :=
  [.push 2 1024,
   .op .MSTORE,
   .push 0 0,
   .op .MLOAD,
   .push 1 160,
   .op .SHR,
   .push 1 11,
   .op .MLOAD]

def entrypart9Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 : UInt256) (rest : List UInt256) : State :=
  let v0 : ByteArray := MachineState.writeBytes s.memory (Data.Bytes.natToBytesPadded x0.toNat 32) 1024
  let v1 : UInt256 := MachineState.readWord v0 0
  let v2 : UInt256 := UInt256.shiftRight v1 (UInt256.ofNat 160)
  let v3 : UInt256 := MachineState.readWord v0 11
  {s with pc := UInt256.ofNat 5776, memory := v0, stack := v3 :: v2 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: x18 :: rest}

theorem entrypart9_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 982) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions entrypart9Program {s with pc := UInt256.ofNat 5764, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: x18 :: rest} =
      some (entrypart9Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 rest) := by
  have hz : ({val := 0} : UInt256) = UInt256.ofNat 0 := rfl
  have hzn : ({val := 0} : UInt256).toNat = 0 := rfl
  have hc0 : rest.length + 0 < 1024 := by omega
  have hc1 : rest.length + 1 < 1024 := by omega
  have hc2 : rest.length + 2 < 1024 := by omega
  have hc3 : rest.length + 3 < 1024 := by omega
  have hc4 : rest.length + 4 < 1024 := by omega
  have hc5 : rest.length + 5 < 1024 := by omega
  have hc6 : rest.length + 6 < 1024 := by omega
  have hc7 : rest.length + 7 < 1024 := by omega
  have hc8 : rest.length + 8 < 1024 := by omega
  have hc9 : rest.length + 9 < 1024 := by omega
  have hc10 : rest.length + 10 < 1024 := by omega
  have hc11 : rest.length + 11 < 1024 := by omega
  have hc12 : rest.length + 12 < 1024 := by omega
  have hc13 : rest.length + 13 < 1024 := by omega
  have hc14 : rest.length + 14 < 1024 := by omega
  have hc15 : rest.length + 15 < 1024 := by omega
  have hc16 : rest.length + 16 < 1024 := by omega
  have hc17 : rest.length + 17 < 1024 := by omega
  have hc18 : rest.length + 18 < 1024 := by omega
  have hc19 : rest.length + 19 < 1024 := by omega
  have hc20 : rest.length + 20 < 1024 := by omega
  have ha0 : (0 : UInt256).toNat = 0 := rfl
  have hf0 := HistoricalSearch.CRTMemoryBounds.activeWords_fix s 0 32 (by decide) (by norm_num) hact
  have ha11 : (11 : UInt256).toNat = 11 := rfl
  have hf11 := HistoricalSearch.CRTMemoryBounds.activeWords_fix s 11 32 (by decide) (by norm_num) hact
  have ha1024 : (1024 : UInt256).toNat = 1024 := rfl
  have hf1024 := HistoricalSearch.CRTMemoryBounds.activeWords_fix s 1024 32 (by decide) (by norm_num) hact
  simp [hz, hzn, entrypart9Program, entrypart9Model, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, Challenge.EvmProof.Word.literal_eq_ofNat, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8, hc9, hc10, hc11, hc12, hc13, hc14, hc15, hc16, hc17, hc18, hc19, hc20, ha0, hf0, ha11, hf11, ha1024, hf1024]

#print axioms entrypart9_run

def entrypart10Program : List Instr :=
  [.push 1 4,
   .op .SHR,
   .op (.Dup ⟨2, by decide⟩),
   .op .AND,
   .push 1 41,
   .op .MLOAD,
   .op (.Dup ⟨3, by decide⟩),
   .op .AND]

def entrypart10Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 : UInt256) (rest : List UInt256) : State :=
  let v0 : UInt256 := UInt256.shiftRight x0 (UInt256.ofNat 4)
  let v1 : UInt256 := UInt256.land x2 v0
  let v2 : UInt256 := MachineState.readWord s.memory 41
  let v3 : UInt256 := UInt256.land x2 v2
  {s with pc := UInt256.ofNat 5786, memory := s.memory, stack := v3 :: v1 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: x18 :: x19 :: rest}

theorem entrypart10_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 982) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions entrypart10Program {s with pc := UInt256.ofNat 5776, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: x18 :: x19 :: rest} =
      some (entrypart10Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 rest) := by
  have hz : ({val := 0} : UInt256) = UInt256.ofNat 0 := rfl
  have hzn : ({val := 0} : UInt256).toNat = 0 := rfl
  have hc0 : rest.length + 0 < 1024 := by omega
  have hc1 : rest.length + 1 < 1024 := by omega
  have hc2 : rest.length + 2 < 1024 := by omega
  have hc3 : rest.length + 3 < 1024 := by omega
  have hc4 : rest.length + 4 < 1024 := by omega
  have hc5 : rest.length + 5 < 1024 := by omega
  have hc6 : rest.length + 6 < 1024 := by omega
  have hc7 : rest.length + 7 < 1024 := by omega
  have hc8 : rest.length + 8 < 1024 := by omega
  have hc9 : rest.length + 9 < 1024 := by omega
  have hc10 : rest.length + 10 < 1024 := by omega
  have hc11 : rest.length + 11 < 1024 := by omega
  have hc12 : rest.length + 12 < 1024 := by omega
  have hc13 : rest.length + 13 < 1024 := by omega
  have hc14 : rest.length + 14 < 1024 := by omega
  have hc15 : rest.length + 15 < 1024 := by omega
  have hc16 : rest.length + 16 < 1024 := by omega
  have hc17 : rest.length + 17 < 1024 := by omega
  have hc18 : rest.length + 18 < 1024 := by omega
  have hc19 : rest.length + 19 < 1024 := by omega
  have hc20 : rest.length + 20 < 1024 := by omega
  have hc21 : rest.length + 21 < 1024 := by omega
  have hc22 : rest.length + 22 < 1024 := by omega
  have ha41 : (41 : UInt256).toNat = 41 := rfl
  have hf41 := HistoricalSearch.CRTMemoryBounds.activeWords_fix s 41 32 (by decide) (by norm_num) hact
  simp [hz, hzn, entrypart10Program, entrypart10Model, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, Challenge.EvmProof.Word.literal_eq_ofNat, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8, hc9, hc10, hc11, hc12, hc13, hc14, hc15, hc16, hc17, hc18, hc19, hc20, hc21, hc22, ha41, hf41]

#print axioms entrypart10_run

def entrypart11Program : List Instr :=
  [.push 1 72,
   .op .MLOAD,
   .push 1 4,
   .op .SHR,
   .op (.Dup ⟨4, by decide⟩),
   .op .AND,
   .push 1 102,
   .op .MLOAD]

def entrypart11Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 : UInt256) (rest : List UInt256) : State :=
  let v0 : UInt256 := MachineState.readWord s.memory 72
  let v1 : UInt256 := UInt256.shiftRight v0 (UInt256.ofNat 4)
  let v2 : UInt256 := UInt256.land x3 v1
  let v3 : UInt256 := MachineState.readWord s.memory 102
  {s with pc := UInt256.ofNat 5797, memory := s.memory, stack := v3 :: v2 :: x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: x18 :: x19 :: x20 :: rest}

theorem entrypart11_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 982) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions entrypart11Program {s with pc := UInt256.ofNat 5786, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: x18 :: x19 :: x20 :: rest} =
      some (entrypart11Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 rest) := by
  have hz : ({val := 0} : UInt256) = UInt256.ofNat 0 := rfl
  have hzn : ({val := 0} : UInt256).toNat = 0 := rfl
  have hc0 : rest.length + 0 < 1024 := by omega
  have hc1 : rest.length + 1 < 1024 := by omega
  have hc2 : rest.length + 2 < 1024 := by omega
  have hc3 : rest.length + 3 < 1024 := by omega
  have hc4 : rest.length + 4 < 1024 := by omega
  have hc5 : rest.length + 5 < 1024 := by omega
  have hc6 : rest.length + 6 < 1024 := by omega
  have hc7 : rest.length + 7 < 1024 := by omega
  have hc8 : rest.length + 8 < 1024 := by omega
  have hc9 : rest.length + 9 < 1024 := by omega
  have hc10 : rest.length + 10 < 1024 := by omega
  have hc11 : rest.length + 11 < 1024 := by omega
  have hc12 : rest.length + 12 < 1024 := by omega
  have hc13 : rest.length + 13 < 1024 := by omega
  have hc14 : rest.length + 14 < 1024 := by omega
  have hc15 : rest.length + 15 < 1024 := by omega
  have hc16 : rest.length + 16 < 1024 := by omega
  have hc17 : rest.length + 17 < 1024 := by omega
  have hc18 : rest.length + 18 < 1024 := by omega
  have hc19 : rest.length + 19 < 1024 := by omega
  have hc20 : rest.length + 20 < 1024 := by omega
  have hc21 : rest.length + 21 < 1024 := by omega
  have hc22 : rest.length + 22 < 1024 := by omega
  have hc23 : rest.length + 23 < 1024 := by omega
  have ha72 : (72 : UInt256).toNat = 72 := rfl
  have hf72 := HistoricalSearch.CRTMemoryBounds.activeWords_fix s 72 32 (by decide) (by norm_num) hact
  have ha102 : (102 : UInt256).toNat = 102 := rfl
  have hf102 := HistoricalSearch.CRTMemoryBounds.activeWords_fix s 102 32 (by decide) (by norm_num) hact
  simp [hz, hzn, entrypart11Program, entrypart11Model, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, Challenge.EvmProof.Word.literal_eq_ofNat, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8, hc9, hc10, hc11, hc12, hc13, hc14, hc15, hc16, hc17, hc18, hc19, hc20, hc21, hc22, hc23, ha72, hf72, ha102, hf102]

#print axioms entrypart11_run

def entrypart12Program : List Instr :=
  [.op (.Dup ⟨5, by decide⟩),
   .op .AND,
   .push 1 133,
   .op .MLOAD,
   .push 1 4,
   .op .SHR,
   .op (.Dup ⟨6, by decide⟩),
   .op .AND]

def entrypart12Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 : UInt256) (rest : List UInt256) : State :=
  let v0 : UInt256 := UInt256.land x5 x0
  let v1 : UInt256 := MachineState.readWord s.memory 133
  let v2 : UInt256 := UInt256.shiftRight v1 (UInt256.ofNat 4)
  let v3 : UInt256 := UInt256.land x5 v2
  {s with pc := UInt256.ofNat 5807, memory := s.memory, stack := v3 :: v0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: x18 :: x19 :: x20 :: x21 :: x22 :: rest}

theorem entrypart12_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 982) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions entrypart12Program {s with pc := UInt256.ofNat 5797, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: x18 :: x19 :: x20 :: x21 :: x22 :: rest} =
      some (entrypart12Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 rest) := by
  have hz : ({val := 0} : UInt256) = UInt256.ofNat 0 := rfl
  have hzn : ({val := 0} : UInt256).toNat = 0 := rfl
  have hc0 : rest.length + 0 < 1024 := by omega
  have hc1 : rest.length + 1 < 1024 := by omega
  have hc2 : rest.length + 2 < 1024 := by omega
  have hc3 : rest.length + 3 < 1024 := by omega
  have hc4 : rest.length + 4 < 1024 := by omega
  have hc5 : rest.length + 5 < 1024 := by omega
  have hc6 : rest.length + 6 < 1024 := by omega
  have hc7 : rest.length + 7 < 1024 := by omega
  have hc8 : rest.length + 8 < 1024 := by omega
  have hc9 : rest.length + 9 < 1024 := by omega
  have hc10 : rest.length + 10 < 1024 := by omega
  have hc11 : rest.length + 11 < 1024 := by omega
  have hc12 : rest.length + 12 < 1024 := by omega
  have hc13 : rest.length + 13 < 1024 := by omega
  have hc14 : rest.length + 14 < 1024 := by omega
  have hc15 : rest.length + 15 < 1024 := by omega
  have hc16 : rest.length + 16 < 1024 := by omega
  have hc17 : rest.length + 17 < 1024 := by omega
  have hc18 : rest.length + 18 < 1024 := by omega
  have hc19 : rest.length + 19 < 1024 := by omega
  have hc20 : rest.length + 20 < 1024 := by omega
  have hc21 : rest.length + 21 < 1024 := by omega
  have hc22 : rest.length + 22 < 1024 := by omega
  have hc23 : rest.length + 23 < 1024 := by omega
  have hc24 : rest.length + 24 < 1024 := by omega
  have hc25 : rest.length + 25 < 1024 := by omega
  have ha133 : (133 : UInt256).toNat = 133 := rfl
  have hf133 := HistoricalSearch.CRTMemoryBounds.activeWords_fix s 133 32 (by decide) (by norm_num) hact
  simp [hz, hzn, entrypart12Program, entrypart12Model, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, Challenge.EvmProof.Word.literal_eq_ofNat, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8, hc9, hc10, hc11, hc12, hc13, hc14, hc15, hc16, hc17, hc18, hc19, hc20, hc21, hc22, hc23, hc24, hc25, ha133, hf133]

#print axioms entrypart12_run

def entrypart13Program : List Instr :=
  [.push 1 163,
   .op .MLOAD,
   .op (.Dup ⟨7, by decide⟩),
   .op .AND,
   .push 1 194,
   .op .MLOAD,
   .push 1 4,
   .op .SHR]

def entrypart13Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 : UInt256) (rest : List UInt256) : State :=
  let v0 : UInt256 := MachineState.readWord s.memory 163
  let v1 : UInt256 := UInt256.land x6 v0
  let v2 : UInt256 := MachineState.readWord s.memory 194
  let v3 : UInt256 := UInt256.shiftRight v2 (UInt256.ofNat 4)
  {s with pc := UInt256.ofNat 5818, memory := s.memory, stack := v3 :: v1 :: x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: x18 :: x19 :: x20 :: x21 :: x22 :: x23 :: rest}

theorem entrypart13_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 982) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions entrypart13Program {s with pc := UInt256.ofNat 5807, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: x18 :: x19 :: x20 :: x21 :: x22 :: x23 :: rest} =
      some (entrypart13Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 rest) := by
  have hz : ({val := 0} : UInt256) = UInt256.ofNat 0 := rfl
  have hzn : ({val := 0} : UInt256).toNat = 0 := rfl
  have hc0 : rest.length + 0 < 1024 := by omega
  have hc1 : rest.length + 1 < 1024 := by omega
  have hc2 : rest.length + 2 < 1024 := by omega
  have hc3 : rest.length + 3 < 1024 := by omega
  have hc4 : rest.length + 4 < 1024 := by omega
  have hc5 : rest.length + 5 < 1024 := by omega
  have hc6 : rest.length + 6 < 1024 := by omega
  have hc7 : rest.length + 7 < 1024 := by omega
  have hc8 : rest.length + 8 < 1024 := by omega
  have hc9 : rest.length + 9 < 1024 := by omega
  have hc10 : rest.length + 10 < 1024 := by omega
  have hc11 : rest.length + 11 < 1024 := by omega
  have hc12 : rest.length + 12 < 1024 := by omega
  have hc13 : rest.length + 13 < 1024 := by omega
  have hc14 : rest.length + 14 < 1024 := by omega
  have hc15 : rest.length + 15 < 1024 := by omega
  have hc16 : rest.length + 16 < 1024 := by omega
  have hc17 : rest.length + 17 < 1024 := by omega
  have hc18 : rest.length + 18 < 1024 := by omega
  have hc19 : rest.length + 19 < 1024 := by omega
  have hc20 : rest.length + 20 < 1024 := by omega
  have hc21 : rest.length + 21 < 1024 := by omega
  have hc22 : rest.length + 22 < 1024 := by omega
  have hc23 : rest.length + 23 < 1024 := by omega
  have hc24 : rest.length + 24 < 1024 := by omega
  have hc25 : rest.length + 25 < 1024 := by omega
  have hc26 : rest.length + 26 < 1024 := by omega
  have hc27 : rest.length + 27 < 1024 := by omega
  have ha163 : (163 : UInt256).toNat = 163 := rfl
  have hf163 := HistoricalSearch.CRTMemoryBounds.activeWords_fix s 163 32 (by decide) (by norm_num) hact
  have ha194 : (194 : UInt256).toNat = 194 := rfl
  have hf194 := HistoricalSearch.CRTMemoryBounds.activeWords_fix s 194 32 (by decide) (by norm_num) hact
  simp [hz, hzn, entrypart13Program, entrypart13Model, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, Challenge.EvmProof.Word.literal_eq_ofNat, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8, hc9, hc10, hc11, hc12, hc13, hc14, hc15, hc16, hc17, hc18, hc19, hc20, hc21, hc22, hc23, hc24, hc25, hc26, hc27, ha163, hf163, ha194, hf194]

#print axioms entrypart13_run

def entrypart14Program : List Instr :=
  [.op (.Dup ⟨8, by decide⟩),
   .op .AND,
   .push 1 224,
   .op .MLOAD,
   .op (.Dup ⟨9, by decide⟩),
   .op .AND,
   .push 32 3618502788666131106986593281521497120414687020801267626233049500247285301247,
   .op .JUMPDEST]

def entrypart14Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 : UInt256) (rest : List UInt256) : State :=
  let v0 : UInt256 := UInt256.land x8 x0
  let v1 : UInt256 := MachineState.readWord s.memory 224
  let v2 : UInt256 := UInt256.land x8 v1
  {s with pc := UInt256.ofNat 5859, memory := s.memory, stack := (UInt256.ofNat 3618502788666131106986593281521497120414687020801267626233049500247285301247) :: v2 :: v0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: x18 :: x19 :: x20 :: x21 :: x22 :: x23 :: x24 :: x25 :: rest}

theorem entrypart14_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 982) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions entrypart14Program {s with pc := UInt256.ofNat 5818, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: x18 :: x19 :: x20 :: x21 :: x22 :: x23 :: x24 :: x25 :: rest} =
      some (entrypart14Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 rest) := by
  have hz : ({val := 0} : UInt256) = UInt256.ofNat 0 := rfl
  have hzn : ({val := 0} : UInt256).toNat = 0 := rfl
  have hc0 : rest.length + 0 < 1024 := by omega
  have hc1 : rest.length + 1 < 1024 := by omega
  have hc2 : rest.length + 2 < 1024 := by omega
  have hc3 : rest.length + 3 < 1024 := by omega
  have hc4 : rest.length + 4 < 1024 := by omega
  have hc5 : rest.length + 5 < 1024 := by omega
  have hc6 : rest.length + 6 < 1024 := by omega
  have hc7 : rest.length + 7 < 1024 := by omega
  have hc8 : rest.length + 8 < 1024 := by omega
  have hc9 : rest.length + 9 < 1024 := by omega
  have hc10 : rest.length + 10 < 1024 := by omega
  have hc11 : rest.length + 11 < 1024 := by omega
  have hc12 : rest.length + 12 < 1024 := by omega
  have hc13 : rest.length + 13 < 1024 := by omega
  have hc14 : rest.length + 14 < 1024 := by omega
  have hc15 : rest.length + 15 < 1024 := by omega
  have hc16 : rest.length + 16 < 1024 := by omega
  have hc17 : rest.length + 17 < 1024 := by omega
  have hc18 : rest.length + 18 < 1024 := by omega
  have hc19 : rest.length + 19 < 1024 := by omega
  have hc20 : rest.length + 20 < 1024 := by omega
  have hc21 : rest.length + 21 < 1024 := by omega
  have hc22 : rest.length + 22 < 1024 := by omega
  have hc23 : rest.length + 23 < 1024 := by omega
  have hc24 : rest.length + 24 < 1024 := by omega
  have hc25 : rest.length + 25 < 1024 := by omega
  have hc26 : rest.length + 26 < 1024 := by omega
  have hc27 : rest.length + 27 < 1024 := by omega
  have hc28 : rest.length + 28 < 1024 := by omega
  have ha224 : (224 : UInt256).toNat = 224 := rfl
  have hf224 := HistoricalSearch.CRTMemoryBounds.activeWords_fix s 224 32 (by decide) (by norm_num) hact
  simp [hz, hzn, entrypart14Program, entrypart14Model, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, Challenge.EvmProof.Word.literal_eq_ofNat, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8, hc9, hc10, hc11, hc12, hc13, hc14, hc15, hc16, hc17, hc18, hc19, hc20, hc21, hc22, hc23, hc24, hc25, hc26, hc27, hc28, ha224, hf224]

#print axioms entrypart14_run

def entryProgram : List Instr :=
  [.op .JUMPDEST,
   .op (.Dup ⟨14, by decide⟩),
   .push 2 1728,
   .op .MSTORE,
   .push 2 3643,
   .op (.Swap ⟨3, by decide⟩),
   .op .POP,
   .push 0 0,
   .op (.Swap ⟨0, by decide⟩),
   .op .POP,
   .push 2 2720,
   .op .MLOAD,
   .push 31 28269553036454149273332760011886696253239742350009903329945699220681916415,
   .push 2 2592,
   .op .MLOAD,
   .op (.Dup ⟨1, by decide⟩),
   .op .AND,
   .push 2 768,
   .op .MSTORE,
   .push 2 2562,
   .op .MLOAD,
   .push 1 4,
   .op .SHR,
   .op (.Dup ⟨1, by decide⟩),
   .op .AND,
   .push 2 800,
   .op .MSTORE,
   .push 2 2531,
   .op .MLOAD,
   .op (.Dup ⟨1, by decide⟩),
   .op .AND,
   .push 2 832,
   .op .MSTORE,
   .push 2 2501,
   .op .MLOAD,
   .push 1 4,
   .op .SHR,
   .op (.Dup ⟨1, by decide⟩),
   .op .AND,
   .push 2 864,
   .op .MSTORE,
   .push 2 2470,
   .op .MLOAD,
   .op (.Dup ⟨1, by decide⟩),
   .op .AND,
   .push 2 896,
   .op .MSTORE,
   .push 2 2440,
   .op .MLOAD,
   .push 1 4,
   .op .SHR,
   .op (.Dup ⟨1, by decide⟩),
   .op .AND,
   .push 2 928,
   .op .MSTORE,
   .push 2 2409,
   .op .MLOAD,
   .op (.Dup ⟨1, by decide⟩),
   .op .AND,
   .push 2 960,
   .op .MSTORE,
   .push 2 2379,
   .op .MLOAD,
   .push 1 4,
   .op .SHR,
   .op (.Dup ⟨1, by decide⟩),
   .op .AND,
   .push 2 992,
   .op .MSTORE,
   .push 2 2368,
   .op .MLOAD,
   .push 1 160,
   .op .SHR,
   .push 2 1024,
   .op .MSTORE,
   .push 0 0,
   .op .MLOAD,
   .push 1 160,
   .op .SHR,
   .push 1 11,
   .op .MLOAD,
   .push 1 4,
   .op .SHR,
   .op (.Dup ⟨2, by decide⟩),
   .op .AND,
   .push 1 41,
   .op .MLOAD,
   .op (.Dup ⟨3, by decide⟩),
   .op .AND,
   .push 1 72,
   .op .MLOAD,
   .push 1 4,
   .op .SHR,
   .op (.Dup ⟨4, by decide⟩),
   .op .AND,
   .push 1 102,
   .op .MLOAD,
   .op (.Dup ⟨5, by decide⟩),
   .op .AND,
   .push 1 133,
   .op .MLOAD,
   .push 1 4,
   .op .SHR,
   .op (.Dup ⟨6, by decide⟩),
   .op .AND,
   .push 1 163,
   .op .MLOAD,
   .op (.Dup ⟨7, by decide⟩),
   .op .AND,
   .push 1 194,
   .op .MLOAD,
   .push 1 4,
   .op .SHR,
   .op (.Dup ⟨8, by decide⟩),
   .op .AND,
   .push 1 224,
   .op .MLOAD,
   .op (.Dup ⟨9, by decide⟩),
   .op .AND,
   .push 32 3618502788666131106986593281521497120414687020801267626233049500247285301247,
   .op .JUMPDEST]

def entryModel (s : State) (pbi hd w3 ent m32 allones m128 m64 m0 tl m96 inv tn aprev counter ret : UInt256) (rest : List UInt256) : State :=
  let v0 : ByteArray := MachineState.writeBytes s.memory (Data.Bytes.natToBytesPadded counter.toNat 32) 1728
  let v1 : UInt256 := MachineState.readWord v0 2720
  let v2 : UInt256 := MachineState.readWord v0 2592
  let v3 : UInt256 := UInt256.land (UInt256.ofNat 28269553036454149273332760011886696253239742350009903329945699220681916415) v2
  let v4 : ByteArray := MachineState.writeBytes v0 (Data.Bytes.natToBytesPadded v3.toNat 32) 768
  let v5 : UInt256 := MachineState.readWord v4 2562
  let v6 : UInt256 := UInt256.shiftRight v5 (UInt256.ofNat 4)
  let v7 : UInt256 := UInt256.land (UInt256.ofNat 28269553036454149273332760011886696253239742350009903329945699220681916415) v6
  let v8 : ByteArray := MachineState.writeBytes v4 (Data.Bytes.natToBytesPadded v7.toNat 32) 800
  let v9 : UInt256 := MachineState.readWord v8 2531
  let v10 : UInt256 := UInt256.land (UInt256.ofNat 28269553036454149273332760011886696253239742350009903329945699220681916415) v9
  let v11 : ByteArray := MachineState.writeBytes v8 (Data.Bytes.natToBytesPadded v10.toNat 32) 832
  let v12 : UInt256 := MachineState.readWord v11 2501
  let v13 : UInt256 := UInt256.shiftRight v12 (UInt256.ofNat 4)
  let v14 : UInt256 := UInt256.land (UInt256.ofNat 28269553036454149273332760011886696253239742350009903329945699220681916415) v13
  let v15 : ByteArray := MachineState.writeBytes v11 (Data.Bytes.natToBytesPadded v14.toNat 32) 864
  let v16 : UInt256 := MachineState.readWord v15 2470
  let v17 : UInt256 := UInt256.land (UInt256.ofNat 28269553036454149273332760011886696253239742350009903329945699220681916415) v16
  let v18 : ByteArray := MachineState.writeBytes v15 (Data.Bytes.natToBytesPadded v17.toNat 32) 896
  let v19 : UInt256 := MachineState.readWord v18 2440
  let v20 : UInt256 := UInt256.shiftRight v19 (UInt256.ofNat 4)
  let v21 : UInt256 := UInt256.land (UInt256.ofNat 28269553036454149273332760011886696253239742350009903329945699220681916415) v20
  let v22 : ByteArray := MachineState.writeBytes v18 (Data.Bytes.natToBytesPadded v21.toNat 32) 928
  let v23 : UInt256 := MachineState.readWord v22 2409
  let v24 : UInt256 := UInt256.land (UInt256.ofNat 28269553036454149273332760011886696253239742350009903329945699220681916415) v23
  let v25 : ByteArray := MachineState.writeBytes v22 (Data.Bytes.natToBytesPadded v24.toNat 32) 960
  let v26 : UInt256 := MachineState.readWord v25 2379
  let v27 : UInt256 := UInt256.shiftRight v26 (UInt256.ofNat 4)
  let v28 : UInt256 := UInt256.land (UInt256.ofNat 28269553036454149273332760011886696253239742350009903329945699220681916415) v27
  let v29 : ByteArray := MachineState.writeBytes v25 (Data.Bytes.natToBytesPadded v28.toNat 32) 992
  let v30 : UInt256 := MachineState.readWord v29 2368
  let v31 : UInt256 := UInt256.shiftRight v30 (UInt256.ofNat 160)
  let v32 : ByteArray := MachineState.writeBytes v29 (Data.Bytes.natToBytesPadded v31.toNat 32) 1024
  let v33 : UInt256 := MachineState.readWord v32 0
  let v34 : UInt256 := UInt256.shiftRight v33 (UInt256.ofNat 160)
  let v35 : UInt256 := MachineState.readWord v32 11
  let v36 : UInt256 := UInt256.shiftRight v35 (UInt256.ofNat 4)
  let v37 : UInt256 := UInt256.land (UInt256.ofNat 28269553036454149273332760011886696253239742350009903329945699220681916415) v36
  let v38 : UInt256 := MachineState.readWord v32 41
  let v39 : UInt256 := UInt256.land (UInt256.ofNat 28269553036454149273332760011886696253239742350009903329945699220681916415) v38
  let v40 : UInt256 := MachineState.readWord v32 72
  let v41 : UInt256 := UInt256.shiftRight v40 (UInt256.ofNat 4)
  let v42 : UInt256 := UInt256.land (UInt256.ofNat 28269553036454149273332760011886696253239742350009903329945699220681916415) v41
  let v43 : UInt256 := MachineState.readWord v32 102
  let v44 : UInt256 := UInt256.land (UInt256.ofNat 28269553036454149273332760011886696253239742350009903329945699220681916415) v43
  let v45 : UInt256 := MachineState.readWord v32 133
  let v46 : UInt256 := UInt256.shiftRight v45 (UInt256.ofNat 4)
  let v47 : UInt256 := UInt256.land (UInt256.ofNat 28269553036454149273332760011886696253239742350009903329945699220681916415) v46
  let v48 : UInt256 := MachineState.readWord v32 163
  let v49 : UInt256 := UInt256.land (UInt256.ofNat 28269553036454149273332760011886696253239742350009903329945699220681916415) v48
  let v50 : UInt256 := MachineState.readWord v32 194
  let v51 : UInt256 := UInt256.shiftRight v50 (UInt256.ofNat 4)
  let v52 : UInt256 := UInt256.land (UInt256.ofNat 28269553036454149273332760011886696253239742350009903329945699220681916415) v51
  let v53 : UInt256 := MachineState.readWord v32 224
  let v54 : UInt256 := UInt256.land (UInt256.ofNat 28269553036454149273332760011886696253239742350009903329945699220681916415) v53
  {s with pc := UInt256.ofNat 5859, memory := v32, stack := (UInt256.ofNat 3618502788666131106986593281521497120414687020801267626233049500247285301247) :: v54 :: v52 :: v49 :: v47 :: v44 :: v42 :: v39 :: v37 :: v34 :: (UInt256.ofNat 28269553036454149273332760011886696253239742350009903329945699220681916415) :: v1 :: (UInt256.ofNat 0) :: hd :: w3 :: (UInt256.ofNat 3643) :: m32 :: allones :: m128 :: m64 :: m0 :: tl :: m96 :: inv :: tn :: aprev :: counter :: ret :: rest}

theorem entry_run (s : State) (pbi hd w3 ent m32 allones m128 m64 m0 tl m96 inv tn aprev counter ret : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 982) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions entryProgram {s with pc := UInt256.ofNat 5615, stack := pbi :: hd :: w3 :: ent :: m32 :: allones :: m128 :: m64 :: m0 :: tl :: m96 :: inv :: tn :: aprev :: counter :: ret :: rest} =
      some (entryModel s pbi hd w3 ent m32 allones m128 m64 m0 tl m96 inv tn aprev counter ret rest) := by
  let v0 : ByteArray := MachineState.writeBytes s.memory (Data.Bytes.natToBytesPadded counter.toNat 32) 1728
  let v1 : UInt256 := MachineState.readWord v0 2720
  let v2 : UInt256 := MachineState.readWord v0 2592
  let v3 : UInt256 := UInt256.land (UInt256.ofNat 28269553036454149273332760011886696253239742350009903329945699220681916415) v2
  let v4 : ByteArray := MachineState.writeBytes v0 (Data.Bytes.natToBytesPadded v3.toNat 32) 768
  let v5 : UInt256 := MachineState.readWord v4 2562
  let v6 : UInt256 := UInt256.shiftRight v5 (UInt256.ofNat 4)
  let v7 : UInt256 := UInt256.land (UInt256.ofNat 28269553036454149273332760011886696253239742350009903329945699220681916415) v6
  let v8 : ByteArray := MachineState.writeBytes v4 (Data.Bytes.natToBytesPadded v7.toNat 32) 800
  let v9 : UInt256 := MachineState.readWord v8 2531
  let v10 : UInt256 := UInt256.land (UInt256.ofNat 28269553036454149273332760011886696253239742350009903329945699220681916415) v9
  let v11 : ByteArray := MachineState.writeBytes v8 (Data.Bytes.natToBytesPadded v10.toNat 32) 832
  let v12 : UInt256 := MachineState.readWord v11 2501
  let v13 : UInt256 := UInt256.shiftRight v12 (UInt256.ofNat 4)
  let v14 : UInt256 := UInt256.land (UInt256.ofNat 28269553036454149273332760011886696253239742350009903329945699220681916415) v13
  let v15 : ByteArray := MachineState.writeBytes v11 (Data.Bytes.natToBytesPadded v14.toNat 32) 864
  let v16 : UInt256 := MachineState.readWord v15 2470
  let v17 : UInt256 := UInt256.land (UInt256.ofNat 28269553036454149273332760011886696253239742350009903329945699220681916415) v16
  let v18 : ByteArray := MachineState.writeBytes v15 (Data.Bytes.natToBytesPadded v17.toNat 32) 896
  let v19 : UInt256 := MachineState.readWord v18 2440
  let v20 : UInt256 := UInt256.shiftRight v19 (UInt256.ofNat 4)
  let v21 : UInt256 := UInt256.land (UInt256.ofNat 28269553036454149273332760011886696253239742350009903329945699220681916415) v20
  let v22 : ByteArray := MachineState.writeBytes v18 (Data.Bytes.natToBytesPadded v21.toNat 32) 928
  let v23 : UInt256 := MachineState.readWord v22 2409
  let v24 : UInt256 := UInt256.land (UInt256.ofNat 28269553036454149273332760011886696253239742350009903329945699220681916415) v23
  let v25 : ByteArray := MachineState.writeBytes v22 (Data.Bytes.natToBytesPadded v24.toNat 32) 960
  let v26 : UInt256 := MachineState.readWord v25 2379
  let v27 : UInt256 := UInt256.shiftRight v26 (UInt256.ofNat 4)
  let v28 : UInt256 := UInt256.land (UInt256.ofNat 28269553036454149273332760011886696253239742350009903329945699220681916415) v27
  let v29 : ByteArray := MachineState.writeBytes v25 (Data.Bytes.natToBytesPadded v28.toNat 32) 992
  let v30 : UInt256 := MachineState.readWord v29 2368
  let v31 : UInt256 := UInt256.shiftRight v30 (UInt256.ofNat 160)
  let v32 : ByteArray := MachineState.writeBytes v29 (Data.Bytes.natToBytesPadded v31.toNat 32) 1024
  let v33 : UInt256 := MachineState.readWord v32 0
  let v34 : UInt256 := UInt256.shiftRight v33 (UInt256.ofNat 160)
  let v35 : UInt256 := MachineState.readWord v32 11
  let v36 : UInt256 := UInt256.shiftRight v35 (UInt256.ofNat 4)
  let v37 : UInt256 := UInt256.land (UInt256.ofNat 28269553036454149273332760011886696253239742350009903329945699220681916415) v36
  let v38 : UInt256 := MachineState.readWord v32 41
  let v39 : UInt256 := UInt256.land (UInt256.ofNat 28269553036454149273332760011886696253239742350009903329945699220681916415) v38
  let v40 : UInt256 := MachineState.readWord v32 72
  let v41 : UInt256 := UInt256.shiftRight v40 (UInt256.ofNat 4)
  let v42 : UInt256 := UInt256.land (UInt256.ofNat 28269553036454149273332760011886696253239742350009903329945699220681916415) v41
  let v43 : UInt256 := MachineState.readWord v32 102
  let v44 : UInt256 := UInt256.land (UInt256.ofNat 28269553036454149273332760011886696253239742350009903329945699220681916415) v43
  let v45 : UInt256 := MachineState.readWord v32 133
  let v46 : UInt256 := UInt256.shiftRight v45 (UInt256.ofNat 4)
  let v47 : UInt256 := UInt256.land (UInt256.ofNat 28269553036454149273332760011886696253239742350009903329945699220681916415) v46
  let v48 : UInt256 := MachineState.readWord v32 163
  let v49 : UInt256 := UInt256.land (UInt256.ofNat 28269553036454149273332760011886696253239742350009903329945699220681916415) v48
  let v50 : UInt256 := MachineState.readWord v32 194
  let v51 : UInt256 := UInt256.shiftRight v50 (UInt256.ofNat 4)
  let v52 : UInt256 := UInt256.land (UInt256.ofNat 28269553036454149273332760011886696253239742350009903329945699220681916415) v51
  let v53 : UInt256 := MachineState.readWord v32 224
  let v54 : UInt256 := UInt256.land (UInt256.ofNat 28269553036454149273332760011886696253239742350009903329945699220681916415) v53
  have h0 : runInstructions entrypart0Program {s with pc := UInt256.ofNat 5615, memory := s.memory, stack := pbi :: hd :: w3 :: ent :: m32 :: allones :: m128 :: m64 :: m0 :: tl :: m96 :: inv :: tn :: aprev :: counter :: ret :: rest} = some {s with pc := UInt256.ofNat 5627, memory := v0, stack := (UInt256.ofNat 0) :: pbi :: hd :: w3 :: (UInt256.ofNat 3643) :: m32 :: allones :: m128 :: m64 :: m0 :: tl :: m96 :: inv :: tn :: aprev :: counter :: ret :: rest} := by
    simpa only [entrypart0Model, v0] using entrypart0_run (s) (pbi) (hd) (w3) (ent) (m32) (allones) (m128) (m64) (m0) (tl) (m96) (inv) (tn) (aprev) (counter) (ret) rest hcap hact
  have h1 : runInstructions entrypart1Program {s with pc := UInt256.ofNat 5627, memory := v0, stack := (UInt256.ofNat 0) :: pbi :: hd :: w3 :: (UInt256.ofNat 3643) :: m32 :: allones :: m128 :: m64 :: m0 :: tl :: m96 :: inv :: tn :: aprev :: counter :: ret :: rest} = some {s with pc := UInt256.ofNat 5670, memory := v0, stack := (UInt256.ofNat 28269553036454149273332760011886696253239742350009903329945699220681916415) :: v2 :: (UInt256.ofNat 28269553036454149273332760011886696253239742350009903329945699220681916415) :: v1 :: (UInt256.ofNat 0) :: hd :: w3 :: (UInt256.ofNat 3643) :: m32 :: allones :: m128 :: m64 :: m0 :: tl :: m96 :: inv :: tn :: aprev :: counter :: ret :: rest} := by
    simpa only [entrypart1Model, v1, v2] using entrypart1_run ({s with memory := v0}) ((UInt256.ofNat 0)) (pbi) (hd) (w3) ((UInt256.ofNat 3643)) (m32) (allones) (m128) (m64) (m0) (tl) (m96) (inv) (tn) (aprev) (counter) (ret) rest hcap hact
  have h2 : runInstructions entrypart2Program {s with pc := UInt256.ofNat 5670, memory := v0, stack := (UInt256.ofNat 28269553036454149273332760011886696253239742350009903329945699220681916415) :: v2 :: (UInt256.ofNat 28269553036454149273332760011886696253239742350009903329945699220681916415) :: v1 :: (UInt256.ofNat 0) :: hd :: w3 :: (UInt256.ofNat 3643) :: m32 :: allones :: m128 :: m64 :: m0 :: tl :: m96 :: inv :: tn :: aprev :: counter :: ret :: rest} = some {s with pc := UInt256.ofNat 5683, memory := v4, stack := (UInt256.ofNat 28269553036454149273332760011886696253239742350009903329945699220681916415) :: v6 :: (UInt256.ofNat 28269553036454149273332760011886696253239742350009903329945699220681916415) :: v1 :: (UInt256.ofNat 0) :: hd :: w3 :: (UInt256.ofNat 3643) :: m32 :: allones :: m128 :: m64 :: m0 :: tl :: m96 :: inv :: tn :: aprev :: counter :: ret :: rest} := by
    simpa only [entrypart2Model, v3, v4, v5, v6] using entrypart2_run ({s with memory := v0}) ((UInt256.ofNat 28269553036454149273332760011886696253239742350009903329945699220681916415)) (v2) ((UInt256.ofNat 28269553036454149273332760011886696253239742350009903329945699220681916415)) (v1) ((UInt256.ofNat 0)) (hd) (w3) ((UInt256.ofNat 3643)) (m32) (allones) (m128) (m64) (m0) (tl) (m96) (inv) (tn) (aprev) (counter) (ret) rest hcap hact
  have h3 : runInstructions entrypart3Program {s with pc := UInt256.ofNat 5683, memory := v4, stack := (UInt256.ofNat 28269553036454149273332760011886696253239742350009903329945699220681916415) :: v6 :: (UInt256.ofNat 28269553036454149273332760011886696253239742350009903329945699220681916415) :: v1 :: (UInt256.ofNat 0) :: hd :: w3 :: (UInt256.ofNat 3643) :: m32 :: allones :: m128 :: m64 :: m0 :: tl :: m96 :: inv :: tn :: aprev :: counter :: ret :: rest} = some {s with pc := UInt256.ofNat 5698, memory := v11, stack := (UInt256.ofNat 28269553036454149273332760011886696253239742350009903329945699220681916415) :: v1 :: (UInt256.ofNat 0) :: hd :: w3 :: (UInt256.ofNat 3643) :: m32 :: allones :: m128 :: m64 :: m0 :: tl :: m96 :: inv :: tn :: aprev :: counter :: ret :: rest} := by
    simpa only [entrypart3Model, v7, v8, v9, v10, v11] using entrypart3_run ({s with memory := v4}) ((UInt256.ofNat 28269553036454149273332760011886696253239742350009903329945699220681916415)) (v6) ((UInt256.ofNat 28269553036454149273332760011886696253239742350009903329945699220681916415)) (v1) ((UInt256.ofNat 0)) (hd) (w3) ((UInt256.ofNat 3643)) (m32) (allones) (m128) (m64) (m0) (tl) (m96) (inv) (tn) (aprev) (counter) (ret) rest hcap hact
  have h4 : runInstructions entrypart4Program {s with pc := UInt256.ofNat 5698, memory := v11, stack := (UInt256.ofNat 28269553036454149273332760011886696253239742350009903329945699220681916415) :: v1 :: (UInt256.ofNat 0) :: hd :: w3 :: (UInt256.ofNat 3643) :: m32 :: allones :: m128 :: m64 :: m0 :: tl :: m96 :: inv :: tn :: aprev :: counter :: ret :: rest} = some {s with pc := UInt256.ofNat 5711, memory := v15, stack := (UInt256.ofNat 28269553036454149273332760011886696253239742350009903329945699220681916415) :: v1 :: (UInt256.ofNat 0) :: hd :: w3 :: (UInt256.ofNat 3643) :: m32 :: allones :: m128 :: m64 :: m0 :: tl :: m96 :: inv :: tn :: aprev :: counter :: ret :: rest} := by
    simpa only [entrypart4Model, v12, v13, v14, v15] using entrypart4_run ({s with memory := v11}) ((UInt256.ofNat 28269553036454149273332760011886696253239742350009903329945699220681916415)) (v1) ((UInt256.ofNat 0)) (hd) (w3) ((UInt256.ofNat 3643)) (m32) (allones) (m128) (m64) (m0) (tl) (m96) (inv) (tn) (aprev) (counter) (ret) rest hcap hact
  have h5 : runInstructions entrypart5Program {s with pc := UInt256.ofNat 5711, memory := v15, stack := (UInt256.ofNat 28269553036454149273332760011886696253239742350009903329945699220681916415) :: v1 :: (UInt256.ofNat 0) :: hd :: w3 :: (UInt256.ofNat 3643) :: m32 :: allones :: m128 :: m64 :: m0 :: tl :: m96 :: inv :: tn :: aprev :: counter :: ret :: rest} = some {s with pc := UInt256.ofNat 5725, memory := v18, stack := v19 :: (UInt256.ofNat 28269553036454149273332760011886696253239742350009903329945699220681916415) :: v1 :: (UInt256.ofNat 0) :: hd :: w3 :: (UInt256.ofNat 3643) :: m32 :: allones :: m128 :: m64 :: m0 :: tl :: m96 :: inv :: tn :: aprev :: counter :: ret :: rest} := by
    simpa only [entrypart5Model, v16, v17, v18, v19] using entrypart5_run ({s with memory := v15}) ((UInt256.ofNat 28269553036454149273332760011886696253239742350009903329945699220681916415)) (v1) ((UInt256.ofNat 0)) (hd) (w3) ((UInt256.ofNat 3643)) (m32) (allones) (m128) (m64) (m0) (tl) (m96) (inv) (tn) (aprev) (counter) (ret) rest hcap hact
  have h6 : runInstructions entrypart6Program {s with pc := UInt256.ofNat 5725, memory := v18, stack := v19 :: (UInt256.ofNat 28269553036454149273332760011886696253239742350009903329945699220681916415) :: v1 :: (UInt256.ofNat 0) :: hd :: w3 :: (UInt256.ofNat 3643) :: m32 :: allones :: m128 :: m64 :: m0 :: tl :: m96 :: inv :: tn :: aprev :: counter :: ret :: rest} = some {s with pc := UInt256.ofNat 5738, memory := v22, stack := v23 :: (UInt256.ofNat 28269553036454149273332760011886696253239742350009903329945699220681916415) :: v1 :: (UInt256.ofNat 0) :: hd :: w3 :: (UInt256.ofNat 3643) :: m32 :: allones :: m128 :: m64 :: m0 :: tl :: m96 :: inv :: tn :: aprev :: counter :: ret :: rest} := by
    simpa only [entrypart6Model, v20, v21, v22, v23] using entrypart6_run ({s with memory := v18}) (v19) ((UInt256.ofNat 28269553036454149273332760011886696253239742350009903329945699220681916415)) (v1) ((UInt256.ofNat 0)) (hd) (w3) ((UInt256.ofNat 3643)) (m32) (allones) (m128) (m64) (m0) (tl) (m96) (inv) (tn) (aprev) (counter) (ret) rest hcap hact
  have h7 : runInstructions entrypart7Program {s with pc := UInt256.ofNat 5738, memory := v22, stack := v23 :: (UInt256.ofNat 28269553036454149273332760011886696253239742350009903329945699220681916415) :: v1 :: (UInt256.ofNat 0) :: hd :: w3 :: (UInt256.ofNat 3643) :: m32 :: allones :: m128 :: m64 :: m0 :: tl :: m96 :: inv :: tn :: aprev :: counter :: ret :: rest} = some {s with pc := UInt256.ofNat 5751, memory := v25, stack := v27 :: (UInt256.ofNat 28269553036454149273332760011886696253239742350009903329945699220681916415) :: v1 :: (UInt256.ofNat 0) :: hd :: w3 :: (UInt256.ofNat 3643) :: m32 :: allones :: m128 :: m64 :: m0 :: tl :: m96 :: inv :: tn :: aprev :: counter :: ret :: rest} := by
    simpa only [entrypart7Model, v24, v25, v26, v27] using entrypart7_run ({s with memory := v22}) (v23) ((UInt256.ofNat 28269553036454149273332760011886696253239742350009903329945699220681916415)) (v1) ((UInt256.ofNat 0)) (hd) (w3) ((UInt256.ofNat 3643)) (m32) (allones) (m128) (m64) (m0) (tl) (m96) (inv) (tn) (aprev) (counter) (ret) rest hcap hact
  have h8 : runInstructions entrypart8Program {s with pc := UInt256.ofNat 5751, memory := v25, stack := v27 :: (UInt256.ofNat 28269553036454149273332760011886696253239742350009903329945699220681916415) :: v1 :: (UInt256.ofNat 0) :: hd :: w3 :: (UInt256.ofNat 3643) :: m32 :: allones :: m128 :: m64 :: m0 :: tl :: m96 :: inv :: tn :: aprev :: counter :: ret :: rest} = some {s with pc := UInt256.ofNat 5764, memory := v29, stack := v31 :: (UInt256.ofNat 28269553036454149273332760011886696253239742350009903329945699220681916415) :: v1 :: (UInt256.ofNat 0) :: hd :: w3 :: (UInt256.ofNat 3643) :: m32 :: allones :: m128 :: m64 :: m0 :: tl :: m96 :: inv :: tn :: aprev :: counter :: ret :: rest} := by
    simpa only [entrypart8Model, v28, v29, v30, v31] using entrypart8_run ({s with memory := v25}) (v27) ((UInt256.ofNat 28269553036454149273332760011886696253239742350009903329945699220681916415)) (v1) ((UInt256.ofNat 0)) (hd) (w3) ((UInt256.ofNat 3643)) (m32) (allones) (m128) (m64) (m0) (tl) (m96) (inv) (tn) (aprev) (counter) (ret) rest hcap hact
  have h9 : runInstructions entrypart9Program {s with pc := UInt256.ofNat 5764, memory := v29, stack := v31 :: (UInt256.ofNat 28269553036454149273332760011886696253239742350009903329945699220681916415) :: v1 :: (UInt256.ofNat 0) :: hd :: w3 :: (UInt256.ofNat 3643) :: m32 :: allones :: m128 :: m64 :: m0 :: tl :: m96 :: inv :: tn :: aprev :: counter :: ret :: rest} = some {s with pc := UInt256.ofNat 5776, memory := v32, stack := v35 :: v34 :: (UInt256.ofNat 28269553036454149273332760011886696253239742350009903329945699220681916415) :: v1 :: (UInt256.ofNat 0) :: hd :: w3 :: (UInt256.ofNat 3643) :: m32 :: allones :: m128 :: m64 :: m0 :: tl :: m96 :: inv :: tn :: aprev :: counter :: ret :: rest} := by
    simpa only [entrypart9Model, v32, v33, v34, v35] using entrypart9_run ({s with memory := v29}) (v31) ((UInt256.ofNat 28269553036454149273332760011886696253239742350009903329945699220681916415)) (v1) ((UInt256.ofNat 0)) (hd) (w3) ((UInt256.ofNat 3643)) (m32) (allones) (m128) (m64) (m0) (tl) (m96) (inv) (tn) (aprev) (counter) (ret) rest hcap hact
  have h10 : runInstructions entrypart10Program {s with pc := UInt256.ofNat 5776, memory := v32, stack := v35 :: v34 :: (UInt256.ofNat 28269553036454149273332760011886696253239742350009903329945699220681916415) :: v1 :: (UInt256.ofNat 0) :: hd :: w3 :: (UInt256.ofNat 3643) :: m32 :: allones :: m128 :: m64 :: m0 :: tl :: m96 :: inv :: tn :: aprev :: counter :: ret :: rest} = some {s with pc := UInt256.ofNat 5786, memory := v32, stack := v39 :: v37 :: v34 :: (UInt256.ofNat 28269553036454149273332760011886696253239742350009903329945699220681916415) :: v1 :: (UInt256.ofNat 0) :: hd :: w3 :: (UInt256.ofNat 3643) :: m32 :: allones :: m128 :: m64 :: m0 :: tl :: m96 :: inv :: tn :: aprev :: counter :: ret :: rest} := by
    simpa only [entrypart10Model, v36, v37, v38, v39] using entrypart10_run ({s with memory := v32}) (v35) (v34) ((UInt256.ofNat 28269553036454149273332760011886696253239742350009903329945699220681916415)) (v1) ((UInt256.ofNat 0)) (hd) (w3) ((UInt256.ofNat 3643)) (m32) (allones) (m128) (m64) (m0) (tl) (m96) (inv) (tn) (aprev) (counter) (ret) rest hcap hact
  have h11 : runInstructions entrypart11Program {s with pc := UInt256.ofNat 5786, memory := v32, stack := v39 :: v37 :: v34 :: (UInt256.ofNat 28269553036454149273332760011886696253239742350009903329945699220681916415) :: v1 :: (UInt256.ofNat 0) :: hd :: w3 :: (UInt256.ofNat 3643) :: m32 :: allones :: m128 :: m64 :: m0 :: tl :: m96 :: inv :: tn :: aprev :: counter :: ret :: rest} = some {s with pc := UInt256.ofNat 5797, memory := v32, stack := v43 :: v42 :: v39 :: v37 :: v34 :: (UInt256.ofNat 28269553036454149273332760011886696253239742350009903329945699220681916415) :: v1 :: (UInt256.ofNat 0) :: hd :: w3 :: (UInt256.ofNat 3643) :: m32 :: allones :: m128 :: m64 :: m0 :: tl :: m96 :: inv :: tn :: aprev :: counter :: ret :: rest} := by
    simpa only [entrypart11Model, v40, v41, v42, v43] using entrypart11_run ({s with memory := v32}) (v39) (v37) (v34) ((UInt256.ofNat 28269553036454149273332760011886696253239742350009903329945699220681916415)) (v1) ((UInt256.ofNat 0)) (hd) (w3) ((UInt256.ofNat 3643)) (m32) (allones) (m128) (m64) (m0) (tl) (m96) (inv) (tn) (aprev) (counter) (ret) rest hcap hact
  have h12 : runInstructions entrypart12Program {s with pc := UInt256.ofNat 5797, memory := v32, stack := v43 :: v42 :: v39 :: v37 :: v34 :: (UInt256.ofNat 28269553036454149273332760011886696253239742350009903329945699220681916415) :: v1 :: (UInt256.ofNat 0) :: hd :: w3 :: (UInt256.ofNat 3643) :: m32 :: allones :: m128 :: m64 :: m0 :: tl :: m96 :: inv :: tn :: aprev :: counter :: ret :: rest} = some {s with pc := UInt256.ofNat 5807, memory := v32, stack := v47 :: v44 :: v42 :: v39 :: v37 :: v34 :: (UInt256.ofNat 28269553036454149273332760011886696253239742350009903329945699220681916415) :: v1 :: (UInt256.ofNat 0) :: hd :: w3 :: (UInt256.ofNat 3643) :: m32 :: allones :: m128 :: m64 :: m0 :: tl :: m96 :: inv :: tn :: aprev :: counter :: ret :: rest} := by
    simpa only [entrypart12Model, v44, v45, v46, v47] using entrypart12_run ({s with memory := v32}) (v43) (v42) (v39) (v37) (v34) ((UInt256.ofNat 28269553036454149273332760011886696253239742350009903329945699220681916415)) (v1) ((UInt256.ofNat 0)) (hd) (w3) ((UInt256.ofNat 3643)) (m32) (allones) (m128) (m64) (m0) (tl) (m96) (inv) (tn) (aprev) (counter) (ret) rest hcap hact
  have h13 : runInstructions entrypart13Program {s with pc := UInt256.ofNat 5807, memory := v32, stack := v47 :: v44 :: v42 :: v39 :: v37 :: v34 :: (UInt256.ofNat 28269553036454149273332760011886696253239742350009903329945699220681916415) :: v1 :: (UInt256.ofNat 0) :: hd :: w3 :: (UInt256.ofNat 3643) :: m32 :: allones :: m128 :: m64 :: m0 :: tl :: m96 :: inv :: tn :: aprev :: counter :: ret :: rest} = some {s with pc := UInt256.ofNat 5818, memory := v32, stack := v51 :: v49 :: v47 :: v44 :: v42 :: v39 :: v37 :: v34 :: (UInt256.ofNat 28269553036454149273332760011886696253239742350009903329945699220681916415) :: v1 :: (UInt256.ofNat 0) :: hd :: w3 :: (UInt256.ofNat 3643) :: m32 :: allones :: m128 :: m64 :: m0 :: tl :: m96 :: inv :: tn :: aprev :: counter :: ret :: rest} := by
    simpa only [entrypart13Model, v48, v49, v50, v51] using entrypart13_run ({s with memory := v32}) (v47) (v44) (v42) (v39) (v37) (v34) ((UInt256.ofNat 28269553036454149273332760011886696253239742350009903329945699220681916415)) (v1) ((UInt256.ofNat 0)) (hd) (w3) ((UInt256.ofNat 3643)) (m32) (allones) (m128) (m64) (m0) (tl) (m96) (inv) (tn) (aprev) (counter) (ret) rest hcap hact
  have h14 : runInstructions entrypart14Program {s with pc := UInt256.ofNat 5818, memory := v32, stack := v51 :: v49 :: v47 :: v44 :: v42 :: v39 :: v37 :: v34 :: (UInt256.ofNat 28269553036454149273332760011886696253239742350009903329945699220681916415) :: v1 :: (UInt256.ofNat 0) :: hd :: w3 :: (UInt256.ofNat 3643) :: m32 :: allones :: m128 :: m64 :: m0 :: tl :: m96 :: inv :: tn :: aprev :: counter :: ret :: rest} = some {s with pc := UInt256.ofNat 5859, memory := v32, stack := (UInt256.ofNat 3618502788666131106986593281521497120414687020801267626233049500247285301247) :: v54 :: v52 :: v49 :: v47 :: v44 :: v42 :: v39 :: v37 :: v34 :: (UInt256.ofNat 28269553036454149273332760011886696253239742350009903329945699220681916415) :: v1 :: (UInt256.ofNat 0) :: hd :: w3 :: (UInt256.ofNat 3643) :: m32 :: allones :: m128 :: m64 :: m0 :: tl :: m96 :: inv :: tn :: aprev :: counter :: ret :: rest} := by
    simpa only [entrypart14Model, v52, v53, v54] using entrypart14_run ({s with memory := v32}) (v51) (v49) (v47) (v44) (v42) (v39) (v37) (v34) ((UInt256.ofNat 28269553036454149273332760011886696253239742350009903329945699220681916415)) (v1) ((UInt256.ofNat 0)) (hd) (w3) ((UInt256.ofNat 3643)) (m32) (allones) (m128) (m64) (m0) (tl) (m96) (inv) (tn) (aprev) (counter) (ret) rest hcap hact
  exact (runInstructions_append_some _ _ _ _ _ h0 (runInstructions_append_some _ _ _ _ _ h1 (runInstructions_append_some _ _ _ _ _ h2 (runInstructions_append_some _ _ _ _ _ h3 (runInstructions_append_some _ _ _ _ _ h4 (runInstructions_append_some _ _ _ _ _ h5 (runInstructions_append_some _ _ _ _ _ h6 (runInstructions_append_some _ _ _ _ _ h7 (runInstructions_append_some _ _ _ _ _ h8 (runInstructions_append_some _ _ _ _ _ h9 (runInstructions_append_some _ _ _ _ _ h10 (runInstructions_append_some _ _ _ _ _ h11 (runInstructions_append_some _ _ _ _ _ h12 (runInstructions_append_some _ _ _ _ _ h13 h14))))))))))))))

#print axioms entry_run



def overflowpart0Program : List Instr :=
  [.push 2 1600,
   .op .MLOAD,
   .push 1 192,
   .op .SHR,
   .op (.Dup ⟨0, by decide⟩),
   .push 2 1760,
   .op .MSTORE,
   .push 2 8324]

def overflowpart0Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 : UInt256) (rest : List UInt256) : State :=
  let v0 : UInt256 := MachineState.readWord s.memory 1600
  let v1 : UInt256 := UInt256.shiftRight v0 (UInt256.ofNat 192)
  let v2 : ByteArray := MachineState.writeBytes s.memory (Data.Bytes.natToBytesPadded v1.toNat 32) 1760
  {s with pc := UInt256.ofNat 8144, memory := v2, stack := (UInt256.ofNat 8324) :: v1 :: x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: x18 :: x19 :: x20 :: x21 :: x22 :: x23 :: x24 :: x25 :: x26 :: x27 :: rest}

theorem overflowpart0_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 982) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions overflowpart0Program {s with pc := UInt256.ofNat 8129, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: x18 :: x19 :: x20 :: x21 :: x22 :: x23 :: x24 :: x25 :: x26 :: x27 :: rest} =
      some (overflowpart0Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 rest) := by
  have hz : ({val := 0} : UInt256) = UInt256.ofNat 0 := rfl
  have hzn : ({val := 0} : UInt256).toNat = 0 := rfl
  have hc0 : rest.length + 0 < 1024 := by omega
  have hc1 : rest.length + 1 < 1024 := by omega
  have hc2 : rest.length + 2 < 1024 := by omega
  have hc3 : rest.length + 3 < 1024 := by omega
  have hc4 : rest.length + 4 < 1024 := by omega
  have hc5 : rest.length + 5 < 1024 := by omega
  have hc6 : rest.length + 6 < 1024 := by omega
  have hc7 : rest.length + 7 < 1024 := by omega
  have hc8 : rest.length + 8 < 1024 := by omega
  have hc9 : rest.length + 9 < 1024 := by omega
  have hc10 : rest.length + 10 < 1024 := by omega
  have hc11 : rest.length + 11 < 1024 := by omega
  have hc12 : rest.length + 12 < 1024 := by omega
  have hc13 : rest.length + 13 < 1024 := by omega
  have hc14 : rest.length + 14 < 1024 := by omega
  have hc15 : rest.length + 15 < 1024 := by omega
  have hc16 : rest.length + 16 < 1024 := by omega
  have hc17 : rest.length + 17 < 1024 := by omega
  have hc18 : rest.length + 18 < 1024 := by omega
  have hc19 : rest.length + 19 < 1024 := by omega
  have hc20 : rest.length + 20 < 1024 := by omega
  have hc21 : rest.length + 21 < 1024 := by omega
  have hc22 : rest.length + 22 < 1024 := by omega
  have hc23 : rest.length + 23 < 1024 := by omega
  have hc24 : rest.length + 24 < 1024 := by omega
  have hc25 : rest.length + 25 < 1024 := by omega
  have hc26 : rest.length + 26 < 1024 := by omega
  have hc27 : rest.length + 27 < 1024 := by omega
  have hc28 : rest.length + 28 < 1024 := by omega
  have hc29 : rest.length + 29 < 1024 := by omega
  have hc30 : rest.length + 30 < 1024 := by omega
  have hc31 : rest.length + 31 < 1024 := by omega
  have ha1600 : (1600 : UInt256).toNat = 1600 := rfl
  have hf1600 := HistoricalSearch.CRTMemoryBounds.activeWords_fix s 1600 32 (by decide) (by norm_num) hact
  have ha1760 : (1760 : UInt256).toNat = 1760 := rfl
  have hf1760 := HistoricalSearch.CRTMemoryBounds.activeWords_fix s 1760 32 (by decide) (by norm_num) hact
  simp [hz, hzn, overflowpart0Program, overflowpart0Model, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, Challenge.EvmProof.Word.literal_eq_ofNat, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8, hc9, hc10, hc11, hc12, hc13, hc14, hc15, hc16, hc17, hc18, hc19, hc20, hc21, hc22, hc23, hc24, hc25, hc26, hc27, hc28, hc29, hc30, hc31, ha1600, hf1600, ha1760, hf1760]

#print axioms overflowpart0_run

def overflowProgram : List Instr :=
  [.push 2 1600,
   .op .MLOAD,
   .push 1 192,
   .op .SHR,
   .op (.Dup ⟨0, by decide⟩),
   .push 2 1760,
   .op .MSTORE,
   .push 2 8324]

def overflowModel (s : State) (P n0 n1 n2 n3 n4 n5 n6 n7 n8 mask minv pbi hd w3 ent m32 allones m128 m64 m0 tl m96 inv tn aprev counter ret : UInt256) (rest : List UInt256) : State :=
  let v0 : UInt256 := MachineState.readWord s.memory 1600
  let v1 : UInt256 := UInt256.shiftRight v0 (UInt256.ofNat 192)
  let v2 : ByteArray := MachineState.writeBytes s.memory (Data.Bytes.natToBytesPadded v1.toNat 32) 1760
  {s with pc := UInt256.ofNat 8144, memory := v2, stack := (UInt256.ofNat 8324) :: v1 :: P :: n0 :: n1 :: n2 :: n3 :: n4 :: n5 :: n6 :: n7 :: n8 :: mask :: minv :: pbi :: hd :: w3 :: ent :: m32 :: allones :: m128 :: m64 :: m0 :: tl :: m96 :: inv :: tn :: aprev :: counter :: ret :: rest}

theorem overflow_run (s : State) (P n0 n1 n2 n3 n4 n5 n6 n7 n8 mask minv pbi hd w3 ent m32 allones m128 m64 m0 tl m96 inv tn aprev counter ret : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 982) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions overflowProgram {s with pc := UInt256.ofNat 8129, stack := P :: n0 :: n1 :: n2 :: n3 :: n4 :: n5 :: n6 :: n7 :: n8 :: mask :: minv :: pbi :: hd :: w3 :: ent :: m32 :: allones :: m128 :: m64 :: m0 :: tl :: m96 :: inv :: tn :: aprev :: counter :: ret :: rest} =
      some (overflowModel s P n0 n1 n2 n3 n4 n5 n6 n7 n8 mask minv pbi hd w3 ent m32 allones m128 m64 m0 tl m96 inv tn aprev counter ret rest) := by
  let v0 : UInt256 := MachineState.readWord s.memory 1600
  let v1 : UInt256 := UInt256.shiftRight v0 (UInt256.ofNat 192)
  let v2 : ByteArray := MachineState.writeBytes s.memory (Data.Bytes.natToBytesPadded v1.toNat 32) 1760
  have h0 : runInstructions overflowpart0Program {s with pc := UInt256.ofNat 8129, memory := s.memory, stack := P :: n0 :: n1 :: n2 :: n3 :: n4 :: n5 :: n6 :: n7 :: n8 :: mask :: minv :: pbi :: hd :: w3 :: ent :: m32 :: allones :: m128 :: m64 :: m0 :: tl :: m96 :: inv :: tn :: aprev :: counter :: ret :: rest} = some {s with pc := UInt256.ofNat 8144, memory := v2, stack := (UInt256.ofNat 8324) :: v1 :: P :: n0 :: n1 :: n2 :: n3 :: n4 :: n5 :: n6 :: n7 :: n8 :: mask :: minv :: pbi :: hd :: w3 :: ent :: m32 :: allones :: m128 :: m64 :: m0 :: tl :: m96 :: inv :: tn :: aprev :: counter :: ret :: rest} := by
    simpa only [overflowpart0Model, v0, v1, v2] using overflowpart0_run (s) (P) (n0) (n1) (n2) (n3) (n4) (n5) (n6) (n7) (n8) (mask) (minv) (pbi) (hd) (w3) (ent) (m32) (allones) (m128) (m64) (m0) (tl) (m96) (inv) (tn) (aprev) (counter) (ret) rest hcap hact
  exact h0

#print axioms overflow_run

def countpart0Program : List Instr :=
  [.push 2 1728,
   .op .MLOAD,
   .op .ISZERO,
   .push 2 8800]

def countpart0Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 : UInt256) (rest : List UInt256) : State :=
  let v0 : UInt256 := MachineState.readWord s.memory 1728
  let v1 : UInt256 := UInt256.isZero v0
  {s with pc := UInt256.ofNat 8153, memory := s.memory, stack := (UInt256.ofNat 8800) :: v1 :: x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: x18 :: x19 :: x20 :: x21 :: x22 :: x23 :: x24 :: x25 :: x26 :: x27 :: rest}

theorem countpart0_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 982) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions countpart0Program {s with pc := UInt256.ofNat 8145, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: x18 :: x19 :: x20 :: x21 :: x22 :: x23 :: x24 :: x25 :: x26 :: x27 :: rest} =
      some (countpart0Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 rest) := by
  have hz : ({val := 0} : UInt256) = UInt256.ofNat 0 := rfl
  have hzn : ({val := 0} : UInt256).toNat = 0 := rfl
  have hc0 : rest.length + 0 < 1024 := by omega
  have hc1 : rest.length + 1 < 1024 := by omega
  have hc2 : rest.length + 2 < 1024 := by omega
  have hc3 : rest.length + 3 < 1024 := by omega
  have hc4 : rest.length + 4 < 1024 := by omega
  have hc5 : rest.length + 5 < 1024 := by omega
  have hc6 : rest.length + 6 < 1024 := by omega
  have hc7 : rest.length + 7 < 1024 := by omega
  have hc8 : rest.length + 8 < 1024 := by omega
  have hc9 : rest.length + 9 < 1024 := by omega
  have hc10 : rest.length + 10 < 1024 := by omega
  have hc11 : rest.length + 11 < 1024 := by omega
  have hc12 : rest.length + 12 < 1024 := by omega
  have hc13 : rest.length + 13 < 1024 := by omega
  have hc14 : rest.length + 14 < 1024 := by omega
  have hc15 : rest.length + 15 < 1024 := by omega
  have hc16 : rest.length + 16 < 1024 := by omega
  have hc17 : rest.length + 17 < 1024 := by omega
  have hc18 : rest.length + 18 < 1024 := by omega
  have hc19 : rest.length + 19 < 1024 := by omega
  have hc20 : rest.length + 20 < 1024 := by omega
  have hc21 : rest.length + 21 < 1024 := by omega
  have hc22 : rest.length + 22 < 1024 := by omega
  have hc23 : rest.length + 23 < 1024 := by omega
  have hc24 : rest.length + 24 < 1024 := by omega
  have hc25 : rest.length + 25 < 1024 := by omega
  have hc26 : rest.length + 26 < 1024 := by omega
  have hc27 : rest.length + 27 < 1024 := by omega
  have hc28 : rest.length + 28 < 1024 := by omega
  have hc29 : rest.length + 29 < 1024 := by omega
  have hc30 : rest.length + 30 < 1024 := by omega
  have ha1728 : (1728 : UInt256).toNat = 1728 := rfl
  have hf1728 := HistoricalSearch.CRTMemoryBounds.activeWords_fix s 1728 32 (by decide) (by norm_num) hact
  simp [hz, hzn, countpart0Program, countpart0Model, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, Challenge.EvmProof.Word.literal_eq_ofNat, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8, hc9, hc10, hc11, hc12, hc13, hc14, hc15, hc16, hc17, hc18, hc19, hc20, hc21, hc22, hc23, hc24, hc25, hc26, hc27, hc28, hc29, hc30, ha1728, hf1728]

#print axioms countpart0_run

def countProgram : List Instr :=
  [.push 2 1728,
   .op .MLOAD,
   .op .ISZERO,
   .push 2 8800]

def countModel (s : State) (P n0 n1 n2 n3 n4 n5 n6 n7 n8 mask minv pbi hd w3 ent m32 allones m128 m64 m0 tl m96 inv tn aprev counter ret : UInt256) (rest : List UInt256) : State :=
  let v0 : UInt256 := MachineState.readWord s.memory 1728
  let v1 : UInt256 := UInt256.isZero v0
  {s with pc := UInt256.ofNat 8153, memory := s.memory, stack := (UInt256.ofNat 8800) :: v1 :: P :: n0 :: n1 :: n2 :: n3 :: n4 :: n5 :: n6 :: n7 :: n8 :: mask :: minv :: pbi :: hd :: w3 :: ent :: m32 :: allones :: m128 :: m64 :: m0 :: tl :: m96 :: inv :: tn :: aprev :: counter :: ret :: rest}

theorem count_run (s : State) (P n0 n1 n2 n3 n4 n5 n6 n7 n8 mask minv pbi hd w3 ent m32 allones m128 m64 m0 tl m96 inv tn aprev counter ret : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 982) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions countProgram {s with pc := UInt256.ofNat 8145, stack := P :: n0 :: n1 :: n2 :: n3 :: n4 :: n5 :: n6 :: n7 :: n8 :: mask :: minv :: pbi :: hd :: w3 :: ent :: m32 :: allones :: m128 :: m64 :: m0 :: tl :: m96 :: inv :: tn :: aprev :: counter :: ret :: rest} =
      some (countModel s P n0 n1 n2 n3 n4 n5 n6 n7 n8 mask minv pbi hd w3 ent m32 allones m128 m64 m0 tl m96 inv tn aprev counter ret rest) := by
  let v0 : UInt256 := MachineState.readWord s.memory 1728
  let v1 : UInt256 := UInt256.isZero v0
  have h0 : runInstructions countpart0Program {s with pc := UInt256.ofNat 8145, memory := s.memory, stack := P :: n0 :: n1 :: n2 :: n3 :: n4 :: n5 :: n6 :: n7 :: n8 :: mask :: minv :: pbi :: hd :: w3 :: ent :: m32 :: allones :: m128 :: m64 :: m0 :: tl :: m96 :: inv :: tn :: aprev :: counter :: ret :: rest} = some {s with pc := UInt256.ofNat 8153, memory := s.memory, stack := (UInt256.ofNat 8800) :: v1 :: P :: n0 :: n1 :: n2 :: n3 :: n4 :: n5 :: n6 :: n7 :: n8 :: mask :: minv :: pbi :: hd :: w3 :: ent :: m32 :: allones :: m128 :: m64 :: m0 :: tl :: m96 :: inv :: tn :: aprev :: counter :: ret :: rest} := by
    simpa only [countpart0Model, v0, v1] using countpart0_run (s) (P) (n0) (n1) (n2) (n3) (n4) (n5) (n6) (n7) (n8) (mask) (minv) (pbi) (hd) (w3) (ent) (m32) (allones) (m128) (m64) (m0) (tl) (m96) (inv) (tn) (aprev) (counter) (ret) rest hcap hact
  exact h0

#print axioms count_run


def retainpart0Program : List Instr :=
  [.push 1 1,
   .push 2 1728,
   .op .MLOAD,
   .op .SUB,
   .push 2 1728,
   .op .MSTORE,
   .push 2 1600,
   .op .MLOAD]

def retainpart0Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 : UInt256) (rest : List UInt256) : State :=
  let v0 : UInt256 := MachineState.readWord s.memory 1728
  let v1 : UInt256 := v0 - (UInt256.ofNat 1)
  let v2 : ByteArray := MachineState.writeBytes s.memory (Data.Bytes.natToBytesPadded v1.toNat 32) 1728
  let v3 : UInt256 := MachineState.readWord v2 1600
  {s with pc := UInt256.ofNat 8169, memory := v2, stack := v3 :: x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: x18 :: x19 :: x20 :: x21 :: x22 :: x23 :: x24 :: x25 :: x26 :: x27 :: rest}

theorem retainpart0_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 982) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions retainpart0Program {s with pc := UInt256.ofNat 8154, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: x18 :: x19 :: x20 :: x21 :: x22 :: x23 :: x24 :: x25 :: x26 :: x27 :: rest} =
      some (retainpart0Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 rest) := by
  have hz : ({val := 0} : UInt256) = UInt256.ofNat 0 := rfl
  have hzn : ({val := 0} : UInt256).toNat = 0 := rfl
  have hc0 : rest.length + 0 < 1024 := by omega
  have hc1 : rest.length + 1 < 1024 := by omega
  have hc2 : rest.length + 2 < 1024 := by omega
  have hc3 : rest.length + 3 < 1024 := by omega
  have hc4 : rest.length + 4 < 1024 := by omega
  have hc5 : rest.length + 5 < 1024 := by omega
  have hc6 : rest.length + 6 < 1024 := by omega
  have hc7 : rest.length + 7 < 1024 := by omega
  have hc8 : rest.length + 8 < 1024 := by omega
  have hc9 : rest.length + 9 < 1024 := by omega
  have hc10 : rest.length + 10 < 1024 := by omega
  have hc11 : rest.length + 11 < 1024 := by omega
  have hc12 : rest.length + 12 < 1024 := by omega
  have hc13 : rest.length + 13 < 1024 := by omega
  have hc14 : rest.length + 14 < 1024 := by omega
  have hc15 : rest.length + 15 < 1024 := by omega
  have hc16 : rest.length + 16 < 1024 := by omega
  have hc17 : rest.length + 17 < 1024 := by omega
  have hc18 : rest.length + 18 < 1024 := by omega
  have hc19 : rest.length + 19 < 1024 := by omega
  have hc20 : rest.length + 20 < 1024 := by omega
  have hc21 : rest.length + 21 < 1024 := by omega
  have hc22 : rest.length + 22 < 1024 := by omega
  have hc23 : rest.length + 23 < 1024 := by omega
  have hc24 : rest.length + 24 < 1024 := by omega
  have hc25 : rest.length + 25 < 1024 := by omega
  have hc26 : rest.length + 26 < 1024 := by omega
  have hc27 : rest.length + 27 < 1024 := by omega
  have hc28 : rest.length + 28 < 1024 := by omega
  have hc29 : rest.length + 29 < 1024 := by omega
  have hc30 : rest.length + 30 < 1024 := by omega
  have hc31 : rest.length + 31 < 1024 := by omega
  have hc32 : rest.length + 32 < 1024 := by omega
  have hc33 : rest.length + 33 < 1024 := by omega
  have hc34 : rest.length + 34 < 1024 := by omega
  have hc35 : rest.length + 35 < 1024 := by omega
  have hc36 : rest.length + 36 < 1024 := by omega
  have hc37 : rest.length + 37 < 1024 := by omega
  have hc38 : rest.length + 38 < 1024 := by omega
  have hc39 : rest.length + 39 < 1024 := by omega
  have hc40 : rest.length + 40 < 1024 := by omega
  have hc41 : rest.length + 41 < 1024 := by omega
  have ha1728 : (1728 : UInt256).toNat = 1728 := rfl
  have hf1728 := HistoricalSearch.CRTMemoryBounds.activeWords_fix s 1728 32 (by decide) (by norm_num) hact
  have ha1600 : (1600 : UInt256).toNat = 1600 := rfl
  have hf1600 := HistoricalSearch.CRTMemoryBounds.activeWords_fix s 1600 32 (by decide) (by norm_num) hact
  simp [hz, hzn, retainpart0Program, retainpart0Model, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, Challenge.EvmProof.Word.literal_eq_ofNat, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8, hc9, hc10, hc11, hc12, hc13, hc14, hc15, hc16, hc17, hc18, hc19, hc20, hc21, hc22, hc23, hc24, hc25, hc26, hc27, hc28, hc29, hc30, hc31, hc32, hc33, hc34, hc35, hc36, hc37, hc38, hc39, hc40, hc41, ha1728, hf1728, ha1600, hf1600]

#print axioms retainpart0_run

def retainpart1Program : List Instr :=
  [.op (.Dup ⟨11, by decide⟩),
   .push 2 1568,
   .op .MLOAD,
   .push 2 1536,
   .op .MLOAD,
   .push 2 1504,
   .op .MLOAD]

def retainpart1Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 : UInt256) (rest : List UInt256) : State :=
  let v0 : UInt256 := MachineState.readWord s.memory 1568
  let v1 : UInt256 := MachineState.readWord s.memory 1536
  let v2 : UInt256 := MachineState.readWord s.memory 1504
  {s with pc := UInt256.ofNat 8182, memory := s.memory, stack := v2 :: v1 :: v0 :: x11 :: x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: x18 :: x19 :: x20 :: x21 :: x22 :: x23 :: x24 :: x25 :: x26 :: x27 :: x28 :: rest}

theorem retainpart1_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 982) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions retainpart1Program {s with pc := UInt256.ofNat 8169, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: x18 :: x19 :: x20 :: x21 :: x22 :: x23 :: x24 :: x25 :: x26 :: x27 :: x28 :: rest} =
      some (retainpart1Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 rest) := by
  have hz : ({val := 0} : UInt256) = UInt256.ofNat 0 := rfl
  have hzn : ({val := 0} : UInt256).toNat = 0 := rfl
  have hc0 : rest.length + 0 < 1024 := by omega
  have hc1 : rest.length + 1 < 1024 := by omega
  have hc2 : rest.length + 2 < 1024 := by omega
  have hc3 : rest.length + 3 < 1024 := by omega
  have hc4 : rest.length + 4 < 1024 := by omega
  have hc5 : rest.length + 5 < 1024 := by omega
  have hc6 : rest.length + 6 < 1024 := by omega
  have hc7 : rest.length + 7 < 1024 := by omega
  have hc8 : rest.length + 8 < 1024 := by omega
  have hc9 : rest.length + 9 < 1024 := by omega
  have hc10 : rest.length + 10 < 1024 := by omega
  have hc11 : rest.length + 11 < 1024 := by omega
  have hc12 : rest.length + 12 < 1024 := by omega
  have hc13 : rest.length + 13 < 1024 := by omega
  have hc14 : rest.length + 14 < 1024 := by omega
  have hc15 : rest.length + 15 < 1024 := by omega
  have hc16 : rest.length + 16 < 1024 := by omega
  have hc17 : rest.length + 17 < 1024 := by omega
  have hc18 : rest.length + 18 < 1024 := by omega
  have hc19 : rest.length + 19 < 1024 := by omega
  have hc20 : rest.length + 20 < 1024 := by omega
  have hc21 : rest.length + 21 < 1024 := by omega
  have hc22 : rest.length + 22 < 1024 := by omega
  have hc23 : rest.length + 23 < 1024 := by omega
  have hc24 : rest.length + 24 < 1024 := by omega
  have hc25 : rest.length + 25 < 1024 := by omega
  have hc26 : rest.length + 26 < 1024 := by omega
  have hc27 : rest.length + 27 < 1024 := by omega
  have hc28 : rest.length + 28 < 1024 := by omega
  have hc29 : rest.length + 29 < 1024 := by omega
  have hc30 : rest.length + 30 < 1024 := by omega
  have hc31 : rest.length + 31 < 1024 := by omega
  have hc32 : rest.length + 32 < 1024 := by omega
  have hc33 : rest.length + 33 < 1024 := by omega
  have hc34 : rest.length + 34 < 1024 := by omega
  have hc35 : rest.length + 35 < 1024 := by omega
  have hc36 : rest.length + 36 < 1024 := by omega
  have hc37 : rest.length + 37 < 1024 := by omega
  have hc38 : rest.length + 38 < 1024 := by omega
  have hc39 : rest.length + 39 < 1024 := by omega
  have hc40 : rest.length + 40 < 1024 := by omega
  have hc41 : rest.length + 41 < 1024 := by omega
  have ha1568 : (1568 : UInt256).toNat = 1568 := rfl
  have hf1568 := HistoricalSearch.CRTMemoryBounds.activeWords_fix s 1568 32 (by decide) (by norm_num) hact
  have ha1536 : (1536 : UInt256).toNat = 1536 := rfl
  have hf1536 := HistoricalSearch.CRTMemoryBounds.activeWords_fix s 1536 32 (by decide) (by norm_num) hact
  have ha1504 : (1504 : UInt256).toNat = 1504 := rfl
  have hf1504 := HistoricalSearch.CRTMemoryBounds.activeWords_fix s 1504 32 (by decide) (by norm_num) hact
  simp [hz, hzn, retainpart1Program, retainpart1Model, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, Challenge.EvmProof.Word.literal_eq_ofNat, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8, hc9, hc10, hc11, hc12, hc13, hc14, hc15, hc16, hc17, hc18, hc19, hc20, hc21, hc22, hc23, hc24, hc25, hc26, hc27, hc28, hc29, hc30, hc31, hc32, hc33, hc34, hc35, hc36, hc37, hc38, hc39, hc40, hc41, ha1568, hf1568, ha1536, hf1536, ha1504, hf1504]

#print axioms retainpart1_run

def retainpart2Program : List Instr :=
  [.push 2 1472,
   .op .MLOAD,
   .push 2 1440,
   .op .MLOAD,
   .push 2 1408,
   .op .MLOAD,
   .push 2 1376,
   .op .MLOAD]

def retainpart2Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 x32 : UInt256) (rest : List UInt256) : State :=
  let v0 : UInt256 := MachineState.readWord s.memory 1472
  let v1 : UInt256 := MachineState.readWord s.memory 1440
  let v2 : UInt256 := MachineState.readWord s.memory 1408
  let v3 : UInt256 := MachineState.readWord s.memory 1376
  {s with pc := UInt256.ofNat 8198, memory := s.memory, stack := v3 :: v2 :: v1 :: v0 :: x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: x18 :: x19 :: x20 :: x21 :: x22 :: x23 :: x24 :: x25 :: x26 :: x27 :: x28 :: x29 :: x30 :: x31 :: x32 :: rest}

theorem retainpart2_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 x32 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 982) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions retainpart2Program {s with pc := UInt256.ofNat 8182, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: x18 :: x19 :: x20 :: x21 :: x22 :: x23 :: x24 :: x25 :: x26 :: x27 :: x28 :: x29 :: x30 :: x31 :: x32 :: rest} =
      some (retainpart2Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 x32 rest) := by
  have hz : ({val := 0} : UInt256) = UInt256.ofNat 0 := rfl
  have hzn : ({val := 0} : UInt256).toNat = 0 := rfl
  have hc0 : rest.length + 0 < 1024 := by omega
  have hc1 : rest.length + 1 < 1024 := by omega
  have hc2 : rest.length + 2 < 1024 := by omega
  have hc3 : rest.length + 3 < 1024 := by omega
  have hc4 : rest.length + 4 < 1024 := by omega
  have hc5 : rest.length + 5 < 1024 := by omega
  have hc6 : rest.length + 6 < 1024 := by omega
  have hc7 : rest.length + 7 < 1024 := by omega
  have hc8 : rest.length + 8 < 1024 := by omega
  have hc9 : rest.length + 9 < 1024 := by omega
  have hc10 : rest.length + 10 < 1024 := by omega
  have hc11 : rest.length + 11 < 1024 := by omega
  have hc12 : rest.length + 12 < 1024 := by omega
  have hc13 : rest.length + 13 < 1024 := by omega
  have hc14 : rest.length + 14 < 1024 := by omega
  have hc15 : rest.length + 15 < 1024 := by omega
  have hc16 : rest.length + 16 < 1024 := by omega
  have hc17 : rest.length + 17 < 1024 := by omega
  have hc18 : rest.length + 18 < 1024 := by omega
  have hc19 : rest.length + 19 < 1024 := by omega
  have hc20 : rest.length + 20 < 1024 := by omega
  have hc21 : rest.length + 21 < 1024 := by omega
  have hc22 : rest.length + 22 < 1024 := by omega
  have hc23 : rest.length + 23 < 1024 := by omega
  have hc24 : rest.length + 24 < 1024 := by omega
  have hc25 : rest.length + 25 < 1024 := by omega
  have hc26 : rest.length + 26 < 1024 := by omega
  have hc27 : rest.length + 27 < 1024 := by omega
  have hc28 : rest.length + 28 < 1024 := by omega
  have hc29 : rest.length + 29 < 1024 := by omega
  have hc30 : rest.length + 30 < 1024 := by omega
  have hc31 : rest.length + 31 < 1024 := by omega
  have hc32 : rest.length + 32 < 1024 := by omega
  have hc33 : rest.length + 33 < 1024 := by omega
  have hc34 : rest.length + 34 < 1024 := by omega
  have hc35 : rest.length + 35 < 1024 := by omega
  have hc36 : rest.length + 36 < 1024 := by omega
  have hc37 : rest.length + 37 < 1024 := by omega
  have hc38 : rest.length + 38 < 1024 := by omega
  have hc39 : rest.length + 39 < 1024 := by omega
  have hc40 : rest.length + 40 < 1024 := by omega
  have hc41 : rest.length + 41 < 1024 := by omega
  have ha1472 : (1472 : UInt256).toNat = 1472 := rfl
  have hf1472 := HistoricalSearch.CRTMemoryBounds.activeWords_fix s 1472 32 (by decide) (by norm_num) hact
  have ha1440 : (1440 : UInt256).toNat = 1440 := rfl
  have hf1440 := HistoricalSearch.CRTMemoryBounds.activeWords_fix s 1440 32 (by decide) (by norm_num) hact
  have ha1408 : (1408 : UInt256).toNat = 1408 := rfl
  have hf1408 := HistoricalSearch.CRTMemoryBounds.activeWords_fix s 1408 32 (by decide) (by norm_num) hact
  have ha1376 : (1376 : UInt256).toNat = 1376 := rfl
  have hf1376 := HistoricalSearch.CRTMemoryBounds.activeWords_fix s 1376 32 (by decide) (by norm_num) hact
  simp [hz, hzn, retainpart2Program, retainpart2Model, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, Challenge.EvmProof.Word.literal_eq_ofNat, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8, hc9, hc10, hc11, hc12, hc13, hc14, hc15, hc16, hc17, hc18, hc19, hc20, hc21, hc22, hc23, hc24, hc25, hc26, hc27, hc28, hc29, hc30, hc31, hc32, hc33, hc34, hc35, hc36, hc37, hc38, hc39, hc40, hc41, ha1472, hf1472, ha1440, hf1440, ha1408, hf1408, ha1376, hf1376]

#print axioms retainpart2_run

def retainpart3Program : List Instr :=
  [.push 2 1344,
   .op .MLOAD,
   .push 1 96,
   .op .SHR,
   .op (.Dup ⟨1, by decide⟩),
   .push 1 148,
   .op .SHL,
   .op .OR]

def retainpart3Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 x32 x33 x34 x35 x36 : UInt256) (rest : List UInt256) : State :=
  let v0 : UInt256 := MachineState.readWord s.memory 1344
  let v1 : UInt256 := UInt256.shiftRight v0 (UInt256.ofNat 96)
  let v2 : UInt256 := UInt256.shiftLeft x0 (UInt256.ofNat 148)
  let v3 : UInt256 := UInt256.lor v2 v1
  {s with pc := UInt256.ofNat 8210, memory := s.memory, stack := v3 :: x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: x18 :: x19 :: x20 :: x21 :: x22 :: x23 :: x24 :: x25 :: x26 :: x27 :: x28 :: x29 :: x30 :: x31 :: x32 :: x33 :: x34 :: x35 :: x36 :: rest}

theorem retainpart3_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 x32 x33 x34 x35 x36 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 982) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions retainpart3Program {s with pc := UInt256.ofNat 8198, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: x18 :: x19 :: x20 :: x21 :: x22 :: x23 :: x24 :: x25 :: x26 :: x27 :: x28 :: x29 :: x30 :: x31 :: x32 :: x33 :: x34 :: x35 :: x36 :: rest} =
      some (retainpart3Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 x32 x33 x34 x35 x36 rest) := by
  have hz : ({val := 0} : UInt256) = UInt256.ofNat 0 := rfl
  have hzn : ({val := 0} : UInt256).toNat = 0 := rfl
  have hc0 : rest.length + 0 < 1024 := by omega
  have hc1 : rest.length + 1 < 1024 := by omega
  have hc2 : rest.length + 2 < 1024 := by omega
  have hc3 : rest.length + 3 < 1024 := by omega
  have hc4 : rest.length + 4 < 1024 := by omega
  have hc5 : rest.length + 5 < 1024 := by omega
  have hc6 : rest.length + 6 < 1024 := by omega
  have hc7 : rest.length + 7 < 1024 := by omega
  have hc8 : rest.length + 8 < 1024 := by omega
  have hc9 : rest.length + 9 < 1024 := by omega
  have hc10 : rest.length + 10 < 1024 := by omega
  have hc11 : rest.length + 11 < 1024 := by omega
  have hc12 : rest.length + 12 < 1024 := by omega
  have hc13 : rest.length + 13 < 1024 := by omega
  have hc14 : rest.length + 14 < 1024 := by omega
  have hc15 : rest.length + 15 < 1024 := by omega
  have hc16 : rest.length + 16 < 1024 := by omega
  have hc17 : rest.length + 17 < 1024 := by omega
  have hc18 : rest.length + 18 < 1024 := by omega
  have hc19 : rest.length + 19 < 1024 := by omega
  have hc20 : rest.length + 20 < 1024 := by omega
  have hc21 : rest.length + 21 < 1024 := by omega
  have hc22 : rest.length + 22 < 1024 := by omega
  have hc23 : rest.length + 23 < 1024 := by omega
  have hc24 : rest.length + 24 < 1024 := by omega
  have hc25 : rest.length + 25 < 1024 := by omega
  have hc26 : rest.length + 26 < 1024 := by omega
  have hc27 : rest.length + 27 < 1024 := by omega
  have hc28 : rest.length + 28 < 1024 := by omega
  have hc29 : rest.length + 29 < 1024 := by omega
  have hc30 : rest.length + 30 < 1024 := by omega
  have hc31 : rest.length + 31 < 1024 := by omega
  have hc32 : rest.length + 32 < 1024 := by omega
  have hc33 : rest.length + 33 < 1024 := by omega
  have hc34 : rest.length + 34 < 1024 := by omega
  have hc35 : rest.length + 35 < 1024 := by omega
  have hc36 : rest.length + 36 < 1024 := by omega
  have hc37 : rest.length + 37 < 1024 := by omega
  have hc38 : rest.length + 38 < 1024 := by omega
  have hc39 : rest.length + 39 < 1024 := by omega
  have hc40 : rest.length + 40 < 1024 := by omega
  have hc41 : rest.length + 41 < 1024 := by omega
  have ha1344 : (1344 : UInt256).toNat = 1344 := rfl
  have hf1344 := HistoricalSearch.CRTMemoryBounds.activeWords_fix s 1344 32 (by decide) (by norm_num) hact
  simp [hz, hzn, retainpart3Program, retainpart3Model, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, Challenge.EvmProof.Word.literal_eq_ofNat, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8, hc9, hc10, hc11, hc12, hc13, hc14, hc15, hc16, hc17, hc18, hc19, hc20, hc21, hc22, hc23, hc24, hc25, hc26, hc27, hc28, hc29, hc30, hc31, hc32, hc33, hc34, hc35, hc36, hc37, hc38, hc39, hc40, hc41, ha1344, hf1344]

#print axioms retainpart3_run

def retainpart4Program : List Instr :=
  [.op (.Dup ⟨8, by decide⟩),
   .op .AND,
   .push 2 768,
   .op .MSTORE,
   .push 1 96,
   .op .SHR,
   .op (.Dup ⟨1, by decide⟩),
   .push 1 148]

def retainpart4Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 x32 x33 x34 x35 x36 x37 : UInt256) (rest : List UInt256) : State :=
  let v0 : UInt256 := UInt256.land x8 x0
  let v1 : ByteArray := MachineState.writeBytes s.memory (Data.Bytes.natToBytesPadded v0.toNat 32) 768
  let v2 : UInt256 := UInt256.shiftRight x1 (UInt256.ofNat 96)
  {s with pc := UInt256.ofNat 8222, memory := v1, stack := (UInt256.ofNat 148) :: x2 :: v2 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: x18 :: x19 :: x20 :: x21 :: x22 :: x23 :: x24 :: x25 :: x26 :: x27 :: x28 :: x29 :: x30 :: x31 :: x32 :: x33 :: x34 :: x35 :: x36 :: x37 :: rest}

theorem retainpart4_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 x32 x33 x34 x35 x36 x37 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 982) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions retainpart4Program {s with pc := UInt256.ofNat 8210, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: x18 :: x19 :: x20 :: x21 :: x22 :: x23 :: x24 :: x25 :: x26 :: x27 :: x28 :: x29 :: x30 :: x31 :: x32 :: x33 :: x34 :: x35 :: x36 :: x37 :: rest} =
      some (retainpart4Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 x32 x33 x34 x35 x36 x37 rest) := by
  have hz : ({val := 0} : UInt256) = UInt256.ofNat 0 := rfl
  have hzn : ({val := 0} : UInt256).toNat = 0 := rfl
  have hc0 : rest.length + 0 < 1024 := by omega
  have hc1 : rest.length + 1 < 1024 := by omega
  have hc2 : rest.length + 2 < 1024 := by omega
  have hc3 : rest.length + 3 < 1024 := by omega
  have hc4 : rest.length + 4 < 1024 := by omega
  have hc5 : rest.length + 5 < 1024 := by omega
  have hc6 : rest.length + 6 < 1024 := by omega
  have hc7 : rest.length + 7 < 1024 := by omega
  have hc8 : rest.length + 8 < 1024 := by omega
  have hc9 : rest.length + 9 < 1024 := by omega
  have hc10 : rest.length + 10 < 1024 := by omega
  have hc11 : rest.length + 11 < 1024 := by omega
  have hc12 : rest.length + 12 < 1024 := by omega
  have hc13 : rest.length + 13 < 1024 := by omega
  have hc14 : rest.length + 14 < 1024 := by omega
  have hc15 : rest.length + 15 < 1024 := by omega
  have hc16 : rest.length + 16 < 1024 := by omega
  have hc17 : rest.length + 17 < 1024 := by omega
  have hc18 : rest.length + 18 < 1024 := by omega
  have hc19 : rest.length + 19 < 1024 := by omega
  have hc20 : rest.length + 20 < 1024 := by omega
  have hc21 : rest.length + 21 < 1024 := by omega
  have hc22 : rest.length + 22 < 1024 := by omega
  have hc23 : rest.length + 23 < 1024 := by omega
  have hc24 : rest.length + 24 < 1024 := by omega
  have hc25 : rest.length + 25 < 1024 := by omega
  have hc26 : rest.length + 26 < 1024 := by omega
  have hc27 : rest.length + 27 < 1024 := by omega
  have hc28 : rest.length + 28 < 1024 := by omega
  have hc29 : rest.length + 29 < 1024 := by omega
  have hc30 : rest.length + 30 < 1024 := by omega
  have hc31 : rest.length + 31 < 1024 := by omega
  have hc32 : rest.length + 32 < 1024 := by omega
  have hc33 : rest.length + 33 < 1024 := by omega
  have hc34 : rest.length + 34 < 1024 := by omega
  have hc35 : rest.length + 35 < 1024 := by omega
  have hc36 : rest.length + 36 < 1024 := by omega
  have hc37 : rest.length + 37 < 1024 := by omega
  have hc38 : rest.length + 38 < 1024 := by omega
  have hc39 : rest.length + 39 < 1024 := by omega
  have hc40 : rest.length + 40 < 1024 := by omega
  have hc41 : rest.length + 41 < 1024 := by omega
  have ha768 : (768 : UInt256).toNat = 768 := rfl
  have hf768 := HistoricalSearch.CRTMemoryBounds.activeWords_fix s 768 32 (by decide) (by norm_num) hact
  simp [hz, hzn, retainpart4Program, retainpart4Model, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, Challenge.EvmProof.Word.literal_eq_ofNat, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8, hc9, hc10, hc11, hc12, hc13, hc14, hc15, hc16, hc17, hc18, hc19, hc20, hc21, hc22, hc23, hc24, hc25, hc26, hc27, hc28, hc29, hc30, hc31, hc32, hc33, hc34, hc35, hc36, hc37, hc38, hc39, hc40, hc41, ha768, hf768]

#print axioms retainpart4_run

def retainpart5Program : List Instr :=
  [.op .SHL,
   .op .OR,
   .op (.Dup ⟨7, by decide⟩),
   .op .AND,
   .push 2 800,
   .op .MSTORE,
   .push 1 96,
   .op .SHR]

def retainpart5Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 x32 x33 x34 x35 x36 x37 x38 : UInt256) (rest : List UInt256) : State :=
  let v0 : UInt256 := UInt256.shiftLeft x1 x0
  let v1 : UInt256 := UInt256.lor v0 x2
  let v2 : UInt256 := UInt256.land x9 v1
  let v3 : ByteArray := MachineState.writeBytes s.memory (Data.Bytes.natToBytesPadded v2.toNat 32) 800
  let v4 : UInt256 := UInt256.shiftRight x3 (UInt256.ofNat 96)
  {s with pc := UInt256.ofNat 8233, memory := v3, stack := v4 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: x18 :: x19 :: x20 :: x21 :: x22 :: x23 :: x24 :: x25 :: x26 :: x27 :: x28 :: x29 :: x30 :: x31 :: x32 :: x33 :: x34 :: x35 :: x36 :: x37 :: x38 :: rest}

theorem retainpart5_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 x32 x33 x34 x35 x36 x37 x38 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 982) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions retainpart5Program {s with pc := UInt256.ofNat 8222, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: x18 :: x19 :: x20 :: x21 :: x22 :: x23 :: x24 :: x25 :: x26 :: x27 :: x28 :: x29 :: x30 :: x31 :: x32 :: x33 :: x34 :: x35 :: x36 :: x37 :: x38 :: rest} =
      some (retainpart5Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 x32 x33 x34 x35 x36 x37 x38 rest) := by
  have hz : ({val := 0} : UInt256) = UInt256.ofNat 0 := rfl
  have hzn : ({val := 0} : UInt256).toNat = 0 := rfl
  have hc0 : rest.length + 0 < 1024 := by omega
  have hc1 : rest.length + 1 < 1024 := by omega
  have hc2 : rest.length + 2 < 1024 := by omega
  have hc3 : rest.length + 3 < 1024 := by omega
  have hc4 : rest.length + 4 < 1024 := by omega
  have hc5 : rest.length + 5 < 1024 := by omega
  have hc6 : rest.length + 6 < 1024 := by omega
  have hc7 : rest.length + 7 < 1024 := by omega
  have hc8 : rest.length + 8 < 1024 := by omega
  have hc9 : rest.length + 9 < 1024 := by omega
  have hc10 : rest.length + 10 < 1024 := by omega
  have hc11 : rest.length + 11 < 1024 := by omega
  have hc12 : rest.length + 12 < 1024 := by omega
  have hc13 : rest.length + 13 < 1024 := by omega
  have hc14 : rest.length + 14 < 1024 := by omega
  have hc15 : rest.length + 15 < 1024 := by omega
  have hc16 : rest.length + 16 < 1024 := by omega
  have hc17 : rest.length + 17 < 1024 := by omega
  have hc18 : rest.length + 18 < 1024 := by omega
  have hc19 : rest.length + 19 < 1024 := by omega
  have hc20 : rest.length + 20 < 1024 := by omega
  have hc21 : rest.length + 21 < 1024 := by omega
  have hc22 : rest.length + 22 < 1024 := by omega
  have hc23 : rest.length + 23 < 1024 := by omega
  have hc24 : rest.length + 24 < 1024 := by omega
  have hc25 : rest.length + 25 < 1024 := by omega
  have hc26 : rest.length + 26 < 1024 := by omega
  have hc27 : rest.length + 27 < 1024 := by omega
  have hc28 : rest.length + 28 < 1024 := by omega
  have hc29 : rest.length + 29 < 1024 := by omega
  have hc30 : rest.length + 30 < 1024 := by omega
  have hc31 : rest.length + 31 < 1024 := by omega
  have hc32 : rest.length + 32 < 1024 := by omega
  have hc33 : rest.length + 33 < 1024 := by omega
  have hc34 : rest.length + 34 < 1024 := by omega
  have hc35 : rest.length + 35 < 1024 := by omega
  have hc36 : rest.length + 36 < 1024 := by omega
  have hc37 : rest.length + 37 < 1024 := by omega
  have hc38 : rest.length + 38 < 1024 := by omega
  have hc39 : rest.length + 39 < 1024 := by omega
  have hc40 : rest.length + 40 < 1024 := by omega
  have hc41 : rest.length + 41 < 1024 := by omega
  have ha800 : (800 : UInt256).toNat = 800 := rfl
  have hf800 := HistoricalSearch.CRTMemoryBounds.activeWords_fix s 800 32 (by decide) (by norm_num) hact
  simp [hz, hzn, retainpart5Program, retainpart5Model, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, Challenge.EvmProof.Word.literal_eq_ofNat, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8, hc9, hc10, hc11, hc12, hc13, hc14, hc15, hc16, hc17, hc18, hc19, hc20, hc21, hc22, hc23, hc24, hc25, hc26, hc27, hc28, hc29, hc30, hc31, hc32, hc33, hc34, hc35, hc36, hc37, hc38, hc39, hc40, hc41, ha800, hf800]

#print axioms retainpart5_run

def retainpart6Program : List Instr :=
  [.op (.Dup ⟨1, by decide⟩),
   .push 1 148,
   .op .SHL,
   .op .OR,
   .op (.Dup ⟨6, by decide⟩),
   .op .AND,
   .push 2 832,
   .op .MSTORE]

def retainpart6Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 x32 x33 x34 x35 : UInt256) (rest : List UInt256) : State :=
  let v0 : UInt256 := UInt256.shiftLeft x1 (UInt256.ofNat 148)
  let v1 : UInt256 := UInt256.lor v0 x0
  let v2 : UInt256 := UInt256.land x6 v1
  let v3 : ByteArray := MachineState.writeBytes s.memory (Data.Bytes.natToBytesPadded v2.toNat 32) 832
  {s with pc := UInt256.ofNat 8244, memory := v3, stack := x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: x18 :: x19 :: x20 :: x21 :: x22 :: x23 :: x24 :: x25 :: x26 :: x27 :: x28 :: x29 :: x30 :: x31 :: x32 :: x33 :: x34 :: x35 :: rest}

theorem retainpart6_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 x32 x33 x34 x35 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 982) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions retainpart6Program {s with pc := UInt256.ofNat 8233, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: x18 :: x19 :: x20 :: x21 :: x22 :: x23 :: x24 :: x25 :: x26 :: x27 :: x28 :: x29 :: x30 :: x31 :: x32 :: x33 :: x34 :: x35 :: rest} =
      some (retainpart6Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 x32 x33 x34 x35 rest) := by
  have hz : ({val := 0} : UInt256) = UInt256.ofNat 0 := rfl
  have hzn : ({val := 0} : UInt256).toNat = 0 := rfl
  have hc0 : rest.length + 0 < 1024 := by omega
  have hc1 : rest.length + 1 < 1024 := by omega
  have hc2 : rest.length + 2 < 1024 := by omega
  have hc3 : rest.length + 3 < 1024 := by omega
  have hc4 : rest.length + 4 < 1024 := by omega
  have hc5 : rest.length + 5 < 1024 := by omega
  have hc6 : rest.length + 6 < 1024 := by omega
  have hc7 : rest.length + 7 < 1024 := by omega
  have hc8 : rest.length + 8 < 1024 := by omega
  have hc9 : rest.length + 9 < 1024 := by omega
  have hc10 : rest.length + 10 < 1024 := by omega
  have hc11 : rest.length + 11 < 1024 := by omega
  have hc12 : rest.length + 12 < 1024 := by omega
  have hc13 : rest.length + 13 < 1024 := by omega
  have hc14 : rest.length + 14 < 1024 := by omega
  have hc15 : rest.length + 15 < 1024 := by omega
  have hc16 : rest.length + 16 < 1024 := by omega
  have hc17 : rest.length + 17 < 1024 := by omega
  have hc18 : rest.length + 18 < 1024 := by omega
  have hc19 : rest.length + 19 < 1024 := by omega
  have hc20 : rest.length + 20 < 1024 := by omega
  have hc21 : rest.length + 21 < 1024 := by omega
  have hc22 : rest.length + 22 < 1024 := by omega
  have hc23 : rest.length + 23 < 1024 := by omega
  have hc24 : rest.length + 24 < 1024 := by omega
  have hc25 : rest.length + 25 < 1024 := by omega
  have hc26 : rest.length + 26 < 1024 := by omega
  have hc27 : rest.length + 27 < 1024 := by omega
  have hc28 : rest.length + 28 < 1024 := by omega
  have hc29 : rest.length + 29 < 1024 := by omega
  have hc30 : rest.length + 30 < 1024 := by omega
  have hc31 : rest.length + 31 < 1024 := by omega
  have hc32 : rest.length + 32 < 1024 := by omega
  have hc33 : rest.length + 33 < 1024 := by omega
  have hc34 : rest.length + 34 < 1024 := by omega
  have hc35 : rest.length + 35 < 1024 := by omega
  have hc36 : rest.length + 36 < 1024 := by omega
  have hc37 : rest.length + 37 < 1024 := by omega
  have hc38 : rest.length + 38 < 1024 := by omega
  have hc39 : rest.length + 39 < 1024 := by omega
  have hc40 : rest.length + 40 < 1024 := by omega
  have hc41 : rest.length + 41 < 1024 := by omega
  have ha832 : (832 : UInt256).toNat = 832 := rfl
  have hf832 := HistoricalSearch.CRTMemoryBounds.activeWords_fix s 832 32 (by decide) (by norm_num) hact
  simp [hz, hzn, retainpart6Program, retainpart6Model, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, Challenge.EvmProof.Word.literal_eq_ofNat, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8, hc9, hc10, hc11, hc12, hc13, hc14, hc15, hc16, hc17, hc18, hc19, hc20, hc21, hc22, hc23, hc24, hc25, hc26, hc27, hc28, hc29, hc30, hc31, hc32, hc33, hc34, hc35, hc36, hc37, hc38, hc39, hc40, hc41, ha832, hf832]

#print axioms retainpart6_run

def retainpart7Program : List Instr :=
  [.push 1 96,
   .op .SHR,
   .op (.Dup ⟨1, by decide⟩),
   .push 1 148,
   .op .SHL,
   .op .OR,
   .op (.Dup ⟨5, by decide⟩),
   .op .AND]

def retainpart7Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 x32 x33 x34 : UInt256) (rest : List UInt256) : State :=
  let v0 : UInt256 := UInt256.shiftRight x0 (UInt256.ofNat 96)
  let v1 : UInt256 := UInt256.shiftLeft x1 (UInt256.ofNat 148)
  let v2 : UInt256 := UInt256.lor v1 v0
  let v3 : UInt256 := UInt256.land x5 v2
  {s with pc := UInt256.ofNat 8254, memory := s.memory, stack := v3 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: x18 :: x19 :: x20 :: x21 :: x22 :: x23 :: x24 :: x25 :: x26 :: x27 :: x28 :: x29 :: x30 :: x31 :: x32 :: x33 :: x34 :: rest}

theorem retainpart7_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 x32 x33 x34 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 982) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions retainpart7Program {s with pc := UInt256.ofNat 8244, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: x18 :: x19 :: x20 :: x21 :: x22 :: x23 :: x24 :: x25 :: x26 :: x27 :: x28 :: x29 :: x30 :: x31 :: x32 :: x33 :: x34 :: rest} =
      some (retainpart7Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 x32 x33 x34 rest) := by
  have hz : ({val := 0} : UInt256) = UInt256.ofNat 0 := rfl
  have hzn : ({val := 0} : UInt256).toNat = 0 := rfl
  have hc0 : rest.length + 0 < 1024 := by omega
  have hc1 : rest.length + 1 < 1024 := by omega
  have hc2 : rest.length + 2 < 1024 := by omega
  have hc3 : rest.length + 3 < 1024 := by omega
  have hc4 : rest.length + 4 < 1024 := by omega
  have hc5 : rest.length + 5 < 1024 := by omega
  have hc6 : rest.length + 6 < 1024 := by omega
  have hc7 : rest.length + 7 < 1024 := by omega
  have hc8 : rest.length + 8 < 1024 := by omega
  have hc9 : rest.length + 9 < 1024 := by omega
  have hc10 : rest.length + 10 < 1024 := by omega
  have hc11 : rest.length + 11 < 1024 := by omega
  have hc12 : rest.length + 12 < 1024 := by omega
  have hc13 : rest.length + 13 < 1024 := by omega
  have hc14 : rest.length + 14 < 1024 := by omega
  have hc15 : rest.length + 15 < 1024 := by omega
  have hc16 : rest.length + 16 < 1024 := by omega
  have hc17 : rest.length + 17 < 1024 := by omega
  have hc18 : rest.length + 18 < 1024 := by omega
  have hc19 : rest.length + 19 < 1024 := by omega
  have hc20 : rest.length + 20 < 1024 := by omega
  have hc21 : rest.length + 21 < 1024 := by omega
  have hc22 : rest.length + 22 < 1024 := by omega
  have hc23 : rest.length + 23 < 1024 := by omega
  have hc24 : rest.length + 24 < 1024 := by omega
  have hc25 : rest.length + 25 < 1024 := by omega
  have hc26 : rest.length + 26 < 1024 := by omega
  have hc27 : rest.length + 27 < 1024 := by omega
  have hc28 : rest.length + 28 < 1024 := by omega
  have hc29 : rest.length + 29 < 1024 := by omega
  have hc30 : rest.length + 30 < 1024 := by omega
  have hc31 : rest.length + 31 < 1024 := by omega
  have hc32 : rest.length + 32 < 1024 := by omega
  have hc33 : rest.length + 33 < 1024 := by omega
  have hc34 : rest.length + 34 < 1024 := by omega
  have hc35 : rest.length + 35 < 1024 := by omega
  have hc36 : rest.length + 36 < 1024 := by omega
  have hc37 : rest.length + 37 < 1024 := by omega
  have hc38 : rest.length + 38 < 1024 := by omega
  have hc39 : rest.length + 39 < 1024 := by omega
  have hc40 : rest.length + 40 < 1024 := by omega
  have hc41 : rest.length + 41 < 1024 := by omega
  simp [hz, hzn, retainpart7Program, retainpart7Model, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, Challenge.EvmProof.Word.literal_eq_ofNat, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8, hc9, hc10, hc11, hc12, hc13, hc14, hc15, hc16, hc17, hc18, hc19, hc20, hc21, hc22, hc23, hc24, hc25, hc26, hc27, hc28, hc29, hc30, hc31, hc32, hc33, hc34, hc35, hc36, hc37, hc38, hc39, hc40, hc41]

#print axioms retainpart7_run

def retainpart8Program : List Instr :=
  [.push 2 864,
   .op .MSTORE,
   .push 1 96,
   .op .SHR,
   .op (.Dup ⟨1, by decide⟩),
   .push 1 148,
   .op .SHL,
   .op .OR]

def retainpart8Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 x32 x33 x34 : UInt256) (rest : List UInt256) : State :=
  let v0 : ByteArray := MachineState.writeBytes s.memory (Data.Bytes.natToBytesPadded x0.toNat 32) 864
  let v1 : UInt256 := UInt256.shiftRight x1 (UInt256.ofNat 96)
  let v2 : UInt256 := UInt256.shiftLeft x2 (UInt256.ofNat 148)
  let v3 : UInt256 := UInt256.lor v2 v1
  {s with pc := UInt256.ofNat 8266, memory := v0, stack := v3 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: x18 :: x19 :: x20 :: x21 :: x22 :: x23 :: x24 :: x25 :: x26 :: x27 :: x28 :: x29 :: x30 :: x31 :: x32 :: x33 :: x34 :: rest}

theorem retainpart8_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 x32 x33 x34 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 982) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions retainpart8Program {s with pc := UInt256.ofNat 8254, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: x18 :: x19 :: x20 :: x21 :: x22 :: x23 :: x24 :: x25 :: x26 :: x27 :: x28 :: x29 :: x30 :: x31 :: x32 :: x33 :: x34 :: rest} =
      some (retainpart8Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 x32 x33 x34 rest) := by
  have hz : ({val := 0} : UInt256) = UInt256.ofNat 0 := rfl
  have hzn : ({val := 0} : UInt256).toNat = 0 := rfl
  have hc0 : rest.length + 0 < 1024 := by omega
  have hc1 : rest.length + 1 < 1024 := by omega
  have hc2 : rest.length + 2 < 1024 := by omega
  have hc3 : rest.length + 3 < 1024 := by omega
  have hc4 : rest.length + 4 < 1024 := by omega
  have hc5 : rest.length + 5 < 1024 := by omega
  have hc6 : rest.length + 6 < 1024 := by omega
  have hc7 : rest.length + 7 < 1024 := by omega
  have hc8 : rest.length + 8 < 1024 := by omega
  have hc9 : rest.length + 9 < 1024 := by omega
  have hc10 : rest.length + 10 < 1024 := by omega
  have hc11 : rest.length + 11 < 1024 := by omega
  have hc12 : rest.length + 12 < 1024 := by omega
  have hc13 : rest.length + 13 < 1024 := by omega
  have hc14 : rest.length + 14 < 1024 := by omega
  have hc15 : rest.length + 15 < 1024 := by omega
  have hc16 : rest.length + 16 < 1024 := by omega
  have hc17 : rest.length + 17 < 1024 := by omega
  have hc18 : rest.length + 18 < 1024 := by omega
  have hc19 : rest.length + 19 < 1024 := by omega
  have hc20 : rest.length + 20 < 1024 := by omega
  have hc21 : rest.length + 21 < 1024 := by omega
  have hc22 : rest.length + 22 < 1024 := by omega
  have hc23 : rest.length + 23 < 1024 := by omega
  have hc24 : rest.length + 24 < 1024 := by omega
  have hc25 : rest.length + 25 < 1024 := by omega
  have hc26 : rest.length + 26 < 1024 := by omega
  have hc27 : rest.length + 27 < 1024 := by omega
  have hc28 : rest.length + 28 < 1024 := by omega
  have hc29 : rest.length + 29 < 1024 := by omega
  have hc30 : rest.length + 30 < 1024 := by omega
  have hc31 : rest.length + 31 < 1024 := by omega
  have hc32 : rest.length + 32 < 1024 := by omega
  have hc33 : rest.length + 33 < 1024 := by omega
  have hc34 : rest.length + 34 < 1024 := by omega
  have hc35 : rest.length + 35 < 1024 := by omega
  have hc36 : rest.length + 36 < 1024 := by omega
  have hc37 : rest.length + 37 < 1024 := by omega
  have hc38 : rest.length + 38 < 1024 := by omega
  have hc39 : rest.length + 39 < 1024 := by omega
  have hc40 : rest.length + 40 < 1024 := by omega
  have hc41 : rest.length + 41 < 1024 := by omega
  have ha864 : (864 : UInt256).toNat = 864 := rfl
  have hf864 := HistoricalSearch.CRTMemoryBounds.activeWords_fix s 864 32 (by decide) (by norm_num) hact
  simp [hz, hzn, retainpart8Program, retainpart8Model, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, Challenge.EvmProof.Word.literal_eq_ofNat, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8, hc9, hc10, hc11, hc12, hc13, hc14, hc15, hc16, hc17, hc18, hc19, hc20, hc21, hc22, hc23, hc24, hc25, hc26, hc27, hc28, hc29, hc30, hc31, hc32, hc33, hc34, hc35, hc36, hc37, hc38, hc39, hc40, hc41, ha864, hf864]

#print axioms retainpart8_run

def retainpart9Program : List Instr :=
  [.op (.Dup ⟨4, by decide⟩),
   .op .AND,
   .push 2 896,
   .op .MSTORE,
   .push 1 96,
   .op .SHR,
   .op (.Dup ⟨1, by decide⟩),
   .push 1 148]

def retainpart9Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 x32 x33 : UInt256) (rest : List UInt256) : State :=
  let v0 : UInt256 := UInt256.land x4 x0
  let v1 : ByteArray := MachineState.writeBytes s.memory (Data.Bytes.natToBytesPadded v0.toNat 32) 896
  let v2 : UInt256 := UInt256.shiftRight x1 (UInt256.ofNat 96)
  {s with pc := UInt256.ofNat 8278, memory := v1, stack := (UInt256.ofNat 148) :: x2 :: v2 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: x18 :: x19 :: x20 :: x21 :: x22 :: x23 :: x24 :: x25 :: x26 :: x27 :: x28 :: x29 :: x30 :: x31 :: x32 :: x33 :: rest}

theorem retainpart9_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 x32 x33 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 982) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions retainpart9Program {s with pc := UInt256.ofNat 8266, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: x18 :: x19 :: x20 :: x21 :: x22 :: x23 :: x24 :: x25 :: x26 :: x27 :: x28 :: x29 :: x30 :: x31 :: x32 :: x33 :: rest} =
      some (retainpart9Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 x32 x33 rest) := by
  have hz : ({val := 0} : UInt256) = UInt256.ofNat 0 := rfl
  have hzn : ({val := 0} : UInt256).toNat = 0 := rfl
  have hc0 : rest.length + 0 < 1024 := by omega
  have hc1 : rest.length + 1 < 1024 := by omega
  have hc2 : rest.length + 2 < 1024 := by omega
  have hc3 : rest.length + 3 < 1024 := by omega
  have hc4 : rest.length + 4 < 1024 := by omega
  have hc5 : rest.length + 5 < 1024 := by omega
  have hc6 : rest.length + 6 < 1024 := by omega
  have hc7 : rest.length + 7 < 1024 := by omega
  have hc8 : rest.length + 8 < 1024 := by omega
  have hc9 : rest.length + 9 < 1024 := by omega
  have hc10 : rest.length + 10 < 1024 := by omega
  have hc11 : rest.length + 11 < 1024 := by omega
  have hc12 : rest.length + 12 < 1024 := by omega
  have hc13 : rest.length + 13 < 1024 := by omega
  have hc14 : rest.length + 14 < 1024 := by omega
  have hc15 : rest.length + 15 < 1024 := by omega
  have hc16 : rest.length + 16 < 1024 := by omega
  have hc17 : rest.length + 17 < 1024 := by omega
  have hc18 : rest.length + 18 < 1024 := by omega
  have hc19 : rest.length + 19 < 1024 := by omega
  have hc20 : rest.length + 20 < 1024 := by omega
  have hc21 : rest.length + 21 < 1024 := by omega
  have hc22 : rest.length + 22 < 1024 := by omega
  have hc23 : rest.length + 23 < 1024 := by omega
  have hc24 : rest.length + 24 < 1024 := by omega
  have hc25 : rest.length + 25 < 1024 := by omega
  have hc26 : rest.length + 26 < 1024 := by omega
  have hc27 : rest.length + 27 < 1024 := by omega
  have hc28 : rest.length + 28 < 1024 := by omega
  have hc29 : rest.length + 29 < 1024 := by omega
  have hc30 : rest.length + 30 < 1024 := by omega
  have hc31 : rest.length + 31 < 1024 := by omega
  have hc32 : rest.length + 32 < 1024 := by omega
  have hc33 : rest.length + 33 < 1024 := by omega
  have hc34 : rest.length + 34 < 1024 := by omega
  have hc35 : rest.length + 35 < 1024 := by omega
  have hc36 : rest.length + 36 < 1024 := by omega
  have hc37 : rest.length + 37 < 1024 := by omega
  have hc38 : rest.length + 38 < 1024 := by omega
  have hc39 : rest.length + 39 < 1024 := by omega
  have hc40 : rest.length + 40 < 1024 := by omega
  have hc41 : rest.length + 41 < 1024 := by omega
  have ha896 : (896 : UInt256).toNat = 896 := rfl
  have hf896 := HistoricalSearch.CRTMemoryBounds.activeWords_fix s 896 32 (by decide) (by norm_num) hact
  simp [hz, hzn, retainpart9Program, retainpart9Model, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, Challenge.EvmProof.Word.literal_eq_ofNat, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8, hc9, hc10, hc11, hc12, hc13, hc14, hc15, hc16, hc17, hc18, hc19, hc20, hc21, hc22, hc23, hc24, hc25, hc26, hc27, hc28, hc29, hc30, hc31, hc32, hc33, hc34, hc35, hc36, hc37, hc38, hc39, hc40, hc41, ha896, hf896]

#print axioms retainpart9_run

def retainpart10Program : List Instr :=
  [.op .SHL,
   .op .OR,
   .op (.Dup ⟨3, by decide⟩),
   .op .AND,
   .push 2 928,
   .op .MSTORE,
   .push 1 96,
   .op .SHR]

def retainpart10Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 x32 x33 x34 : UInt256) (rest : List UInt256) : State :=
  let v0 : UInt256 := UInt256.shiftLeft x1 x0
  let v1 : UInt256 := UInt256.lor v0 x2
  let v2 : UInt256 := UInt256.land x5 v1
  let v3 : ByteArray := MachineState.writeBytes s.memory (Data.Bytes.natToBytesPadded v2.toNat 32) 928
  let v4 : UInt256 := UInt256.shiftRight x3 (UInt256.ofNat 96)
  {s with pc := UInt256.ofNat 8289, memory := v3, stack := v4 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: x18 :: x19 :: x20 :: x21 :: x22 :: x23 :: x24 :: x25 :: x26 :: x27 :: x28 :: x29 :: x30 :: x31 :: x32 :: x33 :: x34 :: rest}

theorem retainpart10_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 x32 x33 x34 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 982) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions retainpart10Program {s with pc := UInt256.ofNat 8278, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: x18 :: x19 :: x20 :: x21 :: x22 :: x23 :: x24 :: x25 :: x26 :: x27 :: x28 :: x29 :: x30 :: x31 :: x32 :: x33 :: x34 :: rest} =
      some (retainpart10Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 x32 x33 x34 rest) := by
  have hz : ({val := 0} : UInt256) = UInt256.ofNat 0 := rfl
  have hzn : ({val := 0} : UInt256).toNat = 0 := rfl
  have hc0 : rest.length + 0 < 1024 := by omega
  have hc1 : rest.length + 1 < 1024 := by omega
  have hc2 : rest.length + 2 < 1024 := by omega
  have hc3 : rest.length + 3 < 1024 := by omega
  have hc4 : rest.length + 4 < 1024 := by omega
  have hc5 : rest.length + 5 < 1024 := by omega
  have hc6 : rest.length + 6 < 1024 := by omega
  have hc7 : rest.length + 7 < 1024 := by omega
  have hc8 : rest.length + 8 < 1024 := by omega
  have hc9 : rest.length + 9 < 1024 := by omega
  have hc10 : rest.length + 10 < 1024 := by omega
  have hc11 : rest.length + 11 < 1024 := by omega
  have hc12 : rest.length + 12 < 1024 := by omega
  have hc13 : rest.length + 13 < 1024 := by omega
  have hc14 : rest.length + 14 < 1024 := by omega
  have hc15 : rest.length + 15 < 1024 := by omega
  have hc16 : rest.length + 16 < 1024 := by omega
  have hc17 : rest.length + 17 < 1024 := by omega
  have hc18 : rest.length + 18 < 1024 := by omega
  have hc19 : rest.length + 19 < 1024 := by omega
  have hc20 : rest.length + 20 < 1024 := by omega
  have hc21 : rest.length + 21 < 1024 := by omega
  have hc22 : rest.length + 22 < 1024 := by omega
  have hc23 : rest.length + 23 < 1024 := by omega
  have hc24 : rest.length + 24 < 1024 := by omega
  have hc25 : rest.length + 25 < 1024 := by omega
  have hc26 : rest.length + 26 < 1024 := by omega
  have hc27 : rest.length + 27 < 1024 := by omega
  have hc28 : rest.length + 28 < 1024 := by omega
  have hc29 : rest.length + 29 < 1024 := by omega
  have hc30 : rest.length + 30 < 1024 := by omega
  have hc31 : rest.length + 31 < 1024 := by omega
  have hc32 : rest.length + 32 < 1024 := by omega
  have hc33 : rest.length + 33 < 1024 := by omega
  have hc34 : rest.length + 34 < 1024 := by omega
  have hc35 : rest.length + 35 < 1024 := by omega
  have hc36 : rest.length + 36 < 1024 := by omega
  have hc37 : rest.length + 37 < 1024 := by omega
  have hc38 : rest.length + 38 < 1024 := by omega
  have hc39 : rest.length + 39 < 1024 := by omega
  have hc40 : rest.length + 40 < 1024 := by omega
  have hc41 : rest.length + 41 < 1024 := by omega
  have ha928 : (928 : UInt256).toNat = 928 := rfl
  have hf928 := HistoricalSearch.CRTMemoryBounds.activeWords_fix s 928 32 (by decide) (by norm_num) hact
  simp [hz, hzn, retainpart10Program, retainpart10Model, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, Challenge.EvmProof.Word.literal_eq_ofNat, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8, hc9, hc10, hc11, hc12, hc13, hc14, hc15, hc16, hc17, hc18, hc19, hc20, hc21, hc22, hc23, hc24, hc25, hc26, hc27, hc28, hc29, hc30, hc31, hc32, hc33, hc34, hc35, hc36, hc37, hc38, hc39, hc40, hc41, ha928, hf928]

#print axioms retainpart10_run

def retainpart11Program : List Instr :=
  [.op (.Dup ⟨1, by decide⟩),
   .push 1 148,
   .op .SHL,
   .op .OR,
   .op (.Dup ⟨2, by decide⟩),
   .op .AND,
   .push 2 960,
   .op .MSTORE]

def retainpart11Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : UInt256) (rest : List UInt256) : State :=
  let v0 : UInt256 := UInt256.shiftLeft x1 (UInt256.ofNat 148)
  let v1 : UInt256 := UInt256.lor v0 x0
  let v2 : UInt256 := UInt256.land x2 v1
  let v3 : ByteArray := MachineState.writeBytes s.memory (Data.Bytes.natToBytesPadded v2.toNat 32) 960
  {s with pc := UInt256.ofNat 8300, memory := v3, stack := x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: x18 :: x19 :: x20 :: x21 :: x22 :: x23 :: x24 :: x25 :: x26 :: x27 :: x28 :: x29 :: x30 :: x31 :: rest}

theorem retainpart11_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 982) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions retainpart11Program {s with pc := UInt256.ofNat 8289, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: x18 :: x19 :: x20 :: x21 :: x22 :: x23 :: x24 :: x25 :: x26 :: x27 :: x28 :: x29 :: x30 :: x31 :: rest} =
      some (retainpart11Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 rest) := by
  have hz : ({val := 0} : UInt256) = UInt256.ofNat 0 := rfl
  have hzn : ({val := 0} : UInt256).toNat = 0 := rfl
  have hc0 : rest.length + 0 < 1024 := by omega
  have hc1 : rest.length + 1 < 1024 := by omega
  have hc2 : rest.length + 2 < 1024 := by omega
  have hc3 : rest.length + 3 < 1024 := by omega
  have hc4 : rest.length + 4 < 1024 := by omega
  have hc5 : rest.length + 5 < 1024 := by omega
  have hc6 : rest.length + 6 < 1024 := by omega
  have hc7 : rest.length + 7 < 1024 := by omega
  have hc8 : rest.length + 8 < 1024 := by omega
  have hc9 : rest.length + 9 < 1024 := by omega
  have hc10 : rest.length + 10 < 1024 := by omega
  have hc11 : rest.length + 11 < 1024 := by omega
  have hc12 : rest.length + 12 < 1024 := by omega
  have hc13 : rest.length + 13 < 1024 := by omega
  have hc14 : rest.length + 14 < 1024 := by omega
  have hc15 : rest.length + 15 < 1024 := by omega
  have hc16 : rest.length + 16 < 1024 := by omega
  have hc17 : rest.length + 17 < 1024 := by omega
  have hc18 : rest.length + 18 < 1024 := by omega
  have hc19 : rest.length + 19 < 1024 := by omega
  have hc20 : rest.length + 20 < 1024 := by omega
  have hc21 : rest.length + 21 < 1024 := by omega
  have hc22 : rest.length + 22 < 1024 := by omega
  have hc23 : rest.length + 23 < 1024 := by omega
  have hc24 : rest.length + 24 < 1024 := by omega
  have hc25 : rest.length + 25 < 1024 := by omega
  have hc26 : rest.length + 26 < 1024 := by omega
  have hc27 : rest.length + 27 < 1024 := by omega
  have hc28 : rest.length + 28 < 1024 := by omega
  have hc29 : rest.length + 29 < 1024 := by omega
  have hc30 : rest.length + 30 < 1024 := by omega
  have hc31 : rest.length + 31 < 1024 := by omega
  have hc32 : rest.length + 32 < 1024 := by omega
  have hc33 : rest.length + 33 < 1024 := by omega
  have hc34 : rest.length + 34 < 1024 := by omega
  have hc35 : rest.length + 35 < 1024 := by omega
  have hc36 : rest.length + 36 < 1024 := by omega
  have hc37 : rest.length + 37 < 1024 := by omega
  have hc38 : rest.length + 38 < 1024 := by omega
  have hc39 : rest.length + 39 < 1024 := by omega
  have hc40 : rest.length + 40 < 1024 := by omega
  have hc41 : rest.length + 41 < 1024 := by omega
  have ha960 : (960 : UInt256).toNat = 960 := rfl
  have hf960 := HistoricalSearch.CRTMemoryBounds.activeWords_fix s 960 32 (by decide) (by norm_num) hact
  simp [hz, hzn, retainpart11Program, retainpart11Model, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, Challenge.EvmProof.Word.literal_eq_ofNat, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8, hc9, hc10, hc11, hc12, hc13, hc14, hc15, hc16, hc17, hc18, hc19, hc20, hc21, hc22, hc23, hc24, hc25, hc26, hc27, hc28, hc29, hc30, hc31, hc32, hc33, hc34, hc35, hc36, hc37, hc38, hc39, hc40, hc41, ha960, hf960]

#print axioms retainpart11_run

def retainpart12Program : List Instr :=
  [.push 1 96,
   .op .SHR,
   .op (.Dup ⟨2, by decide⟩),
   .push 1 148,
   .op .SHL,
   .op .OR,
   .op .AND]

def retainpart12Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 : UInt256) (rest : List UInt256) : State :=
  let v0 : UInt256 := UInt256.shiftRight x0 (UInt256.ofNat 96)
  let v1 : UInt256 := UInt256.shiftLeft x2 (UInt256.ofNat 148)
  let v2 : UInt256 := UInt256.lor v1 v0
  let v3 : UInt256 := UInt256.land v2 x1
  {s with pc := UInt256.ofNat 8309, memory := s.memory, stack := v3 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: x18 :: x19 :: x20 :: x21 :: x22 :: x23 :: x24 :: x25 :: x26 :: x27 :: x28 :: x29 :: x30 :: rest}

theorem retainpart12_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 982) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions retainpart12Program {s with pc := UInt256.ofNat 8300, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: x18 :: x19 :: x20 :: x21 :: x22 :: x23 :: x24 :: x25 :: x26 :: x27 :: x28 :: x29 :: x30 :: rest} =
      some (retainpart12Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 rest) := by
  have hz : ({val := 0} : UInt256) = UInt256.ofNat 0 := rfl
  have hzn : ({val := 0} : UInt256).toNat = 0 := rfl
  have hc0 : rest.length + 0 < 1024 := by omega
  have hc1 : rest.length + 1 < 1024 := by omega
  have hc2 : rest.length + 2 < 1024 := by omega
  have hc3 : rest.length + 3 < 1024 := by omega
  have hc4 : rest.length + 4 < 1024 := by omega
  have hc5 : rest.length + 5 < 1024 := by omega
  have hc6 : rest.length + 6 < 1024 := by omega
  have hc7 : rest.length + 7 < 1024 := by omega
  have hc8 : rest.length + 8 < 1024 := by omega
  have hc9 : rest.length + 9 < 1024 := by omega
  have hc10 : rest.length + 10 < 1024 := by omega
  have hc11 : rest.length + 11 < 1024 := by omega
  have hc12 : rest.length + 12 < 1024 := by omega
  have hc13 : rest.length + 13 < 1024 := by omega
  have hc14 : rest.length + 14 < 1024 := by omega
  have hc15 : rest.length + 15 < 1024 := by omega
  have hc16 : rest.length + 16 < 1024 := by omega
  have hc17 : rest.length + 17 < 1024 := by omega
  have hc18 : rest.length + 18 < 1024 := by omega
  have hc19 : rest.length + 19 < 1024 := by omega
  have hc20 : rest.length + 20 < 1024 := by omega
  have hc21 : rest.length + 21 < 1024 := by omega
  have hc22 : rest.length + 22 < 1024 := by omega
  have hc23 : rest.length + 23 < 1024 := by omega
  have hc24 : rest.length + 24 < 1024 := by omega
  have hc25 : rest.length + 25 < 1024 := by omega
  have hc26 : rest.length + 26 < 1024 := by omega
  have hc27 : rest.length + 27 < 1024 := by omega
  have hc28 : rest.length + 28 < 1024 := by omega
  have hc29 : rest.length + 29 < 1024 := by omega
  have hc30 : rest.length + 30 < 1024 := by omega
  have hc31 : rest.length + 31 < 1024 := by omega
  have hc32 : rest.length + 32 < 1024 := by omega
  have hc33 : rest.length + 33 < 1024 := by omega
  have hc34 : rest.length + 34 < 1024 := by omega
  have hc35 : rest.length + 35 < 1024 := by omega
  have hc36 : rest.length + 36 < 1024 := by omega
  have hc37 : rest.length + 37 < 1024 := by omega
  have hc38 : rest.length + 38 < 1024 := by omega
  have hc39 : rest.length + 39 < 1024 := by omega
  have hc40 : rest.length + 40 < 1024 := by omega
  have hc41 : rest.length + 41 < 1024 := by omega
  simp [hz, hzn, retainpart12Program, retainpart12Model, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, Challenge.EvmProof.Word.literal_eq_ofNat, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8, hc9, hc10, hc11, hc12, hc13, hc14, hc15, hc16, hc17, hc18, hc19, hc20, hc21, hc22, hc23, hc24, hc25, hc26, hc27, hc28, hc29, hc30, hc31, hc32, hc33, hc34, hc35, hc36, hc37, hc38, hc39, hc40, hc41]

#print axioms retainpart12_run

def retainpart13Program : List Instr :=
  [.push 2 992,
   .op .MSTORE,
   .push 1 96,
   .op .SHR,
   .push 2 1024,
   .op .MSTORE,
   .push 2 5858]

def retainpart13Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 : UInt256) (rest : List UInt256) : State :=
  let v0 : ByteArray := MachineState.writeBytes s.memory (Data.Bytes.natToBytesPadded x0.toNat 32) 992
  let v1 : UInt256 := UInt256.shiftRight x1 (UInt256.ofNat 96)
  let v2 : ByteArray := MachineState.writeBytes v0 (Data.Bytes.natToBytesPadded v1.toNat 32) 1024
  {s with pc := UInt256.ofNat 8323, memory := v2, stack := (UInt256.ofNat 5858) :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: x18 :: x19 :: x20 :: x21 :: x22 :: x23 :: x24 :: x25 :: x26 :: x27 :: x28 :: x29 :: rest}

theorem retainpart13_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 982) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions retainpart13Program {s with pc := UInt256.ofNat 8309, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: x18 :: x19 :: x20 :: x21 :: x22 :: x23 :: x24 :: x25 :: x26 :: x27 :: x28 :: x29 :: rest} =
      some (retainpart13Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 rest) := by
  have hz : ({val := 0} : UInt256) = UInt256.ofNat 0 := rfl
  have hzn : ({val := 0} : UInt256).toNat = 0 := rfl
  have hc0 : rest.length + 0 < 1024 := by omega
  have hc1 : rest.length + 1 < 1024 := by omega
  have hc2 : rest.length + 2 < 1024 := by omega
  have hc3 : rest.length + 3 < 1024 := by omega
  have hc4 : rest.length + 4 < 1024 := by omega
  have hc5 : rest.length + 5 < 1024 := by omega
  have hc6 : rest.length + 6 < 1024 := by omega
  have hc7 : rest.length + 7 < 1024 := by omega
  have hc8 : rest.length + 8 < 1024 := by omega
  have hc9 : rest.length + 9 < 1024 := by omega
  have hc10 : rest.length + 10 < 1024 := by omega
  have hc11 : rest.length + 11 < 1024 := by omega
  have hc12 : rest.length + 12 < 1024 := by omega
  have hc13 : rest.length + 13 < 1024 := by omega
  have hc14 : rest.length + 14 < 1024 := by omega
  have hc15 : rest.length + 15 < 1024 := by omega
  have hc16 : rest.length + 16 < 1024 := by omega
  have hc17 : rest.length + 17 < 1024 := by omega
  have hc18 : rest.length + 18 < 1024 := by omega
  have hc19 : rest.length + 19 < 1024 := by omega
  have hc20 : rest.length + 20 < 1024 := by omega
  have hc21 : rest.length + 21 < 1024 := by omega
  have hc22 : rest.length + 22 < 1024 := by omega
  have hc23 : rest.length + 23 < 1024 := by omega
  have hc24 : rest.length + 24 < 1024 := by omega
  have hc25 : rest.length + 25 < 1024 := by omega
  have hc26 : rest.length + 26 < 1024 := by omega
  have hc27 : rest.length + 27 < 1024 := by omega
  have hc28 : rest.length + 28 < 1024 := by omega
  have hc29 : rest.length + 29 < 1024 := by omega
  have hc30 : rest.length + 30 < 1024 := by omega
  have hc31 : rest.length + 31 < 1024 := by omega
  have hc32 : rest.length + 32 < 1024 := by omega
  have hc33 : rest.length + 33 < 1024 := by omega
  have hc34 : rest.length + 34 < 1024 := by omega
  have hc35 : rest.length + 35 < 1024 := by omega
  have hc36 : rest.length + 36 < 1024 := by omega
  have hc37 : rest.length + 37 < 1024 := by omega
  have hc38 : rest.length + 38 < 1024 := by omega
  have hc39 : rest.length + 39 < 1024 := by omega
  have hc40 : rest.length + 40 < 1024 := by omega
  have hc41 : rest.length + 41 < 1024 := by omega
  have ha992 : (992 : UInt256).toNat = 992 := rfl
  have hf992 := HistoricalSearch.CRTMemoryBounds.activeWords_fix s 992 32 (by decide) (by norm_num) hact
  have ha1024 : (1024 : UInt256).toNat = 1024 := rfl
  have hf1024 := HistoricalSearch.CRTMemoryBounds.activeWords_fix s 1024 32 (by decide) (by norm_num) hact
  simp [hz, hzn, retainpart13Program, retainpart13Model, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, Challenge.EvmProof.Word.literal_eq_ofNat, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8, hc9, hc10, hc11, hc12, hc13, hc14, hc15, hc16, hc17, hc18, hc19, hc20, hc21, hc22, hc23, hc24, hc25, hc26, hc27, hc28, hc29, hc30, hc31, hc32, hc33, hc34, hc35, hc36, hc37, hc38, hc39, hc40, hc41, ha992, hf992, ha1024, hf1024]

#print axioms retainpart13_run

def retainProgram : List Instr :=
  [.push 1 1,
   .push 2 1728,
   .op .MLOAD,
   .op .SUB,
   .push 2 1728,
   .op .MSTORE,
   .push 2 1600,
   .op .MLOAD,
   .op (.Dup ⟨11, by decide⟩),
   .push 2 1568,
   .op .MLOAD,
   .push 2 1536,
   .op .MLOAD,
   .push 2 1504,
   .op .MLOAD,
   .push 2 1472,
   .op .MLOAD,
   .push 2 1440,
   .op .MLOAD,
   .push 2 1408,
   .op .MLOAD,
   .push 2 1376,
   .op .MLOAD,
   .push 2 1344,
   .op .MLOAD,
   .push 1 96,
   .op .SHR,
   .op (.Dup ⟨1, by decide⟩),
   .push 1 148,
   .op .SHL,
   .op .OR,
   .op (.Dup ⟨8, by decide⟩),
   .op .AND,
   .push 2 768,
   .op .MSTORE,
   .push 1 96,
   .op .SHR,
   .op (.Dup ⟨1, by decide⟩),
   .push 1 148,
   .op .SHL,
   .op .OR,
   .op (.Dup ⟨7, by decide⟩),
   .op .AND,
   .push 2 800,
   .op .MSTORE,
   .push 1 96,
   .op .SHR,
   .op (.Dup ⟨1, by decide⟩),
   .push 1 148,
   .op .SHL,
   .op .OR,
   .op (.Dup ⟨6, by decide⟩),
   .op .AND,
   .push 2 832,
   .op .MSTORE,
   .push 1 96,
   .op .SHR,
   .op (.Dup ⟨1, by decide⟩),
   .push 1 148,
   .op .SHL,
   .op .OR,
   .op (.Dup ⟨5, by decide⟩),
   .op .AND,
   .push 2 864,
   .op .MSTORE,
   .push 1 96,
   .op .SHR,
   .op (.Dup ⟨1, by decide⟩),
   .push 1 148,
   .op .SHL,
   .op .OR,
   .op (.Dup ⟨4, by decide⟩),
   .op .AND,
   .push 2 896,
   .op .MSTORE,
   .push 1 96,
   .op .SHR,
   .op (.Dup ⟨1, by decide⟩),
   .push 1 148,
   .op .SHL,
   .op .OR,
   .op (.Dup ⟨3, by decide⟩),
   .op .AND,
   .push 2 928,
   .op .MSTORE,
   .push 1 96,
   .op .SHR,
   .op (.Dup ⟨1, by decide⟩),
   .push 1 148,
   .op .SHL,
   .op .OR,
   .op (.Dup ⟨2, by decide⟩),
   .op .AND,
   .push 2 960,
   .op .MSTORE,
   .push 1 96,
   .op .SHR,
   .op (.Dup ⟨2, by decide⟩),
   .push 1 148,
   .op .SHL,
   .op .OR,
   .op .AND,
   .push 2 992,
   .op .MSTORE,
   .push 1 96,
   .op .SHR,
   .push 2 1024,
   .op .MSTORE,
   .push 2 5858]

def retainModel (s : State) (P n0 n1 n2 n3 n4 n5 n6 n7 n8 mask minv pbi hd w3 ent m32 allones m128 m64 m0 tl m96 inv tn aprev counter ret : UInt256) (rest : List UInt256) : State :=
  let v0 : UInt256 := MachineState.readWord s.memory 1728
  let v1 : UInt256 := v0 - (UInt256.ofNat 1)
  let v2 : ByteArray := MachineState.writeBytes s.memory (Data.Bytes.natToBytesPadded v1.toNat 32) 1728
  let v3 : UInt256 := MachineState.readWord v2 1600
  let v4 : UInt256 := MachineState.readWord v2 1568
  let v5 : UInt256 := MachineState.readWord v2 1536
  let v6 : UInt256 := MachineState.readWord v2 1504
  let v7 : UInt256 := MachineState.readWord v2 1472
  let v8 : UInt256 := MachineState.readWord v2 1440
  let v9 : UInt256 := MachineState.readWord v2 1408
  let v10 : UInt256 := MachineState.readWord v2 1376
  let v11 : UInt256 := MachineState.readWord v2 1344
  let v12 : UInt256 := UInt256.shiftRight v11 (UInt256.ofNat 96)
  let v13 : UInt256 := UInt256.shiftLeft v10 (UInt256.ofNat 148)
  let v14 : UInt256 := UInt256.lor v13 v12
  let v15 : UInt256 := UInt256.land mask v14
  let v16 : ByteArray := MachineState.writeBytes v2 (Data.Bytes.natToBytesPadded v15.toNat 32) 768
  let v17 : UInt256 := UInt256.shiftRight v10 (UInt256.ofNat 96)
  let v18 : UInt256 := UInt256.shiftLeft v9 (UInt256.ofNat 148)
  let v19 : UInt256 := UInt256.lor v18 v17
  let v20 : UInt256 := UInt256.land mask v19
  let v21 : ByteArray := MachineState.writeBytes v16 (Data.Bytes.natToBytesPadded v20.toNat 32) 800
  let v22 : UInt256 := UInt256.shiftRight v9 (UInt256.ofNat 96)
  let v23 : UInt256 := UInt256.shiftLeft v8 (UInt256.ofNat 148)
  let v24 : UInt256 := UInt256.lor v23 v22
  let v25 : UInt256 := UInt256.land mask v24
  let v26 : ByteArray := MachineState.writeBytes v21 (Data.Bytes.natToBytesPadded v25.toNat 32) 832
  let v27 : UInt256 := UInt256.shiftRight v8 (UInt256.ofNat 96)
  let v28 : UInt256 := UInt256.shiftLeft v7 (UInt256.ofNat 148)
  let v29 : UInt256 := UInt256.lor v28 v27
  let v30 : UInt256 := UInt256.land mask v29
  let v31 : ByteArray := MachineState.writeBytes v26 (Data.Bytes.natToBytesPadded v30.toNat 32) 864
  let v32 : UInt256 := UInt256.shiftRight v7 (UInt256.ofNat 96)
  let v33 : UInt256 := UInt256.shiftLeft v6 (UInt256.ofNat 148)
  let v34 : UInt256 := UInt256.lor v33 v32
  let v35 : UInt256 := UInt256.land mask v34
  let v36 : ByteArray := MachineState.writeBytes v31 (Data.Bytes.natToBytesPadded v35.toNat 32) 896
  let v37 : UInt256 := UInt256.shiftRight v6 (UInt256.ofNat 96)
  let v38 : UInt256 := UInt256.shiftLeft v5 (UInt256.ofNat 148)
  let v39 : UInt256 := UInt256.lor v38 v37
  let v40 : UInt256 := UInt256.land mask v39
  let v41 : ByteArray := MachineState.writeBytes v36 (Data.Bytes.natToBytesPadded v40.toNat 32) 928
  let v42 : UInt256 := UInt256.shiftRight v5 (UInt256.ofNat 96)
  let v43 : UInt256 := UInt256.shiftLeft v4 (UInt256.ofNat 148)
  let v44 : UInt256 := UInt256.lor v43 v42
  let v45 : UInt256 := UInt256.land mask v44
  let v46 : ByteArray := MachineState.writeBytes v41 (Data.Bytes.natToBytesPadded v45.toNat 32) 960
  let v47 : UInt256 := UInt256.shiftRight v4 (UInt256.ofNat 96)
  let v48 : UInt256 := UInt256.shiftLeft v3 (UInt256.ofNat 148)
  let v49 : UInt256 := UInt256.lor v48 v47
  let v50 : UInt256 := UInt256.land v49 mask
  let v51 : ByteArray := MachineState.writeBytes v46 (Data.Bytes.natToBytesPadded v50.toNat 32) 992
  let v52 : UInt256 := UInt256.shiftRight v3 (UInt256.ofNat 96)
  let v53 : ByteArray := MachineState.writeBytes v51 (Data.Bytes.natToBytesPadded v52.toNat 32) 1024
  {s with pc := UInt256.ofNat 8323, memory := v53, stack := (UInt256.ofNat 5858) :: P :: n0 :: n1 :: n2 :: n3 :: n4 :: n5 :: n6 :: n7 :: n8 :: mask :: minv :: pbi :: hd :: w3 :: ent :: m32 :: allones :: m128 :: m64 :: m0 :: tl :: m96 :: inv :: tn :: aprev :: counter :: ret :: rest}

theorem retain_run (s : State) (P n0 n1 n2 n3 n4 n5 n6 n7 n8 mask minv pbi hd w3 ent m32 allones m128 m64 m0 tl m96 inv tn aprev counter ret : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 982) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions retainProgram {s with pc := UInt256.ofNat 8154, stack := P :: n0 :: n1 :: n2 :: n3 :: n4 :: n5 :: n6 :: n7 :: n8 :: mask :: minv :: pbi :: hd :: w3 :: ent :: m32 :: allones :: m128 :: m64 :: m0 :: tl :: m96 :: inv :: tn :: aprev :: counter :: ret :: rest} =
      some (retainModel s P n0 n1 n2 n3 n4 n5 n6 n7 n8 mask minv pbi hd w3 ent m32 allones m128 m64 m0 tl m96 inv tn aprev counter ret rest) := by
  let v0 : UInt256 := MachineState.readWord s.memory 1728
  let v1 : UInt256 := v0 - (UInt256.ofNat 1)
  let v2 : ByteArray := MachineState.writeBytes s.memory (Data.Bytes.natToBytesPadded v1.toNat 32) 1728
  let v3 : UInt256 := MachineState.readWord v2 1600
  let v4 : UInt256 := MachineState.readWord v2 1568
  let v5 : UInt256 := MachineState.readWord v2 1536
  let v6 : UInt256 := MachineState.readWord v2 1504
  let v7 : UInt256 := MachineState.readWord v2 1472
  let v8 : UInt256 := MachineState.readWord v2 1440
  let v9 : UInt256 := MachineState.readWord v2 1408
  let v10 : UInt256 := MachineState.readWord v2 1376
  let v11 : UInt256 := MachineState.readWord v2 1344
  let v12 : UInt256 := UInt256.shiftRight v11 (UInt256.ofNat 96)
  let v13 : UInt256 := UInt256.shiftLeft v10 (UInt256.ofNat 148)
  let v14 : UInt256 := UInt256.lor v13 v12
  let v15 : UInt256 := UInt256.land mask v14
  let v16 : ByteArray := MachineState.writeBytes v2 (Data.Bytes.natToBytesPadded v15.toNat 32) 768
  let v17 : UInt256 := UInt256.shiftRight v10 (UInt256.ofNat 96)
  let v18 : UInt256 := UInt256.shiftLeft v9 (UInt256.ofNat 148)
  let v19 : UInt256 := UInt256.lor v18 v17
  let v20 : UInt256 := UInt256.land mask v19
  let v21 : ByteArray := MachineState.writeBytes v16 (Data.Bytes.natToBytesPadded v20.toNat 32) 800
  let v22 : UInt256 := UInt256.shiftRight v9 (UInt256.ofNat 96)
  let v23 : UInt256 := UInt256.shiftLeft v8 (UInt256.ofNat 148)
  let v24 : UInt256 := UInt256.lor v23 v22
  let v25 : UInt256 := UInt256.land mask v24
  let v26 : ByteArray := MachineState.writeBytes v21 (Data.Bytes.natToBytesPadded v25.toNat 32) 832
  let v27 : UInt256 := UInt256.shiftRight v8 (UInt256.ofNat 96)
  let v28 : UInt256 := UInt256.shiftLeft v7 (UInt256.ofNat 148)
  let v29 : UInt256 := UInt256.lor v28 v27
  let v30 : UInt256 := UInt256.land mask v29
  let v31 : ByteArray := MachineState.writeBytes v26 (Data.Bytes.natToBytesPadded v30.toNat 32) 864
  let v32 : UInt256 := UInt256.shiftRight v7 (UInt256.ofNat 96)
  let v33 : UInt256 := UInt256.shiftLeft v6 (UInt256.ofNat 148)
  let v34 : UInt256 := UInt256.lor v33 v32
  let v35 : UInt256 := UInt256.land mask v34
  let v36 : ByteArray := MachineState.writeBytes v31 (Data.Bytes.natToBytesPadded v35.toNat 32) 896
  let v37 : UInt256 := UInt256.shiftRight v6 (UInt256.ofNat 96)
  let v38 : UInt256 := UInt256.shiftLeft v5 (UInt256.ofNat 148)
  let v39 : UInt256 := UInt256.lor v38 v37
  let v40 : UInt256 := UInt256.land mask v39
  let v41 : ByteArray := MachineState.writeBytes v36 (Data.Bytes.natToBytesPadded v40.toNat 32) 928
  let v42 : UInt256 := UInt256.shiftRight v5 (UInt256.ofNat 96)
  let v43 : UInt256 := UInt256.shiftLeft v4 (UInt256.ofNat 148)
  let v44 : UInt256 := UInt256.lor v43 v42
  let v45 : UInt256 := UInt256.land mask v44
  let v46 : ByteArray := MachineState.writeBytes v41 (Data.Bytes.natToBytesPadded v45.toNat 32) 960
  let v47 : UInt256 := UInt256.shiftRight v4 (UInt256.ofNat 96)
  let v48 : UInt256 := UInt256.shiftLeft v3 (UInt256.ofNat 148)
  let v49 : UInt256 := UInt256.lor v48 v47
  let v50 : UInt256 := UInt256.land v49 mask
  let v51 : ByteArray := MachineState.writeBytes v46 (Data.Bytes.natToBytesPadded v50.toNat 32) 992
  let v52 : UInt256 := UInt256.shiftRight v3 (UInt256.ofNat 96)
  let v53 : ByteArray := MachineState.writeBytes v51 (Data.Bytes.natToBytesPadded v52.toNat 32) 1024
  have h0 : runInstructions retainpart0Program {s with pc := UInt256.ofNat 8154, memory := s.memory, stack := P :: n0 :: n1 :: n2 :: n3 :: n4 :: n5 :: n6 :: n7 :: n8 :: mask :: minv :: pbi :: hd :: w3 :: ent :: m32 :: allones :: m128 :: m64 :: m0 :: tl :: m96 :: inv :: tn :: aprev :: counter :: ret :: rest} = some {s with pc := UInt256.ofNat 8169, memory := v2, stack := v3 :: P :: n0 :: n1 :: n2 :: n3 :: n4 :: n5 :: n6 :: n7 :: n8 :: mask :: minv :: pbi :: hd :: w3 :: ent :: m32 :: allones :: m128 :: m64 :: m0 :: tl :: m96 :: inv :: tn :: aprev :: counter :: ret :: rest} := by
    simpa only [retainpart0Model, v0, v1, v2, v3] using retainpart0_run (s) (P) (n0) (n1) (n2) (n3) (n4) (n5) (n6) (n7) (n8) (mask) (minv) (pbi) (hd) (w3) (ent) (m32) (allones) (m128) (m64) (m0) (tl) (m96) (inv) (tn) (aprev) (counter) (ret) rest hcap hact
  have h1 : runInstructions retainpart1Program {s with pc := UInt256.ofNat 8169, memory := v2, stack := v3 :: P :: n0 :: n1 :: n2 :: n3 :: n4 :: n5 :: n6 :: n7 :: n8 :: mask :: minv :: pbi :: hd :: w3 :: ent :: m32 :: allones :: m128 :: m64 :: m0 :: tl :: m96 :: inv :: tn :: aprev :: counter :: ret :: rest} = some {s with pc := UInt256.ofNat 8182, memory := v2, stack := v6 :: v5 :: v4 :: mask :: v3 :: P :: n0 :: n1 :: n2 :: n3 :: n4 :: n5 :: n6 :: n7 :: n8 :: mask :: minv :: pbi :: hd :: w3 :: ent :: m32 :: allones :: m128 :: m64 :: m0 :: tl :: m96 :: inv :: tn :: aprev :: counter :: ret :: rest} := by
    simpa only [retainpart1Model, v4, v5, v6] using retainpart1_run ({s with memory := v2}) (v3) (P) (n0) (n1) (n2) (n3) (n4) (n5) (n6) (n7) (n8) (mask) (minv) (pbi) (hd) (w3) (ent) (m32) (allones) (m128) (m64) (m0) (tl) (m96) (inv) (tn) (aprev) (counter) (ret) rest hcap hact
  have h2 : runInstructions retainpart2Program {s with pc := UInt256.ofNat 8182, memory := v2, stack := v6 :: v5 :: v4 :: mask :: v3 :: P :: n0 :: n1 :: n2 :: n3 :: n4 :: n5 :: n6 :: n7 :: n8 :: mask :: minv :: pbi :: hd :: w3 :: ent :: m32 :: allones :: m128 :: m64 :: m0 :: tl :: m96 :: inv :: tn :: aprev :: counter :: ret :: rest} = some {s with pc := UInt256.ofNat 8198, memory := v2, stack := v10 :: v9 :: v8 :: v7 :: v6 :: v5 :: v4 :: mask :: v3 :: P :: n0 :: n1 :: n2 :: n3 :: n4 :: n5 :: n6 :: n7 :: n8 :: mask :: minv :: pbi :: hd :: w3 :: ent :: m32 :: allones :: m128 :: m64 :: m0 :: tl :: m96 :: inv :: tn :: aprev :: counter :: ret :: rest} := by
    simpa only [retainpart2Model, v7, v8, v9, v10] using retainpart2_run ({s with memory := v2}) (v6) (v5) (v4) (mask) (v3) (P) (n0) (n1) (n2) (n3) (n4) (n5) (n6) (n7) (n8) (mask) (minv) (pbi) (hd) (w3) (ent) (m32) (allones) (m128) (m64) (m0) (tl) (m96) (inv) (tn) (aprev) (counter) (ret) rest hcap hact
  have h3 : runInstructions retainpart3Program {s with pc := UInt256.ofNat 8198, memory := v2, stack := v10 :: v9 :: v8 :: v7 :: v6 :: v5 :: v4 :: mask :: v3 :: P :: n0 :: n1 :: n2 :: n3 :: n4 :: n5 :: n6 :: n7 :: n8 :: mask :: minv :: pbi :: hd :: w3 :: ent :: m32 :: allones :: m128 :: m64 :: m0 :: tl :: m96 :: inv :: tn :: aprev :: counter :: ret :: rest} = some {s with pc := UInt256.ofNat 8210, memory := v2, stack := v14 :: v10 :: v9 :: v8 :: v7 :: v6 :: v5 :: v4 :: mask :: v3 :: P :: n0 :: n1 :: n2 :: n3 :: n4 :: n5 :: n6 :: n7 :: n8 :: mask :: minv :: pbi :: hd :: w3 :: ent :: m32 :: allones :: m128 :: m64 :: m0 :: tl :: m96 :: inv :: tn :: aprev :: counter :: ret :: rest} := by
    simpa only [retainpart3Model, v11, v12, v13, v14] using retainpart3_run ({s with memory := v2}) (v10) (v9) (v8) (v7) (v6) (v5) (v4) (mask) (v3) (P) (n0) (n1) (n2) (n3) (n4) (n5) (n6) (n7) (n8) (mask) (minv) (pbi) (hd) (w3) (ent) (m32) (allones) (m128) (m64) (m0) (tl) (m96) (inv) (tn) (aprev) (counter) (ret) rest hcap hact
  have h4 : runInstructions retainpart4Program {s with pc := UInt256.ofNat 8210, memory := v2, stack := v14 :: v10 :: v9 :: v8 :: v7 :: v6 :: v5 :: v4 :: mask :: v3 :: P :: n0 :: n1 :: n2 :: n3 :: n4 :: n5 :: n6 :: n7 :: n8 :: mask :: minv :: pbi :: hd :: w3 :: ent :: m32 :: allones :: m128 :: m64 :: m0 :: tl :: m96 :: inv :: tn :: aprev :: counter :: ret :: rest} = some {s with pc := UInt256.ofNat 8222, memory := v16, stack := (UInt256.ofNat 148) :: v9 :: v17 :: v9 :: v8 :: v7 :: v6 :: v5 :: v4 :: mask :: v3 :: P :: n0 :: n1 :: n2 :: n3 :: n4 :: n5 :: n6 :: n7 :: n8 :: mask :: minv :: pbi :: hd :: w3 :: ent :: m32 :: allones :: m128 :: m64 :: m0 :: tl :: m96 :: inv :: tn :: aprev :: counter :: ret :: rest} := by
    simpa only [retainpart4Model, v15, v16, v17] using retainpart4_run ({s with memory := v2}) (v14) (v10) (v9) (v8) (v7) (v6) (v5) (v4) (mask) (v3) (P) (n0) (n1) (n2) (n3) (n4) (n5) (n6) (n7) (n8) (mask) (minv) (pbi) (hd) (w3) (ent) (m32) (allones) (m128) (m64) (m0) (tl) (m96) (inv) (tn) (aprev) (counter) (ret) rest hcap hact
  have h5 : runInstructions retainpart5Program {s with pc := UInt256.ofNat 8222, memory := v16, stack := (UInt256.ofNat 148) :: v9 :: v17 :: v9 :: v8 :: v7 :: v6 :: v5 :: v4 :: mask :: v3 :: P :: n0 :: n1 :: n2 :: n3 :: n4 :: n5 :: n6 :: n7 :: n8 :: mask :: minv :: pbi :: hd :: w3 :: ent :: m32 :: allones :: m128 :: m64 :: m0 :: tl :: m96 :: inv :: tn :: aprev :: counter :: ret :: rest} = some {s with pc := UInt256.ofNat 8233, memory := v21, stack := v22 :: v8 :: v7 :: v6 :: v5 :: v4 :: mask :: v3 :: P :: n0 :: n1 :: n2 :: n3 :: n4 :: n5 :: n6 :: n7 :: n8 :: mask :: minv :: pbi :: hd :: w3 :: ent :: m32 :: allones :: m128 :: m64 :: m0 :: tl :: m96 :: inv :: tn :: aprev :: counter :: ret :: rest} := by
    simpa only [retainpart5Model, v18, v19, v20, v21, v22] using retainpart5_run ({s with memory := v16}) ((UInt256.ofNat 148)) (v9) (v17) (v9) (v8) (v7) (v6) (v5) (v4) (mask) (v3) (P) (n0) (n1) (n2) (n3) (n4) (n5) (n6) (n7) (n8) (mask) (minv) (pbi) (hd) (w3) (ent) (m32) (allones) (m128) (m64) (m0) (tl) (m96) (inv) (tn) (aprev) (counter) (ret) rest hcap hact
  have h6 : runInstructions retainpart6Program {s with pc := UInt256.ofNat 8233, memory := v21, stack := v22 :: v8 :: v7 :: v6 :: v5 :: v4 :: mask :: v3 :: P :: n0 :: n1 :: n2 :: n3 :: n4 :: n5 :: n6 :: n7 :: n8 :: mask :: minv :: pbi :: hd :: w3 :: ent :: m32 :: allones :: m128 :: m64 :: m0 :: tl :: m96 :: inv :: tn :: aprev :: counter :: ret :: rest} = some {s with pc := UInt256.ofNat 8244, memory := v26, stack := v8 :: v7 :: v6 :: v5 :: v4 :: mask :: v3 :: P :: n0 :: n1 :: n2 :: n3 :: n4 :: n5 :: n6 :: n7 :: n8 :: mask :: minv :: pbi :: hd :: w3 :: ent :: m32 :: allones :: m128 :: m64 :: m0 :: tl :: m96 :: inv :: tn :: aprev :: counter :: ret :: rest} := by
    simpa only [retainpart6Model, v23, v24, v25, v26] using retainpart6_run ({s with memory := v21}) (v22) (v8) (v7) (v6) (v5) (v4) (mask) (v3) (P) (n0) (n1) (n2) (n3) (n4) (n5) (n6) (n7) (n8) (mask) (minv) (pbi) (hd) (w3) (ent) (m32) (allones) (m128) (m64) (m0) (tl) (m96) (inv) (tn) (aprev) (counter) (ret) rest hcap hact
  have h7 : runInstructions retainpart7Program {s with pc := UInt256.ofNat 8244, memory := v26, stack := v8 :: v7 :: v6 :: v5 :: v4 :: mask :: v3 :: P :: n0 :: n1 :: n2 :: n3 :: n4 :: n5 :: n6 :: n7 :: n8 :: mask :: minv :: pbi :: hd :: w3 :: ent :: m32 :: allones :: m128 :: m64 :: m0 :: tl :: m96 :: inv :: tn :: aprev :: counter :: ret :: rest} = some {s with pc := UInt256.ofNat 8254, memory := v26, stack := v30 :: v7 :: v6 :: v5 :: v4 :: mask :: v3 :: P :: n0 :: n1 :: n2 :: n3 :: n4 :: n5 :: n6 :: n7 :: n8 :: mask :: minv :: pbi :: hd :: w3 :: ent :: m32 :: allones :: m128 :: m64 :: m0 :: tl :: m96 :: inv :: tn :: aprev :: counter :: ret :: rest} := by
    simpa only [retainpart7Model, v27, v28, v29, v30] using retainpart7_run ({s with memory := v26}) (v8) (v7) (v6) (v5) (v4) (mask) (v3) (P) (n0) (n1) (n2) (n3) (n4) (n5) (n6) (n7) (n8) (mask) (minv) (pbi) (hd) (w3) (ent) (m32) (allones) (m128) (m64) (m0) (tl) (m96) (inv) (tn) (aprev) (counter) (ret) rest hcap hact
  have h8 : runInstructions retainpart8Program {s with pc := UInt256.ofNat 8254, memory := v26, stack := v30 :: v7 :: v6 :: v5 :: v4 :: mask :: v3 :: P :: n0 :: n1 :: n2 :: n3 :: n4 :: n5 :: n6 :: n7 :: n8 :: mask :: minv :: pbi :: hd :: w3 :: ent :: m32 :: allones :: m128 :: m64 :: m0 :: tl :: m96 :: inv :: tn :: aprev :: counter :: ret :: rest} = some {s with pc := UInt256.ofNat 8266, memory := v31, stack := v34 :: v6 :: v5 :: v4 :: mask :: v3 :: P :: n0 :: n1 :: n2 :: n3 :: n4 :: n5 :: n6 :: n7 :: n8 :: mask :: minv :: pbi :: hd :: w3 :: ent :: m32 :: allones :: m128 :: m64 :: m0 :: tl :: m96 :: inv :: tn :: aprev :: counter :: ret :: rest} := by
    simpa only [retainpart8Model, v31, v32, v33, v34] using retainpart8_run ({s with memory := v26}) (v30) (v7) (v6) (v5) (v4) (mask) (v3) (P) (n0) (n1) (n2) (n3) (n4) (n5) (n6) (n7) (n8) (mask) (minv) (pbi) (hd) (w3) (ent) (m32) (allones) (m128) (m64) (m0) (tl) (m96) (inv) (tn) (aprev) (counter) (ret) rest hcap hact
  have h9 : runInstructions retainpart9Program {s with pc := UInt256.ofNat 8266, memory := v31, stack := v34 :: v6 :: v5 :: v4 :: mask :: v3 :: P :: n0 :: n1 :: n2 :: n3 :: n4 :: n5 :: n6 :: n7 :: n8 :: mask :: minv :: pbi :: hd :: w3 :: ent :: m32 :: allones :: m128 :: m64 :: m0 :: tl :: m96 :: inv :: tn :: aprev :: counter :: ret :: rest} = some {s with pc := UInt256.ofNat 8278, memory := v36, stack := (UInt256.ofNat 148) :: v5 :: v37 :: v5 :: v4 :: mask :: v3 :: P :: n0 :: n1 :: n2 :: n3 :: n4 :: n5 :: n6 :: n7 :: n8 :: mask :: minv :: pbi :: hd :: w3 :: ent :: m32 :: allones :: m128 :: m64 :: m0 :: tl :: m96 :: inv :: tn :: aprev :: counter :: ret :: rest} := by
    simpa only [retainpart9Model, v35, v36, v37] using retainpart9_run ({s with memory := v31}) (v34) (v6) (v5) (v4) (mask) (v3) (P) (n0) (n1) (n2) (n3) (n4) (n5) (n6) (n7) (n8) (mask) (minv) (pbi) (hd) (w3) (ent) (m32) (allones) (m128) (m64) (m0) (tl) (m96) (inv) (tn) (aprev) (counter) (ret) rest hcap hact
  have h10 : runInstructions retainpart10Program {s with pc := UInt256.ofNat 8278, memory := v36, stack := (UInt256.ofNat 148) :: v5 :: v37 :: v5 :: v4 :: mask :: v3 :: P :: n0 :: n1 :: n2 :: n3 :: n4 :: n5 :: n6 :: n7 :: n8 :: mask :: minv :: pbi :: hd :: w3 :: ent :: m32 :: allones :: m128 :: m64 :: m0 :: tl :: m96 :: inv :: tn :: aprev :: counter :: ret :: rest} = some {s with pc := UInt256.ofNat 8289, memory := v41, stack := v42 :: v4 :: mask :: v3 :: P :: n0 :: n1 :: n2 :: n3 :: n4 :: n5 :: n6 :: n7 :: n8 :: mask :: minv :: pbi :: hd :: w3 :: ent :: m32 :: allones :: m128 :: m64 :: m0 :: tl :: m96 :: inv :: tn :: aprev :: counter :: ret :: rest} := by
    simpa only [retainpart10Model, v38, v39, v40, v41, v42] using retainpart10_run ({s with memory := v36}) ((UInt256.ofNat 148)) (v5) (v37) (v5) (v4) (mask) (v3) (P) (n0) (n1) (n2) (n3) (n4) (n5) (n6) (n7) (n8) (mask) (minv) (pbi) (hd) (w3) (ent) (m32) (allones) (m128) (m64) (m0) (tl) (m96) (inv) (tn) (aprev) (counter) (ret) rest hcap hact
  have h11 : runInstructions retainpart11Program {s with pc := UInt256.ofNat 8289, memory := v41, stack := v42 :: v4 :: mask :: v3 :: P :: n0 :: n1 :: n2 :: n3 :: n4 :: n5 :: n6 :: n7 :: n8 :: mask :: minv :: pbi :: hd :: w3 :: ent :: m32 :: allones :: m128 :: m64 :: m0 :: tl :: m96 :: inv :: tn :: aprev :: counter :: ret :: rest} = some {s with pc := UInt256.ofNat 8300, memory := v46, stack := v4 :: mask :: v3 :: P :: n0 :: n1 :: n2 :: n3 :: n4 :: n5 :: n6 :: n7 :: n8 :: mask :: minv :: pbi :: hd :: w3 :: ent :: m32 :: allones :: m128 :: m64 :: m0 :: tl :: m96 :: inv :: tn :: aprev :: counter :: ret :: rest} := by
    simpa only [retainpart11Model, v43, v44, v45, v46] using retainpart11_run ({s with memory := v41}) (v42) (v4) (mask) (v3) (P) (n0) (n1) (n2) (n3) (n4) (n5) (n6) (n7) (n8) (mask) (minv) (pbi) (hd) (w3) (ent) (m32) (allones) (m128) (m64) (m0) (tl) (m96) (inv) (tn) (aprev) (counter) (ret) rest hcap hact
  have h12 : runInstructions retainpart12Program {s with pc := UInt256.ofNat 8300, memory := v46, stack := v4 :: mask :: v3 :: P :: n0 :: n1 :: n2 :: n3 :: n4 :: n5 :: n6 :: n7 :: n8 :: mask :: minv :: pbi :: hd :: w3 :: ent :: m32 :: allones :: m128 :: m64 :: m0 :: tl :: m96 :: inv :: tn :: aprev :: counter :: ret :: rest} = some {s with pc := UInt256.ofNat 8309, memory := v46, stack := v50 :: v3 :: P :: n0 :: n1 :: n2 :: n3 :: n4 :: n5 :: n6 :: n7 :: n8 :: mask :: minv :: pbi :: hd :: w3 :: ent :: m32 :: allones :: m128 :: m64 :: m0 :: tl :: m96 :: inv :: tn :: aprev :: counter :: ret :: rest} := by
    simpa only [retainpart12Model, v47, v48, v49, v50] using retainpart12_run ({s with memory := v46}) (v4) (mask) (v3) (P) (n0) (n1) (n2) (n3) (n4) (n5) (n6) (n7) (n8) (mask) (minv) (pbi) (hd) (w3) (ent) (m32) (allones) (m128) (m64) (m0) (tl) (m96) (inv) (tn) (aprev) (counter) (ret) rest hcap hact
  have h13 : runInstructions retainpart13Program {s with pc := UInt256.ofNat 8309, memory := v46, stack := v50 :: v3 :: P :: n0 :: n1 :: n2 :: n3 :: n4 :: n5 :: n6 :: n7 :: n8 :: mask :: minv :: pbi :: hd :: w3 :: ent :: m32 :: allones :: m128 :: m64 :: m0 :: tl :: m96 :: inv :: tn :: aprev :: counter :: ret :: rest} = some {s with pc := UInt256.ofNat 8323, memory := v53, stack := (UInt256.ofNat 5858) :: P :: n0 :: n1 :: n2 :: n3 :: n4 :: n5 :: n6 :: n7 :: n8 :: mask :: minv :: pbi :: hd :: w3 :: ent :: m32 :: allones :: m128 :: m64 :: m0 :: tl :: m96 :: inv :: tn :: aprev :: counter :: ret :: rest} := by
    simpa only [retainpart13Model, v51, v52, v53] using retainpart13_run ({s with memory := v46}) (v50) (v3) (P) (n0) (n1) (n2) (n3) (n4) (n5) (n6) (n7) (n8) (mask) (minv) (pbi) (hd) (w3) (ent) (m32) (allones) (m128) (m64) (m0) (tl) (m96) (inv) (tn) (aprev) (counter) (ret) rest hcap hact
  exact (runInstructions_append_some _ _ _ _ _ h0 (runInstructions_append_some _ _ _ _ _ h1 (runInstructions_append_some _ _ _ _ _ h2 (runInstructions_append_some _ _ _ _ _ h3 (runInstructions_append_some _ _ _ _ _ h4 (runInstructions_append_some _ _ _ _ _ h5 (runInstructions_append_some _ _ _ _ _ h6 (runInstructions_append_some _ _ _ _ _ h7 (runInstructions_append_some _ _ _ _ _ h8 (runInstructions_append_some _ _ _ _ _ h9 (runInstructions_append_some _ _ _ _ _ h10 (runInstructions_append_some _ _ _ _ _ h11 (runInstructions_append_some _ _ _ _ _ h12 h13)))))))))))))

#print axioms retain_run

def exitpart0Program : List Instr :=
  [.op .JUMPDEST,
   .op .POP,
   .op .POP,
   .op .POP,
   .op .POP,
   .op .POP,
   .op .POP,
   .op .POP]

def exitpart0Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 : UInt256) (rest : List UInt256) : State :=
  {s with pc := UInt256.ofNat 8808, memory := s.memory, stack := x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: x18 :: x19 :: x20 :: x21 :: x22 :: x23 :: x24 :: x25 :: x26 :: x27 :: rest}

theorem exitpart0_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 982) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions exitpart0Program {s with pc := UInt256.ofNat 8800, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: x18 :: x19 :: x20 :: x21 :: x22 :: x23 :: x24 :: x25 :: x26 :: x27 :: rest} =
      some (exitpart0Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 rest) := by
  have hz : ({val := 0} : UInt256) = UInt256.ofNat 0 := rfl
  have hzn : ({val := 0} : UInt256).toNat = 0 := rfl
  have hc0 : rest.length + 0 < 1024 := by omega
  have hc1 : rest.length + 1 < 1024 := by omega
  have hc2 : rest.length + 2 < 1024 := by omega
  have hc3 : rest.length + 3 < 1024 := by omega
  have hc4 : rest.length + 4 < 1024 := by omega
  have hc5 : rest.length + 5 < 1024 := by omega
  have hc6 : rest.length + 6 < 1024 := by omega
  have hc7 : rest.length + 7 < 1024 := by omega
  have hc8 : rest.length + 8 < 1024 := by omega
  have hc9 : rest.length + 9 < 1024 := by omega
  have hc10 : rest.length + 10 < 1024 := by omega
  have hc11 : rest.length + 11 < 1024 := by omega
  have hc12 : rest.length + 12 < 1024 := by omega
  have hc13 : rest.length + 13 < 1024 := by omega
  have hc14 : rest.length + 14 < 1024 := by omega
  have hc15 : rest.length + 15 < 1024 := by omega
  have hc16 : rest.length + 16 < 1024 := by omega
  have hc17 : rest.length + 17 < 1024 := by omega
  have hc18 : rest.length + 18 < 1024 := by omega
  have hc19 : rest.length + 19 < 1024 := by omega
  have hc20 : rest.length + 20 < 1024 := by omega
  have hc21 : rest.length + 21 < 1024 := by omega
  have hc22 : rest.length + 22 < 1024 := by omega
  have hc23 : rest.length + 23 < 1024 := by omega
  have hc24 : rest.length + 24 < 1024 := by omega
  have hc25 : rest.length + 25 < 1024 := by omega
  have hc26 : rest.length + 26 < 1024 := by omega
  have hc27 : rest.length + 27 < 1024 := by omega
  have hc28 : rest.length + 28 < 1024 := by omega
  have hc29 : rest.length + 29 < 1024 := by omega
  have hc30 : rest.length + 30 < 1024 := by omega
  have hc31 : rest.length + 31 < 1024 := by omega
  have hc32 : rest.length + 32 < 1024 := by omega
  have hc33 : rest.length + 33 < 1024 := by omega
  have hc34 : rest.length + 34 < 1024 := by omega
  have hc35 : rest.length + 35 < 1024 := by omega
  have hc36 : rest.length + 36 < 1024 := by omega
  have hc37 : rest.length + 37 < 1024 := by omega
  have hc38 : rest.length + 38 < 1024 := by omega
  have hc39 : rest.length + 39 < 1024 := by omega
  have hc40 : rest.length + 40 < 1024 := by omega
  have hc41 : rest.length + 41 < 1024 := by omega
  simp [hz, hzn, exitpart0Program, exitpart0Model, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, Challenge.EvmProof.Word.literal_eq_ofNat, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8, hc9, hc10, hc11, hc12, hc13, hc14, hc15, hc16, hc17, hc18, hc19, hc20, hc21, hc22, hc23, hc24, hc25, hc26, hc27, hc28, hc29, hc30, hc31, hc32, hc33, hc34, hc35, hc36, hc37, hc38, hc39, hc40, hc41]

#print axioms exitpart0_run

def exitpart1Program : List Instr :=
  [.op .POP,
   .op .POP,
   .op .POP,
   .op .POP,
   .op .POP,
   .push 2 1568,
   .op .MLOAD]

def exitpart1Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 : UInt256) (rest : List UInt256) : State :=
  let v0 : UInt256 := MachineState.readWord s.memory 1568
  {s with pc := UInt256.ofNat 8817, memory := s.memory, stack := v0 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: x18 :: x19 :: x20 :: rest}

theorem exitpart1_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 982) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions exitpart1Program {s with pc := UInt256.ofNat 8808, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: x18 :: x19 :: x20 :: rest} =
      some (exitpart1Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 rest) := by
  have hz : ({val := 0} : UInt256) = UInt256.ofNat 0 := rfl
  have hzn : ({val := 0} : UInt256).toNat = 0 := rfl
  have hc0 : rest.length + 0 < 1024 := by omega
  have hc1 : rest.length + 1 < 1024 := by omega
  have hc2 : rest.length + 2 < 1024 := by omega
  have hc3 : rest.length + 3 < 1024 := by omega
  have hc4 : rest.length + 4 < 1024 := by omega
  have hc5 : rest.length + 5 < 1024 := by omega
  have hc6 : rest.length + 6 < 1024 := by omega
  have hc7 : rest.length + 7 < 1024 := by omega
  have hc8 : rest.length + 8 < 1024 := by omega
  have hc9 : rest.length + 9 < 1024 := by omega
  have hc10 : rest.length + 10 < 1024 := by omega
  have hc11 : rest.length + 11 < 1024 := by omega
  have hc12 : rest.length + 12 < 1024 := by omega
  have hc13 : rest.length + 13 < 1024 := by omega
  have hc14 : rest.length + 14 < 1024 := by omega
  have hc15 : rest.length + 15 < 1024 := by omega
  have hc16 : rest.length + 16 < 1024 := by omega
  have hc17 : rest.length + 17 < 1024 := by omega
  have hc18 : rest.length + 18 < 1024 := by omega
  have hc19 : rest.length + 19 < 1024 := by omega
  have hc20 : rest.length + 20 < 1024 := by omega
  have hc21 : rest.length + 21 < 1024 := by omega
  have hc22 : rest.length + 22 < 1024 := by omega
  have hc23 : rest.length + 23 < 1024 := by omega
  have hc24 : rest.length + 24 < 1024 := by omega
  have hc25 : rest.length + 25 < 1024 := by omega
  have hc26 : rest.length + 26 < 1024 := by omega
  have hc27 : rest.length + 27 < 1024 := by omega
  have hc28 : rest.length + 28 < 1024 := by omega
  have hc29 : rest.length + 29 < 1024 := by omega
  have hc30 : rest.length + 30 < 1024 := by omega
  have hc31 : rest.length + 31 < 1024 := by omega
  have hc32 : rest.length + 32 < 1024 := by omega
  have hc33 : rest.length + 33 < 1024 := by omega
  have hc34 : rest.length + 34 < 1024 := by omega
  have hc35 : rest.length + 35 < 1024 := by omega
  have hc36 : rest.length + 36 < 1024 := by omega
  have hc37 : rest.length + 37 < 1024 := by omega
  have hc38 : rest.length + 38 < 1024 := by omega
  have hc39 : rest.length + 39 < 1024 := by omega
  have hc40 : rest.length + 40 < 1024 := by omega
  have hc41 : rest.length + 41 < 1024 := by omega
  have ha1568 : (1568 : UInt256).toNat = 1568 := rfl
  have hf1568 := HistoricalSearch.CRTMemoryBounds.activeWords_fix s 1568 32 (by decide) (by norm_num) hact
  simp [hz, hzn, exitpart1Program, exitpart1Model, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, Challenge.EvmProof.Word.literal_eq_ofNat, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8, hc9, hc10, hc11, hc12, hc13, hc14, hc15, hc16, hc17, hc18, hc19, hc20, hc21, hc22, hc23, hc24, hc25, hc26, hc27, hc28, hc29, hc30, hc31, hc32, hc33, hc34, hc35, hc36, hc37, hc38, hc39, hc40, hc41, ha1568, hf1568]

#print axioms exitpart1_run

def exitpart2Program : List Instr :=
  [.push 2 1536,
   .op .MLOAD,
   .push 2 1504,
   .op .MLOAD,
   .push 2 1472,
   .op .MLOAD,
   .push 2 1440,
   .op .MLOAD]

def exitpart2Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 : UInt256) (rest : List UInt256) : State :=
  let v0 : UInt256 := MachineState.readWord s.memory 1536
  let v1 : UInt256 := MachineState.readWord s.memory 1504
  let v2 : UInt256 := MachineState.readWord s.memory 1472
  let v3 : UInt256 := MachineState.readWord s.memory 1440
  {s with pc := UInt256.ofNat 8833, memory := s.memory, stack := v3 :: v2 :: v1 :: v0 :: x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: rest}

theorem exitpart2_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 982) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions exitpart2Program {s with pc := UInt256.ofNat 8817, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: rest} =
      some (exitpart2Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 rest) := by
  have hz : ({val := 0} : UInt256) = UInt256.ofNat 0 := rfl
  have hzn : ({val := 0} : UInt256).toNat = 0 := rfl
  have hc0 : rest.length + 0 < 1024 := by omega
  have hc1 : rest.length + 1 < 1024 := by omega
  have hc2 : rest.length + 2 < 1024 := by omega
  have hc3 : rest.length + 3 < 1024 := by omega
  have hc4 : rest.length + 4 < 1024 := by omega
  have hc5 : rest.length + 5 < 1024 := by omega
  have hc6 : rest.length + 6 < 1024 := by omega
  have hc7 : rest.length + 7 < 1024 := by omega
  have hc8 : rest.length + 8 < 1024 := by omega
  have hc9 : rest.length + 9 < 1024 := by omega
  have hc10 : rest.length + 10 < 1024 := by omega
  have hc11 : rest.length + 11 < 1024 := by omega
  have hc12 : rest.length + 12 < 1024 := by omega
  have hc13 : rest.length + 13 < 1024 := by omega
  have hc14 : rest.length + 14 < 1024 := by omega
  have hc15 : rest.length + 15 < 1024 := by omega
  have hc16 : rest.length + 16 < 1024 := by omega
  have hc17 : rest.length + 17 < 1024 := by omega
  have hc18 : rest.length + 18 < 1024 := by omega
  have hc19 : rest.length + 19 < 1024 := by omega
  have hc20 : rest.length + 20 < 1024 := by omega
  have hc21 : rest.length + 21 < 1024 := by omega
  have hc22 : rest.length + 22 < 1024 := by omega
  have hc23 : rest.length + 23 < 1024 := by omega
  have hc24 : rest.length + 24 < 1024 := by omega
  have hc25 : rest.length + 25 < 1024 := by omega
  have hc26 : rest.length + 26 < 1024 := by omega
  have hc27 : rest.length + 27 < 1024 := by omega
  have hc28 : rest.length + 28 < 1024 := by omega
  have hc29 : rest.length + 29 < 1024 := by omega
  have hc30 : rest.length + 30 < 1024 := by omega
  have hc31 : rest.length + 31 < 1024 := by omega
  have hc32 : rest.length + 32 < 1024 := by omega
  have hc33 : rest.length + 33 < 1024 := by omega
  have hc34 : rest.length + 34 < 1024 := by omega
  have hc35 : rest.length + 35 < 1024 := by omega
  have hc36 : rest.length + 36 < 1024 := by omega
  have hc37 : rest.length + 37 < 1024 := by omega
  have hc38 : rest.length + 38 < 1024 := by omega
  have hc39 : rest.length + 39 < 1024 := by omega
  have hc40 : rest.length + 40 < 1024 := by omega
  have hc41 : rest.length + 41 < 1024 := by omega
  have ha1536 : (1536 : UInt256).toNat = 1536 := rfl
  have hf1536 := HistoricalSearch.CRTMemoryBounds.activeWords_fix s 1536 32 (by decide) (by norm_num) hact
  have ha1504 : (1504 : UInt256).toNat = 1504 := rfl
  have hf1504 := HistoricalSearch.CRTMemoryBounds.activeWords_fix s 1504 32 (by decide) (by norm_num) hact
  have ha1472 : (1472 : UInt256).toNat = 1472 := rfl
  have hf1472 := HistoricalSearch.CRTMemoryBounds.activeWords_fix s 1472 32 (by decide) (by norm_num) hact
  have ha1440 : (1440 : UInt256).toNat = 1440 := rfl
  have hf1440 := HistoricalSearch.CRTMemoryBounds.activeWords_fix s 1440 32 (by decide) (by norm_num) hact
  simp [hz, hzn, exitpart2Program, exitpart2Model, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, Challenge.EvmProof.Word.literal_eq_ofNat, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8, hc9, hc10, hc11, hc12, hc13, hc14, hc15, hc16, hc17, hc18, hc19, hc20, hc21, hc22, hc23, hc24, hc25, hc26, hc27, hc28, hc29, hc30, hc31, hc32, hc33, hc34, hc35, hc36, hc37, hc38, hc39, hc40, hc41, ha1536, hf1536, ha1504, hf1504, ha1472, hf1472, ha1440, hf1440]

#print axioms exitpart2_run

def exitpart3Program : List Instr :=
  [.push 2 1408,
   .op .MLOAD,
   .push 2 1376,
   .op .MLOAD,
   .push 2 1344,
   .op .MLOAD,
   .push 1 96,
   .op .SHR]

def exitpart3Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 : UInt256) (rest : List UInt256) : State :=
  let v0 : UInt256 := MachineState.readWord s.memory 1408
  let v1 : UInt256 := MachineState.readWord s.memory 1376
  let v2 : UInt256 := MachineState.readWord s.memory 1344
  let v3 : UInt256 := UInt256.shiftRight v2 (UInt256.ofNat 96)
  {s with pc := UInt256.ofNat 8848, memory := s.memory, stack := v3 :: v1 :: v0 :: x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: x18 :: x19 :: x20 :: rest}

theorem exitpart3_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 982) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions exitpart3Program {s with pc := UInt256.ofNat 8833, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: x18 :: x19 :: x20 :: rest} =
      some (exitpart3Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 rest) := by
  have hz : ({val := 0} : UInt256) = UInt256.ofNat 0 := rfl
  have hzn : ({val := 0} : UInt256).toNat = 0 := rfl
  have hc0 : rest.length + 0 < 1024 := by omega
  have hc1 : rest.length + 1 < 1024 := by omega
  have hc2 : rest.length + 2 < 1024 := by omega
  have hc3 : rest.length + 3 < 1024 := by omega
  have hc4 : rest.length + 4 < 1024 := by omega
  have hc5 : rest.length + 5 < 1024 := by omega
  have hc6 : rest.length + 6 < 1024 := by omega
  have hc7 : rest.length + 7 < 1024 := by omega
  have hc8 : rest.length + 8 < 1024 := by omega
  have hc9 : rest.length + 9 < 1024 := by omega
  have hc10 : rest.length + 10 < 1024 := by omega
  have hc11 : rest.length + 11 < 1024 := by omega
  have hc12 : rest.length + 12 < 1024 := by omega
  have hc13 : rest.length + 13 < 1024 := by omega
  have hc14 : rest.length + 14 < 1024 := by omega
  have hc15 : rest.length + 15 < 1024 := by omega
  have hc16 : rest.length + 16 < 1024 := by omega
  have hc17 : rest.length + 17 < 1024 := by omega
  have hc18 : rest.length + 18 < 1024 := by omega
  have hc19 : rest.length + 19 < 1024 := by omega
  have hc20 : rest.length + 20 < 1024 := by omega
  have hc21 : rest.length + 21 < 1024 := by omega
  have hc22 : rest.length + 22 < 1024 := by omega
  have hc23 : rest.length + 23 < 1024 := by omega
  have hc24 : rest.length + 24 < 1024 := by omega
  have hc25 : rest.length + 25 < 1024 := by omega
  have hc26 : rest.length + 26 < 1024 := by omega
  have hc27 : rest.length + 27 < 1024 := by omega
  have hc28 : rest.length + 28 < 1024 := by omega
  have hc29 : rest.length + 29 < 1024 := by omega
  have hc30 : rest.length + 30 < 1024 := by omega
  have hc31 : rest.length + 31 < 1024 := by omega
  have hc32 : rest.length + 32 < 1024 := by omega
  have hc33 : rest.length + 33 < 1024 := by omega
  have hc34 : rest.length + 34 < 1024 := by omega
  have hc35 : rest.length + 35 < 1024 := by omega
  have hc36 : rest.length + 36 < 1024 := by omega
  have hc37 : rest.length + 37 < 1024 := by omega
  have hc38 : rest.length + 38 < 1024 := by omega
  have hc39 : rest.length + 39 < 1024 := by omega
  have hc40 : rest.length + 40 < 1024 := by omega
  have hc41 : rest.length + 41 < 1024 := by omega
  have ha1408 : (1408 : UInt256).toNat = 1408 := rfl
  have hf1408 := HistoricalSearch.CRTMemoryBounds.activeWords_fix s 1408 32 (by decide) (by norm_num) hact
  have ha1376 : (1376 : UInt256).toNat = 1376 := rfl
  have hf1376 := HistoricalSearch.CRTMemoryBounds.activeWords_fix s 1376 32 (by decide) (by norm_num) hact
  have ha1344 : (1344 : UInt256).toNat = 1344 := rfl
  have hf1344 := HistoricalSearch.CRTMemoryBounds.activeWords_fix s 1344 32 (by decide) (by norm_num) hact
  simp [hz, hzn, exitpart3Program, exitpart3Model, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, Challenge.EvmProof.Word.literal_eq_ofNat, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8, hc9, hc10, hc11, hc12, hc13, hc14, hc15, hc16, hc17, hc18, hc19, hc20, hc21, hc22, hc23, hc24, hc25, hc26, hc27, hc28, hc29, hc30, hc31, hc32, hc33, hc34, hc35, hc36, hc37, hc38, hc39, hc40, hc41, ha1408, hf1408, ha1376, hf1376, ha1344, hf1344]

#print axioms exitpart3_run

def exitpart4Program : List Instr :=
  [.op (.Dup ⟨1, by decide⟩),
   .push 1 148,
   .op .SHL,
   .op .OR,
   .push 2 2336,
   .op .MSTORE,
   .push 1 108,
   .op .SHR]

def exitpart4Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 : UInt256) (rest : List UInt256) : State :=
  let v0 : UInt256 := UInt256.shiftLeft x1 (UInt256.ofNat 148)
  let v1 : UInt256 := UInt256.lor v0 x0
  let v2 : ByteArray := MachineState.writeBytes s.memory (Data.Bytes.natToBytesPadded v1.toNat 32) 2336
  let v3 : UInt256 := UInt256.shiftRight x1 (UInt256.ofNat 108)
  {s with pc := UInt256.ofNat 8860, memory := v2, stack := v3 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: x18 :: x19 :: x20 :: x21 :: x22 :: x23 :: rest}

theorem exitpart4_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 982) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions exitpart4Program {s with pc := UInt256.ofNat 8848, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: x18 :: x19 :: x20 :: x21 :: x22 :: x23 :: rest} =
      some (exitpart4Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 rest) := by
  have hz : ({val := 0} : UInt256) = UInt256.ofNat 0 := rfl
  have hzn : ({val := 0} : UInt256).toNat = 0 := rfl
  have hc0 : rest.length + 0 < 1024 := by omega
  have hc1 : rest.length + 1 < 1024 := by omega
  have hc2 : rest.length + 2 < 1024 := by omega
  have hc3 : rest.length + 3 < 1024 := by omega
  have hc4 : rest.length + 4 < 1024 := by omega
  have hc5 : rest.length + 5 < 1024 := by omega
  have hc6 : rest.length + 6 < 1024 := by omega
  have hc7 : rest.length + 7 < 1024 := by omega
  have hc8 : rest.length + 8 < 1024 := by omega
  have hc9 : rest.length + 9 < 1024 := by omega
  have hc10 : rest.length + 10 < 1024 := by omega
  have hc11 : rest.length + 11 < 1024 := by omega
  have hc12 : rest.length + 12 < 1024 := by omega
  have hc13 : rest.length + 13 < 1024 := by omega
  have hc14 : rest.length + 14 < 1024 := by omega
  have hc15 : rest.length + 15 < 1024 := by omega
  have hc16 : rest.length + 16 < 1024 := by omega
  have hc17 : rest.length + 17 < 1024 := by omega
  have hc18 : rest.length + 18 < 1024 := by omega
  have hc19 : rest.length + 19 < 1024 := by omega
  have hc20 : rest.length + 20 < 1024 := by omega
  have hc21 : rest.length + 21 < 1024 := by omega
  have hc22 : rest.length + 22 < 1024 := by omega
  have hc23 : rest.length + 23 < 1024 := by omega
  have hc24 : rest.length + 24 < 1024 := by omega
  have hc25 : rest.length + 25 < 1024 := by omega
  have hc26 : rest.length + 26 < 1024 := by omega
  have hc27 : rest.length + 27 < 1024 := by omega
  have hc28 : rest.length + 28 < 1024 := by omega
  have hc29 : rest.length + 29 < 1024 := by omega
  have hc30 : rest.length + 30 < 1024 := by omega
  have hc31 : rest.length + 31 < 1024 := by omega
  have hc32 : rest.length + 32 < 1024 := by omega
  have hc33 : rest.length + 33 < 1024 := by omega
  have hc34 : rest.length + 34 < 1024 := by omega
  have hc35 : rest.length + 35 < 1024 := by omega
  have hc36 : rest.length + 36 < 1024 := by omega
  have hc37 : rest.length + 37 < 1024 := by omega
  have hc38 : rest.length + 38 < 1024 := by omega
  have hc39 : rest.length + 39 < 1024 := by omega
  have hc40 : rest.length + 40 < 1024 := by omega
  have hc41 : rest.length + 41 < 1024 := by omega
  have ha2336 : (2336 : UInt256).toNat = 2336 := rfl
  have hf2336 := HistoricalSearch.CRTMemoryBounds.activeWords_fix s 2336 32 (by decide) (by norm_num) hact
  simp [hz, hzn, exitpart4Program, exitpart4Model, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, Challenge.EvmProof.Word.literal_eq_ofNat, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8, hc9, hc10, hc11, hc12, hc13, hc14, hc15, hc16, hc17, hc18, hc19, hc20, hc21, hc22, hc23, hc24, hc25, hc26, hc27, hc28, hc29, hc30, hc31, hc32, hc33, hc34, hc35, hc36, hc37, hc38, hc39, hc40, hc41, ha2336, hf2336]

#print axioms exitpart4_run

def exitpart5Program : List Instr :=
  [.op (.Dup ⟨1, by decide⟩),
   .push 1 136,
   .op .SHL,
   .op .OR,
   .push 2 2304,
   .op .MSTORE,
   .push 1 120,
   .op .SHR]

def exitpart5Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 : UInt256) (rest : List UInt256) : State :=
  let v0 : UInt256 := UInt256.shiftLeft x1 (UInt256.ofNat 136)
  let v1 : UInt256 := UInt256.lor v0 x0
  let v2 : ByteArray := MachineState.writeBytes s.memory (Data.Bytes.natToBytesPadded v1.toNat 32) 2304
  let v3 : UInt256 := UInt256.shiftRight x1 (UInt256.ofNat 120)
  {s with pc := UInt256.ofNat 8872, memory := v2, stack := v3 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: x18 :: x19 :: x20 :: x21 :: x22 :: rest}

theorem exitpart5_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 982) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions exitpart5Program {s with pc := UInt256.ofNat 8860, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: x18 :: x19 :: x20 :: x21 :: x22 :: rest} =
      some (exitpart5Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 rest) := by
  have hz : ({val := 0} : UInt256) = UInt256.ofNat 0 := rfl
  have hzn : ({val := 0} : UInt256).toNat = 0 := rfl
  have hc0 : rest.length + 0 < 1024 := by omega
  have hc1 : rest.length + 1 < 1024 := by omega
  have hc2 : rest.length + 2 < 1024 := by omega
  have hc3 : rest.length + 3 < 1024 := by omega
  have hc4 : rest.length + 4 < 1024 := by omega
  have hc5 : rest.length + 5 < 1024 := by omega
  have hc6 : rest.length + 6 < 1024 := by omega
  have hc7 : rest.length + 7 < 1024 := by omega
  have hc8 : rest.length + 8 < 1024 := by omega
  have hc9 : rest.length + 9 < 1024 := by omega
  have hc10 : rest.length + 10 < 1024 := by omega
  have hc11 : rest.length + 11 < 1024 := by omega
  have hc12 : rest.length + 12 < 1024 := by omega
  have hc13 : rest.length + 13 < 1024 := by omega
  have hc14 : rest.length + 14 < 1024 := by omega
  have hc15 : rest.length + 15 < 1024 := by omega
  have hc16 : rest.length + 16 < 1024 := by omega
  have hc17 : rest.length + 17 < 1024 := by omega
  have hc18 : rest.length + 18 < 1024 := by omega
  have hc19 : rest.length + 19 < 1024 := by omega
  have hc20 : rest.length + 20 < 1024 := by omega
  have hc21 : rest.length + 21 < 1024 := by omega
  have hc22 : rest.length + 22 < 1024 := by omega
  have hc23 : rest.length + 23 < 1024 := by omega
  have hc24 : rest.length + 24 < 1024 := by omega
  have hc25 : rest.length + 25 < 1024 := by omega
  have hc26 : rest.length + 26 < 1024 := by omega
  have hc27 : rest.length + 27 < 1024 := by omega
  have hc28 : rest.length + 28 < 1024 := by omega
  have hc29 : rest.length + 29 < 1024 := by omega
  have hc30 : rest.length + 30 < 1024 := by omega
  have hc31 : rest.length + 31 < 1024 := by omega
  have hc32 : rest.length + 32 < 1024 := by omega
  have hc33 : rest.length + 33 < 1024 := by omega
  have hc34 : rest.length + 34 < 1024 := by omega
  have hc35 : rest.length + 35 < 1024 := by omega
  have hc36 : rest.length + 36 < 1024 := by omega
  have hc37 : rest.length + 37 < 1024 := by omega
  have hc38 : rest.length + 38 < 1024 := by omega
  have hc39 : rest.length + 39 < 1024 := by omega
  have hc40 : rest.length + 40 < 1024 := by omega
  have hc41 : rest.length + 41 < 1024 := by omega
  have ha2304 : (2304 : UInt256).toNat = 2304 := rfl
  have hf2304 := HistoricalSearch.CRTMemoryBounds.activeWords_fix s 2304 32 (by decide) (by norm_num) hact
  simp [hz, hzn, exitpart5Program, exitpart5Model, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, Challenge.EvmProof.Word.literal_eq_ofNat, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8, hc9, hc10, hc11, hc12, hc13, hc14, hc15, hc16, hc17, hc18, hc19, hc20, hc21, hc22, hc23, hc24, hc25, hc26, hc27, hc28, hc29, hc30, hc31, hc32, hc33, hc34, hc35, hc36, hc37, hc38, hc39, hc40, hc41, ha2304, hf2304]

#print axioms exitpart5_run

def exitpart6Program : List Instr :=
  [.op (.Dup ⟨1, by decide⟩),
   .push 1 124,
   .op .SHL,
   .op .OR,
   .push 2 2272,
   .op .MSTORE,
   .push 1 132,
   .op .SHR]

def exitpart6Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 : UInt256) (rest : List UInt256) : State :=
  let v0 : UInt256 := UInt256.shiftLeft x1 (UInt256.ofNat 124)
  let v1 : UInt256 := UInt256.lor v0 x0
  let v2 : ByteArray := MachineState.writeBytes s.memory (Data.Bytes.natToBytesPadded v1.toNat 32) 2272
  let v3 : UInt256 := UInt256.shiftRight x1 (UInt256.ofNat 132)
  {s with pc := UInt256.ofNat 8884, memory := v2, stack := v3 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: x18 :: x19 :: x20 :: x21 :: rest}

theorem exitpart6_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 982) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions exitpart6Program {s with pc := UInt256.ofNat 8872, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: x18 :: x19 :: x20 :: x21 :: rest} =
      some (exitpart6Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 rest) := by
  have hz : ({val := 0} : UInt256) = UInt256.ofNat 0 := rfl
  have hzn : ({val := 0} : UInt256).toNat = 0 := rfl
  have hc0 : rest.length + 0 < 1024 := by omega
  have hc1 : rest.length + 1 < 1024 := by omega
  have hc2 : rest.length + 2 < 1024 := by omega
  have hc3 : rest.length + 3 < 1024 := by omega
  have hc4 : rest.length + 4 < 1024 := by omega
  have hc5 : rest.length + 5 < 1024 := by omega
  have hc6 : rest.length + 6 < 1024 := by omega
  have hc7 : rest.length + 7 < 1024 := by omega
  have hc8 : rest.length + 8 < 1024 := by omega
  have hc9 : rest.length + 9 < 1024 := by omega
  have hc10 : rest.length + 10 < 1024 := by omega
  have hc11 : rest.length + 11 < 1024 := by omega
  have hc12 : rest.length + 12 < 1024 := by omega
  have hc13 : rest.length + 13 < 1024 := by omega
  have hc14 : rest.length + 14 < 1024 := by omega
  have hc15 : rest.length + 15 < 1024 := by omega
  have hc16 : rest.length + 16 < 1024 := by omega
  have hc17 : rest.length + 17 < 1024 := by omega
  have hc18 : rest.length + 18 < 1024 := by omega
  have hc19 : rest.length + 19 < 1024 := by omega
  have hc20 : rest.length + 20 < 1024 := by omega
  have hc21 : rest.length + 21 < 1024 := by omega
  have hc22 : rest.length + 22 < 1024 := by omega
  have hc23 : rest.length + 23 < 1024 := by omega
  have hc24 : rest.length + 24 < 1024 := by omega
  have hc25 : rest.length + 25 < 1024 := by omega
  have hc26 : rest.length + 26 < 1024 := by omega
  have hc27 : rest.length + 27 < 1024 := by omega
  have hc28 : rest.length + 28 < 1024 := by omega
  have hc29 : rest.length + 29 < 1024 := by omega
  have hc30 : rest.length + 30 < 1024 := by omega
  have hc31 : rest.length + 31 < 1024 := by omega
  have hc32 : rest.length + 32 < 1024 := by omega
  have hc33 : rest.length + 33 < 1024 := by omega
  have hc34 : rest.length + 34 < 1024 := by omega
  have hc35 : rest.length + 35 < 1024 := by omega
  have hc36 : rest.length + 36 < 1024 := by omega
  have hc37 : rest.length + 37 < 1024 := by omega
  have hc38 : rest.length + 38 < 1024 := by omega
  have hc39 : rest.length + 39 < 1024 := by omega
  have hc40 : rest.length + 40 < 1024 := by omega
  have hc41 : rest.length + 41 < 1024 := by omega
  have ha2272 : (2272 : UInt256).toNat = 2272 := rfl
  have hf2272 := HistoricalSearch.CRTMemoryBounds.activeWords_fix s 2272 32 (by decide) (by norm_num) hact
  simp [hz, hzn, exitpart6Program, exitpart6Model, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, Challenge.EvmProof.Word.literal_eq_ofNat, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8, hc9, hc10, hc11, hc12, hc13, hc14, hc15, hc16, hc17, hc18, hc19, hc20, hc21, hc22, hc23, hc24, hc25, hc26, hc27, hc28, hc29, hc30, hc31, hc32, hc33, hc34, hc35, hc36, hc37, hc38, hc39, hc40, hc41, ha2272, hf2272]

#print axioms exitpart6_run

def exitpart7Program : List Instr :=
  [.op (.Dup ⟨1, by decide⟩),
   .push 1 112,
   .op .SHL,
   .op .OR,
   .push 2 2240,
   .op .MSTORE,
   .push 1 144,
   .op .SHR]

def exitpart7Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 : UInt256) (rest : List UInt256) : State :=
  let v0 : UInt256 := UInt256.shiftLeft x1 (UInt256.ofNat 112)
  let v1 : UInt256 := UInt256.lor v0 x0
  let v2 : ByteArray := MachineState.writeBytes s.memory (Data.Bytes.natToBytesPadded v1.toNat 32) 2240
  let v3 : UInt256 := UInt256.shiftRight x1 (UInt256.ofNat 144)
  {s with pc := UInt256.ofNat 8896, memory := v2, stack := v3 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: x18 :: x19 :: x20 :: rest}

theorem exitpart7_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 982) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions exitpart7Program {s with pc := UInt256.ofNat 8884, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: x18 :: x19 :: x20 :: rest} =
      some (exitpart7Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 rest) := by
  have hz : ({val := 0} : UInt256) = UInt256.ofNat 0 := rfl
  have hzn : ({val := 0} : UInt256).toNat = 0 := rfl
  have hc0 : rest.length + 0 < 1024 := by omega
  have hc1 : rest.length + 1 < 1024 := by omega
  have hc2 : rest.length + 2 < 1024 := by omega
  have hc3 : rest.length + 3 < 1024 := by omega
  have hc4 : rest.length + 4 < 1024 := by omega
  have hc5 : rest.length + 5 < 1024 := by omega
  have hc6 : rest.length + 6 < 1024 := by omega
  have hc7 : rest.length + 7 < 1024 := by omega
  have hc8 : rest.length + 8 < 1024 := by omega
  have hc9 : rest.length + 9 < 1024 := by omega
  have hc10 : rest.length + 10 < 1024 := by omega
  have hc11 : rest.length + 11 < 1024 := by omega
  have hc12 : rest.length + 12 < 1024 := by omega
  have hc13 : rest.length + 13 < 1024 := by omega
  have hc14 : rest.length + 14 < 1024 := by omega
  have hc15 : rest.length + 15 < 1024 := by omega
  have hc16 : rest.length + 16 < 1024 := by omega
  have hc17 : rest.length + 17 < 1024 := by omega
  have hc18 : rest.length + 18 < 1024 := by omega
  have hc19 : rest.length + 19 < 1024 := by omega
  have hc20 : rest.length + 20 < 1024 := by omega
  have hc21 : rest.length + 21 < 1024 := by omega
  have hc22 : rest.length + 22 < 1024 := by omega
  have hc23 : rest.length + 23 < 1024 := by omega
  have hc24 : rest.length + 24 < 1024 := by omega
  have hc25 : rest.length + 25 < 1024 := by omega
  have hc26 : rest.length + 26 < 1024 := by omega
  have hc27 : rest.length + 27 < 1024 := by omega
  have hc28 : rest.length + 28 < 1024 := by omega
  have hc29 : rest.length + 29 < 1024 := by omega
  have hc30 : rest.length + 30 < 1024 := by omega
  have hc31 : rest.length + 31 < 1024 := by omega
  have hc32 : rest.length + 32 < 1024 := by omega
  have hc33 : rest.length + 33 < 1024 := by omega
  have hc34 : rest.length + 34 < 1024 := by omega
  have hc35 : rest.length + 35 < 1024 := by omega
  have hc36 : rest.length + 36 < 1024 := by omega
  have hc37 : rest.length + 37 < 1024 := by omega
  have hc38 : rest.length + 38 < 1024 := by omega
  have hc39 : rest.length + 39 < 1024 := by omega
  have hc40 : rest.length + 40 < 1024 := by omega
  have hc41 : rest.length + 41 < 1024 := by omega
  have ha2240 : (2240 : UInt256).toNat = 2240 := rfl
  have hf2240 := HistoricalSearch.CRTMemoryBounds.activeWords_fix s 2240 32 (by decide) (by norm_num) hact
  simp [hz, hzn, exitpart7Program, exitpart7Model, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, Challenge.EvmProof.Word.literal_eq_ofNat, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8, hc9, hc10, hc11, hc12, hc13, hc14, hc15, hc16, hc17, hc18, hc19, hc20, hc21, hc22, hc23, hc24, hc25, hc26, hc27, hc28, hc29, hc30, hc31, hc32, hc33, hc34, hc35, hc36, hc37, hc38, hc39, hc40, hc41, ha2240, hf2240]

#print axioms exitpart7_run

def exitpart8Program : List Instr :=
  [.op (.Dup ⟨1, by decide⟩),
   .push 1 100,
   .op .SHL,
   .op .OR,
   .push 2 2208,
   .op .MSTORE,
   .push 1 156,
   .op .SHR]

def exitpart8Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 : UInt256) (rest : List UInt256) : State :=
  let v0 : UInt256 := UInt256.shiftLeft x1 (UInt256.ofNat 100)
  let v1 : UInt256 := UInt256.lor v0 x0
  let v2 : ByteArray := MachineState.writeBytes s.memory (Data.Bytes.natToBytesPadded v1.toNat 32) 2208
  let v3 : UInt256 := UInt256.shiftRight x1 (UInt256.ofNat 156)
  {s with pc := UInt256.ofNat 8908, memory := v2, stack := v3 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: x18 :: x19 :: rest}

theorem exitpart8_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 982) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions exitpart8Program {s with pc := UInt256.ofNat 8896, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: x18 :: x19 :: rest} =
      some (exitpart8Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 rest) := by
  have hz : ({val := 0} : UInt256) = UInt256.ofNat 0 := rfl
  have hzn : ({val := 0} : UInt256).toNat = 0 := rfl
  have hc0 : rest.length + 0 < 1024 := by omega
  have hc1 : rest.length + 1 < 1024 := by omega
  have hc2 : rest.length + 2 < 1024 := by omega
  have hc3 : rest.length + 3 < 1024 := by omega
  have hc4 : rest.length + 4 < 1024 := by omega
  have hc5 : rest.length + 5 < 1024 := by omega
  have hc6 : rest.length + 6 < 1024 := by omega
  have hc7 : rest.length + 7 < 1024 := by omega
  have hc8 : rest.length + 8 < 1024 := by omega
  have hc9 : rest.length + 9 < 1024 := by omega
  have hc10 : rest.length + 10 < 1024 := by omega
  have hc11 : rest.length + 11 < 1024 := by omega
  have hc12 : rest.length + 12 < 1024 := by omega
  have hc13 : rest.length + 13 < 1024 := by omega
  have hc14 : rest.length + 14 < 1024 := by omega
  have hc15 : rest.length + 15 < 1024 := by omega
  have hc16 : rest.length + 16 < 1024 := by omega
  have hc17 : rest.length + 17 < 1024 := by omega
  have hc18 : rest.length + 18 < 1024 := by omega
  have hc19 : rest.length + 19 < 1024 := by omega
  have hc20 : rest.length + 20 < 1024 := by omega
  have hc21 : rest.length + 21 < 1024 := by omega
  have hc22 : rest.length + 22 < 1024 := by omega
  have hc23 : rest.length + 23 < 1024 := by omega
  have hc24 : rest.length + 24 < 1024 := by omega
  have hc25 : rest.length + 25 < 1024 := by omega
  have hc26 : rest.length + 26 < 1024 := by omega
  have hc27 : rest.length + 27 < 1024 := by omega
  have hc28 : rest.length + 28 < 1024 := by omega
  have hc29 : rest.length + 29 < 1024 := by omega
  have hc30 : rest.length + 30 < 1024 := by omega
  have hc31 : rest.length + 31 < 1024 := by omega
  have hc32 : rest.length + 32 < 1024 := by omega
  have hc33 : rest.length + 33 < 1024 := by omega
  have hc34 : rest.length + 34 < 1024 := by omega
  have hc35 : rest.length + 35 < 1024 := by omega
  have hc36 : rest.length + 36 < 1024 := by omega
  have hc37 : rest.length + 37 < 1024 := by omega
  have hc38 : rest.length + 38 < 1024 := by omega
  have hc39 : rest.length + 39 < 1024 := by omega
  have hc40 : rest.length + 40 < 1024 := by omega
  have hc41 : rest.length + 41 < 1024 := by omega
  have ha2208 : (2208 : UInt256).toNat = 2208 := rfl
  have hf2208 := HistoricalSearch.CRTMemoryBounds.activeWords_fix s 2208 32 (by decide) (by norm_num) hact
  simp [hz, hzn, exitpart8Program, exitpart8Model, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, Challenge.EvmProof.Word.literal_eq_ofNat, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8, hc9, hc10, hc11, hc12, hc13, hc14, hc15, hc16, hc17, hc18, hc19, hc20, hc21, hc22, hc23, hc24, hc25, hc26, hc27, hc28, hc29, hc30, hc31, hc32, hc33, hc34, hc35, hc36, hc37, hc38, hc39, hc40, hc41, ha2208, hf2208]

#print axioms exitpart8_run

def exitpart9Program : List Instr :=
  [.op (.Dup ⟨1, by decide⟩),
   .push 1 88,
   .op .SHL,
   .op .OR,
   .push 2 2176,
   .op .MSTORE,
   .push 1 168,
   .op .SHR]

def exitpart9Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 : UInt256) (rest : List UInt256) : State :=
  let v0 : UInt256 := UInt256.shiftLeft x1 (UInt256.ofNat 88)
  let v1 : UInt256 := UInt256.lor v0 x0
  let v2 : ByteArray := MachineState.writeBytes s.memory (Data.Bytes.natToBytesPadded v1.toNat 32) 2176
  let v3 : UInt256 := UInt256.shiftRight x1 (UInt256.ofNat 168)
  {s with pc := UInt256.ofNat 8920, memory := v2, stack := v3 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: x18 :: rest}

theorem exitpart9_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 982) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions exitpart9Program {s with pc := UInt256.ofNat 8908, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: x18 :: rest} =
      some (exitpart9Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 rest) := by
  have hz : ({val := 0} : UInt256) = UInt256.ofNat 0 := rfl
  have hzn : ({val := 0} : UInt256).toNat = 0 := rfl
  have hc0 : rest.length + 0 < 1024 := by omega
  have hc1 : rest.length + 1 < 1024 := by omega
  have hc2 : rest.length + 2 < 1024 := by omega
  have hc3 : rest.length + 3 < 1024 := by omega
  have hc4 : rest.length + 4 < 1024 := by omega
  have hc5 : rest.length + 5 < 1024 := by omega
  have hc6 : rest.length + 6 < 1024 := by omega
  have hc7 : rest.length + 7 < 1024 := by omega
  have hc8 : rest.length + 8 < 1024 := by omega
  have hc9 : rest.length + 9 < 1024 := by omega
  have hc10 : rest.length + 10 < 1024 := by omega
  have hc11 : rest.length + 11 < 1024 := by omega
  have hc12 : rest.length + 12 < 1024 := by omega
  have hc13 : rest.length + 13 < 1024 := by omega
  have hc14 : rest.length + 14 < 1024 := by omega
  have hc15 : rest.length + 15 < 1024 := by omega
  have hc16 : rest.length + 16 < 1024 := by omega
  have hc17 : rest.length + 17 < 1024 := by omega
  have hc18 : rest.length + 18 < 1024 := by omega
  have hc19 : rest.length + 19 < 1024 := by omega
  have hc20 : rest.length + 20 < 1024 := by omega
  have hc21 : rest.length + 21 < 1024 := by omega
  have hc22 : rest.length + 22 < 1024 := by omega
  have hc23 : rest.length + 23 < 1024 := by omega
  have hc24 : rest.length + 24 < 1024 := by omega
  have hc25 : rest.length + 25 < 1024 := by omega
  have hc26 : rest.length + 26 < 1024 := by omega
  have hc27 : rest.length + 27 < 1024 := by omega
  have hc28 : rest.length + 28 < 1024 := by omega
  have hc29 : rest.length + 29 < 1024 := by omega
  have hc30 : rest.length + 30 < 1024 := by omega
  have hc31 : rest.length + 31 < 1024 := by omega
  have hc32 : rest.length + 32 < 1024 := by omega
  have hc33 : rest.length + 33 < 1024 := by omega
  have hc34 : rest.length + 34 < 1024 := by omega
  have hc35 : rest.length + 35 < 1024 := by omega
  have hc36 : rest.length + 36 < 1024 := by omega
  have hc37 : rest.length + 37 < 1024 := by omega
  have hc38 : rest.length + 38 < 1024 := by omega
  have hc39 : rest.length + 39 < 1024 := by omega
  have hc40 : rest.length + 40 < 1024 := by omega
  have hc41 : rest.length + 41 < 1024 := by omega
  have ha2176 : (2176 : UInt256).toNat = 2176 := rfl
  have hf2176 := HistoricalSearch.CRTMemoryBounds.activeWords_fix s 2176 32 (by decide) (by norm_num) hact
  simp [hz, hzn, exitpart9Program, exitpart9Model, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, Challenge.EvmProof.Word.literal_eq_ofNat, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8, hc9, hc10, hc11, hc12, hc13, hc14, hc15, hc16, hc17, hc18, hc19, hc20, hc21, hc22, hc23, hc24, hc25, hc26, hc27, hc28, hc29, hc30, hc31, hc32, hc33, hc34, hc35, hc36, hc37, hc38, hc39, hc40, hc41, ha2176, hf2176]

#print axioms exitpart9_run

def exitpart10Program : List Instr :=
  [.op (.Dup ⟨1, by decide⟩),
   .push 1 76,
   .op .SHL,
   .op .OR,
   .push 2 2144,
   .op .MSTORE,
   .push 1 180,
   .op .SHR]

def exitpart10Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 : UInt256) (rest : List UInt256) : State :=
  let v0 : UInt256 := UInt256.shiftLeft x1 (UInt256.ofNat 76)
  let v1 : UInt256 := UInt256.lor v0 x0
  let v2 : ByteArray := MachineState.writeBytes s.memory (Data.Bytes.natToBytesPadded v1.toNat 32) 2144
  let v3 : UInt256 := UInt256.shiftRight x1 (UInt256.ofNat 180)
  {s with pc := UInt256.ofNat 8932, memory := v2, stack := v3 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: rest}

theorem exitpart10_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 982) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions exitpart10Program {s with pc := UInt256.ofNat 8920, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: rest} =
      some (exitpart10Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 rest) := by
  have hz : ({val := 0} : UInt256) = UInt256.ofNat 0 := rfl
  have hzn : ({val := 0} : UInt256).toNat = 0 := rfl
  have hc0 : rest.length + 0 < 1024 := by omega
  have hc1 : rest.length + 1 < 1024 := by omega
  have hc2 : rest.length + 2 < 1024 := by omega
  have hc3 : rest.length + 3 < 1024 := by omega
  have hc4 : rest.length + 4 < 1024 := by omega
  have hc5 : rest.length + 5 < 1024 := by omega
  have hc6 : rest.length + 6 < 1024 := by omega
  have hc7 : rest.length + 7 < 1024 := by omega
  have hc8 : rest.length + 8 < 1024 := by omega
  have hc9 : rest.length + 9 < 1024 := by omega
  have hc10 : rest.length + 10 < 1024 := by omega
  have hc11 : rest.length + 11 < 1024 := by omega
  have hc12 : rest.length + 12 < 1024 := by omega
  have hc13 : rest.length + 13 < 1024 := by omega
  have hc14 : rest.length + 14 < 1024 := by omega
  have hc15 : rest.length + 15 < 1024 := by omega
  have hc16 : rest.length + 16 < 1024 := by omega
  have hc17 : rest.length + 17 < 1024 := by omega
  have hc18 : rest.length + 18 < 1024 := by omega
  have hc19 : rest.length + 19 < 1024 := by omega
  have hc20 : rest.length + 20 < 1024 := by omega
  have hc21 : rest.length + 21 < 1024 := by omega
  have hc22 : rest.length + 22 < 1024 := by omega
  have hc23 : rest.length + 23 < 1024 := by omega
  have hc24 : rest.length + 24 < 1024 := by omega
  have hc25 : rest.length + 25 < 1024 := by omega
  have hc26 : rest.length + 26 < 1024 := by omega
  have hc27 : rest.length + 27 < 1024 := by omega
  have hc28 : rest.length + 28 < 1024 := by omega
  have hc29 : rest.length + 29 < 1024 := by omega
  have hc30 : rest.length + 30 < 1024 := by omega
  have hc31 : rest.length + 31 < 1024 := by omega
  have hc32 : rest.length + 32 < 1024 := by omega
  have hc33 : rest.length + 33 < 1024 := by omega
  have hc34 : rest.length + 34 < 1024 := by omega
  have hc35 : rest.length + 35 < 1024 := by omega
  have hc36 : rest.length + 36 < 1024 := by omega
  have hc37 : rest.length + 37 < 1024 := by omega
  have hc38 : rest.length + 38 < 1024 := by omega
  have hc39 : rest.length + 39 < 1024 := by omega
  have hc40 : rest.length + 40 < 1024 := by omega
  have hc41 : rest.length + 41 < 1024 := by omega
  have ha2144 : (2144 : UInt256).toNat = 2144 := rfl
  have hf2144 := HistoricalSearch.CRTMemoryBounds.activeWords_fix s 2144 32 (by decide) (by norm_num) hact
  simp [hz, hzn, exitpart10Program, exitpart10Model, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, Challenge.EvmProof.Word.literal_eq_ofNat, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8, hc9, hc10, hc11, hc12, hc13, hc14, hc15, hc16, hc17, hc18, hc19, hc20, hc21, hc22, hc23, hc24, hc25, hc26, hc27, hc28, hc29, hc30, hc31, hc32, hc33, hc34, hc35, hc36, hc37, hc38, hc39, hc40, hc41, ha2144, hf2144]

#print axioms exitpart10_run

def exitpart11Program : List Instr :=
  [.push 2 1600,
   .op .MLOAD,
   .push 1 64,
   .op .SHL,
   .op .OR,
   .push 2 2112,
   .op .MSTORE]

def exitpart11Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 : UInt256) (rest : List UInt256) : State :=
  let v0 : UInt256 := MachineState.readWord s.memory 1600
  let v1 : UInt256 := UInt256.shiftLeft v0 (UInt256.ofNat 64)
  let v2 : UInt256 := UInt256.lor v1 x0
  let v3 : ByteArray := MachineState.writeBytes s.memory (Data.Bytes.natToBytesPadded v2.toNat 32) 2112
  {s with pc := UInt256.ofNat 8944, memory := v3, stack := x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: rest}

theorem exitpart11_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 982) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions exitpart11Program {s with pc := UInt256.ofNat 8932, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: rest} =
      some (exitpart11Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 rest) := by
  have hz : ({val := 0} : UInt256) = UInt256.ofNat 0 := rfl
  have hzn : ({val := 0} : UInt256).toNat = 0 := rfl
  have hc0 : rest.length + 0 < 1024 := by omega
  have hc1 : rest.length + 1 < 1024 := by omega
  have hc2 : rest.length + 2 < 1024 := by omega
  have hc3 : rest.length + 3 < 1024 := by omega
  have hc4 : rest.length + 4 < 1024 := by omega
  have hc5 : rest.length + 5 < 1024 := by omega
  have hc6 : rest.length + 6 < 1024 := by omega
  have hc7 : rest.length + 7 < 1024 := by omega
  have hc8 : rest.length + 8 < 1024 := by omega
  have hc9 : rest.length + 9 < 1024 := by omega
  have hc10 : rest.length + 10 < 1024 := by omega
  have hc11 : rest.length + 11 < 1024 := by omega
  have hc12 : rest.length + 12 < 1024 := by omega
  have hc13 : rest.length + 13 < 1024 := by omega
  have hc14 : rest.length + 14 < 1024 := by omega
  have hc15 : rest.length + 15 < 1024 := by omega
  have hc16 : rest.length + 16 < 1024 := by omega
  have hc17 : rest.length + 17 < 1024 := by omega
  have hc18 : rest.length + 18 < 1024 := by omega
  have hc19 : rest.length + 19 < 1024 := by omega
  have hc20 : rest.length + 20 < 1024 := by omega
  have hc21 : rest.length + 21 < 1024 := by omega
  have hc22 : rest.length + 22 < 1024 := by omega
  have hc23 : rest.length + 23 < 1024 := by omega
  have hc24 : rest.length + 24 < 1024 := by omega
  have hc25 : rest.length + 25 < 1024 := by omega
  have hc26 : rest.length + 26 < 1024 := by omega
  have hc27 : rest.length + 27 < 1024 := by omega
  have hc28 : rest.length + 28 < 1024 := by omega
  have hc29 : rest.length + 29 < 1024 := by omega
  have hc30 : rest.length + 30 < 1024 := by omega
  have hc31 : rest.length + 31 < 1024 := by omega
  have hc32 : rest.length + 32 < 1024 := by omega
  have hc33 : rest.length + 33 < 1024 := by omega
  have hc34 : rest.length + 34 < 1024 := by omega
  have hc35 : rest.length + 35 < 1024 := by omega
  have hc36 : rest.length + 36 < 1024 := by omega
  have hc37 : rest.length + 37 < 1024 := by omega
  have hc38 : rest.length + 38 < 1024 := by omega
  have hc39 : rest.length + 39 < 1024 := by omega
  have hc40 : rest.length + 40 < 1024 := by omega
  have hc41 : rest.length + 41 < 1024 := by omega
  have ha1600 : (1600 : UInt256).toNat = 1600 := rfl
  have hf1600 := HistoricalSearch.CRTMemoryBounds.activeWords_fix s 1600 32 (by decide) (by norm_num) hact
  have ha2112 : (2112 : UInt256).toNat = 2112 := rfl
  have hf2112 := HistoricalSearch.CRTMemoryBounds.activeWords_fix s 2112 32 (by decide) (by norm_num) hact
  simp [hz, hzn, exitpart11Program, exitpart11Model, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, Challenge.EvmProof.Word.literal_eq_ofNat, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8, hc9, hc10, hc11, hc12, hc13, hc14, hc15, hc16, hc17, hc18, hc19, hc20, hc21, hc22, hc23, hc24, hc25, hc26, hc27, hc28, hc29, hc30, hc31, hc32, hc33, hc34, hc35, hc36, hc37, hc38, hc39, hc40, hc41, ha1600, hf1600, ha2112, hf2112]

#print axioms exitpart11_run

def exitpart12Program : List Instr :=
  [.push 2 1024,
   .op .MLOAD,
   .push 1 160,
   .op .SHL,
   .push 2 992,
   .op .MLOAD,
   .push 1 84,
   .op .SHR]

def exitpart12Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 : UInt256) (rest : List UInt256) : State :=
  let v0 : UInt256 := MachineState.readWord s.memory 1024
  let v1 : UInt256 := UInt256.shiftLeft v0 (UInt256.ofNat 160)
  let v2 : UInt256 := MachineState.readWord s.memory 992
  let v3 : UInt256 := UInt256.shiftRight v2 (UInt256.ofNat 84)
  {s with pc := UInt256.ofNat 8958, memory := s.memory, stack := v3 :: v1 :: x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: rest}

theorem exitpart12_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 982) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions exitpart12Program {s with pc := UInt256.ofNat 8944, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: rest} =
      some (exitpart12Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 rest) := by
  have hz : ({val := 0} : UInt256) = UInt256.ofNat 0 := rfl
  have hzn : ({val := 0} : UInt256).toNat = 0 := rfl
  have hc0 : rest.length + 0 < 1024 := by omega
  have hc1 : rest.length + 1 < 1024 := by omega
  have hc2 : rest.length + 2 < 1024 := by omega
  have hc3 : rest.length + 3 < 1024 := by omega
  have hc4 : rest.length + 4 < 1024 := by omega
  have hc5 : rest.length + 5 < 1024 := by omega
  have hc6 : rest.length + 6 < 1024 := by omega
  have hc7 : rest.length + 7 < 1024 := by omega
  have hc8 : rest.length + 8 < 1024 := by omega
  have hc9 : rest.length + 9 < 1024 := by omega
  have hc10 : rest.length + 10 < 1024 := by omega
  have hc11 : rest.length + 11 < 1024 := by omega
  have hc12 : rest.length + 12 < 1024 := by omega
  have hc13 : rest.length + 13 < 1024 := by omega
  have hc14 : rest.length + 14 < 1024 := by omega
  have hc15 : rest.length + 15 < 1024 := by omega
  have hc16 : rest.length + 16 < 1024 := by omega
  have hc17 : rest.length + 17 < 1024 := by omega
  have hc18 : rest.length + 18 < 1024 := by omega
  have hc19 : rest.length + 19 < 1024 := by omega
  have hc20 : rest.length + 20 < 1024 := by omega
  have hc21 : rest.length + 21 < 1024 := by omega
  have hc22 : rest.length + 22 < 1024 := by omega
  have hc23 : rest.length + 23 < 1024 := by omega
  have hc24 : rest.length + 24 < 1024 := by omega
  have hc25 : rest.length + 25 < 1024 := by omega
  have hc26 : rest.length + 26 < 1024 := by omega
  have hc27 : rest.length + 27 < 1024 := by omega
  have hc28 : rest.length + 28 < 1024 := by omega
  have hc29 : rest.length + 29 < 1024 := by omega
  have hc30 : rest.length + 30 < 1024 := by omega
  have hc31 : rest.length + 31 < 1024 := by omega
  have hc32 : rest.length + 32 < 1024 := by omega
  have hc33 : rest.length + 33 < 1024 := by omega
  have hc34 : rest.length + 34 < 1024 := by omega
  have hc35 : rest.length + 35 < 1024 := by omega
  have hc36 : rest.length + 36 < 1024 := by omega
  have hc37 : rest.length + 37 < 1024 := by omega
  have hc38 : rest.length + 38 < 1024 := by omega
  have hc39 : rest.length + 39 < 1024 := by omega
  have hc40 : rest.length + 40 < 1024 := by omega
  have hc41 : rest.length + 41 < 1024 := by omega
  have ha1024 : (1024 : UInt256).toNat = 1024 := rfl
  have hf1024 := HistoricalSearch.CRTMemoryBounds.activeWords_fix s 1024 32 (by decide) (by norm_num) hact
  have ha992 : (992 : UInt256).toNat = 992 := rfl
  have hf992 := HistoricalSearch.CRTMemoryBounds.activeWords_fix s 992 32 (by decide) (by norm_num) hact
  simp [hz, hzn, exitpart12Program, exitpart12Model, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, Challenge.EvmProof.Word.literal_eq_ofNat, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8, hc9, hc10, hc11, hc12, hc13, hc14, hc15, hc16, hc17, hc18, hc19, hc20, hc21, hc22, hc23, hc24, hc25, hc26, hc27, hc28, hc29, hc30, hc31, hc32, hc33, hc34, hc35, hc36, hc37, hc38, hc39, hc40, hc41, ha1024, hf1024, ha992, hf992]

#print axioms exitpart12_run

def exitpart13Program : List Instr :=
  [.op .OR,
   .op (.Swap ⟨13, by decide⟩),
   .op .POP,
   .push 2 1728,
   .op .MLOAD,
   .op (.Swap ⟨14, by decide⟩),
   .op .POP]

def exitpart13Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 : UInt256) (rest : List UInt256) : State :=
  let v0 : UInt256 := UInt256.lor x0 x1
  let v1 : UInt256 := MachineState.readWord s.memory 1728
  {s with pc := UInt256.ofNat 8967, memory := s.memory, stack := x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: v0 :: v1 :: x17 :: rest}

theorem exitpart13_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 982) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions exitpart13Program {s with pc := UInt256.ofNat 8958, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: rest} =
      some (exitpart13Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 rest) := by
  have hz : ({val := 0} : UInt256) = UInt256.ofNat 0 := rfl
  have hzn : ({val := 0} : UInt256).toNat = 0 := rfl
  have hc0 : rest.length + 0 < 1024 := by omega
  have hc1 : rest.length + 1 < 1024 := by omega
  have hc2 : rest.length + 2 < 1024 := by omega
  have hc3 : rest.length + 3 < 1024 := by omega
  have hc4 : rest.length + 4 < 1024 := by omega
  have hc5 : rest.length + 5 < 1024 := by omega
  have hc6 : rest.length + 6 < 1024 := by omega
  have hc7 : rest.length + 7 < 1024 := by omega
  have hc8 : rest.length + 8 < 1024 := by omega
  have hc9 : rest.length + 9 < 1024 := by omega
  have hc10 : rest.length + 10 < 1024 := by omega
  have hc11 : rest.length + 11 < 1024 := by omega
  have hc12 : rest.length + 12 < 1024 := by omega
  have hc13 : rest.length + 13 < 1024 := by omega
  have hc14 : rest.length + 14 < 1024 := by omega
  have hc15 : rest.length + 15 < 1024 := by omega
  have hc16 : rest.length + 16 < 1024 := by omega
  have hc17 : rest.length + 17 < 1024 := by omega
  have hc18 : rest.length + 18 < 1024 := by omega
  have hc19 : rest.length + 19 < 1024 := by omega
  have hc20 : rest.length + 20 < 1024 := by omega
  have hc21 : rest.length + 21 < 1024 := by omega
  have hc22 : rest.length + 22 < 1024 := by omega
  have hc23 : rest.length + 23 < 1024 := by omega
  have hc24 : rest.length + 24 < 1024 := by omega
  have hc25 : rest.length + 25 < 1024 := by omega
  have hc26 : rest.length + 26 < 1024 := by omega
  have hc27 : rest.length + 27 < 1024 := by omega
  have hc28 : rest.length + 28 < 1024 := by omega
  have hc29 : rest.length + 29 < 1024 := by omega
  have hc30 : rest.length + 30 < 1024 := by omega
  have hc31 : rest.length + 31 < 1024 := by omega
  have hc32 : rest.length + 32 < 1024 := by omega
  have hc33 : rest.length + 33 < 1024 := by omega
  have hc34 : rest.length + 34 < 1024 := by omega
  have hc35 : rest.length + 35 < 1024 := by omega
  have hc36 : rest.length + 36 < 1024 := by omega
  have hc37 : rest.length + 37 < 1024 := by omega
  have hc38 : rest.length + 38 < 1024 := by omega
  have hc39 : rest.length + 39 < 1024 := by omega
  have hc40 : rest.length + 40 < 1024 := by omega
  have hc41 : rest.length + 41 < 1024 := by omega
  have ha1728 : (1728 : UInt256).toNat = 1728 := rfl
  have hf1728 := HistoricalSearch.CRTMemoryBounds.activeWords_fix s 1728 32 (by decide) (by norm_num) hact
  simp [hz, hzn, exitpart13Program, exitpart13Model, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, Challenge.EvmProof.Word.literal_eq_ofNat, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8, hc9, hc10, hc11, hc12, hc13, hc14, hc15, hc16, hc17, hc18, hc19, hc20, hc21, hc22, hc23, hc24, hc25, hc26, hc27, hc28, hc29, hc30, hc31, hc32, hc33, hc34, hc35, hc36, hc37, hc38, hc39, hc40, hc41, ha1728, hf1728]

#print axioms exitpart13_run

def exitpart14Program : List Instr :=
  [.push 2 1760,
   .op .MLOAD,
   .op (.Swap ⟨12, by decide⟩),
   .op .POP,
   .push 2 3942]

def exitpart14Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 : UInt256) (rest : List UInt256) : State :=
  let v0 : UInt256 := MachineState.readWord s.memory 1760
  {s with pc := UInt256.ofNat 8976, memory := s.memory, stack := (UInt256.ofNat 3942) :: x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: v0 :: x13 :: x14 :: x15 :: rest}

theorem exitpart14_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 982) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions exitpart14Program {s with pc := UInt256.ofNat 8967, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: rest} =
      some (exitpart14Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 rest) := by
  have hz : ({val := 0} : UInt256) = UInt256.ofNat 0 := rfl
  have hzn : ({val := 0} : UInt256).toNat = 0 := rfl
  have hc0 : rest.length + 0 < 1024 := by omega
  have hc1 : rest.length + 1 < 1024 := by omega
  have hc2 : rest.length + 2 < 1024 := by omega
  have hc3 : rest.length + 3 < 1024 := by omega
  have hc4 : rest.length + 4 < 1024 := by omega
  have hc5 : rest.length + 5 < 1024 := by omega
  have hc6 : rest.length + 6 < 1024 := by omega
  have hc7 : rest.length + 7 < 1024 := by omega
  have hc8 : rest.length + 8 < 1024 := by omega
  have hc9 : rest.length + 9 < 1024 := by omega
  have hc10 : rest.length + 10 < 1024 := by omega
  have hc11 : rest.length + 11 < 1024 := by omega
  have hc12 : rest.length + 12 < 1024 := by omega
  have hc13 : rest.length + 13 < 1024 := by omega
  have hc14 : rest.length + 14 < 1024 := by omega
  have hc15 : rest.length + 15 < 1024 := by omega
  have hc16 : rest.length + 16 < 1024 := by omega
  have hc17 : rest.length + 17 < 1024 := by omega
  have hc18 : rest.length + 18 < 1024 := by omega
  have hc19 : rest.length + 19 < 1024 := by omega
  have hc20 : rest.length + 20 < 1024 := by omega
  have hc21 : rest.length + 21 < 1024 := by omega
  have hc22 : rest.length + 22 < 1024 := by omega
  have hc23 : rest.length + 23 < 1024 := by omega
  have hc24 : rest.length + 24 < 1024 := by omega
  have hc25 : rest.length + 25 < 1024 := by omega
  have hc26 : rest.length + 26 < 1024 := by omega
  have hc27 : rest.length + 27 < 1024 := by omega
  have hc28 : rest.length + 28 < 1024 := by omega
  have hc29 : rest.length + 29 < 1024 := by omega
  have hc30 : rest.length + 30 < 1024 := by omega
  have hc31 : rest.length + 31 < 1024 := by omega
  have hc32 : rest.length + 32 < 1024 := by omega
  have hc33 : rest.length + 33 < 1024 := by omega
  have hc34 : rest.length + 34 < 1024 := by omega
  have hc35 : rest.length + 35 < 1024 := by omega
  have hc36 : rest.length + 36 < 1024 := by omega
  have hc37 : rest.length + 37 < 1024 := by omega
  have hc38 : rest.length + 38 < 1024 := by omega
  have hc39 : rest.length + 39 < 1024 := by omega
  have hc40 : rest.length + 40 < 1024 := by omega
  have hc41 : rest.length + 41 < 1024 := by omega
  have ha1760 : (1760 : UInt256).toNat = 1760 := rfl
  have hf1760 := HistoricalSearch.CRTMemoryBounds.activeWords_fix s 1760 32 (by decide) (by norm_num) hact
  simp [hz, hzn, exitpart14Program, exitpart14Model, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, Challenge.EvmProof.Word.literal_eq_ofNat, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8, hc9, hc10, hc11, hc12, hc13, hc14, hc15, hc16, hc17, hc18, hc19, hc20, hc21, hc22, hc23, hc24, hc25, hc26, hc27, hc28, hc29, hc30, hc31, hc32, hc33, hc34, hc35, hc36, hc37, hc38, hc39, hc40, hc41, ha1760, hf1760]

#print axioms exitpart14_run

def exitProgram : List Instr :=
  [.op .JUMPDEST,
   .op .POP,
   .op .POP,
   .op .POP,
   .op .POP,
   .op .POP,
   .op .POP,
   .op .POP,
   .op .POP,
   .op .POP,
   .op .POP,
   .op .POP,
   .op .POP,
   .push 2 1568,
   .op .MLOAD,
   .push 2 1536,
   .op .MLOAD,
   .push 2 1504,
   .op .MLOAD,
   .push 2 1472,
   .op .MLOAD,
   .push 2 1440,
   .op .MLOAD,
   .push 2 1408,
   .op .MLOAD,
   .push 2 1376,
   .op .MLOAD,
   .push 2 1344,
   .op .MLOAD,
   .push 1 96,
   .op .SHR,
   .op (.Dup ⟨1, by decide⟩),
   .push 1 148,
   .op .SHL,
   .op .OR,
   .push 2 2336,
   .op .MSTORE,
   .push 1 108,
   .op .SHR,
   .op (.Dup ⟨1, by decide⟩),
   .push 1 136,
   .op .SHL,
   .op .OR,
   .push 2 2304,
   .op .MSTORE,
   .push 1 120,
   .op .SHR,
   .op (.Dup ⟨1, by decide⟩),
   .push 1 124,
   .op .SHL,
   .op .OR,
   .push 2 2272,
   .op .MSTORE,
   .push 1 132,
   .op .SHR,
   .op (.Dup ⟨1, by decide⟩),
   .push 1 112,
   .op .SHL,
   .op .OR,
   .push 2 2240,
   .op .MSTORE,
   .push 1 144,
   .op .SHR,
   .op (.Dup ⟨1, by decide⟩),
   .push 1 100,
   .op .SHL,
   .op .OR,
   .push 2 2208,
   .op .MSTORE,
   .push 1 156,
   .op .SHR,
   .op (.Dup ⟨1, by decide⟩),
   .push 1 88,
   .op .SHL,
   .op .OR,
   .push 2 2176,
   .op .MSTORE,
   .push 1 168,
   .op .SHR,
   .op (.Dup ⟨1, by decide⟩),
   .push 1 76,
   .op .SHL,
   .op .OR,
   .push 2 2144,
   .op .MSTORE,
   .push 1 180,
   .op .SHR,
   .push 2 1600,
   .op .MLOAD,
   .push 1 64,
   .op .SHL,
   .op .OR,
   .push 2 2112,
   .op .MSTORE,
   .push 2 1024,
   .op .MLOAD,
   .push 1 160,
   .op .SHL,
   .push 2 992,
   .op .MLOAD,
   .push 1 84,
   .op .SHR,
   .op .OR,
   .op (.Swap ⟨13, by decide⟩),
   .op .POP,
   .push 2 1728,
   .op .MLOAD,
   .op (.Swap ⟨14, by decide⟩),
   .op .POP,
   .push 2 1760,
   .op .MLOAD,
   .op (.Swap ⟨12, by decide⟩),
   .op .POP,
   .push 2 3942]

def exitModel (s : State) (P n0 n1 n2 n3 n4 n5 n6 n7 n8 mask minv pbi hd w3 ent m32 allones m128 m64 m0 tl m96 inv tn aprev counter ret : UInt256) (rest : List UInt256) : State :=
  let v0 : UInt256 := MachineState.readWord s.memory 1568
  let v1 : UInt256 := MachineState.readWord s.memory 1536
  let v2 : UInt256 := MachineState.readWord s.memory 1504
  let v3 : UInt256 := MachineState.readWord s.memory 1472
  let v4 : UInt256 := MachineState.readWord s.memory 1440
  let v5 : UInt256 := MachineState.readWord s.memory 1408
  let v6 : UInt256 := MachineState.readWord s.memory 1376
  let v7 : UInt256 := MachineState.readWord s.memory 1344
  let v8 : UInt256 := UInt256.shiftRight v7 (UInt256.ofNat 96)
  let v9 : UInt256 := UInt256.shiftLeft v6 (UInt256.ofNat 148)
  let v10 : UInt256 := UInt256.lor v9 v8
  let v11 : ByteArray := MachineState.writeBytes s.memory (Data.Bytes.natToBytesPadded v10.toNat 32) 2336
  let v12 : UInt256 := UInt256.shiftRight v6 (UInt256.ofNat 108)
  let v13 : UInt256 := UInt256.shiftLeft v5 (UInt256.ofNat 136)
  let v14 : UInt256 := UInt256.lor v13 v12
  let v15 : ByteArray := MachineState.writeBytes v11 (Data.Bytes.natToBytesPadded v14.toNat 32) 2304
  let v16 : UInt256 := UInt256.shiftRight v5 (UInt256.ofNat 120)
  let v17 : UInt256 := UInt256.shiftLeft v4 (UInt256.ofNat 124)
  let v18 : UInt256 := UInt256.lor v17 v16
  let v19 : ByteArray := MachineState.writeBytes v15 (Data.Bytes.natToBytesPadded v18.toNat 32) 2272
  let v20 : UInt256 := UInt256.shiftRight v4 (UInt256.ofNat 132)
  let v21 : UInt256 := UInt256.shiftLeft v3 (UInt256.ofNat 112)
  let v22 : UInt256 := UInt256.lor v21 v20
  let v23 : ByteArray := MachineState.writeBytes v19 (Data.Bytes.natToBytesPadded v22.toNat 32) 2240
  let v24 : UInt256 := UInt256.shiftRight v3 (UInt256.ofNat 144)
  let v25 : UInt256 := UInt256.shiftLeft v2 (UInt256.ofNat 100)
  let v26 : UInt256 := UInt256.lor v25 v24
  let v27 : ByteArray := MachineState.writeBytes v23 (Data.Bytes.natToBytesPadded v26.toNat 32) 2208
  let v28 : UInt256 := UInt256.shiftRight v2 (UInt256.ofNat 156)
  let v29 : UInt256 := UInt256.shiftLeft v1 (UInt256.ofNat 88)
  let v30 : UInt256 := UInt256.lor v29 v28
  let v31 : ByteArray := MachineState.writeBytes v27 (Data.Bytes.natToBytesPadded v30.toNat 32) 2176
  let v32 : UInt256 := UInt256.shiftRight v1 (UInt256.ofNat 168)
  let v33 : UInt256 := UInt256.shiftLeft v0 (UInt256.ofNat 76)
  let v34 : UInt256 := UInt256.lor v33 v32
  let v35 : ByteArray := MachineState.writeBytes v31 (Data.Bytes.natToBytesPadded v34.toNat 32) 2144
  let v36 : UInt256 := UInt256.shiftRight v0 (UInt256.ofNat 180)
  let v37 : UInt256 := MachineState.readWord v35 1600
  let v38 : UInt256 := UInt256.shiftLeft v37 (UInt256.ofNat 64)
  let v39 : UInt256 := UInt256.lor v38 v36
  let v40 : ByteArray := MachineState.writeBytes v35 (Data.Bytes.natToBytesPadded v39.toNat 32) 2112
  let v41 : UInt256 := MachineState.readWord v40 1024
  let v42 : UInt256 := UInt256.shiftLeft v41 (UInt256.ofNat 160)
  let v43 : UInt256 := MachineState.readWord v40 992
  let v44 : UInt256 := UInt256.shiftRight v43 (UInt256.ofNat 84)
  let v45 : UInt256 := UInt256.lor v44 v42
  let v46 : UInt256 := MachineState.readWord v40 1728
  let v47 : UInt256 := MachineState.readWord v40 1760
  {s with pc := UInt256.ofNat 8976, memory := v40, stack := (UInt256.ofNat 3942) :: pbi :: hd :: w3 :: ent :: m32 :: allones :: m128 :: m64 :: m0 :: tl :: m96 :: inv :: v47 :: v45 :: v46 :: ret :: rest}

theorem exit_run (s : State) (P n0 n1 n2 n3 n4 n5 n6 n7 n8 mask minv pbi hd w3 ent m32 allones m128 m64 m0 tl m96 inv tn aprev counter ret : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 982) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions exitProgram {s with pc := UInt256.ofNat 8800, stack := P :: n0 :: n1 :: n2 :: n3 :: n4 :: n5 :: n6 :: n7 :: n8 :: mask :: minv :: pbi :: hd :: w3 :: ent :: m32 :: allones :: m128 :: m64 :: m0 :: tl :: m96 :: inv :: tn :: aprev :: counter :: ret :: rest} =
      some (exitModel s P n0 n1 n2 n3 n4 n5 n6 n7 n8 mask minv pbi hd w3 ent m32 allones m128 m64 m0 tl m96 inv tn aprev counter ret rest) := by
  let v0 : UInt256 := MachineState.readWord s.memory 1568
  let v1 : UInt256 := MachineState.readWord s.memory 1536
  let v2 : UInt256 := MachineState.readWord s.memory 1504
  let v3 : UInt256 := MachineState.readWord s.memory 1472
  let v4 : UInt256 := MachineState.readWord s.memory 1440
  let v5 : UInt256 := MachineState.readWord s.memory 1408
  let v6 : UInt256 := MachineState.readWord s.memory 1376
  let v7 : UInt256 := MachineState.readWord s.memory 1344
  let v8 : UInt256 := UInt256.shiftRight v7 (UInt256.ofNat 96)
  let v9 : UInt256 := UInt256.shiftLeft v6 (UInt256.ofNat 148)
  let v10 : UInt256 := UInt256.lor v9 v8
  let v11 : ByteArray := MachineState.writeBytes s.memory (Data.Bytes.natToBytesPadded v10.toNat 32) 2336
  let v12 : UInt256 := UInt256.shiftRight v6 (UInt256.ofNat 108)
  let v13 : UInt256 := UInt256.shiftLeft v5 (UInt256.ofNat 136)
  let v14 : UInt256 := UInt256.lor v13 v12
  let v15 : ByteArray := MachineState.writeBytes v11 (Data.Bytes.natToBytesPadded v14.toNat 32) 2304
  let v16 : UInt256 := UInt256.shiftRight v5 (UInt256.ofNat 120)
  let v17 : UInt256 := UInt256.shiftLeft v4 (UInt256.ofNat 124)
  let v18 : UInt256 := UInt256.lor v17 v16
  let v19 : ByteArray := MachineState.writeBytes v15 (Data.Bytes.natToBytesPadded v18.toNat 32) 2272
  let v20 : UInt256 := UInt256.shiftRight v4 (UInt256.ofNat 132)
  let v21 : UInt256 := UInt256.shiftLeft v3 (UInt256.ofNat 112)
  let v22 : UInt256 := UInt256.lor v21 v20
  let v23 : ByteArray := MachineState.writeBytes v19 (Data.Bytes.natToBytesPadded v22.toNat 32) 2240
  let v24 : UInt256 := UInt256.shiftRight v3 (UInt256.ofNat 144)
  let v25 : UInt256 := UInt256.shiftLeft v2 (UInt256.ofNat 100)
  let v26 : UInt256 := UInt256.lor v25 v24
  let v27 : ByteArray := MachineState.writeBytes v23 (Data.Bytes.natToBytesPadded v26.toNat 32) 2208
  let v28 : UInt256 := UInt256.shiftRight v2 (UInt256.ofNat 156)
  let v29 : UInt256 := UInt256.shiftLeft v1 (UInt256.ofNat 88)
  let v30 : UInt256 := UInt256.lor v29 v28
  let v31 : ByteArray := MachineState.writeBytes v27 (Data.Bytes.natToBytesPadded v30.toNat 32) 2176
  let v32 : UInt256 := UInt256.shiftRight v1 (UInt256.ofNat 168)
  let v33 : UInt256 := UInt256.shiftLeft v0 (UInt256.ofNat 76)
  let v34 : UInt256 := UInt256.lor v33 v32
  let v35 : ByteArray := MachineState.writeBytes v31 (Data.Bytes.natToBytesPadded v34.toNat 32) 2144
  let v36 : UInt256 := UInt256.shiftRight v0 (UInt256.ofNat 180)
  let v37 : UInt256 := MachineState.readWord v35 1600
  let v38 : UInt256 := UInt256.shiftLeft v37 (UInt256.ofNat 64)
  let v39 : UInt256 := UInt256.lor v38 v36
  let v40 : ByteArray := MachineState.writeBytes v35 (Data.Bytes.natToBytesPadded v39.toNat 32) 2112
  let v41 : UInt256 := MachineState.readWord v40 1024
  let v42 : UInt256 := UInt256.shiftLeft v41 (UInt256.ofNat 160)
  let v43 : UInt256 := MachineState.readWord v40 992
  let v44 : UInt256 := UInt256.shiftRight v43 (UInt256.ofNat 84)
  let v45 : UInt256 := UInt256.lor v44 v42
  let v46 : UInt256 := MachineState.readWord v40 1728
  let v47 : UInt256 := MachineState.readWord v40 1760
  have h0 : runInstructions exitpart0Program {s with pc := UInt256.ofNat 8800, memory := s.memory, stack := P :: n0 :: n1 :: n2 :: n3 :: n4 :: n5 :: n6 :: n7 :: n8 :: mask :: minv :: pbi :: hd :: w3 :: ent :: m32 :: allones :: m128 :: m64 :: m0 :: tl :: m96 :: inv :: tn :: aprev :: counter :: ret :: rest} = some {s with pc := UInt256.ofNat 8808, memory := s.memory, stack := n6 :: n7 :: n8 :: mask :: minv :: pbi :: hd :: w3 :: ent :: m32 :: allones :: m128 :: m64 :: m0 :: tl :: m96 :: inv :: tn :: aprev :: counter :: ret :: rest} := by
    simpa only [exitpart0Model] using exitpart0_run (s) (P) (n0) (n1) (n2) (n3) (n4) (n5) (n6) (n7) (n8) (mask) (minv) (pbi) (hd) (w3) (ent) (m32) (allones) (m128) (m64) (m0) (tl) (m96) (inv) (tn) (aprev) (counter) (ret) rest hcap hact
  have h1 : runInstructions exitpart1Program {s with pc := UInt256.ofNat 8808, memory := s.memory, stack := n6 :: n7 :: n8 :: mask :: minv :: pbi :: hd :: w3 :: ent :: m32 :: allones :: m128 :: m64 :: m0 :: tl :: m96 :: inv :: tn :: aprev :: counter :: ret :: rest} = some {s with pc := UInt256.ofNat 8817, memory := s.memory, stack := v0 :: pbi :: hd :: w3 :: ent :: m32 :: allones :: m128 :: m64 :: m0 :: tl :: m96 :: inv :: tn :: aprev :: counter :: ret :: rest} := by
    simpa only [exitpart1Model, v0] using exitpart1_run (s) (n6) (n7) (n8) (mask) (minv) (pbi) (hd) (w3) (ent) (m32) (allones) (m128) (m64) (m0) (tl) (m96) (inv) (tn) (aprev) (counter) (ret) rest hcap hact
  have h2 : runInstructions exitpart2Program {s with pc := UInt256.ofNat 8817, memory := s.memory, stack := v0 :: pbi :: hd :: w3 :: ent :: m32 :: allones :: m128 :: m64 :: m0 :: tl :: m96 :: inv :: tn :: aprev :: counter :: ret :: rest} = some {s with pc := UInt256.ofNat 8833, memory := s.memory, stack := v4 :: v3 :: v2 :: v1 :: v0 :: pbi :: hd :: w3 :: ent :: m32 :: allones :: m128 :: m64 :: m0 :: tl :: m96 :: inv :: tn :: aprev :: counter :: ret :: rest} := by
    simpa only [exitpart2Model, v1, v2, v3, v4] using exitpart2_run (s) (v0) (pbi) (hd) (w3) (ent) (m32) (allones) (m128) (m64) (m0) (tl) (m96) (inv) (tn) (aprev) (counter) (ret) rest hcap hact
  have h3 : runInstructions exitpart3Program {s with pc := UInt256.ofNat 8833, memory := s.memory, stack := v4 :: v3 :: v2 :: v1 :: v0 :: pbi :: hd :: w3 :: ent :: m32 :: allones :: m128 :: m64 :: m0 :: tl :: m96 :: inv :: tn :: aprev :: counter :: ret :: rest} = some {s with pc := UInt256.ofNat 8848, memory := s.memory, stack := v8 :: v6 :: v5 :: v4 :: v3 :: v2 :: v1 :: v0 :: pbi :: hd :: w3 :: ent :: m32 :: allones :: m128 :: m64 :: m0 :: tl :: m96 :: inv :: tn :: aprev :: counter :: ret :: rest} := by
    simpa only [exitpart3Model, v5, v6, v7, v8] using exitpart3_run (s) (v4) (v3) (v2) (v1) (v0) (pbi) (hd) (w3) (ent) (m32) (allones) (m128) (m64) (m0) (tl) (m96) (inv) (tn) (aprev) (counter) (ret) rest hcap hact
  have h4 : runInstructions exitpart4Program {s with pc := UInt256.ofNat 8848, memory := s.memory, stack := v8 :: v6 :: v5 :: v4 :: v3 :: v2 :: v1 :: v0 :: pbi :: hd :: w3 :: ent :: m32 :: allones :: m128 :: m64 :: m0 :: tl :: m96 :: inv :: tn :: aprev :: counter :: ret :: rest} = some {s with pc := UInt256.ofNat 8860, memory := v11, stack := v12 :: v5 :: v4 :: v3 :: v2 :: v1 :: v0 :: pbi :: hd :: w3 :: ent :: m32 :: allones :: m128 :: m64 :: m0 :: tl :: m96 :: inv :: tn :: aprev :: counter :: ret :: rest} := by
    simpa only [exitpart4Model, v9, v10, v11, v12] using exitpart4_run (s) (v8) (v6) (v5) (v4) (v3) (v2) (v1) (v0) (pbi) (hd) (w3) (ent) (m32) (allones) (m128) (m64) (m0) (tl) (m96) (inv) (tn) (aprev) (counter) (ret) rest hcap hact
  have h5 : runInstructions exitpart5Program {s with pc := UInt256.ofNat 8860, memory := v11, stack := v12 :: v5 :: v4 :: v3 :: v2 :: v1 :: v0 :: pbi :: hd :: w3 :: ent :: m32 :: allones :: m128 :: m64 :: m0 :: tl :: m96 :: inv :: tn :: aprev :: counter :: ret :: rest} = some {s with pc := UInt256.ofNat 8872, memory := v15, stack := v16 :: v4 :: v3 :: v2 :: v1 :: v0 :: pbi :: hd :: w3 :: ent :: m32 :: allones :: m128 :: m64 :: m0 :: tl :: m96 :: inv :: tn :: aprev :: counter :: ret :: rest} := by
    simpa only [exitpart5Model, v13, v14, v15, v16] using exitpart5_run ({s with memory := v11}) (v12) (v5) (v4) (v3) (v2) (v1) (v0) (pbi) (hd) (w3) (ent) (m32) (allones) (m128) (m64) (m0) (tl) (m96) (inv) (tn) (aprev) (counter) (ret) rest hcap hact
  have h6 : runInstructions exitpart6Program {s with pc := UInt256.ofNat 8872, memory := v15, stack := v16 :: v4 :: v3 :: v2 :: v1 :: v0 :: pbi :: hd :: w3 :: ent :: m32 :: allones :: m128 :: m64 :: m0 :: tl :: m96 :: inv :: tn :: aprev :: counter :: ret :: rest} = some {s with pc := UInt256.ofNat 8884, memory := v19, stack := v20 :: v3 :: v2 :: v1 :: v0 :: pbi :: hd :: w3 :: ent :: m32 :: allones :: m128 :: m64 :: m0 :: tl :: m96 :: inv :: tn :: aprev :: counter :: ret :: rest} := by
    simpa only [exitpart6Model, v17, v18, v19, v20] using exitpart6_run ({s with memory := v15}) (v16) (v4) (v3) (v2) (v1) (v0) (pbi) (hd) (w3) (ent) (m32) (allones) (m128) (m64) (m0) (tl) (m96) (inv) (tn) (aprev) (counter) (ret) rest hcap hact
  have h7 : runInstructions exitpart7Program {s with pc := UInt256.ofNat 8884, memory := v19, stack := v20 :: v3 :: v2 :: v1 :: v0 :: pbi :: hd :: w3 :: ent :: m32 :: allones :: m128 :: m64 :: m0 :: tl :: m96 :: inv :: tn :: aprev :: counter :: ret :: rest} = some {s with pc := UInt256.ofNat 8896, memory := v23, stack := v24 :: v2 :: v1 :: v0 :: pbi :: hd :: w3 :: ent :: m32 :: allones :: m128 :: m64 :: m0 :: tl :: m96 :: inv :: tn :: aprev :: counter :: ret :: rest} := by
    simpa only [exitpart7Model, v21, v22, v23, v24] using exitpart7_run ({s with memory := v19}) (v20) (v3) (v2) (v1) (v0) (pbi) (hd) (w3) (ent) (m32) (allones) (m128) (m64) (m0) (tl) (m96) (inv) (tn) (aprev) (counter) (ret) rest hcap hact
  have h8 : runInstructions exitpart8Program {s with pc := UInt256.ofNat 8896, memory := v23, stack := v24 :: v2 :: v1 :: v0 :: pbi :: hd :: w3 :: ent :: m32 :: allones :: m128 :: m64 :: m0 :: tl :: m96 :: inv :: tn :: aprev :: counter :: ret :: rest} = some {s with pc := UInt256.ofNat 8908, memory := v27, stack := v28 :: v1 :: v0 :: pbi :: hd :: w3 :: ent :: m32 :: allones :: m128 :: m64 :: m0 :: tl :: m96 :: inv :: tn :: aprev :: counter :: ret :: rest} := by
    simpa only [exitpart8Model, v25, v26, v27, v28] using exitpart8_run ({s with memory := v23}) (v24) (v2) (v1) (v0) (pbi) (hd) (w3) (ent) (m32) (allones) (m128) (m64) (m0) (tl) (m96) (inv) (tn) (aprev) (counter) (ret) rest hcap hact
  have h9 : runInstructions exitpart9Program {s with pc := UInt256.ofNat 8908, memory := v27, stack := v28 :: v1 :: v0 :: pbi :: hd :: w3 :: ent :: m32 :: allones :: m128 :: m64 :: m0 :: tl :: m96 :: inv :: tn :: aprev :: counter :: ret :: rest} = some {s with pc := UInt256.ofNat 8920, memory := v31, stack := v32 :: v0 :: pbi :: hd :: w3 :: ent :: m32 :: allones :: m128 :: m64 :: m0 :: tl :: m96 :: inv :: tn :: aprev :: counter :: ret :: rest} := by
    simpa only [exitpart9Model, v29, v30, v31, v32] using exitpart9_run ({s with memory := v27}) (v28) (v1) (v0) (pbi) (hd) (w3) (ent) (m32) (allones) (m128) (m64) (m0) (tl) (m96) (inv) (tn) (aprev) (counter) (ret) rest hcap hact
  have h10 : runInstructions exitpart10Program {s with pc := UInt256.ofNat 8920, memory := v31, stack := v32 :: v0 :: pbi :: hd :: w3 :: ent :: m32 :: allones :: m128 :: m64 :: m0 :: tl :: m96 :: inv :: tn :: aprev :: counter :: ret :: rest} = some {s with pc := UInt256.ofNat 8932, memory := v35, stack := v36 :: pbi :: hd :: w3 :: ent :: m32 :: allones :: m128 :: m64 :: m0 :: tl :: m96 :: inv :: tn :: aprev :: counter :: ret :: rest} := by
    simpa only [exitpart10Model, v33, v34, v35, v36] using exitpart10_run ({s with memory := v31}) (v32) (v0) (pbi) (hd) (w3) (ent) (m32) (allones) (m128) (m64) (m0) (tl) (m96) (inv) (tn) (aprev) (counter) (ret) rest hcap hact
  have h11 : runInstructions exitpart11Program {s with pc := UInt256.ofNat 8932, memory := v35, stack := v36 :: pbi :: hd :: w3 :: ent :: m32 :: allones :: m128 :: m64 :: m0 :: tl :: m96 :: inv :: tn :: aprev :: counter :: ret :: rest} = some {s with pc := UInt256.ofNat 8944, memory := v40, stack := pbi :: hd :: w3 :: ent :: m32 :: allones :: m128 :: m64 :: m0 :: tl :: m96 :: inv :: tn :: aprev :: counter :: ret :: rest} := by
    simpa only [exitpart11Model, v37, v38, v39, v40] using exitpart11_run ({s with memory := v35}) (v36) (pbi) (hd) (w3) (ent) (m32) (allones) (m128) (m64) (m0) (tl) (m96) (inv) (tn) (aprev) (counter) (ret) rest hcap hact
  have h12 : runInstructions exitpart12Program {s with pc := UInt256.ofNat 8944, memory := v40, stack := pbi :: hd :: w3 :: ent :: m32 :: allones :: m128 :: m64 :: m0 :: tl :: m96 :: inv :: tn :: aprev :: counter :: ret :: rest} = some {s with pc := UInt256.ofNat 8958, memory := v40, stack := v44 :: v42 :: pbi :: hd :: w3 :: ent :: m32 :: allones :: m128 :: m64 :: m0 :: tl :: m96 :: inv :: tn :: aprev :: counter :: ret :: rest} := by
    simpa only [exitpart12Model, v41, v42, v43, v44] using exitpart12_run ({s with memory := v40}) (pbi) (hd) (w3) (ent) (m32) (allones) (m128) (m64) (m0) (tl) (m96) (inv) (tn) (aprev) (counter) (ret) rest hcap hact
  have h13 : runInstructions exitpart13Program {s with pc := UInt256.ofNat 8958, memory := v40, stack := v44 :: v42 :: pbi :: hd :: w3 :: ent :: m32 :: allones :: m128 :: m64 :: m0 :: tl :: m96 :: inv :: tn :: aprev :: counter :: ret :: rest} = some {s with pc := UInt256.ofNat 8967, memory := v40, stack := pbi :: hd :: w3 :: ent :: m32 :: allones :: m128 :: m64 :: m0 :: tl :: m96 :: inv :: tn :: v45 :: v46 :: ret :: rest} := by
    simpa only [exitpart13Model, v45, v46] using exitpart13_run ({s with memory := v40}) (v44) (v42) (pbi) (hd) (w3) (ent) (m32) (allones) (m128) (m64) (m0) (tl) (m96) (inv) (tn) (aprev) (counter) (ret) rest hcap hact
  have h14 : runInstructions exitpart14Program {s with pc := UInt256.ofNat 8967, memory := v40, stack := pbi :: hd :: w3 :: ent :: m32 :: allones :: m128 :: m64 :: m0 :: tl :: m96 :: inv :: tn :: v45 :: v46 :: ret :: rest} = some {s with pc := UInt256.ofNat 8976, memory := v40, stack := (UInt256.ofNat 3942) :: pbi :: hd :: w3 :: ent :: m32 :: allones :: m128 :: m64 :: m0 :: tl :: m96 :: inv :: v47 :: v45 :: v46 :: ret :: rest} := by
    simpa only [exitpart14Model, v47] using exitpart14_run ({s with memory := v40}) (pbi) (hd) (w3) (ent) (m32) (allones) (m128) (m64) (m0) (tl) (m96) (inv) (tn) (v45) (v46) (ret) rest hcap hact
  exact (runInstructions_append_some _ _ _ _ _ h0 (runInstructions_append_some _ _ _ _ _ h1 (runInstructions_append_some _ _ _ _ _ h2 (runInstructions_append_some _ _ _ _ _ h3 (runInstructions_append_some _ _ _ _ _ h4 (runInstructions_append_some _ _ _ _ _ h5 (runInstructions_append_some _ _ _ _ _ h6 (runInstructions_append_some _ _ _ _ _ h7 (runInstructions_append_some _ _ _ _ _ h8 (runInstructions_append_some _ _ _ _ _ h9 (runInstructions_append_some _ _ _ _ _ h10 (runInstructions_append_some _ _ _ _ _ h11 (runInstructions_append_some _ _ _ _ _ h12 (runInstructions_append_some _ _ _ _ _ h13 h14))))))))))))))

#print axioms exit_run

def kernelProgram : List Instr :=
  col0Program ++ col1Program ++ col2Program ++ col3Program ++ col4Program ++ col5Program ++ col6Program ++ col7Program ++ col8Program ++ col9Program ++ col10Program ++ col11Program ++ col12Program ++ col13Program ++ col14Program ++ col15Program ++ col16Program

def kernelModel (s : State) (P n0 n1 n2 n3 n4 n5 n6 n7 n8 mask minv : UInt256) (rest : List UInt256) : State :=
  let t0 := col0Model s P n0 n1 n2 n3 n4 n5 n6 n7 n8 mask minv rest
  let t1 := col1Model t0 (t0.stack.headD (UInt256.ofNat 0)) P n0 n1 n2 n3 n4 n5 n6 n7 n8 mask minv rest
  let t2 := col2Model t1 (t1.stack.headD (UInt256.ofNat 0)) P n0 n1 n2 n3 n4 n5 n6 n7 n8 mask minv rest
  let t3 := col3Model t2 (t2.stack.headD (UInt256.ofNat 0)) P n0 n1 n2 n3 n4 n5 n6 n7 n8 mask minv rest
  let t4 := col4Model t3 (t3.stack.headD (UInt256.ofNat 0)) P n0 n1 n2 n3 n4 n5 n6 n7 n8 mask minv rest
  let t5 := col5Model t4 (t4.stack.headD (UInt256.ofNat 0)) P n0 n1 n2 n3 n4 n5 n6 n7 n8 mask minv rest
  let t6 := col6Model t5 (t5.stack.headD (UInt256.ofNat 0)) P n0 n1 n2 n3 n4 n5 n6 n7 n8 mask minv rest
  let t7 := col7Model t6 (t6.stack.headD (UInt256.ofNat 0)) P n0 n1 n2 n3 n4 n5 n6 n7 n8 mask minv rest
  let t8 := col8Model t7 (t7.stack.headD (UInt256.ofNat 0)) P n0 n1 n2 n3 n4 n5 n6 n7 n8 mask minv rest
  let t9 := col9Model t8 (t8.stack.headD (UInt256.ofNat 0)) P n0 n1 n2 n3 n4 n5 n6 n7 n8 mask minv rest
  let t10 := col10Model t9 (t9.stack.headD (UInt256.ofNat 0)) P n0 n1 n2 n3 n4 n5 n6 n7 n8 mask minv rest
  let t11 := col11Model t10 (t10.stack.headD (UInt256.ofNat 0)) P n0 n1 n2 n3 n4 n5 n6 n7 n8 mask minv rest
  let t12 := col12Model t11 (t11.stack.headD (UInt256.ofNat 0)) P n0 n1 n2 n3 n4 n5 n6 n7 n8 mask minv rest
  let t13 := col13Model t12 (t12.stack.headD (UInt256.ofNat 0)) P n0 n1 n2 n3 n4 n5 n6 n7 n8 mask minv rest
  let t14 := col14Model t13 (t13.stack.headD (UInt256.ofNat 0)) P n0 n1 n2 n3 n4 n5 n6 n7 n8 mask minv rest
  let t15 := col15Model t14 (t14.stack.headD (UInt256.ofNat 0)) P n0 n1 n2 n3 n4 n5 n6 n7 n8 mask minv rest
  let t16 := col16Model t15 (t15.stack.headD (UInt256.ofNat 0)) P n0 n1 n2 n3 n4 n5 n6 n7 n8 mask minv rest
  t16

theorem col0_activeWords (s : State) (P n0 n1 n2 n3 n4 n5 n6 n7 n8 mask minv : UInt256) (rest : List UInt256) :
    (col0Model s P n0 n1 n2 n3 n4 n5 n6 n7 n8 mask minv rest).activeWords = s.activeWords := by rfl

theorem col0_normalize (s : State) (P n0 n1 n2 n3 n4 n5 n6 n7 n8 mask minv : UInt256) (rest : List UInt256) :
    {col0Model s P n0 n1 n2 n3 n4 n5 n6 n7 n8 mask minv rest with pc := UInt256.ofNat 5891, stack := (col0Model s P n0 n1 n2 n3 n4 n5 n6 n7 n8 mask minv rest).stack.headD (UInt256.ofNat 0) :: P :: n0 :: n1 :: n2 :: n3 :: n4 :: n5 :: n6 :: n7 :: n8 :: mask :: minv :: rest} =
      col0Model s P n0 n1 n2 n3 n4 n5 n6 n7 n8 mask minv rest := by rfl

theorem col1_activeWords (s : State) (carry P n0 n1 n2 n3 n4 n5 n6 n7 n8 mask minv : UInt256) (rest : List UInt256) :
    (col1Model s carry P n0 n1 n2 n3 n4 n5 n6 n7 n8 mask minv rest).activeWords = s.activeWords := by rfl

theorem col1_normalize (s : State) (carry P n0 n1 n2 n3 n4 n5 n6 n7 n8 mask minv : UInt256) (rest : List UInt256) :
    {col1Model s carry P n0 n1 n2 n3 n4 n5 n6 n7 n8 mask minv rest with pc := UInt256.ofNat 5941, stack := (col1Model s carry P n0 n1 n2 n3 n4 n5 n6 n7 n8 mask minv rest).stack.headD (UInt256.ofNat 0) :: P :: n0 :: n1 :: n2 :: n3 :: n4 :: n5 :: n6 :: n7 :: n8 :: mask :: minv :: rest} =
      col1Model s carry P n0 n1 n2 n3 n4 n5 n6 n7 n8 mask minv rest := by rfl

theorem col2_activeWords (s : State) (carry P n0 n1 n2 n3 n4 n5 n6 n7 n8 mask minv : UInt256) (rest : List UInt256) :
    (col2Model s carry P n0 n1 n2 n3 n4 n5 n6 n7 n8 mask minv rest).activeWords = s.activeWords := by rfl

theorem col2_normalize (s : State) (carry P n0 n1 n2 n3 n4 n5 n6 n7 n8 mask minv : UInt256) (rest : List UInt256) :
    {col2Model s carry P n0 n1 n2 n3 n4 n5 n6 n7 n8 mask minv rest with pc := UInt256.ofNat 6021, stack := (col2Model s carry P n0 n1 n2 n3 n4 n5 n6 n7 n8 mask minv rest).stack.headD (UInt256.ofNat 0) :: P :: n0 :: n1 :: n2 :: n3 :: n4 :: n5 :: n6 :: n7 :: n8 :: mask :: minv :: rest} =
      col2Model s carry P n0 n1 n2 n3 n4 n5 n6 n7 n8 mask minv rest := by rfl

theorem col3_activeWords (s : State) (carry P n0 n1 n2 n3 n4 n5 n6 n7 n8 mask minv : UInt256) (rest : List UInt256) :
    (col3Model s carry P n0 n1 n2 n3 n4 n5 n6 n7 n8 mask minv rest).activeWords = s.activeWords := by rfl

theorem col3_normalize (s : State) (carry P n0 n1 n2 n3 n4 n5 n6 n7 n8 mask minv : UInt256) (rest : List UInt256) :
    {col3Model s carry P n0 n1 n2 n3 n4 n5 n6 n7 n8 mask minv rest with pc := UInt256.ofNat 6122, stack := (col3Model s carry P n0 n1 n2 n3 n4 n5 n6 n7 n8 mask minv rest).stack.headD (UInt256.ofNat 0) :: P :: n0 :: n1 :: n2 :: n3 :: n4 :: n5 :: n6 :: n7 :: n8 :: mask :: minv :: rest} =
      col3Model s carry P n0 n1 n2 n3 n4 n5 n6 n7 n8 mask minv rest := by rfl

theorem col4_activeWords (s : State) (carry P n0 n1 n2 n3 n4 n5 n6 n7 n8 mask minv : UInt256) (rest : List UInt256) :
    (col4Model s carry P n0 n1 n2 n3 n4 n5 n6 n7 n8 mask minv rest).activeWords = s.activeWords := by rfl

theorem col4_normalize (s : State) (carry P n0 n1 n2 n3 n4 n5 n6 n7 n8 mask minv : UInt256) (rest : List UInt256) :
    {col4Model s carry P n0 n1 n2 n3 n4 n5 n6 n7 n8 mask minv rest with pc := UInt256.ofNat 6253, stack := (col4Model s carry P n0 n1 n2 n3 n4 n5 n6 n7 n8 mask minv rest).stack.headD (UInt256.ofNat 0) :: P :: n0 :: n1 :: n2 :: n3 :: n4 :: n5 :: n6 :: n7 :: n8 :: mask :: minv :: rest} =
      col4Model s carry P n0 n1 n2 n3 n4 n5 n6 n7 n8 mask minv rest := by rfl

theorem col5_activeWords (s : State) (carry P n0 n1 n2 n3 n4 n5 n6 n7 n8 mask minv : UInt256) (rest : List UInt256) :
    (col5Model s carry P n0 n1 n2 n3 n4 n5 n6 n7 n8 mask minv rest).activeWords = s.activeWords := by rfl

theorem col5_normalize (s : State) (carry P n0 n1 n2 n3 n4 n5 n6 n7 n8 mask minv : UInt256) (rest : List UInt256) :
    {col5Model s carry P n0 n1 n2 n3 n4 n5 n6 n7 n8 mask minv rest with pc := UInt256.ofNat 6405, stack := (col5Model s carry P n0 n1 n2 n3 n4 n5 n6 n7 n8 mask minv rest).stack.headD (UInt256.ofNat 0) :: P :: n0 :: n1 :: n2 :: n3 :: n4 :: n5 :: n6 :: n7 :: n8 :: mask :: minv :: rest} =
      col5Model s carry P n0 n1 n2 n3 n4 n5 n6 n7 n8 mask minv rest := by rfl

theorem col6_activeWords (s : State) (carry P n0 n1 n2 n3 n4 n5 n6 n7 n8 mask minv : UInt256) (rest : List UInt256) :
    (col6Model s carry P n0 n1 n2 n3 n4 n5 n6 n7 n8 mask minv rest).activeWords = s.activeWords := by rfl

theorem col6_normalize (s : State) (carry P n0 n1 n2 n3 n4 n5 n6 n7 n8 mask minv : UInt256) (rest : List UInt256) :
    {col6Model s carry P n0 n1 n2 n3 n4 n5 n6 n7 n8 mask minv rest with pc := UInt256.ofNat 6587, stack := (col6Model s carry P n0 n1 n2 n3 n4 n5 n6 n7 n8 mask minv rest).stack.headD (UInt256.ofNat 0) :: P :: n0 :: n1 :: n2 :: n3 :: n4 :: n5 :: n6 :: n7 :: n8 :: mask :: minv :: rest} =
      col6Model s carry P n0 n1 n2 n3 n4 n5 n6 n7 n8 mask minv rest := by rfl

theorem col7_activeWords (s : State) (carry P n0 n1 n2 n3 n4 n5 n6 n7 n8 mask minv : UInt256) (rest : List UInt256) :
    (col7Model s carry P n0 n1 n2 n3 n4 n5 n6 n7 n8 mask minv rest).activeWords = s.activeWords := by rfl

theorem col7_normalize (s : State) (carry P n0 n1 n2 n3 n4 n5 n6 n7 n8 mask minv : UInt256) (rest : List UInt256) :
    {col7Model s carry P n0 n1 n2 n3 n4 n5 n6 n7 n8 mask minv rest with pc := UInt256.ofNat 6790, stack := (col7Model s carry P n0 n1 n2 n3 n4 n5 n6 n7 n8 mask minv rest).stack.headD (UInt256.ofNat 0) :: P :: n0 :: n1 :: n2 :: n3 :: n4 :: n5 :: n6 :: n7 :: n8 :: mask :: minv :: rest} =
      col7Model s carry P n0 n1 n2 n3 n4 n5 n6 n7 n8 mask minv rest := by rfl

theorem col8_activeWords (s : State) (carry P n0 n1 n2 n3 n4 n5 n6 n7 n8 mask minv : UInt256) (rest : List UInt256) :
    (col8Model s carry P n0 n1 n2 n3 n4 n5 n6 n7 n8 mask minv rest).activeWords = s.activeWords := by rfl

theorem col8_normalize (s : State) (carry P n0 n1 n2 n3 n4 n5 n6 n7 n8 mask minv : UInt256) (rest : List UInt256) :
    {col8Model s carry P n0 n1 n2 n3 n4 n5 n6 n7 n8 mask minv rest with pc := UInt256.ofNat 7070, stack := (col8Model s carry P n0 n1 n2 n3 n4 n5 n6 n7 n8 mask minv rest).stack.headD (UInt256.ofNat 0) :: P :: n0 :: n1 :: n2 :: n3 :: n4 :: n5 :: n6 :: n7 :: n8 :: mask :: minv :: rest} =
      col8Model s carry P n0 n1 n2 n3 n4 n5 n6 n7 n8 mask minv rest := by rfl

theorem col9_activeWords (s : State) (carry P n0 n1 n2 n3 n4 n5 n6 n7 n8 mask minv : UInt256) (rest : List UInt256) :
    (col9Model s carry P n0 n1 n2 n3 n4 n5 n6 n7 n8 mask minv rest).activeWords = s.activeWords := by rfl

theorem col9_normalize (s : State) (carry P n0 n1 n2 n3 n4 n5 n6 n7 n8 mask minv : UInt256) (rest : List UInt256) :
    {col9Model s carry P n0 n1 n2 n3 n4 n5 n6 n7 n8 mask minv rest with pc := UInt256.ofNat 7293, stack := (col9Model s carry P n0 n1 n2 n3 n4 n5 n6 n7 n8 mask minv rest).stack.headD (UInt256.ofNat 0) :: P :: n0 :: n1 :: n2 :: n3 :: n4 :: n5 :: n6 :: n7 :: n8 :: mask :: minv :: rest} =
      col9Model s carry P n0 n1 n2 n3 n4 n5 n6 n7 n8 mask minv rest := by rfl

theorem col10_activeWords (s : State) (carry P n0 n1 n2 n3 n4 n5 n6 n7 n8 mask minv : UInt256) (rest : List UInt256) :
    (col10Model s carry P n0 n1 n2 n3 n4 n5 n6 n7 n8 mask minv rest).activeWords = s.activeWords := by rfl

theorem col10_normalize (s : State) (carry P n0 n1 n2 n3 n4 n5 n6 n7 n8 mask minv : UInt256) (rest : List UInt256) :
    {col10Model s carry P n0 n1 n2 n3 n4 n5 n6 n7 n8 mask minv rest with pc := UInt256.ofNat 7495, stack := (col10Model s carry P n0 n1 n2 n3 n4 n5 n6 n7 n8 mask minv rest).stack.headD (UInt256.ofNat 0) :: P :: n0 :: n1 :: n2 :: n3 :: n4 :: n5 :: n6 :: n7 :: n8 :: mask :: minv :: rest} =
      col10Model s carry P n0 n1 n2 n3 n4 n5 n6 n7 n8 mask minv rest := by rfl

theorem col11_activeWords (s : State) (carry P n0 n1 n2 n3 n4 n5 n6 n7 n8 mask minv : UInt256) (rest : List UInt256) :
    (col11Model s carry P n0 n1 n2 n3 n4 n5 n6 n7 n8 mask minv rest).activeWords = s.activeWords := by rfl

theorem col11_normalize (s : State) (carry P n0 n1 n2 n3 n4 n5 n6 n7 n8 mask minv : UInt256) (rest : List UInt256) :
    {col11Model s carry P n0 n1 n2 n3 n4 n5 n6 n7 n8 mask minv rest with pc := UInt256.ofNat 7667, stack := (col11Model s carry P n0 n1 n2 n3 n4 n5 n6 n7 n8 mask minv rest).stack.headD (UInt256.ofNat 0) :: P :: n0 :: n1 :: n2 :: n3 :: n4 :: n5 :: n6 :: n7 :: n8 :: mask :: minv :: rest} =
      col11Model s carry P n0 n1 n2 n3 n4 n5 n6 n7 n8 mask minv rest := by rfl

theorem col12_activeWords (s : State) (carry P n0 n1 n2 n3 n4 n5 n6 n7 n8 mask minv : UInt256) (rest : List UInt256) :
    (col12Model s carry P n0 n1 n2 n3 n4 n5 n6 n7 n8 mask minv rest).activeWords = s.activeWords := by rfl

theorem col12_normalize (s : State) (carry P n0 n1 n2 n3 n4 n5 n6 n7 n8 mask minv : UInt256) (rest : List UInt256) :
    {col12Model s carry P n0 n1 n2 n3 n4 n5 n6 n7 n8 mask minv rest with pc := UInt256.ofNat 7818, stack := (col12Model s carry P n0 n1 n2 n3 n4 n5 n6 n7 n8 mask minv rest).stack.headD (UInt256.ofNat 0) :: P :: n0 :: n1 :: n2 :: n3 :: n4 :: n5 :: n6 :: n7 :: n8 :: mask :: minv :: rest} =
      col12Model s carry P n0 n1 n2 n3 n4 n5 n6 n7 n8 mask minv rest := by rfl

theorem col13_activeWords (s : State) (carry P n0 n1 n2 n3 n4 n5 n6 n7 n8 mask minv : UInt256) (rest : List UInt256) :
    (col13Model s carry P n0 n1 n2 n3 n4 n5 n6 n7 n8 mask minv rest).activeWords = s.activeWords := by rfl

theorem col13_normalize (s : State) (carry P n0 n1 n2 n3 n4 n5 n6 n7 n8 mask minv : UInt256) (rest : List UInt256) :
    {col13Model s carry P n0 n1 n2 n3 n4 n5 n6 n7 n8 mask minv rest with pc := UInt256.ofNat 7939, stack := (col13Model s carry P n0 n1 n2 n3 n4 n5 n6 n7 n8 mask minv rest).stack.headD (UInt256.ofNat 0) :: P :: n0 :: n1 :: n2 :: n3 :: n4 :: n5 :: n6 :: n7 :: n8 :: mask :: minv :: rest} =
      col13Model s carry P n0 n1 n2 n3 n4 n5 n6 n7 n8 mask minv rest := by rfl

theorem col14_activeWords (s : State) (carry P n0 n1 n2 n3 n4 n5 n6 n7 n8 mask minv : UInt256) (rest : List UInt256) :
    (col14Model s carry P n0 n1 n2 n3 n4 n5 n6 n7 n8 mask minv rest).activeWords = s.activeWords := by rfl

theorem col14_normalize (s : State) (carry P n0 n1 n2 n3 n4 n5 n6 n7 n8 mask minv : UInt256) (rest : List UInt256) :
    {col14Model s carry P n0 n1 n2 n3 n4 n5 n6 n7 n8 mask minv rest with pc := UInt256.ofNat 8039, stack := (col14Model s carry P n0 n1 n2 n3 n4 n5 n6 n7 n8 mask minv rest).stack.headD (UInt256.ofNat 0) :: P :: n0 :: n1 :: n2 :: n3 :: n4 :: n5 :: n6 :: n7 :: n8 :: mask :: minv :: rest} =
      col14Model s carry P n0 n1 n2 n3 n4 n5 n6 n7 n8 mask minv rest := by rfl

theorem col15_activeWords (s : State) (carry P n0 n1 n2 n3 n4 n5 n6 n7 n8 mask minv : UInt256) (rest : List UInt256) :
    (col15Model s carry P n0 n1 n2 n3 n4 n5 n6 n7 n8 mask minv rest).activeWords = s.activeWords := by rfl

theorem col15_normalize (s : State) (carry P n0 n1 n2 n3 n4 n5 n6 n7 n8 mask minv : UInt256) (rest : List UInt256) :
    {col15Model s carry P n0 n1 n2 n3 n4 n5 n6 n7 n8 mask minv rest with pc := UInt256.ofNat 8109, stack := (col15Model s carry P n0 n1 n2 n3 n4 n5 n6 n7 n8 mask minv rest).stack.headD (UInt256.ofNat 0) :: P :: n0 :: n1 :: n2 :: n3 :: n4 :: n5 :: n6 :: n7 :: n8 :: mask :: minv :: rest} =
      col15Model s carry P n0 n1 n2 n3 n4 n5 n6 n7 n8 mask minv rest := by rfl

theorem col16_activeWords (s : State) (carry P n0 n1 n2 n3 n4 n5 n6 n7 n8 mask minv : UInt256) (rest : List UInt256) :
    (col16Model s carry P n0 n1 n2 n3 n4 n5 n6 n7 n8 mask minv rest).activeWords = s.activeWords := by rfl

theorem kernel_run (s : State) (P n0 n1 n2 n3 n4 n5 n6 n7 n8 mask minv : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 998) (hact : 88 ≤ s.activeWords.toNat)
    (hmask : mask = UInt256.ofNat (2^244-1))
    (h0 : UInt256.land mask (MachineState.readWord s.memory 224) = n0)
    (h8 : UInt256.shiftRight (MachineState.readWord s.memory 0) (UInt256.ofNat 160) = n8) :
    runInstructions kernelProgram {s with pc := UInt256.ofNat 5859, stack := P :: n0 :: n1 :: n2 :: n3 :: n4 :: n5 :: n6 :: n7 :: n8 :: mask :: minv :: rest} =
      some (kernelModel s P n0 n1 n2 n3 n4 n5 n6 n7 n8 mask minv rest) := by
  obtain ⟨t0, ht0⟩ : ∃ t : State, t = col0Model s P n0 n1 n2 n3 n4 n5 n6 n7 n8 mask minv rest := ⟨_, rfl⟩
  have hm0_0 : MachineState.readWord t0.memory 0 = MachineState.readWord s.memory 0 := by
    rw [ht0]
    exact (col0_read0 s P n0 n1 n2 n3 n4 n5 n6 n7 n8 mask minv rest)
  have hm224_0 : MachineState.readWord t0.memory 224 = MachineState.readWord s.memory 224 := by
    rw [ht0]
    exact (col0_read224 s P n0 n1 n2 n3 n4 n5 n6 n7 n8 mask minv rest)
  have hr0 : runInstructions col0Program {s with pc := UInt256.ofNat 5859, stack := P :: n0 :: n1 :: n2 :: n3 :: n4 :: n5 :: n6 :: n7 :: n8 :: mask :: minv :: rest} = some (cachedState 1 t0) := (col0_run s P n0 n1 n2 n3 n4 n5 n6 n7 n8 mask minv rest hcap hact hmask).trans (congrArg (fun st => some (cachedState 1 st)) ht0.symm)
  obtain ⟨t1, ht1⟩ : ∃ t : State, t = col1Model t0 (t0.stack.headD (UInt256.ofNat 0)) P n0 n1 n2 n3 n4 n5 n6 n7 n8 mask minv rest := ⟨_, rfl⟩
  have hs1 : {t0 with pc := UInt256.ofNat 5891, stack := (t0.stack.headD (UInt256.ofNat 0)) :: P :: n0 :: n1 :: n2 :: n3 :: n4 :: n5 :: n6 :: n7 :: n8 :: mask :: minv :: rest} = t0 := by rw [ht0]; exact col0_normalize s P n0 n1 n2 n3 n4 n5 n6 n7 n8 mask minv rest
  have he1 : t0.activeWords = s.activeWords := by rw [ht0]; exact col0_activeWords s P n0 n1 n2 n3 n4 n5 n6 n7 n8 mask minv rest
  have ha1 : 88 ≤ t0.activeWords.toNat := by rw [he1]; exact hact
  have hm0_1 : MachineState.readWord t1.memory 0 = MachineState.readWord s.memory 0 := by
    rw [ht1]
    exact (col1_read0 t0 (t0.stack.headD (UInt256.ofNat 0)) P n0 n1 n2 n3 n4 n5 n6 n7 n8 mask minv rest).trans hm0_0
  have hm224_1 : MachineState.readWord t1.memory 224 = MachineState.readWord s.memory 224 := by
    rw [ht1]
    exact (col1_read224 t0 (t0.stack.headD (UInt256.ofNat 0)) P n0 n1 n2 n3 n4 n5 n6 n7 n8 mask minv rest).trans hm224_0
  have hr1 : runInstructions col1Program (cachedState 1 t0) = some (cachedState 2 t1) :=
    (congrArg (fun st => runInstructions col1Program (cachedState 1 st)) hs1.symm).trans ((col1_run t0 (t0.stack.headD (UInt256.ofNat 0)) P n0 n1 n2 n3 n4 n5 n6 n7 n8 mask minv rest hcap ha1 hmask).trans (congrArg (fun st => some (cachedState 2 st)) ht1.symm))
  obtain ⟨t2, ht2⟩ : ∃ t : State, t = col2Model t1 (t1.stack.headD (UInt256.ofNat 0)) P n0 n1 n2 n3 n4 n5 n6 n7 n8 mask minv rest := ⟨_, rfl⟩
  have hs2 : {t1 with pc := UInt256.ofNat 5941, stack := (t1.stack.headD (UInt256.ofNat 0)) :: P :: n0 :: n1 :: n2 :: n3 :: n4 :: n5 :: n6 :: n7 :: n8 :: mask :: minv :: rest} = t1 := by rw [ht1]; exact col1_normalize t0 (t0.stack.headD (UInt256.ofNat 0)) P n0 n1 n2 n3 n4 n5 n6 n7 n8 mask minv rest
  have he2 : t1.activeWords = t0.activeWords := by rw [ht1]; exact col1_activeWords t0 (t0.stack.headD (UInt256.ofNat 0)) P n0 n1 n2 n3 n4 n5 n6 n7 n8 mask minv rest
  have ha2 : 88 ≤ t1.activeWords.toNat := by rw [he2]; exact ha1
  have hm0_2 : MachineState.readWord t2.memory 0 = MachineState.readWord s.memory 0 := by
    rw [ht2]
    exact (col2_read0 t1 (t1.stack.headD (UInt256.ofNat 0)) P n0 n1 n2 n3 n4 n5 n6 n7 n8 mask minv rest).trans hm0_1
  have hm224_2 : MachineState.readWord t2.memory 224 = MachineState.readWord s.memory 224 := by
    rw [ht2]
    exact (col2_read224 t1 (t1.stack.headD (UInt256.ofNat 0)) P n0 n1 n2 n3 n4 n5 n6 n7 n8 mask minv rest).trans hm224_1
  have hr2 : runInstructions col2Program (cachedState 2 t1) = some (cachedState 3 t2) :=
    (congrArg (fun st => runInstructions col2Program (cachedState 2 st)) hs2.symm).trans ((col2_run t1 (t1.stack.headD (UInt256.ofNat 0)) P n0 n1 n2 n3 n4 n5 n6 n7 n8 mask minv rest hcap ha2 hmask).trans (congrArg (fun st => some (cachedState 3 st)) ht2.symm))
  obtain ⟨t3, ht3⟩ : ∃ t : State, t = col3Model t2 (t2.stack.headD (UInt256.ofNat 0)) P n0 n1 n2 n3 n4 n5 n6 n7 n8 mask minv rest := ⟨_, rfl⟩
  have hs3 : {t2 with pc := UInt256.ofNat 6021, stack := (t2.stack.headD (UInt256.ofNat 0)) :: P :: n0 :: n1 :: n2 :: n3 :: n4 :: n5 :: n6 :: n7 :: n8 :: mask :: minv :: rest} = t2 := by rw [ht2]; exact col2_normalize t1 (t1.stack.headD (UInt256.ofNat 0)) P n0 n1 n2 n3 n4 n5 n6 n7 n8 mask minv rest
  have he3 : t2.activeWords = t1.activeWords := by rw [ht2]; exact col2_activeWords t1 (t1.stack.headD (UInt256.ofNat 0)) P n0 n1 n2 n3 n4 n5 n6 n7 n8 mask minv rest
  have ha3 : 88 ≤ t2.activeWords.toNat := by rw [he3]; exact ha2
  have hm0_3 : MachineState.readWord t3.memory 0 = MachineState.readWord s.memory 0 := by
    rw [ht3]
    exact (col3_read0 t2 (t2.stack.headD (UInt256.ofNat 0)) P n0 n1 n2 n3 n4 n5 n6 n7 n8 mask minv rest).trans hm0_2
  have hm224_3 : MachineState.readWord t3.memory 224 = MachineState.readWord s.memory 224 := by
    rw [ht3]
    exact (col3_read224 t2 (t2.stack.headD (UInt256.ofNat 0)) P n0 n1 n2 n3 n4 n5 n6 n7 n8 mask minv rest).trans hm224_2
  have hr3 : runInstructions col3Program (cachedState 3 t2) = some (cachedState 4 t3) :=
    (congrArg (fun st => runInstructions col3Program (cachedState 3 st)) hs3.symm).trans ((col3_run t2 (t2.stack.headD (UInt256.ofNat 0)) P n0 n1 n2 n3 n4 n5 n6 n7 n8 mask minv rest hcap ha3 hmask).trans (congrArg (fun st => some (cachedState 4 st)) ht3.symm))
  obtain ⟨t4, ht4⟩ : ∃ t : State, t = col4Model t3 (t3.stack.headD (UInt256.ofNat 0)) P n0 n1 n2 n3 n4 n5 n6 n7 n8 mask minv rest := ⟨_, rfl⟩
  have hs4 : {t3 with pc := UInt256.ofNat 6122, stack := (t3.stack.headD (UInt256.ofNat 0)) :: P :: n0 :: n1 :: n2 :: n3 :: n4 :: n5 :: n6 :: n7 :: n8 :: mask :: minv :: rest} = t3 := by rw [ht3]; exact col3_normalize t2 (t2.stack.headD (UInt256.ofNat 0)) P n0 n1 n2 n3 n4 n5 n6 n7 n8 mask minv rest
  have he4 : t3.activeWords = t2.activeWords := by rw [ht3]; exact col3_activeWords t2 (t2.stack.headD (UInt256.ofNat 0)) P n0 n1 n2 n3 n4 n5 n6 n7 n8 mask minv rest
  have ha4 : 88 ≤ t3.activeWords.toNat := by rw [he4]; exact ha3
  have hm0_4 : MachineState.readWord t4.memory 0 = MachineState.readWord s.memory 0 := by
    rw [ht4]
    exact (col4_read0 t3 (t3.stack.headD (UInt256.ofNat 0)) P n0 n1 n2 n3 n4 n5 n6 n7 n8 mask minv rest).trans hm0_3
  have hm224_4 : MachineState.readWord t4.memory 224 = MachineState.readWord s.memory 224 := by
    rw [ht4]
    exact (col4_read224 t3 (t3.stack.headD (UInt256.ofNat 0)) P n0 n1 n2 n3 n4 n5 n6 n7 n8 mask minv rest).trans hm224_3
  have hr4 : runInstructions col4Program (cachedState 4 t3) = some (cachedState 5 t4) :=
    (congrArg (fun st => runInstructions col4Program (cachedState 4 st)) hs4.symm).trans ((col4_run t3 (t3.stack.headD (UInt256.ofNat 0)) P n0 n1 n2 n3 n4 n5 n6 n7 n8 mask minv rest hcap ha4 hmask).trans (congrArg (fun st => some (cachedState 5 st)) ht4.symm))
  obtain ⟨t5, ht5⟩ : ∃ t : State, t = col5Model t4 (t4.stack.headD (UInt256.ofNat 0)) P n0 n1 n2 n3 n4 n5 n6 n7 n8 mask minv rest := ⟨_, rfl⟩
  have hs5 : {t4 with pc := UInt256.ofNat 6253, stack := (t4.stack.headD (UInt256.ofNat 0)) :: P :: n0 :: n1 :: n2 :: n3 :: n4 :: n5 :: n6 :: n7 :: n8 :: mask :: minv :: rest} = t4 := by rw [ht4]; exact col4_normalize t3 (t3.stack.headD (UInt256.ofNat 0)) P n0 n1 n2 n3 n4 n5 n6 n7 n8 mask minv rest
  have he5 : t4.activeWords = t3.activeWords := by rw [ht4]; exact col4_activeWords t3 (t3.stack.headD (UInt256.ofNat 0)) P n0 n1 n2 n3 n4 n5 n6 n7 n8 mask minv rest
  have ha5 : 88 ≤ t4.activeWords.toNat := by rw [he5]; exact ha4
  have hm0_5 : MachineState.readWord t5.memory 0 = MachineState.readWord s.memory 0 := by
    rw [ht5]
    exact (col5_read0 t4 (t4.stack.headD (UInt256.ofNat 0)) P n0 n1 n2 n3 n4 n5 n6 n7 n8 mask minv rest).trans hm0_4
  have hm224_5 : MachineState.readWord t5.memory 224 = MachineState.readWord s.memory 224 := by
    rw [ht5]
    exact (col5_read224 t4 (t4.stack.headD (UInt256.ofNat 0)) P n0 n1 n2 n3 n4 n5 n6 n7 n8 mask minv rest).trans hm224_4
  have hr5 : runInstructions col5Program (cachedState 5 t4) = some (cachedState 6 t5) :=
    (congrArg (fun st => runInstructions col5Program (cachedState 5 st)) hs5.symm).trans ((col5_run t4 (t4.stack.headD (UInt256.ofNat 0)) P n0 n1 n2 n3 n4 n5 n6 n7 n8 mask minv rest hcap ha5 hmask).trans (congrArg (fun st => some (cachedState 6 st)) ht5.symm))
  obtain ⟨t6, ht6⟩ : ∃ t : State, t = col6Model t5 (t5.stack.headD (UInt256.ofNat 0)) P n0 n1 n2 n3 n4 n5 n6 n7 n8 mask minv rest := ⟨_, rfl⟩
  have hs6 : {t5 with pc := UInt256.ofNat 6405, stack := (t5.stack.headD (UInt256.ofNat 0)) :: P :: n0 :: n1 :: n2 :: n3 :: n4 :: n5 :: n6 :: n7 :: n8 :: mask :: minv :: rest} = t5 := by rw [ht5]; exact col5_normalize t4 (t4.stack.headD (UInt256.ofNat 0)) P n0 n1 n2 n3 n4 n5 n6 n7 n8 mask minv rest
  have he6 : t5.activeWords = t4.activeWords := by rw [ht5]; exact col5_activeWords t4 (t4.stack.headD (UInt256.ofNat 0)) P n0 n1 n2 n3 n4 n5 n6 n7 n8 mask minv rest
  have ha6 : 88 ≤ t5.activeWords.toNat := by rw [he6]; exact ha5
  have hm0_6 : MachineState.readWord t6.memory 0 = MachineState.readWord s.memory 0 := by
    rw [ht6]
    exact (col6_read0 t5 (t5.stack.headD (UInt256.ofNat 0)) P n0 n1 n2 n3 n4 n5 n6 n7 n8 mask minv rest).trans hm0_5
  have hm224_6 : MachineState.readWord t6.memory 224 = MachineState.readWord s.memory 224 := by
    rw [ht6]
    exact (col6_read224 t5 (t5.stack.headD (UInt256.ofNat 0)) P n0 n1 n2 n3 n4 n5 n6 n7 n8 mask minv rest).trans hm224_5
  have hr6 : runInstructions col6Program (cachedState 6 t5) = some (cachedState 7 t6) :=
    (congrArg (fun st => runInstructions col6Program (cachedState 6 st)) hs6.symm).trans ((col6_run t5 (t5.stack.headD (UInt256.ofNat 0)) P n0 n1 n2 n3 n4 n5 n6 n7 n8 mask minv rest hcap ha6 hmask).trans (congrArg (fun st => some (cachedState 7 st)) ht6.symm))
  obtain ⟨t7, ht7⟩ : ∃ t : State, t = col7Model t6 (t6.stack.headD (UInt256.ofNat 0)) P n0 n1 n2 n3 n4 n5 n6 n7 n8 mask minv rest := ⟨_, rfl⟩
  have hs7 : {t6 with pc := UInt256.ofNat 6587, stack := (t6.stack.headD (UInt256.ofNat 0)) :: P :: n0 :: n1 :: n2 :: n3 :: n4 :: n5 :: n6 :: n7 :: n8 :: mask :: minv :: rest} = t6 := by rw [ht6]; exact col6_normalize t5 (t5.stack.headD (UInt256.ofNat 0)) P n0 n1 n2 n3 n4 n5 n6 n7 n8 mask minv rest
  have he7 : t6.activeWords = t5.activeWords := by rw [ht6]; exact col6_activeWords t5 (t5.stack.headD (UInt256.ofNat 0)) P n0 n1 n2 n3 n4 n5 n6 n7 n8 mask minv rest
  have ha7 : 88 ≤ t6.activeWords.toNat := by rw [he7]; exact ha6
  have hm0_7 : MachineState.readWord t7.memory 0 = MachineState.readWord s.memory 0 := by
    rw [ht7]
    exact (col7_read0 t6 (t6.stack.headD (UInt256.ofNat 0)) P n0 n1 n2 n3 n4 n5 n6 n7 n8 mask minv rest).trans hm0_6
  have hm224_7 : MachineState.readWord t7.memory 224 = MachineState.readWord s.memory 224 := by
    rw [ht7]
    exact (col7_read224 t6 (t6.stack.headD (UInt256.ofNat 0)) P n0 n1 n2 n3 n4 n5 n6 n7 n8 mask minv rest).trans hm224_6
  have hr7 : runInstructions col7Program (cachedState 7 t6) = some (cachedState 8 t7) :=
    (congrArg (fun st => runInstructions col7Program (cachedState 7 st)) hs7.symm).trans ((col7_run t6 (t6.stack.headD (UInt256.ofNat 0)) P n0 n1 n2 n3 n4 n5 n6 n7 n8 mask minv rest hcap ha7 hmask).trans (congrArg (fun st => some (cachedState 8 st)) ht7.symm))
  obtain ⟨t8, ht8⟩ : ∃ t : State, t = col8Model t7 (t7.stack.headD (UInt256.ofNat 0)) P n0 n1 n2 n3 n4 n5 n6 n7 n8 mask minv rest := ⟨_, rfl⟩
  have hs8 : {t7 with pc := UInt256.ofNat 6790, stack := (t7.stack.headD (UInt256.ofNat 0)) :: P :: n0 :: n1 :: n2 :: n3 :: n4 :: n5 :: n6 :: n7 :: n8 :: mask :: minv :: rest} = t7 := by rw [ht7]; exact col7_normalize t6 (t6.stack.headD (UInt256.ofNat 0)) P n0 n1 n2 n3 n4 n5 n6 n7 n8 mask minv rest
  have he8 : t7.activeWords = t6.activeWords := by rw [ht7]; exact col7_activeWords t6 (t6.stack.headD (UInt256.ofNat 0)) P n0 n1 n2 n3 n4 n5 n6 n7 n8 mask minv rest
  have ha8 : 88 ≤ t7.activeWords.toNat := by rw [he8]; exact ha7
  have hm0_8 : MachineState.readWord t8.memory 0 = MachineState.readWord s.memory 0 := by
    rw [ht8]
    exact (col8_read0 t7 (t7.stack.headD (UInt256.ofNat 0)) P n0 n1 n2 n3 n4 n5 n6 n7 n8 mask minv rest).trans hm0_7
  have hm224_8 : MachineState.readWord t8.memory 224 = MachineState.readWord s.memory 224 := by
    rw [ht8]
    exact (col8_read224 t7 (t7.stack.headD (UInt256.ofNat 0)) P n0 n1 n2 n3 n4 n5 n6 n7 n8 mask minv rest).trans hm224_7
  have hr8 : runInstructions col8Program (cachedState 8 t7) = some (cachedState 9 t8) :=
    (congrArg (fun st => runInstructions col8Program (cachedState 8 st)) hs8.symm).trans ((col8_run t7 (t7.stack.headD (UInt256.ofNat 0)) P n0 n1 n2 n3 n4 n5 n6 n7 n8 mask minv rest hcap ha8 hmask (by rw [hm0_7]; exact h8)).trans (congrArg (fun st => some (cachedState 9 st)) ht8.symm))
  obtain ⟨t9, ht9⟩ : ∃ t : State, t = col9Model t8 (t8.stack.headD (UInt256.ofNat 0)) P n0 n1 n2 n3 n4 n5 n6 n7 n8 mask minv rest := ⟨_, rfl⟩
  have hs9 : {t8 with pc := UInt256.ofNat 7070, stack := (t8.stack.headD (UInt256.ofNat 0)) :: P :: n0 :: n1 :: n2 :: n3 :: n4 :: n5 :: n6 :: n7 :: n8 :: mask :: minv :: rest} = t8 := by rw [ht8]; exact col8_normalize t7 (t7.stack.headD (UInt256.ofNat 0)) P n0 n1 n2 n3 n4 n5 n6 n7 n8 mask minv rest
  have he9 : t8.activeWords = t7.activeWords := by rw [ht8]; exact col8_activeWords t7 (t7.stack.headD (UInt256.ofNat 0)) P n0 n1 n2 n3 n4 n5 n6 n7 n8 mask minv rest
  have ha9 : 88 ≤ t8.activeWords.toNat := by rw [he9]; exact ha8
  have hm0_9 : MachineState.readWord t9.memory 0 = MachineState.readWord s.memory 0 := by
    rw [ht9]
    exact (col9_read0 t8 (t8.stack.headD (UInt256.ofNat 0)) P n0 n1 n2 n3 n4 n5 n6 n7 n8 mask minv rest).trans hm0_8
  have hm224_9 : MachineState.readWord t9.memory 224 = MachineState.readWord s.memory 224 := by
    rw [ht9]
    exact (col9_read224 t8 (t8.stack.headD (UInt256.ofNat 0)) P n0 n1 n2 n3 n4 n5 n6 n7 n8 mask minv rest).trans hm224_8
  have hr9 : runInstructions col9Program (cachedState 9 t8) = some (cachedState 10 t9) :=
    (congrArg (fun st => runInstructions col9Program (cachedState 9 st)) hs9.symm).trans ((col9_run t8 (t8.stack.headD (UInt256.ofNat 0)) P n0 n1 n2 n3 n4 n5 n6 n7 n8 mask minv rest hcap ha9 hmask).trans (congrArg (fun st => some (cachedState 10 st)) ht9.symm))
  obtain ⟨t10, ht10⟩ : ∃ t : State, t = col10Model t9 (t9.stack.headD (UInt256.ofNat 0)) P n0 n1 n2 n3 n4 n5 n6 n7 n8 mask minv rest := ⟨_, rfl⟩
  have hs10 : {t9 with pc := UInt256.ofNat 7293, stack := (t9.stack.headD (UInt256.ofNat 0)) :: P :: n0 :: n1 :: n2 :: n3 :: n4 :: n5 :: n6 :: n7 :: n8 :: mask :: minv :: rest} = t9 := by rw [ht9]; exact col9_normalize t8 (t8.stack.headD (UInt256.ofNat 0)) P n0 n1 n2 n3 n4 n5 n6 n7 n8 mask minv rest
  have he10 : t9.activeWords = t8.activeWords := by rw [ht9]; exact col9_activeWords t8 (t8.stack.headD (UInt256.ofNat 0)) P n0 n1 n2 n3 n4 n5 n6 n7 n8 mask minv rest
  have ha10 : 88 ≤ t9.activeWords.toNat := by rw [he10]; exact ha9
  have hm0_10 : MachineState.readWord t10.memory 0 = MachineState.readWord s.memory 0 := by
    rw [ht10]
    exact (col10_read0 t9 (t9.stack.headD (UInt256.ofNat 0)) P n0 n1 n2 n3 n4 n5 n6 n7 n8 mask minv rest).trans hm0_9
  have hm224_10 : MachineState.readWord t10.memory 224 = MachineState.readWord s.memory 224 := by
    rw [ht10]
    exact (col10_read224 t9 (t9.stack.headD (UInt256.ofNat 0)) P n0 n1 n2 n3 n4 n5 n6 n7 n8 mask minv rest).trans hm224_9
  have hr10 : runInstructions col10Program (cachedState 10 t9) = some (cachedState 11 t10) :=
    (congrArg (fun st => runInstructions col10Program (cachedState 10 st)) hs10.symm).trans ((col10_run t9 (t9.stack.headD (UInt256.ofNat 0)) P n0 n1 n2 n3 n4 n5 n6 n7 n8 mask minv rest hcap ha10 hmask).trans (congrArg (fun st => some (cachedState 11 st)) ht10.symm))
  obtain ⟨t11, ht11⟩ : ∃ t : State, t = col11Model t10 (t10.stack.headD (UInt256.ofNat 0)) P n0 n1 n2 n3 n4 n5 n6 n7 n8 mask minv rest := ⟨_, rfl⟩
  have hs11 : {t10 with pc := UInt256.ofNat 7495, stack := (t10.stack.headD (UInt256.ofNat 0)) :: P :: n0 :: n1 :: n2 :: n3 :: n4 :: n5 :: n6 :: n7 :: n8 :: mask :: minv :: rest} = t10 := by rw [ht10]; exact col10_normalize t9 (t9.stack.headD (UInt256.ofNat 0)) P n0 n1 n2 n3 n4 n5 n6 n7 n8 mask minv rest
  have he11 : t10.activeWords = t9.activeWords := by rw [ht10]; exact col10_activeWords t9 (t9.stack.headD (UInt256.ofNat 0)) P n0 n1 n2 n3 n4 n5 n6 n7 n8 mask minv rest
  have ha11 : 88 ≤ t10.activeWords.toNat := by rw [he11]; exact ha10
  have hm0_11 : MachineState.readWord t11.memory 0 = MachineState.readWord s.memory 0 := by
    rw [ht11]
    exact (col11_read0 t10 (t10.stack.headD (UInt256.ofNat 0)) P n0 n1 n2 n3 n4 n5 n6 n7 n8 mask minv rest).trans hm0_10
  have hm224_11 : MachineState.readWord t11.memory 224 = MachineState.readWord s.memory 224 := by
    rw [ht11]
    exact (col11_read224 t10 (t10.stack.headD (UInt256.ofNat 0)) P n0 n1 n2 n3 n4 n5 n6 n7 n8 mask minv rest).trans hm224_10
  have hr11 : runInstructions col11Program (cachedState 11 t10) = some (cachedState 12 t11) :=
    (congrArg (fun st => runInstructions col11Program (cachedState 11 st)) hs11.symm).trans ((col11_run t10 (t10.stack.headD (UInt256.ofNat 0)) P n0 n1 n2 n3 n4 n5 n6 n7 n8 mask minv rest hcap ha11 hmask).trans (congrArg (fun st => some (cachedState 12 st)) ht11.symm))
  obtain ⟨t12, ht12⟩ : ∃ t : State, t = col12Model t11 (t11.stack.headD (UInt256.ofNat 0)) P n0 n1 n2 n3 n4 n5 n6 n7 n8 mask minv rest := ⟨_, rfl⟩
  have hs12 : {t11 with pc := UInt256.ofNat 7667, stack := (t11.stack.headD (UInt256.ofNat 0)) :: P :: n0 :: n1 :: n2 :: n3 :: n4 :: n5 :: n6 :: n7 :: n8 :: mask :: minv :: rest} = t11 := by rw [ht11]; exact col11_normalize t10 (t10.stack.headD (UInt256.ofNat 0)) P n0 n1 n2 n3 n4 n5 n6 n7 n8 mask minv rest
  have he12 : t11.activeWords = t10.activeWords := by rw [ht11]; exact col11_activeWords t10 (t10.stack.headD (UInt256.ofNat 0)) P n0 n1 n2 n3 n4 n5 n6 n7 n8 mask minv rest
  have ha12 : 88 ≤ t11.activeWords.toNat := by rw [he12]; exact ha11
  have hm0_12 : MachineState.readWord t12.memory 0 = MachineState.readWord s.memory 0 := by
    rw [ht12]
    exact (col12_read0 t11 (t11.stack.headD (UInt256.ofNat 0)) P n0 n1 n2 n3 n4 n5 n6 n7 n8 mask minv rest).trans hm0_11
  have hm224_12 : MachineState.readWord t12.memory 224 = MachineState.readWord s.memory 224 := by
    rw [ht12]
    exact (col12_read224 t11 (t11.stack.headD (UInt256.ofNat 0)) P n0 n1 n2 n3 n4 n5 n6 n7 n8 mask minv rest).trans hm224_11
  have hr12 : runInstructions col12Program (cachedState 12 t11) = some (cachedState 13 t12) :=
    (congrArg (fun st => runInstructions col12Program (cachedState 12 st)) hs12.symm).trans ((col12_run t11 (t11.stack.headD (UInt256.ofNat 0)) P n0 n1 n2 n3 n4 n5 n6 n7 n8 mask minv rest hcap ha12 hmask).trans (congrArg (fun st => some (cachedState 13 st)) ht12.symm))
  obtain ⟨t13, ht13⟩ : ∃ t : State, t = col13Model t12 (t12.stack.headD (UInt256.ofNat 0)) P n0 n1 n2 n3 n4 n5 n6 n7 n8 mask minv rest := ⟨_, rfl⟩
  have hs13 : {t12 with pc := UInt256.ofNat 7818, stack := (t12.stack.headD (UInt256.ofNat 0)) :: P :: n0 :: n1 :: n2 :: n3 :: n4 :: n5 :: n6 :: n7 :: n8 :: mask :: minv :: rest} = t12 := by rw [ht12]; exact col12_normalize t11 (t11.stack.headD (UInt256.ofNat 0)) P n0 n1 n2 n3 n4 n5 n6 n7 n8 mask minv rest
  have he13 : t12.activeWords = t11.activeWords := by rw [ht12]; exact col12_activeWords t11 (t11.stack.headD (UInt256.ofNat 0)) P n0 n1 n2 n3 n4 n5 n6 n7 n8 mask minv rest
  have ha13 : 88 ≤ t12.activeWords.toNat := by rw [he13]; exact ha12
  have hm0_13 : MachineState.readWord t13.memory 0 = MachineState.readWord s.memory 0 := by
    rw [ht13]
    exact (col13_read0 t12 (t12.stack.headD (UInt256.ofNat 0)) P n0 n1 n2 n3 n4 n5 n6 n7 n8 mask minv rest).trans hm0_12
  have hm224_13 : MachineState.readWord t13.memory 224 = MachineState.readWord s.memory 224 := by
    rw [ht13]
    exact (col13_read224 t12 (t12.stack.headD (UInt256.ofNat 0)) P n0 n1 n2 n3 n4 n5 n6 n7 n8 mask minv rest).trans hm224_12
  have hr13 : runInstructions col13Program (cachedState 13 t12) = some (cachedState 14 t13) :=
    (congrArg (fun st => runInstructions col13Program (cachedState 13 st)) hs13.symm).trans ((col13_run t12 (t12.stack.headD (UInt256.ofNat 0)) P n0 n1 n2 n3 n4 n5 n6 n7 n8 mask minv rest hcap ha13 hmask).trans (congrArg (fun st => some (cachedState 14 st)) ht13.symm))
  obtain ⟨t14, ht14⟩ : ∃ t : State, t = col14Model t13 (t13.stack.headD (UInt256.ofNat 0)) P n0 n1 n2 n3 n4 n5 n6 n7 n8 mask minv rest := ⟨_, rfl⟩
  have hs14 : {t13 with pc := UInt256.ofNat 7939, stack := (t13.stack.headD (UInt256.ofNat 0)) :: P :: n0 :: n1 :: n2 :: n3 :: n4 :: n5 :: n6 :: n7 :: n8 :: mask :: minv :: rest} = t13 := by rw [ht13]; exact col13_normalize t12 (t12.stack.headD (UInt256.ofNat 0)) P n0 n1 n2 n3 n4 n5 n6 n7 n8 mask minv rest
  have he14 : t13.activeWords = t12.activeWords := by rw [ht13]; exact col13_activeWords t12 (t12.stack.headD (UInt256.ofNat 0)) P n0 n1 n2 n3 n4 n5 n6 n7 n8 mask minv rest
  have ha14 : 88 ≤ t13.activeWords.toNat := by rw [he14]; exact ha13
  have hm0_14 : MachineState.readWord t14.memory 0 = MachineState.readWord s.memory 0 := by
    rw [ht14]
    exact (col14_read0 t13 (t13.stack.headD (UInt256.ofNat 0)) P n0 n1 n2 n3 n4 n5 n6 n7 n8 mask minv rest).trans hm0_13
  have hm224_14 : MachineState.readWord t14.memory 224 = MachineState.readWord s.memory 224 := by
    rw [ht14]
    exact (col14_read224 t13 (t13.stack.headD (UInt256.ofNat 0)) P n0 n1 n2 n3 n4 n5 n6 n7 n8 mask minv rest).trans hm224_13
  have hr14 : runInstructions col14Program (cachedState 14 t13) = some (cachedState 15 t14) :=
    (congrArg (fun st => runInstructions col14Program (cachedState 14 st)) hs14.symm).trans ((col14_run t13 (t13.stack.headD (UInt256.ofNat 0)) P n0 n1 n2 n3 n4 n5 n6 n7 n8 mask minv rest hcap ha14 hmask).trans (congrArg (fun st => some (cachedState 15 st)) ht14.symm))
  obtain ⟨t15, ht15⟩ : ∃ t : State, t = col15Model t14 (t14.stack.headD (UInt256.ofNat 0)) P n0 n1 n2 n3 n4 n5 n6 n7 n8 mask minv rest := ⟨_, rfl⟩
  have hs15 : {t14 with pc := UInt256.ofNat 8039, stack := (t14.stack.headD (UInt256.ofNat 0)) :: P :: n0 :: n1 :: n2 :: n3 :: n4 :: n5 :: n6 :: n7 :: n8 :: mask :: minv :: rest} = t14 := by rw [ht14]; exact col14_normalize t13 (t13.stack.headD (UInt256.ofNat 0)) P n0 n1 n2 n3 n4 n5 n6 n7 n8 mask minv rest
  have he15 : t14.activeWords = t13.activeWords := by rw [ht14]; exact col14_activeWords t13 (t13.stack.headD (UInt256.ofNat 0)) P n0 n1 n2 n3 n4 n5 n6 n7 n8 mask minv rest
  have ha15 : 88 ≤ t14.activeWords.toNat := by rw [he15]; exact ha14
  have hm0_15 : MachineState.readWord t15.memory 0 = MachineState.readWord s.memory 0 := by
    rw [ht15]
    exact (col15_read0 t14 (t14.stack.headD (UInt256.ofNat 0)) P n0 n1 n2 n3 n4 n5 n6 n7 n8 mask minv rest).trans hm0_14
  have hm224_15 : MachineState.readWord t15.memory 224 = MachineState.readWord s.memory 224 := by
    rw [ht15]
    exact (col15_read224 t14 (t14.stack.headD (UInt256.ofNat 0)) P n0 n1 n2 n3 n4 n5 n6 n7 n8 mask minv rest).trans hm224_14
  have hr15 : runInstructions col15Program (cachedState 15 t14) = some (cachedState 16 t15) :=
    (congrArg (fun st => runInstructions col15Program (cachedState 15 st)) hs15.symm).trans ((col15_run t14 (t14.stack.headD (UInt256.ofNat 0)) P n0 n1 n2 n3 n4 n5 n6 n7 n8 mask minv rest hcap ha15 hmask).trans (congrArg (fun st => some (cachedState 16 st)) ht15.symm))
  obtain ⟨t16, ht16⟩ : ∃ t : State, t = col16Model t15 (t15.stack.headD (UInt256.ofNat 0)) P n0 n1 n2 n3 n4 n5 n6 n7 n8 mask minv rest := ⟨_, rfl⟩
  have hs16 : {t15 with pc := UInt256.ofNat 8109, stack := (t15.stack.headD (UInt256.ofNat 0)) :: P :: n0 :: n1 :: n2 :: n3 :: n4 :: n5 :: n6 :: n7 :: n8 :: mask :: minv :: rest} = t15 := by rw [ht15]; exact col15_normalize t14 (t14.stack.headD (UInt256.ofNat 0)) P n0 n1 n2 n3 n4 n5 n6 n7 n8 mask minv rest
  have he16 : t15.activeWords = t14.activeWords := by rw [ht15]; exact col15_activeWords t14 (t14.stack.headD (UInt256.ofNat 0)) P n0 n1 n2 n3 n4 n5 n6 n7 n8 mask minv rest
  have ha16 : 88 ≤ t15.activeWords.toNat := by rw [he16]; exact ha15
  have hm0_16 : MachineState.readWord t16.memory 0 = MachineState.readWord s.memory 0 := by
    rw [ht16]
    exact (col16_read0 t15 (t15.stack.headD (UInt256.ofNat 0)) P n0 n1 n2 n3 n4 n5 n6 n7 n8 mask minv rest).trans hm0_15
  have hm224_16 : MachineState.readWord t16.memory 224 = MachineState.readWord s.memory 224 := by
    rw [ht16]
    exact (col16_read224 t15 (t15.stack.headD (UInt256.ofNat 0)) P n0 n1 n2 n3 n4 n5 n6 n7 n8 mask minv rest).trans hm224_15
  have hr16 : runInstructions col16Program (cachedState 16 t15) = some (cachedState 17 t16) :=
    (congrArg (fun st => runInstructions col16Program (cachedState 16 st)) hs16.symm).trans ((col16_run t15 (t15.stack.headD (UInt256.ofNat 0)) P n0 n1 n2 n3 n4 n5 n6 n7 n8 mask minv rest hcap ha16 hmask (by rw [hm224_15]; exact h0)).trans (congrArg (fun st => some (cachedState 17 st)) ht16.symm))
  have hend : t16 = kernelModel s P n0 n1 n2 n3 n4 n5 n6 n7 n8 mask minv rest := by
    simp only [kernelModel, ← ht0, ← ht1, ← ht2, ← ht3, ← ht4, ← ht5, ← ht6, ← ht7, ← ht8, ← ht9, ← ht10, ← ht11, ← ht12, ← ht13, ← ht14, ← ht15, ← ht16]
  exact (runInstructions_append_some _ _ _ _ _ hr0 (runInstructions_append_some _ _ _ _ _ hr1 (runInstructions_append_some _ _ _ _ _ hr2 (runInstructions_append_some _ _ _ _ _ hr3 (runInstructions_append_some _ _ _ _ _ hr4 (runInstructions_append_some _ _ _ _ _ hr5 (runInstructions_append_some _ _ _ _ _ hr6 (runInstructions_append_some _ _ _ _ _ hr7 (runInstructions_append_some _ _ _ _ _ hr8 (runInstructions_append_some _ _ _ _ _ hr9 (runInstructions_append_some _ _ _ _ _ hr10 (runInstructions_append_some _ _ _ _ _ hr11 (runInstructions_append_some _ _ _ _ _ hr12 (runInstructions_append_some _ _ _ _ _ hr13 (runInstructions_append_some _ _ _ _ _ hr14 (runInstructions_append_some _ _ _ _ _ hr15 hr16)))))))))))))))).trans (congrArg some hend)

#print axioms kernel_run
end HistoricalSearch.GeneratedColumns
