import Challenge.Modexp.Submission.Proofs.Cycle.DoubleInput01
set_option warningAsError true
set_option linter.unusedVariables false
namespace CycleSubmission.Execution
open EvmSemantics EvmSemantics.EVM YulEvmCompiler
local notation "W" => UInt256
local notation "N" => UInt256.ofNat
def squareColumn0Model (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 : W) (rest : List W) : State :=
  let v0 : W := MachineState.readWord s.memory 768
  let v1 : W := v0 * v0
  let v2 : W := MachineState.readWord s.memory 2720
  let v3 : W := v2 * v1
  let v4 : W := UInt256.land w10 v3
  let v5 : W := UInt256.mulMod v0 v0 w7
  let v6 : W := UInt256.mulMod w11 v4 w7
  let v7 : W := v6 + v5
  let v8 : W := UInt256.mulMod (N 2048) v7 w7
  let v9 : W := MachineState.readWord s.memory 768
  let v10 : W := w3 * v9
  let v11 : W := v10 + v10
  let v12 : W := UInt256.mulMod w3 v9 w7
  let v13 : W := v12 + v12
  let v14 : W := v8 + v13
  let v15 : W := v8 + v11
  let v16 : W := v4 * w9
  let v17 : W := v16 + v15
  let v18 : W := UInt256.mulMod v4 w9 w7
  let v19 : W := v18 + v14
  let v20 : W := MachineState.readWord s.memory 2720
  let v21 : W := v17 * v20
  let v22 : W := UInt256.land w10 v21
  let v23 : W := UInt256.mulMod v22 w11 w7
  let v24 : W := v23 + v19
  let v25 : W := UInt256.mulMod (N 2048) v24 w7
  let v26 : W := MachineState.readWord s.memory 768
  let v27 : W := w4 * v26
  let v28 : W := v27 + v27
  let v29 : W := UInt256.mulMod w4 v26 w7
  let v30 : W := v29 + v29
  let v31 : W := v25 + v30
  let v32 : W := v25 + v28
  let v33 : W := w3 * w3
  let v34 : W := v33 + v32
  let v35 : W := v4 * w0
  let v36 : W := v35 + v34
  let v37 : W := v22 * w9
  let v38 : W := v37 + v36
  let v39 : W := UInt256.mulMod w3 w3 w7
  let v40 : W := v39 + v31
  let v41 : W := UInt256.mulMod v4 w0 w7
  let v42 : W := v41 + v40
  let v43 : W := UInt256.mulMod v22 w9 w7
  let v44 : W := v43 + v42
  {s with pc := N 5840, memory := s.memory, stack := w11 :: w7 :: v44 :: v38 :: w0 :: w1 :: w2 :: w3 :: w4 :: w5 :: v22 :: w7 :: v4 :: w9 :: w10 :: w11 :: w12 :: w13 :: rest}

def squareColumn0Program : List Instr := CycleSubmission.DoubleInput01.program0
end CycleSubmission.Execution
