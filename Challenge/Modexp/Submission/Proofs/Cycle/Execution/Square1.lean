import Challenge.Modexp.Submission.Proofs.Cycle.DoubleInput01
set_option warningAsError true
set_option linter.unusedVariables false
namespace CycleSubmission.Execution
open EvmSemantics EvmSemantics.EVM YulEvmCompiler
local notation "W" => UInt256
local notation "N" => UInt256.ofNat
def squareColumn1Model (s : State) (carry w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 : W) (rest : List W) : State :=
  let v0 : W := MachineState.readWord s.memory 2720
  let v1 : W := w2 * v0
  let v2 : W := UInt256.land w13 v1
  let v3 : ByteArray := MachineState.writeBytes s.memory (Data.Bytes.natToBytesPadded v2.toNat 32) 192
  let v4 : W := UInt256.mulMod v2 carry w0
  let v5 : W := v4 + w1
  let v6 : W := UInt256.mulMod (N 2048) v5 w0
  let v7 : W := MachineState.readWord v3 32
  let v8 : W := MachineState.readWord v3 768
  let v9 : W := v7 * v8
  let v10 : W := w6 * w7
  let v11 : W := v10 + v9
  let v12 : W := v11 + v11
  let v13 : W := UInt256.mulMod v7 v8 w10
  let v14 : W := UInt256.mulMod w6 w7 w10
  let v15 : W := v14 + v13
  let v16 : W := v15 + v15
  let v17 : W := v6 + v16
  let v18 : W := v6 + v12
  let v19 : W := w11 * w15
  let v20 : W := v19 + v18
  let v21 : W := w9 * w3
  let v22 : W := v21 + v20
  let v23 : W := MachineState.readWord v3 192
  let v24 : W := v23 * w12
  let v25 : W := v24 + v22
  let v26 : W := UInt256.mulMod w11 w15 w10
  let v27 : W := v26 + v17
  let v28 : W := UInt256.mulMod w9 w3 w10
  let v29 : W := v28 + v27
  let v30 : W := MachineState.readWord v3 192
  let v31 : W := UInt256.mulMod v30 w12 w10
  let v32 : W := v31 + v29
  let v33 : W := MachineState.readWord v3 2720
  let v34 : W := v25 * v33
  let v35 : W := UInt256.land w13 v34
  let v36 : ByteArray := MachineState.writeBytes v3 (Data.Bytes.natToBytesPadded v35.toNat 32) 0
  let v37 : W := UInt256.mulMod v35 w14 w10
  let v38 : W := v37 + v32
  let v39 : W := UInt256.mulMod (N 2048) v38 w10
  let v40 : W := MachineState.readWord v36 64
  let v41 : W := MachineState.readWord v36 768
  let v42 : W := v40 * v41
  let v43 : W := MachineState.readWord v36 32
  let v44 : W := w6 * v43
  let v45 : W := v44 + v42
  let v46 : W := v45 + v45
  let v47 : W := UInt256.mulMod v40 v41 w10
  let v48 : W := MachineState.readWord v36 32
  let v49 : W := UInt256.mulMod w6 v48 w10
  {s with pc := N 5968, memory := v36, stack := v49 :: v47 :: v46 :: v39 :: w3 :: w4 :: w5 :: w6 :: w7 :: w8 :: w9 :: w10 :: w11 :: w12 :: w13 :: w14 :: w15 :: w16 :: rest}

def squareColumn1Program : List Instr := CycleSubmission.DoubleInput01.program1
end CycleSubmission.Execution
