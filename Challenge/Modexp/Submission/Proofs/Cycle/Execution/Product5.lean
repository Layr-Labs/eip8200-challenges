import Challenge.Modexp.Submission.Proofs.Fast.Monpro
import Challenge.Modexp.Submission.Proofs.Bytecode.WindowNibbleDefs
set_option warningAsError true
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option maxRecDepth 40000
set_option maxHeartbeats 8000000
namespace CycleSubmission.Execution
open EvmSemantics EvmSemantics.EVM YulEvmCompiler
open Challenge.Modexp.Submission.Proofs.Bytecode.WindowNibbleKernel
open Challenge.Modexp.Submission.Proofs.Fast

def productColumn5Model (s : State) (carry word0 word1 word2 word3 word4 word5 word6 word7 word8 word9 word10 word11 word12 word13 word14 word15 word16 word17 word18 : UInt256) (rest : List UInt256) : State :=
  let v0 : UInt256 := carry + word0
  let v1 : UInt256 := UInt256.mulMod word4 word1 word2
  let v2 : UInt256 := v1 + word3
  let v3 : UInt256 := MachineState.readWord s.memory 1920
  let v4 : UInt256 := v3 * word9
  let v5 : UInt256 := v4 + v0
  let v6 : UInt256 := UInt256.mulMod v3 word9 word12
  let v7 : UInt256 := v6 + v2
  let v8 : UInt256 := MachineState.readWord s.memory 32
  let v9 : UInt256 := MachineState.readWord s.memory 1888
  let v10 : UInt256 := v9 * v8
  let v11 : UInt256 := v10 + v5
  let v12 : UInt256 := UInt256.mulMod v9 v8 word12
  let v13 : UInt256 := v12 + v7
  let v14 : UInt256 := MachineState.readWord s.memory 64
  let v15 : UInt256 := MachineState.readWord s.memory 1856
  let v16 : UInt256 := v15 * v14
  let v17 : UInt256 := v16 + v11
  let v18 : UInt256 := UInt256.mulMod v15 v14 word12
  let v19 : UInt256 := v18 + v13
  let v20 : UInt256 := MachineState.readWord s.memory 96
  let v21 : UInt256 := MachineState.readWord s.memory 1824
  let v22 : UInt256 := v21 * v20
  let v23 : UInt256 := v22 + v17
  let v24 : UInt256 := UInt256.mulMod v21 v20 word12
  let v25 : UInt256 := v24 + v19
  let v26 : UInt256 := MachineState.readWord s.memory 128
  let v27 : UInt256 := MachineState.readWord s.memory 1792
  let v28 : UInt256 := v27 * v26
  let v29 : UInt256 := v28 + v23
  let v30 : UInt256 := UInt256.mulMod v27 v26 word12
  let v31 : UInt256 := v30 + v25
  let v32 : UInt256 := word13 * word6
  let v33 : UInt256 := v32 + v29
  let v34 : UInt256 := word11 * word10
  let v35 : UInt256 := v34 + v33
  let v36 : UInt256 := MachineState.readWord s.memory 192
  let v37 : UInt256 := v36 * word7
  let v38 : UInt256 := v37 + v35
  let v39 : UInt256 := MachineState.readWord s.memory 0
  let v40 : UInt256 := v39 * word17
  let v41 : UInt256 := v40 + v38
  let v42 : UInt256 := MachineState.readWord s.memory 224
  let v43 : UInt256 := v42 * word5
  let v44 : UInt256 := v43 + v41
  let v45 : UInt256 := MachineState.readWord s.memory 1216
  let v46 : UInt256 := v45 * word14
  let v47 : UInt256 := v46 + v44
  let v48 : UInt256 := UInt256.mulMod word13 word6 word12
  let v49 : UInt256 := v48 + v31
  let v50 : UInt256 := UInt256.mulMod word11 word10 word12
  let v51 : UInt256 := v50 + v49
  {s with pc := UInt256.ofNat 8580, memory := s.memory, stack := word7 :: word12 :: v51 :: v47 :: word5 :: word6 :: word7 :: word8 :: word9 :: word10 :: word11 :: word12 :: word13 :: word14 :: word15 :: word16 :: word17 :: word18 :: rest}

end CycleSubmission.Execution
