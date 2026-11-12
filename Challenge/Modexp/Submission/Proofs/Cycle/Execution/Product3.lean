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

def productColumn3Model (s : State) (carry word0 word1 word2 word3 word4 word5 word6 word7 word8 word9 word10 word11 word12 word13 word14 word15 : UInt256) (rest : List UInt256) : State :=
  let v0 : UInt256 := MachineState.readWord s.memory 192
  let v1 : UInt256 := v0 * carry
  let v2 : UInt256 := v1 + word0
  let v3 : UInt256 := MachineState.readWord s.memory 0
  let v4 : UInt256 := v3 * word11
  let v5 : UInt256 := v4 + v2
  let v6 : UInt256 := UInt256.mulMod word10 word4 word9
  let v7 : UInt256 := v6 + word1
  let v8 : UInt256 := UInt256.mulMod word8 word14 word9
  let v9 : UInt256 := v8 + v7
  let v10 : UInt256 := MachineState.readWord s.memory 192
  let v11 : UInt256 := UInt256.mulMod v10 word2 word9
  let v12 : UInt256 := v11 + v9
  let v13 : UInt256 := MachineState.readWord s.memory 0
  let v14 : UInt256 := UInt256.mulMod v13 word11 word9
  let v15 : UInt256 := v14 + v12
  let v16 : UInt256 := MachineState.readWord s.memory 2720
  let v17 : UInt256 := v5 * v16
  let v18 : UInt256 := UInt256.land word12 v17
  let v19 : ByteArray := MachineState.writeBytes s.memory (Data.Bytes.natToBytesPadded v18.toNat 32) 224
  let v20 : UInt256 := UInt256.mulMod v18 word13 word9
  let v21 : UInt256 := v20 + v15
  let v22 : UInt256 := UInt256.mulMod (UInt256.ofNat 2048) v21 word9
  let v23 : UInt256 := MachineState.readWord v19 768
  let v24 : UInt256 := MachineState.readWord v19 1952
  let v25 : UInt256 := v24 * v23
  let v26 : UInt256 := v25 + v22
  let v27 : UInt256 := UInt256.mulMod v24 v23 word9
  let v28 : UInt256 := v27 + v22
  let v29 : UInt256 := MachineState.readWord v19 1920
  let v30 : UInt256 := v29 * word5
  let v31 : UInt256 := v30 + v26
  let v32 : UInt256 := UInt256.mulMod v29 word5 word9
  let v33 : UInt256 := v32 + v28
  let v34 : UInt256 := MachineState.readWord v19 1888
  let v35 : UInt256 := v34 * word6
  let v36 : UInt256 := v35 + v31
  let v37 : UInt256 := UInt256.mulMod v34 word6 word9
  let v38 : UInt256 := v37 + v33
  let v39 : UInt256 := MachineState.readWord v19 32
  let v40 : UInt256 := MachineState.readWord v19 1856
  let v41 : UInt256 := v40 * v39
  let v42 : UInt256 := v41 + v36
  let v43 : UInt256 := UInt256.mulMod v40 v39 word9
  let v44 : UInt256 := v43 + v38
  let v45 : UInt256 := MachineState.readWord v19 64
  let v46 : UInt256 := MachineState.readWord v19 1824
  {s with pc := UInt256.ofNat 8264, memory := v19, stack := v46 :: v45 :: v42 :: v45 :: word9 :: v44 :: v46 :: word2 :: word3 :: word4 :: word5 :: word6 :: word7 :: word8 :: word9 :: word10 :: word11 :: word12 :: word13 :: word14 :: word15 :: rest}

end CycleSubmission.Execution
