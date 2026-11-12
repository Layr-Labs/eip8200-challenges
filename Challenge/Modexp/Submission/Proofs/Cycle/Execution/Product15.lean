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

def productColumn15Model (s : State) (carry word0 word1 word2 word3 word4 word5 word6 word7 word8 word9 word10 word11 word12 word13 word14 word15 : UInt256) (rest : List UInt256) : State :=
  let v0 : UInt256 := word4 * carry
  let v1 : UInt256 := v0 + word0
  let v2 : UInt256 := word14 * word13
  let v3 : UInt256 := v2 + v1
  let v4 : UInt256 := MachineState.readWord s.memory 0
  let v5 : UInt256 := UInt256.mulMod word10 v4 word9
  let v6 : UInt256 := v5 + word1
  let v7 : UInt256 := MachineState.readWord s.memory 224
  let v8 : UInt256 := UInt256.mulMod word8 v7 word9
  let v9 : UInt256 := v8 + v6
  let v10 : UInt256 := UInt256.mulMod word3 word6 word9
  let v11 : UInt256 := v10 + v9
  let v12 : UInt256 := UInt256.mulMod word7 word5 word9
  let v13 : UInt256 := v12 + v11
  let v14 : UInt256 := UInt256.mulMod word4 word11 word9
  let v15 : UInt256 := v14 + v13
  let v16 : UInt256 := UInt256.mulMod word13 word14 word9
  let v17 : UInt256 := v16 + v15
  let v18 : UInt256 := UInt256.land word12 v3
  let v19 : UInt256 := v17 - v18
  let v20 : UInt256 := word9 + v19
  let v21 : UInt256 := UInt256.mulMod v20 (UInt256.ofNat 2048) word9
  let v22 : UInt256 := MachineState.readWord s.memory 64
  let v23 : UInt256 := MachineState.readWord s.memory 2048
  let v24 : ByteArray := MachineState.writeBytes s.memory (Data.Bytes.natToBytesPadded v18.toNat 32) 832
  let v25 : UInt256 := v23 * v22
  let v26 : UInt256 := v25 + v21
  let v27 : UInt256 := UInt256.mulMod v23 v22 word9
  let v28 : UInt256 := v27 + v21
  let v29 : UInt256 := MachineState.readWord v24 96
  let v30 : UInt256 := MachineState.readWord v24 2016
  let v31 : UInt256 := v30 * v29
  let v32 : UInt256 := v31 + v26
  let v33 : UInt256 := UInt256.mulMod v30 v29 word9
  let v34 : UInt256 := v33 + v28
  let v35 : UInt256 := MachineState.readWord v24 128
  let v36 : UInt256 := MachineState.readWord v24 1984
  let v37 : UInt256 := v36 * v35
  let v38 : UInt256 := v37 + v32
  let v39 : UInt256 := UInt256.mulMod v36 v35 word9
  let v40 : UInt256 := v39 + v34
  let v41 : UInt256 := MachineState.readWord v24 160
  let v42 : UInt256 := MachineState.readWord v24 1952
  let v43 : UInt256 := v42 * v41
  let v44 : UInt256 := v43 + v38
  let v45 : UInt256 := UInt256.mulMod v42 v41 word9
  let v46 : UInt256 := v45 + v40
  {s with pc := UInt256.ofNat 9778, memory := v24, stack := v46 :: v44 :: word2 :: word3 :: word4 :: word5 :: word6 :: word7 :: word8 :: word9 :: word10 :: word11 :: word12 :: word13 :: word14 :: word15 :: rest}

end CycleSubmission.Execution
