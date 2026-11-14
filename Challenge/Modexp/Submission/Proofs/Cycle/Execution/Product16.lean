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

def productColumn16Model (s : State) (carry word0 word1 word2 word3 word4 word5 word6 word7 word8 word9 word10 word11 word12 word13 word14 : UInt256) (rest : List UInt256) : State :=
  let v0 : UInt256 := MachineState.readWord s.memory 1920
  let v1 : UInt256 := v0 * word1
  let v2 : UInt256 := v1 + word0
  let v3 : UInt256 := UInt256.mulMod v0 word1 word8
  let v4 : UInt256 := v3 + carry
  let v5 : UInt256 := MachineState.readWord s.memory 224
  let v6 : UInt256 := word9 * v5
  let v7 : UInt256 := v6 + v2
  let v8 : UInt256 := word7 * word5
  let v9 : UInt256 := v8 + v7
  let v10 : UInt256 := word2 * word4
  let v11 : UInt256 := v10 + v9
  let v12 : UInt256 := word6 * word10
  let v13 : UInt256 := v12 + v11
  let v14 : UInt256 := word3 * word12
  let v15 : UInt256 := v14 + v13
  let v16 : UInt256 := MachineState.readWord s.memory 224
  let v17 : UInt256 := UInt256.mulMod word9 v16 word8
  let v18 : UInt256 := v17 + v4
  let v19 : UInt256 := UInt256.mulMod word7 word5 word8
  let v20 : UInt256 := v19 + v18
  let v21 : UInt256 := UInt256.mulMod word2 word4 word8
  let v22 : UInt256 := v21 + v20
  let v23 : UInt256 := UInt256.mulMod word6 word10 word8
  let v24 : UInt256 := v23 + v22
  let v25 : UInt256 := UInt256.mulMod word3 word12 word8
  let v26 : UInt256 := v25 + v24
  let v27 : UInt256 := UInt256.land word11 v15
  let v28 : UInt256 := v26 - v27
  let v29 : UInt256 := word8 + v28
  let v30 : UInt256 := UInt256.mulMod v29 (UInt256.ofNat 2048) word8
  let v31 : UInt256 := MachineState.readWord s.memory 96
  let v32 : UInt256 := MachineState.readWord s.memory 2048
  let v33 : ByteArray := MachineState.writeBytes s.memory (Data.Bytes.natToBytesPadded v27.toNat 32) 32
  let v34 : UInt256 := v32 * v31
  let v35 : UInt256 := v34 + v30
  let v36 : UInt256 := UInt256.mulMod v32 v31 word8
  let v37 : UInt256 := v36 + v30
  let v38 : UInt256 := MachineState.readWord v33 128
  let v39 : UInt256 := MachineState.readWord v33 2016
  let v40 : UInt256 := v39 * v38
  let v41 : UInt256 := v40 + v35
  let v42 : UInt256 := UInt256.mulMod v39 v38 word8
  let v43 : UInt256 := v42 + v37
  let v44 : UInt256 := MachineState.readWord v33 160
  let v45 : UInt256 := MachineState.readWord v33 1984
  {s with pc := UInt256.ofNat 7854, memory := v33, stack := v41 :: v44 :: word8 :: v43 :: v45 :: word1 :: word2 :: word3 :: word4 :: word5 :: word6 :: word7 :: word8 :: word9 :: word10 :: word11 :: word12 :: word13 :: word14 :: rest}

end CycleSubmission.Execution
