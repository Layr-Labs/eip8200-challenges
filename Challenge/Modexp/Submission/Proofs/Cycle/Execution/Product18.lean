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

def productColumn18Model (s : State) (carry word0 word1 word2 word3 word4 word5 word6 word7 word8 word9 word10 word11 word12 word13 word14 word15 word16 word17 word18 word19 : UInt256) (rest : List UInt256) : State :=
  let v0 : UInt256 := carry * word0
  let v1 : UInt256 := v0 + word1
  let v2 : UInt256 := UInt256.mulMod word5 word2 word3
  let v3 : UInt256 := v2 + word4
  let v4 : UInt256 := word14 * word9
  let v5 : UInt256 := v4 + v1
  let v6 : UInt256 := word12 * word15
  let v7 : UInt256 := v6 + v5
  let v8 : UInt256 := word7 * word17
  let v9 : UInt256 := v8 + v7
  let v10 : UInt256 := UInt256.mulMod word14 word9 word13
  let v11 : UInt256 := v10 + v3
  let v12 : UInt256 := UInt256.mulMod word12 word15 word13
  let v13 : UInt256 := v12 + v11
  let v14 : UInt256 := UInt256.mulMod word7 word17 word13
  let v15 : UInt256 := v14 + v13
  let v16 : UInt256 := UInt256.land word16 v9
  let v17 : ByteArray := MachineState.writeBytes s.memory (Data.Bytes.natToBytesPadded v16.toNat 32) 96
  let v18 : UInt256 := v15 - v16
  let v19 : UInt256 := word13 + v18
  let v20 : UInt256 := UInt256.mulMod v19 (UInt256.ofNat 2048) word13
  let v21 : UInt256 := MachineState.readWord v17 2048
  let v22 : UInt256 := MachineState.readWord v17 160
  let v23 : UInt256 := MachineState.readWord v17 800
  let v24 : UInt256 := v21 * v22
  let v25 : UInt256 := v24 + v20
  let v26 : UInt256 := UInt256.mulMod v21 v22 word13
  let v27 : UInt256 := v26 + v20
  let v28 : UInt256 := MachineState.readWord v17 2016
  let v29 : UInt256 := v28 * word6
  let v30 : UInt256 := v29 + v25
  let v31 : UInt256 := UInt256.mulMod v28 word6 word13
  let v32 : UInt256 := v31 + v27
  let v33 : UInt256 := word14 * word15
  let v34 : UInt256 := v33 + v30
  let v35 : UInt256 := word12 * word17
  let v36 : UInt256 := v35 + v34
  let v37 : UInt256 := UInt256.mulMod word14 word15 word13
  let v38 : UInt256 := v37 + v32
  let v39 : UInt256 := UInt256.mulMod word12 word17 word13
  let v40 : UInt256 := v39 + v38
  let v41 : UInt256 := UInt256.land word16 v36
  let v42 : ByteArray := MachineState.writeBytes v17 (Data.Bytes.natToBytesPadded v41.toNat 32) 128
  let v43 : UInt256 := v40 - v41
  let v44 : UInt256 := word13 + v43
  let v45 : UInt256 := UInt256.mulMod v44 (UInt256.ofNat 2048) word13
  let v46 : UInt256 := MachineState.readWord v42 2048
  {s with pc := UInt256.ofNat 10209, memory := v42, stack := v45 :: v46 :: word6 :: word7 :: word8 :: v23 :: word10 :: word11 :: word12 :: word13 :: word14 :: word15 :: word16 :: word17 :: word18 :: word19 :: rest}

end CycleSubmission.Execution
