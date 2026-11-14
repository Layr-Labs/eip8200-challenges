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
def productColumn4Model (s : State) (carry word0 word1 word2 word3 word4 word5 word6 word7 word8 word9 word10 word11 word12 word13 word14 word15 word16 word17 word18 word19 : UInt256) (rest : List UInt256) : State :=
  let v0 : UInt256 := carry * word0
  let v1 : UInt256 := v0 + word1
  let v2 : UInt256 := UInt256.mulMod word5 word2 word3
  let v3 : UInt256 := v2 + word4
  let v4 : UInt256 := MachineState.readWord s.memory 96
  let v5 : UInt256 := MachineState.readWord s.memory 1792
  let v6 : UInt256 := v5 * v4
  let v7 : UInt256 := v6 + v1
  let v8 : UInt256 := UInt256.mulMod v5 v4 word13
  let v9 : UInt256 := v8 + v3
  let v10 : UInt256 := word14 * word11
  let v11 : UInt256 := v10 + v7
  let v12 : UInt256 := word12 * word8
  let v13 : UInt256 := v12 + v11
  let v14 : UInt256 := MachineState.readWord s.memory 192
  let v15 : UInt256 := v14 * word18
  let v16 : UInt256 := v15 + v13
  let v17 : UInt256 := MachineState.readWord s.memory 0
  let v18 : UInt256 := v17 * word6
  let v19 : UInt256 := v18 + v16
  let v20 : UInt256 := MachineState.readWord s.memory 224
  let v21 : UInt256 := v20 * word15
  let v22 : UInt256 := v21 + v19
  let v23 : UInt256 := UInt256.mulMod word14 word11 word13
  let v24 : UInt256 := v23 + v9
  let v25 : UInt256 := UInt256.mulMod word12 word8 word13
  let v26 : UInt256 := v25 + v24
  let v27 : UInt256 := MachineState.readWord s.memory 192
  let v28 : UInt256 := UInt256.mulMod v27 word18 word13
  let v29 : UInt256 := v28 + v26
  let v30 : UInt256 := MachineState.readWord s.memory 0
  let v31 : UInt256 := UInt256.mulMod v30 word6 word13
  let v32 : UInt256 := v31 + v29
  let v33 : UInt256 := MachineState.readWord s.memory 224
  let v34 : UInt256 := UInt256.mulMod v33 word15 word13
  let v35 : UInt256 := v34 + v32
  let v36 : UInt256 := MachineState.readWord s.memory 2720
  let v37 : UInt256 := v22 * v36
  let v38 : UInt256 := UInt256.land word16 v37
  let v39 : ByteArray := MachineState.writeBytes s.memory (Data.Bytes.natToBytesPadded v38.toNat 32) 1216
  let v40 : UInt256 := UInt256.mulMod v38 word17 word13
  let v41 : UInt256 := v40 + v35
  let v42 : UInt256 := UInt256.mulMod (UInt256.ofNat 2048) v41 word13
  let v43 : UInt256 := MachineState.readWord v39 768
  let v44 : UInt256 := MachineState.readWord v39 1984
  let v45 : UInt256 := v44 * v43
  let v46 : UInt256 := v45 + v42
  let v47 : UInt256 := UInt256.mulMod v44 v43 word13
  let v48 : UInt256 := v47 + v42
  let v49 : UInt256 := MachineState.readWord v39 1952
  let v50 : UInt256 := v49 * word9
  {s with pc := UInt256.ofNat 6536,memory := v39,stack := v50::v46::word9::word13::v48::v49::word6::word7::word8::word9::word10::word11::word12::word13::word14::word15::word16::word17::word18::word19::rest}
end CycleSubmission.Execution
