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
def productColumn17Model (s : State) (carry word0 word1 word2 word3 word4 word5 word6 word7 word8 word9 word10 word11 word12 word13 word14 word15 word16 word17 : UInt256) (rest : List UInt256) : State :=
  let v0 : UInt256 := word3 * word0
  let v1 : UInt256 := v0 + carry
  let v2 : UInt256 := UInt256.mulMod word3 word0 word1
  let v3 : UInt256 := v2 + word2
  let v4 : UInt256 := MachineState.readWord s.memory 1952
  let v5 : UInt256 := v4 * word4
  let v6 : UInt256 := v5 + v1
  let v7 : UInt256 := UInt256.mulMod v4 word4 word11
  let v8 : UInt256 := v7 + v3
  let v9 : UInt256 := word12 * word8
  let v10 : UInt256 := v9 + v6
  let v11 : UInt256 := word10 * word7
  let v12 : UInt256 := v11 + v10
  let v13 : UInt256 := word5 * word13
  let v14 : UInt256 := v13 + v12
  let v15 : UInt256 := word9 * word15
  let v16 : UInt256 := v15 + v14
  let v17 : UInt256 := UInt256.mulMod word12 word8 word11
  let v18 : UInt256 := v17 + v8
  let v19 : UInt256 := UInt256.mulMod word10 word7 word11
  let v20 : UInt256 := v19 + v18
  let v21 : UInt256 := UInt256.mulMod word5 word13 word11
  let v22 : UInt256 := v21 + v20
  let v23 : UInt256 := UInt256.mulMod word9 word15 word11
  let v24 : UInt256 := v23 + v22
  let v25 : UInt256 := UInt256.land word14 v16
  let v26 : ByteArray := MachineState.writeBytes s.memory (Data.Bytes.natToBytesPadded v25.toNat 32) 64
  let v27 : UInt256 := v24 - v25
  let v28 : UInt256 := word11 + v27
  let v29 : UInt256 := UInt256.mulMod v28 (UInt256.ofNat 2048) word11
  let v30 : UInt256 := MachineState.readWord v26 2048
  let v31 : UInt256 := MachineState.readWord v26 128
  let v32 : UInt256 := MachineState.readWord v26 832
  let v33 : UInt256 := v30 * v31
  let v34 : UInt256 := v33 + v29
  let v35 : UInt256 := UInt256.mulMod v30 v31 word11
  let v36 : UInt256 := v35 + v29
  let v37 : UInt256 := MachineState.readWord v26 160
  let v38 : UInt256 := MachineState.readWord v26 2016
  let v39 : UInt256 := v38 * v37
  let v40 : UInt256 := v39 + v34
  let v41 : UInt256 := UInt256.mulMod v38 v37 word11
  let v42 : UInt256 := v41 + v36
  let v43 : UInt256 := MachineState.readWord v26 1984
  {s with pc := UInt256.ofNat 8196,memory := v26,stack := v43::word4::v40::word4::word11::v42::v43::word4::word5::word6::word7::v32::word9::word10::word11::word12::word13::word14::word15::word16::word17::rest}
end CycleSubmission.Execution
