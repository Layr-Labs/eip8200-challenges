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

def productColumn19Model (s : State) (carry word0 word1 word2 word3 word4 word5 word6 word7 word8 word9 word10 word11 word12 word13 word14 : UInt256) (rest : List UInt256) : State :=
  let v0 : UInt256 := UInt256.mulMod word0 word1 word8
  let v1 : UInt256 := v0 + carry
  let v2 : UInt256 := word0 * word1
  let v3 : UInt256 := v2 + carry
  let v4 : UInt256 := word9 * word12
  let v5 : UInt256 := v4 + v3
  let v6 : UInt256 := UInt256.mulMod word9 word12 word8
  let v7 : UInt256 := v6 + v1
  let v8 : UInt256 := UInt256.land word11 v5
  let v9 : UInt256 := v7 - v8
  let v10 : UInt256 := word8 + v9
  let v11 : UInt256 := UInt256.mulMod v10 (UInt256.ofNat 2048) word8
  let v12 : ByteArray := MachineState.writeBytes s.memory (Data.Bytes.natToBytesPadded v8.toNat 32) 160
  {s with pc := UInt256.ofNat 8138, memory := v12, stack := word14 :: word2 :: word3 :: word4 :: word5 :: word6 :: word7 :: word8 :: word9 :: word10 :: word11 :: word12 :: word13 :: v11 :: rest}

end CycleSubmission.Execution
