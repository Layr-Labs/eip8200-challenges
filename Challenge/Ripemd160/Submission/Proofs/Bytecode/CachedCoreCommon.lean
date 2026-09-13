import Challenge.Ripemd160.Submission.Proofs.Bytecode.PairedAllInlineCoreTrace
import Challenge.Ripemd160.Submission.Proofs.Bytecode.StackRoundData
import Challenge.Ripemd160.Submission.Proofs.Bytecode.StackSiteBuilder
set_option warningAsError true
set_option maxRecDepth 100000
set_option maxHeartbeats 40000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.CachedCoreCommon
open EvmSemantics EvmSemantics.EVM YulEvmCompiler Challenge.EvmProof
open StackRoundTrace StackRoundTemplate PairedHelperBooleanTrace
structure Input where
  v0 : UInt256
  v1 : UInt256
  v2 : UInt256
  v3 : UInt256
  v4 : UInt256
  v5 : UInt256
  v6 : UInt256
  v7 : UInt256
  v8 : UInt256
  v9 : UInt256

def cache (memory : ByteArray) : List UInt256 :=
  [UInt256.ofNat 22, MachineState.readWord memory 256, MachineState.readWord memory 384, MachineState.readWord memory 416, MachineState.readWord memory 352, MachineState.readWord memory 320]
@[simp] theorem cache_length (memory : ByteArray) : (cache memory).length = 6 := rfl

def inputStack (memory : ByteArray) (x : Input) (rho : List UInt256) : List UInt256 :=
  [x.v0, x.v1, x.v2, x.v3, x.v4, x.v5, x.v6, x.v7, x.v8, x.v9] ++ (cache memory ++ rho)

end Challenge.Ripemd160.Submission.Proofs.Bytecode.CachedCoreCommon
