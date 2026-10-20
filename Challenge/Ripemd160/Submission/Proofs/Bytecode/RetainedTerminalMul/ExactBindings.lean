import Challenge.Ripemd160.Submission.Proofs.Bytecode.RetainedTerminalMul.RetainedAdapters
set_option warningAsError true
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
namespace RetainedIntegration105.ExactBindings
open EvmSemantics EvmSemantics.EVM YulEvmCompiler Challenge.EvmProof
open Challenge.Ripemd160.Submission.Proofs.Bytecode
open StackRoundTrace RetainedIntegration105
def anchorBytes : List UInt8 := [95, 53, 128, 127, 97, 97, 97, 97, 97, 97, 97, 97, 97, 97, 97, 97, 97, 97, 97, 97, 97, 97, 97, 97, 97, 97, 97, 97, 97, 97, 97, 97, 97, 97, 97, 97, 24, 97, 31, 221, 87]
def repeatBytes : List UInt8 := [88, 97, 36, 210, 86]
def storeBytes : List UInt8 := [91, 115, 134, 60, 89, 133, 136, 189, 114, 164, 186, 191, 54, 198, 187, 1, 242, 123, 189, 192, 236, 212, 95, 82]
def resultBytes : List UInt8 := [97, 18, 177, 87]
def digest : UInt256 := 766350606435067737561421097975693824639675460820
theorem anchor_binding : YulEvmCompiler.assembleBytes (anchorTemplate) = anchorBytes := by decide
#print axioms anchor_binding

theorem repeat_binding : Challenge.EvmProof.PcEncoding.assembleBytes (repeatTemplate) = repeatBytes := by decide
#print axioms repeat_binding

theorem store_binding : YulEvmCompiler.assembleBytes (storeTemplate digest) = storeBytes := by decide
#print axioms store_binding

theorem result_binding : YulEvmCompiler.assembleBytes (DirectLiteralRawV4.resultTemplate) = resultBytes := by decide
#print axioms result_binding

end RetainedIntegration105.ExactBindings
