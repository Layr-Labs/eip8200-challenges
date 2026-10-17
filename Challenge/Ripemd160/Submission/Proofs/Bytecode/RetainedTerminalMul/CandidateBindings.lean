import Challenge.Ripemd160.Submission.Proofs.Bytecode.RetainedTerminalMul.CandidateInstructions
import Challenge.Ripemd160.Submission.Proofs.Bytecode.RetainedTerminalMul.BindingBridge
set_option warningAsError true
set_option maxRecDepth 100000
namespace RetainedBridge111.Candidate
open EvmSemantics EvmSemantics.EVM Challenge.EvmProof
open RetainedIntegration105
/-- Match the actual data slice to the previously checked raw evaluator body. -/
theorem literal_eq_template :
    literalInstructions = literalTemplate ExactBindings.digest := by rfl


#print axioms literal_eq_template
end RetainedBridge111.Candidate
