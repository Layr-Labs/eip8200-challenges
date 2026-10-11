import Challenge.EvmProof.Gas
namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.ColdTraceCompose
open EvmSemantics EvmSemantics.EVM Challenge.EvmProof
opaque two {s t u : State} (a : GasSteps s t) (b : GasSteps t u) : GasSteps s u := a.trans b
#print axioms two
end Challenge.Ripemd160.Submission.Proofs.Bytecode.ColdTraceCompose
