import Challenge.Ripemd160.ProofSupport.Bytecode
import Challenge.Ripemd160.Reference.Bytecode

set_option warningAsError true

namespace Challenge.Ripemd160.Reference.Proofs.Bytecode

open Challenge.Ripemd160.ProofSupport.Bytecode

def referenceDirectGoal : Prop := DirectProof referenceBytecode

end Challenge.Ripemd160.Reference.Proofs.Bytecode
