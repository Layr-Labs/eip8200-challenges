import Challenge.Ripemd160.ProofSupport.Bytecode
import Challenge.Ripemd160.Reference.Bytecode
import Challenge.Ripemd160.Reference.Proofs.Bytecode.ReferenceCorrect

set_option warningAsError true

/-!
# Direct-bytecode target and proof umbrella for the RIPEMD-160 reference

`referenceDirectGoal` fixes the reusable raw-bytecode obligation to the frozen
artifact. The implementation-specific proof is exposed unconditionally as
`ReferenceCorrect.reference_correct : Correct referenceBytecode`, together
with its exact-schedule strengthening
`ReferenceCorrect.reference_correctWithSchedule`.
-/

namespace Challenge.Ripemd160.Reference.Proofs.Bytecode

open Challenge.Ripemd160.ProofSupport.Bytecode

def referenceDirectGoal : Prop := DirectProof referenceBytecode

end Challenge.Ripemd160.Reference.Proofs.Bytecode
