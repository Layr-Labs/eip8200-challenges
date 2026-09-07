import Challenge.Ripemd160.ProofSupport.Bytecode
import Challenge.Ripemd160.Submission.Bytecode
import Challenge.Ripemd160.Submission.Proofs.Bytecode.ReferenceCorrect

set_option warningAsError true

/-!
# Direct-bytecode target and proof umbrella for the RIPEMD-160 reference

`referenceDirectGoal` fixes the reusable raw-bytecode obligation to the frozen
artifact. The implementation-specific proof is exposed unconditionally as
`ReferenceCorrect.reference_correct : Correct submissionBytecode`, together
with its exact-schedule strengthening
`ReferenceCorrect.reference_correctWithSchedule`.
-/

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode

open Challenge.Ripemd160.ProofSupport.Bytecode

def referenceDirectGoal : Prop := DirectProof submissionBytecode

end Challenge.Ripemd160.Submission.Proofs.Bytecode
