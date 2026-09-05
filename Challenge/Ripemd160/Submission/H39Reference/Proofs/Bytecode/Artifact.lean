import Challenge.Ripemd160.Submission.H39Reference.Bytecode
import Challenge.Ripemd160.Submission.H39Memo.Artifact
import Challenge.Ripemd160.Submission.H39Memo.RefMetadata

set_option warningAsError true

/-!
# H39 artifact adapter

All concrete bytes and instruction certificates come from `H39Memo.Artifact`.
This namespace keeps the copied functional proof names stable.
-/

namespace Challenge.Ripemd160.Submission.H39Reference.Proofs.Bytecode.Artifact

abbrev referenceInstructions : List YulEvmCompiler.Instr :=
  Challenge.Ripemd160.Submission.H39Memo.Artifact.referenceInstructions

abbrev referenceArtifact : Challenge.EvmProof.ProgramArtifact :=
  Challenge.Ripemd160.Submission.H39Memo.Artifact.referenceArtifact

abbrev instructionPC (index : Nat) : Nat :=
  Challenge.Ripemd160.Submission.H39Memo.Artifact.instructionPC index

abbrev InitStore := Challenge.Ripemd160.Submission.H39Memo.Artifact.InitStore

abbrev initStores : List InitStore :=
  Challenge.Ripemd160.Submission.H39Memo.Artifact.initStores

abbrev initStore_valid :=
  Challenge.Ripemd160.Submission.H39Memo.Artifact.initStore_valid

abbrev padEnterPath :=
  Challenge.Ripemd160.Submission.H39Memo.Artifact.padEnterPath

abbrev padLengthPath :=
  Challenge.Ripemd160.Submission.H39Memo.Artifact.padLengthPath

abbrev padSetupPath :=
  Challenge.Ripemd160.Submission.H39Memo.Artifact.padSetupPath

abbrev refPc349 := Challenge.Ripemd160.Submission.H39Memo.Artifact.refPc349
abbrev refPc378 := Challenge.Ripemd160.Submission.H39Memo.Artifact.refPc378
abbrev refPc403 := Challenge.Ripemd160.Submission.H39Memo.Artifact.refPc403

end Challenge.Ripemd160.Submission.H39Reference.Proofs.Bytecode.Artifact
