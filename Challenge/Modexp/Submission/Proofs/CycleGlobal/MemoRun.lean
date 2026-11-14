import Challenge.Modexp.Submission.Proofs.CycleGlobal.MemoPaths
noncomputable section
set_option warningAsError true
namespace CycleSubmission.Global.Memo
open Challenge.Modexp EvmSemantics EvmSemantics.EVM Challenge.EvmProof
open Challenge.Modexp.Submission.Proofs.Bytecode
abbrev entryState (input : ByteArray) : State := CycleSubmission.CombinedMemoGuard.state CycleSubmission.Artifact.artifact input 903
abbrev legacyState (input : ByteArray) : State := CycleSubmission.CombinedMemoGuard.state CycleSubmission.Artifact.artifact input 519
abbrev hitEntryState (input : ByteArray) : State := CycleSubmission.CombinedMemoGuard.state CycleSubmission.Artifact.artifact input 933
noncomputable def gasSteps_hit (input : ByteArray) (hvalid : ValidInput input) (hmatch : MemoLogic.Matches input) :
 GasSteps (entryState input) (hitEntryState input) :=
 CycleSubmission.CombinedMemoGuard.hit CycleSubmission.Artifact.artifact combinedBlock codeBound jumpDestLegacy input hvalid hmatch
noncomputable def gasSteps_miss (input : ByteArray) (hvalid : ValidInput input) (hmiss : ¬ MemoLogic.Matches input) :
 GasSteps (entryState input) (legacyState input) :=
 CycleSubmission.CombinedMemoGuard.miss CycleSubmission.Artifact.artifact combinedBlock codeBound jumpDestLegacy input hvalid hmiss
#print axioms gasSteps_hit
#print axioms gasSteps_miss
end CycleSubmission.Global.Memo
