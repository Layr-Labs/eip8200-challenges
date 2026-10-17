import Challenge.Ripemd160.Submission.Proofs.Bytecode.DirectGuardEarly
import Challenge.Ripemd160.Submission.Proofs.Bytecode.TerminalMulRaw
import Challenge.Ripemd160.Submission.Proofs.Bytecode.RecognitionLift
import Challenge.Ripemd160.Submission.Proofs.Bytecode.StackSiteBuilder
import Challenge.Ripemd160.Submission.Proofs.Bytecode.StackRoundData

set_option warningAsError true
set_option maxRecDepth 100000
set_option maxHeartbeats 20000000
set_option linter.unusedSimpArgs false
namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.DirectGuard
open Challenge.Ripemd160 Challenge.EvmProof EvmSemantics EvmSemantics.EVM
open KnownInputCompactState StackRoundTrace StackRoundTemplate

private def scanner := TerminalMulRaw.template
private theorem scanner_slice :
    (Artifact.submissionArtifact.instructions.drop 5260).take scanner.length = scanner := by
  rfl
private theorem scanner_pc : Artifact.submissionArtifact.instructionPC 5260 = 9429 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl
private theorem scanner_bounds :
    5260 + scanner.length ≤ Artifact.submissionArtifact.instructions.length := by
  change 5260 + scanner.length ≤ Artifact.submissionInstructions.length
  rw [Artifact.referenceInstructions_count]
  decide
private theorem scanner_wf : StackRoundData.TemplateWellFormed scanner := by decide
private theorem scanner_advances : ∀ i ∈ scanner.dropLast, RecognitionLift.Advances i := by
  apply RecognitionLift.advancesAll_sound
  decide
private def scanner_site : GenericRoundSite Artifact.submissionArtifact .Osaka scanner :=
  StackSiteBuilder.ofSlice scanner 5260 scanner_slice scanner_bounds
    (by change submissionBytecode.size < 2 ^ 256; rw [referenceBytecode_size]; decide)
    (StackRoundData.templateWellFormed_mem scanner_wf) (by decide)
private theorem scanner_site_pc : scanner_site.startPC = UInt256.ofNat 9429 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 5260) = _
  rw [scanner_pc]

private def scannerEntry (input : ByteArray) : State :=
  { initialState submissionBytecode input 0 with
    pc := UInt256.ofNat 9429
    activeWords := UInt256.ofNat 0
    stack := [equalityAcc input 0, referenceWord input] }

private theorem run_scanner (input : ByteArray)
    (href : referenceWord input = KnownInputData.fullWord) :
    runInstrSeq scanner (scannerEntry input) = some (loopExitState input) := by
  simpa only [scanner, scannerEntry, loopExitState, List.append_nil,
    Challenge.Ripemd160.initialState_calldata, Word.literal_eq_ofNat] using
    TerminalMulRaw.run_equalityAcc
      ({ initialState submissionBytecode input 0 with activeWords := UInt256.ofNat 0 })
      [] (by decide) rfl href

private theorem scanner_start (input : ByteArray) :
    (scannerEntry input).pc = scanner_site.startPC := scanner_site_pc.symm

private def gasSteps_scanner (input : ByteArray)
    (href : referenceWord input = KnownInputData.fullWord) :
    GasSteps (scannerEntry input) (loopExitState input) :=
  RecognitionLift.gasSteps_of_raw scanner_site _ _ (by rfl) (by rfl) (by rfl)
    deployAddress_not_precompile (scanner_start input) scanner_advances (run_scanner input href)

def gasSteps_unrolled_loop (input : ByteArray)
    (href : referenceWord input = KnownInputData.fullWord) :
    GasSteps (loopState input 0) (loopExitState input) := by
  exact gasSteps_scanner input href

#print axioms gasSteps_unrolled_loop
end Challenge.Ripemd160.Submission.Proofs.Bytecode.DirectGuard
