import Challenge.Ripemd160.Submission.Proofs.Bytecode.DriverTrace
import Challenge.Ripemd160.Submission.Proofs.Bytecode.EmptySpec
import Challenge.Ripemd160.Submission.Proofs.Bytecode.CachedCoreCommon
set_option warningAsError true
set_option maxRecDepth 100000
set_option maxHeartbeats 40000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.DirectEmptyReturn
open EvmSemantics EvmSemantics.EVM YulEvmCompiler Challenge.EvmProof
open StackRoundTrace StackRoundTemplate PairedHelperBooleanTrace PairedAllInlineCoreTrace CachedCoreCommon
def decisionPath : List (Stepper.Located Artifact.submissionArtifact .Osaka) :=
  DriverTrace.enterPath

def bodyEntry (s : State) (input : ByteArray) (_i : Nat) : State :=
  { s with
    pc := UInt256.ofNat 369
    stack := [UInt256.ofNat 0, Padding.paddedWord input] }

theorem run_decision_empty (s : State) (input : ByteArray) (i : Nat)
    (hempty : input.size = 0)
    (hcalldata : s.executionEnv.calldata = input)
    (hrun : s.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock decisionPath
      (DriverTrace.setupEntry s input) = some (bodyEntry s input i) := by
  have hfalse : ¬ UInt256.isTrue (UInt256.ofNat input.size) := by
    simp [hempty, UInt256.isTrue]
  have hpc231 : Artifact.submissionArtifact.instructionPC 231 = 364 := by
    rw [ArtifactByteLength.instructionPC_eq_byteLength]
    decide
  have hpc232 : Artifact.submissionArtifact.instructionPC 232 = 365 := by
    rw [ArtifactByteLength.instructionPC_eq_byteLength]
    decide
  have hpc233 : Artifact.submissionArtifact.instructionPC 233 = 368 := by
    rw [ArtifactByteLength.instructionPC_eq_byteLength]
    decide
  simp [decisionPath, DriverTrace.enterPath, Challenge.EvmProof.Stepper.runLocatedBlock,
    Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
    DriverTrace.setupEntry, bodyEntry, hcalldata, hrun, hempty, hfalse,
    hpc231, hpc232, hpc233,
    UInt256.isTrue, Challenge.EvmProof.Word.ofNat_add_mod,
    Challenge.EvmProof.Word.succ_ofNat_mod]

def bodyTemplate : List Instr :=
  [ .push ⟨20, by decide⟩ (UInt256.ofNat 890993315260586290631548281360202943075753233713),
    .push ⟨0, by decide⟩ (UInt256.ofNat 0),
    .op .MSTORE,
    .push ⟨1, by decide⟩ (UInt256.ofNat 32),
    .push ⟨0, by decide⟩ (UInt256.ofNat 0),
    .op .RETURN ]
theorem body_slice :
    (Artifact.submissionArtifact.instructions.drop 234).take bodyTemplate.length = bodyTemplate := by rfl
def bodySite : GenericRoundSite Artifact.submissionArtifact .Osaka bodyTemplate :=
  StackSiteBuilder.ofSlice bodyTemplate 234 body_slice
    (by change 234 + bodyTemplate.length ≤ Artifact.submissionInstructions.length
        rw [Artifact.referenceInstructions_count]; decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem (instructions := bodyTemplate) (by decide))
    (by decide)
theorem body_pc : bodySite.startPC = UInt256.ofNat 369 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 234) = UInt256.ofNat 369
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide
theorem body_advances : ∀ instruction ∈ bodyTemplate.dropLast, DenseScheduleLift.Advances instruction := by
  apply coreAdvancesAll_sound
  decide
def outputMemory (memory : ByteArray) : ByteArray :=
  MachineState.writeBytes memory EmptySpec.emptyOutput 0

def finalState (s : State) (input : ByteArray) (i : Nat) : State :=
  {bodyEntry s input i with pc := UInt256.ofNat 395, memory := outputMemory s.memory, activeWords := UInt256.ofNat (MachineState.activeWordsAfter
      (s.activeWordsAfterUInt256 0 32).toNat 0 32), halt := .Returned, hReturn := MachineState.readPadded (outputMemory s.memory) 0 32}

theorem run_body (s : State) (input : ByteArray) (i : Nat) (hrun : s.halt = .Running) :
    runInstrSeq bodyTemplate (bodyEntry s input i) = some (finalState s input i) := by
  have hbytes : Data.Bytes.natToBytesPadded (UInt256.ofNat EmptySpec.digestNat).toNat 32 =
      EmptySpec.emptyOutput := by
    rw [Memory.natToBytesPadded_eq_natToBE]
    decide
  simp [bodyTemplate, bodyEntry, finalState, outputMemory,
    runInstrSeq, Stepper.runInstr, UInt256.succ, Instr.size, hrun,
    State.activeWordsAfterUInt256, Challenge.EvmProof.Word.word_toNat_ofNat,
    ← hbytes, EmptySpec.digestNat]
  all_goals repeat first | apply And.intro | rfl

def gasSteps_return (s : State) (input : ByteArray) (i : Nat) (hempty : input.size = 0)
    (hcalldata : s.executionEnv.calldata = input)
    (hcode : s.executionEnv.code = submissionBytecode) (hfork : s.fork = .Osaka)
    (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    GasSteps (DriverTrace.setupEntry s input) (finalState s input i) := by
  have gd := Stepper.runLocatedBlock_sound Artifact.submissionArtifact .Osaka
    decisionPath (s := DriverTrace.setupEntry s input) hcode hfork
    (run_decision_empty s input i hempty hcalldata hrun) hrun hnp
  have gb := gasSteps_terminal_of_raw bodySite (bodyEntry s input i) _
    hcode hfork hrun hnp body_pc.symm body_advances (run_body s input i hrun)
  exact gd.trans gb

theorem correct_empty (input : ByteArray) (hfit : CalldataFits input) (hempty : input.size = 0)
    (entryPrefix : GasSteps (initialState submissionBytecode input 0) (Execution.atPC input 268)) :
    ∃ g₀ : Nat, ∀ gas : Nat, g₀ ≤ gas →
      Eval (initialState submissionBytecode input gas) (.returned (spec input)) := by
  let s := PaddingTrace.padReturned input
  have hp := PaddingTrace.gasSteps_pad input hfit entryPrefix
  have hs : s = DriverTrace.setupEntry s input := by
    have hpc := PaddingTrace.padReturned_pc input
    have hstack := PaddingTrace.padReturned_stack input
    dsimp only [s, DriverTrace.setupEntry]
    rw [← hpc, ← hstack]
  have hr := gasSteps_return s input 0 hempty (by rfl)
    (PaddingTrace.padReturned_code input) (PaddingTrace.padReturned_fork input)
    (PaddingTrace.padReturned_halt input) (PaddingTrace.padReturned_noPrecompile input)
  let trace := hp.trans (hr.cast hs.symm rfl)
  have hinput : input = ByteArray.empty := by
    apply ByteArray.ext
    apply Array.ext
    · simpa using hempty
    · intro i hi
      simp [hempty] at hi
  have hread : MachineState.readPadded (outputMemory s.memory) 0 32 = EmptySpec.emptyOutput := by
    exact Memory.readPadded_writeBytes_same s.memory EmptySpec.emptyOutput 0
  have hspec : spec input = EmptySpec.emptyOutput := by rw [hinput]; exact EmptySpec.spec_empty
  refine ⟨trace.cost, fun gas hgas => ?_⟩
  have heval := eval_of_steps (trace.trace gas hgas) (by
    simp [withGas, finalState, bodyEntry, s, State.isDone, State.isHalted, State.isRunning]
    rfl)
  rw [State.toResult_returned _ (by rfl)] at heval
  change Eval (withGas (initialState submissionBytecode input 0) gas)
    (.returned (MachineState.readPadded (outputMemory s.memory) 0 32)) at heval
  rw [hread, ← hspec] at heval
  have hwith : withGas (initialState submissionBytecode input 0) gas = initialState submissionBytecode input gas := rfl
  simpa only [hwith] using heval
#print axioms correct_empty
end Challenge.Ripemd160.Submission.Proofs.Bytecode.DirectEmptyReturn
