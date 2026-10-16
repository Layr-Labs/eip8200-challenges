import Challenge.Ripemd160.ProofSupport.InitialState
import Challenge.Ripemd160.Submission.Proofs.Bytecode.J2Moves
import Challenge.Ripemd160.Submission.Proofs.Bytecode.J2Accumulator
import Challenge.Ripemd160.Submission.Proofs.Bytecode.J2Payload
import Challenge.Ripemd160.Submission.Proofs.Bytecode.StackSiteBuilder
import Challenge.Ripemd160.Submission.Proofs.Bytecode.StackRoundData
import Challenge.Ripemd160.Submission.Proofs.Bytecode.Artifact

set_option warningAsError true
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false

/-! The early serializer copies the selected digest before the recognizer starts.
The loop changes only pc and stack.  Its successful exit therefore needs only
MSIZE, PUSH0, RETURN; in particular preparation must not execute MSIZE. -/
namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.EarlySerializeReturn
open Challenge.Ripemd160 Challenge.EvmProof EvmSemantics EvmSemantics.EVM YulEvmCompiler
open J2Moves RecognitionSelectorRaw RecognitionSelectorResult StackRoundTrace StackRoundTemplate

/-- The zero-gas state used by all gas-parametric traces in this module. -/
def base (input : ByteArray) : State := initialState submissionBytecode input 0

def source (input : ByteArray) : UInt256 :=
  selected (UInt256.ofNat submissionBytecode.size) input.size

def beforeCopy (input : ByteArray) (rho : List UInt256) : State :=
  atState (base input) 4803 (12 :: source input :: 20 :: rho)

/-- State at the scanner initializer, after CODECOPY and before any MSIZE. -/
def prepared (input : ByteArray) (rho : List UInt256) : State :=
  copied (beforeCopy input rho) (source input) rho

/-- The final return uses the prepared memory, not an unrelated running state. -/
def output (input : ByteArray) (rho : List UInt256) : State :=
  RecognitionSelectorRaw.returned (prepared input rho) (UInt256.ofNat 5571) rho

@[simp] theorem prepared_pc (input : ByteArray) (rho : List UInt256) :
    (prepared input rho).pc = UInt256.ofNat 4804 := by
  change (UInt256.ofNat 4803).succ = UInt256.ofNat 4804
  decide

/-- The trace endpoint is exactly the scanner's atState presentation. -/
theorem prepared_atState (input : ByteArray) (rho : List UInt256) :
    prepared input rho = atState (prepared input rho) 4804 rho := by
  simp only [prepared, copied, beforeCopy, atState]
  rfl

@[simp] theorem prepared_stack (input : ByteArray) (rho : List UInt256) :
    (prepared input rho).stack = rho := rfl

@[simp] theorem prepared_activeWords (input : ByteArray) (rho : List UInt256) :
    (prepared input rho).activeWords = UInt256.ofNat 1 := rfl

@[simp] theorem prepared_memory (input : ByteArray) (rho : List UInt256) :
    (prepared input rho).memory = MachineState.writeBytes ByteArray.empty
      (MachineState.readPadded submissionBytecode (source input).toNat 20) 12 := by
  simp only [prepared, copied, beforeCopy, atState, base, initialState]

@[simp] theorem prepared_memory_size (input : ByteArray) (rho : List UInt256) :
    (prepared input rho).memory.size = 32 := by
  rw [prepared_memory, MachineState.writeBytes_size]
  simp [Memory.readPadded_size]

@[simp] theorem prepared_code (input : ByteArray) (rho : List UInt256) :
    (prepared input rho).executionEnv.code = Artifact.submissionArtifact.code := rfl

@[simp] theorem prepared_input (input : ByteArray) (rho : List UInt256) :
    (prepared input rho).executionEnv.calldata = input := rfl

@[simp] theorem prepared_input_size (input : ByteArray) (rho : List UInt256) :
    (prepared input rho).executionEnv.calldata.size = input.size := rfl

@[simp] theorem prepared_fork (input : ByteArray) (rho : List UInt256) :
    (prepared input rho).fork = .Osaka := rfl

@[simp] theorem prepared_run (input : ByteArray) (rho : List UInt256) :
    (prepared input rho).halt = .Running := rfl

@[simp] theorem prepared_callStack (input : ByteArray) (rho : List UInt256) :
    (prepared input rho).callStack = [] := rfl

theorem prepared_np (input : ByteArray) (rho : List UInt256) :
    Precompile.isPrecompileWithConfig (prepared input rho).executionEnv.precompileConfig
      (prepared input rho).executionEnv.fork (prepared input rho).executionEnv.codeAddr = false :=
  deployAddress_not_precompile

theorem source_environment (input : ByteArray) (rho : List UInt256) :
    source input = selected (UInt256.ofNat (prepared input rho).executionEnv.code.size)
      (prepared input rho).executionEnv.calldata.size := rfl

@[simp] theorem atState_prepared_memory (input : ByteArray) (rho : List UInt256)
    (pc : Nat) (stack : List UInt256) :
    (atState (prepared input rho) pc stack).memory = (prepared input rho).memory := rfl

@[simp] theorem atState_prepared_memory_size (input : ByteArray) (rho : List UInt256)
    (pc : Nat) (stack : List UInt256) :
    (atState (prepared input rho) pc stack).memory.size = 32 :=
  prepared_memory_size input rho

@[simp] theorem atState_prepared_activeWords (input : ByteArray) (rho : List UInt256)
    (pc : Nat) (stack : List UInt256) :
    (atState (prepared input rho) pc stack).activeWords = UInt256.ofNat 1 := rfl

@[simp] theorem atState_prepared_input (input : ByteArray) (rho : List UInt256)
    (pc : Nat) (stack : List UInt256) :
    (atState (prepared input rho) pc stack).executionEnv.calldata = input := rfl

/-- An incoming serializer stack is irrelevant once the loop replaces it. -/
theorem atState_prepared_stack_irrel (input : ByteArray) (saved rho : List UInt256)
    (pc : Nat) (stack : List UInt256) :
    atState (prepared input saved) pc stack = atState (prepared input rho) pc stack := rfl

private theorem code_bound : Artifact.submissionArtifact.code.size < 2^256 := by
  change submissionBytecode.size < 2^256
  rw [referenceBytecode_size]
  decide

/- Standalone certificates: no dependency on the old, late-copy return sites. -/
namespace prefixSite
abbrev template : List Instr := RecognitionSelectorRaw.prefixTemplate
theorem actual_slice :
    (Artifact.submissionArtifact.instructions.drop 3523).take template.length = template := by rfl

def site : GenericRoundSite Artifact.submissionArtifact .Osaka template :=
  StackSiteBuilder.ofSlice template 3523 actual_slice
    (by change 3523 + template.length ≤ Artifact.submissionInstructions.length
        rw [Artifact.referenceInstructions_count]; decide)
    code_bound (StackRoundData.templateWellFormed_mem (instructions := template) (by decide)) (by decide)

theorem site_pc : site.startPC = UInt256.ofNat 4786 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 3523) = UInt256.ofNat 4786
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide

theorem end_pc : pcAfter (UInt256.ofNat 4786) template = UInt256.ofNat 4803 := by decide

theorem form : ∀ instruction ∈ template.dropLast, RecognitionLift.Advances instruction :=
  RecognitionLift.advancesAll_sound _ (by decide)
end prefixSite

namespace finishSite
abbrev template : List Instr := RecognitionSelectorRaw.finish
theorem actual_slice :
    (Artifact.submissionArtifact.instructions.drop 3735).take template.length = template := by rfl

def site : GenericRoundSite Artifact.submissionArtifact .Osaka template :=
  StackSiteBuilder.ofSlice template 3735 actual_slice
    (by change 3735 + template.length ≤ Artifact.submissionInstructions.length
        rw [Artifact.referenceInstructions_count]; decide)
    code_bound (StackRoundData.templateWellFormed_mem (instructions := template) (by decide)) (by decide)

theorem site_pc : site.startPC = UInt256.ofNat 5571 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 3735) = UInt256.ofNat 5571
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide

theorem end_pc : pcAfter (UInt256.ofNat 5571) template = UInt256.ofNat 5573 := by decide

theorem form : ∀ instruction ∈ template.dropLast, RecognitionLift.Advances instruction :=
  RecognitionLift.advancesAll_sound _ (by decide)
end finishSite

private theorem copy_decoded (input : ByteArray) (rho : List UInt256) :
    (beforeCopy input rho).decodedOp = some .CODECOPY := by
  have hd := Artifact.submissionArtifact.decodeAt_op_index 3534 .CODECOPY
    (by rfl) (by decide) trivial
  apply Artifact.submissionArtifact.state_decodedOp_of (beforeCopy input rho) 3534
    rfl _ .CODECOPY none hd (by rfl)
  change (UInt256.ofNat 4803).toNat = Artifact.submissionArtifact.instructionPC 3534
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide

/-- Only prefix + CODECOPY: the next instruction is the scanner initializer. -/
def gasSteps_prepare (input : ByteArray) (rho : List UInt256) (hcap : rho.length ≤ 990) :
    GasSteps (atState (base input) 4786 rho) (prepared input rho) := by
  have hp : runInstrSeq prefixSite.template (atState (base input) 4786 rho) =
      some (beforeCopy input rho) := by
    have h := run_prefix (base input) (UInt256.ofNat 4786) rho (by omega) rfl
    simpa only [prefixSite.end_pc, beforeCopy, atState, source, base, initialState] using h
  have gp := RecognitionLift.gasSteps_of_raw prefixSite.site
    (atState (base input) 4786 rho) (beforeCopy input rho)
    (show (base input).executionEnv.code = Artifact.submissionArtifact.code from rfl)
    (show (base input).fork = .Osaka from rfl)
    (show (base input).halt = .Running from rfl)
    deployAddress_not_precompile prefixSite.site_pc.symm prefixSite.form hp
  have hac : (beforeCopy input rho).activeWordsAfterUInt256 12 20 = UInt256.ofNat 1 := by
    simp [State.activeWordsAfterUInt256, beforeCopy, atState, base, initialState,
      Word.word_toNat_ofNat]
    rfl
  have gc := Codecopy.step 12 (source input) 20 rho (copy_decoded input rho) rfl
    (by change (12 :: source input :: 20 :: rho).length + 0 ≤ 1024 + 3; simp; omega)
    rfl deployAddress_not_precompile
  apply gp.trans
  simpa only [prepared, copied, hac,
    show (beforeCopy input rho).memory = ByteArray.empty from rfl,
    show (12 : UInt256).toNat = 12 from rfl,
    show (20 : UInt256).toNat = 20 from rfl] using gc

private theorem size_decoded (input : ByteArray) (saved rho : List UInt256) :
    (atState (prepared input saved) 5570 rho).decodedOp = some .MSIZE := by
  have hd := Artifact.submissionArtifact.decodeAt_op_index 3734 .MSIZE
    (by rfl) (by decide) trivial
  apply Artifact.submissionArtifact.state_decodedOp_of
    (atState (prepared input saved) 5570 rho) 3734 rfl _ .MSIZE none hd (by rfl)
  change (UInt256.ofNat 5570).toNat = Artifact.submissionArtifact.instructionPC 3734
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide

/-- The recognizer may replace the entire stack; only the prepared memory matters. -/
def gasSteps_return (input : ByteArray) (saved rho : List UInt256) (hcap : rho.length ≤ 990) :
    GasSteps (atState (prepared input saved) 5570 rho) (output input rho) := by
  have gs := Msize.step (size_decoded input saved rho)
    (by change rho.length < 1024; omega) rfl deployAddress_not_precompile
  have hf : runInstrSeq finishSite.template
      (atState (prepared input saved) 5571 (32 :: rho)) =
      some (RecognitionSelectorRaw.returned (prepared input saved) (UInt256.ofNat 5571) rho) :=
    run_finish (prepared input saved) (UInt256.ofNat 5571) rho (by omega) rfl
  have gf := RecognitionLift.gasSteps_of_raw finishSite.site
    (atState (prepared input saved) 5571 (32 :: rho))
    (RecognitionSelectorRaw.returned (prepared input saved) (UInt256.ofNat 5571) rho)
    (prepared_code input saved) (prepared_fork input saved) (prepared_run input saved)
    (prepared_np input saved) finishSite.site_pc.symm finishSite.form hf
  have hpc : (UInt256.ofNat 5570).succ = UInt256.ofNat 5571 := by decide
  have gs' : GasSteps (atState (prepared input saved) 5570 rho)
      (atState (prepared input saved) 5571 (32 :: rho)) := by
    simpa only [atState, prepared_activeWords, Word.word_toNat_ofNat,
      Word.literal_eq_ofNat, hpc,
      show (1 : Nat) % 2^256 = 1 from by decide, Nat.mul_one] using gs
  have gout : RecognitionSelectorRaw.returned (prepared input saved) (UInt256.ofNat 5571) rho =
      output input rho := rfl
  exact gs'.trans (gout ▸ gf)

@[simp] theorem output_halt (input : ByteArray) (rho : List UInt256) :
    (output input rho).halt = .Returned := rfl

@[simp] theorem output_callStack (input : ByteArray) (rho : List UInt256) :
    (output input rho).callStack = [] := rfl

private theorem selected_read (input : ByteArray) (hn : RecognitionAccumulator.Allowed input.size) :
    MachineState.readPadded submissionBytecode (source input).toNat 20 =
      MachineState.readPadded RecognitionDigest.payload (280 - 20 * ((14357627 / input.size) % 16)) 20 := by
  unfold source
  rw [referenceBytecode_size]
  exact J2Payload.read_selected input.size hn

/-- The digest stored by preparation persists through any loop pc/stack updates. -/
theorem prepared_digest (input : ByteArray) (rho : List UInt256)
    (hn : RecognitionAccumulator.Allowed input.size) :
    (prepared input rho).memory = RecognitionDigest.paddedDigest input.size :=
  copied_memory (beforeCopy input rho) (source input) rho input.size hn (selected_read input hn)

theorem atState_prepared_digest (input : ByteArray) (rho : List UInt256)
    (pc : Nat) (stack : List UInt256) (hn : RecognitionAccumulator.Allowed input.size) :
    (atState (prepared input rho) pc stack).memory = RecognitionDigest.paddedDigest input.size :=
  prepared_digest input rho hn

theorem output_spec (input : ByteArray) (rho : List UInt256)
    (hn : RecognitionAccumulator.Allowed input.size)
    (hz : J2Accumulator.resultAcc input input.size = 0) :
    (output input rho).hReturn = spec input := by
  change MachineState.readPadded (prepared input rho).memory 0 32 = spec input
  rw [prepared_digest input rho hn, ← digest_size input.size hn,
    Memory.readPadded_zero_size]
  exact (RecognitionDigest.accepted_spec input input.size hn rfl
    ((RecognitionAccumulator.resultAcc_zero_iff _ _ hn rfl).mpr
      ((J2Accumulator.resultAcc_zero_iff _ _ hn rfl).mp hz))).symm

/-- The successful suffix is correct for every sufficiently large gas supply.
This is local to the prepared state; reaching the recognizer's hit remains the
responsibility of the caller. -/
theorem return_correct (input : ByteArray) (saved rho : List UInt256)
    (hcap : rho.length ≤ 990) (hn : RecognitionAccumulator.Allowed input.size)
    (hz : J2Accumulator.resultAcc input input.size = 0) :
    ∃ g₀ : Nat, ∀ gas : Nat, g₀ ≤ gas →
      Eval (withGas (atState (prepared input saved) 5570 rho) gas)
        (.returned (spec input)) := by
  let trace := gasSteps_return input saved rho hcap
  refine ⟨trace.cost, fun gas hgas => ?_⟩
  have heval := eval_of_steps (trace.trace gas hgas) (by
    simp [withGas, State.isDone, State.isHalted, State.isRunning,
      output_halt, output_callStack])
  rw [State.toResult_returned _ (by simp [withGas])] at heval
  change Eval (withGas (atState (prepared input saved) 5570 rho) gas)
    (.returned (output input rho).hReturn) at heval
  simpa only [output_spec input rho hn hz] using heval

#print axioms gasSteps_prepare
#print axioms gasSteps_return
#print axioms output_spec
#print axioms return_correct
end Challenge.Ripemd160.Submission.Proofs.Bytecode.EarlySerializeReturn
