import Challenge.Ripemd160.Submission.Proofs.Bytecode.RecognitionPaddedResult
import Challenge.Ripemd160.ProofSupport.InitialState
import Challenge.Ripemd160.Submission.Proofs.Bytecode.J2Moves
import Challenge.Ripemd160.Submission.Proofs.Bytecode.J2Accumulator
import Challenge.Ripemd160.Submission.Proofs.Bytecode.J2Payload
import Challenge.Ripemd160.Submission.Proofs.Bytecode.CombinedSelectorRaw
import Challenge.Ripemd160.Submission.Proofs.Bytecode.StackSiteBuilder
import Challenge.Ripemd160.Submission.Proofs.Bytecode.StackRoundData
import Challenge.Ripemd160.Submission.Proofs.Bytecode.Artifact
import Challenge.Ripemd160.Submission.Proofs.Bytecode.ReverseLiteralScan

set_option warningAsError true
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false

/-! The early serializer copies the selected digest before the recognizer starts.
The loop changes only pc and stack.  Its successful exit therefore needs only
MSIZE, PUSH0, RETURN; in particular preparation must not execute MSIZE. -/
namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.ReverseSerializeReturn
open Challenge.Ripemd160 Challenge.EvmProof EvmSemantics EvmSemantics.EVM YulEvmCompiler
open J2Moves RecognitionSelectorRaw RecognitionSelectorResult StackRoundTrace StackRoundTemplate

/-- The zero-gas state used by all gas-parametric traces in this module. -/
def base (input : ByteArray) : State := initialState submissionBytecode input 0

def source (input : ByteArray) : UInt256 :=
  CombinedSelectorRaw.selected (UInt256.ofNat submissionBytecode.size) input.size

def beforeCopy (input : ByteArray) (rho : List UInt256) : State :=
  atState (base input) 4805 (0 :: source input :: 32 :: source input :: rho)

/-- State at the scanner initializer, after CODECOPY and before any MSIZE. -/
def copied (input : ByteArray) (rho : List UInt256) : State :=
  RecognitionPaddedResult.copied (beforeCopy input rho) (source input) (source input::rho)

def prepared (input : ByteArray) (rho : List UInt256) : State :=
  {copied input rho with pc:=UInt256.add (UInt256.ofNat 32) (source input), stack:=rho}

/-- The final return uses the prepared memory, not an unrelated running state. -/
def output (input : ByteArray) (rho : List UInt256) (i : Fin 14) : State :=
  RecognitionSelectorRaw.returned (prepared input rho) (UInt256.ofNat (ReverseLiteralScan.returnPC i+1)) rho

theorem prepared_atState (input : ByteArray) (rho : List UInt256) (i : Fin 14)
    (hn : input.size = ReverseLiteralScan.nval i) :
    prepared input rho = atState (prepared input rho) (ReverseLiteralScan.tailPC i) rho := by
  have ht : UInt256.add (UInt256.ofNat 32) (source input) = UInt256.ofNat (ReverseLiteralScan.tailPC i) := by
    unfold source
    simp only [CombinedSelectorRaw.selected]
    rw [hn]
    exact ReverseLiteralScan.source_target i
  simp only [prepared,atState]
  rw [ht]

@[simp] theorem prepared_stack (input : ByteArray) (rho : List UInt256) :
    (prepared input rho).stack = rho := rfl

@[simp] theorem prepared_activeWords (input : ByteArray) (rho : List UInt256) :
    (prepared input rho).activeWords = UInt256.ofNat 1 := rfl

@[simp] theorem prepared_memory (input : ByteArray) (rho : List UInt256) :
    (prepared input rho).memory = MachineState.writeBytes ByteArray.empty
      (MachineState.readPadded submissionBytecode (source input).toNat 32) 0 := by
  simp only [prepared, copied, RecognitionPaddedResult.copied, beforeCopy, atState, base, initialState]

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
    source input = CombinedSelectorRaw.selected (UInt256.ofNat (prepared input rho).executionEnv.code.size)
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
abbrev template : List Instr := CombinedSelectorRaw.prefixTemplate
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

theorem end_pc : pcAfter (UInt256.ofNat 4786) template = UInt256.ofNat 4805 := by decide

theorem form : ∀ instruction ∈ template.dropLast, RecognitionLift.Advances instruction :=
  RecognitionLift.advancesAll_sound _ (by decide)
end prefixSite

private theorem copy_decoded (input : ByteArray) (rho : List UInt256) :
    (beforeCopy input rho).decodedOp = some .CODECOPY := by
  have hd := Artifact.submissionArtifact.decodeAt_op_index 3531 .CODECOPY
    (by rfl) (by decide) trivial
  apply Artifact.submissionArtifact.state_decodedOp_of (beforeCopy input rho) 3531
    rfl _ .CODECOPY none hd (by rfl)
  change (UInt256.ofNat 4805).toNat = Artifact.submissionArtifact.instructionPC 3531
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide

namespace jumpSite
abbrev template : List Instr := CombinedSelectorRaw.jumpTemplate
theorem actual_slice :
    (Artifact.submissionArtifact.instructions.drop 3532).take template.length = template := by rfl

def site : GenericRoundSite Artifact.submissionArtifact .Osaka template :=
  StackSiteBuilder.ofSlice template 3532 actual_slice
    (by change 3532+template.length ≤ Artifact.submissionInstructions.length
        rw [Artifact.referenceInstructions_count]; decide)
    code_bound (StackRoundData.templateWellFormed_mem (instructions := template) (by decide)) (by decide)

theorem site_pc : site.startPC = UInt256.ofNat 4806 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 3532) = UInt256.ofNat 4806
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide

theorem form : ∀ instruction ∈ template.dropLast, RecognitionLift.Advances instruction :=
  RecognitionLift.advancesAll_sound _ (by decide)
end jumpSite

def gasSteps_prepare (input : ByteArray) (rho : List UInt256) (hcap : rho.length ≤ 990)
    (i : Fin 14) (hn : input.size = ReverseLiteralScan.nval i) :
    GasSteps (atState (base input) 4786 rho) (prepared input rho) := by
  have hp : runInstrSeq prefixSite.template (atState (base input) 4786 rho) =
      some (beforeCopy input rho) := by
    have h := CombinedSelectorRaw.run_prefix (base input) (UInt256.ofNat 4786) rho (by omega) rfl
    simpa only [prefixSite.end_pc, beforeCopy, atState, source, base, initialState] using h
  have gp := RecognitionLift.gasSteps_of_raw prefixSite.site
    (atState (base input) 4786 rho) (beforeCopy input rho)
    (show (base input).executionEnv.code = Artifact.submissionArtifact.code from rfl)
    (show (base input).fork = .Osaka from rfl)
    (show (base input).halt = .Running from rfl)
    deployAddress_not_precompile prefixSite.site_pc.symm prefixSite.form hp
  have hac : (beforeCopy input rho).activeWordsAfterUInt256 0 32 = UInt256.ofNat 1 := by
    simp [State.activeWordsAfterUInt256, beforeCopy, atState, base, initialState,
      Word.word_toNat_ofNat]
    rfl
  have gc := Codecopy.step 0 (source input) 32 (source input::rho) (copy_decoded input rho) rfl
    (by change (0 :: source input :: 32 :: source input :: rho).length + 0 ≤ 1024 + 3; simp; omega)
    rfl deployAddress_not_precompile
  have gc' : GasSteps (beforeCopy input rho) (copied input rho) := by
    simpa only [copied, RecognitionPaddedResult.copied, hac,
      show (beforeCopy input rho).memory = ByteArray.empty from rfl,
      show (0 : UInt256).toNat = 0 from rfl,
      show (32 : UInt256).toNat = 32 from rfl] using gc
  have ht : UInt256.add (UInt256.ofNat 32) (source input) = UInt256.ofNat (ReverseLiteralScan.tailPC i) := by
    unfold source
    simp only [CombinedSelectorRaw.selected]
    rw [hn]
    exact ReverseLiteralScan.source_target i
  have hv : Decode.isValidJumpDest (copied input rho).executionEnv.code
      (UInt256.add (UInt256.ofNat 32) (source input)).toNat = true := by
    rw [ht]
    change Decode.isValidJumpDest Artifact.submissionArtifact.code (UInt256.ofNat (ReverseLiteralScan.tailPC i)).toNat = true
    have hb : ReverseLiteralScan.tailPC i < 2^256 := by fin_cases i <;> decide
    rw [Word.word_toNat_ofNat,Nat.mod_eq_of_lt hb]
    exact ReverseLiteralScan.valid_tail i
  have hr := CombinedSelectorRaw.run_jump (copied input rho) (UInt256.ofNat 4806) (source input) rho hcap rfl hv
  have hr' : runInstrSeq jumpSite.template (copied input rho) = some (prepared input rho) := by
    simpa only [jumpSite.template,prepared,copied,RecognitionPaddedResult.copied,beforeCopy,atState,
      show (UInt256.ofNat 4805).succ=UInt256.ofNat 4806 from by decide] using hr
  have gj := RecognitionLift.gasSteps_of_raw jumpSite.site
    (copied input rho) (prepared input rho) rfl rfl rfl deployAddress_not_precompile
    jumpSite.site_pc.symm jumpSite.form hr'
  exact gp.trans (gc'.trans gj)

def returnIndex : Fin 14 → Nat
 | ⟨0, _⟩ => 4662
 | ⟨1, _⟩ => 3994
 | ⟨2, _⟩ => 4289
 | ⟨3, _⟩ => 5220
 | ⟨4, _⟩ => 4125
 | ⟨5, _⟩ => 4997
 | ⟨6, _⟩ => 5042
 | ⟨7, _⟩ => 4087
 | ⟨8, _⟩ => 3829
 | ⟨9, _⟩ => 5659
 | ⟨10, _⟩ => 5378
 | ⟨11, _⟩ => 5822
 | ⟨12, _⟩ => 5822
 | ⟨13, _⟩ => 5822

namespace finishSite
abbrev template : List Instr := RecognitionSelectorRaw.finish

theorem actual_slice (i : Fin 14) :
    (Artifact.submissionArtifact.instructions.drop (returnIndex i+1)).take template.length = template := by
  fin_cases i <;> rfl

def site (i : Fin 14) : GenericRoundSite Artifact.submissionArtifact .Osaka template :=
  StackSiteBuilder.ofSlice template (returnIndex i+1) (actual_slice i)
    (by change returnIndex i+1+template.length ≤ Artifact.submissionInstructions.length
        rw [Artifact.referenceInstructions_count]; fin_cases i <;> decide)
    code_bound (StackRoundData.templateWellFormed_mem (instructions := template) (by decide)) (by decide)

theorem site_pc (i : Fin 14) : (site i).startPC = UInt256.ofNat (ReverseLiteralScan.returnPC i+1) := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC (returnIndex i+1)) = _
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; fin_cases i <;> decide

theorem form : ∀ instruction ∈ template.dropLast, RecognitionLift.Advances instruction :=
  RecognitionLift.advancesAll_sound _ (by decide)
end finishSite

private theorem size_decoded (input : ByteArray) (saved rho : List UInt256) (i : Fin 14) :
    (atState (prepared input saved) (ReverseLiteralScan.returnPC i) rho).decodedOp = some .MSIZE := by
  have hd := Artifact.submissionArtifact.decodeAt_op_index (returnIndex i) .MSIZE
    (by fin_cases i <;> rfl) (by decide) trivial
  apply Artifact.submissionArtifact.state_decodedOp_of
    (atState (prepared input saved) (ReverseLiteralScan.returnPC i) rho) (returnIndex i) rfl _ .MSIZE none hd (by rfl)
  change (UInt256.ofNat (ReverseLiteralScan.returnPC i)).toNat = Artifact.submissionArtifact.instructionPC (returnIndex i)
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; fin_cases i <;> decide

def gasSteps_return (input : ByteArray) (saved rho : List UInt256) (hcap : rho.length ≤ 990) (i : Fin 14) :
    GasSteps (atState (prepared input saved) (ReverseLiteralScan.returnPC i) rho) (output input rho i) := by
  have gs := Msize.step (size_decoded input saved rho i)
    (by change rho.length < 1024; omega) rfl deployAddress_not_precompile
  have hf : runInstrSeq finishSite.template
      (atState (prepared input saved) (ReverseLiteralScan.returnPC i+1) (32 :: rho)) =
      some (RecognitionSelectorRaw.returned (prepared input saved) (UInt256.ofNat (ReverseLiteralScan.returnPC i+1)) rho) :=
    run_finish (prepared input saved) (UInt256.ofNat (ReverseLiteralScan.returnPC i+1)) rho (by omega) rfl
  have gf := RecognitionLift.gasSteps_of_raw (finishSite.site i)
    (atState (prepared input saved) (ReverseLiteralScan.returnPC i+1) (32 :: rho))
    (RecognitionSelectorRaw.returned (prepared input saved) (UInt256.ofNat (ReverseLiteralScan.returnPC i+1)) rho)
    (prepared_code input saved) (prepared_fork input saved) (prepared_run input saved)
    (prepared_np input saved) (finishSite.site_pc i).symm finishSite.form hf
  have hpc : (UInt256.ofNat (ReverseLiteralScan.returnPC i)).succ = UInt256.ofNat (ReverseLiteralScan.returnPC i+1) := by
    fin_cases i <;> decide
  have gs' : GasSteps (atState (prepared input saved) (ReverseLiteralScan.returnPC i) rho)
      (atState (prepared input saved) (ReverseLiteralScan.returnPC i+1) (32 :: rho)) := by
    simpa only [atState, prepared_activeWords, Word.word_toNat_ofNat,
      Word.literal_eq_ofNat, hpc,
      show (1 : Nat) % 2^256 = 1 from by decide, Nat.mul_one] using gs
  exact gs'.trans gf

@[simp] theorem output_halt (input : ByteArray) (rho : List UInt256) (i : Fin 14) :
    (output input rho i).halt = .Returned := rfl

@[simp] theorem output_callStack (input : ByteArray) (rho : List UInt256) (i : Fin 14) :
    (output input rho i).callStack = [] := rfl

private theorem selected_read (input : ByteArray) (hn : RecognitionAccumulator.Allowed input.size) :
    MachineState.readPadded submissionBytecode (source input).toNat 32 =
      RecognitionDigest.paddedDigest input.size := by
  unfold source
  rw [referenceBytecode_size]
  exact J2Payload.read_selected input.size hn

/-- The digest stored by preparation persists through any loop pc/stack updates. -/
theorem prepared_digest (input : ByteArray) (rho : List UInt256)
    (hn : RecognitionAccumulator.Allowed input.size) :
    (prepared input rho).memory = RecognitionDigest.paddedDigest input.size := by
  change (copied input rho).memory = _
  apply RecognitionPaddedResult.copied_memory
  simpa only [beforeCopy, atState, base, source,
    initialState, referenceBytecode_size] using J2Payload.read_selected input.size hn

theorem atState_prepared_digest (input : ByteArray) (rho : List UInt256)
    (pc : Nat) (stack : List UInt256) (hn : RecognitionAccumulator.Allowed input.size) :
    (atState (prepared input rho) pc stack).memory = RecognitionDigest.paddedDigest input.size :=
  prepared_digest input rho hn

theorem output_spec (input : ByteArray) (rho : List UInt256) (i : Fin 14)
    (hn : RecognitionAccumulator.Allowed input.size)
    (hz : J2Accumulator.resultAcc input input.size = 0) :
    (output input rho i).hReturn = spec input := by
  change MachineState.readPadded (prepared input rho).memory 0 32 = spec input
  rw [prepared_digest input rho hn, ← digest_size input.size hn,
    Memory.readPadded_zero_size]
  exact (RecognitionDigest.accepted_spec input input.size hn rfl
    ((RecognitionAccumulator.resultAcc_zero_iff _ _ hn rfl).mpr
      ((J2Accumulator.resultAcc_zero_iff _ _ hn rfl).mp hz))).symm

#print axioms gasSteps_prepare
#print axioms gasSteps_return
#print axioms output_spec
end Challenge.Ripemd160.Submission.Proofs.Bytecode.ReverseSerializeReturn
