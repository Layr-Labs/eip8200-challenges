import Challenge.Ripemd160.Submission.Proofs.Bytecode.RecognitionPaddedResult
import Challenge.Ripemd160.ProofSupport.InitialState
import Challenge.Ripemd160.Submission.Proofs.Bytecode.J2Moves
import Challenge.Ripemd160.Submission.Proofs.Bytecode.J2Accumulator
import Challenge.Ripemd160.Submission.Proofs.Bytecode.DirectDigestRaw
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
  DirectDigestRaw.selected (UInt256.ofNat 8191) input.size

def loaded (input : ByteArray) (rho : List UInt256) : State :=
  {base input with pc := source input,stack := rho}

def prepared (input : ByteArray) (rho : List UInt256) : State :=
  {base input with
    pc := UInt256.add (UInt256.ofNat 24) (source input)
    stack := rho
    activeWords := UInt256.ofNat 1
    memory := MachineState.writeBytes ByteArray.empty
      (Data.Bytes.natToBytesPadded (RecognitionDigest.paddedDigestWord input.size).toNat 32) 0}

def finishPC (i : Fin 13) : Nat := ReverseLiteralScan.returnPC i + 1

/-- The final return uses the prepared memory, not an unrelated running state. -/
def output (input : ByteArray) (rho : List UInt256) (i : Fin 13) : State :=
  RecognitionSelectorRaw.returned (prepared input rho) (UInt256.ofNat (finishPC i)) rho

theorem prepared_atState (input : ByteArray) (rho : List UInt256) (i : Fin 13)
    (hn : input.size = ReverseLiteralScan.nval i) :
    prepared input rho = atState (prepared input rho) (ReverseLiteralScan.tailPC i) rho := by
  have ht : UInt256.add (UInt256.ofNat 24) (source input) = UInt256.ofNat (ReverseLiteralScan.tailPC i) := by
    unfold source
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
      (Data.Bytes.natToBytesPadded (RecognitionDigest.paddedDigestWord input.size).toNat 32) 0 := rfl

@[simp] theorem prepared_memory_size (input : ByteArray) (rho : List UInt256) :
    (prepared input rho).memory.size = 32 := by
  rw [prepared_memory, MachineState.writeBytes_size]
  simp [YulEvmCompiler.BytesLemmas.natToBytesPadded_size]

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
    source input = DirectDigestRaw.selected (UInt256.ofNat (prepared input rho).executionEnv.code.size)
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

def storeIndex : Fin 13 → Nat
 | ⟨0, _⟩ => 3612
 | ⟨1, _⟩ => 3478
 | ⟨2, _⟩ => 4160
 | ⟨3, _⟩ => 3662
 | ⟨4, _⟩ => 4214
 | ⟨5, _⟩ => 3594
 | ⟨6, _⟩ => 4196
 | ⟨7, _⟩ => 4675
 | ⟨8, _⟩ => 3722
 | ⟨9, _⟩ => 4277
 | ⟨10, _⟩ => 3694
 | ⟨11, _⟩ => 4972
 | ⟨12, _⟩ => 3750

namespace storeSite
abbrev template (i : Fin 13) : List Instr :=
  DirectDigestRaw.storeTemplate (RecognitionDigest.paddedDigestWord (ReverseLiteralScan.nval i))
theorem actual_slice (i : Fin 13) :
    (Artifact.submissionArtifact.instructions.drop (storeIndex i)).take (template i).length = template i := by
  fin_cases i <;> rfl

def site (i : Fin 13) : GenericRoundSite Artifact.submissionArtifact .Osaka (template i) :=
  StackSiteBuilder.ofSlice (template i) (storeIndex i) (actual_slice i)
    (by change storeIndex i+(template i).length ≤ Artifact.submissionInstructions.length
        rw [Artifact.referenceInstructions_count]; fin_cases i <;> decide)
    code_bound (StackRoundData.templateWellFormed_mem (instructions := template i) (by fin_cases i <;> decide))
    (by fin_cases i <;> decide)

theorem site_pc (i : Fin 13) : (site i).startPC =
    DirectDigestRaw.selected (UInt256.ofNat 8191) (ReverseLiteralScan.nval i) := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC (storeIndex i)) = _
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; fin_cases i <;> decide

theorem valid (i : Fin 13) : Decode.isValidJumpDest Artifact.submissionArtifact.code
    (DirectDigestRaw.selected (UInt256.ofNat 8191) (ReverseLiteralScan.nval i)).toNat = true := by
  have hp : Artifact.submissionArtifact.instructionPC (storeIndex i) =
      (DirectDigestRaw.selected (UInt256.ofNat 8191) (ReverseLiteralScan.nval i)).toNat := by
    rw [ArtifactByteLength.instructionPC_eq_byteLength]; fin_cases i <;> decide
  have h := Artifact.submissionArtifact.isValidJumpDest_index (storeIndex i) (by fin_cases i <;> rfl)
  rw [hp] at h
  exact h

theorem form (i : Fin 13) : ∀ instruction ∈ (template i).dropLast, RecognitionLift.Advances instruction :=
  RecognitionLift.advancesAll_sound _ (by fin_cases i <;> decide)
end storeSite

def gasSteps_prepare_loaded (input : ByteArray) (rho : List UInt256) (hcap : rho.length ≤ 990)
    (i : Fin 13) (hn : input.size = ReverseLiteralScan.nval i) :
    GasSteps (loaded input rho) (prepared input rho) := by
  have hac : (base input).activeWordsAfterUInt256 0 32 = UInt256.ofNat 1 := by
    simp [State.activeWordsAfterUInt256,base,initialState,Word.word_toNat_ofNat]
    rfl
  have hr := DirectDigestRaw.run_store (base input) (source input)
    (RecognitionDigest.paddedDigestWord input.size) rho hcap rfl
  have he : DirectDigestRaw.stored (base input) (source input)
      (RecognitionDigest.paddedDigestWord input.size) rho = prepared input rho := by
    simp only [DirectDigestRaw.stored,prepared,hac,DirectDigestRaw.store_pc]
    rfl
  have hr' : runInstrSeq (storeSite.template i) (loaded input rho) = some (prepared input rho) := by
    rw [he] at hr
    simpa only [storeSite.template,hn,loaded] using hr
  have gj := RecognitionLift.gasSteps_of_raw (storeSite.site i)
    (loaded input rho) (prepared input rho) rfl rfl rfl deployAddress_not_precompile
    (by change DirectDigestRaw.selected (UInt256.ofNat 8191) input.size = (storeSite.site i).startPC
        rw [hn]; exact (storeSite.site_pc i).symm)
    (storeSite.form i) hr'
  exact gj

def returnIndex : Fin 13 → Nat
 | ⟨0, _⟩ => 3622
 | ⟨1, _⟩ => 3488
 | ⟨2, _⟩ => 4170
 | ⟨3, _⟩ => 3677
 | ⟨4, _⟩ => 4229
 | ⟨5, _⟩ => 3609
 | ⟨6, _⟩ => 4211
 | ⟨7, _⟩ => 4695
 | ⟨8, _⟩ => 3747
 | ⟨9, _⟩ => 4302
 | ⟨10, _⟩ => 3719
 | ⟨11, _⟩ => 5017
 | ⟨12, _⟩ => 3815

def finishIndex (i : Fin 13) : Nat := returnIndex i + 1

namespace finishSite
abbrev template : List Instr := RecognitionSelectorRaw.finish

theorem actual_slice (i : Fin 13) :
    (Artifact.submissionArtifact.instructions.drop (finishIndex i)).take template.length = template := by
  fin_cases i <;> rfl

def site (i : Fin 13) : GenericRoundSite Artifact.submissionArtifact .Osaka template :=
  StackSiteBuilder.ofSlice template (finishIndex i) (actual_slice i)
    (by change finishIndex i+template.length ≤ Artifact.submissionInstructions.length
        rw [Artifact.referenceInstructions_count]; fin_cases i <;> decide)
    code_bound (StackRoundData.templateWellFormed_mem (instructions := template) (by decide)) (by decide)

theorem site_pc (i : Fin 13) : (site i).startPC = UInt256.ofNat (finishPC i) := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC (finishIndex i)) = _
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; fin_cases i <;> decide

theorem form : ∀ instruction ∈ template.dropLast, RecognitionLift.Advances instruction :=
  RecognitionLift.advancesAll_sound _ (by decide)
end finishSite

private theorem size_decoded (input : ByteArray) (saved rho : List UInt256) (i : Fin 13) :
    (atState (prepared input saved) (ReverseLiteralScan.returnPC i) rho).decodedOp = some .MSIZE := by
  have hd := Artifact.submissionArtifact.decodeAt_op_index (returnIndex i) .MSIZE
    (by fin_cases i <;> rfl) (by decide) trivial
  apply Artifact.submissionArtifact.state_decodedOp_of
    (atState (prepared input saved) (ReverseLiteralScan.returnPC i) rho) (returnIndex i) rfl _ .MSIZE none hd (by rfl)
  change (UInt256.ofNat (ReverseLiteralScan.returnPC i)).toNat = Artifact.submissionArtifact.instructionPC (returnIndex i)
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; fin_cases i <;> decide

def gasSteps_return (input : ByteArray) (saved rho : List UInt256) (hcap : rho.length ≤ 990) (i : Fin 13) :
    GasSteps (atState (prepared input saved) (ReverseLiteralScan.returnPC i) rho) (output input rho i) := by
  have gs := Msize.step (size_decoded input saved rho i)
    (by change rho.length < 1024; omega) rfl deployAddress_not_precompile
  have hf : runInstrSeq finishSite.template
      (atState (prepared input saved) (ReverseLiteralScan.returnPC i+1) (32 :: rho)) =
      some (RecognitionSelectorRaw.returned (prepared input saved) (UInt256.ofNat (ReverseLiteralScan.returnPC i+1)) rho) :=
    run_finish (prepared input saved) (UInt256.ofNat (ReverseLiteralScan.returnPC i+1)) rho (by omega) rfl
  have hfinish : finishPC i = ReverseLiteralScan.returnPC i+1 := by simp [finishPC]
  have gf := RecognitionLift.gasSteps_of_raw (finishSite.site i)
    (atState (prepared input saved) (ReverseLiteralScan.returnPC i+1) (32 :: rho))
    (RecognitionSelectorRaw.returned (prepared input saved) (UInt256.ofNat (ReverseLiteralScan.returnPC i+1)) rho)
    (prepared_code input saved) (prepared_fork input saved) (prepared_run input saved)
    (prepared_np input saved) (by rw [finishSite.site_pc,hfinish]; rfl) finishSite.form hf
  have hpc : (UInt256.ofNat (ReverseLiteralScan.returnPC i)).succ = UInt256.ofNat (ReverseLiteralScan.returnPC i+1) := by
    fin_cases i <;> decide
  have gs' : GasSteps (atState (prepared input saved) (ReverseLiteralScan.returnPC i) rho)
      (atState (prepared input saved) (ReverseLiteralScan.returnPC i+1) (32 :: rho)) := by
    simpa only [atState, prepared_activeWords, Word.word_toNat_ofNat,
      Word.literal_eq_ofNat, hpc,
      show (1 : Nat) % 2^256 = 1 from by decide, Nat.mul_one] using gs
  have he : RecognitionSelectorRaw.returned (prepared input saved)
      (UInt256.ofNat (ReverseLiteralScan.returnPC i+1)) rho = output input rho i := by
    simp only [output,hfinish,RecognitionSelectorRaw.returned,prepared,base]
    rfl
  rw [he] at gf
  exact gs'.trans gf

@[simp] theorem output_halt (input : ByteArray) (rho : List UInt256) (i : Fin 13) :
    (output input rho i).halt = .Returned := rfl

@[simp] theorem output_callStack (input : ByteArray) (rho : List UInt256) (i : Fin 13) :
    (output input rho i).callStack = [] := rfl

private theorem write_empty (b : ByteArray) : MachineState.writeBytes ByteArray.empty b 0 = b := by
  apply ByteArray.ext_getElem
  · rw [MachineState.writeBytes_size]
    split
    · next h => simpa using h.symm
    · simp
  · intro i hi hj
    rw [← Memory.getD0_eq_getElem _ _ hi, ← Memory.getD0_eq_getElem _ _ hj,
      MachineState.writeBytes_getElem?_getD]
    simp only [Nat.zero_le, Nat.zero_add, true_and, Nat.sub_zero, if_pos hj]

private theorem word_bytes (n : Nat) (hn : RecognitionAccumulator.Allowed n) :
    Data.Bytes.natToBytesPadded (RecognitionDigest.paddedDigestWord n).toNat 32 = RecognitionDigest.paddedDigest n := by
  rcases hn with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  all_goals rw [Memory.natToBytesPadded_eq_natToBE]; decide

/-- Canonical full-word stores, proved independently of CODECOPY payload lookup. -/
theorem prepared_digest (input : ByteArray) (rho : List UInt256)
    (hn : RecognitionAccumulator.Allowed input.size) :
    (prepared input rho).memory = RecognitionDigest.paddedDigest input.size := by
  rw [prepared_memory,write_empty,word_bytes input.size hn]

theorem atState_prepared_digest (input : ByteArray) (rho : List UInt256)
    (pc : Nat) (stack : List UInt256) (hn : RecognitionAccumulator.Allowed input.size) :
    (atState (prepared input rho) pc stack).memory = RecognitionDigest.paddedDigest input.size :=
  prepared_digest input rho hn

theorem output_spec (input : ByteArray) (rho : List UInt256) (i : Fin 13)
    (hn : RecognitionAccumulator.Allowed input.size)
    (hz : J2Accumulator.resultAcc input input.size = 0) :
    (output input rho i).hReturn = spec input := by
  change MachineState.readPadded (prepared input rho).memory 0 32 = spec input
  rw [prepared_digest input rho hn, ← digest_size input.size hn,
    Memory.readPadded_zero_size]
  exact (RecognitionDigest.accepted_spec input input.size hn rfl
    ((RecognitionAccumulator.resultAcc_zero_iff _ _ hn rfl).mpr
      ((J2Accumulator.resultAcc_zero_iff _ _ hn rfl).mp hz))).symm

#print axioms gasSteps_prepare_loaded
#print axioms gasSteps_return
#print axioms output_spec
end Challenge.Ripemd160.Submission.Proofs.Bytecode.ReverseSerializeReturn
