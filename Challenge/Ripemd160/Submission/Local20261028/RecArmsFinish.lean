import Challenge.Ripemd160.Submission.Local20261028.RecArmsScan
import Challenge.Ripemd160.Submission.Local20261028.RecGasCost
import Challenge.Ripemd160.Submission.Local20261028.RecEarlySerializeFallback
import Challenge.Ripemd160.Submission.Local20261028.ColdGenericFramedCorrect
import Challenge.Ripemd160.Submission.Proofs.Bytecode.RecognitionSelectorResult
set_option warningAsError true
set_option linter.unusedSimpArgs false
set_option maxRecDepth 100000
set_option maxHeartbeats 16000000
set_option linter.unusedSimpArgs false

/-!
# Arm outcomes: digest return on a match, generic compressor on a miss
-/

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.Local20261028.Control.Arms.Finish
open Challenge.Ripemd160 EvmSemantics EvmSemantics.EVM YulEvmCompiler Challenge.EvmProof
open Challenge.Ripemd160.Submission.Proofs.Bytecode
open StackRoundTrace StackRoundTemplate J2Moves
open Arms.Scan

theorem run_finish (input : ByteArray) (n pc : Nat) :
    ∃ t, runInstrSeq finishTemplate {prepared input n with pc := UInt256.ofNat pc, stack := []} = some t ∧
      t.halt = .Returned ∧ t.callStack = [] ∧ t.hReturn = MachineState.readPadded (digestMemory n) 0 32 :=
  ⟨_, rfl, rfl, rfl, rfl⟩

/-- A finish site turns a matched prepared state into a returned state. -/
theorem finish_gasSteps (input : ByteArray) (n pc : Nat)
    (site : GenericRoundSite Control.Artifact.submissionArtifact .Osaka finishTemplate)
    (hpc : site.startPC = UInt256.ofNat pc) :
    ∃ t, Nonempty (GasSteps {prepared input n with pc := UInt256.ofNat pc, stack := []} t) ∧
      t.halt = .Returned ∧ t.callStack = [] ∧ t.hReturn = MachineState.readPadded (digestMemory n) 0 32 := by
  obtain ⟨t, ht, h1, h2, h3⟩ := run_finish input n pc
  exact ⟨t, ⟨RecognitionLift.gasSteps_of_raw site _ t rfl rfl rfl deployAddress_not_precompile hpc.symm
    (RecognitionLift.advancesAll_sound _ (by decide)) ht⟩, h1, h2, h3⟩

def finishSiteAt (idx : Nat)
    (hslice : (Control.Artifact.submissionArtifact.instructions.drop idx).take finishTemplate.length = finishTemplate)
    (hbound : idx + finishTemplate.length ≤ Control.Artifact.submissionInstructions.length) :
    GenericRoundSite Control.Artifact.submissionArtifact .Osaka finishTemplate :=
  StackSiteBuilder.ofSlice finishTemplate idx hslice hbound
    (by rw [CandidateArtifact.code_size]; decide)
    (Control.StackRoundData.templateWellFormed_mem (instructions := finishTemplate) (by decide)) (by decide)

def finishSite0 := finishSiteAt 6179 (by rfl)
  (by rw [CandidateArtifact.instruction_count]; decide)
def finishSite1 := finishSiteAt 6315 (by rfl)
  (by rw [CandidateArtifact.instruction_count]; decide)
def finishSite2 := finishSiteAt 6302 (by rfl)
  (by rw [CandidateArtifact.instruction_count]; decide)

theorem finishSite0_pc : finishSite0.startPC = UInt256.ofNat 8244 := by
  change UInt256.ofNat (Control.Artifact.submissionArtifact.instructionPC 6179) = _
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide
theorem finishSite1_pc : finishSite1.startPC = UInt256.ofNat 8825 := by
  change UInt256.ofNat (Control.Artifact.submissionArtifact.instructionPC 6315) = _
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide
theorem finishSite2_pc : finishSite2.startPC = UInt256.ofNat 8758 := by
  change UInt256.ofNat (Control.Artifact.submissionArtifact.instructionPC 6302) = _
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide

/-! ## Digest -/

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

theorem digestMemory_eq (n : Nat) (hn : RecognitionAccumulator.Allowed n) :
    digestMemory n = RecognitionDigest.paddedDigest n := by
  rw [digestMemory, write_empty, word_bytes n hn]

theorem output_spec (input : ByteArray) (n : Nat) (hn : RecognitionAccumulator.Allowed n)
    (heq : input = RecognitionAccumulator.reference n) :
    MachineState.readPadded (digestMemory n) 0 32 = spec input := by
  rw [digestMemory_eq n hn, ← RecognitionSelectorResult.digest_size n hn, Memory.readPadded_zero_size,
    heq, RecognitionDigest.spec_reference n hn]

theorem of_returned (input : ByteArray) (t : State)
    (trace : GasSteps (initialState Control.submissionBytecode input 0) t)
    (hhalt : t.halt = .Returned) (hcall : t.callStack = [])
    (hout : t.hReturn = spec input) :
    ∃ g₀ : Nat, ∀ gas : Nat, g₀ ≤ gas →
      Eval (initialState Control.submissionBytecode input gas) (.returned (spec input)) := by
  refine ⟨trace.cost, fun gas hgas => ?_⟩
  have heval := eval_of_steps (trace.trace gas hgas) (by
    simp [withGas, State.isDone, State.isHalted, State.isRunning, hhalt, hcall])
  rw [State.toResult_returned _ (by simpa [withGas] using hhalt)] at heval
  change Eval (withGas (initialState Control.submissionBytecode input 0) gas)
    (.returned t.hReturn) at heval
  rw [hout] at heval
  simpa [Control.GasCost.withGas_initialState_zero] using heval

theorem result_zero (input : ByteArray) (n : Nat) (hn : RecognitionAccumulator.Allowed n)
    (hsize : input.size = n) (hz : (ZeroTailModel.result input n).toNat = 0) :
    input = RecognitionAccumulator.reference n := by
  apply (ZeroTailModel.result_zero_iff input n hn hsize).mp
  apply Word.word_ext
  exact hz

/-- A chained or one-word arm, once entered, yields the RIPEMD-160 answer. -/
theorem arm_correct (input : ByteArray) (hfit : CalldataFits input) (n : Nat)
    (hn : RecognitionAccumulator.Allowed n) (hsize : input.size = n) (rpc : Nat)
    (hpre : GasSteps (initialState Control.submissionBytecode input 0)
      {prepared input n with
        pc := if (ZeroTailModel.result input n).toNat = 0 then UInt256.ofNat rpc else UInt256.ofNat 8078,
        stack := []})
    (hfin : ∃ t, Nonempty (GasSteps {prepared input n with pc := UInt256.ofNat rpc, stack := []} t) ∧
      t.halt = .Returned ∧ t.callStack = [] ∧ t.hReturn = MachineState.readPadded (digestMemory n) 0 32) :
    ∃ g₀ : Nat, ∀ gas : Nat, g₀ ≤ gas →
      Eval (initialState Control.submissionBytecode input gas) (.returned (spec input)) := by
  have hpos : 0 < input.size := by
    have := RecognitionAccumulator.allowed_bounds n hn
    omega
  by_cases hz : (ZeroTailModel.result input n).toNat = 0
  · rw [if_pos hz] at hpre
    obtain ⟨t, ⟨gt⟩, h1, h2, h3⟩ := hfin
    apply of_returned input t (hpre.trans gt) h1 h2
    rw [h3]
    exact output_spec input n hn (result_zero input n hn hsize hz)
  · rw [if_neg hz] at hpre
    have gf := Control.EarlySerializeFallback.gasSteps_of_eq input hfit hpos
      {prepared input n with pc := UInt256.ofNat 8078, stack := []} (digestMemory n)
      (digestMemory_size n) [] (by simp) rfl
    exact Control.GenericFramedCorrect.correct input hfit hpos [] (by simp) (hpre.trans gf)

end Challenge.Ripemd160.Submission.Proofs.Bytecode.Local20261028.Control.Arms.Finish
