import Challenge.Ripemd160.Submission.Proofs.Bytecode.HoistedStoreEntry

set_option warningAsError true
set_option maxRecDepth 100000
set_option maxHeartbeats 12000000
set_option linter.unusedSimpArgs false
namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.HoistedStoreRetained
open EvmSemantics EvmSemantics.EVM YulEvmCompiler Challenge.EvmProof
open Challenge.Ripemd160
open StackRoundTrace StackRoundTemplate RetainedIntegration105 RetainedResultEdge112

inductive Piece | data | result | success

def template : Piece → List Instr
  | .data => literalTemplate ExactBindings.digest
  | .result => DirectLiteralRawV4.resultTemplate
  | .success => successTemplate

def index : Piece → Nat | .data => 5022 | .result => 5183 | .success => 5185
def pc : Piece → Nat | .data => 8157 | .result => 9416 | .success => 9420

theorem actual_slice (p : Piece) :
    (HoistedStoreArtifact.instructions.drop (index p)).take (template p).length = template p := by
  cases p <;> rfl

theorem bounds (p : Piece) :
    index p + (template p).length ≤ HoistedStoreArtifact.instructions.length := by
  rw [HoistedStoreArtifact.instruction_count]
  cases p <;> decide

def site (p : Piece) : GenericRoundSite HoistedStoreArtifact.artifact .Osaka (template p) :=
  StackSiteBuilder.ofSlice (template p) (index p) (actual_slice p) (bounds p)
    HoistedStoreSites.code_bound
    (StackRoundData.templateWellFormed_mem (by cases p <;> decide)) (by cases p <;> decide)

theorem site_pc (p : Piece) : (site p).startPC = UInt256.ofNat (pc p) := by
  change UInt256.ofNat (HoistedStoreArtifact.artifact.instructionPC (index p)) = _
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  cases p <;> decide

theorem form (p : Piece) : ∀ i ∈ (template p).dropLast, RecognitionLift.Advances i := by
  apply RecognitionLift.advancesAll_sound
  cases p <;> decide

def lift (p : Piece) (s t : State) (e : HoistedStoreSites.Env s) (rho : List UInt256)
    (h : runInstrSeq (template p) {s with pc := UInt256.ofNat (pc p), stack := rho} = some t) :
    GasSteps {s with pc := UInt256.ofNat (pc p), stack := rho} t :=
  RecognitionLift.gasSteps_of_raw (site p) _ _ e.code e.fork e.run e.np
    (site_pc p).symm (form p) h

def gasSteps_data (s : State) (rho : List UInt256) (e : HoistedStoreSites.Env s)
    (hs : rho.length ≤ 976) (ha : s.activeWords = UInt256.ofNat 0) :
    GasSteps {s with pc := UInt256.ofNat 8157, stack := MachineState.readWord s.executionEnv.calldata 0 :: rho}
      {(stored s ExactBindings.digest) with pc := UInt256.ofNat 9416, stack := retainedResult s.executionEnv.calldata :: rho} := by
  apply lift .data s _ e _
  have h := RetainedBridge111.run_actual_data s rho (by omega) e.run ha
  rw [RetainedBridge111.Candidate.actual_data_slice, RetainedBridge111.Candidate.literal_eq_template,
    data_end_pc] at h
  exact h

def gasSteps_return (s : State) (rho : List UInt256) (e : HoistedStoreSites.Env s)
    (hs : rho.length ≤ 976) (ha : s.activeWords = UInt256.ofNat 0)
    (hz : retainedResult s.executionEnv.calldata = 0) :
    GasSteps {s with pc := UInt256.ofNat 8157, stack := MachineState.readWord s.executionEnv.calldata 0 :: rho}
      (returned (stored s ExactBindings.digest) rho) := by
  have hd := gasSteps_data s rho e hs ha
  let w := stored s ExactBindings.digest
  have ew : HoistedStoreSites.Env w := ⟨e.code, e.fork, e.run, e.np⟩
  have hv : Decode.isValidJumpDest w.executionEnv.code 4785 = true := by
    rw [ew.code]; exact HoistedStoreSites.valid_cleanup
  have hr : GasSteps {w with pc := UInt256.ofNat 9416, stack := retainedResult s.executionEnv.calldata :: rho}
      {w with pc := UInt256.ofNat 9420, stack := rho} := by
    apply lift .result w _ ew _
    simpa only [template, pc, result_end_pc, hz, show (0 : UInt256).toNat = 0 by decide, if_true] using
      DirectLiteralRawV4.run_result w (UInt256.ofNat 9416) (retainedResult s.executionEnv.calldata) rho
        (by omega) e.run hv
  have ha1 : w.activeWords = UInt256.ofNat 1 := by
    simp [w, stored, State.activeWordsAfterUInt256, MachineState.activeWordsAfter, ha, Word.word_toNat_ofNat]
  have ht : GasSteps {w with pc := UInt256.ofNat 9420, stack := rho} (returned w rho) :=
    lift .success w _ ew rho (run_success w rho (by omega) e.run ha1)
  exact hd.trans (hr.trans ht)

def gasSteps_miss_copy (s : State) (rho : List UInt256) (e : HoistedStoreSites.Env s)
    (hs : rho.length ≤ 976) (ha : s.activeWords = UInt256.ofNat 0) (hmem : s.memory.size = 0)
    (hfit : s.executionEnv.calldata.size < 2 ^ 256) (hpos : 0 < s.executionEnv.calldata.size)
    (hz : retainedResult s.executionEnv.calldata ≠ 0) :
    GasSteps {s with pc := UInt256.ofNat 8157, stack := MachineState.readWord s.executionEnv.calldata 0 :: rho}
      (RetainedFallback114.copied s rho) := by
  have hd := gasSteps_data s rho e hs ha
  let w := stored s ExactBindings.digest
  have ew : HoistedStoreSites.Env w := ⟨e.code, e.fork, e.run, e.np⟩
  have hv : Decode.isValidJumpDest w.executionEnv.code 4785 = true := by
    rw [ew.code]; exact HoistedStoreSites.valid_cleanup
  have hn : (retainedResult s.executionEnv.calldata).toNat ≠ 0 := by
    intro h; exact hz (Word.word_ext h)
  have hr : GasSteps {w with pc := UInt256.ofNat 9416, stack := retainedResult s.executionEnv.calldata :: rho}
      {w with pc := UInt256.ofNat 4785, stack := rho} := by
    apply lift .result w _ ew _
    simpa only [template, pc, result_end_pc, if_neg hn] using
      DirectLiteralRawV4.run_result w (UInt256.ofNat 9416) (retainedResult s.executionEnv.calldata) rho
        (by omega) e.run hv
  have ha1 : w.activeWords = UInt256.ofNat 1 := by
    simp [w, stored, State.activeWordsAfterUInt256, MachineState.activeWordsAfter, ha, Word.word_toNat_ofNat]
  have hm32 : w.memory.size = 32 := by
    simp [w, stored, MachineState.writeBytes_size, BytesLemmas.natToBytesPadded_size, hmem]
  have hc := HoistedStoreEdges.gasSteps_cleanup w rho ew hs ha1
  have hp := HoistedStoreEdges.gasSteps_copy w rho ew hs hfit hpos hm32
  have eqcopy : RetainedFallback114.copied w rho = RetainedFallback114.copied s rho := by
    simp only [RetainedFallback114.copied, w, stored]
    rfl
  exact (hd.trans (hr.trans (hc.trans hp))).cast rfl eqcopy

#print axioms actual_slice
#print axioms gasSteps_return
#print axioms gasSteps_miss_copy
end Challenge.Ripemd160.Submission.Proofs.Bytecode.HoistedStoreRetained
