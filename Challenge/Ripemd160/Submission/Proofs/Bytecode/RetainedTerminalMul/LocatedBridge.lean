import Challenge.Ripemd160.Submission.Proofs.Bytecode.RetainedTerminalMul.CandidateBindings
import Challenge.Ripemd160.Submission.Proofs.Bytecode.RetainedTerminalMul.Artifact
import Challenge.Ripemd160.Submission.Proofs.Bytecode.RetainedTerminalMul.CleanupBridge
import Challenge.Ripemd160.Submission.Proofs.Bytecode.RecognitionLift
import Challenge.Ripemd160.Submission.Proofs.Bytecode.StackSiteBuilder
import Challenge.Ripemd160.Submission.Proofs.Bytecode.StackRoundData
import Challenge.Ripemd160.Submission.Proofs.Bytecode.newArtifactByteLength
import Challenge.Ripemd160.Submission.Proofs.Bytecode.Low64RepeatMath

set_option warningAsError true
set_option maxRecDepth 100000
set_option maxHeartbeats 12000000
set_option linter.unusedSimpArgs false

/-! Exact located-path bridge for the isolated retained-word candidate.
This is a decoded-execution result, NOT a universal entry certificate. -/
namespace RetainedLocated113
open EvmSemantics EvmSemantics.EVM YulEvmCompiler Challenge.EvmProof
open Challenge.Ripemd160
open Challenge.Ripemd160.Submission.Proofs.Bytecode
open StackRoundTrace StackRoundTemplate RetainedIntegration105
open RetainedResultEdge112

inductive Piece
  | data | result | success | cleanup | anchor | repeat | genericDest

def template : Piece → List Instr
  | .data => literalTemplate ExactBindings.digest
  | .result => DirectLiteralRawV4.resultTemplate
  | .success => successTemplate
  | .cleanup => cleanupTemplate
  | .anchor => anchorTemplate
  | .repeat => repeatTemplate
  | .genericDest => [.op .JUMPDEST]

def index : Piece → Nat
  | .data => 5040 | .result => 5201 | .success => 5203 | .cleanup => 3475
  | .anchor => 11 | .repeat => 20 | .genericDest => 125

def pc : Piece → Nat
  | .data => 8157 | .result => 9416 | .success => 9420 | .cleanup => 4785
  | .anchor => 21 | .repeat => 48 | .genericDest => 245

theorem actual_slice (p : Piece) :
    (RetainedBridge111.Candidate.instructions.drop (index p)).take (template p).length = template p := by
  cases p with
  | data => exact RetainedBridge111.Candidate.actual_data_slice.trans RetainedBridge111.Candidate.literal_eq_template
  | result => exact RetainedResultEdge112.Candidate.actual_result_slice
  | success => exact actual_success_slice
  | cleanup => exact actual_cleanup_slice
  | anchor => exact actual_anchor_slice
  | «repeat» => exact actual_repeat_seed_slice
  | genericDest => rfl

theorem bounds (p : Piece) : index p + (template p).length ≤ RetainedBridge111.Candidate.instructions.length := by
  rw [RetainedBridge111.Candidate.instruction_count]
  cases p <;> decide

theorem wellFormed (p : Piece) : StackRoundData.TemplateWellFormed (template p) := by
  cases p <;> decide

theorem nonempty (p : Piece) : template p ≠ [] := by
  cases p <;> decide

theorem code_bound : RetainedBridge111.Candidate.artifact.code.size < 2 ^ 256 := by
  change RetainedBridge111.Candidate.candidateCode.size < 2 ^ 256
  rw [RetainedBridge111.Candidate.candidate_size]
  decide

def site (p : Piece) : GenericRoundSite RetainedBridge111.Candidate.artifact .Osaka (template p) :=
  StackSiteBuilder.ofSlice (template p) (index p) (actual_slice p) (bounds p)
    code_bound (StackRoundData.templateWellFormed_mem (wellFormed p)) (nonempty p)

theorem site_pc (p : Piece) : (site p).startPC = UInt256.ofNat (pc p) := by
  change UInt256.ofNat (RetainedBridge111.Candidate.artifact.instructionPC (index p)) = UInt256.ofNat (pc p)
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  cases p <;> decide

theorem form (p : Piece) : ∀ i ∈ (template p).dropLast, RecognitionLift.Advances i := by
  apply RecognitionLift.advancesAll_sound
  cases p <;> decide

structure Env (s : State) : Prop where
  code : s.executionEnv.code = RetainedBridge111.Candidate.candidateCode
  fork : s.fork = .Osaka
  run : s.halt = .Running
  np : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
    s.executionEnv.fork s.executionEnv.codeAddr = false

def lift (p : Piece) (s t : State) (e : Env s) (stack : List UInt256)
    (h : runInstrSeq (template p) {s with pc := UInt256.ofNat (pc p), stack := stack} = some t) :
    GasSteps {s with pc := UInt256.ofNat (pc p), stack := stack} t :=
  RecognitionLift.gasSteps_of_raw (site p) _ _ e.code e.fork e.run e.np (site_pc p).symm (form p) h

theorem valid_miss : Decode.isValidJumpDest RetainedBridge111.Candidate.candidateCode 4785 = true := by
  have hp : RetainedBridge111.Candidate.artifact.instructionPC 3475 = 4785 := by
    rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide
  have h := RetainedBridge111.Candidate.artifact.isValidJumpDest_index 3475 (by rfl)
  rw [hp] at h
  exact h

/-- The exact 161-instruction comparison slice now has decoded EVM GasSteps. -/
def gasSteps_data (s : State) (rho : List UInt256) (e : Env s)
    (hs : rho.length ≤ 980) (ha : s.activeWords = UInt256.ofNat 0) :
    GasSteps {s with pc := UInt256.ofNat 8157, stack := MachineState.readWord s.executionEnv.calldata 0 :: rho}
      {(stored s ExactBindings.digest) with pc := UInt256.ofNat 9416, stack := retainedResult s.executionEnv.calldata :: rho} := by
  apply lift .data s _ e _
  have h := RetainedBridge111.run_actual_data s rho hs e.run ha
  rw [RetainedBridge111.Candidate.actual_data_slice, RetainedBridge111.Candidate.literal_eq_template,
    data_end_pc] at h
  exact h

/-- Success edge through the actual JUMPI and RETURN, not an unlocated evaluator. -/
def gasSteps_return (s : State) (rho : List UInt256) (e : Env s)
    (hs : rho.length ≤ 980) (ha : s.activeWords = UInt256.ofNat 0)
    (hz : retainedResult s.executionEnv.calldata = 0) :
    GasSteps {s with pc := UInt256.ofNat 8157, stack := MachineState.readWord s.executionEnv.calldata 0 :: rho}
      (returned (stored s ExactBindings.digest) rho) := by
  have hd := gasSteps_data s rho e hs ha
  let w := stored s ExactBindings.digest
  have ew : Env w := ⟨e.code, e.fork, e.run, e.np⟩
  have hv : Decode.isValidJumpDest w.executionEnv.code 4785 = true := by rw [ew.code]; exact valid_miss
  have hr : GasSteps {w with pc := UInt256.ofNat 9416, stack := retainedResult s.executionEnv.calldata :: rho}
      {w with pc := UInt256.ofNat 9420, stack := rho} := by
    apply lift .result w _ ew _
    simpa only [template, pc, result_end_pc, hz, show (0 : UInt256).toNat = 0 by decide, if_true] using
      DirectLiteralRawV4.run_result w (UInt256.ofNat 9416) (retainedResult s.executionEnv.calldata) rho
        (by omega) e.run hv
  have ha1 : w.activeWords = UInt256.ofNat 1 := by
    simp [w, stored, State.activeWordsAfterUInt256, MachineState.activeWordsAfter, ha, Word.word_toNat_ofNat]
  have ht : GasSteps {w with pc := UInt256.ofNat 9420, stack := rho} (returned w rho) :=
    lift .success w _ ew rho (run_success w rho hs e.run ha1)
  exact hd.trans (hr.trans ht)

theorem valid_generic : Decode.isValidJumpDest RetainedBridge111.Candidate.candidateCode 245 = true := by
  have hp : RetainedBridge111.Candidate.artifact.instructionPC 125 = 245 := by
    rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide
  have h := RetainedBridge111.Candidate.artifact.isValidJumpDest_index 125 (by rfl)
  rw [hp] at h
  exact h

theorem valid_anchor : Decode.isValidJumpDest RetainedBridge111.Candidate.candidateCode 8157 = true := by
  have hp : RetainedBridge111.Candidate.artifact.instructionPC 5040 = 8157 := by
    rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide
  have h := RetainedBridge111.Candidate.artifact.isValidJumpDest_index 5040 (by rfl)
  rw [hp] at h
  exact h

theorem valid_repeat : Decode.isValidJumpDest RetainedBridge111.Candidate.candidateCode 9429 = true := by
  have hp : RetainedBridge111.Candidate.artifact.instructionPC 5212 = 9429 := by
    rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide
  have h := RetainedBridge111.Candidate.artifact.isValidJumpDest_index 5212 (by rfl)
  rw [hp] at h
  exact h

/-- All content-miss steps now execute the exact candidate, including cleanup. -/
def gasSteps_miss (s : State) (rho : List UInt256) (e : Env s)
    (hs : rho.length ≤ 980) (ha : s.activeWords = UInt256.ofNat 0)
    (hn : retainedResult s.executionEnv.calldata ≠ 0) :
    GasSteps {s with pc := UInt256.ofNat 8157, stack := MachineState.readWord s.executionEnv.calldata 0 :: rho}
      (cleared (stored s ExactBindings.digest) rho) := by
  have hd := gasSteps_data s rho e hs ha
  let w := stored s ExactBindings.digest
  have ew : Env w := ⟨e.code, e.fork, e.run, e.np⟩
  have hv : Decode.isValidJumpDest w.executionEnv.code 4785 = true := by rw [ew.code]; exact valid_miss
  have hg : Decode.isValidJumpDest w.executionEnv.code 245 = true := by rw [ew.code]; exact valid_generic
  have hnt : (retainedResult s.executionEnv.calldata).toNat ≠ 0 := by
    intro h; exact hn (Word.word_ext h)
  have hr : GasSteps {w with pc := UInt256.ofNat 9416, stack := retainedResult s.executionEnv.calldata :: rho}
      {w with pc := UInt256.ofNat 4785, stack := rho} := by
    apply lift .result w _ ew _
    simpa only [template, pc, result_end_pc, hnt, if_false] using
      DirectLiteralRawV4.run_result w (UInt256.ofNat 9416) (retainedResult s.executionEnv.calldata) rho
        (by omega) e.run hv
  have ha1 : w.activeWords = UInt256.ofNat 1 := by
    simp [w, stored, State.activeWordsAfterUInt256, MachineState.activeWordsAfter, ha, Word.word_toNat_ofNat]
  have ht : GasSteps {w with pc := UInt256.ofNat 4785, stack := rho} (cleared w rho) :=
    lift .cleanup w _ ew rho (run_cleanup w rho hs e.run ha1 hg)
  exact hd.trans (hr.trans ht)

/-- The taken entry anchor and success path are decoded execution of the candidate. -/
def gasSteps_anchor_return (s : State) (rho : List UInt256) (e : Env s)
    (hs : rho.length ≤ 980) (ha : s.activeWords = UInt256.ofNat 0)
    (hne : Low64RepeatMath.condition s.executionEnv.calldata ≠ 0)
    (hz : retainedResult s.executionEnv.calldata = 0) :
    GasSteps {s with pc := UInt256.ofNat 21, stack := rho}
      (returned (stored s ExactBindings.digest) rho) := by
  have hv : Decode.isValidJumpDest s.executionEnv.code 8157 = true := by rw [e.code]; exact valid_anchor
  have he := lift .anchor s _ e rho (run_anchor_taken s rho hs e.run hne hv)
  exact he.trans (gasSteps_return s rho e hs ha hz)

/-- The taken entry anchor and miss path restore the original frame at PC245. -/
def gasSteps_anchor_miss (s : State) (rho : List UInt256) (e : Env s)
    (hs : rho.length ≤ 980) (ha : s.activeWords = UInt256.ofNat 0)
    (hne : Low64RepeatMath.condition s.executionEnv.calldata ≠ 0)
    (hn : retainedResult s.executionEnv.calldata ≠ 0) :
    GasSteps {s with pc := UInt256.ofNat 21, stack := rho}
      (cleared (stored s ExactBindings.digest) rho) := by
  have hv : Decode.isValidJumpDest s.executionEnv.code 8157 = true := by rw [e.code]; exact valid_anchor
  have he := lift .anchor s _ e rho (run_anchor_taken s rho hs e.run hne hv)
  exact he.trans (gasSteps_miss s rho e hs ha hn)

/-- The repeated-word entry consumes neither the arbitrary frame nor the reference. -/
def gasSteps_anchor_repeat (s : State) (rho : List UInt256) (e : Env s)
    (hs : rho.length ≤ 980)
    (heq : KnownInputCompactState.referenceWord s.executionEnv.calldata = KnownInputData.fullWord) :
    GasSteps {s with pc := UInt256.ofNat 21, stack := rho}
      {s with pc := UInt256.ofNat 9429, stack :=
        [PcSeedRaw.seed s.executionEnv.calldata,
         KnownInputCompactState.referenceWord s.executionEnv.calldata] ++ rho} := by
  have hv : Decode.isValidJumpDest s.executionEnv.code 9429 = true := by rw [e.code]; exact valid_repeat
  have he := lift .anchor s _ e rho (run_anchor_fall s rho hs e.run heq)
  have hr := lift .repeat s _ e (MachineState.readWord s.executionEnv.calldata 0 :: rho)
    (run_repeat s rho hs e.run hv)
  exact he.trans hr

#print axioms gasSteps_miss
#print axioms gasSteps_anchor_return
#print axioms gasSteps_anchor_miss
#print axioms gasSteps_anchor_repeat
#print axioms actual_slice
#print axioms site_pc
#print axioms valid_miss
#print axioms gasSteps_data
#print axioms gasSteps_return
end RetainedLocated113
