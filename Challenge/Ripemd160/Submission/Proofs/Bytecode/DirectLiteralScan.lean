import Challenge.Ripemd160.Submission.Proofs.Bytecode.DirectLiteralRaw
import Challenge.Ripemd160.Submission.Proofs.Bytecode.DenseScheduleTrace
import Challenge.Ripemd160.Submission.Proofs.Bytecode.StackSiteBuilder
import Challenge.Ripemd160.Submission.Proofs.Bytecode.StackRoundData
import Challenge.Ripemd160.Submission.Proofs.Bytecode.Artifact
set_option maxRecDepth 100000
set_option maxHeartbeats 12000000
set_option warningAsError true
set_option linter.unusedSimpArgs false
open EvmSemantics EvmSemantics.EVM YulEvmCompiler Challenge.EvmProof
open Challenge.Ripemd160.Submission.Proofs.Bytecode
open StackRoundTrace StackRoundTemplate DirectLiteralRaw DirectLiteralModel J2Moves
namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.DirectLiteralScan

def fullTemplate : Nat → Nat → List Instr
 | _, 0 => []
 | k, m+1 => (cmpTemplate k ++ orTemplate) ++ fullTemplate (k+1) m

theorem run_fullTemplate (s : State) (pc : UInt256) (rho : List UInt256)
    (hs : rho.length ≤ 990) (hrun : s.halt = .Running)
    (k m : Nat) (hkm : k+m ≤ 32) :
    runInstrSeq (fullTemplate k m) {s with pc := pc, stack := full s.executionEnv.calldata k :: rho} =
    some {s with pc := pcAfter pc (fullTemplate k m), stack := full s.executionEnv.calldata (k+m) :: rho} := by
  induction m generalizing k pc with
  | zero => simp [fullTemplate,runInstrSeq,pcAfter]
  | succ m ih =>
    have hc := run_cmp s pc k (by omega) (full s.executionEnv.calldata k) rho hs hrun
    have ho := run_or s (pcAfter pc (cmpTemplate k))
      (diff s.executionEnv.calldata k) (full s.executionEnv.calldata k) rho hs hrun
    have hco := DenseScheduleTrace.runInstrSeq_append_running hc hrun ho
    have hi := ih (pcAfter pc (cmpTemplate k ++ orTemplate)) (k+1) (by omega)
    have hf : UInt256.lor (diff s.executionEnv.calldata k) (full s.executionEnv.calldata k) =
      full s.executionEnv.calldata (k+1) := rfl
    rw [hf] at hco
    simp only [DenseScheduleTrace.pcAfter_append] at hi
    have hj := DenseScheduleTrace.runInstrSeq_append_running hco hrun hi
    simpa only [fullTemplate,DenseScheduleTrace.pcAfter_append, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hj

def body (k m : Nat) : List Instr := fullTemplate k m ++ cmpTemplate (k+m)
def test (k m : Nat) : List Instr := body k m ++ branchTemplate (k+m)

theorem run_body (s : State) (pc : UInt256) (rho : List UInt256)
    (hs : rho.length ≤ 990) (hrun : s.halt = .Running)
    (k m : Nat) (hkm : k+m < 32) :
    runInstrSeq (body k m) {s with pc := pc, stack := full s.executionEnv.calldata k :: rho} =
    some {s with pc := pcAfter pc (body k m), stack := diff s.executionEnv.calldata (k+m) :: full s.executionEnv.calldata (k+m) :: rho} := by
  have h1 := run_fullTemplate s pc rho hs hrun k m (by omega)
  have h2 := run_cmp s (pcAfter pc (fullTemplate k m)) (k+m) hkm (full s.executionEnv.calldata (k+m)) rho hs hrun
  have h := DenseScheduleTrace.runInstrSeq_append_running h1 hrun h2
  simpa only [body,DenseScheduleTrace.pcAfter_append] using h

theorem run_test (s : State) (pc : UInt256) (rho : List UInt256)
    (hs : rho.length ≤ 988) (hrun : s.halt = .Running)
    (hv : Decode.isValidJumpDest s.executionEnv.code 6108 = true)
    (k m : Nat) (hkm : k+m < 32) :
    runInstrSeq (test k m) {s with pc := pc, stack := full s.executionEnv.calldata k :: rho} =
    some {s with pc := if (UInt256.ofNat s.executionEnv.calldata.size).toNat < (UInt256.ofNat (32*(k+m)+33)).toNat then UInt256.ofNat 6108 else pcAfter pc (test k m), stack := UInt256.ofNat (32*(k+m)+33) :: diff s.executionEnv.calldata (k+m) :: full s.executionEnv.calldata (k+m) :: rho} := by
  have h1 := run_body s pc rho (by omega) hrun k m hkm
  have h2 := run_branch s (pcAfter pc (body k m)) (k+m)
    (diff s.executionEnv.calldata (k+m) :: full s.executionEnv.calldata (k+m) :: rho)
    (by simp; omega) hrun hv
  have h := DenseScheduleTrace.runInstrSeq_append_running h1 hrun h2
  simpa only [test,DenseScheduleTrace.pcAfter_append] using h

theorem run_terminal (s : State) (pc : UInt256) (rho : List UInt256)
    (hs : rho.length ≤ 988) (hrun : s.halt = .Running) :
    runInstrSeq (body 12 19 ++ lastTemplate) {s with pc := pc, stack := full s.executionEnv.calldata 12 :: rho} =
    some {s with pc := pcAfter pc (body 12 19 ++ lastTemplate), stack := UInt256.ofNat 1025 :: diff s.executionEnv.calldata 31 :: full s.executionEnv.calldata 31 :: rho} := by
  have h1 := run_body s pc rho (by omega) hrun 12 19 (by decide)
  have h2 := run_last s (pcAfter pc (body 12 19))
    (diff s.executionEnv.calldata 31 :: full s.executionEnv.calldata 31 :: rho)
    (by simp; omega) hrun
  have h := DenseScheduleTrace.runInstrSeq_append_running h1 hrun h2
  simpa only [DenseScheduleTrace.pcAfter_append] using h

def lo : Nat → Nat | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 8 | _ => 12
def hi : Nat → Nat | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 7 | 5 => 11 | _ => 31
def entryPC : Nat → Nat | 0 => 4805 | 1 => 4852 | 2 => 4900 | 3 => 4948 | 4 => 4996 | 5 => 5159 | _ => 5326
def entryIndex : Nat → Nat | 0 => 3536 | 1 => 3548 | 2 => 3560 | 3 => 3572 | 4 => 3584 | 5 => 3611 | _ => 3638
def cleanPC : Nat → Nat | 0 => 4850 | 1 => 4898 | 2 => 4946 | 3 => 4994 | 4 => 5157 | _ => 5324
def cleanIndex : Nat → Nat | 0 => 3546 | 1 => 3558 | 2 => 3570 | 3 => 3582 | 4 => 3609 | _ => 3636
def bound (j : Nat) : Nat := 32*hi j+33

def entry (s : State) (rho : List UInt256) (j : Nat) : State :=
  atState s (entryPC j) (full s.executionEnv.calldata (lo j) :: rho)
def tailState (s : State) (rho : List UInt256) (j : Nat) : State :=
  atState s 6108 (UInt256.ofNat (bound j) :: diff s.executionEnv.calldata (hi j) :: full s.executionEnv.calldata (hi j) :: rho)
def tailAcc (s : State) (j : Nat) : UInt256 :=
  UInt256.lor (UInt256.shiftRight (diff s.executionEnv.calldata (hi j))
    (shifted (UInt256.ofNat s.executionEnv.calldata.size) (UInt256.ofNat (bound j))))
    (full s.executionEnv.calldata (hi j))

structure Moves (s : State) (rho : List UInt256) where
  start : GasSteps (atState s 4804 rho) (entry s rho 0)
  pass (j : Fin 6) (h : bound j.val ≤ s.executionEnv.calldata.size) :
    GasSteps (entry s rho j.val) (entry s rho (j.val+1))
  hit (j : Fin 6) (h : s.executionEnv.calldata.size < bound j.val) :
    GasSteps (entry s rho j.val) (tailState s rho j.val)
  last : GasSteps (entry s rho 6) (tailState s rho 6)
  tail (j : Fin 7) : GasSteps (tailState s rho j.val)
    (atState s 6117 (tailAcc s j.val :: rho))
  result (a : UInt256) : GasSteps (atState s 6117 (a :: rho))
    (atState s (if a.toNat = 0 then 6121 else 4565) rho)

inductive Piece
 | start | test (j : Fin 6) | clean (j : Fin 6) | terminal | tail | result

def template : Piece → List Instr
 | .start => startTemplate
 | .test j => test (lo j.val) (hi j.val-lo j.val)
 | .clean _ => dropOrTemplate
 | .terminal => body 12 19 ++ lastTemplate
 | .tail => tailTemplate
 | .result => resultTemplate

def index : Piece → Nat
 | .start => 3535 | .test j => entryIndex j.val | .clean j => cleanIndex j.val
 | .terminal => 3638 | .tail => 3738 | .result => 3746

def pc : Piece → Nat
 | .start => 4804 | .test j => entryPC j.val | .clean j => cleanPC j.val
 | .terminal => 5326 | .tail => 6108 | .result => 6117

theorem actual_slice (p : Piece) :
    (Artifact.submissionArtifact.instructions.drop (index p)).take (template p).length = template p := by
  cases p with
  | test j => fin_cases j <;> rfl
  | clean j => fin_cases j <;> rfl
  | _ => rfl

theorem bounds (p : Piece) : index p + (template p).length ≤ Artifact.submissionArtifact.instructions.length := by
  change index p + (template p).length ≤ Artifact.submissionInstructions.length
  rw [Artifact.referenceInstructions_count]
  cases p with
  | test j => fin_cases j <;> decide
  | clean j => fin_cases j <;> decide
  | _ => decide

theorem wellFormed (p : Piece) : StackRoundData.TemplateWellFormed (template p) := by
  cases p with
  | test j => fin_cases j <;> decide
  | clean j => fin_cases j <;> decide
  | _ => decide

theorem nonempty (p : Piece) : template p ≠ [] := by
  have h : 0 < (template p).length := by
    cases p with
    | test j => fin_cases j <;> decide
    | clean j => fin_cases j <;> decide
    | _ => decide
  intro he
  simp only [he,List.length_nil] at h
  omega

def site (p : Piece) : GenericRoundSite Artifact.submissionArtifact .Osaka (template p) :=
  StackSiteBuilder.ofSlice (template p) (index p) (actual_slice p) (bounds p)
    StackRoundData.artifact_code_bound (StackRoundData.templateWellFormed_mem (wellFormed p)) (nonempty p)

theorem site_pc (p : Piece) : (site p).startPC = UInt256.ofNat (pc p) := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC (index p)) = UInt256.ofNat (pc p)
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  cases p with
  | test j => fin_cases j <;> decide
  | clean j => fin_cases j <;> decide
  | _ => decide

theorem form (p : Piece) : ∀ i ∈ (template p).dropLast, RecognitionLift.Advances i := by
  apply RecognitionLift.advancesAll_sound
  cases p with
  | test j => fin_cases j <;> decide
  | clean j => fin_cases j <;> decide
  | _ => decide

structure Env (s : State) : Prop where
  code : s.executionEnv.code = Artifact.submissionArtifact.code
  fork : s.fork = .Osaka
  run : s.halt = .Running
  np : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
    s.executionEnv.fork s.executionEnv.codeAddr = false

def lift (p : Piece) (s t : State) (e : Env s) (stack : List UInt256)
    (h : runInstrSeq (template p) (atState s (pc p) stack) = some t) :
    GasSteps (atState s (pc p) stack) t :=
  RecognitionLift.gasSteps_of_raw (site p) _ _ e.code e.fork e.run e.np (site_pc p).symm (form p) h

theorem valid_tail : Decode.isValidJumpDest Artifact.submissionArtifact.code 6108 = true := by
  have hp : Artifact.submissionArtifact.instructionPC 3720 = 5173 := by
    rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide
  have h := Artifact.submissionArtifact.isValidJumpDest_index 3720 (by rfl)
  rw [hp] at h
  exact h

theorem valid_fallback : Decode.isValidJumpDest Artifact.submissionArtifact.code 4565 = true := by
  have hp : Artifact.submissionArtifact.instructionPC 3394 = 4617 := by
    rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide
  have h := Artifact.submissionArtifact.isValidJumpDest_index 3394 (by rfl)
  rw [hp] at h
  exact h

theorem test_end (j : Fin 6) : pcAfter (UInt256.ofNat (entryPC j.val)) (test (lo j.val) (hi j.val-lo j.val)) = UInt256.ofNat (cleanPC j.val) := by
  fin_cases j <;> decide

theorem clean_end (j : Fin 6) : pcAfter (UInt256.ofNat (cleanPC j.val)) dropOrTemplate = UInt256.ofNat (entryPC (j.val+1)) := by
  fin_cases j <;> decide

theorem wordIndex (j : Fin 6) : lo j.val + (hi j.val-lo j.val) = hi j.val := by
  fin_cases j <;> decide

theorem nextWord (j : Fin 6) : lo (j.val+1) = hi j.val+1 := by
  fin_cases j <;> decide

def moves (s : State) (e : Env s) (rho : List UInt256)
    (hs : rho.length ≤ 988) (hn : s.executionEnv.calldata.size < 2^256) : Moves s rho := by
  have hv : Decode.isValidJumpDest s.executionEnv.code 6108 = true := by rw [e.code]; exact valid_tail
  have hvf : Decode.isValidJumpDest s.executionEnv.code 4565 = true := by rw [e.code]; exact valid_fallback
  have hnword : (UInt256.ofNat s.executionEnv.calldata.size).toNat = s.executionEnv.calldata.size := by
    rw [Word.word_toNat_ofNat,Nat.mod_eq_of_lt hn]
  have hbword (j : Fin 6) : (UInt256.ofNat (32*hi j.val+33)).toNat = 32*hi j.val+33 := by
    fin_cases j <;> decide
  have hkm (j : Fin 6) : lo j.val+(hi j.val-lo j.val) < 32 := by
    fin_cases j <;> decide
  refine ⟨?_,?_,?_,?_,?_,?_⟩
  · have h := run_start s (UInt256.ofNat 4804) rho (by omega) e.run
    have hp : pcAfter (UInt256.ofNat 4804) startTemplate = UInt256.ofNat 4805 := by decide
    rw [hp] at h
    exact lift .start s _ e rho h
  · intro j hp
    have hr := run_test s (UInt256.ofNat (entryPC j.val)) rho hs e.run hv (lo j.val) (hi j.val-lo j.val) (hkm j)
    have hc : ¬s.executionEnv.calldata.size < 32*hi j.val+33 := by change ¬s.executionEnv.calldata.size < bound j.val; omega
    simp only [wordIndex j,hnword,hbword j,if_neg hc] at hr
    rw [test_end j] at hr
    have g1 := lift (.test j) s _ e (full s.executionEnv.calldata (lo j.val)::rho) hr
    have hd := run_dropOr s (UInt256.ofNat (cleanPC j.val)) (UInt256.ofNat (bound j.val))
      (diff s.executionEnv.calldata (hi j.val)) (full s.executionEnv.calldata (hi j.val)) rho (by omega) e.run
    rw [clean_end j] at hd
    have g2 := lift (.clean j) s _ e
      (UInt256.ofNat (bound j.val)::diff s.executionEnv.calldata (hi j.val)::full s.executionEnv.calldata (hi j.val)::rho) hd
    have hf : UInt256.lor (diff s.executionEnv.calldata (hi j.val)) (full s.executionEnv.calldata (hi j.val)) = full s.executionEnv.calldata (hi j.val+1) := rfl
    simpa only [entry,atState,nextWord j,hf,pc] using g1.trans g2
  · intro j hp
    have hr := run_test s (UInt256.ofNat (entryPC j.val)) rho hs e.run hv (lo j.val) (hi j.val-lo j.val) (hkm j)
    have hc : s.executionEnv.calldata.size < 32*hi j.val+33 := hp
    simp only [wordIndex j,hnword,hbword j,if_pos hc] at hr
    exact lift (.test j) s _ e (full s.executionEnv.calldata (lo j.val)::rho) hr
  · have hr := run_terminal s (UInt256.ofNat 5326) rho hs e.run
    have he : pcAfter (UInt256.ofNat 5326) (body 12 19 ++ lastTemplate) = UInt256.ofNat 6108 := by decide
    rw [he] at hr
    exact lift .terminal s _ e (full s.executionEnv.calldata 12::rho) hr
  · intro j
    have hr := run_tail s (UInt256.ofNat 6108) (UInt256.ofNat (bound j.val))
      (diff s.executionEnv.calldata (hi j.val)) (full s.executionEnv.calldata (hi j.val)) rho (by omega) e.run
    have he : pcAfter (UInt256.ofNat 6108) tailTemplate = UInt256.ofNat 6117 := by decide
    rw [he] at hr
    exact lift .tail s _ e (UInt256.ofNat (bound j.val)::diff s.executionEnv.calldata (hi j.val)::full s.executionEnv.calldata (hi j.val)::rho) hr
  · intro a
    have hr := run_result s (UInt256.ofNat 6117) a rho (by omega) e.run hvf
    have he : pcAfter (UInt256.ofNat 6117) resultTemplate = UInt256.ofNat 6121 := by decide
    rw [he] at hr
    have gr := lift .result s _ e (a::rho) hr
    by_cases hz : a.toNat=0 <;> simpa only [hz,ite_true,ite_false,atState,pc] using gr

def phase (n : Nat) : Nat := if n ≤ 32 then 0 else if n ≤ 64 then 1 else if n ≤ 96 then 2 else if n ≤ 128 then 3 else if n ≤ 256 then 4 else if n ≤ 384 then 5 else 6

def Facts (n : Nat) : Prop :=
  phase n < 7 ∧ hi (phase n) = last n ∧
  shifted (UInt256.ofNat n) (UInt256.ofNat (bound (phase n))) = UInt256.ofNat ((32*(last n+1)-n)*8) ∧
  (∀ j : Fin 6, j.val < phase n → bound j.val ≤ n) ∧
  (phase n < 6 → n < bound (phase n))

theorem facts (n : Nat) (hn : RecognitionAccumulator.Allowed n) : Facts n := by
  rcases hn with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals unfold Facts
  all_goals decide

def scanPrefix (s : State) (rho : List UInt256) (mv : Moves s rho)
    (n : Nat) (hf : Facts n) (hsize : s.executionEnv.calldata.size = n)
    (j : Nat) (hj : j ≤ phase n) :
    GasSteps (atState s 4804 rho) (entry s rho j) := by
  induction j with
  | zero => exact mv.start
  | succ j ih =>
    have hj6 : j < 6 := by have h := hf.1; omega
    have hp : bound j ≤ s.executionEnv.calldata.size := by
      rw [hsize]
      exact hf.2.2.2.1 ⟨j,hj6⟩ (show j < phase n by omega)
    exact (ih (by omega)).trans (mv.pass ⟨j,hj6⟩ hp)

def toTail (s : State) (rho : List UInt256) (mv : Moves s rho)
    (n : Nat) (hf : Facts n) (hsize : s.executionEnv.calldata.size = n) :
    GasSteps (atState s 4804 rho) (tailState s rho (phase n)) := by
  have gp := scanPrefix s rho mv n hf hsize (phase n) (by omega)
  by_cases h6 : phase n < 6
  · exact gp.trans (mv.hit ⟨phase n,h6⟩ (by rw [hsize]; exact hf.2.2.2.2 h6))
  · have he : phase n = 6 := by have h := hf.1; omega
    have gl : GasSteps (entry s rho (phase n)) (tailState s rho (phase n)) := by
      simpa only [he] using mv.last
    exact gp.trans gl

theorem tailAcc_eq (s : State) (n : Nat) (hf : Facts n)
    (hsize : s.executionEnv.calldata.size = n) : tailAcc s (phase n) = result s.executionEnv.calldata n := by
  unfold tailAcc
  rw [hsize, hf.2.2.1, hf.2.1]
  rfl

def scan (s : State) (rho : List UInt256) (mv : Moves s rho)
    (n : Nat) (hn : RecognitionAccumulator.Allowed n) (hsize : s.executionEnv.calldata.size = n) :
    GasSteps (atState s 4804 rho)
      (atState s (if (result s.executionEnv.calldata n).toNat = 0 then 6121 else 4565) rho) := by
  have hf := facts n hn
  have gt := toTail s rho mv n hf hsize
  have ga := mv.tail ⟨phase n,hf.1⟩
  rw [tailAcc_eq s n hf hsize] at ga
  exact gt.trans (ga.trans (mv.result _))

def gasSteps_scan (s : State) (e : Env s) (rho : List UInt256)
    (hs : rho.length ≤ 988) (hn : RecognitionAccumulator.Allowed s.executionEnv.calldata.size) :
    GasSteps (atState s 4804 rho)
      (atState s (if (result s.executionEnv.calldata s.executionEnv.calldata.size).toNat = 0 then 6121 else 4565) rho) := by
  have hb := RecognitionAccumulator.allowed_bounds s.executionEnv.calldata.size hn
  have hsz : s.executionEnv.calldata.size < 2^256 := by
    have h : 1000 < 2^256 := by decide
    omega
  exact scan s rho (moves s e rho hs hsz) _ hn rfl

#print axioms moves
#print axioms gasSteps_scan
end Challenge.Ripemd160.Submission.Proofs.Bytecode.DirectLiteralScan
