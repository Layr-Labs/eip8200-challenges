import Challenge.Ripemd160.Submission.Proofs.Bytecode.DirectLiteralRawV4
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
open StackRoundTrace StackRoundTemplate DirectLiteralRawV4 DirectLiteralModel J2Moves
namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.DirectLiteralScanV4

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
    (hv : Decode.isValidJumpDest s.executionEnv.code 6091 = true)
    (k m : Nat) (hkm : k+m < 32) :
    runInstrSeq (test k m) {s with pc := pc, stack := full s.executionEnv.calldata k :: rho} =
    some {s with pc := if (UInt256.ofNat s.executionEnv.calldata.size).toNat < (UInt256.ofNat (32*(k+m)+33)).toNat then UInt256.ofNat 6091 else pcAfter pc (test k m), stack := diff s.executionEnv.calldata (k+m) :: full s.executionEnv.calldata (k+m) :: rho} := by
  have h1 := run_body s pc rho (by omega) hrun k m hkm
  have h2 := run_branch s (pcAfter pc (body k m)) (k+m)
    (diff s.executionEnv.calldata (k+m) :: full s.executionEnv.calldata (k+m) :: rho)
    (by simp; omega) hrun hv
  have h := DenseScheduleTrace.runInstrSeq_append_running h1 hrun h2
  simpa only [test,DenseScheduleTrace.pcAfter_append] using h

theorem run_terminal (s : State) (pc : UInt256) (rho : List UInt256)
    (hs : rho.length ≤ 988) (hrun : s.halt = .Running) :
    runInstrSeq (body 12 19) {s with pc := pc, stack := full s.executionEnv.calldata 12 :: rho} =
    some {s with pc := pcAfter pc (body 12 19), stack := diff s.executionEnv.calldata 31 :: full s.executionEnv.calldata 31 :: rho} :=
  run_body s pc rho (by omega) hrun 12 19 (by decide)

def lo : Nat → Nat | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 8 | _ => 12
def hi : Nat → Nat | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 7 | 5 => 11 | _ => 31
def entryPC : Nat → Nat | 0 => 4804 | 1 => 4848 | 2 => 4894 | 3 => 4940 | 4 => 4986 | 5 => 5147 | _ => 5312
def entryIndex : Nat → Nat | 0 => 3531 | 1 => 3540 | 2 => 3550 | 3 => 3560 | 4 => 3570 | 5 => 3595 | _ => 3620
def cleanPC : Nat → Nat | 0 => 4848 | 1 => 4893 | 2 => 4939 | 3 => 4985 | 4 => 5146 | _ => 5311
def cleanIndex : Nat → Nat | 0 => 3540 | 1 => 3549 | 2 => 3559 | 3 => 3569 | 4 => 3594 | _ => 3619
def bound (j : Nat) : Nat := 32*hi j+33

def entry (s : State) (rho : List UInt256) (j : Nat) : State :=
  atState s (entryPC j) (if j=0 then rho else full s.executionEnv.calldata (lo j) :: rho)
def tailState (s : State) (rho : List UInt256) (j : Nat) : State :=
  atState s (if j=0 then 6108 else 6091) (if j=0 then diff s.executionEnv.calldata 0 :: rho else diff s.executionEnv.calldata (hi j) :: full s.executionEnv.calldata (hi j) :: rho)
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
    (atState s (if j.val=0 then 6117 else 6101) (tailAcc s j.val :: rho))
  firstResult (a : UInt256) : GasSteps (atState s 6117 (a :: rho))
    (atState s (if a.toNat = 0 then 6121 else 4565) rho)
  result (a : UInt256) : GasSteps (atState s 6101 (a :: rho))
    (atState s (if a.toNat = 0 then 6105 else 4565) rho)

inductive Piece
 | first | firstTail | firstResult | test (j : Fin 6) | clean (j : Fin 6) | terminal | tail | result

def template : Piece → List Instr
 | .first => firstCmp ++ firstBranch
 | .firstTail => firstTail
 | .firstResult => resultTemplate
 | .test j => if j.val=0 then firstCmp ++ firstBranch else test (lo j.val) (hi j.val-lo j.val)
 | .clean j => if j.val=0 then cmpTemplate 1 else orTemplate
 | .terminal => body 12 19
 | .tail => tailTemplate
 | .result => resultTemplate

def index : Piece → Nat
 | .first => 3531 | .firstTail => 3732 | .firstResult => 3739 | .test j => entryIndex j.val | .clean j => cleanIndex j.val
 | .terminal => 3620 | .tail => 3719 | .result => 3727

def pc : Piece → Nat
 | .first => 4804 | .firstTail => 6108 | .firstResult => 6117 | .test j => entryPC j.val | .clean j => cleanPC j.val
 | .terminal => 5312 | .tail => 6091 | .result => 6101

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

theorem valid_tail : Decode.isValidJumpDest Artifact.submissionArtifact.code 6091 = true := by
  have hp : Artifact.submissionArtifact.instructionPC 3719 = 5100 := by
    rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide
  have h := Artifact.submissionArtifact.isValidJumpDest_index 3719 (by rfl)
  rw [hp] at h
  exact h

theorem valid_fallback : Decode.isValidJumpDest Artifact.submissionArtifact.code 4565 = true := by
  have hp : Artifact.submissionArtifact.instructionPC 3412 = 4617 := by
    rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide
  have h := Artifact.submissionArtifact.isValidJumpDest_index 3412 (by rfl)
  rw [hp] at h
  exact h

theorem test_end (j : Fin 6) (hn : j.val ≠ 0) : pcAfter (UInt256.ofNat (entryPC j.val)) (test (lo j.val) (hi j.val-lo j.val)) = UInt256.ofNat (cleanPC j.val) := by
  fin_cases j <;> first | exact False.elim (hn rfl) | decide

theorem clean_end (j : Fin 6) (hn : j.val ≠ 0) : pcAfter (UInt256.ofNat (cleanPC j.val)) orTemplate = UInt256.ofNat (entryPC (j.val+1)) := by
  fin_cases j <;> first | exact False.elim (hn rfl) | decide

theorem wordIndex (j : Fin 6) : lo j.val + (hi j.val-lo j.val) = hi j.val := by
  fin_cases j <;> decide

theorem nextWord (j : Fin 6) : lo (j.val+1) = hi j.val+1 := by
  fin_cases j <;> decide

theorem valid_firstTail : Decode.isValidJumpDest Artifact.submissionArtifact.code 6108 = true := by
  have hp : Artifact.submissionArtifact.instructionPC 3732 = 5167 := by
    rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide
  have h := Artifact.submissionArtifact.isValidJumpDest_index 3732 (by rfl)
  rw [hp] at h
  exact h

theorem first_full (input : ByteArray) : full input 1 = diff input 0 := by
  exact lor_zero _

theorem run_first (s : State) (pc : UInt256) (rho : List UInt256)
    (hs : rho.length ≤ 988) (hrun : s.halt = .Running)
    (hv : Decode.isValidJumpDest s.executionEnv.code 6108 = true) :
    runInstrSeq (firstCmp ++ firstBranch) {s with pc:=pc, stack:=rho} =
      some {s with pc:=if (UInt256.ofNat s.executionEnv.calldata.size).toNat < 33 then UInt256.ofNat 6108 else pcAfter pc (firstCmp ++ firstBranch), stack:=diff s.executionEnv.calldata 0 :: rho} := by
  have h1 := run_firstCmp s pc rho (by omega) hrun
  have h2 := run_firstBranch s (pcAfter pc firstCmp) (diff s.executionEnv.calldata 0 :: rho) (by simp; omega) hrun hv
  have h := DenseScheduleTrace.runInstrSeq_append_running h1 hrun h2
  simpa only [DenseScheduleTrace.pcAfter_append] using h

def moves (s : State) (e : Env s) (rho : List UInt256)
    (hs : rho.length ≤ 988) (hn : s.executionEnv.calldata.size < 2^256) : Moves s rho := by
  have hv : Decode.isValidJumpDest s.executionEnv.code 6091 = true := by rw [e.code]; exact valid_tail
  have hvf : Decode.isValidJumpDest s.executionEnv.code 4565 = true := by rw [e.code]; exact valid_fallback
  have hnword : (UInt256.ofNat s.executionEnv.calldata.size).toNat = s.executionEnv.calldata.size := by
    rw [Word.word_toNat_ofNat,Nat.mod_eq_of_lt hn]
  have hbword (j : Fin 6) : (UInt256.ofNat (32*hi j.val+33)).toNat = 32*hi j.val+33 := by
    fin_cases j <;> decide
  have hkm (j : Fin 6) : lo j.val+(hi j.val-lo j.val) < 32 := by
    fin_cases j <;> decide
  have hcode : s.executionEnv.code.size = 9208 := by
    rw [e.code]
    exact Challenge.Ripemd160.referenceBytecode_size
  have hv0 : Decode.isValidJumpDest s.executionEnv.code 6108 = true := by rw [e.code]; exact valid_firstTail
  refine ⟨?_,?_,?_,?_,?_,?_,?_⟩
  · simpa [entry,entryPC,atState] using GasSteps.refl (atState s 4804 rho)
  · intro j hp
    by_cases hj0 : j.val=0
    · have hr := run_first s (UInt256.ofNat 4804) rho hs e.run hv0
      have hc : ¬(UInt256.ofNat s.executionEnv.calldata.size).toNat < 33 := by rw [hnword]; simpa [bound,hi,hj0] using hp
      have he : pcAfter (UInt256.ofNat 4804) (firstCmp ++ firstBranch) = UInt256.ofNat 4848 := by decide
      simp only [if_neg hc,he] at hr
      have g := lift .first s _ e rho hr
      simpa [entry,hj0,entryPC,lo,first_full,pc,atState,show j.val+1=1 by omega] using g
    have hr := run_test s (UInt256.ofNat (entryPC j.val)) rho hs e.run hv (lo j.val) (hi j.val-lo j.val) (hkm j)
    have hc : ¬s.executionEnv.calldata.size < 32*hi j.val+33 := by change ¬s.executionEnv.calldata.size < bound j.val; omega
    simp only [wordIndex j,hnword,hbword j,if_neg hc] at hr
    rw [test_end j hj0] at hr
    have htemp : template (.test j) = test (lo j.val) (hi j.val-lo j.val) := by simp [template,hj0]
    rw [← htemp] at hr
    have g1 := lift (.test j) s _ e (full s.executionEnv.calldata (lo j.val)::rho) hr
    have hd := run_or s (UInt256.ofNat (cleanPC j.val))
      (diff s.executionEnv.calldata (hi j.val)) (full s.executionEnv.calldata (hi j.val)) rho (by omega) e.run
    rw [clean_end j hj0] at hd
    have htemp : template (.clean j) = orTemplate := by simp [template,hj0]
    rw [← htemp] at hd
    have g2 := lift (.clean j) s _ e
      (diff s.executionEnv.calldata (hi j.val)::full s.executionEnv.calldata (hi j.val)::rho) hd
    have hf : UInt256.lor (diff s.executionEnv.calldata (hi j.val)) (full s.executionEnv.calldata (hi j.val)) = full s.executionEnv.calldata (hi j.val+1) := rfl
    simpa [entry,atState,nextWord j,hf,pc,hj0,show j.val+1 ≠ 0 by omega] using g1.trans g2
  · intro j hp
    by_cases hj0 : j.val=0
    · have hr := run_first s (UInt256.ofNat 4804) rho hs e.run hv0
      have hc : (UInt256.ofNat s.executionEnv.calldata.size).toNat < 33 := by rw [hnword]; simpa [bound,hi,hj0] using hp
      simp only [if_pos hc] at hr
      have g := lift .first s _ e rho hr
      simpa [entry,tailState,hj0,entryPC,lo,hi,pc,atState] using g
    have hr := run_test s (UInt256.ofNat (entryPC j.val)) rho hs e.run hv (lo j.val) (hi j.val-lo j.val) (hkm j)
    have hc : s.executionEnv.calldata.size < 32*hi j.val+33 := hp
    simp only [wordIndex j,hnword,hbword j,if_pos hc] at hr
    have htemp : template (.test j) = test (lo j.val) (hi j.val-lo j.val) := by simp [template,hj0]
    rw [← htemp] at hr
    simpa [entry,tailState,hj0,pc,atState] using lift (.test j) s _ e (full s.executionEnv.calldata (lo j.val)::rho) hr
  · have hr := run_terminal s (UInt256.ofNat 5312) rho hs e.run
    have he : pcAfter (UInt256.ofNat 5312) (body 12 19) = UInt256.ofNat 6091 := by decide
    rw [he] at hr
    exact lift .terminal s _ e (full s.executionEnv.calldata 12::rho) hr
  · intro j
    by_cases hj0 : j.val=0
    · have hr := run_firstTail s (UInt256.ofNat 6108) (diff s.executionEnv.calldata 0) rho (by omega) e.run hcode
      have he : pcAfter (UInt256.ofNat 6108) firstTail = UInt256.ofNat 6117 := by decide
      rw [he] at hr
      have g := lift .firstTail s _ e (diff s.executionEnv.calldata 0 ::rho) hr
      simpa [tailState,tailAcc,hj0,hi,full,lor_zero,pc,atState,shifted] using g
    have hr := run_tail s (UInt256.ofNat 6091) (UInt256.ofNat (bound j.val))
      (diff s.executionEnv.calldata (hi j.val)) (full s.executionEnv.calldata (hi j.val)) rho (by omega) e.run hcode
    have he : pcAfter (UInt256.ofNat 6091) tailTemplate = UInt256.ofNat 6101 := by decide
    rw [he] at hr
    simpa [tailState,tailAcc,hj0,pc,atState] using lift .tail s _ e (diff s.executionEnv.calldata (hi j.val)::full s.executionEnv.calldata (hi j.val)::rho) hr
  · intro a
    have hr := run_result s (UInt256.ofNat 6117) a rho (by omega) e.run hvf
    have he : pcAfter (UInt256.ofNat 6117) resultTemplate = UInt256.ofNat 6121 := by decide
    rw [he] at hr
    have gr := lift .firstResult s _ e (a::rho) hr
    by_cases hz : a.toNat=0 <;> simpa only [hz,ite_true,ite_false,atState,pc] using gr
  · intro a
    have hr := run_result s (UInt256.ofNat 6101) a rho (by omega) e.run hvf
    have he : pcAfter (UInt256.ofNat 6101) resultTemplate = UInt256.ofNat 6105 := by decide
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
      (atState s (if (result s.executionEnv.calldata n).toNat = 0 then (if phase n=0 then 6121 else 6105) else 4565) rho) := by
  have hf := facts n hn
  have gt := toTail s rho mv n hf hsize
  have ga := mv.tail ⟨phase n,hf.1⟩
  rw [tailAcc_eq s n hf hsize] at ga
  by_cases h0 : phase n=0
  · simp only [h0,ite_true] at ga gt ⊢
    exact gt.trans (ga.trans (mv.firstResult _))
  · simp only [h0,ite_false] at ga ⊢
    exact gt.trans (ga.trans (mv.result _))

def gasSteps_scan (s : State) (e : Env s) (rho : List UInt256)
    (hs : rho.length ≤ 988) (hn : RecognitionAccumulator.Allowed s.executionEnv.calldata.size) :
    GasSteps (atState s 4804 rho)
      (atState s (if (result s.executionEnv.calldata s.executionEnv.calldata.size).toNat = 0 then (if phase s.executionEnv.calldata.size=0 then 6121 else 6105) else 4565) rho) := by
  have hb := RecognitionAccumulator.allowed_bounds s.executionEnv.calldata.size hn
  have hsz : s.executionEnv.calldata.size < 2^256 := by
    have h : 1000 < 2^256 := by decide
    omega
  exact scan s rho (moves s e rho hs hsz) _ hn rfl

#print axioms moves
#print axioms gasSteps_scan
end Challenge.Ripemd160.Submission.Proofs.Bytecode.DirectLiteralScanV4
