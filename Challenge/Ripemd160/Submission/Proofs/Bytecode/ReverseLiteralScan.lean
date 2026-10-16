import Challenge.Ripemd160.Submission.Proofs.Bytecode.ReverseLiteralRaw
import Challenge.Ripemd160.Submission.Proofs.Bytecode.DenseScheduleTrace
import Challenge.Ripemd160.Submission.Proofs.Bytecode.StackSiteBuilder
import Challenge.Ripemd160.Submission.Proofs.Bytecode.StackRoundData
import Challenge.Ripemd160.Submission.Proofs.Bytecode.Artifact
set_option maxRecDepth 100000
set_option maxHeartbeats 16000000
set_option warningAsError true
set_option linter.unusedSimpArgs false
open EvmSemantics EvmSemantics.EVM YulEvmCompiler Challenge.EvmProof
open Challenge.Ripemd160.Submission.Proofs.Bytecode
open StackRoundTrace StackRoundTemplate DirectLiteralRawV4 DirectLiteralModel J2Moves ReverseLiteralRaw
namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.ReverseLiteralScan

abbrev lengths : List Nat := [1,31,32,55,56,63,64,65,119,120,128,256,376,1000]
def nval : Fin 14 → Nat
 | ⟨0, _⟩ => 1
 | ⟨1, _⟩ => 31
 | ⟨2, _⟩ => 32
 | ⟨3, _⟩ => 55
 | ⟨4, _⟩ => 56
 | ⟨5, _⟩ => 63
 | ⟨6, _⟩ => 64
 | ⟨7, _⟩ => 65
 | ⟨8, _⟩ => 119
 | ⟨9, _⟩ => 120
 | ⟨10, _⟩ => 128
 | ⟨11, _⟩ => 256
 | ⟨12, _⟩ => 376
 | ⟨13, _⟩ => 1000
def tailPC : Fin 14 → Nat
 | ⟨0, _⟩ => 6040
 | ⟨1, _⟩ => 6231
 | ⟨2, _⟩ => 6762
 | ⟨3, _⟩ => 5459
 | ⟨4, _⟩ => 5338
 | ⟨5, _⟩ => 6644
 | ⟨6, _⟩ => 5783
 | ⟨7, _⟩ => 5201
 | ⟨8, _⟩ => 4934
 | ⟨9, _⟩ => 5872
 | ⟨10, _⟩ => 6317
 | ⟨11, _⟩ => 6584
 | ⟨12, _⟩ => 4883
 | ⟨13, _⟩ => 6161
def tailIndex : Fin 14 → Nat
 | ⟨0, _⟩ => 4147
 | ⟨1, _⟩ => 4266
 | ⟨2, _⟩ => 4526
 | ⟨3, _⟩ => 3835
 | ⟨4, _⟩ => 3782
 | ⟨5, _⟩ => 4476
 | ⟨6, _⟩ => 4091
 | ⟨7, _⟩ => 3746
 | ⟨8, _⟩ => 3613
 | ⟨9, _⟩ => 4113
 | ⟨10, _⟩ => 4317
 | ⟨11, _⟩ => 4451
 | ⟨12, _⟩ => 3599
 | ⟨13, _⟩ => 4233
def returnPC : Fin 14 → Nat
 | ⟨0, _⟩ => 6084
 | ⟨1, _⟩ => 6275
 | ⟨2, _⟩ => 6803
 | ⟨3, _⟩ => 5541
 | ⟨4, _⟩ => 5420
 | ⟨5, _⟩ => 6726
 | ⟨6, _⟩ => 5862
 | ⟨7, _⟩ => 5321
 | ⟨8, _⟩ => 5092
 | ⟨9, _⟩ => 6030
 | ⟨10, _⟩ => 6472
 | ⟨11, _⟩ => 8110
 | ⟨12, _⟩ => 8110
 | ⟨13, _⟩ => 8110

def joinPC (k : Nat) : Nat := if k=30 then 6900 else if k=10 then 7681 else 7837

def revTemplate (chain : Bool) : Nat → List Instr
 | 0 => []
 | k+1 => (if (chain = true ∧ (k=30 ∨ k=10 ∨ k=6 ∨ k=2 ∨ k=1 ∨ k=0)) then [.op .JUMPDEST] else []) ++
    (cmpTemplate k ++ orTemplate) ++ revTemplate chain k

def prefixTemplate (i : Fin 14) : List Instr :=
  [.op .JUMPDEST] ++ cmpTemplate (last (nval i)) ++ shrTemplate (ReverseLiteralRaw.shift (nval i))

def tailTemplate (i : Fin 14) : List Instr :=
  if last (nval i) ≤ 3 then (prefixTemplate i ++ revTemplate false (last (nval i))) ++ resultTemplate
  else prefixTemplate i ++ jumpTemplate (joinPC (last (nval i)-1))

def chainK (i : Fin 3) : Nat := if i=0 then 7 else if i=1 then 11 else 31

def chainTemplate (i : Fin 3) : List Instr :=
  revTemplate true (chainK i) ++ resultTemplate

def chainPC (i : Fin 3) : Nat := if i=0 then 7837 else if i=1 then 7681 else 6900
def chainIndex : Fin 3 → Nat
 | ⟨0, _⟩ => 4752
 | ⟨1, _⟩ => 4731
 | ⟨2, _⟩ => 4630

inductive Piece where
 | dispatch
 | tail (i : Fin 14)
 | chain (i : Fin 3)

def template : Piece → List Instr
 | .dispatch => dispatchTemplate
 | .tail i => tailTemplate i
 | .chain i => chainTemplate i

def index : Piece → Nat
 | .dispatch => 3531
 | .tail i => tailIndex i
 | .chain i => chainIndex i

def pc : Piece → Nat
 | .dispatch => 4804
 | .tail i => tailPC i
 | .chain i => chainPC i

set_option maxHeartbeats 16000000 in
theorem actual_slice (p : Piece) :
  (Artifact.submissionArtifact.instructions.drop (index p)).take (template p).length = template p := by
  cases p with
  | tail i => fin_cases i <;> rfl
  | chain i => fin_cases i <;> rfl
  | dispatch => rfl

theorem bounds (p : Piece) : index p + (template p).length ≤ Artifact.submissionInstructions.length := by
  rw [Artifact.referenceInstructions_count]
  cases p with
  | tail i => fin_cases i <;> decide
  | chain i => fin_cases i <;> decide
  | dispatch => decide

theorem wellFormed (p : Piece) : StackRoundData.TemplateWellFormed (template p) := by
  cases p with
  | tail i => fin_cases i <;> decide
  | chain i => fin_cases i <;> decide
  | dispatch => decide

theorem nonempty (p : Piece) : template p ≠ [] := by
  cases p with
  | tail i => fin_cases i <;> decide
  | chain i => fin_cases i <;> decide
  | dispatch => decide

def site (p : Piece) : GenericRoundSite Artifact.submissionArtifact .Osaka (template p) :=
  StackSiteBuilder.ofSlice (template p) (index p) (actual_slice p) (bounds p)
    StackRoundData.artifact_code_bound (StackRoundData.templateWellFormed_mem (wellFormed p)) (nonempty p)

theorem site_pc (p : Piece) : (site p).startPC = UInt256.ofNat (pc p) := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC (index p)) = UInt256.ofNat (pc p)
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  cases p with
  | tail i => fin_cases i <;> decide
  | chain i => fin_cases i <;> decide
  | dispatch => decide

theorem form (p : Piece) : ∀ i ∈ (template p).dropLast, RecognitionLift.Advances i := by
  apply RecognitionLift.advancesAll_sound
  cases p with
  | tail i => fin_cases i <;> decide
  | chain i => fin_cases i <;> decide
  | dispatch => decide

structure Env (s : State) : Prop where
  code : s.executionEnv.code = Artifact.submissionArtifact.code
  fork : s.fork = .Osaka
  run : s.halt = .Running
  np : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
    s.executionEnv.fork s.executionEnv.codeAddr = false

def lift (p : Piece) (s t : State) (e : Env s) (stack : List UInt256)
    (hraw : runInstrSeq (template p) (atState s (pc p) stack) = some t) :
    GasSteps (atState s (pc p) stack) t :=
  RecognitionLift.gasSteps_of_raw (site p) _ t e.code e.fork e.run e.np
    (by simpa [atState] using (site_pc p).symm) (form p) hraw


theorem run_revTemplate (s : State) (pc : UInt256) (a : UInt256) (rho : List UInt256)
    (hs : rho.length ≤ 990) (hrun : s.halt = .Running) (chain : Bool)
    (k : Nat) (hk : k ≤ 32) :
    runInstrSeq (revTemplate chain k) {s with pc:=pc,stack:=a::rho} =
      some {s with pc:=pcAfter pc (revTemplate chain k),stack:=rev s.executionEnv.calldata a k ::rho} := by
  induction k generalizing pc a with
  | zero => simp [revTemplate,runInstrSeq,pcAfter,rev]
  | succ k ih =>
    let dest : List Instr := if (chain = true ∧ (k=30 ∨ k=10 ∨ k=6 ∨ k=2 ∨ k=1 ∨ k=0)) then [.op .JUMPDEST] else []
    have hd : runInstrSeq dest {s with pc:=pc,stack:=a::rho} =
        some {s with pc:=pcAfter pc dest,stack:=a::rho} := by
      by_cases h : (chain = true ∧ (k=30 ∨ k=10 ∨ k=6 ∨ k=2 ∨ k=1 ∨ k=0))
      · simpa only [dest,if_pos h] using run_jd s pc (a::rho) (by simp;omega) hrun
      · simp [dest,h,runInstrSeq,pcAfter]
    have hc := run_cmp s (pcAfter pc dest) k (by omega) a rho hs hrun
    have ho := run_or s (pcAfter (pcAfter pc dest) (cmpTemplate k))
      (diff s.executionEnv.calldata k) a rho hs hrun
    have hco := DenseScheduleTrace.runInstrSeq_append_running hc hrun ho
    have hdc := DenseScheduleTrace.runInstrSeq_append_running hd hrun hco
    have hi := ih (pcAfter pc (dest ++ (cmpTemplate k ++ orTemplate)))
      (UInt256.lor (diff s.executionEnv.calldata k) a) (by omega)
    simp only [DenseScheduleTrace.pcAfter_append] at hi hdc
    have hall := DenseScheduleTrace.runInstrSeq_append_running hdc hrun hi
    simpa only [revTemplate,dest,DenseScheduleTrace.pcAfter_append,rev] using hall

theorem run_prefix (s : State) (pc : UInt256) (i : Fin 14) (rho : List UInt256)
    (hs : rho.length ≤ 990) (hrun : s.halt = .Running) :
    runInstrSeq (prefixTemplate i) {s with pc:=pc,stack:=rho} =
      some {s with pc:=pcAfter pc (prefixTemplate i),stack:=tailValue s.executionEnv.calldata (nval i)::rho} := by
  have hk : last (nval i) < 32 := by fin_cases i <;> decide
  have hd := run_jd s pc rho (by omega) hrun
  have hc := run_cmp0 s (pcAfter pc [.op .JUMPDEST]) (last (nval i)) hk rho hs hrun
  have hdc := DenseScheduleTrace.runInstrSeq_append_running hd hrun hc
  have hsh := run_shr s (pcAfter pc ([.op .JUMPDEST] ++ cmpTemplate (last (nval i))))
    (diff s.executionEnv.calldata (last (nval i))) (ReverseLiteralRaw.shift (nval i)) rho hs hrun
  simp only [DenseScheduleTrace.pcAfter_append] at hsh
  have hall := DenseScheduleTrace.runInstrSeq_append_running hdc hrun hsh
  simpa only [prefixTemplate,tailValue,DenseScheduleTrace.pcAfter_append] using hall

theorem tail_end (i : Fin 14) (h : last (nval i) ≤ 3) :
    pcAfter (UInt256.ofNat (tailPC i)) (tailTemplate i) = UInt256.ofNat (returnPC i) := by
  fin_cases i <;> (try {norm_num [nval,last] at h}) <;> decide

theorem chain_end (i : Fin 3) :
    pcAfter (UInt256.ofNat (chainPC i)) (chainTemplate i) = UInt256.ofNat 8110 := by
  fin_cases i <;> decide

theorem run_small (s : State) (e : Env s) (rho : List UInt256) (hs : rho.length ≤ 990)
    (i : Fin 14) (hi : last (nval i) ≤ 3)
    (hv : Decode.isValidJumpDest s.executionEnv.code 4565 = true) :
    runInstrSeq (tailTemplate i) (atState s (tailPC i) rho) =
      some (atState s (if (result s.executionEnv.calldata (nval i)).toNat=0 then returnPC i else 4565) rho) := by
  have hp := run_prefix s (UInt256.ofNat (tailPC i)) i rho hs e.run
  have hr := run_revTemplate s (pcAfter (UInt256.ofNat (tailPC i)) (prefixTemplate i))
    (tailValue s.executionEnv.calldata (nval i)) rho hs e.run false (last (nval i)) (by omega)
  have hpr := DenseScheduleTrace.runInstrSeq_append_running hp e.run hr
  rw [rev_tail] at hpr
  have hf := run_result s
    (pcAfter (pcAfter (UInt256.ofNat (tailPC i)) (prefixTemplate i)) (revTemplate false (last (nval i))))
    (result s.executionEnv.calldata (nval i)) rho hs e.run hv
  have hall := DenseScheduleTrace.runInstrSeq_append_running hpr e.run hf
  have he := tail_end i hi
  simp only [tailTemplate,if_pos hi,DenseScheduleTrace.pcAfter_append] at he
  simpa only [tailTemplate,if_pos hi,atState,DenseScheduleTrace.pcAfter_append,he,apply_ite] using hall

theorem run_chain (s : State) (e : Env s) (rho : List UInt256) (hs : rho.length ≤ 990)
    (i : Fin 3) (a : UInt256)
    (hv : Decode.isValidJumpDest s.executionEnv.code 4565 = true) :
    runInstrSeq (chainTemplate i) (atState s (chainPC i) (a::rho)) =
      some (atState s (if (rev s.executionEnv.calldata a (chainK i)).toNat=0 then 8110 else 4565) rho) := by
  have hk : chainK i ≤ 32 := by fin_cases i <;> decide
  have hr := run_revTemplate s (UInt256.ofNat (chainPC i)) a rho hs e.run true (chainK i) hk
  have hf := run_result s (pcAfter (UInt256.ofNat (chainPC i)) (revTemplate true (chainK i)))
    (rev s.executionEnv.calldata a (chainK i)) rho hs e.run hv
  have hall := DenseScheduleTrace.runInstrSeq_append_running hr e.run hf
  have he := chain_end i
  simp only [chainTemplate,DenseScheduleTrace.pcAfter_append] at he
  change pcAfter (pcAfter (UInt256.ofNat (chainPC i)) (revTemplate true (chainK i))) resultTemplate = UInt256.ofNat 8110 at he
  rw [he] at hall
  change runInstrSeq (revTemplate true (chainK i) ++ resultTemplate) _ = _
  by_cases hz : (rev s.executionEnv.calldata a (chainK i)).toNat=0
  · simpa only [atState,if_pos hz] using hall
  · simpa only [atState,if_neg hz] using hall


def chainId (i : Fin 14) : Fin 3 := if nval i=256 then 0 else if nval i=376 then 1 else 2

theorem chainK_eq (i : Fin 14) (hi : ¬last (nval i) ≤ 3) : chainK (chainId i) = last (nval i) := by
  fin_cases i <;> (try {exfalso; exact hi (by decide)}) <;> decide

theorem join_eq (i : Fin 14) (hi : ¬last (nval i) ≤ 3) :
    joinPC (last (nval i)-1) = chainPC (chainId i) := by
  fin_cases i <;> (try {exfalso; exact hi (by decide)}) <;> decide

theorem large_return (i : Fin 14) (hi : ¬last (nval i) ≤ 3) : returnPC i = 8110 := by
  fin_cases i <;> (try {exfalso; exact hi (by decide)}) <;> decide

theorem run_large (s : State) (e : Env s) (rho : List UInt256) (hs : rho.length ≤ 990)
    (i : Fin 14) (hi : ¬last (nval i) ≤ 3)
    (hv : Decode.isValidJumpDest s.executionEnv.code (joinPC (last (nval i)-1)) = true) :
    runInstrSeq (tailTemplate i) (atState s (tailPC i) rho) =
      some (atState s (chainPC (chainId i)) (tailValue s.executionEnv.calldata (nval i)::rho)) := by
  have hp := run_prefix s (UInt256.ofNat (tailPC i)) i rho hs e.run
  have hv' : Decode.isValidJumpDest s.executionEnv.code (UInt256.ofNat (joinPC (last (nval i)-1))).toNat = true := by
    have hj : joinPC (last (nval i)-1) < 2^256 := by unfold joinPC; split <;> (try split) <;> decide
    simpa only [Word.word_toNat_ofNat,Nat.mod_eq_of_lt hj] using hv
  have hj := run_jump s (pcAfter (UInt256.ofNat (tailPC i)) (prefixTemplate i))
    (joinPC (last (nval i)-1)) (tailValue s.executionEnv.calldata (nval i)::rho) (by simp;omega) e.run hv'
  have hall := DenseScheduleTrace.runInstrSeq_append_running hp e.run hj
  simpa only [tailTemplate,if_neg hi,atState,join_eq i hi] using hall

theorem valid_tail (i : Fin 14) : Decode.isValidJumpDest Artifact.submissionArtifact.code (tailPC i) = true := by
  have hp : Artifact.submissionArtifact.instructionPC (tailIndex i) = tailPC i := by
    rw [ArtifactByteLength.instructionPC_eq_byteLength]; fin_cases i <;> decide
  have h := Artifact.submissionArtifact.isValidJumpDest_index (tailIndex i) (by fin_cases i <;> rfl)
  rw [hp] at h
  exact h

theorem valid_chain (i : Fin 3) : Decode.isValidJumpDest Artifact.submissionArtifact.code (chainPC i) = true := by
  have hp : Artifact.submissionArtifact.instructionPC (chainIndex i) = chainPC i := by
    rw [ArtifactByteLength.instructionPC_eq_byteLength]; fin_cases i <;> decide
  have h := Artifact.submissionArtifact.isValidJumpDest_index (chainIndex i) (by fin_cases i <;> rfl)
  rw [hp] at h
  exact h

theorem valid_fallback : Decode.isValidJumpDest Artifact.submissionArtifact.code 4565 = true := by
  have hp : Artifact.submissionArtifact.instructionPC 3412 = 4565 := by
    rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide
  have h := Artifact.submissionArtifact.isValidJumpDest_index 3412 (by rfl)
  rw [hp] at h
  exact h

theorem target_eq (i : Fin 14) : target (nval i) = UInt256.ofNat (tailPC i) := by
  fin_cases i <;> decide

def gasSteps_for (s : State) (e : Env s) (rho : List UInt256) (hs : rho.length ≤ 988)
    (i : Fin 14) (hn : s.executionEnv.calldata.size = nval i) :
    GasSteps (atState s 4804 rho)
      (atState s (if (result s.executionEnv.calldata s.executionEnv.calldata.size).toNat=0 then returnPC i else 4565) rho) := by
  have hv : Decode.isValidJumpDest s.executionEnv.code (target s.executionEnv.calldata.size).toNat = true := by
    rw [hn,target_eq,e.code]
    have hb : tailPC i < 2^256 := by fin_cases i <;> decide
    rw [Word.word_toNat_ofNat,Nat.mod_eq_of_lt hb]
    exact valid_tail i
  have hd := run_dispatch s rho (by omega) e.run hv
  rw [hn,target_eq] at hd
  have gd : GasSteps (atState s 4804 rho) (atState s (tailPC i) rho) := lift .dispatch s _ e rho hd
  have hvf : Decode.isValidJumpDest s.executionEnv.code 4565 = true := by rw [e.code]; exact valid_fallback
  by_cases hi : last (nval i) ≤ 3
  · have hr := run_small s e rho (by omega) i hi hvf
    have gt := lift (.tail i) s _ e rho hr
    simpa only [hn] using gd.trans gt
  · have hvj : Decode.isValidJumpDest s.executionEnv.code (joinPC (last (nval i)-1)) = true := by
      rw [join_eq i hi,e.code]
      exact valid_chain (chainId i)
    have ht := run_large s e rho (by omega) i hi hvj
    have gt := lift (.tail i) s _ e rho ht
    have hc := run_chain s e rho (by omega) (chainId i) (tailValue s.executionEnv.calldata (nval i)) hvf
    rw [chainK_eq i hi,rev_tail] at hc
    have gc := lift (.chain (chainId i)) s _ e (tailValue s.executionEnv.calldata (nval i)::rho) hc
    simpa only [hn,large_return i hi] using gd.trans (gt.trans gc)

theorem allowed_index (n : Nat) (hn : RecognitionAccumulator.Allowed n) : ∃ i : Fin 14, nval i=n := by
  rcases hn with h|h|h|h|h|h|h|h|h|h|h|h|h|h
  · exact ⟨0, h.symm⟩
  · exact ⟨1, h.symm⟩
  · exact ⟨2, h.symm⟩
  · exact ⟨3, h.symm⟩
  · exact ⟨4, h.symm⟩
  · exact ⟨5, h.symm⟩
  · exact ⟨6, h.symm⟩
  · exact ⟨7, h.symm⟩
  · exact ⟨8, h.symm⟩
  · exact ⟨9, h.symm⟩
  · exact ⟨10, h.symm⟩
  · exact ⟨11, h.symm⟩
  · exact ⟨12, h.symm⟩
  · exact ⟨13, h.symm⟩

#print axioms gasSteps_for
#print axioms allowed_index
end Challenge.Ripemd160.Submission.Proofs.Bytecode.ReverseLiteralScan
