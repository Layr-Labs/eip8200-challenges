import Challenge.Ripemd160.Submission.Proofs.Bytecode.ReverseLiteralRaw
import Challenge.Ripemd160.Submission.Proofs.Bytecode.DirectDigestRaw
import Challenge.Ripemd160.Submission.Proofs.Bytecode.ZeroTailModel
import Challenge.Ripemd160.Submission.Proofs.Bytecode.DenseScheduleTrace
import Challenge.Ripemd160.Submission.Proofs.Bytecode.StackSiteBuilder
import Challenge.Ripemd160.Submission.Proofs.Bytecode.HoistedInherited.StackRoundData
import Challenge.Ripemd160.Submission.Proofs.Bytecode.HoistedInherited.Artifact
set_option maxRecDepth 100000
set_option maxHeartbeats 16000000
set_option warningAsError true
set_option linter.unusedSimpArgs false
open EvmSemantics EvmSemantics.EVM YulEvmCompiler Challenge.EvmProof
open Challenge.Ripemd160.Submission.Proofs.Bytecode
open StackRoundTrace StackRoundTemplate DirectLiteralRawV4 DirectLiteralModel J2Moves ReverseLiteralRaw
namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.HoistedInherited.ReverseLiteralScan

abbrev lengths : List Nat := [1,31,32,55,56,63,64,65,119,120,128,256,376,1000]
def nval : Fin 13 → Nat
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
def tailPC : Fin 13 → Nat
 | ⟨0, _⟩ => 7629
 | ⟨1, _⟩ => 4825
 | ⟨2, _⟩ => 6520
 | ⟨3, _⟩ => 5212
 | ⟨4, _⟩ => 6714
 | ⟨5, _⟩ => 5004
 | ⟨6, _⟩ => 6610
 | ⟨7, _⟩ => 7413
 | ⟨8, _⟩ => 5510
 | ⟨9, _⟩ => 6863
 | ⟨10, _⟩ => 5330
 | ⟨11, _⟩ => 7829
 | ⟨12, _⟩ => 5690
def tailIndex : Fin 13 → Nat
 | ⟨0, _⟩ => 4812
 | ⟨1, _⟩ => 3476
 | ⟨2, _⟩ => 4220
 | ⟨3, _⟩ => 3722
 | ⟨4, _⟩ => 4274
 | ⟨5, _⟩ => 3600
 | ⟨6, _⟩ => 4256
 | ⟨7, _⟩ => 4715
 | ⟨8, _⟩ => 3782
 | ⟨9, _⟩ => 4337
 | ⟨10, _⟩ => 3754
 | ⟨11, _⟩ => 4958
 | ⟨12, _⟩ => 3810
def returnPC : Fin 13 → Nat
 | ⟨0, _⟩ => 7669
 | ⟨1, _⟩ => 4865
 | ⟨2, _⟩ => 6560
 | ⟨3, _⟩ => 5289
 | ⟨4, _⟩ => 6791
 | ⟨5, _⟩ => 5081
 | ⟨6, _⟩ => 6687
 | ⟨7, _⟩ => 7528
 | ⟨8, _⟩ => 5663
 | ⟨9, _⟩ => 7016
 | ⟨10, _⟩ => 5483
 | ⟨11, _⟩ => 8134
 | ⟨12, _⟩ => 6151


def cmpTemplate (k : Nat) : List Instr :=
 if k=1 then [.push ⟨32, by decide⟩ (PatternedWordData.expectedWordAt k),
   .op .MSIZE, .op .CALLDATALOAD, .op .XOR]
 else DirectLiteralRawV4.cmpTemplate k

def revTemplate (chain : Bool) : Nat → List Instr
 | 0 => []
 | k+1 => (if (chain = true ∧ (k=30)) then [.op .JUMPDEST] else []) ++
    (cmpTemplate k ++ orTemplate) ++ revTemplate chain k

def lastOffset (i : Fin 13) : List Instr :=
 if last (nval i) = 1 then [.op .MSIZE] else
 [.push ⟨if last (nval i) = 0 then 0 else if last (nval i) < 8 then 1 else 2,
     by split <;> (try split) <;> decide⟩ (UInt256.ofNat (32 * last (nval i)))]

def prefixTemplate (i : Fin 13) : List Instr :=
 [.push ⟨32, by decide⟩ (ZeroTailModel.expectedLast (nval i))] ++
 lastOffset i ++ [.op .CALLDATALOAD, .op .XOR]

def tailTemplate (i : Fin 13) : List Instr :=
  (prefixTemplate i ++ revTemplate false (last (nval i))) ++ resultTemplate

inductive Piece where
 | tail (i : Fin 13)

def template : Piece → List Instr
 | .tail i => tailTemplate i

def index : Piece → Nat
 | .tail i => tailIndex i

def pc : Piece → Nat
 | .tail i => tailPC i

set_option maxHeartbeats 16000000 in
theorem actual_slice (p : Piece) :
  (HoistedInherited.Artifact.submissionArtifact.instructions.drop (index p)).take (template p).length = template p := by
  cases p with
  | tail i => fin_cases i <;> rfl

theorem bounds (p : Piece) : index p + (template p).length ≤ HoistedInherited.Artifact.submissionInstructions.length := by
  rw [HoistedInherited.Artifact.referenceInstructions_count]
  cases p with
  | tail i => fin_cases i <;> decide

theorem wellFormed (p : Piece) : HoistedInherited.StackRoundData.TemplateWellFormed (template p) := by
  cases p with
  | tail i => fin_cases i <;> decide

theorem nonempty (p : Piece) : template p ≠ [] := by
  cases p with
  | tail i => fin_cases i <;> decide

def site (p : Piece) : GenericRoundSite HoistedInherited.Artifact.submissionArtifact .Osaka (template p) :=
  StackSiteBuilder.ofSlice (template p) (index p) (actual_slice p) (bounds p)
    HoistedInherited.StackRoundData.artifact_code_bound (HoistedInherited.StackRoundData.templateWellFormed_mem (wellFormed p)) (nonempty p)

theorem site_pc (p : Piece) : (site p).startPC = UInt256.ofNat (pc p) := by
  change UInt256.ofNat (HoistedInherited.Artifact.submissionArtifact.instructionPC (index p)) = UInt256.ofNat (pc p)
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  cases p with
  | tail i => fin_cases i <;> decide

theorem form (p : Piece) : ∀ i ∈ (template p).dropLast, RecognitionLift.Advances i := by
  apply RecognitionLift.advancesAll_sound
  cases p with
  | tail i => fin_cases i <;> decide

structure Env (s : State) : Prop where
  code : s.executionEnv.code = HoistedInherited.Artifact.submissionArtifact.code
  fork : s.fork = .Osaka
  run : s.halt = .Running
  active : s.activeWords = UInt256.ofNat 1
  np : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
    s.executionEnv.fork s.executionEnv.codeAddr = false

def lift (p : Piece) (s t : State) (e : Env s) (stack : List UInt256)
    (hraw : runInstrSeq (template p) (atState s (pc p) stack) = some t) :
    GasSteps (atState s (pc p) stack) t :=
  RecognitionLift.gasSteps_of_raw (site p) _ t e.code e.fork e.run e.np
    (by simpa [atState] using (site_pc p).symm) (form p) hraw


theorem run_cmpSize (s : State) (pc : UInt256) (k : Nat) (hk : k<32)
    (a : UInt256) (rho : List UInt256) (hs : rho.length ≤ 990)
    (hrun : s.halt = .Running) (ha : s.activeWords = UInt256.ofNat 1) :
    runInstrSeq (cmpTemplate k) {s with pc:=pc,stack:=a::rho} =
      some {s with pc:=pcAfter pc (cmpTemplate k),stack:=diff s.executionEnv.calldata k::a::rho} := by
  by_cases hk1 : k=1
  · subst k
    have hcap (n : Nat) (hn : n ≤ 20) : rho.length+n<1024 := by omega
    simp (discharger := omega) [cmpTemplate,diff,runInstrSeq,DataStepper.runInstr,pcAfter,
      hrun,show rho.length<1024 by omega,hcap,UInt256.succ,Instr.size,Nat.add_assoc,
      Word.literal_eq_ofNat,List.getElem?_cons_zero,List.exchange,MachineState.msize,ha]
    repeat first | apply And.intro | rfl
  · simpa only [cmpTemplate,if_neg hk1] using DirectLiteralRawV4.run_cmp s pc k hk a rho hs hrun

theorem run_revTemplate (s : State) (pc : UInt256) (a : UInt256) (rho : List UInt256)
    (hs : rho.length ≤ 990) (hrun : s.halt = .Running)
    (ha : s.activeWords = UInt256.ofNat 1) (chain : Bool)
    (k : Nat) (hk : k ≤ 32) :
    runInstrSeq (revTemplate chain k) {s with pc:=pc,stack:=a::rho} =
      some {s with pc:=pcAfter pc (revTemplate chain k),stack:=rev s.executionEnv.calldata a k ::rho} := by
  induction k generalizing pc a with
  | zero => simp [revTemplate,runInstrSeq,pcAfter,rev]
  | succ k ih =>
    let dest : List Instr := if (chain = true ∧ (k=30)) then [.op .JUMPDEST] else []
    have hd : runInstrSeq dest {s with pc:=pc,stack:=a::rho} =
        some {s with pc:=pcAfter pc dest,stack:=a::rho} := by
      by_cases h : (chain = true ∧ (k=30))
      · simpa only [dest,if_pos h] using run_jd s pc (a::rho) (by simp;omega) hrun
      · simp [dest,h,runInstrSeq,pcAfter]
    have hc := run_cmpSize s (pcAfter pc dest) k (by omega) a rho hs hrun ha
    have ho := run_or s (pcAfter (pcAfter pc dest) (cmpTemplate k))
      (diff s.executionEnv.calldata k) a rho hs hrun
    have hco := DenseScheduleTrace.runInstrSeq_append_running hc hrun ho
    have hdc := DenseScheduleTrace.runInstrSeq_append_running hd hrun hco
    have hi := ih (pcAfter pc (dest ++ (cmpTemplate k ++ orTemplate)))
      (UInt256.lor (diff s.executionEnv.calldata k) a) (by omega)
    simp only [DenseScheduleTrace.pcAfter_append] at hi hdc
    have hall := DenseScheduleTrace.runInstrSeq_append_running hdc hrun hi
    simpa only [revTemplate,dest,DenseScheduleTrace.pcAfter_append,rev] using hall

theorem run_prefix (s : State) (pc : UInt256) (i : Fin 13) (rho : List UInt256)
    (hs : rho.length ≤ 990) (hrun : s.halt = .Running)
    (ha : s.activeWords = UInt256.ofNat 1) :
    runInstrSeq (prefixTemplate i) {s with pc:=pc,stack:=rho} =
      some {s with pc:=pcAfter pc (prefixTemplate i),stack:=ZeroTailModel.tailDiff s.executionEnv.calldata (nval i)::rho} := by
  have hcap (n : Nat) (hn : n ≤ 20) : rho.length+n<1024 := by omega
  have hk : last (nval i) < 32 := by fin_cases i <;> decide
  have hoff : (UInt256.ofNat (32*last (nval i))).toNat = 32*last (nval i) := by
    rw [Word.word_toNat_ofNat,Nat.mod_eq_of_lt (by omega)]
  by_cases hk1 : last (nval i)=1
  · simp (discharger := omega) [prefixTemplate,lastOffset,hk1,ZeroTailModel.tailDiff,
      runInstrSeq,DataStepper.runInstr,pcAfter,hrun,show rho.length<1024 by omega,hcap,
      UInt256.succ,Instr.size,Nat.add_assoc,Word.literal_eq_ofNat,
      List.getElem?_cons_zero,List.exchange,MachineState.msize,ha]
    repeat first | apply And.intro | rfl | exact RawExpressionAC.xor_comm _ _
  by_cases hk0 : last (nval i)=0
  · simp (discharger := omega) [prefixTemplate,lastOffset,hk1,ZeroTailModel.tailDiff, hk0, runInstrSeq,DataStepper.runInstr,
      pcAfter,hrun,show rho.length<1024 by omega,hcap,UInt256.succ,Instr.size,Nat.add_assoc,
      Word.literal_eq_ofNat,List.getElem?_cons_zero,List.exchange]
    repeat first | apply And.intro | rfl | exact RawExpressionAC.xor_comm _ _
  by_cases hk8 : last (nval i)<8
  all_goals simp (discharger := omega) [prefixTemplate,lastOffset,hk1,ZeroTailModel.tailDiff,hk0,hk8,runInstrSeq,DataStepper.runInstr,
    pcAfter,hrun,show rho.length<1024 by omega,hcap,UInt256.succ,Instr.size,Nat.add_assoc,hoff,
    Word.literal_eq_ofNat,List.getElem?_cons_zero,List.exchange]
  all_goals repeat first | apply And.intro | rfl | exact RawExpressionAC.xor_comm _ _

theorem tail_end (i : Fin 13) :
    pcAfter (UInt256.ofNat (tailPC i)) (tailTemplate i) = UInt256.ofNat (returnPC i) := by
  fin_cases i <;> decide

theorem run_small (s : State) (e : Env s) (rho : List UInt256) (hs : rho.length ≤ 990)
    (i : Fin 13)
    (hv : Decode.isValidJumpDest s.executionEnv.code 4785 = true) :
    runInstrSeq (tailTemplate i) (atState s (tailPC i) rho) =
      some (atState s (if (ZeroTailModel.result s.executionEnv.calldata (nval i)).toNat=0 then returnPC i else 4785) rho) := by
  have hp := run_prefix s (UInt256.ofNat (tailPC i)) i rho hs e.run e.active
  have hr := run_revTemplate s (pcAfter (UInt256.ofNat (tailPC i)) (prefixTemplate i))
    (ZeroTailModel.tailDiff s.executionEnv.calldata (nval i)) rho hs e.run e.active false (last (nval i)) (by fin_cases i <;> decide)
  have hpr := DenseScheduleTrace.runInstrSeq_append_running hp e.run hr
  rw [← ZeroTailModel.result] at hpr
  have hf := run_result s
    (pcAfter (pcAfter (UInt256.ofNat (tailPC i)) (prefixTemplate i)) (revTemplate false (last (nval i))))
    (ZeroTailModel.result s.executionEnv.calldata (nval i)) rho hs e.run hv
  have hall := DenseScheduleTrace.runInstrSeq_append_running hpr e.run hf
  have he := tail_end i
  simp only [tailTemplate,DenseScheduleTrace.pcAfter_append] at he
  simpa only [tailTemplate,atState,DenseScheduleTrace.pcAfter_append,he,apply_ite] using hall

theorem valid_fallback : Decode.isValidJumpDest HoistedInherited.Artifact.submissionArtifact.code 4785 = true := by
  have hp : HoistedInherited.Artifact.submissionArtifact.instructionPC 3457 = 4785 := by
    rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide
  have h := HoistedInherited.Artifact.submissionArtifact.isValidJumpDest_index 3457 (by rfl)
  rw [hp] at h
  exact h

theorem source_target (i : Fin 13) :
    UInt256.add (UInt256.ofNat 24) (DirectDigestRaw.selected (UInt256.ofNat 8191) (nval i)) = UInt256.ofNat (tailPC i) := by
  fin_cases i <;> decide

def gasSteps_for (s : State) (e : Env s) (rho : List UInt256) (hs : rho.length ≤ 988)
    (i : Fin 13) (hn : s.executionEnv.calldata.size = nval i) :
    GasSteps (atState s (tailPC i) rho)
      (atState s (if (ZeroTailModel.result s.executionEnv.calldata s.executionEnv.calldata.size).toNat=0 then returnPC i else 4785) rho) := by
  have hvf : Decode.isValidJumpDest s.executionEnv.code 4785 = true := by rw [e.code]; exact valid_fallback
  have hr := run_small s e rho (by omega) i hvf
  have gt := lift (.tail i) s _ e rho hr
  simpa only [hn,pc] using gt

theorem allowed_index (n : Nat) (hn : RecognitionAccumulator.Allowed n) (hne : n ≠ 1000) : ∃ i : Fin 13, nval i=n := by
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
  · exact False.elim (hne h)

#print axioms gasSteps_for
#print axioms allowed_index
end Challenge.Ripemd160.Submission.Proofs.Bytecode.HoistedInherited.ReverseLiteralScan
