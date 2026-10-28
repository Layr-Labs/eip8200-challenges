import Challenge.Ripemd160.Submission.Proofs.Bytecode.HoistedInherited.StackRoundData
import Challenge.Ripemd160.Submission.Proofs.Bytecode.ReverseLiteralRaw
import Challenge.Ripemd160.Submission.Proofs.Bytecode.DirectDigestRaw
import Challenge.Ripemd160.Submission.Proofs.Bytecode.ZeroTailModel
import Challenge.Ripemd160.Submission.Proofs.Bytecode.RecognitionDigest
import Challenge.Ripemd160.Submission.Proofs.Bytecode.RecognitionSelectorRaw
import Challenge.Ripemd160.Submission.Proofs.Bytecode.J2Moves
import Challenge.Ripemd160.Submission.Proofs.Bytecode.DenseScheduleTrace
import Challenge.Ripemd160.Submission.Proofs.Bytecode.StackSiteBuilder
import Challenge.Ripemd160.Submission.Proofs.Bytecode.RecognitionLift
import Challenge.Ripemd160.ProofSupport.InitialState
set_option warningAsError true
set_option maxRecDepth 100000
set_option maxHeartbeats 16000000
set_option linter.unusedSimpArgs false

/-!
# Compact patterned arms: one shared descending word chain

Each patterned arm stores its digest, computes the zero-tail difference of its
top word (or an empty accumulator when its length is a multiple of 32) and
jumps into one shared chain of eight literal word checks.  Entered at the
arm's first full word, the chain computes exactly the old per-arm reverse scan
value `ZeroTailModel.result`.
-/

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.Arms.Scan
open Challenge.Ripemd160 EvmSemantics EvmSemantics.EVM YulEvmCompiler Challenge.EvmProof
open Challenge.Ripemd160.Submission.Proofs.Bytecode
open StackRoundTrace StackRoundTemplate DirectLiteralRawV4 DirectLiteralModel J2Moves ReverseLiteralRaw

/-! ## Layout -/

def failPC : Nat := 8078

/-- Chain entry JUMPDESTs. -/
def chainEntry (k : Nat) : Bool := k = 7 ∨ k = 3 ∨ k = 2 ∨ k = 1 ∨ k = 0

/-- Sizes with a chain arm. -/
def nval : Fin 12 → Nat
 | ⟨0, _⟩ => 1 | ⟨1, _⟩ => 31 | ⟨2, _⟩ => 32 | ⟨3, _⟩ => 55 | ⟨4, _⟩ => 56 | ⟨5, _⟩ => 63
 | ⟨6, _⟩ => 64 | ⟨7, _⟩ => 65 | ⟨8, _⟩ => 119 | ⟨9, _⟩ => 120 | ⟨10, _⟩ => 128 | ⟨11, _⟩ => 256

def armIndex : Fin 12 → Nat
 | ⟨0, _⟩ => 6164 | ⟨1, _⟩ => 6299 | ⟨2, _⟩ => 6312 | ⟨3, _⟩ => 6319 | ⟨4, _⟩ => 6329 | ⟨5, _⟩ => 6339
 | ⟨6, _⟩ => 6349 | ⟨7, _⟩ => 6356 | ⟨8, _⟩ => 6366 | ⟨9, _⟩ => 6376 | ⟨10, _⟩ => 6386 | ⟨11, _⟩ => 6393

def armPC : Fin 12 → Nat
 | ⟨0, _⟩ => 8180 | ⟨1, _⟩ => 8761 | ⟨2, _⟩ => 8828 | ⟨3, _⟩ => 8857 | ⟨4, _⟩ => 8921 | ⟨5, _⟩ => 8985
 | ⟨6, _⟩ => 9049 | ⟨7, _⟩ => 9078 | ⟨8, _⟩ => 9143 | ⟨9, _⟩ => 9208 | ⟨10, _⟩ => 9273 | ⟨11, _⟩ => 9302

/-- Number of chain words below the arm's own tail (zero for the two one-word arms). -/
def chainWords : Fin 12 → Nat
 | ⟨0, _⟩ => 0 | ⟨1, _⟩ => 0 | ⟨2, _⟩ => 1 | ⟨3, _⟩ => 1 | ⟨4, _⟩ => 1 | ⟨5, _⟩ => 1
 | ⟨6, _⟩ => 2 | ⟨7, _⟩ => 2 | ⟨8, _⟩ => 3 | ⟨9, _⟩ => 3 | ⟨10, _⟩ => 4 | ⟨11, _⟩ => 8

def chainPC : Nat → Nat
  | 8 => 8446 | 4 => 8599 | 3 => 8638 | 2 => 8677 | 1 => 8715 | _ => 0
def chainIndex : Nat → Nat
  | 8 => 6249 | 4 => 6270 | 3 => 6276 | 2 => 6282 | 1 => 6288 | _ => 0

/-- Index and PC of the success `MSIZE` after the result branch. -/
def returnIndex (i : Fin 12) : Nat := if i.val = 0 then 6174 else if i.val = 1 then 6309 else 6296
def returnPC (i : Fin 12) : Nat := if i.val = 0 then 8244 else if i.val = 1 then 8825 else 8758

/-! ## Templates -/

def cmpTemplate (k : Nat) : List Instr :=
 if k=1 then [.push ⟨32, by decide⟩ (PatternedWordData.expectedWordAt k),
   .op .MSIZE, .op .CALLDATALOAD, .op .XOR]
 else DirectLiteralRawV4.cmpTemplate k

def lastOffset (n : Nat) : List Instr :=
 if last n = 1 then [.op .MSIZE] else
 [.push ⟨if last n = 0 then 0 else if last n < 8 then 1 else 2,
     by split <;> (try split) <;> decide⟩ (UInt256.ofNat (32 * last n))]

def prefixTemplate (n : Nat) : List Instr :=
 [.push ⟨32, by decide⟩ (ZeroTailModel.expectedLast n)] ++
 lastOffset n ++ [.op .CALLDATALOAD, .op .XOR]

/-- An arm's own first accumulator: the masked top word, or an empty accumulator. -/
def startTemplate (n : Nat) : List Instr :=
  if n % 32 = 0 then [.push ⟨0, by decide⟩ (UInt256.ofNat 0)] else prefixTemplate n

def resultTemplate : List Instr :=
  [.push ⟨2, by decide⟩ (UInt256.ofNat 8078), .op .JUMPI]

def revE : Nat → List Instr
  | 0 => []
  | k+1 => (if chainEntry k then [.op .JUMPDEST] else []) ++
      (cmpTemplate k ++ orTemplate) ++ revE k

/-- The chain's own result branch, with a widened push. -/
def chainResultTemplate : List Instr :=
  [.push ⟨3, by decide⟩ (UInt256.ofNat 8078), .op .JUMPI]

def chainTemplate (k : Nat) : List Instr := revE k ++ chainResultTemplate

def armTemplate (i : Fin 12) : List Instr :=
  if chainWords i = 0 then
    DirectDigestRaw.storeTemplate (RecognitionDigest.paddedDigestWord (nval i)) ++
      prefixTemplate (nval i) ++ resultTemplate
  else
    DirectDigestRaw.storeTemplate (RecognitionDigest.paddedDigestWord (nval i)) ++
      startTemplate (nval i) ++ jumpTemplate (chainPC (chainWords i))

def finishTemplate : List Instr := [.op .MSIZE, .push ⟨0, by decide⟩ 0, .op .RETURN]

/-! ## Raw runs -/

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

theorem run_revE (s : State) (pc : UInt256) (a : UInt256) (rho : List UInt256)
    (hs : rho.length ≤ 990) (hrun : s.halt = .Running)
    (ha : s.activeWords = UInt256.ofNat 1) (k : Nat) (hk : k ≤ 32) :
    runInstrSeq (revE k) {s with pc:=pc,stack:=a::rho} =
      some {s with pc:=pcAfter pc (revE k),stack:=rev s.executionEnv.calldata a k ::rho} := by
  induction k generalizing pc a with
  | zero => simp [revE,runInstrSeq,pcAfter,rev]
  | succ k ih =>
    let dest : List Instr := if chainEntry k then [.op .JUMPDEST] else []
    have hd : runInstrSeq dest {s with pc:=pc,stack:=a::rho} =
        some {s with pc:=pcAfter pc dest,stack:=a::rho} := by
      by_cases h : chainEntry k
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
    simpa only [revE,dest,DenseScheduleTrace.pcAfter_append,rev] using hall

theorem run_result (s : State) (pc : UInt256) (a : UInt256) (rho : List UInt256)
    (hs : rho.length ≤ 990) (hrun : s.halt = .Running)
    (hv : Decode.isValidJumpDest s.executionEnv.code 8078 = true) :
    runInstrSeq resultTemplate {s with pc := pc, stack := a :: rho} =
      some {s with
        pc := if a.toNat = 0 then pcAfter pc resultTemplate else UInt256.ofNat 8078
        stack := rho} := by
  have hcap (n : Nat) (hn : n ≤ 20) : rho.length + n < 1024 := by omega
  by_cases hz : a.toNat = 0
  all_goals simp (discharger := omega) [resultTemplate, hz, runInstrSeq, DataStepper.runInstr,
    pcAfter, hrun, show rho.length < 1024 by omega, hcap, UInt256.succ, Instr.size,
    Nat.add_assoc, hv, Word.word_toNat_ofNat, Word.literal_eq_ofNat, UInt256.isTrue]
  all_goals rfl

theorem run_chainResult (s : State) (pc : UInt256) (a : UInt256) (rho : List UInt256)
    (hs : rho.length ≤ 990) (hrun : s.halt = .Running)
    (hv : Decode.isValidJumpDest s.executionEnv.code 8078 = true) :
    runInstrSeq chainResultTemplate {s with pc := pc, stack := a :: rho} =
      some {s with
        pc := if a.toNat = 0 then pcAfter pc chainResultTemplate else UInt256.ofNat 8078
        stack := rho} := by
  have hcap (n : Nat) (hn : n ≤ 20) : rho.length + n < 1024 := by omega
  by_cases hz : a.toNat = 0
  all_goals simp (discharger := omega) [chainResultTemplate, hz, runInstrSeq, DataStepper.runInstr,
    pcAfter, hrun, show rho.length < 1024 by omega, hcap, UInt256.succ, Instr.size,
    Nat.add_assoc, hv, Word.word_toNat_ofNat, Word.literal_eq_ofNat, UInt256.isTrue]
  all_goals rfl

theorem run_chain (s : State) (pc : UInt256) (a : UInt256) (rho : List UInt256)
    (hs : rho.length ≤ 990) (hrun : s.halt = .Running)
    (ha : s.activeWords = UInt256.ofNat 1) (k : Nat) (hk : k ≤ 32)
    (hv : Decode.isValidJumpDest s.executionEnv.code 8078 = true) :
    runInstrSeq (chainTemplate k) {s with pc:=pc,stack:=a::rho} =
      some {s with
        pc := if (rev s.executionEnv.calldata a k).toNat = 0 then pcAfter pc (chainTemplate k)
          else UInt256.ofNat 8078
        stack := rho} := by
  have h1 := run_revE s pc a rho hs hrun ha k hk
  have h3 := run_chainResult s (pcAfter pc (revE k)) (rev s.executionEnv.calldata a k) rho hs hrun hv
  have hall := DenseScheduleTrace.runInstrSeq_append_running h1 hrun h3
  simpa only [chainTemplate, DenseScheduleTrace.pcAfter_append] using hall

theorem run_prefix (s : State) (pc : UInt256) (n : Nat) (hk : last n < 32) (rho : List UInt256)
    (hs : rho.length ≤ 990) (hrun : s.halt = .Running)
    (ha : s.activeWords = UInt256.ofNat 1) :
    runInstrSeq (prefixTemplate n) {s with pc:=pc,stack:=rho} =
      some {s with pc:=pcAfter pc (prefixTemplate n),stack:=ZeroTailModel.tailDiff s.executionEnv.calldata n::rho} := by
  have hcap (n : Nat) (hn : n ≤ 20) : rho.length+n<1024 := by omega
  have hoff : (UInt256.ofNat (32*last n)).toNat = 32*last n := by
    rw [Word.word_toNat_ofNat,Nat.mod_eq_of_lt (by omega)]
  by_cases hk1 : last n=1
  · simp (discharger := omega) [prefixTemplate,lastOffset,hk1,ZeroTailModel.tailDiff,
      runInstrSeq,DataStepper.runInstr,pcAfter,hrun,show rho.length<1024 by omega,hcap,
      UInt256.succ,Instr.size,Nat.add_assoc,Word.literal_eq_ofNat,
      List.getElem?_cons_zero,List.exchange,MachineState.msize,ha]
    repeat first | apply And.intro | rfl | exact RawExpressionAC.xor_comm _ _
  by_cases hk0 : last n=0
  · simp (discharger := omega) [prefixTemplate,lastOffset,hk1,ZeroTailModel.tailDiff, hk0, runInstrSeq,DataStepper.runInstr,
      pcAfter,hrun,show rho.length<1024 by omega,hcap,UInt256.succ,Instr.size,Nat.add_assoc,
      Word.literal_eq_ofNat,List.getElem?_cons_zero,List.exchange]
    repeat first | apply And.intro | rfl | exact RawExpressionAC.xor_comm _ _
  by_cases hk8 : last n<8
  all_goals simp (discharger := omega) [prefixTemplate,lastOffset,hk1,ZeroTailModel.tailDiff,hk0,hk8,runInstrSeq,DataStepper.runInstr,
    pcAfter,hrun,show rho.length<1024 by omega,hcap,UInt256.succ,Instr.size,Nat.add_assoc,hoff,
    Word.literal_eq_ofNat,List.getElem?_cons_zero,List.exchange]
  all_goals repeat first | apply And.intro | rfl | exact RawExpressionAC.xor_comm _ _

/-! ## States -/

def base (input : ByteArray) : State := initialState HoistedInherited.submissionBytecode input 0

def digestMemory (n : Nat) : ByteArray :=
  MachineState.writeBytes ByteArray.empty
    (Data.Bytes.natToBytesPadded (RecognitionDigest.paddedDigestWord n).toNat 32) 0

def prepared (input : ByteArray) (n : Nat) : State :=
  {base input with activeWords := UInt256.ofNat 1, memory := digestMemory n}

@[simp] theorem prepared_activeWords (input : ByteArray) (n : Nat) :
    (prepared input n).activeWords = UInt256.ofNat 1 := rfl
@[simp] theorem prepared_calldata (input : ByteArray) (n : Nat) :
    (prepared input n).executionEnv.calldata = input := rfl
@[simp] theorem prepared_code (input : ByteArray) (n : Nat) :
    (prepared input n).executionEnv.code = HoistedInherited.Artifact.submissionArtifact.code := rfl
@[simp] theorem prepared_run (input : ByteArray) (n : Nat) :
    (prepared input n).halt = .Running := rfl

theorem digestMemory_size (n : Nat) : (digestMemory n).size = 32 := by
  rw [digestMemory, MachineState.writeBytes_size]
  simp [YulEvmCompiler.BytesLemmas.natToBytesPadded_size]

/-- Digest store from the zero-memory frame. -/
theorem run_store (input : ByteArray) (pc : UInt256) (n : Nat) :
    runInstrSeq (DirectDigestRaw.storeTemplate (RecognitionDigest.paddedDigestWord n))
      {base input with pc := pc, stack := []} =
      some {prepared input n with pc := UInt256.add (UInt256.ofNat 24) pc, stack := []} := by
  have hac : (base input).activeWordsAfterUInt256 0 32 = UInt256.ofNat 1 := by
    simp [State.activeWordsAfterUInt256,base,initialState,Word.word_toNat_ofNat]
    rfl
  have hr := DirectDigestRaw.run_store (base input) pc
    (RecognitionDigest.paddedDigestWord n) [] (by simp) rfl
  rw [hr]
  simp only [DirectDigestRaw.stored, hac, DirectDigestRaw.store_pc, prepared, base, digestMemory]
  rfl

/-! ## Values -/

def startValue (input : ByteArray) (n : Nat) : UInt256 :=
  if n % 32 = 0 then UInt256.ofNat 0 else ZeroTailModel.tailDiff input n

theorem run_start (s : State) (pc : UInt256) (n : Nat) (hk : last n < 32) (rho : List UInt256)
    (hs : rho.length ≤ 990) (hrun : s.halt = .Running)
    (ha : s.activeWords = UInt256.ofNat 1) :
    runInstrSeq (startTemplate n) {s with pc:=pc,stack:=rho} =
      some {s with pc:=pcAfter pc (startTemplate n),stack:=startValue s.executionEnv.calldata n::rho} := by
  by_cases hf : n % 32 = 0
  · simp (discharger := omega) [startTemplate, startValue, hf, runInstrSeq, DataStepper.runInstr,
      pcAfter, hrun, show rho.length < 1024 by omega, UInt256.succ, Instr.size]
    exact ⟨rfl, rfl⟩
  · simpa only [startTemplate, startValue, if_neg hf] using run_prefix s pc n hk rho hs hrun ha

theorem valid_at (index pc : Nat) (hj : HoistedInherited.Artifact.submissionArtifact.instructions[index]? = some (.op .JUMPDEST))
    (hp : HoistedInherited.Artifact.submissionArtifact.instructionPC index = pc) :
    Decode.isValidJumpDest HoistedInherited.Artifact.submissionArtifact.code pc = true := by
  have h := HoistedInherited.Artifact.submissionArtifact.isValidJumpDest_index index hj
  rw [hp] at h
  exact h

theorem valid_fail : Decode.isValidJumpDest HoistedInherited.Artifact.submissionArtifact.code 8078 = true :=
  valid_at 6086 8078 (by rfl) (by rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide)

theorem lor_ofNat_zero (a : UInt256) : UInt256.lor a (UInt256.ofNat 0) = a := DirectLiteralRawV4.lor_zero a

theorem value_partial (input : ByteArray) (n : Nat) (hn : n % 32 ≠ 0) :
    rev input (startValue input n) (last n) = ZeroTailModel.result input n := by
  simp only [startValue, if_neg hn]
  rfl

theorem value_full (input : ByteArray) (n : Nat) (hn : n % 32 = 0)
    (he : ZeroTailModel.expectedLast n = PatternedWordData.expectedWordAt (last n)) :
    rev input (startValue input n) (last n + 1) = ZeroTailModel.result input n := by
  simp only [startValue, if_pos hn, rev, ZeroTailModel.result, ZeroTailModel.tailDiff, he, diff,
    lor_ofNat_zero]
  rw [RawExpressionAC.xor_comm]

end Challenge.Ripemd160.Submission.Proofs.Bytecode.Arms.Scan
