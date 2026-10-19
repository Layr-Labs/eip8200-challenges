import Challenge.Ripemd160.Submission.Proofs.Bytecode.RetainedTerminalMul.RetainedFirstWordRaw
import Challenge.Ripemd160.Submission.Proofs.Bytecode.CounterFreeSeedRaw
import Challenge.Ripemd160.Submission.Proofs.Bytecode.ZeroTailModel
import Challenge.Ripemd160.Submission.Proofs.Bytecode.RawExpressionAC
import Challenge.Ripemd160.Submission.Proofs.Bytecode.Low64RepeatMath

set_option warningAsError true
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.unusedSimpArgs false

/-! Focused, artifact-independent adapters. These are not a new submission
certificate: jump destination and execution environment facts remain explicit. -/
namespace RetainedIntegration105
open EvmSemantics EvmSemantics.EVM YulEvmCompiler Challenge.EvmProof
open Challenge.Ripemd160.Submission.Proofs.Bytecode
open StackRoundTrace StackRoundTemplate DirectLiteralModel DirectLiteralRawV4
open DenseScheduleTrace (runInstrSeq_append_running pcAfter_append)
open RetainedFirstWordResearch

/-- Low-64 screen: `SHL(calldata[0] XOR 0x6161616161616161, 192)`. -/
def anchorWord (input : ByteArray) : UInt256 :=
  Low64RepeatMath.condition input

theorem anchorWord_eq (input : ByteArray) : anchorWord input = Low64RepeatMath.condition input := rfl

theorem anchorWord_isTrue (input : ByteArray) (hne : anchorWord input ≠ 0) :
    UInt256.isTrue (anchorWord input) := by
  intro hz
  exact hne (Word.word_ext hz)

/-- A repeated `0x61` word makes the low 64 bits match, so the shifted XOR is zero. -/
theorem anchorWord_false (input : ByteArray)
    (h : KnownInputCompactState.referenceWord input = KnownInputData.fullWord) :
    ¬ UInt256.isTrue (anchorWord input) := by
  have h0 : anchorWord input = 0 := by
    unfold KnownInputCompactState.referenceWord at h
    unfold anchorWord Low64RepeatMath.condition
    rw [h]
    decide
  intro ht
  exact ht (by rw [h0]; rfl)

def anchorPrefix : List Instr :=
  [.push ⟨0, by decide⟩ 0, .op .CALLDATALOAD, .op (.Dup ⟨0, by decide⟩),
   .push ⟨8, by decide⟩ 0x6161616161616161, .op .XOR, .push ⟨1, by decide⟩ 192,
   .op .SHL, .push ⟨2, by decide⟩ 8157]

theorem run_anchor_prefix (s : State) (pc : UInt256) (rho : List UInt256)
    (hs : rho.length ≤ 980) (hrun : s.halt = .Running) :
    runInstrSeq anchorPrefix {s with pc := pc, stack := rho} =
      some {s with pc := pcAfter pc anchorPrefix, stack := [UInt256.ofNat 8157, anchorWord s.executionEnv.calldata, MachineState.readWord s.executionEnv.calldata 0] ++ rho} := by
  have hcap (n : Nat) (hn : n ≤ 20) : rho.length + n < 1024 := by omega
  simp (discharger := omega) [anchorPrefix, runInstrSeq, DataStepper.runInstr,
    pcAfter, hrun, show rho.length < 1024 by omega, hcap, UInt256.succ,
    Instr.size, Nat.add_assoc, Word.literal_eq_ofNat, Word.word_toNat_ofNat,
    anchorWord, Low64RepeatMath.condition, Low64Anchor.low64,
    KnownInputCompactState.referenceWord, List.getElem?_cons_zero]
  repeat first | apply And.intro | rfl

def anchorTemplate : List Instr := anchorPrefix ++ [.op .JUMPI]

theorem run_anchor_taken (s : State) (rho : List UInt256)
    (hs : rho.length ≤ 980) (hrun : s.halt = .Running)
    (hne : Low64RepeatMath.condition s.executionEnv.calldata ≠ 0)
    (hv : Decode.isValidJumpDest s.executionEnv.code 8157 = true) :
    runInstrSeq anchorTemplate {s with pc := UInt256.ofNat 21, stack := rho} =
      some {s with pc := UInt256.ofNat 8157, stack := MachineState.readWord s.executionEnv.calldata 0 :: rho} := by
  have hp := run_anchor_prefix s (UInt256.ofNat 21) rho hs hrun
  have ht := anchorWord_isTrue s.executionEnv.calldata (by rwa [anchorWord_eq])
  have hj : runInstrSeq [.op .JUMPI]
      {s with pc := pcAfter (UInt256.ofNat 21) anchorPrefix, stack := [UInt256.ofNat 8157, anchorWord s.executionEnv.calldata, MachineState.readWord s.executionEnv.calldata 0] ++ rho} =
      some {s with pc := UInt256.ofNat 8157, stack := MachineState.readWord s.executionEnv.calldata 0 :: rho} := by
    simp [runInstrSeq, DataStepper.runInstr, hrun,
      show rho.length + 3 < 1024 by omega, ht, hv, Word.word_toNat_ofNat]
  exact runInstrSeq_append_running hp hrun hj

theorem run_anchor_fall (s : State) (rho : List UInt256)
    (hs : rho.length ≤ 980) (hrun : s.halt = .Running)
    (heq : KnownInputCompactState.referenceWord s.executionEnv.calldata = KnownInputData.fullWord) :
    runInstrSeq anchorTemplate {s with pc := UInt256.ofNat 21, stack := rho} =
      some {s with pc := UInt256.ofNat 41, stack := MachineState.readWord s.executionEnv.calldata 0 :: rho} := by
  have hp := run_anchor_prefix s (UInt256.ofNat 21) rho hs hrun
  have ht := anchorWord_false s.executionEnv.calldata heq
  have hj : runInstrSeq [.op .JUMPI]
      {s with pc := pcAfter (UInt256.ofNat 21) anchorPrefix, stack := [UInt256.ofNat 8157, anchorWord s.executionEnv.calldata, MachineState.readWord s.executionEnv.calldata 0] ++ rho} =
      some {s with pc := UInt256.ofNat 41, stack := MachineState.readWord s.executionEnv.calldata 0 :: rho} := by
    simp [runInstrSeq, DataStepper.runInstr, hrun,
      show rho.length + 3 < 1024 by omega, ht, pcAfter, anchorPrefix, Instr.size,
      UInt256.succ, Word.word_toNat_ofNat]
    rfl
  exact runInstrSeq_append_running hp hrun hj

/-- PC41..50: no PUSH0/MLOAD/CALLDATALOAD warm-up; reuse retained r. -/
theorem run_anchor_low_fall (s : State) (rho : List UInt256)
    (hs : rho.length ≤ 980) (hrun : s.halt = .Running)
    (heq : Low64RepeatMath.condition s.executionEnv.calldata = 0) :
    runInstrSeq anchorTemplate {s with pc := UInt256.ofNat 21, stack := rho} =
      some {s with pc := UInt256.ofNat 41, stack := MachineState.readWord s.executionEnv.calldata 0 :: rho} := by
  have hp := run_anchor_prefix s (UInt256.ofNat 21) rho hs hrun
  have ht : ¬ UInt256.isTrue (anchorWord s.executionEnv.calldata) := by
    rw [anchorWord_eq, heq]
    decide
  have hj : runInstrSeq [.op .JUMPI]
      {s with pc := pcAfter (UInt256.ofNat 21) anchorPrefix, stack := [UInt256.ofNat 8157, anchorWord s.executionEnv.calldata, MachineState.readWord s.executionEnv.calldata 0] ++ rho} =
      some {s with pc := UInt256.ofNat 41, stack := MachineState.readWord s.executionEnv.calldata 0 :: rho} := by
    simp [runInstrSeq, DataStepper.runInstr, hrun,
      show rho.length + 3 < 1024 by omega, ht, pcAfter, anchorPrefix, Instr.size,
      UInt256.succ, Word.word_toNat_ofNat]
    rfl
  exact runInstrSeq_append_running hp hrun hj

/-- PC41..50: no PUSH0/MLOAD/CALLDATALOAD warm-up; reuse retained r. -/
def repeatTemplate : List Instr := CounterFreeSeedRaw.Seed.template ++ CounterFreeSeedRaw.jumpTemplate

theorem run_repeat (s : State) (rho : List UInt256)
    (hs : rho.length ≤ 980) (hrun : s.halt = .Running)
    (hv : Decode.isValidJumpDest s.executionEnv.code 9429 = true) :
    runInstrSeq repeatTemplate {s with pc := UInt256.ofNat 41, stack := MachineState.readWord s.executionEnv.calldata 0 :: rho} =
      some {s with pc := UInt256.ofNat 9429, stack := [DirectGuard.equalityAcc s.executionEnv.calldata 0, KnownInputCompactState.referenceWord s.executionEnv.calldata] ++ rho} := by
  have hc := CounterFreeSeedRaw.Seed.run_template s (UInt256.ofNat 41)
    (MachineState.readWord s.executionEnv.calldata 0) rho (by omega) hrun
  have hj := CounterFreeSeedRaw.run_jump s
    (pcAfter (UInt256.ofNat 41) CounterFreeSeedRaw.Seed.template)
    ([DirectGuard.equalityAcc s.executionEnv.calldata 0,
      KnownInputCompactState.referenceWord s.executionEnv.calldata] ++ rho)
    (by simp; omega) hrun hv
  have hh := runInstrSeq_append_running hc hrun hj
  simpa only [repeatTemplate, DirectGuard.equalityAcc,
    KnownInputCompactState.referenceWord] using hh

/-- One compare+OR for k>0. k=1 uses MSIZE=32, not an immediate. -/
def positiveStep (k : Nat) : List Instr :=
  (if k = 1 then [.push ⟨32, by decide⟩ (PatternedWordData.expectedWordAt 1),
      .op .MSIZE, .op .CALLDATALOAD, .op .XOR] else cmpTemplate k) ++ orTemplate

def positiveScan : Nat → List Instr
  | 0 => []
  | k+1 => positiveStep (k+1) ++ positiveScan k

theorem run_positive_step (s : State) (pc a : UInt256) (rho : List UInt256)
    (k : Nat) (hk : 0 < k ∧ k < 32) (hs : rho.length ≤ 980)
    (hrun : s.halt = .Running) (hm : s.msize = UInt256.ofNat 32) :
    runInstrSeq (positiveStep k) {s with pc := pc, stack := a :: rho} =
      some {s with pc := pcAfter pc (positiveStep k), stack := UInt256.lor (diff s.executionEnv.calldata k) a :: rho} := by
  by_cases he : k = 1
  · subst k
    have hcap (n : Nat) (hn : n ≤ 20) : rho.length + n < 1024 := by omega
    simp (discharger := omega) [positiveStep, orTemplate, diff, runInstrSeq,
      DataStepper.runInstr, pcAfter, hrun, show rho.length < 1024 by omega,
      hcap, hm, Word.word_toNat_ofNat, Word.literal_eq_ofNat, Instr.size,
      UInt256.succ, Nat.add_assoc]
    repeat first | apply And.intro | rfl
  · have hc := ReverseLiteralRaw.run_cmp0 s pc k hk.2 (a :: rho) (by simp; omega) hrun
    have ho := run_or s (pcAfter pc (cmpTemplate k)) (diff s.executionEnv.calldata k)
      a rho (by omega) hrun
    have hh := runInstrSeq_append_running hc hrun ho
    simpa only [positiveStep, if_neg he, pcAfter_append] using hh

theorem run_positive_scan (s : State) (pc a : UInt256) (rho : List UInt256)
    (k : Nat) (hk : k < 32) (hs : rho.length ≤ 980)
    (hrun : s.halt = .Running) (hm : s.msize = UInt256.ofNat 32) :
    runInstrSeq (positiveScan k) {s with pc := pc, stack := a :: rho} =
      some {s with pc := pcAfter pc (positiveScan k), stack := reversePositive s.executionEnv.calldata a k :: rho} := by
  induction k generalizing pc a with
  | zero => simp [positiveScan, reversePositive, runInstrSeq, pcAfter]
  | succ k ih =>
    have hc := run_positive_step s pc a rho (k+1) ⟨by omega, hk⟩ hs hrun hm
    have ht := ih (pcAfter pc (positiveStep (k+1)))
      (UInt256.lor (diff s.executionEnv.calldata (k+1)) a) (by omega)
    have hh := runInstrSeq_append_running hc hrun ht
    simpa only [positiveScan, reversePositive, pcAfter_append] using hh

/-- k31 is checked in full against its zero-padded literal. No shift remains. -/
def retainedResult (input : ByteArray) : UInt256 :=
  reversePositive input (diff input 0) 31

theorem retainedResult_eq (input : ByteArray) :
    retainedResult input = ZeroTailModel.result input 1000 := by
  have htail : diff input 31 = ZeroTailModel.tailDiff input 1000 := by
    unfold diff ZeroTailModel.tailDiff
    rw [DirectGuard.xor_comm']
    congr 1
  have he := reversePositive_seed input (UInt256.ofNat 0) 31
  change reversePositive input (UInt256.lor (diff input 0) 0) 31 = _ at he
  rw [lor_zero] at he
  rw [retainedResult, he, ReverseLiteralRaw.rev, htail]
  change ReverseLiteralRaw.rev input (UInt256.lor (ZeroTailModel.tailDiff input 1000) 0) 31 = _
  rw [lor_zero]
  rfl

theorem retainedResult_zero_iff (input : ByteArray) (hn : input.size = 1000) :
    retainedResult input = 0 ↔ input = RecognitionAccumulator.reference 1000 := by
  rw [retainedResult_eq]
  exact ZeroTailModel.result_zero_iff input 1000 (by unfold RecognitionAccumulator.Allowed; omega) hn

/-- Digest-store uses the original cold frame. MSIZE then supplies byte offset 32. -/
def storeTemplate (word : UInt256) : List Instr :=
  [.op .JUMPDEST, .push ⟨20, by decide⟩ word, .push ⟨0, by decide⟩ 0, .op .MSTORE]

def stored (s : State) (word : UInt256) : State :=
  {s with memory := MachineState.writeBytes s.memory (Data.Bytes.natToBytesPadded word.toNat 32) 0, activeWords := s.activeWordsAfterUInt256 0 32}

theorem run_store (s : State) (word : UInt256) (rho : List UInt256)
    (hs : rho.length ≤ 990) (hrun : s.halt = .Running) :
    runInstrSeq (storeTemplate word) {s with pc := UInt256.ofNat 8157, stack := rho} =
      some {(stored s word) with pc := UInt256.ofNat 8181, stack := rho} := by
  have hcap (n : Nat) (hn : n ≤ 20) : rho.length + n < 1024 := by omega
  simp (discharger := omega) [storeTemplate, stored, runInstrSeq, DataStepper.runInstr,
    hrun, UInt256.succ, Instr.size, Nat.add_assoc, Word.literal_eq_ofNat,
    show rho.length < 1024 by omega, hcap]
  repeat first | apply And.intro | rfl

def literalTemplate (word : UInt256) : List Instr :=
  (storeTemplate word ++ seedTemplate) ++ positiveScan 31

/-- Full private comparison body, up to the common JUMPI at PC9419.
Cold activeWords=0 is indispensable: otherwise the MSIZE offset is not 32. -/
theorem run_literal (s : State) (word : UInt256) (rho : List UInt256)
    (hs : rho.length ≤ 980) (hrun : s.halt = .Running)
    (ha : s.activeWords = UInt256.ofNat 0) :
    runInstrSeq (literalTemplate word)
      {s with pc := UInt256.ofNat 8157, stack := MachineState.readWord s.executionEnv.calldata 0 :: rho} =
      some {(stored s word) with pc := pcAfter (UInt256.ofNat 8157) (literalTemplate word), stack := retainedResult s.executionEnv.calldata :: rho} := by
  let w := stored s word
  have hwrun : w.halt = .Running := hrun
  have hwms : w.msize = UInt256.ofNat 32 := by
    simp [w, stored, MachineState.msize,
      State.activeWordsAfterUInt256, MachineState.activeWordsAfter, ha,
      Word.word_toNat_ofNat]
  have hstore := run_store s word
    (MachineState.readWord s.executionEnv.calldata 0 :: rho) (by simp; omega) hrun
  have hseed := run_seed w (UInt256.ofNat 8181) rho (by omega) hwrun
  have hbody := run_positive_scan w (pcAfter (UInt256.ofNat 8181) seedTemplate)
    (diff s.executionEnv.calldata 0) rho 31 (by decide) hs hwrun hwms
  have hb := runInstrSeq_append_running hstore hrun hseed
  have hh := runInstrSeq_append_running hb hwrun hbody
  have hpc : pcAfter (UInt256.ofNat 8157) (storeTemplate word) = UInt256.ofNat 8181 := by
    simp [pcAfter, storeTemplate, Instr.size, UInt256.succ, Word.literal_eq_ofNat]
    rfl
  simpa only [literalTemplate, pcAfter_append, hpc, retainedResult, w, stored] using hh

#print axioms run_literal

#print axioms run_anchor_taken
#print axioms run_anchor_fall
#print axioms run_repeat
#print axioms run_positive_scan
#print axioms retainedResult_zero_iff
end RetainedIntegration105
