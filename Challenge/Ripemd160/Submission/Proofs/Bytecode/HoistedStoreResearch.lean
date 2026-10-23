import Challenge.Ripemd160.Submission.Proofs.Bytecode.PcSeedRaw
import Challenge.Ripemd160.Submission.Proofs.Bytecode.PcSeedMath
import Challenge.Ripemd160.Submission.Proofs.Bytecode.ExactGuardSpec
import Challenge.Ripemd160.Submission.Proofs.Bytecode.RetainedTerminalMul.CleanupBridge
import Challenge.Ripemd160.Submission.Proofs.Bytecode.RetainedTerminalMul.FallbackBridge

set_option warningAsError true
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000

/-! Research only: raw seed/scanner/return and cleared-copy fallback proofs,
plus assembly certificates for the changed instruction windows.
The proposed hoisted-store scanner uses MSIZE=32 instead of PUSH1 16.
Its zero/nonzero result agrees universally with the retained recognizer.
Whole-program artifact binding and universal candidate correctness remain open.
The deployed bytecode and its existing certificate are intentionally unchanged. -/
namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.HoistedStoreResearch
open EvmSemantics EvmSemantics.EVM YulEvmCompiler Challenge.EvmProof

private theorem pair_parts (a b c d : Nat)
    (hb : b < 256^16) (hd : d < 256^16)
    (h : a * 256^16 + b = c * 256^16 + d) : a = c ∧ b = d := by
  have left : (a * 256^16 + b) / 256^16 = a := by
    rw [Nat.add_comm, Nat.mul_comm a, Nat.add_mul_div_left _ _ (by norm_num),
      Nat.div_eq_of_lt hb, Nat.zero_add]
  have right : (c * 256^16 + d) / 256^16 = c := by
    rw [Nat.add_comm, Nat.mul_comm c, Nat.add_mul_div_left _ _ (by norm_num),
      Nat.div_eq_of_lt hd, Nat.zero_add]
  have heq : a = c := by
    have hh := congrArg (fun n => n / 256^16) h
    rwa [left, right] at hh
  exact ⟨heq, by rw [heq] at h; omega⟩

/-- A reference word at offset 48 forces the middle two overlapping windows
at offsets 16 and 32 to equal the reference together, or neither to do so. -/
theorem overlapping_windows (input : ByteArray)
    (h48 : MachineState.readWord input 48 = MachineState.readWord input 0) :
    MachineState.readWord input 16 = MachineState.readWord input 0 ↔
      MachineState.readWord input 32 = MachineState.readWord input 0 := by
  have h48n := congrArg UInt256.toNat h48
  simp only [Bytes.readWord_toNat] at h48n
  have h0 := Bytes.bytesToNatPadded_add input 0 16 16
  have h16 := Bytes.bytesToNatPadded_add input 16 16 16
  have h32 := Bytes.bytesToNatPadded_add input 32 16 16
  have h48' := Bytes.bytesToNatPadded_add input 48 16 16
  simp only [Nat.reduceAdd] at h0 h16 h32 h48'
  have hb0 := Bytes.bytesToNatPadded_lt_pow input 0 16
  have hb16 := Bytes.bytesToNatPadded_lt_pow input 16 16
  have hb32 := Bytes.bytesToNatPadded_lt_pow input 32 16
  have hb48 := Bytes.bytesToNatPadded_lt_pow input 48 16
  have hb64 := Bytes.bytesToNatPadded_lt_pow input 64 16
  have heq48 : Precompile.bytesToNatPadded input 48 16 =
      Precompile.bytesToNatPadded input 0 16 :=
    (pair_parts _ _ _ _ hb64 hb16 (by rw [← h48', ← h0]; exact h48n)).1
  constructor
  · intro h
    have hn := congrArg UInt256.toNat h
    simp only [Bytes.readWord_toNat] at hn
    obtain ⟨hba, hcb⟩ := pair_parts _ _ _ _ hb32 hb16
      (by rw [← h16, ← h0]; exact hn)
    apply Word.word_ext
    simp only [Bytes.readWord_toNat]
    rw [h32, h0, hcb, hba, heq48]
  · intro h
    have hn := congrArg UInt256.toNat h
    simp only [Bytes.readWord_toNat] at hn
    obtain ⟨hca, hdb⟩ := pair_parts _ _ _ _ hb48 hb16
      (by rw [← h32, ← h0]; exact hn)
    have hba : Precompile.bytesToNatPadded input 16 16 =
        Precompile.bytesToNatPadded input 0 16 := hdb.symm.trans heq48
    apply Word.word_ext
    simp only [Bytes.readWord_toNat]
    rw [h16, h0, hba, hca]

/-- The final Boolean-MUL/XOR keeps its zero-test after the offset change.
The false-accumulator case needs no input or nonzero-reference assumption. -/
theorem terminal_zero_iff (input : ByteArray) (a : UInt256)
    (ha : TerminalMulRaw.BooleanWord a)
    (hseed : a = 1 → MachineState.readWord input 48 = MachineState.readWord input 0) :
    UInt256.xor (UInt256.mul (MachineState.readWord input 16) a)
        (MachineState.readWord input 0) = 0 ↔
      UInt256.xor (UInt256.mul (MachineState.readWord input 32) a)
        (MachineState.readWord input 0) = 0 := by
  rcases ha with h0 | h1
  · subst a
    rw [TerminalMulRaw.mul_zero, TerminalMulRaw.mul_zero]
  · subst a
    rw [TerminalMulRaw.mul_one, TerminalMulRaw.mul_one,
      KnownInputLogic.wordXor_eq_zero_iff, KnownInputLogic.wordXor_eq_zero_iff]
    exact overlapping_windows input (hseed rfl)

/-- A conjunction scan cannot repair a failed initial equality. -/
private theorem foldAcc_seed (input : ByteArray) (r a : UInt256) (xs : List Nat)
    (ha : TerminalMulRaw.BooleanWord a) :
    UnrolledRepeatRaw.foldAcc input r a xs = 1 → a = 1 := by
  induction xs generalizing a with
  | nil => simp [UnrolledRepeatRaw.foldAcc]
  | cons o rest ih =>
    intro h
    have hb := TerminalMulRaw.eq_boolean (MachineState.readWord input o) r
    have hs := ih (UnrolledRepeatRaw.step input r a o)
      (TerminalMulRaw.step_boolean input r a o ha) h
    unfold UnrolledRepeatRaw.step at hs
    rcases ha with h0 | h1
    · rw [h0, TerminalMulRaw.land_zero] at hs
      exact False.elim ((by decide : (0 : UInt256) ≠ 1) hs)
    · exact h1

/-- Unconditional in calldata: the complete changed recognizer accepts
exactly the same inputs as the protected-validated old recognizer. -/
theorem scanner_zero_iff (input : ByteArray) :
    PcSeedRaw.mismatch input = 0 ↔
      UInt256.xor (UInt256.mul (MachineState.readWord input 32)
        (UnrolledRepeatRaw.foldAcc input (MachineState.readWord input 0)
          (PcSeedRaw.seed input) PcSeedRaw.offsets.dropLast))
        (MachineState.readWord input 0) = 0 := by
  unfold PcSeedRaw.mismatch
  apply terminal_zero_iff
  · exact TerminalMulRaw.foldAcc_boolean _ _ _ _ (TerminalMulRaw.eq_boolean _ _)
  · intro h
    have hs := foldAcc_seed input (MachineState.readWord input 0)
      (PcSeedRaw.seed input) PcSeedRaw.offsets.dropLast
      (TerminalMulRaw.eq_boolean _ _) h
    unfold PcSeedRaw.seed UInt256.eq at hs
    split at hs
    · rename_i heq
      exact (Word.word_ext heq).symm
    · exact False.elim ((by decide : (0 : UInt256) ≠ 1) hs)

open StackRoundTrace

def digest : UInt256 := UInt256.ofNat 972889429405991776604892044862621566948497025487

def hoistTemplate : List Instr :=
  [.op .JUMPDEST, .push ⟨20, by decide⟩ digest,
   .push ⟨0, by decide⟩ 0, .op .MSTORE]

def stored (s : State) : State :=
  { s with
    memory := MachineState.writeBytes s.memory (Data.Bytes.natToBytesPadded digest.toNat 32) 0
    activeWords := UInt256.ofNat 1 }

/-- The hoisted write preserves the arbitrary scanner frame and allocates
exactly one memory word, establishing the new MSIZE constant. -/
theorem run_hoist (s : State) (rho : List UInt256)
    (hs : rho.length ≤ 980) (hrun : s.halt = .Running)
    (ha : s.activeWords = UInt256.ofNat 0) :
    runInstrSeq hoistTemplate {s with pc := UInt256.ofNat 9427, stack := rho} =
      some {stored s with pc := UInt256.ofNat 9451, stack := rho} := by
  have hcap (n : Nat) (hn : n ≤ 4) : rho.length + n < 1024 := by omega
  simp (discharger := omega) [hoistTemplate, stored, runInstrSeq,
    DataStepper.runInstr, MachineState.mstore, State.activeWordsAfterUInt256,
    MachineState.activeWordsAfter, ha, hrun, hcap,
    show rho.length < 1024 by omega,
    show rho.length + 1 < 1024 by omega,
    show rho.length + 1 + 1 < 1024 by omega, UInt256.succ, Instr.size,
    Word.word_toNat_ofNat, Word.literal_eq_ofNat,
    show ({val := 0} : UInt256).toNat = 0 by rfl]
  repeat first | apply And.intro | rfl

def terminalTemplate : List Instr :=
  [.op .MSIZE, .op .CALLDATALOAD, .op .MUL, .op .XOR]

/-- Exact semantics of the new four-instruction terminal. -/
theorem run_terminal (s : State) (a r : UInt256) (rho : List UInt256)
    (hs : rho.length ≤ 980) (hrun : s.halt = .Running)
    (ha : s.activeWords = UInt256.ofNat 1) :
    runInstrSeq terminalTemplate
      {s with pc := UInt256.ofNat 9648, stack := [a,r] ++ rho} =
      some {s with pc := UInt256.ofNat 9652, stack := [UInt256.xor (UInt256.mul
          (MachineState.readWord s.executionEnv.calldata 32) a) r] ++ rho} := by
  have hcap (n : Nat) (hn : n ≤ 4) : rho.length + n < 1024 := by omega
  simp (discharger := omega) [terminalTemplate, runInstrSeq,
    DataStepper.runInstr, MachineState.msize, ha, hrun, hcap,
    show rho.length + 1 + 1 < 1024 by omega,
    show rho.length + 1 + 1 + 1 < 1024 by omega,
    UInt256.succ, Instr.size, Word.word_toNat_ofNat,
    DirectGuard.xor_comm']
  repeat first | apply And.intro | rfl

def scannerTemplate : List Instr :=
  (hoistTemplate ++ UnrolledRepeatRaw.scanTemplate PcSeedRaw.offsets.dropLast) ++ terminalTemplate

def newMismatch (input : ByteArray) (a r : UInt256) : UInt256 :=
  UInt256.xor (UInt256.mul (MachineState.readWord input 32)
    (UnrolledRepeatRaw.foldAcc input r a PcSeedRaw.offsets.dropLast)) r

/-- The complete relocated straight-line scanner, including the speculative
write and changed terminal, is proved against the pinned data stepper. -/
theorem run_scanner (s : State) (a r : UInt256) (rho : List UInt256)
    (hs : rho.length ≤ 978) (hrun : s.halt = .Running)
    (ha : s.activeWords = UInt256.ofNat 0) :
    runInstrSeq scannerTemplate
      {s with pc := UInt256.ofNat 9427, stack := [a,r] ++ rho} =
      some {stored s with pc := UInt256.ofNat 9652, stack := [newMismatch s.executionEnv.calldata a r] ++ rho} := by
  have hlen : ([a,r] ++ rho).length ≤ 980 := by
    simp only [List.length_append, List.length_cons, List.length_nil]
    omega
  have hh := run_hoist s ([a,r] ++ rho) hlen hrun ha
  have hc := UnrolledRepeatRaw.run_scan (stored s) (UInt256.ofNat 9451) a r
    PcSeedRaw.offsets.dropLast (by decide) rho (by omega) (by simpa [stored] using hrun)
  have hpc : pcAfter (UInt256.ofNat 9451)
      (UnrolledRepeatRaw.scanTemplate PcSeedRaw.offsets.dropLast) = UInt256.ofNat 9648 := by decide
  rw [hpc] at hc
  have ht := run_terminal (stored s)
    (UnrolledRepeatRaw.foldAcc s.executionEnv.calldata r a PcSeedRaw.offsets.dropLast)
    r rho (by omega) (by simpa [stored] using hrun) (by rfl)
  have h1 := DenseScheduleTrace.runInstrSeq_append_running hh
    (by simpa [stored] using hrun) hc
  have h2 := DenseScheduleTrace.runInstrSeq_append_running h1
    (by simpa [stored] using hrun) ht
  simpa only [scannerTemplate, newMismatch, stored] using h2

def terminalBranch : List Instr :=
  [.push ⟨2, by decide⟩ (UInt256.ofNat 9659), .op .JUMPI]

/-- The relocated failure edge consumes its condition and targets the cleanup
trampoline, leaving only the untouched outer stack frame. -/
theorem run_terminalBranch (s : State) (c : UInt256) (rho : List UInt256)
    (hs : rho.length ≤ 980) (hrun : s.halt = .Running)
    (hv : Decode.isValidJumpDest s.executionEnv.code 9659 = true) :
    runInstrSeq terminalBranch
      {s with pc := UInt256.ofNat 9652, stack := c :: rho} =
      some {s with pc := if c.toNat ≠ 0 then UInt256.ofNat 9659 else UInt256.ofNat 9656, stack := rho} := by
  by_cases hz : c.toNat = 0
  all_goals
    simp (discharger := omega) [terminalBranch, runInstrSeq, DataStepper.runInstr,
      hrun, hv, hz, UInt256.isTrue, UInt256.succ, Instr.size,
      show rho.length < 1024 by omega,
      show rho.length + 1 < 1024 by omega,
      show rho.length + 1 + 1 < 1024 by omega,
      show rho.length + 1 + 1 + 1 < 1024 by omega, Word.word_toNat_ofNat]
    repeat first | apply And.intro | rfl

/-- On failure reconstruct the old generic frame before reusing the old
speculative-write cleanup at the relocated PC 4803. This is the extra failure-path gas cost. -/
def missTemplate : List Instr :=
  [.op .JUMPDEST, .push ⟨0, by decide⟩ 0,
   .push ⟨2, by decide⟩ (UInt256.ofNat 4803), .op .JUMP]

theorem run_miss (s : State) (rho : List UInt256)
    (hs : rho.length ≤ 980) (hrun : s.halt = .Running)
    (hv : Decode.isValidJumpDest s.executionEnv.code 4803 = true) :
    runInstrSeq missTemplate {s with pc := UInt256.ofNat 9659, stack := rho} =
      some {s with pc := UInt256.ofNat 4803, stack := 0 :: rho} := by
  simp (discharger := omega) [missTemplate, runInstrSeq, DataStepper.runInstr,
    hrun, hv, UInt256.succ, Instr.size,
    show rho.length < 1024 by omega,
    show rho.length + 1 < 1024 by omega,
    show rho.length + 1 + 1 < 1024 by omega,
    show rho.length + 1 + 1 + 1 < 1024 by omega, Word.word_toNat_ofNat]
  repeat first | apply And.intro | rfl

def successTemplate : List Instr := [.op .MSIZE, .push ⟨0, by decide⟩ 0, .op .RETURN]

theorem run_success (s : State) (rho : List UInt256)
    (hs : rho.length ≤ 980) (hrun : s.halt = .Running)
    (ha : s.activeWords = UInt256.ofNat 1) :
    runInstrSeq successTemplate {s with pc := UInt256.ofNat 9656, stack := rho} =
      some {s with pc := UInt256.ofNat 9658, stack := rho, halt := .Returned, hReturn := MachineState.readPadded s.memory 0 32} := by
  simp (discharger := omega) [successTemplate, runInstrSeq, DataStepper.runInstr,
    MachineState.msize, State.activeWordsAfterUInt256, MachineState.activeWordsAfter,
    ha, hrun, UInt256.succ, Instr.size, Word.word_toNat_ofNat,
    show rho.length < 1024 by omega,
    show rho.length + 1 < 1024 by omega,
    show rho.length + 1 + 1 < 1024 by omega]
  repeat first | apply And.intro | rfl


/-- Kernel-checked assembly of the whole proposed replacement region, excluding
only its two unreachable STOP padding bytes. This is not a whole-image binding. -/
def patchRegionBytes : List UInt8 := [91,115,170,105,222,238,154,137,34,233,47,129,5,224,7,247,97,16,243,129,233,207,95,82,97,3,200,53,130,20,22,97,3,176,53,130,20,22,97,3,144,53,130,20,22,97,3,112,53,130,20,22,97,3,80,53,130,20,22,97,3,48,53,130,20,22,97,3,16,53,130,20,22,97,2,240,53,130,20,22,97,2,208,53,130,20,22,97,2,176,53,130,20,22,97,2,144,53,130,20,22,97,2,112,53,130,20,22,97,2,80,53,130,20,22,97,2,48,53,130,20,22,97,2,16,53,130,20,22,97,1,240,53,130,20,22,97,1,208,53,130,20,22,97,1,176,53,130,20,22,97,1,144,53,130,20,22,97,1,112,53,130,20,22,97,1,80,53,130,20,22,97,1,48,53,130,20,22,97,1,16,53,130,20,22,96,240,53,130,20,22,96,208,53,130,20,22,96,176,53,130,20,22,96,144,53,130,20,22,96,112,53,130,20,22,96,80,53,130,20,22,89,53,2,24,97,37,187,87,89,95,243,91,95,97,18,195,86]

def patchRegionTemplate : List Instr :=
  ((scannerTemplate ++ terminalBranch) ++ successTemplate) ++ missTemplate

theorem patch_region_assembly : assembleBytes patchRegionTemplate = patchRegionBytes := by
  decide

theorem patch_region_length : patchRegionBytes.length = 238 := by decide

theorem run_cleanup_relocated (s : State) (rho : List UInt256)
    (hs : rho.length ≤ 980) (hrun : s.halt = .Running)
    (ha : s.activeWords = UInt256.ofNat 1)
    (hv : Decode.isValidJumpDest s.executionEnv.code 245 = true) :
    runInstrSeq RetainedResultEdge112.cleanupTemplate
      {s with pc := UInt256.ofNat 4803, stack := rho} =
      some (RetainedResultEdge112.cleared s rho) := by
  have hcap (n : Nat) (hn : n ≤ 3) : rho.length + n < 1024 := by omega
  simp (discharger := omega) [RetainedResultEdge112.cleanupTemplate,
    RetainedResultEdge112.cleared, runInstrSeq, DataStepper.runInstr,
    MachineState.mstore, State.activeWordsAfterUInt256, MachineState.activeWordsAfter,
    ha, hrun, hv, show rho.length < 1024 by omega, hcap, UInt256.succ,
    Instr.size, Nat.add_assoc, Word.word_toNat_ofNat, Word.literal_eq_ofNat,
    show ({val := 0} : UInt256).toNat = 0 by rfl]

/-- The new failure trampoline joins the unchanged cleanup exactly, preserving
its old generic stack frame and clearing the hoisted digest before fallback. -/
theorem run_miss_cleanup (s : State) (rho : List UInt256)
    (hs : rho.length ≤ 978) (hrun : s.halt = .Running)
    (ha : s.activeWords = UInt256.ofNat 1)
    (hvCleanup : Decode.isValidJumpDest s.executionEnv.code 4803 = true)
    (hvGeneric : Decode.isValidJumpDest s.executionEnv.code 245 = true) :
    runInstrSeq (missTemplate ++ RetainedResultEdge112.cleanupTemplate)
      {s with pc := UInt256.ofNat 9659, stack := rho} =
      some (RetainedResultEdge112.cleared s (0 :: rho)) := by
  have hlen : (0 :: rho).length ≤ 980 := by
    simp only [List.length_cons]
    omega
  have hm := run_miss s rho (by omega) hrun hvCleanup
  have hc := run_cleanup_relocated s (0 :: rho)
    hlen hrun ha hvGeneric
  exact DenseScheduleTrace.runInstrSeq_append_running hm hrun hc

/-- Raw execution of the whole success path, with arbitrary persistent fields
and stack tail. Whole-image located/gas lifting and correctness composition remain separate. -/
theorem run_scanner_success (s : State) (rho : List UInt256)
    (hs : rho.length ≤ 976) (hrun : s.halt = .Running)
    (ha : s.activeWords = UInt256.ofNat 0)
    (hv : Decode.isValidJumpDest s.executionEnv.code 9659 = true)
    (hz : PcSeedRaw.mismatch s.executionEnv.calldata = 0) :
    runInstrSeq ((scannerTemplate ++ terminalBranch) ++ successTemplate)
      {s with pc := UInt256.ofNat 9427, stack := [PcSeedRaw.seed s.executionEnv.calldata,
        MachineState.readWord s.executionEnv.calldata 0] ++ rho} =
      some {stored s with pc := UInt256.ofNat 9658, stack := rho, halt := .Returned, hReturn := MachineState.readPadded (stored s).memory 0 32} := by
  let r := MachineState.readWord s.executionEnv.calldata 0
  let a := PcSeedRaw.seed s.executionEnv.calldata
  let c := newMismatch s.executionEnv.calldata a r
  have hzero : c = 0 := (scanner_zero_iff s.executionEnv.calldata).mp hz
  have hc := run_scanner s a r rho (by omega) hrun ha
  have hb := run_terminalBranch (stored s) c rho (by omega)
    (by simpa [stored] using hrun) (by simpa [stored] using hv)
  have hct : c.toNat = 0 := by rw [hzero]; decide
  simp only [hct, ne_eq, not_true_eq_false, if_false] at hb
  have hr := run_success (stored s) rho (by omega)
    (by simpa [stored] using hrun) (by rfl)
  have h1 := DenseScheduleTrace.runInstrSeq_append_running hc
    (by simpa [stored] using hrun) hb
  exact DenseScheduleTrace.runInstrSeq_append_running h1 (by simpa [stored] using hrun) hr

/-- The complete miss path reaches the old cleanup with the original frame,
then erases the speculative word before the generic hash path. -/
theorem run_scanner_miss (s : State) (rho : List UInt256)
    (hs : rho.length ≤ 976) (hrun : s.halt = .Running)
    (ha : s.activeWords = UInt256.ofNat 0)
    (hv : Decode.isValidJumpDest s.executionEnv.code 9659 = true)
    (hvCleanup : Decode.isValidJumpDest s.executionEnv.code 4803 = true)
    (hvGeneric : Decode.isValidJumpDest s.executionEnv.code 245 = true)
    (hz : PcSeedRaw.mismatch s.executionEnv.calldata ≠ 0) :
    runInstrSeq ((scannerTemplate ++ terminalBranch) ++
      (missTemplate ++ RetainedResultEdge112.cleanupTemplate))
      {s with pc := UInt256.ofNat 9427, stack := [PcSeedRaw.seed s.executionEnv.calldata,
        MachineState.readWord s.executionEnv.calldata 0] ++ rho} =
      some (RetainedResultEdge112.cleared (stored s) (0 :: rho)) := by
  let r := MachineState.readWord s.executionEnv.calldata 0
  let a := PcSeedRaw.seed s.executionEnv.calldata
  let c := newMismatch s.executionEnv.calldata a r
  have hnonzero : c ≠ 0 := by
    intro h
    exact hz ((scanner_zero_iff s.executionEnv.calldata).mpr h)
  have hc := run_scanner s a r rho (by omega) hrun ha
  have hb := run_terminalBranch (stored s) c rho (by omega)
    (by simpa [stored] using hrun) (by simpa [stored] using hv)
  have hct : c.toNat ≠ 0 := by
    intro h
    apply hnonzero
    exact Word.word_ext h
  simp only [if_pos hct] at hb
  have hr := run_miss_cleanup (stored s) rho (by omega)
    (by simpa [stored] using hrun) (by rfl)
    (by simpa [stored] using hvCleanup) (by simpa [stored] using hvGeneric)
  have h1 := DenseScheduleTrace.runInstrSeq_append_running hc
    (by simpa [stored] using hrun) hb
  exact DenseScheduleTrace.runInstrSeq_append_running h1 (by simpa [stored] using hrun) hr

/-- Hoisting writes exactly the padded target digest, independently of the
previous memory contents. -/
theorem stored_return_bytes (s : State) :
    MachineState.readPadded (stored s).memory 0 32 =
      Data.Bytes.natToBytesPadded digest.toNat 32 := by
  have hsize : (Data.Bytes.natToBytesPadded digest.toNat 32).size = 32 :=
    BytesLemmas.natToBytesPadded_size _ _
  change MachineState.readPadded
    (MachineState.writeBytes s.memory (Data.Bytes.natToBytesPadded digest.toNat 32) 0)
    0 32 = _
  simpa only [hsize] using
    (Memory.readPadded_writeBytes_same s.memory (Data.Bytes.natToBytesPadded digest.toNat 32) 0)

def seedTemplate : List Instr :=
  [.op .PC, .op .CALLDATALOAD, .op (.Dup ⟨1, by decide⟩), .op .EQ,
   .push ⟨2, by decide⟩ 9427, .op .JUMP]

/-- The second byte edit only retargets the existing PC=48 seed jump. -/
theorem run_seed (s : State) (rho : List UInt256)
    (hs : rho.length ≤ 980) (hrun : s.halt = .Running)
    (hv : Decode.isValidJumpDest s.executionEnv.code 9427 = true) :
    runInstrSeq seedTemplate
      {s with pc := UInt256.ofNat 48, stack := MachineState.readWord s.executionEnv.calldata 0 :: rho} =
      some {s with pc := UInt256.ofNat 9427, stack := [PcSeedRaw.seed s.executionEnv.calldata, MachineState.readWord s.executionEnv.calldata 0] ++ rho} := by
  have hcap (n : Nat) (hn : n ≤ 20) : rho.length + n < 1024 := by omega
  simp (discharger := omega) [seedTemplate, runInstrSeq, DataStepper.runInstr,
    hrun, hcap, PcSeedRaw.seed, UInt256.succ, Instr.size, Word.word_toNat_ofNat,
    DirectGuard.equality_comm, hv, List.getElem?_cons_zero, List.getElem?_cons_succ,
    Word.literal_eq_ofNat,
    show rho.length + 1 < 1024 by omega,
    show rho.length + 1 + 1 < 1024 by omega,
    show rho.length + 1 + 1 + 1 < 1024 by omega]

/-- The changed scanner's success condition, with the unchanged size/low64
entry preconditions, implies that its hoisted word is the RIPEMD160 spec. -/
theorem accepted_spec (input : ByteArray) (hsize : input.size = 1000)
    (hcond : Low64RepeatMath.condition input = 0)
    (hm : newMismatch input (PcSeedRaw.seed input) (MachineState.readWord input 0) = 0) :
    Challenge.Ripemd160.spec input = Data.Bytes.natToBytesPadded digest.toNat 32 := by
  have hold := (scanner_zero_iff input).mpr hm
  have hi := PcSeedMath.mismatch_zero_target input hsize hcond hold
  rw [hi]
  have hc := ExactGuardSpec.spec_targetInput_eq
  change Challenge.Ripemd160.spec KnownInputData.targetInput = ExactGuardSpec.paddedDigest at hc
  rw [hc]
  exact ExactGuardSpec.wordBytes_eq_paddedDigest.symm

/-- The generic calldata copy fully absorbs the speculative digest and its
one-word memory watermark. This reuses the predecessor's cleared-copy proof. -/
theorem run_scanner_miss_copy (s : State) (rho : List UInt256)
    (hs : rho.length ≤ 976) (hrun : s.halt = .Running)
    (ha : s.activeWords = UInt256.ofNat 0) (hm : s.memory.size = 0)
    (hv : Decode.isValidJumpDest s.executionEnv.code 9659 = true)
    (hvCleanup : Decode.isValidJumpDest s.executionEnv.code 4803 = true)
    (hvGeneric : Decode.isValidJumpDest s.executionEnv.code 245 = true)
    (hz : PcSeedRaw.mismatch s.executionEnv.calldata ≠ 0)
    (hfit : s.executionEnv.calldata.size < 2 ^ 256)
    (hpos : 0 < s.executionEnv.calldata.size) :
    runInstrSeq (((scannerTemplate ++ terminalBranch) ++
      (missTemplate ++ RetainedResultEdge112.cleanupTemplate)) ++ RetainedFallback114.copyTemplate)
      {s with pc := UInt256.ofNat 9427, stack := [PcSeedRaw.seed s.executionEnv.calldata,
        MachineState.readWord s.executionEnv.calldata 0] ++ rho} =
      some (RetainedFallback114.copied s (0 :: rho)) := by
  have hs32 : (stored s).memory.size = 32 := by
    simp [stored, MachineState.writeBytes_size, BytesLemmas.natToBytesPadded_size, hm]
  have hm0 := run_scanner_miss s rho hs hrun ha hv hvCleanup hvGeneric hz
  have hc := RetainedFallback114.run_copy (stored s) (0 :: rho)
    (by simp only [List.length_cons]; omega)
    (by simpa [stored] using hrun) hfit hpos hs32
  have he := DenseScheduleTrace.runInstrSeq_append_running hm0
    (by simpa [stored, RetainedResultEdge112.cleared] using hrun) hc
  simpa only [RetainedFallback114.copied, stored, State.activeWordsAfterUInt256] using he

/-- Byte binding for the retargeted seed (the only edit outside the scanner
region). The existing PC=48 load remains intentional and unchanged. -/
theorem seed_assembly : PcEncoding.assembleBytes seedTemplate =
    [0x58, 0x35, 0x81, 0x14, 0x61, 0x24, 0xd3, 0x56] := by decide

/-- Complete raw success behavior from the old seed entry, with returned bytes
proved equal to the protected RIPEMD160 specification for arbitrary calldata
satisfying the unchanged outer guards. -/
theorem run_seed_success_spec (s : State) (rho : List UInt256)
    (hs : rho.length ≤ 976) (hrun : s.halt = .Running)
    (ha : s.activeWords = UInt256.ofNat 0)
    (hvSeed : Decode.isValidJumpDest s.executionEnv.code 9427 = true)
    (hvMiss : Decode.isValidJumpDest s.executionEnv.code 9659 = true)
    (hsize : s.executionEnv.calldata.size = 1000)
    (hcond : Low64RepeatMath.condition s.executionEnv.calldata = 0)
    (hz : PcSeedRaw.mismatch s.executionEnv.calldata = 0) :
    runInstrSeq (seedTemplate ++ ((scannerTemplate ++ terminalBranch) ++ successTemplate))
      {s with pc := UInt256.ofNat 48, stack := MachineState.readWord s.executionEnv.calldata 0 :: rho} =
      some {stored s with pc := UInt256.ofNat 9658, stack := rho, halt := .Returned, hReturn := Challenge.Ripemd160.spec s.executionEnv.calldata} := by
  have hseed := run_seed s rho (by omega) hrun hvSeed
  have hscan := run_scanner_success s rho hs hrun ha hvMiss hz
  have h := DenseScheduleTrace.runInstrSeq_append_running hseed hrun hscan
  have hspec := accepted_spec s.executionEnv.calldata hsize hcond
    ((scanner_zero_iff s.executionEnv.calldata).mp hz)
  rw [stored_return_bytes, ← hspec] at h
  exact h


#print axioms seed_assembly
#print axioms run_seed_success_spec
#print axioms run_scanner_miss_copy
#print axioms run_seed
#print axioms accepted_spec
#print axioms stored_return_bytes
#print axioms run_scanner_miss
#print axioms run_scanner_success
#print axioms run_miss_cleanup
#print axioms patch_region_assembly
#print axioms run_terminalBranch
#print axioms run_miss
#print axioms run_success
#print axioms overlapping_windows
#print axioms terminal_zero_iff
#print axioms scanner_zero_iff
#print axioms run_hoist
#print axioms run_terminal
#print axioms run_scanner
end Challenge.Ripemd160.Submission.Proofs.Bytecode.HoistedStoreResearch
