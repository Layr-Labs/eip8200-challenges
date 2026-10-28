import Challenge.Ripemd160.Submission.Proofs.Bytecode.DenseScheduleTrace
import Challenge.Ripemd160.Submission.Local20261028.RecEqualityAccumulator

set_option warningAsError true
set_option linter.unusedSimpArgs false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false

/-!
# Pure trace of the unrolled repeated-word scanner

This module contains no artifact or gas assumptions.  The input is always the
calldata of the arbitrary underlying state; the reference word, accumulator,
discarded counter, and suffix stack are arbitrary.  Small instruction traces
are composed with `runInstrSeq_append_running`, rather than simplifying the
complete 155-instruction execution.
-/

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.Local20261028.Control.UnrolledRepeatRaw

open EvmSemantics EvmSemantics.EVM YulEvmCompiler Challenge.EvmProof
open StackRoundTrace
open DenseScheduleTrace (pcAfter_append runInstrSeq_append_running)

/-- Discard the old counter, retaining the accumulator and reference word. -/
def startTemplate : List Instr :=
  [.op .JUMPDEST, .op (.Swap ⟨0, by decide⟩), .op .POP]

/-- Minimal PUSH for a 16-bit offset, followed by one comparison and AND. -/
def cmpTemplate (offset : Nat) : List Instr :=
  [.push ⟨if offset = 0 then 0 else if offset < 256 then 1 else 2,
      by split <;> (try split) <;> decide⟩ (UInt256.ofNat offset),
   .op .CALLDATALOAD, .op (.Dup ⟨2, by decide⟩), .op .EQ, .op .AND]

/-- Restore the zero counter below the folded accumulator. -/
def endTemplate : List Instr :=
  [.push ⟨0, by decide⟩ 0, .op (.Swap ⟨0, by decide⟩)]

/-- The exact order of the thirty comparisons in the unrolled scanner. -/
def offsets : List Nat :=
  [928, 896, 960, 832, 800, 864, 736, 704, 768, 640, 608, 672,
   544, 512, 576, 448, 416, 480, 352, 320, 384, 256, 224, 288,
   160, 128, 192, 64, 32, 96]

def scanTemplate : List Nat → List Instr
  | [] => []
  | offset :: rest => cmpTemplate offset ++ scanTemplate rest

def template : List Instr :=
  (startTemplate ++ scanTemplate offsets) ++ endTemplate

/-- One comparison applied to an arbitrary (not necessarily Boolean) seed. -/
def step (input : ByteArray) (r a : UInt256) (offset : Nat) : UInt256 :=
  UInt256.land (UInt256.eq (MachineState.readWord input offset) r) a

/-- Left fold, in execution order, over an arbitrary list of offsets. -/
def foldAcc (input : ByteArray) (r a : UInt256) (xs : List Nat) : UInt256 :=
  xs.foldl (step input r) a

/-- Offset groups matching the recurrence in `DirectGuard.equalityAcc`. -/
def offsetGroups : Nat → List Nat
  | 0 => []
  | n + 1 => offsetGroups n ++ [928 - 96 * n, 896 - 96 * n, 960 - 96 * n]

/-- The group-wise accumulator, with arbitrary reference word and seed. -/
def acc (input : ByteArray) (r a : UInt256) : Nat → UInt256
  | 0 => a
  | n + 1 =>
      step input r
        (step input r (step input r (acc input r a n) (928 - 96 * n))
          (896 - 96 * n))
        (960 - 96 * n)

theorem offsets_eq_groups : offsets = offsetGroups 10 := by rfl

theorem offsets_bound : ∀ offset ∈ offsets, offset < 65536 := by decide

theorem foldAcc_append (input : ByteArray) (r a : UInt256) (xs ys : List Nat) :
    foldAcc input r a (xs ++ ys) =
      foldAcc input r (foldAcc input r a xs) ys := by
  exact List.foldl_append

theorem foldAcc_groups (input : ByteArray) (r a : UInt256) (n : Nat) :
    foldAcc input r a (offsetGroups n) = acc input r a n := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [offsetGroups, foldAcc_append, ih]
      rfl

theorem foldAcc_offsets (input : ByteArray) (r a : UInt256) :
    foldAcc input r a offsets = acc input r a 10 := by
  rw [offsets_eq_groups, foldAcc_groups]

/-- The general recurrence specializes exactly to the existing accumulator. -/
theorem acc_equalityAcc (input : ByteArray) (n : Nat) :
    acc input (Control.KnownInputCompactState.referenceWord input)
        (DirectGuard.equalityAcc input 0) n = DirectGuard.equalityAcc input n := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [acc, ih]
      rfl

theorem run_start (s : State) (pc a counter r : UInt256) (rho : List UInt256)
    (hs : rho.length ≤ 990) (hrun : s.halt = .Running) :
    runInstrSeq startTemplate {s with pc := pc, stack := [a, counter, r] ++ rho} =
      some {s with pc := pcAfter pc startTemplate, stack := [a, r] ++ rho} := by
  have hcap (n : Nat) (hn : n ≤ 20) : rho.length + n < 1024 := by omega
  simp (discharger := omega) [startTemplate, runInstrSeq, DataStepper.runInstr,
    pcAfter, hrun, hcap, UInt256.succ, Instr.size, Nat.add_assoc,
    Word.literal_eq_ofNat, List.getElem?_cons_zero, List.exchange]
  repeat first | apply And.intro | rfl

/-- Generic per-comparison correctness, including the minimal-PUSH width cases. -/
theorem run_cmp (s : State) (pc a r : UInt256) (offset : Nat)
    (hoffset : offset < 65536) (rho : List UInt256)
    (hs : rho.length ≤ 990) (hrun : s.halt = .Running) :
    runInstrSeq (cmpTemplate offset) {s with pc := pc, stack := [a, r] ++ rho} =
      some {s with
        pc := pcAfter pc (cmpTemplate offset)
        stack := [step s.executionEnv.calldata r a offset, r] ++ rho} := by
  have hcap (n : Nat) (hn : n ≤ 20) : rho.length + n < 1024 := by omega
  have hoff : (UInt256.ofNat offset).toNat = offset := by
    rw [Word.word_toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  by_cases hz : offset = 0
  · subst offset
    simp (discharger := omega) [cmpTemplate, step, runInstrSeq, DataStepper.runInstr,
      pcAfter, hrun, hcap, UInt256.succ, Instr.size, Nat.add_assoc,
      Word.word_toNat_ofNat, Word.literal_eq_ofNat, List.getElem?_cons_zero,
      DirectGuard.equality_comm]
    repeat first | apply And.intro | rfl
  by_cases hsmall : offset < 256
  all_goals
    simp (discharger := omega) [cmpTemplate, hz, hsmall, step, runInstrSeq,
      DataStepper.runInstr, pcAfter, hrun, hcap, UInt256.succ, Instr.size,
      Nat.add_assoc, hoff, Word.literal_eq_ofNat, List.getElem?_cons_zero,
      DirectGuard.equality_comm]
  all_goals repeat first | apply And.intro | rfl

theorem run_end (s : State) (pc a r : UInt256) (rho : List UInt256)
    (hs : rho.length ≤ 990) (hrun : s.halt = .Running) :
    runInstrSeq endTemplate {s with pc := pc, stack := [a, r] ++ rho} =
      some {s with pc := pcAfter pc endTemplate, stack := [a, 0, r] ++ rho} := by
  have hcap (n : Nat) (hn : n ≤ 20) : rho.length + n < 1024 := by omega
  simp (discharger := omega) [endTemplate, runInstrSeq, DataStepper.runInstr,
    pcAfter, hrun, hcap, UInt256.succ, Instr.size, Nat.add_assoc,
    Word.literal_eq_ofNat, List.getElem?_cons_zero, List.exchange]
  repeat first | apply And.intro | rfl

/-- Compositional correctness of any list of 16-bit-offset comparisons. -/
theorem run_scan (s : State) (pc a r : UInt256) (xs : List Nat)
    (hxs : ∀ offset ∈ xs, offset < 65536) (rho : List UInt256)
    (hs : rho.length ≤ 990) (hrun : s.halt = .Running) :
    runInstrSeq (scanTemplate xs) {s with pc := pc, stack := [a, r] ++ rho} =
      some {s with
        pc := pcAfter pc (scanTemplate xs)
        stack := [foldAcc s.executionEnv.calldata r a xs, r] ++ rho} := by
  induction xs generalizing pc a with
  | nil => rfl
  | cons offset rest ih =>
      have hc := run_cmp s pc a r offset (hxs offset (by simp)) rho hs hrun
      have ht := ih (pcAfter pc (cmpTemplate offset))
        (step s.executionEnv.calldata r a offset)
        (fun x hx => hxs x (by simp [hx]))
      have h := runInstrSeq_append_running hc hrun ht
      simpa only [scanTemplate, pcAfter_append, foldAcc, List.foldl_cons] using h

/-- Full raw correctness, still allowing an arbitrary starting program counter. -/
theorem run_template (s : State) (pc a counter r : UInt256) (rho : List UInt256)
    (hs : rho.length ≤ 990) (hrun : s.halt = .Running) :
    runInstrSeq template {s with pc := pc, stack := [a, counter, r] ++ rho} =
      some {s with
        pc := pcAfter pc template
        stack := [acc s.executionEnv.calldata r a 10, 0, r] ++ rho} := by
  have hstart := run_start s pc a counter r rho hs hrun
  have hscan := run_scan s (pcAfter pc startTemplate) a r offsets offsets_bound rho hs hrun
  have hbody := runInstrSeq_append_running hstart hrun hscan
  rw [foldAcc_offsets] at hbody
  have hend := run_end s (pcAfter (pcAfter pc startTemplate) (scanTemplate offsets))
    (acc s.executionEnv.calldata r a 10) r rho hs hrun
  have h := runInstrSeq_append_running hbody hrun hend
  simpa only [template, pcAfter_append] using h

theorem template_length : template.length = 155 := by decide

theorem template_endPC : pcAfter (UInt256.ofNat 9709) template = UInt256.ofNat 9917 := by
  decide

/-- The exact scanner window: pc9427 to pc9635, with arbitrary seed and reference. -/
theorem run (s : State) (a counter r : UInt256) (rho : List UInt256)
    (hs : rho.length ≤ 990) (hrun : s.halt = .Running) :
    runInstrSeq template
        {s with pc := UInt256.ofNat 9709, stack := [a, counter, r] ++ rho} =
      some {s with
        pc := UInt256.ofNat 9917
        stack := [acc s.executionEnv.calldata r a 10, 0, r] ++ rho} := by
  simpa only [template_endPC] using run_template s (UInt256.ofNat 9709) a counter r rho hs hrun

/-- Ready-to-use specialization to the existing repeated-input equality model. -/
theorem run_equalityAcc (s : State) (counter : UInt256) (rho : List UInt256)
    (hs : rho.length ≤ 990) (hrun : s.halt = .Running) :
    runInstrSeq template
        {s with
          pc := UInt256.ofNat 9709
          stack := [DirectGuard.equalityAcc s.executionEnv.calldata 0, counter,
            Control.KnownInputCompactState.referenceWord s.executionEnv.calldata] ++ rho} =
      some {s with
        pc := UInt256.ofNat 9917
        stack := [DirectGuard.equalityAcc s.executionEnv.calldata 10, 0,
          Control.KnownInputCompactState.referenceWord s.executionEnv.calldata] ++ rho} := by
  simpa only [acc_equalityAcc] using
    run s (DirectGuard.equalityAcc s.executionEnv.calldata 0) counter
      (Control.KnownInputCompactState.referenceWord s.executionEnv.calldata) rho hs hrun

end Challenge.Ripemd160.Submission.Proofs.Bytecode.Local20261028.Control.UnrolledRepeatRaw
