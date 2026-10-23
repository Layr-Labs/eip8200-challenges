import Challenge.Ripemd160.Submission.Proofs.Bytecode.HoistedInherited.CounterFreeScanBodyRaw

set_option warningAsError true
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false

/-! Focused raw proof only. No artifact, gas, branch, or universal certificate. -/
namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.HoistedInherited.TerminalMulRaw
open EvmSemantics EvmSemantics.EVM YulEvmCompiler Challenge.EvmProof
open Challenge.Ripemd160.Submission.Proofs.Bytecode
open StackRoundTrace
open Challenge.Ripemd160.Submission.Proofs.Bytecode.DenseScheduleTrace (pcAfter_append runInstrSeq_append_running)

/-- The accumulator is an EVM Boolean, not an arbitrary word. -/
def BooleanWord (a : UInt256) : Prop := a = 0 ∨ a = 1

theorem eq_boolean (w r : UInt256) : BooleanWord (UInt256.eq w r) := by
  unfold UInt256.eq
  split
  · exact Or.inr rfl
  · exact Or.inl rfl

theorem land_boolean (a b : UInt256) (ha : BooleanWord a) (hb : BooleanWord b) :
    BooleanWord (UInt256.land a b) := by
  rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;> unfold BooleanWord <;> decide

theorem mul_zero (w : UInt256) : UInt256.mul w 0 = 0 := by
  apply Word.word_ext
  change (w.val * (0 : Fin UInt256.size)).val = 0
  simp

theorem mul_one (w : UInt256) : UInt256.mul w 1 = w := by
  apply Word.word_ext
  change (w.val * (1 : Fin UInt256.size)).val = w.val.val
  simp

theorem land_zero (w : UInt256) : UInt256.land w 0 = 0 := by
  apply Word.word_ext
  simp [Word.word_toNat_land, Word.word_toNat_ofNat, Word.literal_eq_ofNat]

theorem land_one_boolean (w : UInt256) (hw : BooleanWord w) :
    UInt256.land w 1 = w := by
  rcases hw with rfl | rfl <;> decide

/-- Nonzero reference is essential in the false-accumulator case. -/
theorem terminal_algebra (w r a : UInt256) (hr : r ≠ 0) (ha : BooleanWord a) :
    UInt256.eq (UInt256.mul w a) r = UInt256.land (UInt256.eq w r) a := by
  rcases ha with rfl | rfl
  · rw [mul_zero, land_zero]
    simp only [UInt256.eq, DirectGuard.nat_eq_iff]
    rw [if_neg (Ne.symm hr)]
    rfl
  · rw [mul_one, land_one_boolean _ (eq_boolean w r)]

/-- Any comparison preserves Booleanity, for any input/reference and offset. -/
theorem step_boolean (input : ByteArray) (r a : UInt256) (offset : Nat)
    (ha : BooleanWord a) : BooleanWord (HoistedInherited.UnrolledRepeatRaw.step input r a offset) :=
  land_boolean _ _ (eq_boolean _ _) ha

/-- The invariant needed at the last comparison; no input assumptions. -/
theorem foldAcc_boolean (input : ByteArray) (r a : UInt256) (xs : List Nat)
    (ha : BooleanWord a) : BooleanWord (HoistedInherited.UnrolledRepeatRaw.foldAcc input r a xs) := by
  induction xs generalizing a with
  | nil => exact ha
  | cons offset rest ih =>
      exact ih _ (step_boolean input r a offset ha)

theorem equalityAcc0_boolean (input : ByteArray) :
    BooleanWord (DirectGuard.equalityAcc input 0) := eq_boolean _ _

theorem foldAcc_equalityAcc0_boolean (input : ByteArray) (r : UInt256) (xs : List Nat) :
    BooleanWord (HoistedInherited.UnrolledRepeatRaw.foldAcc input r (DirectGuard.equalityAcc input 0) xs) :=
  foldAcc_boolean input r _ xs (equalityAcc0_boolean input)

/-- PUSH1 96; CALLDATALOAD; MUL; EQ. Consumes the reference word. -/
def terminalTemplate : List Instr :=
  [.push ⟨1, by decide⟩ (UInt256.ofNat 96), .op .CALLDATALOAD, .op .MUL, .op .EQ]

theorem run_terminal_product (s : State) (pc a r : UInt256) (rho : List UInt256)
    (hs : rho.length ≤ 990) (hrun : s.halt = .Running) :
    runInstrSeq terminalTemplate {s with pc := pc, stack := [a,r] ++ rho} =
      some {s with
        pc := pcAfter pc terminalTemplate,
        stack := [UInt256.eq (UInt256.mul (MachineState.readWord s.executionEnv.calldata 96) a) r] ++ rho} := by
  have hcap (n : Nat) (hn : n ≤ 20) : rho.length + n < 1024 := by omega
  simp (discharger := omega) [terminalTemplate, runInstrSeq, DataStepper.runInstr,
    pcAfter, hrun, hcap, UInt256.succ, Instr.size, Nat.add_assoc,
    Word.word_toNat_ofNat, Word.literal_eq_ofNat, DirectGuard.equality_comm]
  repeat first | apply And.intro | rfl

theorem run_terminal (s : State) (pc a r : UInt256) (rho : List UInt256)
    (hs : rho.length ≤ 990) (hrun : s.halt = .Running)
    (hr : r ≠ 0) (ha : BooleanWord a) :
    runInstrSeq terminalTemplate {s with pc := pc, stack := [a,r] ++ rho} =
      some {s with
        pc := pcAfter pc terminalTemplate,
        stack := [HoistedInherited.UnrolledRepeatRaw.step s.executionEnv.calldata r a 96] ++ rho} := by
  simpa only [terminal_algebra _ _ _ hr ha, HoistedInherited.UnrolledRepeatRaw.step] using
    run_terminal_product s pc a r rho hs hrun

/-- Keep all earlier comparisons, replacing only the final one. -/
def scanPrefix : List Instr :=
  HoistedInherited.CounterFreeScanBodyRaw.entry ++ HoistedInherited.UnrolledRepeatRaw.scanTemplate HoistedInherited.UnrolledRepeatRaw.offsets.dropLast

def template : List Instr := scanPrefix ++ terminalTemplate

theorem offsets_split : HoistedInherited.UnrolledRepeatRaw.offsets = HoistedInherited.UnrolledRepeatRaw.offsets.dropLast ++ [96] := by rfl

theorem prefix_bound : ∀ offset ∈ HoistedInherited.UnrolledRepeatRaw.offsets.dropLast, offset < 65536 := by decide

theorem run_prefix (s : State) (pc a r : UInt256) (rho : List UInt256)
    (hs : rho.length ≤ 990) (hrun : s.halt = .Running) :
    runInstrSeq scanPrefix {s with pc := pc, stack := [a,r] ++ rho} =
      some {s with
        pc := pcAfter pc scanPrefix,
        stack := [HoistedInherited.UnrolledRepeatRaw.foldAcc s.executionEnv.calldata r a
          HoistedInherited.UnrolledRepeatRaw.offsets.dropLast,r] ++ rho} := by
  have he := HoistedInherited.CounterFreeScanBodyRaw.run_entry s pc a r rho hs hrun
  have hc := HoistedInherited.UnrolledRepeatRaw.run_scan s (pcAfter pc HoistedInherited.CounterFreeScanBodyRaw.entry) a r
    HoistedInherited.UnrolledRepeatRaw.offsets.dropLast prefix_bound rho hs hrun
  simpa only [scanPrefix, pcAfter_append] using runInstrSeq_append_running he hrun hc

/-- General scanner, arbitrary nonzero reference and Boolean seed, no retained r. -/
theorem run_template (s : State) (pc a r : UInt256) (rho : List UInt256)
    (hs : rho.length ≤ 990) (hrun : s.halt = .Running)
    (hr : r ≠ 0) (ha : BooleanWord a) :
    runInstrSeq template {s with pc := pc, stack := [a,r] ++ rho} =
      some {s with
        pc := pcAfter pc template,
        stack := [HoistedInherited.UnrolledRepeatRaw.acc s.executionEnv.calldata r a 10] ++ rho} := by
  have hp := run_prefix s pc a r rho hs hrun
  have ht := run_terminal s (pcAfter pc scanPrefix)
    (HoistedInherited.UnrolledRepeatRaw.foldAcc s.executionEnv.calldata r a HoistedInherited.UnrolledRepeatRaw.offsets.dropLast)
    r rho hs hrun hr (foldAcc_boolean _ _ _ _ ha)
  have h := runInstrSeq_append_running hp hrun ht
  have hacc : HoistedInherited.UnrolledRepeatRaw.step s.executionEnv.calldata r
      (HoistedInherited.UnrolledRepeatRaw.foldAcc s.executionEnv.calldata r a HoistedInherited.UnrolledRepeatRaw.offsets.dropLast) 96 =
      HoistedInherited.UnrolledRepeatRaw.acc s.executionEnv.calldata r a 10 := by
    rw [← HoistedInherited.UnrolledRepeatRaw.foldAcc_offsets, offsets_split, HoistedInherited.UnrolledRepeatRaw.foldAcc_append]
    rfl
  simpa only [template, pcAfter_append, hacc] using h

theorem prefix_endPC : pcAfter (UInt256.ofNat 9429) scanPrefix = UInt256.ofNat 9627 := by decide

theorem terminal_endPC : pcAfter (UInt256.ofNat 9627) terminalTemplate = UInt256.ofNat 9632 := by decide

theorem endPC : pcAfter (UInt256.ofNat 9429) template = UInt256.ofNat 9632 := by decide

/-- The concrete last comparison: exactly the requested AND-shaped result,
with the reference consumed and all of rho preserved. -/
theorem run_terminal_9627 (s : State) (a r : UInt256) (rho : List UInt256)
    (hs : rho.length ≤ 990) (hrun : s.halt = .Running)
    (hr : r ≠ 0) (ha : BooleanWord a) :
    runInstrSeq terminalTemplate {s with pc := UInt256.ofNat 9627, stack := [a,r] ++ rho} =
      some {s with
        pc := UInt256.ofNat 9632
        stack := [UInt256.land
          (UInt256.eq (MachineState.readWord s.executionEnv.calldata 96) r) a] ++ rho} := by
  simpa only [terminal_endPC, HoistedInherited.UnrolledRepeatRaw.step] using
    run_terminal s (UInt256.ofNat 9627) a r rho hs hrun hr ha

theorem run (s : State) (a r : UInt256) (rho : List UInt256)
    (hs : rho.length ≤ 990) (hrun : s.halt = .Running)
    (hr : r ≠ 0) (ha : BooleanWord a) :
    runInstrSeq template {s with pc := UInt256.ofNat 9429, stack := [a,r] ++ rho} =
      some {s with
        pc := UInt256.ofNat 9632,
        stack := [HoistedInherited.UnrolledRepeatRaw.acc s.executionEnv.calldata r a 10] ++ rho} := by
  simpa only [endPC] using run_template s (UInt256.ofNat 9429) a r rho hs hrun hr ha

theorem fullWord_nonzero : KnownInputData.fullWord ≠ 0 := by decide

/-- Anchor specialization: equalityAcc 0 to equalityAcc 10, consuming r. -/
theorem run_equalityAcc (s : State) (rho : List UInt256)
    (hs : rho.length ≤ 990) (hrun : s.halt = .Running)
    (hanchor : HoistedInherited.KnownInputCompactState.referenceWord s.executionEnv.calldata = KnownInputData.fullWord) :
    runInstrSeq template {s with
      pc := UInt256.ofNat 9429
      stack := [DirectGuard.equalityAcc s.executionEnv.calldata 0,
        HoistedInherited.KnownInputCompactState.referenceWord s.executionEnv.calldata] ++ rho} =
      some {s with
        pc := UInt256.ofNat 9632,
        stack := [DirectGuard.equalityAcc s.executionEnv.calldata 10] ++ rho} := by
  have hr : HoistedInherited.KnownInputCompactState.referenceWord s.executionEnv.calldata ≠ 0 := by
    rw [hanchor]
    exact fullWord_nonzero
  simpa only [HoistedInherited.UnrolledRepeatRaw.acc_equalityAcc] using
    run s (DirectGuard.equalityAcc s.executionEnv.calldata 0)
      (HoistedInherited.KnownInputCompactState.referenceWord s.executionEnv.calldata) rho hs hrun hr
      (equalityAcc0_boolean _)

/-- Empty-suffix specialization: the final stack is literally one word.
The known nonzero word appears on entry only, never on exit. -/
theorem run_equalityAcc_singleton (s : State) (hrun : s.halt = .Running)
    (hanchor : HoistedInherited.KnownInputCompactState.referenceWord s.executionEnv.calldata = KnownInputData.fullWord) :
    runInstrSeq template
      {s with
        pc := UInt256.ofNat 9429
        stack := [DirectGuard.equalityAcc s.executionEnv.calldata 0, KnownInputData.fullWord]} =
      some {s with
        pc := UInt256.ofNat 9632
        stack := [DirectGuard.equalityAcc s.executionEnv.calldata 10]} := by
  simpa only [List.append_nil, hanchor] using
    run_equalityAcc s [] (by decide) hrun hanchor

#check terminal_algebra
#check foldAcc_boolean
#check foldAcc_equalityAcc0_boolean
#check run_terminal_product
#check run_terminal
#check run_terminal_9627
#check run_template
#check run
#check run_equalityAcc
#check run_equalityAcc_singleton
#print axioms terminal_algebra
#print axioms foldAcc_boolean
#print axioms foldAcc_equalityAcc0_boolean
#print axioms run_terminal_product
#print axioms run_terminal
#print axioms run_terminal_9627
#print axioms run_template
#print axioms run
#print axioms run_equalityAcc
#print axioms run_equalityAcc_singleton
end Challenge.Ripemd160.Submission.Proofs.Bytecode.HoistedInherited.TerminalMulRaw
