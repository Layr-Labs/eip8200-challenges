import Challenge.Ripemd160.Submission.Local20261028.RecTerminalMulRaw
set_option warningAsError true
set_option linter.unusedSimpArgs false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false
namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.Local20261028.Control.TerminalXorRaw
open EvmSemantics EvmSemantics.EVM YulEvmCompiler Challenge.EvmProof
open Challenge.Ripemd160.Submission.Proofs.Bytecode
open StackRoundTrace
open Challenge.Ripemd160.Submission.Proofs.Bytecode.DenseScheduleTrace (pcAfter_append runInstrSeq_append_running)

def mismatch (input : ByteArray) : UInt256 :=
  UInt256.xor
    (UInt256.mul (MachineState.readWord input 96)
      (Control.UnrolledRepeatRaw.foldAcc input (Control.KnownInputCompactState.referenceWord input)
        (DirectGuard.equalityAcc input 0) Control.UnrolledRepeatRaw.offsets.dropLast))
    (Control.KnownInputCompactState.referenceWord input)

def terminalTemplate : List Instr :=
  [.push ⟨1, by decide⟩ (UInt256.ofNat 96), .op .CALLDATALOAD, .op .MUL, .op .XOR]
def template : List Instr := Control.TerminalMulRaw.scanPrefix ++ terminalTemplate

theorem run_terminal (s : State) (pc a r : UInt256) (rho : List UInt256)
    (hs : rho.length ≤ 990) (hrun : s.halt = .Running) :
    runInstrSeq terminalTemplate {s with pc := pc, stack := [a,r] ++ rho} =
      some {s with
        pc := pcAfter pc terminalTemplate,
        stack := [UInt256.xor (UInt256.mul (MachineState.readWord s.executionEnv.calldata 96) a) r] ++ rho} := by
  have hcap (n : Nat) (hn : n ≤ 20) : rho.length + n < 1024 := by omega
  simp (discharger := omega) [terminalTemplate, runInstrSeq, DataStepper.runInstr,
    pcAfter, hrun, hcap, UInt256.succ, Instr.size, Nat.add_assoc,
    Word.word_toNat_ofNat, Word.literal_eq_ofNat, DirectGuard.xor_comm']
  repeat first | apply And.intro | rfl

/-- Keep all earlier comparisons, replacing only the final one. -/
theorem run_equalityAcc (s : State) (rho : List UInt256)
    (hs : rho.length ≤ 990) (hrun : s.halt = .Running)
    (_hanchor : Control.KnownInputCompactState.referenceWord s.executionEnv.calldata = KnownInputData.fullWord) :
    runInstrSeq template {s with
      pc := UInt256.ofNat 9711
      stack := [DirectGuard.equalityAcc s.executionEnv.calldata 0,
        Control.KnownInputCompactState.referenceWord s.executionEnv.calldata] ++ rho} =
      some {s with
        pc := UInt256.ofNat 9914
        stack := [mismatch s.executionEnv.calldata] ++ rho} := by
  have hp := Control.TerminalMulRaw.run_prefix s (UInt256.ofNat 9711)
    (DirectGuard.equalityAcc s.executionEnv.calldata 0)
    (Control.KnownInputCompactState.referenceWord s.executionEnv.calldata) rho hs hrun
  have ht := run_terminal s (pcAfter (UInt256.ofNat 9711) Control.TerminalMulRaw.scanPrefix)
    (Control.UnrolledRepeatRaw.foldAcc s.executionEnv.calldata
      (Control.KnownInputCompactState.referenceWord s.executionEnv.calldata)
      (DirectGuard.equalityAcc s.executionEnv.calldata 0) Control.UnrolledRepeatRaw.offsets.dropLast)
    (Control.KnownInputCompactState.referenceWord s.executionEnv.calldata) rho hs hrun
  have hh := runInstrSeq_append_running hp hrun ht
  have hpc : pcAfter (pcAfter (UInt256.ofNat 9711) Control.TerminalMulRaw.scanPrefix) terminalTemplate = UInt256.ofNat 9914 := by decide
  simpa only [template, hpc, mismatch] using hh

/-- Keep all earlier comparisons, replacing only the final one. -/
theorem run_unconditional (s : State) (rho : List UInt256)
    (hs : rho.length ≤ 990) (hrun : s.halt = .Running) :
    runInstrSeq template {s with
      pc := UInt256.ofNat 9711
      stack := [DirectGuard.equalityAcc s.executionEnv.calldata 0,
        Control.KnownInputCompactState.referenceWord s.executionEnv.calldata] ++ rho} =
      some {s with
        pc := UInt256.ofNat 9914
        stack := [mismatch s.executionEnv.calldata] ++ rho} := by
  have hp := Control.TerminalMulRaw.run_prefix s (UInt256.ofNat 9711)
    (DirectGuard.equalityAcc s.executionEnv.calldata 0)
    (Control.KnownInputCompactState.referenceWord s.executionEnv.calldata) rho hs hrun
  have ht := run_terminal s (pcAfter (UInt256.ofNat 9711) Control.TerminalMulRaw.scanPrefix)
    (Control.UnrolledRepeatRaw.foldAcc s.executionEnv.calldata
      (Control.KnownInputCompactState.referenceWord s.executionEnv.calldata)
      (DirectGuard.equalityAcc s.executionEnv.calldata 0) Control.UnrolledRepeatRaw.offsets.dropLast)
    (Control.KnownInputCompactState.referenceWord s.executionEnv.calldata) rho hs hrun
  have hh := runInstrSeq_append_running hp hrun ht
  have hpc : pcAfter (pcAfter (UInt256.ofNat 9711) Control.TerminalMulRaw.scanPrefix) terminalTemplate = UInt256.ofNat 9914 := by decide
  simpa only [template, hpc, mismatch] using hh

theorem isZero_mismatch (input : ByteArray)
    (href : Control.KnownInputCompactState.referenceWord input = KnownInputData.fullWord) :
    UInt256.isZero (mismatch input) = DirectGuard.equalityAcc input 10 := by
  rw [mismatch, ← DirectGuard.equality_isZero_xor]
  rw [Control.TerminalMulRaw.terminal_algebra _ _ _
    (by rw [href]; exact Control.TerminalMulRaw.fullWord_nonzero)
    (Control.TerminalMulRaw.foldAcc_boolean _ _ _ _ (Control.TerminalMulRaw.equalityAcc0_boolean input))]
  change Control.UnrolledRepeatRaw.step input (Control.KnownInputCompactState.referenceWord input)
    (Control.UnrolledRepeatRaw.foldAcc input (Control.KnownInputCompactState.referenceWord input)
      (DirectGuard.equalityAcc input 0) Control.UnrolledRepeatRaw.offsets.dropLast) 96 = _
  have h := Control.UnrolledRepeatRaw.acc_equalityAcc input 10
  rw [← Control.UnrolledRepeatRaw.foldAcc_offsets, Control.TerminalMulRaw.offsets_split,
    Control.UnrolledRepeatRaw.foldAcc_append] at h
  exact h
end Challenge.Ripemd160.Submission.Proofs.Bytecode.Local20261028.Control.TerminalXorRaw
