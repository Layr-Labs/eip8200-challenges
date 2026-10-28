import Challenge.Ripemd160.Submission.Proofs.Bytecode.RetainedTerminalMul.RetainedAdapters

set_option warningAsError true
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.unusedSimpArgs false

/-! The 1000-byte low-64 anchor of the candidate: the same screen as
`RetainedIntegration105.anchorPrefix`, jumping to the window-checked 1000-byte
arm at PC9394. -/
namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.HoistedStoreAnchorRaw
open EvmSemantics EvmSemantics.EVM YulEvmCompiler Challenge.EvmProof
open Challenge.Ripemd160.Submission.Proofs.Bytecode
open StackRoundTrace StackRoundTemplate DirectLiteralModel DirectLiteralRawV4
open RetainedIntegration105 (anchorWord anchorWord_eq anchorWord_isTrue anchorWord_false)

def anchorPrefix : List Instr :=
  [.push ⟨0, by decide⟩ 0, .op .CALLDATALOAD, .op (.Dup ⟨0, by decide⟩),
   .push ⟨15, by decide⟩ 0x6161616161616161, .op .XOR, .push ⟨1, by decide⟩ 192,
   .op .SHL, .push ⟨2, by decide⟩ 9394]

theorem run_anchor_prefix (s : State) (pc : UInt256) (rho : List UInt256)
    (hs : rho.length ≤ 980) (hrun : s.halt = .Running) :
    runInstrSeq anchorPrefix {s with pc := pc, stack := rho} =
      some {s with pc := pcAfter pc anchorPrefix, stack := [UInt256.ofNat 9394, anchorWord s.executionEnv.calldata, MachineState.readWord s.executionEnv.calldata 0] ++ rho} := by
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
    (hv : Decode.isValidJumpDest s.executionEnv.code 9394 = true) :
    runInstrSeq anchorTemplate {s with pc := UInt256.ofNat 21, stack := rho} =
      some {s with pc := UInt256.ofNat 9394, stack := MachineState.readWord s.executionEnv.calldata 0 :: rho} := by
  have hp := run_anchor_prefix s (UInt256.ofNat 21) rho hs hrun
  have ht := anchorWord_isTrue s.executionEnv.calldata (by rwa [anchorWord_eq])
  have hj : runInstrSeq [.op .JUMPI]
      {s with pc := pcAfter (UInt256.ofNat 21) anchorPrefix, stack := [UInt256.ofNat 9394, anchorWord s.executionEnv.calldata, MachineState.readWord s.executionEnv.calldata 0] ++ rho} =
      some {s with pc := UInt256.ofNat 9394, stack := MachineState.readWord s.executionEnv.calldata 0 :: rho} := by
    simp [runInstrSeq, DataStepper.runInstr, hrun,
      show rho.length + 3 < 1024 by omega, ht, hv, Word.word_toNat_ofNat]
  exact DenseScheduleTrace.runInstrSeq_append_running hp hrun hj

theorem run_anchor_fall (s : State) (rho : List UInt256)
    (hs : rho.length ≤ 980) (hrun : s.halt = .Running)
    (heq : KnownInputCompactState.referenceWord s.executionEnv.calldata = KnownInputData.fullWord) :
    runInstrSeq anchorTemplate {s with pc := UInt256.ofNat 21, stack := rho} =
      some {s with pc := UInt256.ofNat 48, stack := MachineState.readWord s.executionEnv.calldata 0 :: rho} := by
  have hp := run_anchor_prefix s (UInt256.ofNat 21) rho hs hrun
  have ht := anchorWord_false s.executionEnv.calldata heq
  have hj : runInstrSeq [.op .JUMPI]
      {s with pc := pcAfter (UInt256.ofNat 21) anchorPrefix, stack := [UInt256.ofNat 9394, anchorWord s.executionEnv.calldata, MachineState.readWord s.executionEnv.calldata 0] ++ rho} =
      some {s with pc := UInt256.ofNat 48, stack := MachineState.readWord s.executionEnv.calldata 0 :: rho} := by
    simp [runInstrSeq, DataStepper.runInstr, hrun,
      show rho.length + 3 < 1024 by omega, ht, pcAfter, anchorPrefix, Instr.size,
      UInt256.succ, Word.word_toNat_ofNat]
    rfl
  exact DenseScheduleTrace.runInstrSeq_append_running hp hrun hj

/-- PC41..50: no PUSH0/MLOAD/CALLDATALOAD warm-up; reuse retained r. -/
theorem run_anchor_low_fall (s : State) (rho : List UInt256)
    (hs : rho.length ≤ 980) (hrun : s.halt = .Running)
    (heq : Low64RepeatMath.condition s.executionEnv.calldata = 0) :
    runInstrSeq anchorTemplate {s with pc := UInt256.ofNat 21, stack := rho} =
      some {s with pc := UInt256.ofNat 48, stack := MachineState.readWord s.executionEnv.calldata 0 :: rho} := by
  have hp := run_anchor_prefix s (UInt256.ofNat 21) rho hs hrun
  have ht : ¬ UInt256.isTrue (anchorWord s.executionEnv.calldata) := by
    rw [anchorWord_eq, heq]
    decide
  have hj : runInstrSeq [.op .JUMPI]
      {s with pc := pcAfter (UInt256.ofNat 21) anchorPrefix, stack := [UInt256.ofNat 9394, anchorWord s.executionEnv.calldata, MachineState.readWord s.executionEnv.calldata 0] ++ rho} =
      some {s with pc := UInt256.ofNat 48, stack := MachineState.readWord s.executionEnv.calldata 0 :: rho} := by
    simp [runInstrSeq, DataStepper.runInstr, hrun,
      show rho.length + 3 < 1024 by omega, ht, pcAfter, anchorPrefix, Instr.size,
      UInt256.succ, Word.word_toNat_ofNat]
    rfl
  exact DenseScheduleTrace.runInstrSeq_append_running hp hrun hj

end Challenge.Ripemd160.Submission.Proofs.Bytecode.HoistedStoreAnchorRaw
