import Challenge.Ripemd160.Submission.Local20261028.RecOriginalAnchor
import Challenge.Ripemd160.Submission.Proofs.Bytecode.RetainedTerminalMul.RetainedAdapters

set_option warningAsError true
set_option linter.unusedSimpArgs false
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.Local20261028.Control.HoistedStoreAnchorRaw
open EvmSemantics EvmSemantics.EVM YulEvmCompiler Challenge.EvmProof
open Challenge.Ripemd160.Submission.Proofs.Bytecode
open StackRoundTrace StackRoundTemplate DirectLiteralModel DirectLiteralRawV4
open RetainedIntegration105 (anchorWord anchorWord_eq anchorWord_isTrue anchorWord_false)

def anchorPrefix : List Instr :=
  [.push ⟨0, by decide⟩ 0, .op .CALLDATALOAD, .push ⟨14, by decide⟩ 0x6161616161616161,
   .op .XOR, .push ⟨1, by decide⟩ 192,
   .op .SHL, .push ⟨2, by decide⟩ 5838]

theorem run_anchor_prefix (s : State) (pc : UInt256) (rho : List UInt256)
    (hs : rho.length ≤ 980) (hrun : s.halt = .Running) :
    runInstrSeq anchorPrefix {s with pc := pc, stack := rho} =
      some {s with pc := pcAfter pc anchorPrefix, stack := [UInt256.ofNat 5838, anchorWord s.executionEnv.calldata] ++ rho} := by
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
    (hv : Decode.isValidJumpDest s.executionEnv.code 5838 = true) :
    runInstrSeq anchorTemplate {s with pc := UInt256.ofNat 21, stack := rho} =
      some {s with pc := UInt256.ofNat 5838, stack := rho} := by
  have hp := run_anchor_prefix s (UInt256.ofNat 21) rho hs hrun
  have ht := anchorWord_isTrue s.executionEnv.calldata (by rwa [anchorWord_eq])
  have hj : runInstrSeq [.op .JUMPI]
      {s with pc := pcAfter (UInt256.ofNat 21) anchorPrefix, stack := [UInt256.ofNat 5838, anchorWord s.executionEnv.calldata] ++ rho} =
      some {s with pc := UInt256.ofNat 5838, stack := rho} := by
    simp [runInstrSeq, DataStepper.runInstr, hrun,
      show rho.length + 2 < 1024 by omega, ht, hv, Word.word_toNat_ofNat]
  exact DenseScheduleTrace.runInstrSeq_append_running hp hrun hj

theorem run_anchor_low_fall (s : State) (rho : List UInt256)
    (hs : rho.length ≤ 980) (hrun : s.halt = .Running)
    (heq : Low64RepeatMath.condition s.executionEnv.calldata = 0) :
    runInstrSeq anchorTemplate {s with pc := UInt256.ofNat 21, stack := rho} =
      some {s with pc := UInt256.ofNat 46, stack := rho} := by
  have hp := run_anchor_prefix s (UInt256.ofNat 21) rho hs hrun
  have ht : ¬ UInt256.isTrue (anchorWord s.executionEnv.calldata) := by
    rw [anchorWord_eq, heq]
    decide
  have hj : runInstrSeq [.op .JUMPI]
      {s with pc := pcAfter (UInt256.ofNat 21) anchorPrefix, stack := [UInt256.ofNat 5838, anchorWord s.executionEnv.calldata] ++ rho} =
      some {s with pc := UInt256.ofNat 46, stack := rho} := by
    simp [runInstrSeq, DataStepper.runInstr, hrun,
      show rho.length + 2 < 1024 by omega, ht, pcAfter, anchorPrefix, Instr.size,
      UInt256.succ, Word.word_toNat_ofNat]
    rfl
  exact DenseScheduleTrace.runInstrSeq_append_running hp hrun hj

def reloadTemplate : List Instr := [.push ⟨0, by decide⟩ 0, .op .CALLDATALOAD]

theorem run_reload (s : State) (rho : List UInt256)
    (hs : rho.length ≤ 980) (hrun : s.halt = .Running) :
    runInstrSeq reloadTemplate {s with pc := UInt256.ofNat 46, stack := rho} =
      some {s with pc := UInt256.ofNat 48, stack := MachineState.readWord s.executionEnv.calldata 0 :: rho} := by
  have hcap (n : Nat) (hn : n ≤ 20) : rho.length + n < 1024 := by omega
  simp (discharger := omega) [reloadTemplate, runInstrSeq, DataStepper.runInstr,
    pcAfter, hrun, show rho.length < 1024 by omega, hcap, UInt256.succ,
    Instr.size, Nat.add_assoc, Word.literal_eq_ofNat, Word.word_toNat_ofNat,
    List.getElem?_cons_zero]
  repeat first | apply And.intro | rfl

end Challenge.Ripemd160.Submission.Proofs.Bytecode.Local20261028.Control.HoistedStoreAnchorRaw
