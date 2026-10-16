import Challenge.Ripemd160.Submission.Proofs.Bytecode.UnrolledRepeatRaw

set_option warningAsError true
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false

/-! Raw model for leaving the dead counter off the success edge entirely.
The exit branch and exact-bytecode binding are separate obligations.
-/
namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.CounterFreeScanBodyRaw
open EvmSemantics EvmSemantics.EVM YulEvmCompiler Challenge.EvmProof
open Challenge.Ripemd160.Submission.Proofs.Bytecode
open StackRoundTrace
open Challenge.Ripemd160.Submission.Proofs.Bytecode.DenseScheduleTrace (pcAfter_append runInstrSeq_append_running)

def entry : List Instr := [.op .JUMPDEST]
def template : List Instr :=
  entry ++ UnrolledRepeatRaw.scanTemplate UnrolledRepeatRaw.offsets

theorem run_entry (s : State) (pc a r : UInt256) (rho : List UInt256)
    (hs : rho.length ≤ 990) (hrun : s.halt = .Running) :
    runInstrSeq entry {s with pc := pc, stack := [a,r] ++ rho} =
      some {s with pc := pcAfter pc entry, stack := [a,r] ++ rho} := by
  have hcap : rho.length + 1 + 1 < 1024 := by omega
  simp (discharger := omega) [entry, runInstrSeq, DataStepper.runInstr,
    pcAfter, hrun, UInt256.succ, Instr.size, hcap]
  repeat first | apply And.intro | rfl

theorem run_template (s : State) (pc a r : UInt256) (rho : List UInt256)
    (hs : rho.length ≤ 990) (hrun : s.halt = .Running) :
    runInstrSeq template {s with pc := pc, stack := [a,r] ++ rho} =
      some {s with
        pc := pcAfter pc template
        stack := [UnrolledRepeatRaw.acc s.executionEnv.calldata r a 10,r] ++ rho} := by
  have he := run_entry s pc a r rho hs hrun
  have hc := UnrolledRepeatRaw.run_scan s (pcAfter pc entry) a r
    UnrolledRepeatRaw.offsets UnrolledRepeatRaw.offsets_bound rho hs hrun
  have hb := runInstrSeq_append_running he hrun hc
  rw [UnrolledRepeatRaw.foldAcc_offsets] at hb
  simpa only [template, pcAfter_append] using hb

theorem endPC : pcAfter (UInt256.ofNat 9429) template = UInt256.ofNat 9633 := by decide

theorem run (s : State) (a r : UInt256) (rho : List UInt256)
    (hs : rho.length ≤ 990) (hrun : s.halt = .Running) :
    runInstrSeq template {s with pc := UInt256.ofNat 9429, stack := [a,r] ++ rho} =
      some {s with
        pc := UInt256.ofNat 9633
        stack := [UnrolledRepeatRaw.acc s.executionEnv.calldata r a 10,r] ++ rho} := by
  simpa only [endPC] using run_template s (UInt256.ofNat 9429) a r rho hs hrun

theorem run_equalityAcc (s : State) (rho : List UInt256)
    (hs : rho.length ≤ 990) (hrun : s.halt = .Running) :
    runInstrSeq template
      {s with
        pc := UInt256.ofNat 9429
        stack := [DirectGuard.equalityAcc s.executionEnv.calldata 0,
          KnownInputCompactState.referenceWord s.executionEnv.calldata] ++ rho} =
      some {s with
        pc := UInt256.ofNat 9633
        stack := [DirectGuard.equalityAcc s.executionEnv.calldata 10,
          KnownInputCompactState.referenceWord s.executionEnv.calldata] ++ rho} := by
  simpa only [UnrolledRepeatRaw.acc_equalityAcc] using
    run s (DirectGuard.equalityAcc s.executionEnv.calldata 0)
      (KnownInputCompactState.referenceWord s.executionEnv.calldata) rho hs hrun

#print axioms run
#print axioms run_equalityAcc
end Challenge.Ripemd160.Submission.Proofs.Bytecode.CounterFreeScanBodyRaw
