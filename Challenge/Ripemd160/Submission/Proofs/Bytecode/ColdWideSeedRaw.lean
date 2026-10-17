import Challenge.Ripemd160.Submission.Proofs.Bytecode.CounterFreeSeedRaw
set_option warningAsError true
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.ColdWideSeedRaw
open EvmSemantics EvmSemantics.EVM YulEvmCompiler Challenge.EvmProof
open Challenge.Ripemd160.Submission.Proofs.Bytecode
open StackRoundTrace StackRoundTemplate
open Challenge.Ripemd160.Submission.Proofs.Bytecode.DenseScheduleTrace (runInstrSeq_append_running)

def loadTemplate : List Instr := [.push ⟨0, by decide⟩ 0, .op .CALLDATALOAD]
def compareTemplate : List Instr :=
  [.push ⟨3, by decide⟩ (UInt256.ofNat 968), .op .CALLDATALOAD,
   .op (.Dup ⟨1, by decide⟩), .op .EQ]
def template : List Instr :=
  (loadTemplate ++ compareTemplate) ++ CounterFreeSeedRaw.jumpTemplate

theorem load (s : State) (pc : UInt256) (rho : List UInt256)
    (hs : rho.length ≤ 990) (hrun : s.halt = .Running) :
    runInstrSeq loadTemplate {s with pc := pc, stack := rho} =
      some {s with
        pc := pcAfter pc loadTemplate,
        stack := MachineState.readWord s.executionEnv.calldata 0 :: rho} := by
  have hcap0 : rho.length < 1024 := by omega
  have hcap (n : Nat) (hn : n ≤ 20) : rho.length + n < 1024 := by omega
  simp (discharger := omega) [loadTemplate, runInstrSeq, DataStepper.runInstr,
    pcAfter, hrun, hcap0, hcap, UInt256.succ, Instr.size, Nat.add_assoc,
    Word.literal_eq_ofNat, Word.word_toNat_ofNat]
  repeat first | apply And.intro | rfl

theorem compare (s : State) (pc r : UInt256) (rho : List UInt256)
    (hs : rho.length ≤ 990) (hrun : s.halt = .Running) :
    runInstrSeq compareTemplate {s with pc := pc, stack := r :: rho} =
      some {s with
        pc := pcAfter pc compareTemplate,
        stack := UInt256.eq r (MachineState.readWord s.executionEnv.calldata 968) :: r :: rho} := by
  have hcap0 : rho.length < 1024 := by omega
  have hcap (n : Nat) (hn : n ≤ 20) : rho.length + n < 1024 := by omega
  simp (discharger := omega) [compareTemplate, runInstrSeq, DataStepper.runInstr,
    pcAfter, hrun, hcap0, hcap, UInt256.succ, Instr.size, Nat.add_assoc,
    Word.literal_eq_ofNat, Word.word_toNat_ofNat,
    List.getElem?_cons_zero, DirectGuard.equality_comm]
  repeat first | apply And.intro | rfl

theorem run (s : State) (pc : UInt256) (rho : List UInt256)
    (hs : rho.length ≤ 980) (hrun : s.halt = .Running)
    (hdest : Decode.isValidJumpDest s.executionEnv.code 9429 = true) :
    runInstrSeq template {s with pc := pc, stack := rho} =
      some {s with
        pc := UInt256.ofNat 9429,
        stack := [DirectGuard.equalityAcc s.executionEnv.calldata 0,
          KnownInputCompactState.referenceWord s.executionEnv.calldata] ++ rho} := by
  have hl := load s pc rho (by omega) hrun
  have hc := compare s (pcAfter pc loadTemplate)
    (MachineState.readWord s.executionEnv.calldata 0) rho (by omega) hrun
  have hb := runInstrSeq_append_running hl hrun hc
  have hj := CounterFreeSeedRaw.run_jump s
    (pcAfter (pcAfter pc loadTemplate) compareTemplate)
    ([DirectGuard.equalityAcc s.executionEnv.calldata 0,
      KnownInputCompactState.referenceWord s.executionEnv.calldata] ++ rho)
    (by simp only [List.length_append, List.length_cons, List.length_nil]; omega) hrun hdest
  have hh := runInstrSeq_append_running hb hrun hj
  simpa only [template, DirectGuard.equalityAcc,
    KnownInputCompactState.referenceWord] using hh

#print axioms run
end Challenge.Ripemd160.Submission.Proofs.Bytecode.ColdWideSeedRaw
