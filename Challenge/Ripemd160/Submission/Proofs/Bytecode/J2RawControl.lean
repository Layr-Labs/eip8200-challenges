import Challenge.Ripemd160.Submission.Proofs.Bytecode.J2RawBase
set_option warningAsError true
set_option maxRecDepth 100000
set_option maxHeartbeats 3000000
set_option linter.unusedSimpArgs false
namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.J2Raw
open EvmSemantics EvmSemantics.EVM YulEvmCompiler Challenge.EvmProof
open StackRoundTrace RecognitionRecurrence

def finishRest (f : Frame) (rho : List UInt256) : List UInt256 :=
  [f.off, f.word, f.full, f.stop, c32,
    PatternedSwar.m7, PatternedSwar.m8, PatternedSwar.M] ++ rho

theorem run_first (s : State) (pc : UInt256) (f : Frame) (rho : List UInt256)
    (hstack : rho.length ≤ 990) (hrun : s.halt = .Running)
    (hvalid : Decode.isValidJumpDest s.executionEnv.code 220 = true) :
    runInstrSeq firstTemplate {s with pc := pc, stack := frame f rho} =
      some {s with pc := if f.full.toNat = 0 then UInt256.ofNat 220 else pcAfter pc firstTemplate,
                   stack := frame f rho} := by
  have hbase : rho.length < 1024 := by omega
  have hcap (n : Nat) (hn : n ≤ 30) : rho.length + n < 1024 := by omega
  by_cases hc : f.full.toNat = 0
  all_goals simp (discharger := omega) [firstTemplate, frame, runInstrSeq, DataStepper.runInstr,
    pcAfter, UInt256.succ, Instr.size, List.exchange, List.getElem?_cons_zero,
    Nat.add_assoc, hrun, hbase, hcap, UInt256.lt, UInt256.eq, UInt256.isZero, UInt256.isTrue,
    hc, eq_comm, hvalid, Word.word_toNat_ofNat, Word.literal_eq_ofNat]
  all_goals rfl

theorem run_normalGuard (s : State) (pc : UInt256) (f : Frame) (rho : List UInt256)
    (hstack : rho.length ≤ 990) (hrun : s.halt = .Running)
    (hvalid : Decode.isValidJumpDest s.executionEnv.code 193 = true) :
    runInstrSeq normalGuardTemplate {s with pc := pc, stack := frame f rho} =
      some {s with pc := if f.off.toNat < f.full.toNat then UInt256.ofNat 193 else pcAfter pc normalGuardTemplate,
                   stack := frame f rho} := by
  have hbase : rho.length < 1024 := by omega
  have hcap (n : Nat) (hn : n ≤ 30) : rho.length + n < 1024 := by omega
  by_cases hc : f.off.toNat < f.full.toNat
  all_goals simp (discharger := omega) [normalGuardTemplate, frame, runInstrSeq, DataStepper.runInstr,
    pcAfter, UInt256.succ, Instr.size, List.exchange, List.getElem?_cons_zero,
    Nat.add_assoc, hrun, hbase, hcap, UInt256.lt, UInt256.eq, UInt256.isZero, UInt256.isTrue,
    hc, eq_comm, hvalid, Word.word_toNat_ofNat, Word.literal_eq_ofNat]
  all_goals rfl

theorem run_finish (s : State) (pc : UInt256) (f : Frame) (rho : List UInt256)
    (hstack : rho.length ≤ 990) (hrun : s.halt = .Running)
    (hlen : f.len = UInt256.ofNat s.executionEnv.calldata.size)
    (hvalid : Decode.isValidJumpDest s.executionEnv.code 4699 = true) :
    runInstrSeq finishTemplate {s with pc := pc, stack := frame f rho} =
      some {s with pc := if f.stop.toNat = f.len.toNat then UInt256.ofNat 4699 else pcAfter pc finishTemplate,
                   stack := frame f rho} := by
  have hbase : rho.length < 1024 := by omega
  have hcap (n : Nat) (hn : n ≤ 30) : rho.length + n < 1024 := by omega
  by_cases hc : f.stop.toNat = f.len.toNat
  all_goals simp (discharger := omega) [finishTemplate, frame, runInstrSeq, DataStepper.runInstr,
    pcAfter, UInt256.succ, Instr.size, List.exchange, List.getElem?_cons_zero,
    Nat.add_assoc, hrun, hbase, hcap, ← hlen, UInt256.lt, UInt256.eq, UInt256.isZero, UInt256.isTrue,
    hc, eq_comm, hvalid, Word.word_toNat_ofNat, Word.literal_eq_ofNat]
  all_goals rfl

theorem run_transitionGuard (s : State) (pc : UInt256) (f : Frame) (rho : List UInt256)
    (hstack : rho.length ≤ 990) (hrun : s.halt = .Running)
    (hvalid : Decode.isValidJumpDest s.executionEnv.code 193 = true) :
    runInstrSeq transitionGuardTemplate {s with pc := pc, stack := frame f rho} =
      some {s with pc := if f.off.toNat < f.full.toNat then UInt256.ofNat 193 else pcAfter pc transitionGuardTemplate,
                   stack := frame f rho} := by
  have hbase : rho.length < 1024 := by omega
  have hcap (n : Nat) (hn : n ≤ 30) : rho.length + n < 1024 := by omega
  by_cases hc : f.off.toNat < f.full.toNat
  all_goals simp (discharger := omega) [transitionGuardTemplate, frame, runInstrSeq, DataStepper.runInstr,
    pcAfter, UInt256.succ, Instr.size, List.exchange, List.getElem?_cons_zero,
    Nat.add_assoc, hrun, hbase, hcap, UInt256.lt, UInt256.eq, UInt256.isZero, UInt256.isTrue,
    hc, eq_comm, hvalid, Word.word_toNat_ofNat, Word.literal_eq_ofNat]
  all_goals rfl

theorem run_result (s : State) (pc : UInt256) (f : Frame) (rho : List UInt256)
    (hstack : rho.length ≤ 990) (hrun : s.halt = .Running)
    (hvalid : Decode.isValidJumpDest s.executionEnv.code 310 = true) :
    runInstrSeq resultTemplate {s with pc := pc, stack := frame f rho} =
      some {s with pc := if f.acc.toNat = 0 then pcAfter pc resultTemplate else UInt256.ofNat 310,
                   stack := finishRest f rho} := by
  have hbase : rho.length < 1024 := by omega
  have hcap (n : Nat) (hn : n ≤ 30) : rho.length + n < 1024 := by omega
  by_cases hc : f.acc.toNat = 0
  all_goals simp (discharger := omega) [resultTemplate, frame, finishRest, runInstrSeq, DataStepper.runInstr,
    pcAfter, UInt256.succ, Instr.size, List.exchange, List.getElem?_cons_zero,
    Nat.add_assoc, hrun, hbase, hcap, UInt256.isTrue, hc, hvalid,
    Word.word_toNat_ofNat, Word.literal_eq_ofNat]
  all_goals rfl

theorem run_toTail (s : State) (pc : UInt256) (stack : List UInt256)
    (hstack : stack.length ≤ 1022) (hrun : s.halt = .Running)
    (hvalid : Decode.isValidJumpDest s.executionEnv.code 220 = true) :
    runInstrSeq toTailTemplate {s with pc := pc, stack := stack} =
      some {s with pc := UInt256.ofNat 220, stack := stack} := by
  have hb : stack.length < 1024 := by omega
  have hc : stack.length + 1 < 1024 := by omega
  simp (discharger := omega) [hb, hc, Nat.add_comm, toTailTemplate, runInstrSeq, DataStepper.runInstr, pcAfter,
    UInt256.succ, Instr.size, hrun, hvalid, Word.word_toNat_ofNat, Word.literal_eq_ofNat]

#print axioms run_first
#print axioms run_normalGuard
#print axioms run_finish
#print axioms run_transitionGuard
#print axioms run_result
#print axioms run_toTail
end Challenge.Ripemd160.Submission.Proofs.Bytecode.J2Raw
