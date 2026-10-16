import Challenge.Ripemd160.Submission.Proofs.Bytecode.J2RawBase
import Challenge.Ripemd160.Submission.Proofs.Bytecode.RawExpressionAC
set_option warningAsError true
set_option maxRecDepth 100000
set_option maxHeartbeats 3000000
set_option linter.unusedSimpArgs false
namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.J2Raw
open EvmSemantics EvmSemantics.EVM YulEvmCompiler Challenge.EvmProof
open StackRoundTrace RecognitionRecurrence

def finishRest (f : Frame) (rho : List UInt256) : List UInt256 :=
  [f.off, f.word, f.full, m9f, c96,
    f.stop] ++ rho

theorem run_dispatch0 (s : State) (pc : UInt256) (f : Frame) (rho : List UInt256)
    (hstack : rho.length ≤ 990) (hrun : s.halt = .Running)
    (hvalid : Decode.isValidJumpDest s.executionEnv.code
      (dispatchTarget (UInt256.ofNat 0) f.full).toNat = true) :
    runInstrSeq dispatch0Template {s with pc := pc, stack := frame f rho} =
      some {s with pc := dispatchTarget (UInt256.ofNat 0) f.full, stack := frame f rho} := by
  have hbase : rho.length < 1024 := by omega
  have hcap (n : Nat) (hn : n ≤ 30) : rho.length + n < 1024 := by omega
  have hv : Decode.isValidJumpDest s.executionEnv.code
      (UInt256.ofNat 5090 + UInt256.ofNat 18 * UInt256.sar (⟨0⟩ - f.full) (UInt256.ofNat 5)).toNat = true := hvalid
  simp (discharger := omega) [dispatch0Template, frame, runInstrSeq, DataStepper.runInstr,
    pcAfter, UInt256.succ, Instr.size, List.exchange, List.getElem?_cons_zero,
    Nat.add_assoc, hrun, hbase, hcap, hv]
  rfl

theorem run_dispatch1 (s : State) (pc : UInt256) (x : UInt256) (f : Frame) (rho : List UInt256)
    (hstack : rho.length ≤ 990) (hrun : s.halt = .Running)
    (hvalid : Decode.isValidJumpDest s.executionEnv.code (blockPC 4) = true) :
    runInstrSeq dispatch1Template {s with pc := pc, stack := x :: frame f rho} =
      some {s with pc := if UInt256.land (UInt256.ofNat s.executionEnv.calldata.size) (UInt256.ofNat 16) = 0
        then pcAfter pc dispatch1Template else UInt256.ofNat (blockPC 4), stack := frame f rho} := by
  have hbase : rho.length < 1024 := by omega
  have hcap (n : Nat) (hn : n ≤ 30) : rho.length + n < 1024 := by omega
  have hz : ∀ x : UInt256, x.toNat = 0 ↔ x = 0 := by
    intro x; constructor
    · intro h; apply Word.word_ext; exact h
    · rintro rfl; rfl
  have hmod : blockPC 4 % 115792089237316195423570985008687907853269984665640564039457584007913129639936 = blockPC 4 := by decide
  by_cases hc : UInt256.land (UInt256.ofNat s.executionEnv.calldata.size) (UInt256.ofNat 16) = UInt256.ofNat 0
  all_goals simp (discharger := omega) [dispatch1Template, frame, runInstrSeq, DataStepper.runInstr,
    pcAfter, UInt256.succ, Instr.size, List.exchange, List.getElem?_cons_zero,
    Nat.add_assoc, hrun, hbase, hcap, hvalid, Word.literal_eq_ofNat, Word.word_toNat_ofNat, RawExpressionAC.land_comm, hz, UInt256.isTrue, hc, hmod]
  all_goals rfl


theorem sub_toNat_zero (a b : UInt256) : (UInt256.sub a b).toNat = 0 ↔ a.toNat = b.toNat := by
  unfold UInt256.sub UInt256.toNat
  constructor
  · intro h
    have h1 : a.val - b.val = 0 := Fin.ext h
    exact congrArg Fin.val (sub_eq_zero.mp h1)
  · intro h
    have h1 : a.val = b.val := Fin.ext h
    rw [h1, sub_self]; rfl

theorem hsub_toNat_zero (a b : UInt256) : (a - b).toNat = 0 ↔ a.toNat = b.toNat := sub_toNat_zero a b

theorem run_finish (s : State) (pc : UInt256) (f : Frame) (rho : List UInt256)
    (hstack : rho.length ≤ 990) (hrun : s.halt = .Running)
    (hlen : f.len = UInt256.ofNat s.executionEnv.calldata.size)
    (hvalid : Decode.isValidJumpDest s.executionEnv.code 4891 = true) :
    runInstrSeq finishTemplate {s with pc := pc, stack := pending s f rho} =
      some {s with pc := if f.stop.toNat = f.len.toNat then pcAfter pc finishTemplate else UInt256.ofNat 4891,
                   stack := pending s f rho} := by
  have hbase : rho.length < 1024 := by omega
  have hcap (n : Nat) (hn : n ≤ 30) : rho.length + n < 1024 := by omega
  by_cases hc : f.stop.toNat = f.len.toNat
  all_goals simp (discharger := omega) [finishTemplate, pending, frame, runInstrSeq, DataStepper.runInstr,
    pcAfter, UInt256.succ, Instr.size, List.exchange, List.getElem?_cons_zero,
    Nat.add_assoc, hrun, hbase, hcap, ← hlen, UInt256.isTrue, sub_toNat_zero, hsub_toNat_zero,
    hc, hvalid, Word.word_toNat_ofNat, Word.literal_eq_ofNat]
  all_goals rfl

theorem run_result (s : State) (pc : UInt256) (f : Frame) (rho : List UInt256)
    (hstack : rho.length ≤ 990) (hrun : s.halt = .Running)
    (hvalid : Decode.isValidJumpDest s.executionEnv.code 4565 = true) :
    runInstrSeq resultTemplate {s with pc := pc, stack := frame f rho} =
      some {s with pc := if f.acc.toNat = 0 then pcAfter pc resultTemplate else UInt256.ofNat 4565,
                   stack := finishRest f rho} := by
  have hbase : rho.length < 1024 := by omega
  have hcap (n : Nat) (hn : n ≤ 30) : rho.length + n < 1024 := by omega
  by_cases hc : f.acc.toNat = 0
  all_goals simp (discharger := omega) [resultTemplate, frame, finishRest, runInstrSeq, DataStepper.runInstr,
    pcAfter, UInt256.succ, Instr.size, List.exchange, List.getElem?_cons_zero,
    Nat.add_assoc, hrun, hbase, hcap, UInt256.isTrue, hc, hvalid,
    Word.word_toNat_ofNat, Word.literal_eq_ofNat]
  all_goals rfl

#print axioms run_dispatch0
#print axioms run_dispatch1
#print axioms run_finish
#print axioms run_result
end Challenge.Ripemd160.Submission.Proofs.Bytecode.J2Raw
