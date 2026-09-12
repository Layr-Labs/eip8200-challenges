import Challenge.Ripemd160.Submission.Proofs.Bytecode.RecognitionControlRaw

set_option warningAsError true
set_option maxRecDepth 100000
set_option maxHeartbeats 3000000
set_option linter.unusedSimpArgs false
namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.RecognitionBranchRaw
open EvmSemantics EvmSemantics.EVM YulEvmCompiler Challenge.EvmProof
open StackRoundTrace RecognitionBodyRaw

def clampTemplateWith (width : Fin 33) (dest : Nat) : List Instr := [.op (.Dup ⟨4, by decide⟩), .op (.Dup ⟨4, by decide⟩), .op .LT,
  .push width (UInt256.ofNat dest), .op .JUMPI]

theorem run_clamp_width (width : Fin 33) (hwidth : width ≠ 0) (s : State) (pc : UInt256) (f : RecognitionBodyRaw.Frame)
    (rho : List UInt256) (dest : Nat) (hstack : rho.length ≤ 990)
    (hrun : s.halt = .Running)
    (hvalid : Decode.isValidJumpDest s.executionEnv.code (UInt256.ofNat dest).toNat = true) :
    runInstrSeq (clampTemplateWith width dest) {s with pc := pc, stack := frame f rho} =
      some {s with
        pc := if f.stop.toNat < f.full.toNat then UInt256.ofNat dest else pcAfter pc (clampTemplateWith width dest)
        stack := frame f rho} := by
  have hbase : rho.length < 1024 := by omega
  have hcap (n : Nat) (hn : n ≤ 30) : rho.length + n < 1024 := by omega
  simp only [Word.word_toNat_ofNat] at hvalid
  norm_num only at hvalid
  by_cases hc : f.stop.toNat < f.full.toNat
  all_goals simp (discharger := omega) [clampTemplateWith, frame, runInstrSeq, Stepper.runInstr,
    pcAfter, UInt256.succ, Instr.size, List.exchange, List.getElem?_cons_zero,
    Nat.add_assoc, hrun, hbase, hcap, UInt256.lt, hwidth, UInt256.eq, UInt256.isZero, UInt256.isTrue,
    hc, hvalid, Word.word_toNat_ofNat, Word.literal_eq_ofNat]
  all_goals first | rfl | (simp only [Nat.add_comm]; rfl)
#print axioms run_clamp_width

def clampTemplate (dest : Nat) : List Instr := [.op (.Dup ⟨4, by decide⟩), .op (.Dup ⟨4, by decide⟩), .op .LT,
  .push ⟨1, by decide⟩ (UInt256.ofNat dest), .op .JUMPI]

theorem run_clamp (s : State) (pc : UInt256) (f : RecognitionBodyRaw.Frame)
    (rho : List UInt256) (dest : Nat) (hstack : rho.length ≤ 990)
    (hrun : s.halt = .Running)
    (hvalid : Decode.isValidJumpDest s.executionEnv.code (UInt256.ofNat dest).toNat = true) :
    runInstrSeq (clampTemplate dest) {s with pc := pc, stack := frame f rho} =
      some {s with
        pc := if f.stop.toNat < f.full.toNat then UInt256.ofNat dest else pcAfter pc (clampTemplate dest)
        stack := frame f rho} := by
  have hbase : rho.length < 1024 := by omega
  have hcap (n : Nat) (hn : n ≤ 30) : rho.length + n < 1024 := by omega
  simp only [Word.word_toNat_ofNat] at hvalid
  norm_num only at hvalid
  by_cases hc : f.stop.toNat < f.full.toNat
  all_goals simp (discharger := omega) [clampTemplate, frame, runInstrSeq, Stepper.runInstr,
    pcAfter, UInt256.succ, Instr.size, List.exchange, List.getElem?_cons_zero,
    Nat.add_assoc, hrun, hbase, hcap, UInt256.lt, UInt256.eq, UInt256.isZero, UInt256.isTrue,
    hc, hvalid, Word.word_toNat_ofNat, Word.literal_eq_ofNat]
  all_goals rfl
#print axioms run_clamp

def segmentTemplate (dest : Nat) : List Instr := [.op .JUMPDEST, .op (.Dup ⟨4, by decide⟩), .op (.Dup ⟨2, by decide⟩), .op .LT, .op .ISZERO,
  .push ⟨2, by decide⟩ (UInt256.ofNat dest), .op .JUMPI]

theorem run_segment (s : State) (pc : UInt256) (f : RecognitionBodyRaw.Frame)
    (rho : List UInt256) (dest : Nat) (hstack : rho.length ≤ 990)
    (hrun : s.halt = .Running)
    (hvalid : Decode.isValidJumpDest s.executionEnv.code (UInt256.ofNat dest).toNat = true) :
    runInstrSeq (segmentTemplate dest) {s with pc := pc, stack := frame f rho} =
      some {s with
        pc := if ¬ f.off.toNat < f.full.toNat then UInt256.ofNat dest else pcAfter pc (segmentTemplate dest)
        stack := frame f rho} := by
  have hbase : rho.length < 1024 := by omega
  have hcap (n : Nat) (hn : n ≤ 30) : rho.length + n < 1024 := by omega
  simp only [Word.word_toNat_ofNat] at hvalid
  norm_num only at hvalid
  by_cases hc : ¬ f.off.toNat < f.full.toNat
  all_goals try simp only [not_not] at hc
  all_goals simp (discharger := omega) [segmentTemplate, frame, runInstrSeq, Stepper.runInstr,
    pcAfter, UInt256.succ, Instr.size, List.exchange, List.getElem?_cons_zero,
    Nat.add_assoc, hrun, hbase, hcap, UInt256.lt, UInt256.eq, UInt256.isZero, UInt256.isTrue,
    hc, hvalid, Word.word_toNat_ofNat, Word.literal_eq_ofNat]
  all_goals rfl
#print axioms run_segment

def partialTemplate (dest : Nat) : List Instr := [.op .JUMPDEST, .op .CALLDATASIZE, .op (.Dup ⟨2, by decide⟩), .op .EQ,
  .push ⟨2, by decide⟩ (UInt256.ofNat dest), .op .JUMPI]

theorem run_partial (s : State) (pc : UInt256) (f : RecognitionBodyRaw.Frame)
    (rho : List UInt256) (dest : Nat) (hstack : rho.length ≤ 990)
    (hrun : s.halt = .Running)
    (hvalid : Decode.isValidJumpDest s.executionEnv.code (UInt256.ofNat dest).toNat = true) :
    runInstrSeq (partialTemplate dest) {s with pc := pc, stack := frame f rho} =
      some {s with
        pc := if f.off.toNat = s.executionEnv.calldata.size % 2^256 then UInt256.ofNat dest else pcAfter pc (partialTemplate dest)
        stack := frame f rho} := by
  have hbase : rho.length < 1024 := by omega
  have hcap (n : Nat) (hn : n ≤ 30) : rho.length + n < 1024 := by omega
  simp only [Word.word_toNat_ofNat] at hvalid
  norm_num only at hvalid
  by_cases hc : f.off.toNat = s.executionEnv.calldata.size % 2^256
  all_goals norm_num only at hc
  all_goals simp (discharger := omega) [partialTemplate, frame, runInstrSeq, Stepper.runInstr,
    pcAfter, UInt256.succ, Instr.size, List.exchange, List.getElem?_cons_zero,
    Nat.add_assoc, hrun, hbase, hcap, UInt256.lt, UInt256.eq, UInt256.isZero, UInt256.isTrue,
    hc, hvalid, Word.word_toNat_ofNat, Word.literal_eq_ofNat]
  all_goals rfl
#print axioms run_partial

def finishTemplate (dest : Nat) : List Instr := [.op .JUMPDEST, .op (.Dup ⟨0, by decide⟩), .op .ISZERO,
  .push ⟨2, by decide⟩ (UInt256.ofNat dest), .op .JUMPI]

theorem run_finish (s : State) (pc : UInt256) (f : RecognitionBodyRaw.Frame)
    (rho : List UInt256) (dest : Nat) (hstack : rho.length ≤ 990)
    (hrun : s.halt = .Running)
    (hvalid : Decode.isValidJumpDest s.executionEnv.code (UInt256.ofNat dest).toNat = true) :
    runInstrSeq (finishTemplate dest) {s with pc := pc, stack := frame f rho} =
      some {s with
        pc := if f.acc.toNat = 0 then UInt256.ofNat dest else pcAfter pc (finishTemplate dest)
        stack := frame f rho} := by
  have hbase : rho.length < 1024 := by omega
  have hcap (n : Nat) (hn : n ≤ 30) : rho.length + n < 1024 := by omega
  simp only [Word.word_toNat_ofNat] at hvalid
  norm_num only at hvalid
  by_cases hc : f.acc.toNat = 0
  all_goals simp (discharger := omega) [finishTemplate, frame, runInstrSeq, Stepper.runInstr,
    pcAfter, UInt256.succ, Instr.size, List.exchange, List.getElem?_cons_zero,
    Nat.add_assoc, hrun, hbase, hcap, UInt256.lt, UInt256.eq, UInt256.isZero, UInt256.isTrue,
    hc, hvalid, Word.word_toNat_ofNat, Word.literal_eq_ofNat]
  all_goals rfl
#print axioms run_finish

def resetTemplate : List Instr :=
  [.op (.Dup ⟨4, by decide⟩), .op (.Swap ⟨3, by decide⟩), .op .POP]

theorem run_reset (s : State) (pc : UInt256) (f : RecognitionBodyRaw.Frame)
    (rho : List UInt256) (hstack : rho.length ≤ 990) (hrun : s.halt = .Running) :
    runInstrSeq resetTemplate {s with pc := pc, stack := frame f rho} =
      some {s with pc := pcAfter pc resetTemplate, stack := frame {f with stop := f.full} rho} := by
  have hbase : rho.length < 1024 := by omega
  have hcap (n : Nat) (hn : n ≤ 30) : rho.length + n < 1024 := by omega
  simp (discharger := omega) [resetTemplate, frame, runInstrSeq, Stepper.runInstr,
    pcAfter, UInt256.succ, Instr.size, List.exchange, List.getElem?_cons_zero,
    Nat.add_assoc, hrun, hbase, hcap, Word.word_toNat_ofNat, Word.literal_eq_ofNat]
  all_goals rfl
#print axioms run_reset

def cleanupTemplate (dest : Nat) : List Instr :=
  [.op .POP, .op .POP, .op .POP, .op .POP, .op .POP, .op .POP, .op .POP, .op .POP, .op .POP,
   .push ⟨2, by decide⟩ (UInt256.ofNat dest), .op .JUMP]

theorem run_cleanup (s : State) (pc : UInt256) (f : RecognitionBodyRaw.Frame)
    (rho : List UInt256) (dest : Nat) (hstack : rho.length ≤ 990) (hrun : s.halt = .Running)
    (hvalid : Decode.isValidJumpDest s.executionEnv.code (UInt256.ofNat dest).toNat = true) :
    runInstrSeq (cleanupTemplate dest) {s with pc := pc, stack := frame f rho} =
      some {s with pc := UInt256.ofNat dest, stack := rho} := by
  have hbase : rho.length < 1024 := by omega
  have hcap (n : Nat) (hn : n ≤ 30) : rho.length + n < 1024 := by omega
  simp only [Word.word_toNat_ofNat] at hvalid
  norm_num only at hvalid
  simp (discharger := omega) [cleanupTemplate, frame, runInstrSeq, Stepper.runInstr,
    pcAfter, UInt256.succ, Instr.size, List.exchange, List.getElem?_cons_zero,
    Nat.add_assoc, hrun, hbase, hcap, hvalid, Word.word_toNat_ofNat, Word.literal_eq_ofNat]
#print axioms run_cleanup
end Challenge.Ripemd160.Submission.Proofs.Bytecode.RecognitionBranchRaw
