import Challenge.Ripemd160.Submission.Local20261028.GeneralExecution
import Challenge.Ripemd160.Submission.Local20261028.FirstExecution
import Challenge.Ripemd160.Submission.Proofs.Bytecode.DenseScheduleTrace
set_option warningAsError true
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.unusedSimpArgs false
namespace RipemdSubmissionTables20261028
open EvmSemantics EvmSemantics.EVM YulEvmCompiler Challenge.EvmProof
open Challenge.Ripemd160.Submission.Proofs.Bytecode
open StackRoundTrace

namespace GeneralTable
def result0 (s : State) (x : Nat → UInt256) (rho : List UInt256) : State :=
  {s with pc := (UInt256.ofNat 548), stack := General0.outputs x rho s, memory := General0.memory x s}
theorem step0 (s : State) (x : Nat → UInt256) (rho : List UInt256)
    (hstack : rho.length ≤ 900) (hrun : s.halt = .Running)
    (hactive : 35 ≤ s.activeWords.toNat) :
    runInstrSeq General0.template {s with pc := (UInt256.ofNat 530), stack := General0.inputs x rho} = some (result0 s x rho) := by
  have h := General0.run s x rho hstack hrun hactive
  exact h
def args1 (s : State) (x : Nat → UInt256) (rho : List UInt256) (j : Nat) : UInt256 :=
  ((result0 s x rho).stack[j]?).getD 0
def result1 (s : State) (x : Nat → UInt256) (rho : List UInt256) : State :=
  {(result0 s x rho) with pc := (UInt256.ofNat 609), stack := General1.outputs (args1 s x rho) rho (result0 s x rho), memory := General1.memory (args1 s x rho) (result0 s x rho)}
theorem entry1 (s : State) (x : Nat → UInt256) (rho : List UInt256) :
  {(result0 s x rho) with pc := (UInt256.ofNat 548), stack := General1.inputs (args1 s x rho) rho} = (result0 s x rho) := by
  simp [args1, result0, General0.outputs, General1.inputs]
theorem step1 (s : State) (x : Nat → UInt256) (rho : List UInt256)
    (hstack : rho.length ≤ 900) (hrun : s.halt = .Running)
    (hactive : 35 ≤ s.activeWords.toNat) :
    runInstrSeq General1.template (result0 s x rho) = some (result1 s x rho) := by
  have h := General1.run (result0 s x rho) (args1 s x rho) rho hstack hrun hactive
  rw [entry1] at h
  exact h
def args2 (s : State) (x : Nat → UInt256) (rho : List UInt256) (j : Nat) : UInt256 :=
  ((result1 s x rho).stack[j]?).getD 0
def result2 (s : State) (x : Nat → UInt256) (rho : List UInt256) : State :=
  {(result1 s x rho) with pc := (UInt256.ofNat 630), stack := General2.outputs (args2 s x rho) rho (result1 s x rho), memory := General2.memory (args2 s x rho) (result1 s x rho)}
theorem entry2 (s : State) (x : Nat → UInt256) (rho : List UInt256) :
  {(result1 s x rho) with pc := (UInt256.ofNat 609), stack := General2.inputs (args2 s x rho) rho} = (result1 s x rho) := by
  simp [args2, result1, General1.outputs, General2.inputs]
theorem step2 (s : State) (x : Nat → UInt256) (rho : List UInt256)
    (hstack : rho.length ≤ 900) (hrun : s.halt = .Running)
    (hactive : 35 ≤ s.activeWords.toNat) :
    runInstrSeq General2.template (result1 s x rho) = some (result2 s x rho) := by
  have h := General2.run (result1 s x rho) (args2 s x rho) rho hstack hrun hactive
  rw [entry2] at h
  exact h
def args3 (s : State) (x : Nat → UInt256) (rho : List UInt256) (j : Nat) : UInt256 :=
  ((result2 s x rho).stack[j]?).getD 0
def result3 (s : State) (x : Nat → UInt256) (rho : List UInt256) : State :=
  {(result2 s x rho) with pc := (UInt256.ofNat 651), stack := General3.outputs (args3 s x rho) rho (result2 s x rho), memory := General3.memory (args3 s x rho) (result2 s x rho)}
theorem entry3 (s : State) (x : Nat → UInt256) (rho : List UInt256) :
  {(result2 s x rho) with pc := (UInt256.ofNat 630), stack := General3.inputs (args3 s x rho) rho} = (result2 s x rho) := by
  simp [args3, result2, General2.outputs, General3.inputs]
theorem step3 (s : State) (x : Nat → UInt256) (rho : List UInt256)
    (hstack : rho.length ≤ 900) (hrun : s.halt = .Running)
    (hactive : 35 ≤ s.activeWords.toNat) :
    runInstrSeq General3.template (result2 s x rho) = some (result3 s x rho) := by
  have h := General3.run (result2 s x rho) (args3 s x rho) rho hstack hrun hactive
  rw [entry3] at h
  exact h
def args4 (s : State) (x : Nat → UInt256) (rho : List UInt256) (j : Nat) : UInt256 :=
  ((result3 s x rho).stack[j]?).getD 0
def result4 (s : State) (x : Nat → UInt256) (rho : List UInt256) : State :=
  {(result3 s x rho) with pc := (UInt256.ofNat 670), stack := General4.outputs (args4 s x rho) rho (result3 s x rho), memory := General4.memory (args4 s x rho) (result3 s x rho)}
theorem entry4 (s : State) (x : Nat → UInt256) (rho : List UInt256) :
  {(result3 s x rho) with pc := (UInt256.ofNat 651), stack := General4.inputs (args4 s x rho) rho} = (result3 s x rho) := by
  simp [args4, result3, General3.outputs, General4.inputs]
theorem step4 (s : State) (x : Nat → UInt256) (rho : List UInt256)
    (hstack : rho.length ≤ 900) (hrun : s.halt = .Running)
    (hactive : 35 ≤ s.activeWords.toNat) :
    runInstrSeq General4.template (result3 s x rho) = some (result4 s x rho) := by
  have h := General4.run (result3 s x rho) (args4 s x rho) rho hstack hrun hactive
  rw [entry4] at h
  exact h
def args5 (s : State) (x : Nat → UInt256) (rho : List UInt256) (j : Nat) : UInt256 :=
  ((result4 s x rho).stack[j]?).getD 0
def result5 (s : State) (x : Nat → UInt256) (rho : List UInt256) : State :=
  {(result4 s x rho) with pc := (UInt256.ofNat 693), stack := General5.outputs (args5 s x rho) rho (result4 s x rho), memory := General5.memory (args5 s x rho) (result4 s x rho)}
theorem entry5 (s : State) (x : Nat → UInt256) (rho : List UInt256) :
  {(result4 s x rho) with pc := (UInt256.ofNat 670), stack := General5.inputs (args5 s x rho) rho} = (result4 s x rho) := by
  simp [args5, result4, General4.outputs, General5.inputs]
theorem step5 (s : State) (x : Nat → UInt256) (rho : List UInt256)
    (hstack : rho.length ≤ 900) (hrun : s.halt = .Running)
    (hactive : 35 ≤ s.activeWords.toNat) :
    runInstrSeq General5.template (result4 s x rho) = some (result5 s x rho) := by
  have h := General5.run (result4 s x rho) (args5 s x rho) rho hstack hrun hactive
  rw [entry5] at h
  exact h
def args6 (s : State) (x : Nat → UInt256) (rho : List UInt256) (j : Nat) : UInt256 :=
  ((result5 s x rho).stack[j]?).getD 0
def result6 (s : State) (x : Nat → UInt256) (rho : List UInt256) : State :=
  {(result5 s x rho) with pc := (UInt256.ofNat 749), stack := General6.outputs (args6 s x rho) rho (result5 s x rho), memory := General6.memory (args6 s x rho) (result5 s x rho)}
theorem entry6 (s : State) (x : Nat → UInt256) (rho : List UInt256) :
  {(result5 s x rho) with pc := (UInt256.ofNat 693), stack := General6.inputs (args6 s x rho) rho} = (result5 s x rho) := by
  simp [args6, result5, General5.outputs, General6.inputs]
theorem step6 (s : State) (x : Nat → UInt256) (rho : List UInt256)
    (hstack : rho.length ≤ 900) (hrun : s.halt = .Running)
    (hactive : 35 ≤ s.activeWords.toNat) :
    runInstrSeq General6.template (result5 s x rho) = some (result6 s x rho) := by
  have h := General6.run (result5 s x rho) (args6 s x rho) rho hstack hrun hactive
  rw [entry6] at h
  exact h
def args7 (s : State) (x : Nat → UInt256) (rho : List UInt256) (j : Nat) : UInt256 :=
  ((result6 s x rho).stack[j]?).getD 0
def result7 (s : State) (x : Nat → UInt256) (rho : List UInt256) : State :=
  {(result6 s x rho) with pc := (UInt256.ofNat 803), stack := General7.outputs (args7 s x rho) rho (result6 s x rho), memory := General7.memory (args7 s x rho) (result6 s x rho)}
theorem entry7 (s : State) (x : Nat → UInt256) (rho : List UInt256) :
  {(result6 s x rho) with pc := (UInt256.ofNat 749), stack := General7.inputs (args7 s x rho) rho} = (result6 s x rho) := by
  simp [args7, result6, General6.outputs, General7.inputs]
theorem step7 (s : State) (x : Nat → UInt256) (rho : List UInt256)
    (hstack : rho.length ≤ 900) (hrun : s.halt = .Running)
    (hactive : 35 ≤ s.activeWords.toNat) :
    runInstrSeq General7.template (result6 s x rho) = some (result7 s x rho) := by
  have h := General7.run (result6 s x rho) (args7 s x rho) rho hstack hrun hactive
  rw [entry7] at h
  exact h
def args8 (s : State) (x : Nat → UInt256) (rho : List UInt256) (j : Nat) : UInt256 :=
  ((result7 s x rho).stack[j]?).getD 0
def result8 (s : State) (x : Nat → UInt256) (rho : List UInt256) : State :=
  {(result7 s x rho) with pc := (UInt256.ofNat 823), stack := General8.outputs (args8 s x rho) rho (result7 s x rho), memory := General8.memory (args8 s x rho) (result7 s x rho)}
theorem entry8 (s : State) (x : Nat → UInt256) (rho : List UInt256) :
  {(result7 s x rho) with pc := (UInt256.ofNat 803), stack := General8.inputs (args8 s x rho) rho} = (result7 s x rho) := by
  simp [args8, result7, General7.outputs, General8.inputs]
theorem step8 (s : State) (x : Nat → UInt256) (rho : List UInt256)
    (hstack : rho.length ≤ 900) (hrun : s.halt = .Running)
    (hactive : 35 ≤ s.activeWords.toNat) :
    runInstrSeq General8.template (result7 s x rho) = some (result8 s x rho) := by
  have h := General8.run (result7 s x rho) (args8 s x rho) rho hstack hrun hactive
  rw [entry8] at h
  exact h
def template : List Instr := ((((((((General0.template ++ General1.template) ++ General2.template) ++ General3.template) ++ General4.template) ++ General5.template) ++ General6.template) ++ General7.template) ++ General8.template)
theorem exact_bytes :
    (Challenge.Ripemd160.Benchmark.bytecode.data.toList.drop 530).take 293 =
      PcEncoding.assembleBytes template := by
  rw [CandidateBytes.exact_list]
  change (CandidateBytes.bytes.drop (512+18)).take 293 = _
  rw [← List.drop_drop, CandidateBytes.drop8]
  decide +kernel

theorem run (s : State) (x : Nat → UInt256) (rho : List UInt256)
    (hstack : rho.length ≤ 900) (hrun : s.halt = .Running)
    (hactive : 35 ≤ s.activeWords.toNat) :
    runInstrSeq template {s with pc := (UInt256.ofNat 530), stack := General0.inputs x rho} =
      some {s with pc := (UInt256.ofNat 823), stack := General0.inputs x rho, memory := (result8 s x rho).memory} := by
  have g0 := step0 s x rho hstack hrun hactive
  have g1 := DenseScheduleTrace.runInstrSeq_append_running g0
    (show (result0 s x rho).halt = .Running from hrun)
    (step1 s x rho hstack hrun hactive)
  have g2 := DenseScheduleTrace.runInstrSeq_append_running g1
    (show (result1 s x rho).halt = .Running from hrun)
    (step2 s x rho hstack hrun hactive)
  have g3 := DenseScheduleTrace.runInstrSeq_append_running g2
    (show (result2 s x rho).halt = .Running from hrun)
    (step3 s x rho hstack hrun hactive)
  have g4 := DenseScheduleTrace.runInstrSeq_append_running g3
    (show (result3 s x rho).halt = .Running from hrun)
    (step4 s x rho hstack hrun hactive)
  have g5 := DenseScheduleTrace.runInstrSeq_append_running g4
    (show (result4 s x rho).halt = .Running from hrun)
    (step5 s x rho hstack hrun hactive)
  have g6 := DenseScheduleTrace.runInstrSeq_append_running g5
    (show (result5 s x rho).halt = .Running from hrun)
    (step6 s x rho hstack hrun hactive)
  have g7 := DenseScheduleTrace.runInstrSeq_append_running g6
    (show (result6 s x rho).halt = .Running from hrun)
    (step7 s x rho hstack hrun hactive)
  have g8 := DenseScheduleTrace.runInstrSeq_append_running g7
    (show (result7 s x rho).halt = .Running from hrun)
    (step8 s x rho hstack hrun hactive)
  have hfinal : result8 s x rho =
      {s with pc := (UInt256.ofNat 823), stack := General0.inputs x rho, memory := (result8 s x rho).memory} := by rfl
  rw [hfinal] at g8
  exact g8
#print axioms exact_bytes
#print axioms run
end GeneralTable

namespace FirstTable
def result0 (s : State) (x : Nat → UInt256) (rho : List UInt256) : State :=
  {s with pc := (UInt256.ofNat 10198), stack := First0.outputs x rho s, memory := First0.memory x s}
theorem step0 (s : State) (x : Nat → UInt256) (rho : List UInt256)
    (hstack : rho.length ≤ 900) (hrun : s.halt = .Running)
    (hactive : 34 ≤ s.activeWords.toNat) :
    runInstrSeq First0.template {s with pc := (UInt256.ofNat 10141), stack := First0.inputs x rho} = some (result0 s x rho) := by
  have h := First0.run s x rho hstack hrun hactive
  exact h
def args1 (s : State) (x : Nat → UInt256) (rho : List UInt256) (j : Nat) : UInt256 :=
  ((result0 s x rho).stack[j]?).getD 0
def result1 (s : State) (x : Nat → UInt256) (rho : List UInt256) : State :=
  {(result0 s x rho) with pc := (UInt256.ofNat 10343), stack := First1.outputs (args1 s x rho) rho (result0 s x rho), memory := First1.memory (args1 s x rho) (result0 s x rho)}
theorem entry1 (s : State) (x : Nat → UInt256) (rho : List UInt256) :
  {(result0 s x rho) with pc := (UInt256.ofNat 10198), stack := First1.inputs (args1 s x rho) rho} = (result0 s x rho) := by
  simp [args1, result0, First0.outputs, First1.inputs]
theorem step1 (s : State) (x : Nat → UInt256) (rho : List UInt256)
    (hstack : rho.length ≤ 900) (hrun : s.halt = .Running)
    (hactive : 34 ≤ s.activeWords.toNat) :
    runInstrSeq First1.template (result0 s x rho) = some (result1 s x rho) := by
  have h := First1.run (result0 s x rho) (args1 s x rho) rho hstack hrun hactive
  rw [entry1] at h
  exact h
def args2 (s : State) (x : Nat → UInt256) (rho : List UInt256) (j : Nat) : UInt256 :=
  ((result1 s x rho).stack[j]?).getD 0
def result2 (s : State) (x : Nat → UInt256) (rho : List UInt256) : State :=
  {(result1 s x rho) with pc := (UInt256.ofNat 10361), stack := First2.outputs (args2 s x rho) rho (result1 s x rho), memory := First2.memory (args2 s x rho) (result1 s x rho)}
theorem entry2 (s : State) (x : Nat → UInt256) (rho : List UInt256) :
  {(result1 s x rho) with pc := (UInt256.ofNat 10343), stack := First2.inputs (args2 s x rho) rho} = (result1 s x rho) := by
  simp [args2, result1, First1.outputs, First2.inputs]
theorem step2 (s : State) (x : Nat → UInt256) (rho : List UInt256)
    (hstack : rho.length ≤ 900) (hrun : s.halt = .Running)
    (hactive : 34 ≤ s.activeWords.toNat) :
    runInstrSeq First2.template (result1 s x rho) = some (result2 s x rho) := by
  have h := First2.run (result1 s x rho) (args2 s x rho) rho hstack hrun hactive
  rw [entry2] at h
  exact h
def args3 (s : State) (x : Nat → UInt256) (rho : List UInt256) (j : Nat) : UInt256 :=
  ((result2 s x rho).stack[j]?).getD 0
def result3 (s : State) (x : Nat → UInt256) (rho : List UInt256) : State :=
  {(result2 s x rho) with pc := (UInt256.ofNat 10384), stack := First3.outputs (args3 s x rho) rho (result2 s x rho), memory := First3.memory (args3 s x rho) (result2 s x rho)}
theorem entry3 (s : State) (x : Nat → UInt256) (rho : List UInt256) :
  {(result2 s x rho) with pc := (UInt256.ofNat 10361), stack := First3.inputs (args3 s x rho) rho} = (result2 s x rho) := by
  simp [args3, result2, First2.outputs, First3.inputs]
theorem step3 (s : State) (x : Nat → UInt256) (rho : List UInt256)
    (hstack : rho.length ≤ 900) (hrun : s.halt = .Running)
    (hactive : 34 ≤ s.activeWords.toNat) :
    runInstrSeq First3.template (result2 s x rho) = some (result3 s x rho) := by
  have h := First3.run (result2 s x rho) (args3 s x rho) rho hstack hrun hactive
  rw [entry3] at h
  exact h
def args4 (s : State) (x : Nat → UInt256) (rho : List UInt256) (j : Nat) : UInt256 :=
  ((result3 s x rho).stack[j]?).getD 0
def result4 (s : State) (x : Nat → UInt256) (rho : List UInt256) : State :=
  {(result3 s x rho) with pc := (UInt256.ofNat 10410), stack := First4.outputs (args4 s x rho) rho (result3 s x rho), memory := First4.memory (args4 s x rho) (result3 s x rho)}
theorem entry4 (s : State) (x : Nat → UInt256) (rho : List UInt256) :
  {(result3 s x rho) with pc := (UInt256.ofNat 10384), stack := First4.inputs (args4 s x rho) rho} = (result3 s x rho) := by
  simp [args4, result3, First3.outputs, First4.inputs]
theorem step4 (s : State) (x : Nat → UInt256) (rho : List UInt256)
    (hstack : rho.length ≤ 900) (hrun : s.halt = .Running)
    (hactive : 34 ≤ s.activeWords.toNat) :
    runInstrSeq First4.template (result3 s x rho) = some (result4 s x rho) := by
  have h := First4.run (result3 s x rho) (args4 s x rho) rho hstack hrun hactive
  rw [entry4] at h
  exact h
def args5 (s : State) (x : Nat → UInt256) (rho : List UInt256) (j : Nat) : UInt256 :=
  ((result4 s x rho).stack[j]?).getD 0
def result5 (s : State) (x : Nat → UInt256) (rho : List UInt256) : State :=
  {(result4 s x rho) with pc := (UInt256.ofNat 10433), stack := First5.outputs (args5 s x rho) rho (result4 s x rho), memory := First5.memory (args5 s x rho) (result4 s x rho)}
theorem entry5 (s : State) (x : Nat → UInt256) (rho : List UInt256) :
  {(result4 s x rho) with pc := (UInt256.ofNat 10410), stack := First5.inputs (args5 s x rho) rho} = (result4 s x rho) := by
  simp [args5, result4, First4.outputs, First5.inputs]
theorem step5 (s : State) (x : Nat → UInt256) (rho : List UInt256)
    (hstack : rho.length ≤ 900) (hrun : s.halt = .Running)
    (hactive : 34 ≤ s.activeWords.toNat) :
    runInstrSeq First5.template (result4 s x rho) = some (result5 s x rho) := by
  have h := First5.run (result4 s x rho) (args5 s x rho) rho hstack hrun hactive
  rw [entry5] at h
  exact h
def args6 (s : State) (x : Nat → UInt256) (rho : List UInt256) (j : Nat) : UInt256 :=
  ((result5 s x rho).stack[j]?).getD 0
def result6 (s : State) (x : Nat → UInt256) (rho : List UInt256) : State :=
  {(result5 s x rho) with pc := (UInt256.ofNat 10455), stack := First6.outputs (args6 s x rho) rho (result5 s x rho), memory := First6.memory (args6 s x rho) (result5 s x rho)}
theorem entry6 (s : State) (x : Nat → UInt256) (rho : List UInt256) :
  {(result5 s x rho) with pc := (UInt256.ofNat 10433), stack := First6.inputs (args6 s x rho) rho} = (result5 s x rho) := by
  simp [args6, result5, First5.outputs, First6.inputs]
theorem step6 (s : State) (x : Nat → UInt256) (rho : List UInt256)
    (hstack : rho.length ≤ 900) (hrun : s.halt = .Running)
    (hactive : 34 ≤ s.activeWords.toNat) :
    runInstrSeq First6.template (result5 s x rho) = some (result6 s x rho) := by
  have h := First6.run (result5 s x rho) (args6 s x rho) rho hstack hrun hactive
  rw [entry6] at h
  exact h
def args7 (s : State) (x : Nat → UInt256) (rho : List UInt256) (j : Nat) : UInt256 :=
  ((result6 s x rho).stack[j]?).getD 0
def result7 (s : State) (x : Nat → UInt256) (rho : List UInt256) : State :=
  {(result6 s x rho) with pc := (UInt256.ofNat 10463), stack := First7.outputs (args7 s x rho) rho (result6 s x rho), memory := First7.memory (args7 s x rho) (result6 s x rho)}
theorem entry7 (s : State) (x : Nat → UInt256) (rho : List UInt256) :
  {(result6 s x rho) with pc := (UInt256.ofNat 10455), stack := First7.inputs (args7 s x rho) rho} = (result6 s x rho) := by
  simp [args7, result6, First6.outputs, First7.inputs]
theorem step7 (s : State) (x : Nat → UInt256) (rho : List UInt256)
    (hstack : rho.length ≤ 900) (hrun : s.halt = .Running)
    (hactive : 34 ≤ s.activeWords.toNat) :
    runInstrSeq First7.template (result6 s x rho) = some (result7 s x rho) := by
  have h := First7.run (result6 s x rho) (args7 s x rho) rho hstack hrun hactive
  rw [entry7] at h
  exact h
def template : List Instr := (((((((First0.template ++ First1.template) ++ First2.template) ++ First3.template) ++ First4.template) ++ First5.template) ++ First6.template) ++ First7.template)
theorem exact_bytes :
    (Challenge.Ripemd160.Benchmark.bytecode.data.toList.drop 10141).take 322 =
      PcEncoding.assembleBytes template := by
  rw [CandidateBytes.exact_list]
  change (CandidateBytes.bytes.drop (10112+29)).take 322 = _
  rw [← List.drop_drop, CandidateBytes.drop158]
  decide +kernel

theorem run (s : State) (x : Nat → UInt256) (rho : List UInt256)
    (hstack : rho.length ≤ 900) (hrun : s.halt = .Running)
    (hactive : 34 ≤ s.activeWords.toNat) :
    runInstrSeq template {s with pc := (UInt256.ofNat 10141), stack := First0.inputs x rho} =
      some {s with pc := (UInt256.ofNat 10463), stack := First0.inputs x rho, memory := (result7 s x rho).memory} := by
  have g0 := step0 s x rho hstack hrun hactive
  have g1 := DenseScheduleTrace.runInstrSeq_append_running g0
    (show (result0 s x rho).halt = .Running from hrun)
    (step1 s x rho hstack hrun hactive)
  have g2 := DenseScheduleTrace.runInstrSeq_append_running g1
    (show (result1 s x rho).halt = .Running from hrun)
    (step2 s x rho hstack hrun hactive)
  have g3 := DenseScheduleTrace.runInstrSeq_append_running g2
    (show (result2 s x rho).halt = .Running from hrun)
    (step3 s x rho hstack hrun hactive)
  have g4 := DenseScheduleTrace.runInstrSeq_append_running g3
    (show (result3 s x rho).halt = .Running from hrun)
    (step4 s x rho hstack hrun hactive)
  have g5 := DenseScheduleTrace.runInstrSeq_append_running g4
    (show (result4 s x rho).halt = .Running from hrun)
    (step5 s x rho hstack hrun hactive)
  have g6 := DenseScheduleTrace.runInstrSeq_append_running g5
    (show (result5 s x rho).halt = .Running from hrun)
    (step6 s x rho hstack hrun hactive)
  have g7 := DenseScheduleTrace.runInstrSeq_append_running g6
    (show (result6 s x rho).halt = .Running from hrun)
    (step7 s x rho hstack hrun hactive)
  have hfinal : result7 s x rho =
      {s with pc := (UInt256.ofNat 10463), stack := First0.inputs x rho, memory := (result7 s x rho).memory} := by rfl
  rw [hfinal] at g7
  exact g7
#print axioms exact_bytes
#print axioms run
end FirstTable
end RipemdSubmissionTables20261028
