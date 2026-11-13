import Challenge.Ripemd160.Submission.Local20261028.PrepFirst0
import Challenge.Ripemd160.Submission.Local20261028.PrepFirst1
import Challenge.Ripemd160.Submission.Local20261028.PrepFirst2
import Challenge.Ripemd160.Submission.Local20261028.PrepFirst3
import Challenge.Ripemd160.Submission.Local20261028.PrepFirst4
import Challenge.Ripemd160.Submission.Local20261028.PrepFirst5
import Challenge.Ripemd160.Submission.Proofs.Bytecode.DenseScheduleTrace
set_option warningAsError true
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.unusedSimpArgs false
namespace RipemdSubmission20261101
open EvmSemantics EvmSemantics.EVM YulEvmCompiler Challenge.EvmProof
open Challenge.Ripemd160.Submission.Proofs.Bytecode RipemdSubmissionTables20261028
open StackRoundTrace
namespace FirstTable
def result0 (s : State) (x : Nat → UInt256) (rho : List UInt256) : State :=
  {s with pc := (UInt256.ofNat 9987), stack := First0.outputs x rho s, memory := First0.memory x s}
theorem step0 (s : State) (x : Nat → UInt256) (rho : List UInt256)
    (hstack : rho.length ≤ 900) (hrun : s.halt = .Running)
    (hactive : 34 ≤ s.activeWords.toNat) :
    runInstrSeq First0.template {s with pc := (UInt256.ofNat 9944), stack := First0.inputs x rho} = some (result0 s x rho) := by
  have h := First0.run s x rho hstack hrun hactive
  exact h
def args1 (s : State) (x : Nat → UInt256) (rho : List UInt256) (j : Nat) : UInt256 :=
  ((result0 s x rho).stack[j]?).getD 0
def result1 (s : State) (x : Nat → UInt256) (rho : List UInt256) : State :=
  {(result0 s x rho) with pc := (UInt256.ofNat 10052), stack := First1.outputs (args1 s x rho) rho (result0 s x rho), memory := First1.memory (args1 s x rho) (result0 s x rho)}
theorem entry1 (s : State) (x : Nat → UInt256) (rho : List UInt256) :
    {(result0 s x rho) with pc := (UInt256.ofNat 9987), stack := First1.inputs (args1 s x rho) rho} = (result0 s x rho) := by
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
  {(result1 s x rho) with pc := (UInt256.ofNat 10089), stack := First2.outputs (args2 s x rho) rho (result1 s x rho), memory := First2.memory (args2 s x rho) (result1 s x rho)}
theorem entry2 (s : State) (x : Nat → UInt256) (rho : List UInt256) :
    {(result1 s x rho) with pc := (UInt256.ofNat 10052), stack := First2.inputs (args2 s x rho) rho} = (result1 s x rho) := by
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
  {(result2 s x rho) with pc := (UInt256.ofNat 10136), stack := First3.outputs (args3 s x rho) rho (result2 s x rho), memory := First3.memory (args3 s x rho) (result2 s x rho)}
theorem entry3 (s : State) (x : Nat → UInt256) (rho : List UInt256) :
    {(result2 s x rho) with pc := (UInt256.ofNat 10089), stack := First3.inputs (args3 s x rho) rho} = (result2 s x rho) := by
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
  {(result3 s x rho) with pc := (UInt256.ofNat 10181), stack := First4.outputs (args4 s x rho) rho (result3 s x rho), memory := First4.memory (args4 s x rho) (result3 s x rho)}
theorem entry4 (s : State) (x : Nat → UInt256) (rho : List UInt256) :
    {(result3 s x rho) with pc := (UInt256.ofNat 10136), stack := First4.inputs (args4 s x rho) rho} = (result3 s x rho) := by
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
  {(result4 s x rho) with pc := (UInt256.ofNat 10185), stack := First5.outputs (args5 s x rho) rho (result4 s x rho), memory := First5.memory (args5 s x rho) (result4 s x rho)}
theorem entry5 (s : State) (x : Nat → UInt256) (rho : List UInt256) :
    {(result4 s x rho) with pc := (UInt256.ofNat 10181), stack := First5.inputs (args5 s x rho) rho} = (result4 s x rho) := by
  simp [args5, result4, First4.outputs, First5.inputs]
theorem step5 (s : State) (x : Nat → UInt256) (rho : List UInt256)
    (hstack : rho.length ≤ 900) (hrun : s.halt = .Running)
    (hactive : 34 ≤ s.activeWords.toNat) :
    runInstrSeq First5.template (result4 s x rho) = some (result5 s x rho) := by
  have h := First5.run (result4 s x rho) (args5 s x rho) rho hstack hrun hactive
  rw [entry5] at h
  exact h
def template : List Instr := (((((First0.template ++ First1.template) ++ First2.template) ++ First3.template) ++ First4.template) ++ First5.template)
theorem exact_bytes :
    (Challenge.Ripemd160.Benchmark.bytecode.data.toList.drop 9944).take 241 =
      PcEncoding.assembleBytes template := by
  rw [CandidateBytes.exact_list]
  change (CandidateBytes.bytes.drop (9920+24)).take 241 = _
  rw [← List.drop_drop, CandidateBytes.drop155]
  decide +kernel
theorem run (s : State) (x : Nat → UInt256) (rho : List UInt256)
    (hstack : rho.length ≤ 900) (hrun : s.halt = .Running)
    (hactive : 34 ≤ s.activeWords.toNat) :
    runInstrSeq template {s with pc := (UInt256.ofNat 9944), stack := First0.inputs x rho} =
      some {s with pc := (UInt256.ofNat 10185), stack := First0.inputs x rho, memory := (result5 s x rho).memory} := by
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
  have hfinal : result5 s x rho =
      {s with pc := (UInt256.ofNat 10185), stack := First0.inputs x rho, memory := (result5 s x rho).memory} := by rfl
  rw [hfinal] at g5
  exact g5
#print axioms exact_bytes
#print axioms run
end FirstTable
end RipemdSubmission20261101
