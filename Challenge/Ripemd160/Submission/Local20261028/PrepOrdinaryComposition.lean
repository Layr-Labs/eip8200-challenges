import Challenge.Ripemd160.Submission.Local20261028.PrepOrdinary0
import Challenge.Ripemd160.Submission.Local20261028.PrepOrdinary1
import Challenge.Ripemd160.Submission.Local20261028.PrepOrdinary2
import Challenge.Ripemd160.Submission.Local20261028.PrepOrdinary3
import Challenge.Ripemd160.Submission.Local20261028.PrepOrdinary4
import Challenge.Ripemd160.Submission.Local20261028.PrepOrdinary5
import Challenge.Ripemd160.Submission.Local20261028.PrepOrdinary6
import Challenge.Ripemd160.Submission.Local20261028.PrepOrdinary7
import Challenge.Ripemd160.Submission.Proofs.Bytecode.DenseScheduleTrace
set_option warningAsError true
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.unusedSimpArgs false
namespace RipemdSubmission20261101
open EvmSemantics EvmSemantics.EVM YulEvmCompiler Challenge.EvmProof
open Challenge.Ripemd160.Submission.Proofs.Bytecode RipemdSubmissionTables20261028
open StackRoundTrace
namespace OrdinaryTable
def result0 (s : State) (x : Nat → UInt256) (rho : List UInt256) : State :=
  {s with pc := (UInt256.ofNat 556), stack := Ordinary0.outputs x rho s, memory := Ordinary0.memory x s}
theorem step0 (s : State) (x : Nat → UInt256) (rho : List UInt256)
    (hstack : rho.length ≤ 900) (hrun : s.halt = .Running)
    (hactive : 34 ≤ s.activeWords.toNat) :
    runInstrSeq Ordinary0.template {s with pc := (UInt256.ofNat 530), stack := Ordinary0.inputs x rho} = some (result0 s x rho) := by
  have h := Ordinary0.run s x rho hstack hrun hactive
  exact h
def args1 (s : State) (x : Nat → UInt256) (rho : List UInt256) (j : Nat) : UInt256 :=
  ((result0 s x rho).stack[j]?).getD 0
def result1 (s : State) (x : Nat → UInt256) (rho : List UInt256) : State :=
  {(result0 s x rho) with pc := (UInt256.ofNat 621), stack := Ordinary1.outputs (args1 s x rho) rho (result0 s x rho), memory := Ordinary1.memory (args1 s x rho) (result0 s x rho)}
theorem entry1 (s : State) (x : Nat → UInt256) (rho : List UInt256) :
    {(result0 s x rho) with pc := (UInt256.ofNat 556), stack := Ordinary1.inputs (args1 s x rho) rho} = (result0 s x rho) := by
  simp [args1, result0, Ordinary0.outputs, Ordinary1.inputs]
theorem step1 (s : State) (x : Nat → UInt256) (rho : List UInt256)
    (hstack : rho.length ≤ 900) (hrun : s.halt = .Running)
    (hactive : 34 ≤ s.activeWords.toNat) :
    runInstrSeq Ordinary1.template (result0 s x rho) = some (result1 s x rho) := by
  have h := Ordinary1.run (result0 s x rho) (args1 s x rho) rho hstack hrun hactive
  rw [entry1] at h
  exact h
def args2 (s : State) (x : Nat → UInt256) (rho : List UInt256) (j : Nat) : UInt256 :=
  ((result1 s x rho).stack[j]?).getD 0
def result2 (s : State) (x : Nat → UInt256) (rho : List UInt256) : State :=
  {(result1 s x rho) with pc := (UInt256.ofNat 646), stack := Ordinary2.outputs (args2 s x rho) rho (result1 s x rho), memory := Ordinary2.memory (args2 s x rho) (result1 s x rho)}
theorem entry2 (s : State) (x : Nat → UInt256) (rho : List UInt256) :
    {(result1 s x rho) with pc := (UInt256.ofNat 621), stack := Ordinary2.inputs (args2 s x rho) rho} = (result1 s x rho) := by
  simp [args2, result1, Ordinary1.outputs, Ordinary2.inputs]
theorem step2 (s : State) (x : Nat → UInt256) (rho : List UInt256)
    (hstack : rho.length ≤ 900) (hrun : s.halt = .Running)
    (hactive : 34 ≤ s.activeWords.toNat) :
    runInstrSeq Ordinary2.template (result1 s x rho) = some (result2 s x rho) := by
  have h := Ordinary2.run (result1 s x rho) (args2 s x rho) rho hstack hrun hactive
  rw [entry2] at h
  exact h
def args3 (s : State) (x : Nat → UInt256) (rho : List UInt256) (j : Nat) : UInt256 :=
  ((result2 s x rho).stack[j]?).getD 0
def result3 (s : State) (x : Nat → UInt256) (rho : List UInt256) : State :=
  {(result2 s x rho) with pc := (UInt256.ofNat 680), stack := Ordinary3.outputs (args3 s x rho) rho (result2 s x rho), memory := Ordinary3.memory (args3 s x rho) (result2 s x rho)}
theorem entry3 (s : State) (x : Nat → UInt256) (rho : List UInt256) :
    {(result2 s x rho) with pc := (UInt256.ofNat 646), stack := Ordinary3.inputs (args3 s x rho) rho} = (result2 s x rho) := by
  simp [args3, result2, Ordinary2.outputs, Ordinary3.inputs]
theorem step3 (s : State) (x : Nat → UInt256) (rho : List UInt256)
    (hstack : rho.length ≤ 900) (hrun : s.halt = .Running)
    (hactive : 34 ≤ s.activeWords.toNat) :
    runInstrSeq Ordinary3.template (result2 s x rho) = some (result3 s x rho) := by
  have h := Ordinary3.run (result2 s x rho) (args3 s x rho) rho hstack hrun hactive
  rw [entry3] at h
  exact h
def args4 (s : State) (x : Nat → UInt256) (rho : List UInt256) (j : Nat) : UInt256 :=
  ((result3 s x rho).stack[j]?).getD 0
def result4 (s : State) (x : Nat → UInt256) (rho : List UInt256) : State :=
  {(result3 s x rho) with pc := (UInt256.ofNat 707), stack := Ordinary4.outputs (args4 s x rho) rho (result3 s x rho), memory := Ordinary4.memory (args4 s x rho) (result3 s x rho)}
theorem entry4 (s : State) (x : Nat → UInt256) (rho : List UInt256) :
    {(result3 s x rho) with pc := (UInt256.ofNat 680), stack := Ordinary4.inputs (args4 s x rho) rho} = (result3 s x rho) := by
  simp [args4, result3, Ordinary3.outputs, Ordinary4.inputs]
theorem step4 (s : State) (x : Nat → UInt256) (rho : List UInt256)
    (hstack : rho.length ≤ 900) (hrun : s.halt = .Running)
    (hactive : 34 ≤ s.activeWords.toNat) :
    runInstrSeq Ordinary4.template (result3 s x rho) = some (result4 s x rho) := by
  have h := Ordinary4.run (result3 s x rho) (args4 s x rho) rho hstack hrun hactive
  rw [entry4] at h
  exact h
def args5 (s : State) (x : Nat → UInt256) (rho : List UInt256) (j : Nat) : UInt256 :=
  ((result4 s x rho).stack[j]?).getD 0
def result5 (s : State) (x : Nat → UInt256) (rho : List UInt256) : State :=
  {(result4 s x rho) with pc := (UInt256.ofNat 735), stack := Ordinary5.outputs (args5 s x rho) rho (result4 s x rho), memory := Ordinary5.memory (args5 s x rho) (result4 s x rho)}
theorem entry5 (s : State) (x : Nat → UInt256) (rho : List UInt256) :
    {(result4 s x rho) with pc := (UInt256.ofNat 707), stack := Ordinary5.inputs (args5 s x rho) rho} = (result4 s x rho) := by
  simp [args5, result4, Ordinary4.outputs, Ordinary5.inputs]
theorem step5 (s : State) (x : Nat → UInt256) (rho : List UInt256)
    (hstack : rho.length ≤ 900) (hrun : s.halt = .Running)
    (hactive : 34 ≤ s.activeWords.toNat) :
    runInstrSeq Ordinary5.template (result4 s x rho) = some (result5 s x rho) := by
  have h := Ordinary5.run (result4 s x rho) (args5 s x rho) rho hstack hrun hactive
  rw [entry5] at h
  exact h
def args6 (s : State) (x : Nat → UInt256) (rho : List UInt256) (j : Nat) : UInt256 :=
  ((result5 s x rho).stack[j]?).getD 0
def result6 (s : State) (x : Nat → UInt256) (rho : List UInt256) : State :=
  {(result5 s x rho) with pc := (UInt256.ofNat 765), stack := Ordinary6.outputs (args6 s x rho) rho (result5 s x rho), memory := Ordinary6.memory (args6 s x rho) (result5 s x rho)}
theorem entry6 (s : State) (x : Nat → UInt256) (rho : List UInt256) :
    {(result5 s x rho) with pc := (UInt256.ofNat 735), stack := Ordinary6.inputs (args6 s x rho) rho} = (result5 s x rho) := by
  simp [args6, result5, Ordinary5.outputs, Ordinary6.inputs]
theorem step6 (s : State) (x : Nat → UInt256) (rho : List UInt256)
    (hstack : rho.length ≤ 900) (hrun : s.halt = .Running)
    (hactive : 34 ≤ s.activeWords.toNat) :
    runInstrSeq Ordinary6.template (result5 s x rho) = some (result6 s x rho) := by
  have h := Ordinary6.run (result5 s x rho) (args6 s x rho) rho hstack hrun hactive
  rw [entry6] at h
  exact h
def args7 (s : State) (x : Nat → UInt256) (rho : List UInt256) (j : Nat) : UInt256 :=
  ((result6 s x rho).stack[j]?).getD 0
def result7 (s : State) (x : Nat → UInt256) (rho : List UInt256) : State :=
  {(result6 s x rho) with pc := (UInt256.ofNat 794), stack := Ordinary7.outputs (args7 s x rho) rho (result6 s x rho), memory := Ordinary7.memory (args7 s x rho) (result6 s x rho)}
theorem entry7 (s : State) (x : Nat → UInt256) (rho : List UInt256) :
    {(result6 s x rho) with pc := (UInt256.ofNat 765), stack := Ordinary7.inputs (args7 s x rho) rho} = (result6 s x rho) := by
  simp [args7, result6, Ordinary6.outputs, Ordinary7.inputs]
theorem step7 (s : State) (x : Nat → UInt256) (rho : List UInt256)
    (hstack : rho.length ≤ 900) (hrun : s.halt = .Running)
    (hactive : 34 ≤ s.activeWords.toNat) :
    runInstrSeq Ordinary7.template (result6 s x rho) = some (result7 s x rho) := by
  have h := Ordinary7.run (result6 s x rho) (args7 s x rho) rho hstack hrun hactive
  rw [entry7] at h
  exact h
def template : List Instr := (((((((Ordinary0.template ++ Ordinary1.template) ++ Ordinary2.template) ++ Ordinary3.template) ++ Ordinary4.template) ++ Ordinary5.template) ++ Ordinary6.template) ++ Ordinary7.template)
theorem exact_bytes :
    (Challenge.Ripemd160.Benchmark.bytecode.data.toList.drop 530).take 264 =
      PcEncoding.assembleBytes template := by
  rw [CandidateBytes.exact_list]
  change (CandidateBytes.bytes.drop (512+18)).take 264 = _
  rw [← List.drop_drop, CandidateBytes.drop8]
  decide +kernel
theorem run (s : State) (x : Nat → UInt256) (rho : List UInt256)
    (hstack : rho.length ≤ 900) (hrun : s.halt = .Running)
    (hactive : 34 ≤ s.activeWords.toNat) :
    runInstrSeq template {s with pc := (UInt256.ofNat 530), stack := Ordinary0.inputs x rho} =
      some {s with pc := (UInt256.ofNat 794), stack := Ordinary0.inputs x rho, memory := (result7 s x rho).memory} := by
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
      {s with pc := (UInt256.ofNat 794), stack := Ordinary0.inputs x rho, memory := (result7 s x rho).memory} := by rfl
  rw [hfinal] at g7
  exact g7
#print axioms exact_bytes
#print axioms run
end OrdinaryTable
end RipemdSubmission20261101
