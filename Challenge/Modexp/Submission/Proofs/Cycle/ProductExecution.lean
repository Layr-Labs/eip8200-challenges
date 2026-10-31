import Challenge.Modexp.Submission.Proofs.Cycle.Meaning.Product0
import Challenge.Modexp.Submission.Proofs.Cycle.Meaning.Product1
import Challenge.Modexp.Submission.Proofs.Cycle.Meaning.Product2
import Challenge.Modexp.Submission.Proofs.Cycle.Meaning.Product3
import Challenge.Modexp.Submission.Proofs.Cycle.Meaning.Product4
import Challenge.Modexp.Submission.Proofs.Cycle.Meaning.Product5
import Challenge.Modexp.Submission.Proofs.Cycle.Meaning.Product6
import Challenge.Modexp.Submission.Proofs.Cycle.Meaning.Product7
import Challenge.Modexp.Submission.Proofs.Cycle.Meaning.Product8
import Challenge.Modexp.Submission.Proofs.Cycle.Meaning.Product9
import Challenge.Modexp.Submission.Proofs.Cycle.Meaning.Product10
import Challenge.Modexp.Submission.Proofs.Cycle.Meaning.Product11
import Challenge.Modexp.Submission.Proofs.Cycle.Meaning.Product12
import Challenge.Modexp.Submission.Proofs.Cycle.Meaning.Product13
import Challenge.Modexp.Submission.Proofs.Cycle.Meaning.Product14
import Challenge.Modexp.Submission.Proofs.Cycle.Meaning.Product15
import Challenge.Modexp.Submission.Proofs.Cycle.Meaning.Product16
import Challenge.Modexp.Submission.Proofs.Cycle.Meaning.Product17
import Challenge.Modexp.Submission.Proofs.Cycle.Meaning.Product18
import Challenge.Modexp.Submission.Proofs.Cycle.Meaning.Product19

import Challenge.Modexp.Submission.Proofs.Cycle.Artifact
set_option warningAsError true
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option maxRecDepth 50000
set_option maxHeartbeats 16000000
namespace CycleSubmission.ProductExecution
open EvmSemantics EvmSemantics.EVM YulEvmCompiler
open CycleSubmission.Execution CycleSubmission.ProductMeaning
open CycleSubmission.WordHistory CycleSubmission.WordArithmetic
open Challenge.Modexp.Submission.Proofs.Bytecode
open WindowNibbleKernel WindowTwentyOneBinding WindowTwentyOneSlice
open Challenge.EvmProof

theorem reset_self (s : State) (pc : UInt256) (stack : List UInt256)
    (hp : s.pc = pc) (hs : s.stack = stack) :
    {s with pc := pc, stack := stack} = s := by
  rw [← hp, ← hs]

def program : List Instr :=
  productColumn0Program ++ (productColumn1Program ++ (productColumn2Program ++ (productColumn3Program ++ (productColumn4Program ++ (productColumn5Program ++ (productColumn6Program ++ (productColumn7Program ++ (productColumn8Program ++ (productColumn9Program ++ (productColumn10Program ++ (productColumn11Program ++ (productColumn12Program ++ (productColumn13Program ++ (productColumn14Program ++ (productColumn15Program ++ (productColumn16Program ++ (productColumn17Program ++ (productColumn18Program ++ (productColumn19Program)))))))))))))))))))

def memory0 (mem : ByteArray) (inv : UInt256) (a b n : Nat → UInt256) : ByteArray := mem
def state0 (s : State) (inv : UInt256) (a b n : Nat → UInt256) (rest : List UInt256) : State := s
def memory1 (mem : ByteArray) (inv : UInt256) (a b n : Nat → UInt256) : ByteArray := HistoricalSearch.CRTMemoryCells.storeCells (memory0 mem inv a b n) (cells0 inv a b n)
def state1 (s : State) (inv : UInt256) (a b n : Nat → UInt256) (rest : List UInt256) : State := {s with pc := UInt256.ofNat 7872, memory := memory1 s.memory inv a b n, stack := frame1 inv a b n rest}
def memory2 (mem : ByteArray) (inv : UInt256) (a b n : Nat → UInt256) : ByteArray := HistoricalSearch.CRTMemoryCells.storeCells (memory1 mem inv a b n) (cells1 inv a b n)
def state2 (s : State) (inv : UInt256) (a b n : Nat → UInt256) (rest : List UInt256) : State := {s with pc := UInt256.ofNat 8002, memory := memory2 s.memory inv a b n, stack := frame2 inv a b n rest}
def memory3 (mem : ByteArray) (inv : UInt256) (a b n : Nat → UInt256) : ByteArray := HistoricalSearch.CRTMemoryCells.storeCells (memory2 mem inv a b n) (cells2 inv a b n)
def state3 (s : State) (inv : UInt256) (a b n : Nat → UInt256) (rest : List UInt256) : State := {s with pc := UInt256.ofNat 8130, memory := memory3 s.memory inv a b n, stack := frame3 inv a b n rest}
def memory4 (mem : ByteArray) (inv : UInt256) (a b n : Nat → UInt256) : ByteArray := HistoricalSearch.CRTMemoryCells.storeCells (memory3 mem inv a b n) (cells3 inv a b n)
def state4 (s : State) (inv : UInt256) (a b n : Nat → UInt256) (rest : List UInt256) : State := {s with pc := UInt256.ofNat 8258, memory := memory4 s.memory inv a b n, stack := frame4 inv a b n rest}
def memory5 (mem : ByteArray) (inv : UInt256) (a b n : Nat → UInt256) : ByteArray := HistoricalSearch.CRTMemoryCells.storeCells (memory4 mem inv a b n) (cells4 inv a b n)
def state5 (s : State) (inv : UInt256) (a b n : Nat → UInt256) (rest : List UInt256) : State := {s with pc := UInt256.ofNat 8386, memory := memory5 s.memory inv a b n, stack := frame5 inv a b n rest}
def memory6 (mem : ByteArray) (inv : UInt256) (a b n : Nat → UInt256) : ByteArray := HistoricalSearch.CRTMemoryCells.storeCells (memory5 mem inv a b n) (cells5 inv a b n)
def state6 (s : State) (inv : UInt256) (a b n : Nat → UInt256) (rest : List UInt256) : State := {s with pc := UInt256.ofNat 8514, memory := memory6 s.memory inv a b n, stack := frame6 inv a b n rest}
def memory7 (mem : ByteArray) (inv : UInt256) (a b n : Nat → UInt256) : ByteArray := HistoricalSearch.CRTMemoryCells.storeCells (memory6 mem inv a b n) (cells6 inv a b n)
def state7 (s : State) (inv : UInt256) (a b n : Nat → UInt256) (rest : List UInt256) : State := {s with pc := UInt256.ofNat 8642, memory := memory7 s.memory inv a b n, stack := frame7 inv a b n rest}
def memory8 (mem : ByteArray) (inv : UInt256) (a b n : Nat → UInt256) : ByteArray := HistoricalSearch.CRTMemoryCells.storeCells (memory7 mem inv a b n) (cells7 inv a b n)
def state8 (s : State) (inv : UInt256) (a b n : Nat → UInt256) (rest : List UInt256) : State := {s with pc := UInt256.ofNat 8770, memory := memory8 s.memory inv a b n, stack := frame8 inv a b n rest}
def memory9 (mem : ByteArray) (inv : UInt256) (a b n : Nat → UInt256) : ByteArray := HistoricalSearch.CRTMemoryCells.storeCells (memory8 mem inv a b n) (cells8 inv a b n)
def state9 (s : State) (inv : UInt256) (a b n : Nat → UInt256) (rest : List UInt256) : State := {s with pc := UInt256.ofNat 8898, memory := memory9 s.memory inv a b n, stack := frame9 inv a b n rest}
def memory10 (mem : ByteArray) (inv : UInt256) (a b n : Nat → UInt256) : ByteArray := HistoricalSearch.CRTMemoryCells.storeCells (memory9 mem inv a b n) (cells9 inv a b n)
def state10 (s : State) (inv : UInt256) (a b n : Nat → UInt256) (rest : List UInt256) : State := {s with pc := UInt256.ofNat 9026, memory := memory10 s.memory inv a b n, stack := frame10 inv a b n rest}
def memory11 (mem : ByteArray) (inv : UInt256) (a b n : Nat → UInt256) : ByteArray := HistoricalSearch.CRTMemoryCells.storeCells (memory10 mem inv a b n) (cells10 inv a b n)
def state11 (s : State) (inv : UInt256) (a b n : Nat → UInt256) (rest : List UInt256) : State := {s with pc := UInt256.ofNat 9156, memory := memory11 s.memory inv a b n, stack := frame11 inv a b n rest}
def memory12 (mem : ByteArray) (inv : UInt256) (a b n : Nat → UInt256) : ByteArray := HistoricalSearch.CRTMemoryCells.storeCells (memory11 mem inv a b n) (cells11 inv a b n)
def state12 (s : State) (inv : UInt256) (a b n : Nat → UInt256) (rest : List UInt256) : State := {s with pc := UInt256.ofNat 9284, memory := memory12 s.memory inv a b n, stack := frame12 inv a b n rest}
def memory13 (mem : ByteArray) (inv : UInt256) (a b n : Nat → UInt256) : ByteArray := HistoricalSearch.CRTMemoryCells.storeCells (memory12 mem inv a b n) (cells12 inv a b n)
def state13 (s : State) (inv : UInt256) (a b n : Nat → UInt256) (rest : List UInt256) : State := {s with pc := UInt256.ofNat 9412, memory := memory13 s.memory inv a b n, stack := frame13 inv a b n rest}
def memory14 (mem : ByteArray) (inv : UInt256) (a b n : Nat → UInt256) : ByteArray := HistoricalSearch.CRTMemoryCells.storeCells (memory13 mem inv a b n) (cells13 inv a b n)
def state14 (s : State) (inv : UInt256) (a b n : Nat → UInt256) (rest : List UInt256) : State := {s with pc := UInt256.ofNat 9540, memory := memory14 s.memory inv a b n, stack := frame14 inv a b n rest}
def memory15 (mem : ByteArray) (inv : UInt256) (a b n : Nat → UInt256) : ByteArray := HistoricalSearch.CRTMemoryCells.storeCells (memory14 mem inv a b n) (cells14 inv a b n)
def state15 (s : State) (inv : UInt256) (a b n : Nat → UInt256) (rest : List UInt256) : State := {s with pc := UInt256.ofNat 9668, memory := memory15 s.memory inv a b n, stack := frame15 inv a b n rest}
def memory16 (mem : ByteArray) (inv : UInt256) (a b n : Nat → UInt256) : ByteArray := HistoricalSearch.CRTMemoryCells.storeCells (memory15 mem inv a b n) (cells15 inv a b n)
def state16 (s : State) (inv : UInt256) (a b n : Nat → UInt256) (rest : List UInt256) : State := {s with pc := UInt256.ofNat 9796, memory := memory16 s.memory inv a b n, stack := frame16 inv a b n rest}
def memory17 (mem : ByteArray) (inv : UInt256) (a b n : Nat → UInt256) : ByteArray := HistoricalSearch.CRTMemoryCells.storeCells (memory16 mem inv a b n) (cells16 inv a b n)
def state17 (s : State) (inv : UInt256) (a b n : Nat → UInt256) (rest : List UInt256) : State := {s with pc := UInt256.ofNat 9924, memory := memory17 s.memory inv a b n, stack := frame17 inv a b n rest}
def memory18 (mem : ByteArray) (inv : UInt256) (a b n : Nat → UInt256) : ByteArray := HistoricalSearch.CRTMemoryCells.storeCells (memory17 mem inv a b n) (cells17 inv a b n)
def state18 (s : State) (inv : UInt256) (a b n : Nat → UInt256) (rest : List UInt256) : State := {s with pc := UInt256.ofNat 10052, memory := memory18 s.memory inv a b n, stack := frame18 inv a b n rest}
def memory19 (mem : ByteArray) (inv : UInt256) (a b n : Nat → UInt256) : ByteArray := HistoricalSearch.CRTMemoryCells.storeCells (memory18 mem inv a b n) (cells18 inv a b n)
def state19 (s : State) (inv : UInt256) (a b n : Nat → UInt256) (rest : List UInt256) : State := {s with pc := UInt256.ofNat 10180, memory := memory19 s.memory inv a b n, stack := frame19 inv a b n rest}
def memory20 (mem : ByteArray) (inv : UInt256) (a b n : Nat → UInt256) : ByteArray := HistoricalSearch.CRTMemoryCells.storeCells (memory19 mem inv a b n) (cells19 inv a b n)
def state20 (s : State) (inv : UInt256) (a b n : Nat → UInt256) (rest : List UInt256) : State := {s with pc := UInt256.ofNat 10234, memory := memory20 s.memory inv a b n, stack := frame20 inv a b n rest}
theorem memory0_keeps (mem : ByteArray) (inv : UInt256) (a b n : Nat → UInt256)
    (start count : Nat) (hs : (256 ≤ start ∧ start+count ≤ 768) ∨ 1312 ≤ start) :
    MachineState.readPadded (memory0 mem inv a b n) start count =
      MachineState.readPadded mem start count := by
  rfl

theorem memory1_keeps (mem : ByteArray) (inv : UInt256) (a b n : Nat → UInt256)
    (start count : Nat) (hs : (256 ≤ start ∧ start+count ≤ 768) ∨ 1312 ≤ start) :
    MachineState.readPadded (memory1 mem inv a b n) start count =
      MachineState.readPadded mem start count := by
  have h := HistoricalSearch.CRTMemoryCells.readPadded_storeCells
    (memory0 mem inv a b n) (cells0 inv a b n) start count (by
      intro c hc
      simp only [cells0, List.mem_cons, List.mem_nil_iff, or_false] at hc
      )
  exact h.trans (memory0_keeps mem inv a b n start count hs)

theorem memory2_keeps (mem : ByteArray) (inv : UInt256) (a b n : Nat → UInt256)
    (start count : Nat) (hs : (256 ≤ start ∧ start+count ≤ 768) ∨ 1312 ≤ start) :
    MachineState.readPadded (memory2 mem inv a b n) start count =
      MachineState.readPadded mem start count := by
  have h := HistoricalSearch.CRTMemoryCells.readPadded_storeCells
    (memory1 mem inv a b n) (cells1 inv a b n) start count (by
      intro c hc
      simp only [cells1, List.mem_cons, List.mem_nil_iff, or_false] at hc
      rcases hc with rfl
      all_goals (dsimp; omega))
  exact h.trans (memory1_keeps mem inv a b n start count hs)

theorem memory3_keeps (mem : ByteArray) (inv : UInt256) (a b n : Nat → UInt256)
    (start count : Nat) (hs : (256 ≤ start ∧ start+count ≤ 768) ∨ 1312 ≤ start) :
    MachineState.readPadded (memory3 mem inv a b n) start count =
      MachineState.readPadded mem start count := by
  have h := HistoricalSearch.CRTMemoryCells.readPadded_storeCells
    (memory2 mem inv a b n) (cells2 inv a b n) start count (by
      intro c hc
      simp only [cells2, List.mem_cons, List.mem_nil_iff, or_false] at hc
      rcases hc with rfl
      all_goals (dsimp; omega))
  exact h.trans (memory2_keeps mem inv a b n start count hs)

theorem memory4_keeps (mem : ByteArray) (inv : UInt256) (a b n : Nat → UInt256)
    (start count : Nat) (hs : (256 ≤ start ∧ start+count ≤ 768) ∨ 1312 ≤ start) :
    MachineState.readPadded (memory4 mem inv a b n) start count =
      MachineState.readPadded mem start count := by
  have h := HistoricalSearch.CRTMemoryCells.readPadded_storeCells
    (memory3 mem inv a b n) (cells3 inv a b n) start count (by
      intro c hc
      simp only [cells3, List.mem_cons, List.mem_nil_iff, or_false] at hc
      rcases hc with rfl
      all_goals (dsimp; omega))
  exact h.trans (memory3_keeps mem inv a b n start count hs)

theorem memory5_keeps (mem : ByteArray) (inv : UInt256) (a b n : Nat → UInt256)
    (start count : Nat) (hs : (256 ≤ start ∧ start+count ≤ 768) ∨ 1312 ≤ start) :
    MachineState.readPadded (memory5 mem inv a b n) start count =
      MachineState.readPadded mem start count := by
  have h := HistoricalSearch.CRTMemoryCells.readPadded_storeCells
    (memory4 mem inv a b n) (cells4 inv a b n) start count (by
      intro c hc
      simp only [cells4, List.mem_cons, List.mem_nil_iff, or_false] at hc
      rcases hc with rfl
      all_goals (dsimp; omega))
  exact h.trans (memory4_keeps mem inv a b n start count hs)

theorem memory6_keeps (mem : ByteArray) (inv : UInt256) (a b n : Nat → UInt256)
    (start count : Nat) (hs : (256 ≤ start ∧ start+count ≤ 768) ∨ 1312 ≤ start) :
    MachineState.readPadded (memory6 mem inv a b n) start count =
      MachineState.readPadded mem start count := by
  have h := HistoricalSearch.CRTMemoryCells.readPadded_storeCells
    (memory5 mem inv a b n) (cells5 inv a b n) start count (by
      intro c hc
      simp only [cells5, List.mem_cons, List.mem_nil_iff, or_false] at hc
      )
  exact h.trans (memory5_keeps mem inv a b n start count hs)

theorem memory7_keeps (mem : ByteArray) (inv : UInt256) (a b n : Nat → UInt256)
    (start count : Nat) (hs : (256 ≤ start ∧ start+count ≤ 768) ∨ 1312 ≤ start) :
    MachineState.readPadded (memory7 mem inv a b n) start count =
      MachineState.readPadded mem start count := by
  have h := HistoricalSearch.CRTMemoryCells.readPadded_storeCells
    (memory6 mem inv a b n) (cells6 inv a b n) start count (by
      intro c hc
      simp only [cells6, List.mem_cons, List.mem_nil_iff, or_false] at hc
      rcases hc with rfl
      all_goals (dsimp; omega))
  exact h.trans (memory6_keeps mem inv a b n start count hs)

theorem memory8_keeps (mem : ByteArray) (inv : UInt256) (a b n : Nat → UInt256)
    (start count : Nat) (hs : (256 ≤ start ∧ start+count ≤ 768) ∨ 1312 ≤ start) :
    MachineState.readPadded (memory8 mem inv a b n) start count =
      MachineState.readPadded mem start count := by
  have h := HistoricalSearch.CRTMemoryCells.readPadded_storeCells
    (memory7 mem inv a b n) (cells7 inv a b n) start count (by
      intro c hc
      simp only [cells7, List.mem_cons, List.mem_nil_iff, or_false] at hc
      rcases hc with rfl
      all_goals (dsimp; omega))
  exact h.trans (memory7_keeps mem inv a b n start count hs)

theorem memory9_keeps (mem : ByteArray) (inv : UInt256) (a b n : Nat → UInt256)
    (start count : Nat) (hs : (256 ≤ start ∧ start+count ≤ 768) ∨ 1312 ≤ start) :
    MachineState.readPadded (memory9 mem inv a b n) start count =
      MachineState.readPadded mem start count := by
  have h := HistoricalSearch.CRTMemoryCells.readPadded_storeCells
    (memory8 mem inv a b n) (cells8 inv a b n) start count (by
      intro c hc
      simp only [cells8, List.mem_cons, List.mem_nil_iff, or_false] at hc
      rcases hc with rfl
      all_goals (dsimp; omega))
  exact h.trans (memory8_keeps mem inv a b n start count hs)

theorem memory10_keeps (mem : ByteArray) (inv : UInt256) (a b n : Nat → UInt256)
    (start count : Nat) (hs : (256 ≤ start ∧ start+count ≤ 768) ∨ 1312 ≤ start) :
    MachineState.readPadded (memory10 mem inv a b n) start count =
      MachineState.readPadded mem start count := by
  have h := HistoricalSearch.CRTMemoryCells.readPadded_storeCells
    (memory9 mem inv a b n) (cells9 inv a b n) start count (by
      intro c hc
      simp only [cells9, List.mem_cons, List.mem_nil_iff, or_false] at hc
      )
  exact h.trans (memory9_keeps mem inv a b n start count hs)

theorem memory11_keeps (mem : ByteArray) (inv : UInt256) (a b n : Nat → UInt256)
    (start count : Nat) (hs : (256 ≤ start ∧ start+count ≤ 768) ∨ 1312 ≤ start) :
    MachineState.readPadded (memory11 mem inv a b n) start count =
      MachineState.readPadded mem start count := by
  have h := HistoricalSearch.CRTMemoryCells.readPadded_storeCells
    (memory10 mem inv a b n) (cells10 inv a b n) start count (by
      intro c hc
      simp only [cells10, List.mem_cons, List.mem_nil_iff, or_false] at hc
      )
  exact h.trans (memory10_keeps mem inv a b n start count hs)

theorem memory12_keeps (mem : ByteArray) (inv : UInt256) (a b n : Nat → UInt256)
    (start count : Nat) (hs : (256 ≤ start ∧ start+count ≤ 768) ∨ 1312 ≤ start) :
    MachineState.readPadded (memory12 mem inv a b n) start count =
      MachineState.readPadded mem start count := by
  have h := HistoricalSearch.CRTMemoryCells.readPadded_storeCells
    (memory11 mem inv a b n) (cells11 inv a b n) start count (by
      intro c hc
      simp only [cells11, List.mem_cons, List.mem_nil_iff, or_false] at hc
      )
  exact h.trans (memory11_keeps mem inv a b n start count hs)

theorem memory13_keeps (mem : ByteArray) (inv : UInt256) (a b n : Nat → UInt256)
    (start count : Nat) (hs : (256 ≤ start ∧ start+count ≤ 768) ∨ 1312 ≤ start) :
    MachineState.readPadded (memory13 mem inv a b n) start count =
      MachineState.readPadded mem start count := by
  have h := HistoricalSearch.CRTMemoryCells.readPadded_storeCells
    (memory12 mem inv a b n) (cells12 inv a b n) start count (by
      intro c hc
      simp only [cells12, List.mem_cons, List.mem_nil_iff, or_false] at hc
      rcases hc with rfl
      all_goals (dsimp; omega))
  exact h.trans (memory12_keeps mem inv a b n start count hs)

theorem memory14_keeps (mem : ByteArray) (inv : UInt256) (a b n : Nat → UInt256)
    (start count : Nat) (hs : (256 ≤ start ∧ start+count ≤ 768) ∨ 1312 ≤ start) :
    MachineState.readPadded (memory14 mem inv a b n) start count =
      MachineState.readPadded mem start count := by
  have h := HistoricalSearch.CRTMemoryCells.readPadded_storeCells
    (memory13 mem inv a b n) (cells13 inv a b n) start count (by
      intro c hc
      simp only [cells13, List.mem_cons, List.mem_nil_iff, or_false] at hc
      )
  exact h.trans (memory13_keeps mem inv a b n start count hs)

theorem memory15_keeps (mem : ByteArray) (inv : UInt256) (a b n : Nat → UInt256)
    (start count : Nat) (hs : (256 ≤ start ∧ start+count ≤ 768) ∨ 1312 ≤ start) :
    MachineState.readPadded (memory15 mem inv a b n) start count =
      MachineState.readPadded mem start count := by
  have h := HistoricalSearch.CRTMemoryCells.readPadded_storeCells
    (memory14 mem inv a b n) (cells14 inv a b n) start count (by
      intro c hc
      simp only [cells14, List.mem_cons, List.mem_nil_iff, or_false] at hc
      rcases hc with rfl
      all_goals (dsimp; omega))
  exact h.trans (memory14_keeps mem inv a b n start count hs)

theorem memory16_keeps (mem : ByteArray) (inv : UInt256) (a b n : Nat → UInt256)
    (start count : Nat) (hs : (256 ≤ start ∧ start+count ≤ 768) ∨ 1312 ≤ start) :
    MachineState.readPadded (memory16 mem inv a b n) start count =
      MachineState.readPadded mem start count := by
  have h := HistoricalSearch.CRTMemoryCells.readPadded_storeCells
    (memory15 mem inv a b n) (cells15 inv a b n) start count (by
      intro c hc
      simp only [cells15, List.mem_cons, List.mem_nil_iff, or_false] at hc
      rcases hc with rfl
      all_goals (dsimp; omega))
  exact h.trans (memory15_keeps mem inv a b n start count hs)

theorem memory17_keeps (mem : ByteArray) (inv : UInt256) (a b n : Nat → UInt256)
    (start count : Nat) (hs : (256 ≤ start ∧ start+count ≤ 768) ∨ 1312 ≤ start) :
    MachineState.readPadded (memory17 mem inv a b n) start count =
      MachineState.readPadded mem start count := by
  have h := HistoricalSearch.CRTMemoryCells.readPadded_storeCells
    (memory16 mem inv a b n) (cells16 inv a b n) start count (by
      intro c hc
      simp only [cells16, List.mem_cons, List.mem_nil_iff, or_false] at hc
      rcases hc with rfl
      all_goals (dsimp; omega))
  exact h.trans (memory16_keeps mem inv a b n start count hs)

theorem memory18_keeps (mem : ByteArray) (inv : UInt256) (a b n : Nat → UInt256)
    (start count : Nat) (hs : (256 ≤ start ∧ start+count ≤ 768) ∨ 1312 ≤ start) :
    MachineState.readPadded (memory18 mem inv a b n) start count =
      MachineState.readPadded mem start count := by
  have h := HistoricalSearch.CRTMemoryCells.readPadded_storeCells
    (memory17 mem inv a b n) (cells17 inv a b n) start count (by
      intro c hc
      simp only [cells17, List.mem_cons, List.mem_nil_iff, or_false] at hc
      rcases hc with rfl
      all_goals (dsimp; omega))
  exact h.trans (memory17_keeps mem inv a b n start count hs)

theorem memory19_keeps (mem : ByteArray) (inv : UInt256) (a b n : Nat → UInt256)
    (start count : Nat) (hs : (256 ≤ start ∧ start+count ≤ 768) ∨ 1312 ≤ start) :
    MachineState.readPadded (memory19 mem inv a b n) start count =
      MachineState.readPadded mem start count := by
  have h := HistoricalSearch.CRTMemoryCells.readPadded_storeCells
    (memory18 mem inv a b n) (cells18 inv a b n) start count (by
      intro c hc
      simp only [cells18, List.mem_cons, List.mem_nil_iff, or_false] at hc
      rcases hc with rfl | rfl
      all_goals (dsimp; omega))
  exact h.trans (memory18_keeps mem inv a b n start count hs)

theorem memory20_keeps (mem : ByteArray) (inv : UInt256) (a b n : Nat → UInt256)
    (start count : Nat) (hs : (256 ≤ start ∧ start+count ≤ 768) ∨ 1312 ≤ start) :
    MachineState.readPadded (memory20 mem inv a b n) start count =
      MachineState.readPadded mem start count := by
  have h := HistoricalSearch.CRTMemoryCells.readPadded_storeCells
    (memory19 mem inv a b n) (cells19 inv a b n) start count (by
      intro c hc
      simp only [cells19, List.mem_cons, List.mem_nil_iff, or_false] at hc
      rcases hc with rfl
      all_goals (dsimp; omega))
  exact h.trans (memory19_keeps mem inv a b n start count hs)

theorem run (s : State) (inv : UInt256) (a b n : Nat → UInt256) (rest : List UInt256)
    (h : Memory0 s.memory inv a b n) (hcap : rest.length ≤ 960)
    (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions program
      {s with pc := UInt256.ofNat 7744, stack := frame0 inv a b n rest} =
      some (state20 s inv a b n rest) := by
  have m0 := h

  have m1 := memory0_output (state0 s inv a b n rest) inv a b n rest m0
  have h0 : runInstructions productColumn0Program {s with pc := UInt256.ofNat 7744, stack := frame0 inv a b n rest} = some (state1 s inv a b n rest) :=
    run0 (state0 s inv a b n rest) inv a b n rest m0 hcap hact
  have m2 := memory1_output (state1 s inv a b n rest) inv a b n rest m1
  have h1 : runInstructions productColumn1Program (state1 s inv a b n rest) = some (state2 s inv a b n rest) := by
    have hx := run1 (state1 s inv a b n rest) inv a b n rest m1 hcap hact
    rw [reset_self (state1 s inv a b n rest) (UInt256.ofNat 7872) (frame1 inv a b n rest) rfl rfl] at hx
    exact hx
  have m3 := memory2_output (state2 s inv a b n rest) inv a b n rest m2
  have h2 : runInstructions productColumn2Program (state2 s inv a b n rest) = some (state3 s inv a b n rest) := by
    have hx := run2 (state2 s inv a b n rest) inv a b n rest m2 hcap hact
    rw [reset_self (state2 s inv a b n rest) (UInt256.ofNat 8002) (frame2 inv a b n rest) rfl rfl] at hx
    exact hx
  have m4 := memory3_output (state3 s inv a b n rest) inv a b n rest m3
  have h3 : runInstructions productColumn3Program (state3 s inv a b n rest) = some (state4 s inv a b n rest) := by
    have hx := run3 (state3 s inv a b n rest) inv a b n rest m3 hcap hact
    rw [reset_self (state3 s inv a b n rest) (UInt256.ofNat 8130) (frame3 inv a b n rest) rfl rfl] at hx
    exact hx
  have m5 := memory4_output (state4 s inv a b n rest) inv a b n rest m4
  have h4 : runInstructions productColumn4Program (state4 s inv a b n rest) = some (state5 s inv a b n rest) := by
    have hx := run4 (state4 s inv a b n rest) inv a b n rest m4 hcap hact
    rw [reset_self (state4 s inv a b n rest) (UInt256.ofNat 8258) (frame4 inv a b n rest) rfl rfl] at hx
    exact hx
  have m6 := memory5_output (state5 s inv a b n rest) inv a b n rest m5
  have h5 : runInstructions productColumn5Program (state5 s inv a b n rest) = some (state6 s inv a b n rest) := by
    have hx := run5 (state5 s inv a b n rest) inv a b n rest m5 hcap hact
    rw [reset_self (state5 s inv a b n rest) (UInt256.ofNat 8386) (frame5 inv a b n rest) rfl rfl] at hx
    exact hx
  have m7 := memory6_output (state6 s inv a b n rest) inv a b n rest m6
  have h6 : runInstructions productColumn6Program (state6 s inv a b n rest) = some (state7 s inv a b n rest) := by
    have hx := run6 (state6 s inv a b n rest) inv a b n rest m6 hcap hact
    rw [reset_self (state6 s inv a b n rest) (UInt256.ofNat 8514) (frame6 inv a b n rest) rfl rfl] at hx
    exact hx
  have m8 := memory7_output (state7 s inv a b n rest) inv a b n rest m7
  have h7 : runInstructions productColumn7Program (state7 s inv a b n rest) = some (state8 s inv a b n rest) := by
    have hx := run7 (state7 s inv a b n rest) inv a b n rest m7 hcap hact
    rw [reset_self (state7 s inv a b n rest) (UInt256.ofNat 8642) (frame7 inv a b n rest) rfl rfl] at hx
    exact hx
  have m9 := memory8_output (state8 s inv a b n rest) inv a b n rest m8
  have h8 : runInstructions productColumn8Program (state8 s inv a b n rest) = some (state9 s inv a b n rest) := by
    have hx := run8 (state8 s inv a b n rest) inv a b n rest m8 hcap hact
    rw [reset_self (state8 s inv a b n rest) (UInt256.ofNat 8770) (frame8 inv a b n rest) rfl rfl] at hx
    exact hx
  have m10 := memory9_output (state9 s inv a b n rest) inv a b n rest m9
  have h9 : runInstructions productColumn9Program (state9 s inv a b n rest) = some (state10 s inv a b n rest) := by
    have hx := run9 (state9 s inv a b n rest) inv a b n rest m9 hcap hact
    rw [reset_self (state9 s inv a b n rest) (UInt256.ofNat 8898) (frame9 inv a b n rest) rfl rfl] at hx
    exact hx
  have m11 := memory10_output (state10 s inv a b n rest) inv a b n rest m10
  have h10 : runInstructions productColumn10Program (state10 s inv a b n rest) = some (state11 s inv a b n rest) := by
    have hx := run10 (state10 s inv a b n rest) inv a b n rest m10 hcap hact
    rw [reset_self (state10 s inv a b n rest) (UInt256.ofNat 9026) (frame10 inv a b n rest) rfl rfl] at hx
    exact hx
  have m12 := memory11_output (state11 s inv a b n rest) inv a b n rest m11
  have h11 : runInstructions productColumn11Program (state11 s inv a b n rest) = some (state12 s inv a b n rest) := by
    have hx := run11 (state11 s inv a b n rest) inv a b n rest m11 hcap hact
    rw [reset_self (state11 s inv a b n rest) (UInt256.ofNat 9156) (frame11 inv a b n rest) rfl rfl] at hx
    exact hx
  have m13 := memory12_output (state12 s inv a b n rest) inv a b n rest m12
  have h12 : runInstructions productColumn12Program (state12 s inv a b n rest) = some (state13 s inv a b n rest) := by
    have hx := run12 (state12 s inv a b n rest) inv a b n rest m12 hcap hact
    rw [reset_self (state12 s inv a b n rest) (UInt256.ofNat 9284) (frame12 inv a b n rest) rfl rfl] at hx
    exact hx
  have m14 := memory13_output (state13 s inv a b n rest) inv a b n rest m13
  have h13 : runInstructions productColumn13Program (state13 s inv a b n rest) = some (state14 s inv a b n rest) := by
    have hx := run13 (state13 s inv a b n rest) inv a b n rest m13 hcap hact
    rw [reset_self (state13 s inv a b n rest) (UInt256.ofNat 9412) (frame13 inv a b n rest) rfl rfl] at hx
    exact hx
  have m15 := memory14_output (state14 s inv a b n rest) inv a b n rest m14
  have h14 : runInstructions productColumn14Program (state14 s inv a b n rest) = some (state15 s inv a b n rest) := by
    have hx := run14 (state14 s inv a b n rest) inv a b n rest m14 hcap hact
    rw [reset_self (state14 s inv a b n rest) (UInt256.ofNat 9540) (frame14 inv a b n rest) rfl rfl] at hx
    exact hx
  have m16 := memory15_output (state15 s inv a b n rest) inv a b n rest m15
  have h15 : runInstructions productColumn15Program (state15 s inv a b n rest) = some (state16 s inv a b n rest) := by
    have hx := run15 (state15 s inv a b n rest) inv a b n rest m15 hcap hact
    rw [reset_self (state15 s inv a b n rest) (UInt256.ofNat 9668) (frame15 inv a b n rest) rfl rfl] at hx
    exact hx
  have m17 := memory16_output (state16 s inv a b n rest) inv a b n rest m16
  have h16 : runInstructions productColumn16Program (state16 s inv a b n rest) = some (state17 s inv a b n rest) := by
    have hx := run16 (state16 s inv a b n rest) inv a b n rest m16 hcap hact
    rw [reset_self (state16 s inv a b n rest) (UInt256.ofNat 9796) (frame16 inv a b n rest) rfl rfl] at hx
    exact hx
  have m18 := memory17_output (state17 s inv a b n rest) inv a b n rest m17
  have h17 : runInstructions productColumn17Program (state17 s inv a b n rest) = some (state18 s inv a b n rest) := by
    have hx := run17 (state17 s inv a b n rest) inv a b n rest m17 hcap hact
    rw [reset_self (state17 s inv a b n rest) (UInt256.ofNat 9924) (frame17 inv a b n rest) rfl rfl] at hx
    exact hx
  have m19 := memory18_output (state18 s inv a b n rest) inv a b n rest m18
  have h18 : runInstructions productColumn18Program (state18 s inv a b n rest) = some (state19 s inv a b n rest) := by
    have hx := run18 (state18 s inv a b n rest) inv a b n rest m18 hcap hact
    rw [reset_self (state18 s inv a b n rest) (UInt256.ofNat 10052) (frame18 inv a b n rest) rfl rfl] at hx
    exact hx
  have m20 := memory19_output (state19 s inv a b n rest) inv a b n rest m19
  have h19 : runInstructions productColumn19Program (state19 s inv a b n rest) = some (state20 s inv a b n rest) := by
    have hx := run19 (state19 s inv a b n rest) inv a b n rest m19 hcap hact
    rw [reset_self (state19 s inv a b n rest) (UInt256.ofNat 10180) (frame19 inv a b n rest) rfl rfl] at hx
    exact hx
  exact (runInstructions_append_some _ _ _ _ _ h0 (runInstructions_append_some _ _ _ _ _ h1 (runInstructions_append_some _ _ _ _ _ h2 (runInstructions_append_some _ _ _ _ _ h3 (runInstructions_append_some _ _ _ _ _ h4 (runInstructions_append_some _ _ _ _ _ h5 (runInstructions_append_some _ _ _ _ _ h6 (runInstructions_append_some _ _ _ _ _ h7 (runInstructions_append_some _ _ _ _ _ h8 (runInstructions_append_some _ _ _ _ _ h9 (runInstructions_append_some _ _ _ _ _ h10 (runInstructions_append_some _ _ _ _ _ h11 (runInstructions_append_some _ _ _ _ _ h12 (runInstructions_append_some _ _ _ _ _ h13 (runInstructions_append_some _ _ _ _ _ h14 (runInstructions_append_some _ _ _ _ _ h15 (runInstructions_append_some _ _ _ _ _ h16 (runInstructions_append_some _ _ _ _ _ h17 (runInstructions_append_some _ _ _ _ _ h18 h19)))))))))))))))))))

theorem memory_output (s : State) (inv : UInt256) (a b n : Nat → UInt256) (rest : List UInt256) (h : Memory0 s.memory inv a b n) :
    Memory20 (state20 s inv a b n rest).memory inv a b n := by
  have m0 := h
  have m1 := memory0_output (state0 s inv a b n rest) inv a b n rest m0
  have m2 := memory1_output (state1 s inv a b n rest) inv a b n rest m1
  have m3 := memory2_output (state2 s inv a b n rest) inv a b n rest m2
  have m4 := memory3_output (state3 s inv a b n rest) inv a b n rest m3
  have m5 := memory4_output (state4 s inv a b n rest) inv a b n rest m4
  have m6 := memory5_output (state5 s inv a b n rest) inv a b n rest m5
  have m7 := memory6_output (state6 s inv a b n rest) inv a b n rest m6
  have m8 := memory7_output (state7 s inv a b n rest) inv a b n rest m7
  have m9 := memory8_output (state8 s inv a b n rest) inv a b n rest m8
  have m10 := memory9_output (state9 s inv a b n rest) inv a b n rest m9
  have m11 := memory10_output (state10 s inv a b n rest) inv a b n rest m10
  have m12 := memory11_output (state11 s inv a b n rest) inv a b n rest m11
  have m13 := memory12_output (state12 s inv a b n rest) inv a b n rest m12
  have m14 := memory13_output (state13 s inv a b n rest) inv a b n rest m13
  have m15 := memory14_output (state14 s inv a b n rest) inv a b n rest m14
  have m16 := memory15_output (state15 s inv a b n rest) inv a b n rest m15
  have m17 := memory16_output (state16 s inv a b n rest) inv a b n rest m16
  have m18 := memory17_output (state17 s inv a b n rest) inv a b n rest m17
  have m19 := memory18_output (state18 s inv a b n rest) inv a b n rest m18
  have m20 := memory19_output (state19 s inv a b n rest) inv a b n rest m19
  exact m20

theorem normalizer_input (s : State) (inv : UInt256) (a b n : Nat → UInt256) (rest : List UInt256)
    (h : Memory0 s.memory inv a b n) :
    CycleSubmission.NormalizeMeaning.MemoryInput (state20 s inv a b n rest).memory
      (productd inv a b n) n := by
  have m := memory_output s inv a b n rest h
  exact ⟨m.at768, m.at32, m.at64, m.at96, m.at128, m.at160, m.at1344, m.at1376⟩

theorem output_frame (s : State) (inv : UInt256) (a b n : Nat → UInt256) (rest : List UInt256) :
    (state20 s inv a b n rest).stack = CycleSubmission.NormalizeMeaning.frame
      (productd inv a b n) n
      (productQ8 inv a b n)
      (productQ7 inv a b n) rest := rfl

def outputWord (s : State) : Nat → UInt256
  | 0 => MachineState.readWord s.memory 768
  | 1 => s.stack[3]?.getD (UInt256.ofNat 0)
  | 2 => s.stack[4]?.getD (UInt256.ofNat 0)
  | 3 => MachineState.readWord s.memory 32
  | 4 => MachineState.readWord s.memory 64
  | 5 => MachineState.readWord s.memory 96
  | 6 => MachineState.readWord s.memory 128
  | 7 => MachineState.readWord s.memory 160
  | 8 => s.stack[13]?.getD (UInt256.ofNat 0)
  | _ => UInt256.ofNat 0

theorem output_eq (s : State) (inv : UInt256) (a b n : Nat → UInt256) (rest : List UInt256)
    (h : Memory0 s.memory inv a b n) (i : Nat) (hi : i < 9) :
    outputWord (state20 s inv a b n rest) i = productd inv a b n i := by
  have m := memory_output s inv a b n rest h
  interval_cases i
  · exact m.at768
  · rfl
  · rfl
  · exact m.at32
  · exact m.at64
  · exact m.at96
  · exact m.at128
  · exact m.at160
  · rfl

theorem output_value (s : State) (inv : UInt256) (a b n : Nat → UInt256) (rest : List UInt256)
    (h : Memory0 s.memory inv a b n) :
    HistoricalSearch.MixedMontgomery.weighted radix 9
      (fun i => (outputWord (state20 s inv a b n rest) i).toNat) =
    HistoricalSearch.MixedMontgomery.weighted radix 9
      (fun i => (productd inv a b n i).toNat) := by
  apply Finset.sum_congr rfl
  intro i hi
  dsimp only
  rw [output_eq s inv a b n rest h i (Finset.mem_range.mp hi)]

def block : Block Artifact.artifact .Osaka 7744 program :=
  WindowTwentyOneSlice.block Artifact.wellFormed 6108 2098 7744 program
    (by change 6108+2098 ≤ Artifact.instructions.length
        exact Nat.le_trans (by decide : 6108+2098 ≤ 8730)
          (Nat.le_of_eq Artifact.instructionCount.symm))
    (by rw [PCFast.instructionPC_eq_byteLength]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)

noncomputable def gasSteps (s : State) (inv : UInt256) (a b n : Nat → UInt256) (rest : List UInt256)
    (env : Environment Artifact.artifact .Osaka s)
    (h : Memory0 s.memory inv a b n) (hcap : rest.length ≤ 960)
    (hact : 88 ≤ s.activeWords.toNat) :
    GasSteps {s with pc := UInt256.ofNat 7744, stack := frame0 inv a b n rest}
      (state20 s inv a b n rest) :=
  block.steps
    (s := {s with pc := UInt256.ofNat 7744, stack := frame0 inv a b n rest})
    (env.transfer rfl rfl) rfl (run s inv a b n rest h hcap hact)

noncomputable def correct (s : State) (inv : UInt256) (a b n : Nat → UInt256) (rest : List UInt256)
    (env : Environment Artifact.artifact .Osaka s)
    (h : Memory0 s.memory inv a b n) (hcap : rest.length ≤ 960)
    (hact : 88 ≤ s.activeWords.toNat)
    (ha : ∀ i < 9, (a i).toNat < radix)
    (hb : ∀ i < 9, (b i).toNat < radix)
    (hn : ∀ i < 9, (n i).toNat < radix)
    (N : Nat) (hn0 : (n 0).toNat = N % radix)
    (hinv : (N*inv.toNat+1) % 2^256 = 0) :
    PSigma (fun _ : GasSteps
      {s with pc := UInt256.ofNat 7744, stack := frame0 inv a b n rest}
      (state20 s inv a b n rest) =>
    HistoricalSearch.MixedMontgomery.weighted radix 9
      (fun i => (outputWord (state20 s inv a b n rest) i).toNat) * radix^9 =
    HistoricalSearch.MixedMontgomery.weighted radix 9 (fun i => (a i).toNat) *
    HistoricalSearch.MixedMontgomery.weighted radix 9 (fun i => (b i).toNat) +
    HistoricalSearch.MixedMontgomery.weighted radix 9 (fun i => (productq inv a b n i).toNat) *
    HistoricalSearch.MixedMontgomery.weighted radix 9 (fun i => (n i).toNat)) := by
  refine ⟨gasSteps s inv a b n rest env h hcap hact, ?_⟩
  rw [output_value s inv a b n rest h]
  exact (productTrace inv a b n).exact_product ha hb hn N hn0 hinv

end CycleSubmission.ProductExecution
