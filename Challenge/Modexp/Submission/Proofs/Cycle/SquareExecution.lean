import Challenge.Modexp.Submission.Proofs.Cycle.Meaning.Square0
import Challenge.Modexp.Submission.Proofs.Cycle.Meaning.Square1
import Challenge.Modexp.Submission.Proofs.Cycle.Meaning.Square2
import Challenge.Modexp.Submission.Proofs.Cycle.Meaning.Square3
import Challenge.Modexp.Submission.Proofs.Cycle.Meaning.Square4
import Challenge.Modexp.Submission.Proofs.Cycle.Meaning.Square5
import Challenge.Modexp.Submission.Proofs.Cycle.Meaning.Square6
import Challenge.Modexp.Submission.Proofs.Cycle.Meaning.Square7
import Challenge.Modexp.Submission.Proofs.Cycle.Meaning.Square8
import Challenge.Modexp.Submission.Proofs.Cycle.Meaning.Square9
import Challenge.Modexp.Submission.Proofs.Cycle.Meaning.Square10
import Challenge.Modexp.Submission.Proofs.Cycle.Meaning.Square11
import Challenge.Modexp.Submission.Proofs.Cycle.Meaning.Square12
import Challenge.Modexp.Submission.Proofs.Cycle.Meaning.Square13
import Challenge.Modexp.Submission.Proofs.Cycle.Meaning.Square14

import Challenge.Modexp.Submission.Proofs.Cycle.Artifact
set_option warningAsError true
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option maxRecDepth 50000
set_option maxHeartbeats 16000000
namespace CycleSubmission.SquareExecution
open EvmSemantics EvmSemantics.EVM YulEvmCompiler
open CycleSubmission.Execution CycleSubmission.SquareMeaning
open CycleSubmission.WordHistory CycleSubmission.WordArithmetic
open Challenge.Modexp.Submission.Proofs.Bytecode
open WindowNibbleKernel WindowTwentyOneBinding WindowTwentyOneSlice
open Challenge.EvmProof

theorem reset_self (s : State) (pc : UInt256) (stack : List UInt256)
    (hp : s.pc = pc) (hs : s.stack = stack) :
    {s with pc := pc, stack := stack} = s := by
  rw [← hp, ← hs]

def program : List Instr :=
  squareColumn0Program ++ (squareColumn1Program ++ (squareColumn2Program ++ (squareColumn3Program ++ (squareColumn4Program ++ (squareColumn5Program ++ (squareColumn6Program ++ (squareColumn7Program ++ (squareColumn8Program ++ (squareColumn9Program ++ (squareColumn10Program ++ (squareColumn11Program ++ (squareColumn12Program ++ (squareColumn13Program ++ (squareColumn14Program))))))))))))))

def memory0 (mem : ByteArray) (inv : UInt256) (a b n : Nat → UInt256) : ByteArray := mem
def state0 (s : State) (inv : UInt256) (a b n : Nat → UInt256) (rest : List UInt256) : State := s
def memory1 (mem : ByteArray) (inv : UInt256) (a b n : Nat → UInt256) : ByteArray := HistoricalSearch.CRTMemoryCells.storeCells (memory0 mem inv a b n) (cells0 inv a b n)
def state1 (s : State) (inv : UInt256) (a b n : Nat → UInt256) (rest : List UInt256) : State := {s with pc := UInt256.ofNat 6281, memory := memory1 s.memory inv a b n, stack := frame1 inv a b n rest}
def memory2 (mem : ByteArray) (inv : UInt256) (a b n : Nat → UInt256) : ByteArray := HistoricalSearch.CRTMemoryCells.storeCells (memory1 mem inv a b n) (cells1 inv a b n)
def state2 (s : State) (inv : UInt256) (a b n : Nat → UInt256) (rest : List UInt256) : State := {s with pc := UInt256.ofNat 6409, memory := memory2 s.memory inv a b n, stack := frame2 inv a b n rest}
def memory3 (mem : ByteArray) (inv : UInt256) (a b n : Nat → UInt256) : ByteArray := HistoricalSearch.CRTMemoryCells.storeCells (memory2 mem inv a b n) (cells2 inv a b n)
def state3 (s : State) (inv : UInt256) (a b n : Nat → UInt256) (rest : List UInt256) : State := {s with pc := UInt256.ofNat 6537, memory := memory3 s.memory inv a b n, stack := frame3 inv a b n rest}
def memory4 (mem : ByteArray) (inv : UInt256) (a b n : Nat → UInt256) : ByteArray := HistoricalSearch.CRTMemoryCells.storeCells (memory3 mem inv a b n) (cells3 inv a b n)
def state4 (s : State) (inv : UInt256) (a b n : Nat → UInt256) (rest : List UInt256) : State := {s with pc := UInt256.ofNat 6665, memory := memory4 s.memory inv a b n, stack := frame4 inv a b n rest}
def memory5 (mem : ByteArray) (inv : UInt256) (a b n : Nat → UInt256) : ByteArray := HistoricalSearch.CRTMemoryCells.storeCells (memory4 mem inv a b n) (cells4 inv a b n)
def state5 (s : State) (inv : UInt256) (a b n : Nat → UInt256) (rest : List UInt256) : State := {s with pc := UInt256.ofNat 6793, memory := memory5 s.memory inv a b n, stack := frame5 inv a b n rest}
def memory6 (mem : ByteArray) (inv : UInt256) (a b n : Nat → UInt256) : ByteArray := HistoricalSearch.CRTMemoryCells.storeCells (memory5 mem inv a b n) (cells5 inv a b n)
def state6 (s : State) (inv : UInt256) (a b n : Nat → UInt256) (rest : List UInt256) : State := {s with pc := UInt256.ofNat 6921, memory := memory6 s.memory inv a b n, stack := frame6 inv a b n rest}
def memory7 (mem : ByteArray) (inv : UInt256) (a b n : Nat → UInt256) : ByteArray := HistoricalSearch.CRTMemoryCells.storeCells (memory6 mem inv a b n) (cells6 inv a b n)
def state7 (s : State) (inv : UInt256) (a b n : Nat → UInt256) (rest : List UInt256) : State := {s with pc := UInt256.ofNat 7049, memory := memory7 s.memory inv a b n, stack := frame7 inv a b n rest}
def memory8 (mem : ByteArray) (inv : UInt256) (a b n : Nat → UInt256) : ByteArray := HistoricalSearch.CRTMemoryCells.storeCells (memory7 mem inv a b n) (cells7 inv a b n)
def state8 (s : State) (inv : UInt256) (a b n : Nat → UInt256) (rest : List UInt256) : State := {s with pc := UInt256.ofNat 7177, memory := memory8 s.memory inv a b n, stack := frame8 inv a b n rest}
def memory9 (mem : ByteArray) (inv : UInt256) (a b n : Nat → UInt256) : ByteArray := HistoricalSearch.CRTMemoryCells.storeCells (memory8 mem inv a b n) (cells8 inv a b n)
def state9 (s : State) (inv : UInt256) (a b n : Nat → UInt256) (rest : List UInt256) : State := {s with pc := UInt256.ofNat 7306, memory := memory9 s.memory inv a b n, stack := frame9 inv a b n rest}
def memory10 (mem : ByteArray) (inv : UInt256) (a b n : Nat → UInt256) : ByteArray := HistoricalSearch.CRTMemoryCells.storeCells (memory9 mem inv a b n) (cells9 inv a b n)
def state10 (s : State) (inv : UInt256) (a b n : Nat → UInt256) (rest : List UInt256) : State := {s with pc := UInt256.ofNat 7434, memory := memory10 s.memory inv a b n, stack := frame10 inv a b n rest}
def memory11 (mem : ByteArray) (inv : UInt256) (a b n : Nat → UInt256) : ByteArray := HistoricalSearch.CRTMemoryCells.storeCells (memory10 mem inv a b n) (cells10 inv a b n)
def state11 (s : State) (inv : UInt256) (a b n : Nat → UInt256) (rest : List UInt256) : State := {s with pc := UInt256.ofNat 7563, memory := memory11 s.memory inv a b n, stack := frame11 inv a b n rest}
def memory12 (mem : ByteArray) (inv : UInt256) (a b n : Nat → UInt256) : ByteArray := HistoricalSearch.CRTMemoryCells.storeCells (memory11 mem inv a b n) (cells11 inv a b n)
def state12 (s : State) (inv : UInt256) (a b n : Nat → UInt256) (rest : List UInt256) : State := {s with pc := UInt256.ofNat 7693, memory := memory12 s.memory inv a b n, stack := frame12 inv a b n rest}
def memory13 (mem : ByteArray) (inv : UInt256) (a b n : Nat → UInt256) : ByteArray := HistoricalSearch.CRTMemoryCells.storeCells (memory12 mem inv a b n) (cells12 inv a b n)
def state13 (s : State) (inv : UInt256) (a b n : Nat → UInt256) (rest : List UInt256) : State := {s with pc := UInt256.ofNat 7821, memory := memory13 s.memory inv a b n, stack := frame13 inv a b n rest}
def memory14 (mem : ByteArray) (inv : UInt256) (a b n : Nat → UInt256) : ByteArray := HistoricalSearch.CRTMemoryCells.storeCells (memory13 mem inv a b n) (cells13 inv a b n)
def state14 (s : State) (inv : UInt256) (a b n : Nat → UInt256) (rest : List UInt256) : State := {s with pc := UInt256.ofNat 7950, memory := memory14 s.memory inv a b n, stack := frame14 inv a b n rest}
def memory15 (mem : ByteArray) (inv : UInt256) (a b n : Nat → UInt256) : ByteArray := HistoricalSearch.CRTMemoryCells.storeCells (memory14 mem inv a b n) (cells14 inv a b n)
def state15 (s : State) (inv : UInt256) (a b n : Nat → UInt256) (rest : List UInt256) : State := {s with pc := UInt256.ofNat 8077, memory := memory15 s.memory inv a b n, stack := frame15 inv a b n rest}
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
      rcases hc with rfl | rfl
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
      rcases hc with rfl
      all_goals (dsimp; omega))
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
      )
  exact h.trans (memory7_keeps mem inv a b n start count hs)

theorem memory9_keeps (mem : ByteArray) (inv : UInt256) (a b n : Nat → UInt256)
    (start count : Nat) (hs : (256 ≤ start ∧ start+count ≤ 768) ∨ 1312 ≤ start) :
    MachineState.readPadded (memory9 mem inv a b n) start count =
      MachineState.readPadded mem start count := by
  have h := HistoricalSearch.CRTMemoryCells.readPadded_storeCells
    (memory8 mem inv a b n) (cells8 inv a b n) start count (by
      intro c hc
      simp only [cells8, List.mem_cons, List.mem_nil_iff, or_false] at hc
      )
  exact h.trans (memory8_keeps mem inv a b n start count hs)

theorem memory10_keeps (mem : ByteArray) (inv : UInt256) (a b n : Nat → UInt256)
    (start count : Nat) (hs : (256 ≤ start ∧ start+count ≤ 768) ∨ 1312 ≤ start) :
    MachineState.readPadded (memory10 mem inv a b n) start count =
      MachineState.readPadded mem start count := by
  have h := HistoricalSearch.CRTMemoryCells.readPadded_storeCells
    (memory9 mem inv a b n) (cells9 inv a b n) start count (by
      intro c hc
      simp only [cells9, List.mem_cons, List.mem_nil_iff, or_false] at hc
      rcases hc with rfl
      all_goals (dsimp; omega))
  exact h.trans (memory9_keeps mem inv a b n start count hs)

theorem memory11_keeps (mem : ByteArray) (inv : UInt256) (a b n : Nat → UInt256)
    (start count : Nat) (hs : (256 ≤ start ∧ start+count ≤ 768) ∨ 1312 ≤ start) :
    MachineState.readPadded (memory11 mem inv a b n) start count =
      MachineState.readPadded mem start count := by
  have h := HistoricalSearch.CRTMemoryCells.readPadded_storeCells
    (memory10 mem inv a b n) (cells10 inv a b n) start count (by
      intro c hc
      simp only [cells10, List.mem_cons, List.mem_nil_iff, or_false] at hc
      rcases hc with rfl
      all_goals (dsimp; omega))
  exact h.trans (memory10_keeps mem inv a b n start count hs)

theorem memory12_keeps (mem : ByteArray) (inv : UInt256) (a b n : Nat → UInt256)
    (start count : Nat) (hs : (256 ≤ start ∧ start+count ≤ 768) ∨ 1312 ≤ start) :
    MachineState.readPadded (memory12 mem inv a b n) start count =
      MachineState.readPadded mem start count := by
  have h := HistoricalSearch.CRTMemoryCells.readPadded_storeCells
    (memory11 mem inv a b n) (cells11 inv a b n) start count (by
      intro c hc
      simp only [cells11, List.mem_cons, List.mem_nil_iff, or_false] at hc
      rcases hc with rfl
      all_goals (dsimp; omega))
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
      rcases hc with rfl | rfl
      all_goals (dsimp; omega))
  exact h.trans (memory13_keeps mem inv a b n start count hs)

theorem memory15_keeps (mem : ByteArray) (inv : UInt256) (a b n : Nat → UInt256)
    (start count : Nat) (hs : (256 ≤ start ∧ start+count ≤ 768) ∨ 1312 ≤ start) :
    MachineState.readPadded (memory15 mem inv a b n) start count =
      MachineState.readPadded mem start count := by
  have h := HistoricalSearch.CRTMemoryCells.readPadded_storeCells
    (memory14 mem inv a b n) (cells14 inv a b n) start count (by
      intro c hc
      simp only [cells14, List.mem_cons, List.mem_nil_iff, or_false] at hc
      rcases hc with rfl | rfl
      all_goals (dsimp; omega))
  exact h.trans (memory14_keeps mem inv a b n start count hs)

theorem run (s : State) (inv : UInt256) (a b n : Nat → UInt256) (rest : List UInt256)
    (h : Memory0 s.memory inv a b n) (hcap : rest.length ≤ 960)
    (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions program
      {s with pc := UInt256.ofNat 6153, stack := frame0 inv a b n rest} =
      some (state15 s inv a b n rest) := by
  have m0 := h

  have m1 := memory0_output (state0 s inv a b n rest) inv a b n rest m0
  have h0 : runInstructions squareColumn0Program {s with pc := UInt256.ofNat 6153, stack := frame0 inv a b n rest} = some (state1 s inv a b n rest) :=
    run0 (state0 s inv a b n rest) inv a b n rest m0 hcap hact
  have m2 := memory1_output (state1 s inv a b n rest) inv a b n rest m1
  have h1 : runInstructions squareColumn1Program (state1 s inv a b n rest) = some (state2 s inv a b n rest) := by
    have hx := run1 (state1 s inv a b n rest) inv a b n rest m1 hcap hact
    rw [reset_self (state1 s inv a b n rest) (UInt256.ofNat 6281) (frame1 inv a b n rest) rfl rfl] at hx
    exact hx
  have m3 := memory2_output (state2 s inv a b n rest) inv a b n rest m2
  have h2 : runInstructions squareColumn2Program (state2 s inv a b n rest) = some (state3 s inv a b n rest) := by
    have hx := run2 (state2 s inv a b n rest) inv a b n rest m2 hcap hact
    rw [reset_self (state2 s inv a b n rest) (UInt256.ofNat 6409) (frame2 inv a b n rest) rfl rfl] at hx
    exact hx
  have m4 := memory3_output (state3 s inv a b n rest) inv a b n rest m3
  have h3 : runInstructions squareColumn3Program (state3 s inv a b n rest) = some (state4 s inv a b n rest) := by
    have hx := run3 (state3 s inv a b n rest) inv a b n rest m3 hcap hact
    rw [reset_self (state3 s inv a b n rest) (UInt256.ofNat 6537) (frame3 inv a b n rest) rfl rfl] at hx
    exact hx
  have m5 := memory4_output (state4 s inv a b n rest) inv a b n rest m4
  have h4 : runInstructions squareColumn4Program (state4 s inv a b n rest) = some (state5 s inv a b n rest) := by
    have hx := run4 (state4 s inv a b n rest) inv a b n rest m4 hcap hact
    rw [reset_self (state4 s inv a b n rest) (UInt256.ofNat 6665) (frame4 inv a b n rest) rfl rfl] at hx
    exact hx
  have m6 := memory5_output (state5 s inv a b n rest) inv a b n rest m5
  have h5 : runInstructions squareColumn5Program (state5 s inv a b n rest) = some (state6 s inv a b n rest) := by
    have hx := run5 (state5 s inv a b n rest) inv a b n rest m5 hcap hact
    rw [reset_self (state5 s inv a b n rest) (UInt256.ofNat 6793) (frame5 inv a b n rest) rfl rfl] at hx
    exact hx
  have m7 := memory6_output (state6 s inv a b n rest) inv a b n rest m6
  have h6 : runInstructions squareColumn6Program (state6 s inv a b n rest) = some (state7 s inv a b n rest) := by
    have hx := run6 (state6 s inv a b n rest) inv a b n rest m6 hcap hact
    rw [reset_self (state6 s inv a b n rest) (UInt256.ofNat 6921) (frame6 inv a b n rest) rfl rfl] at hx
    exact hx
  have m8 := memory7_output (state7 s inv a b n rest) inv a b n rest m7
  have h7 : runInstructions squareColumn7Program (state7 s inv a b n rest) = some (state8 s inv a b n rest) := by
    have hx := run7 (state7 s inv a b n rest) inv a b n rest m7 hcap hact
    rw [reset_self (state7 s inv a b n rest) (UInt256.ofNat 7049) (frame7 inv a b n rest) rfl rfl] at hx
    exact hx
  have m9 := memory8_output (state8 s inv a b n rest) inv a b n rest m8
  have h8 : runInstructions squareColumn8Program (state8 s inv a b n rest) = some (state9 s inv a b n rest) := by
    have hx := run8 (state8 s inv a b n rest) inv a b n rest m8 hcap hact
    rw [reset_self (state8 s inv a b n rest) (UInt256.ofNat 7177) (frame8 inv a b n rest) rfl rfl] at hx
    exact hx
  have m10 := memory9_output (state9 s inv a b n rest) inv a b n rest m9
  have h9 : runInstructions squareColumn9Program (state9 s inv a b n rest) = some (state10 s inv a b n rest) := by
    have hx := run9 (state9 s inv a b n rest) inv a b n rest m9 hcap hact
    rw [reset_self (state9 s inv a b n rest) (UInt256.ofNat 7306) (frame9 inv a b n rest) rfl rfl] at hx
    exact hx
  have m11 := memory10_output (state10 s inv a b n rest) inv a b n rest m10
  have h10 : runInstructions squareColumn10Program (state10 s inv a b n rest) = some (state11 s inv a b n rest) := by
    have hx := run10 (state10 s inv a b n rest) inv a b n rest m10 hcap hact
    rw [reset_self (state10 s inv a b n rest) (UInt256.ofNat 7434) (frame10 inv a b n rest) rfl rfl] at hx
    exact hx
  have m12 := memory11_output (state11 s inv a b n rest) inv a b n rest m11
  have h11 : runInstructions squareColumn11Program (state11 s inv a b n rest) = some (state12 s inv a b n rest) := by
    have hx := run11 (state11 s inv a b n rest) inv a b n rest m11 hcap hact
    rw [reset_self (state11 s inv a b n rest) (UInt256.ofNat 7563) (frame11 inv a b n rest) rfl rfl] at hx
    exact hx
  have m13 := memory12_output (state12 s inv a b n rest) inv a b n rest m12
  have h12 : runInstructions squareColumn12Program (state12 s inv a b n rest) = some (state13 s inv a b n rest) := by
    have hx := run12 (state12 s inv a b n rest) inv a b n rest m12 hcap hact
    rw [reset_self (state12 s inv a b n rest) (UInt256.ofNat 7693) (frame12 inv a b n rest) rfl rfl] at hx
    exact hx
  have m14 := memory13_output (state13 s inv a b n rest) inv a b n rest m13
  have h13 : runInstructions squareColumn13Program (state13 s inv a b n rest) = some (state14 s inv a b n rest) := by
    have hx := run13 (state13 s inv a b n rest) inv a b n rest m13 hcap hact
    rw [reset_self (state13 s inv a b n rest) (UInt256.ofNat 7821) (frame13 inv a b n rest) rfl rfl] at hx
    exact hx
  have m15 := memory14_output (state14 s inv a b n rest) inv a b n rest m14
  have h14 : runInstructions squareColumn14Program (state14 s inv a b n rest) = some (state15 s inv a b n rest) := by
    have hx := run14 (state14 s inv a b n rest) inv a b n rest m14 hcap hact
    rw [reset_self (state14 s inv a b n rest) (UInt256.ofNat 7950) (frame14 inv a b n rest) rfl rfl] at hx
    exact hx
  exact (runInstructions_append_some _ _ _ _ _ h0 (runInstructions_append_some _ _ _ _ _ h1 (runInstructions_append_some _ _ _ _ _ h2 (runInstructions_append_some _ _ _ _ _ h3 (runInstructions_append_some _ _ _ _ _ h4 (runInstructions_append_some _ _ _ _ _ h5 (runInstructions_append_some _ _ _ _ _ h6 (runInstructions_append_some _ _ _ _ _ h7 (runInstructions_append_some _ _ _ _ _ h8 (runInstructions_append_some _ _ _ _ _ h9 (runInstructions_append_some _ _ _ _ _ h10 (runInstructions_append_some _ _ _ _ _ h11 (runInstructions_append_some _ _ _ _ _ h12 (runInstructions_append_some _ _ _ _ _ h13 h14))))))))))))))

theorem memory_output (s : State) (inv : UInt256) (a b n : Nat → UInt256) (rest : List UInt256) (h : Memory0 s.memory inv a b n) :
    Memory15 (state15 s inv a b n rest).memory inv a b n := by
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
  exact m15

theorem normalizer_input (s : State) (inv : UInt256) (a b n : Nat → UInt256) (rest : List UInt256)
    (h : Memory0 s.memory inv a b n) :
    CycleSubmission.NormalizeMeaning.MemoryInput (state15 s inv a b n rest).memory
      (squared inv a b n) n := by
  have m := memory_output s inv a b n rest h
  exact ⟨m.at768, m.at32, m.at64, m.at96, m.at128, m.at160, m.at1344, m.at1376⟩

theorem output_frame (s : State) (inv : UInt256) (a b n : Nat → UInt256) (rest : List UInt256) :
    (state15 s inv a b n rest).stack = CycleSubmission.NormalizeMeaning.frame
      (squared inv a b n) n
      (n 0)
      (n 1) rest := rfl

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
    outputWord (state15 s inv a b n rest) i = squared inv a b n i := by
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
      (fun i => (outputWord (state15 s inv a b n rest) i).toNat) =
    HistoricalSearch.MixedMontgomery.weighted radix 9
      (fun i => (squared inv a b n i).toNat) := by
  apply Finset.sum_congr rfl
  intro i hi
  dsimp only
  rw [output_eq s inv a b n rest h i (Finset.mem_range.mp hi)]

def block : Block Artifact.artifact .Osaka 6153 program :=
  WindowTwentyOneSlice.block Artifact.wellFormed 5030 1655 6153 program
    (by change 5030+1655 ≤ Artifact.instructions.length
        exact Nat.le_trans (by decide : 5030+1655 ≤ 9183)
          (Nat.le_of_eq Artifact.instructionCount.symm))
    (by rw [PCFast.instructionPC_eq_byteLength]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)

noncomputable def gasSteps (s : State) (inv : UInt256) (a b n : Nat → UInt256) (rest : List UInt256)
    (env : Environment Artifact.artifact .Osaka s)
    (h : Memory0 s.memory inv a b n) (hcap : rest.length ≤ 960)
    (hact : 88 ≤ s.activeWords.toNat) :
    GasSteps {s with pc := UInt256.ofNat 6153, stack := frame0 inv a b n rest}
      (state15 s inv a b n rest) :=
  block.steps
    (s := {s with pc := UInt256.ofNat 6153, stack := frame0 inv a b n rest})
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
      {s with pc := UInt256.ofNat 6153, stack := frame0 inv a b n rest}
      (state15 s inv a b n rest) =>
    HistoricalSearch.MixedMontgomery.weighted radix 9
      (fun i => (outputWord (state15 s inv a b n rest) i).toNat) * radix^9 =
    HistoricalSearch.MixedMontgomery.weighted radix 9 (fun i => (a i).toNat) *
    HistoricalSearch.MixedMontgomery.weighted radix 9 (fun i => (a i).toNat) +
    HistoricalSearch.MixedMontgomery.weighted radix 9 (fun i => (squareq inv a b n i).toNat) *
    HistoricalSearch.MixedMontgomery.weighted radix 9 (fun i => (n i).toNat)) := by
  refine ⟨gasSteps s inv a b n rest env h hcap hact, ?_⟩
  rw [output_value s inv a b n rest h]
  exact (squareTrace inv a b n).exact_product ha hb hn N hn0 hinv

end CycleSubmission.SquareExecution
