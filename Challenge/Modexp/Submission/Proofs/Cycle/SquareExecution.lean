import Challenge.Modexp.Submission.Proofs.Cycle.NormalizeMeaning
import Challenge.Modexp.Submission.Proofs.Prepared.R9Shared.Complete

import Challenge.Modexp.Submission.Proofs.Cycle.Artifact
set_option warningAsError true
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option maxRecDepth 50000
set_option maxHeartbeats 16000000
namespace CycleSubmission.SquareExecution
open EvmSemantics EvmSemantics.EVM YulEvmCompiler
open CycleSubmission.SquareMeaning
open CycleSubmission.WordHistory CycleSubmission.WordArithmetic
open Challenge.Modexp.Submission.Proofs.Bytecode
open WindowNibbleKernel WindowTwentyOneBinding WindowTwentyOneSlice
open Challenge.EvmProof

theorem reset_self (s : State) (pc : UInt256) (stack : List UInt256)
    (hp : s.pc = pc) (hs : s.stack = stack) :
    {s with pc := pc, stack := stack} = s := by
  rw [← hp, ← hs]

def program : List Instr := R9InvRetainComplete.program

def memory0 (mem : ByteArray) (inv : UInt256) (a b n : Nat → UInt256) : ByteArray := mem
def state0 (s : State) (inv : UInt256) (a b n : Nat → UInt256) (rest : List UInt256) : State := s
def memory1 (mem : ByteArray) (inv : UInt256) (a b n : Nat → UInt256) : ByteArray := HistoricalSearch.CRTMemoryCells.storeCells (memory0 mem inv a b n) (cells0 inv a b n)
def state1 (s : State) (inv : UInt256) (a b n : Nat → UInt256) (rest : List UInt256) : State := {s with pc := UInt256.ofNat 5750, memory := memory1 s.memory inv a b n, stack := frame1 inv a b n rest}
def memory2 (mem : ByteArray) (inv : UInt256) (a b n : Nat → UInt256) : ByteArray := HistoricalSearch.CRTMemoryCells.storeCells (memory1 mem inv a b n) (cells1 inv a b n)
def state2 (s : State) (inv : UInt256) (a b n : Nat → UInt256) (rest : List UInt256) : State := {s with pc := UInt256.ofNat 5932, memory := memory2 s.memory inv a b n, stack := frame2 inv a b n rest}
def memory3 (mem : ByteArray) (inv : UInt256) (a b n : Nat → UInt256) : ByteArray := HistoricalSearch.CRTMemoryCells.storeCells (memory2 mem inv a b n) (cells2 inv a b n)
def state3 (s : State) (inv : UInt256) (a b n : Nat → UInt256) (rest : List UInt256) : State := {s with pc := UInt256.ofNat 6087, memory := memory3 s.memory inv a b n, stack := frame3 inv a b n rest}
def memory4 (mem : ByteArray) (inv : UInt256) (a b n : Nat → UInt256) : ByteArray := HistoricalSearch.CRTMemoryCells.storeCells (memory3 mem inv a b n) (cells3 inv a b n)
def state4 (s : State) (inv : UInt256) (a b n : Nat → UInt256) (rest : List UInt256) : State := {s with pc := UInt256.ofNat 6242, memory := memory4 s.memory inv a b n, stack := frame4 inv a b n rest}
def memory5 (mem : ByteArray) (inv : UInt256) (a b n : Nat → UInt256) : ByteArray := HistoricalSearch.CRTMemoryCells.storeCells (memory4 mem inv a b n) (cells4 inv a b n)
def state5 (s : State) (inv : UInt256) (a b n : Nat → UInt256) (rest : List UInt256) : State := {s with pc := UInt256.ofNat 6397, memory := memory5 s.memory inv a b n, stack := frame5 inv a b n rest}
def memory6 (mem : ByteArray) (inv : UInt256) (a b n : Nat → UInt256) : ByteArray := HistoricalSearch.CRTMemoryCells.storeCells (memory5 mem inv a b n) (cells5 inv a b n)
def state6 (s : State) (inv : UInt256) (a b n : Nat → UInt256) (rest : List UInt256) : State := {s with pc := UInt256.ofNat 6525, memory := memory6 s.memory inv a b n, stack := frame6 inv a b n rest}
def memory7 (mem : ByteArray) (inv : UInt256) (a b n : Nat → UInt256) : ByteArray := HistoricalSearch.CRTMemoryCells.storeCells (memory6 mem inv a b n) (cells6 inv a b n)
def state7 (s : State) (inv : UInt256) (a b n : Nat → UInt256) (rest : List UInt256) : State := {s with pc := UInt256.ofNat 6686, memory := memory7 s.memory inv a b n, stack := frame7 inv a b n rest}
def memory8 (mem : ByteArray) (inv : UInt256) (a b n : Nat → UInt256) : ByteArray := HistoricalSearch.CRTMemoryCells.storeCells (memory7 mem inv a b n) (cells7 inv a b n)
def state8 (s : State) (inv : UInt256) (a b n : Nat → UInt256) (rest : List UInt256) : State := {s with pc := UInt256.ofNat 6837, memory := memory8 s.memory inv a b n, stack := frame8 inv a b n rest}
def memory9 (mem : ByteArray) (inv : UInt256) (a b n : Nat → UInt256) : ByteArray := HistoricalSearch.CRTMemoryCells.storeCells (memory8 mem inv a b n) (cells8 inv a b n)
def state9 (s : State) (inv : UInt256) (a b n : Nat → UInt256) (rest : List UInt256) : State := {s with pc := UInt256.ofNat 6966, memory := memory9 s.memory inv a b n, stack := frame9 inv a b n rest}
def memory10 (mem : ByteArray) (inv : UInt256) (a b n : Nat → UInt256) : ByteArray := HistoricalSearch.CRTMemoryCells.storeCells (memory9 mem inv a b n) (cells9 inv a b n)
def state10 (s : State) (inv : UInt256) (a b n : Nat → UInt256) (rest : List UInt256) : State := {s with pc := UInt256.ofNat 7088, memory := memory10 s.memory inv a b n, stack := frame10 inv a b n rest}
def memory11 (mem : ByteArray) (inv : UInt256) (a b n : Nat → UInt256) : ByteArray := HistoricalSearch.CRTMemoryCells.storeCells (memory10 mem inv a b n) (cells10 inv a b n)
def state11 (s : State) (inv : UInt256) (a b n : Nat → UInt256) (rest : List UInt256) : State := {s with pc := UInt256.ofNat 7205, memory := memory11 s.memory inv a b n, stack := frame11 inv a b n rest}
def memory12 (mem : ByteArray) (inv : UInt256) (a b n : Nat → UInt256) : ByteArray := HistoricalSearch.CRTMemoryCells.storeCells (memory11 mem inv a b n) (cells11 inv a b n)
def state12 (s : State) (inv : UInt256) (a b n : Nat → UInt256) (rest : List UInt256) : State := {s with pc := UInt256.ofNat 7326, memory := memory12 s.memory inv a b n, stack := frame12 inv a b n rest}
def memory13 (mem : ByteArray) (inv : UInt256) (a b n : Nat → UInt256) : ByteArray := HistoricalSearch.CRTMemoryCells.storeCells (memory12 mem inv a b n) (cells12 inv a b n)
def state13 (s : State) (inv : UInt256) (a b n : Nat → UInt256) (rest : List UInt256) : State := {s with pc := UInt256.ofNat 7445, memory := memory13 s.memory inv a b n, stack := frame13 inv a b n rest}
def memory14 (mem : ByteArray) (inv : UInt256) (a b n : Nat → UInt256) : ByteArray := HistoricalSearch.CRTMemoryCells.storeCells (memory13 mem inv a b n) (cells13 inv a b n)
def state14 (s : State) (inv : UInt256) (a b n : Nat → UInt256) (rest : List UInt256) : State := {s with pc := UInt256.ofNat 7565, memory := memory14 s.memory inv a b n, stack := frame14 inv a b n rest}
def memory15 (mem : ByteArray) (inv : UInt256) (a b n : Nat → UInt256) : ByteArray := HistoricalSearch.CRTMemoryCells.storeCells (memory14 mem inv a b n) (cells14 inv a b n)
def state15 (s : State) (inv : UInt256) (a b n : Nat → UInt256) (rest : List UInt256) : State := {s with pc := UInt256.ofNat 7657, memory := memory15 s.memory inv a b n, stack := frame15 inv a b n rest}
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
    (hact : 88 ≤ s.activeWords.toNat)
    (ha : ∀ i < 8, (a i).toNat < radix) :
    runInstructions program
      {s with pc := UInt256.ofNat 5568, stack := frame0 inv a b n rest} =
      some (state15 s inv a b n rest) := by
  have hh := R9InvRetainComplete.run s inv a b n rest hcap hact h ha
  simpa only [program, R9InvRetainComplete.historyMemory, state15, memory0, memory1, memory2, memory3, memory4, memory5, memory6, memory7, memory8, memory9, memory10, memory11, memory12, memory13, memory14, memory15, cells0, cells1, cells2, cells3, cells4, cells5, cells6, cells7, cells8, cells9, cells10, cells11, cells12, cells13, cells14, HistoricalSearch.CRTMemoryCells.storeCells, HistoricalSearch.CRTMemoryCells.writeCell] using hh

theorem memory_output (s : State) (inv : UInt256) (a b n : Nat → UInt256) (rest : List UInt256) (h : Memory0 s.memory inv a b n) :
    Memory15 (state15 s inv a b n rest).memory inv a b n := by
  constructor <;> simp (disch := decide) only [state15, memory0, memory1, memory2, memory3, memory4, memory5, memory6, memory7, memory8, memory9, memory10, memory11, memory12, memory13, memory14, memory15, cells0, cells1, cells2, cells3, cells4, cells5, cells6, cells7, cells8, cells9, cells10, cells11, cells12, cells13, cells14, HistoricalSearch.CRTMemoryCells.storeCells, HistoricalSearch.CRTMemoryCells.writeCell, Challenge.EvmProof.Memory.readWord_writeWord, CycleSubmission.Prepared.Arithmetic.read_disjoint, h.at768, h.at1344, h.at1376, h.at2720, h.at1568, h.at1600, h.at32, h.at64, h.at96, h.at128, h.at160]

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

def block : Block Artifact.artifact .Osaka 5568 program :=
  WindowTwentyOneSlice.block CycleSubmission.Artifact.wellFormed 4232 1573 5568 program
    (by change 4232 + 1573 ≤ CycleSubmission.Artifact.instructions.length; rw [CycleSubmission.Artifact.instructionCount]; decide)
    (by rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)

noncomputable def gasSteps (s : State) (inv : UInt256) (a b n : Nat → UInt256) (rest : List UInt256)
    (env : Environment Artifact.artifact .Osaka s)
    (h : Memory0 s.memory inv a b n) (hcap : rest.length ≤ 960)
    (hact : 88 ≤ s.activeWords.toNat)
    (ha : ∀ i < 8, (a i).toNat < radix) :
    GasSteps {s with pc := UInt256.ofNat 5568, stack := frame0 inv a b n rest}
      (state15 s inv a b n rest) :=
  block.steps
    (s := {s with pc := UInt256.ofNat 5568, stack := frame0 inv a b n rest})
    (env.transfer rfl rfl) rfl (run s inv a b n rest h hcap hact ha)

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
      {s with pc := UInt256.ofNat 5568, stack := frame0 inv a b n rest}
      (state15 s inv a b n rest) =>
    HistoricalSearch.MixedMontgomery.weighted radix 9
      (fun i => (outputWord (state15 s inv a b n rest) i).toNat) * radix^9 =
    HistoricalSearch.MixedMontgomery.weighted radix 9 (fun i => (a i).toNat) *
    HistoricalSearch.MixedMontgomery.weighted radix 9 (fun i => (a i).toNat) +
    HistoricalSearch.MixedMontgomery.weighted radix 9 (fun i => (squareq inv a b n i).toNat) *
    HistoricalSearch.MixedMontgomery.weighted radix 9 (fun i => (n i).toNat)) := by
  refine ⟨gasSteps s inv a b n rest env h hcap hact (fun i hi => ha i (by omega)), ?_⟩
  rw [output_value s inv a b n rest h]
  exact (squareTrace inv a b n).exact_product ha hb hn N hn0 hinv

end CycleSubmission.SquareExecution
