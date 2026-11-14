import Challenge.Modexp.Submission.Proofs.Prepared.ProductGroup8130
import Challenge.Modexp.Submission.Proofs.Prepared.ProductGroup9668
import Challenge.Modexp.Submission.Proofs.Prepared.ProductGroup10052
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
    {s with pc := pc,stack := stack} = s := by
  rw [← hp,← hs]
def program : List Instr :=
  productColumn0Program++(productColumn1Program++(productColumn2Program++(CycleSubmission.Prepared.ProductGroup8130.newProgram++(productColumn6Program++(productColumn7Program++(productColumn8Program++(productColumn9Program++(productColumn10Program++(productColumn11Program++(productColumn12Program++(productColumn13Program++(productColumn14Program++(CycleSubmission.Prepared.ProductGroup9668.newProgram++(CycleSubmission.Prepared.ProductGroup10052.newProgram))))))))))))))
def memory0 (mem : ByteArray) (inv : UInt256) (a b n : Nat → UInt256) : ByteArray := mem
def state0 (s : State) (inv : UInt256) (a b n : Nat → UInt256) (rest : List UInt256) : State := s
def memory1 (mem : ByteArray) (inv : UInt256) (a b n : Nat → UInt256) : ByteArray := HistoricalSearch.CRTMemoryCells.storeCells (memory0 mem inv a b n) (cells0 inv a b n)
def state1 (s : State) (inv : UInt256) (a b n : Nat → UInt256) (rest : List UInt256) : State := {s with pc := UInt256.ofNat 6031,memory := memory1 s.memory inv a b n,stack := frame1 inv a b n rest}
def memory2 (mem : ByteArray) (inv : UInt256) (a b n : Nat → UInt256) : ByteArray := HistoricalSearch.CRTMemoryCells.storeCells (memory1 mem inv a b n) (cells1 inv a b n)
def state2 (s : State) (inv : UInt256) (a b n : Nat → UInt256) (rest : List UInt256) : State := {s with pc := UInt256.ofNat 6157,memory := memory2 s.memory inv a b n,stack := frame2 inv a b n rest}
def memory3 (mem : ByteArray) (inv : UInt256) (a b n : Nat → UInt256) : ByteArray := HistoricalSearch.CRTMemoryCells.storeCells (memory2 mem inv a b n) (cells2 inv a b n)
def state3 (s : State) (inv : UInt256) (a b n : Nat → UInt256) (rest : List UInt256) : State := {s with pc := UInt256.ofNat 6283,memory := memory3 s.memory inv a b n,stack := frame3 inv a b n rest}
def memory4 (mem : ByteArray) (inv : UInt256) (a b n : Nat → UInt256) : ByteArray := HistoricalSearch.CRTMemoryCells.storeCells (memory3 mem inv a b n) (cells3 inv a b n)
def state4 (s : State) (inv : UInt256) (a b n : Nat → UInt256) (rest : List UInt256) : State := {s with pc := UInt256.ofNat 6409,memory := memory4 s.memory inv a b n,stack := frame4 inv a b n rest}
def memory5 (mem : ByteArray) (inv : UInt256) (a b n : Nat → UInt256) : ByteArray := HistoricalSearch.CRTMemoryCells.storeCells (memory4 mem inv a b n) (cells4 inv a b n)
def state5 (s : State) (inv : UInt256) (a b n : Nat → UInt256) (rest : List UInt256) : State := {s with pc := UInt256.ofNat 6536,memory := memory5 s.memory inv a b n,stack := frame5 inv a b n rest}
def memory6 (mem : ByteArray) (inv : UInt256) (a b n : Nat → UInt256) : ByteArray := HistoricalSearch.CRTMemoryCells.storeCells (memory5 mem inv a b n) (cells5 inv a b n)
def state6 (s : State) (inv : UInt256) (a b n : Nat → UInt256) (rest : List UInt256) : State := {s with pc := UInt256.ofNat 6663,memory := memory6 s.memory inv a b n,stack := frame6 inv a b n rest}
def memory7 (mem : ByteArray) (inv : UInt256) (a b n : Nat → UInt256) : ByteArray := HistoricalSearch.CRTMemoryCells.storeCells (memory6 mem inv a b n) (cells6 inv a b n)
def state7 (s : State) (inv : UInt256) (a b n : Nat → UInt256) (rest : List UInt256) : State := {s with pc := UInt256.ofNat 6791,memory := memory7 s.memory inv a b n,stack := frame7 inv a b n rest}
def memory8 (mem : ByteArray) (inv : UInt256) (a b n : Nat → UInt256) : ByteArray := HistoricalSearch.CRTMemoryCells.storeCells (memory7 mem inv a b n) (cells7 inv a b n)
def state8 (s : State) (inv : UInt256) (a b n : Nat → UInt256) (rest : List UInt256) : State := {s with pc := UInt256.ofNat 6918,memory := memory8 s.memory inv a b n,stack := frame8 inv a b n rest}
def memory9 (mem : ByteArray) (inv : UInt256) (a b n : Nat → UInt256) : ByteArray := HistoricalSearch.CRTMemoryCells.storeCells (memory8 mem inv a b n) (cells8 inv a b n)
def state9 (s : State) (inv : UInt256) (a b n : Nat → UInt256) (rest : List UInt256) : State := {s with pc := UInt256.ofNat 7045,memory := memory9 s.memory inv a b n,stack := frame9 inv a b n rest}
def memory10 (mem : ByteArray) (inv : UInt256) (a b n : Nat → UInt256) : ByteArray := HistoricalSearch.CRTMemoryCells.storeCells (memory9 mem inv a b n) (cells9 inv a b n)
def state10 (s : State) (inv : UInt256) (a b n : Nat → UInt256) (rest : List UInt256) : State := {s with pc := UInt256.ofNat 7172,memory := memory10 s.memory inv a b n,stack := frame10 inv a b n rest}
def memory11 (mem : ByteArray) (inv : UInt256) (a b n : Nat → UInt256) : ByteArray := HistoricalSearch.CRTMemoryCells.storeCells (memory10 mem inv a b n) (cells10 inv a b n)
def state11 (s : State) (inv : UInt256) (a b n : Nat → UInt256) (rest : List UInt256) : State := {s with pc := UInt256.ofNat 7301,memory := memory11 s.memory inv a b n,stack := frame11 inv a b n rest}
def memory12 (mem : ByteArray) (inv : UInt256) (a b n : Nat → UInt256) : ByteArray := HistoricalSearch.CRTMemoryCells.storeCells (memory11 mem inv a b n) (cells11 inv a b n)
def state12 (s : State) (inv : UInt256) (a b n : Nat → UInt256) (rest : List UInt256) : State := {s with pc := UInt256.ofNat 7428,memory := memory12 s.memory inv a b n,stack := frame12 inv a b n rest}
def memory13 (mem : ByteArray) (inv : UInt256) (a b n : Nat → UInt256) : ByteArray := HistoricalSearch.CRTMemoryCells.storeCells (memory12 mem inv a b n) (cells12 inv a b n)
def state13 (s : State) (inv : UInt256) (a b n : Nat → UInt256) (rest : List UInt256) : State := {s with pc := UInt256.ofNat 7550,memory := memory13 s.memory inv a b n,stack := frame13 inv a b n rest}
def memory14 (mem : ByteArray) (inv : UInt256) (a b n : Nat → UInt256) : ByteArray := HistoricalSearch.CRTMemoryCells.storeCells (memory13 mem inv a b n) (cells13 inv a b n)
def state14 (s : State) (inv : UInt256) (a b n : Nat → UInt256) (rest : List UInt256) : State := {s with pc := UInt256.ofNat 7667,memory := memory14 s.memory inv a b n,stack := frame14 inv a b n rest}
def memory15 (mem : ByteArray) (inv : UInt256) (a b n : Nat → UInt256) : ByteArray := HistoricalSearch.CRTMemoryCells.storeCells (memory14 mem inv a b n) (cells14 inv a b n)
def state15 (s : State) (inv : UInt256) (a b n : Nat → UInt256) (rest : List UInt256) : State := {s with pc := UInt256.ofNat 7800,memory := memory15 s.memory inv a b n,stack := frame15 inv a b n rest}
def memory16 (mem : ByteArray) (inv : UInt256) (a b n : Nat → UInt256) : ByteArray := HistoricalSearch.CRTMemoryCells.storeCells (memory15 mem inv a b n) (cells15 inv a b n)
def state16 (s : State) (inv : UInt256) (a b n : Nat → UInt256) (rest : List UInt256) : State := {s with pc := UInt256.ofNat 10324,memory := memory16 s.memory inv a b n,stack := frame16 inv a b n rest}
def memory17 (mem : ByteArray) (inv : UInt256) (a b n : Nat → UInt256) : ByteArray := HistoricalSearch.CRTMemoryCells.storeCells (memory16 mem inv a b n) (cells16 inv a b n)
def state17 (s : State) (inv : UInt256) (a b n : Nat → UInt256) (rest : List UInt256) : State := {s with pc := UInt256.ofNat 8046,memory := memory17 s.memory inv a b n,stack := frame17 inv a b n rest}
def memory18 (mem : ByteArray) (inv : UInt256) (a b n : Nat → UInt256) : ByteArray := HistoricalSearch.CRTMemoryCells.storeCells (memory17 mem inv a b n) (cells17 inv a b n)
def state18 (s : State) (inv : UInt256) (a b n : Nat → UInt256) (rest : List UInt256) : State := {s with pc := UInt256.ofNat 8168,memory := memory18 s.memory inv a b n,stack := frame18 inv a b n rest}
def memory19 (mem : ByteArray) (inv : UInt256) (a b n : Nat → UInt256) : ByteArray := HistoricalSearch.CRTMemoryCells.storeCells (memory18 mem inv a b n) (cells18 inv a b n)
def state19 (s : State) (inv : UInt256) (a b n : Nat → UInt256) (rest : List UInt256) : State := {s with pc := UInt256.ofNat 8292,memory := memory19 s.memory inv a b n,stack := frame19 inv a b n rest}
def memory20 (mem : ByteArray) (inv : UInt256) (a b n : Nat → UInt256) : ByteArray := HistoricalSearch.CRTMemoryCells.storeCells (memory19 mem inv a b n) (cells19 inv a b n)
def state20 (s : State) (inv : UInt256) (a b n : Nat → UInt256) (rest : List UInt256) : State := {s with pc := UInt256.ofNat 8330,memory := memory20 s.memory inv a b n,stack := frame20 inv a b n rest}
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
      simp only [cells0,List.mem_cons,List.mem_nil_iff,or_false] at hc
      )
  exact h.trans (memory0_keeps mem inv a b n start count hs)
theorem memory2_keeps (mem : ByteArray) (inv : UInt256) (a b n : Nat → UInt256)
    (start count : Nat) (hs : (256 ≤ start ∧ start+count ≤ 768) ∨ 1312 ≤ start) :
    MachineState.readPadded (memory2 mem inv a b n) start count =
      MachineState.readPadded mem start count := by
  have h := HistoricalSearch.CRTMemoryCells.readPadded_storeCells
    (memory1 mem inv a b n) (cells1 inv a b n) start count (by
      intro c hc
      simp only [cells1,List.mem_cons,List.mem_nil_iff,or_false] at hc
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
      simp only [cells2,List.mem_cons,List.mem_nil_iff,or_false] at hc
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
      simp only [cells3,List.mem_cons,List.mem_nil_iff,or_false] at hc
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
      simp only [cells4,List.mem_cons,List.mem_nil_iff,or_false] at hc
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
      simp only [cells5,List.mem_cons,List.mem_nil_iff,or_false] at hc
      )
  exact h.trans (memory5_keeps mem inv a b n start count hs)
theorem memory7_keeps (mem : ByteArray) (inv : UInt256) (a b n : Nat → UInt256)
    (start count : Nat) (hs : (256 ≤ start ∧ start+count ≤ 768) ∨ 1312 ≤ start) :
    MachineState.readPadded (memory7 mem inv a b n) start count =
      MachineState.readPadded mem start count := by
  have h := HistoricalSearch.CRTMemoryCells.readPadded_storeCells
    (memory6 mem inv a b n) (cells6 inv a b n) start count (by
      intro c hc
      simp only [cells6,List.mem_cons,List.mem_nil_iff,or_false] at hc
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
      simp only [cells7,List.mem_cons,List.mem_nil_iff,or_false] at hc
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
      simp only [cells8,List.mem_cons,List.mem_nil_iff,or_false] at hc
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
      simp only [cells9,List.mem_cons,List.mem_nil_iff,or_false] at hc
      )
  exact h.trans (memory9_keeps mem inv a b n start count hs)
theorem memory11_keeps (mem : ByteArray) (inv : UInt256) (a b n : Nat → UInt256)
    (start count : Nat) (hs : (256 ≤ start ∧ start+count ≤ 768) ∨ 1312 ≤ start) :
    MachineState.readPadded (memory11 mem inv a b n) start count =
      MachineState.readPadded mem start count := by
  have h := HistoricalSearch.CRTMemoryCells.readPadded_storeCells
    (memory10 mem inv a b n) (cells10 inv a b n) start count (by
      intro c hc
      simp only [cells10,List.mem_cons,List.mem_nil_iff,or_false] at hc
      )
  exact h.trans (memory10_keeps mem inv a b n start count hs)
theorem memory12_keeps (mem : ByteArray) (inv : UInt256) (a b n : Nat → UInt256)
    (start count : Nat) (hs : (256 ≤ start ∧ start+count ≤ 768) ∨ 1312 ≤ start) :
    MachineState.readPadded (memory12 mem inv a b n) start count =
      MachineState.readPadded mem start count := by
  have h := HistoricalSearch.CRTMemoryCells.readPadded_storeCells
    (memory11 mem inv a b n) (cells11 inv a b n) start count (by
      intro c hc
      simp only [cells11,List.mem_cons,List.mem_nil_iff,or_false] at hc
      )
  exact h.trans (memory11_keeps mem inv a b n start count hs)
theorem memory13_keeps (mem : ByteArray) (inv : UInt256) (a b n : Nat → UInt256)
    (start count : Nat) (hs : (256 ≤ start ∧ start+count ≤ 768) ∨ 1312 ≤ start) :
    MachineState.readPadded (memory13 mem inv a b n) start count =
      MachineState.readPadded mem start count := by
  have h := HistoricalSearch.CRTMemoryCells.readPadded_storeCells
    (memory12 mem inv a b n) (cells12 inv a b n) start count (by
      intro c hc
      simp only [cells12,List.mem_cons,List.mem_nil_iff,or_false] at hc
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
      simp only [cells13,List.mem_cons,List.mem_nil_iff,or_false] at hc
      )
  exact h.trans (memory13_keeps mem inv a b n start count hs)
theorem memory15_keeps (mem : ByteArray) (inv : UInt256) (a b n : Nat → UInt256)
    (start count : Nat) (hs : (256 ≤ start ∧ start+count ≤ 768) ∨ 1312 ≤ start) :
    MachineState.readPadded (memory15 mem inv a b n) start count =
      MachineState.readPadded mem start count := by
  have h := HistoricalSearch.CRTMemoryCells.readPadded_storeCells
    (memory14 mem inv a b n) (cells14 inv a b n) start count (by
      intro c hc
      simp only [cells14,List.mem_cons,List.mem_nil_iff,or_false] at hc
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
      simp only [cells15,List.mem_cons,List.mem_nil_iff,or_false] at hc
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
      simp only [cells16,List.mem_cons,List.mem_nil_iff,or_false] at hc
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
      simp only [cells17,List.mem_cons,List.mem_nil_iff,or_false] at hc
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
      simp only [cells18,List.mem_cons,List.mem_nil_iff,or_false] at hc
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
      simp only [cells19,List.mem_cons,List.mem_nil_iff,or_false] at hc
      rcases hc with rfl
      all_goals (dsimp; omega))
  exact h.trans (memory19_keeps mem inv a b n start count hs)
theorem run (s : State) (inv : UInt256) (a b n : Nat → UInt256) (rest : List UInt256)
    (h : Memory0 s.memory inv a b n) (hcap : rest.length ≤ 960)
    (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions program
      {s with pc := UInt256.ofNat 5906,stack := frame0 inv a b n rest} =
      some (state20 s inv a b n rest) := by
  have m0 := h
  have m1 := memory0_output (state0 s inv a b n rest) inv a b n rest m0
  have h0 : runInstructions productColumn0Program {s with pc := UInt256.ofNat 5906,stack := frame0 inv a b n rest} = some (state1 s inv a b n rest) :=
    run0 (state0 s inv a b n rest) inv a b n rest m0 hcap hact
  have m2 := memory1_output (state1 s inv a b n rest) inv a b n rest m1
  have h1 : runInstructions productColumn1Program (state1 s inv a b n rest) = some (state2 s inv a b n rest) := by
    have hx := run1 (state1 s inv a b n rest) inv a b n rest m1 hcap hact
    rw [reset_self (state1 s inv a b n rest) (UInt256.ofNat 6031) (frame1 inv a b n rest) rfl rfl] at hx
    exact hx
  have m3 := memory2_output (state2 s inv a b n rest) inv a b n rest m2
  have h2 : runInstructions productColumn2Program (state2 s inv a b n rest) = some (state3 s inv a b n rest) := by
    have hx := run2 (state2 s inv a b n rest) inv a b n rest m2 hcap hact
    rw [reset_self (state2 s inv a b n rest) (UInt256.ofNat 6157) (frame2 inv a b n rest) rfl rfl] at hx
    exact hx
  have m4 := memory3_output (state3 s inv a b n rest) inv a b n rest m3
  have m5 := memory4_output (state4 s inv a b n rest) inv a b n rest m4
  have m6 := memory5_output (state5 s inv a b n rest) inv a b n rest m5
  have m7 := memory6_output (state6 s inv a b n rest) inv a b n rest m6
  have h6 : runInstructions productColumn6Program (state6 s inv a b n rest) = some (state7 s inv a b n rest) := by
    have hx := run6 (state6 s inv a b n rest) inv a b n rest m6 hcap hact
    rw [reset_self (state6 s inv a b n rest) (UInt256.ofNat 6663) (frame6 inv a b n rest) rfl rfl] at hx
    exact hx
  have m8 := memory7_output (state7 s inv a b n rest) inv a b n rest m7
  have h7 : runInstructions productColumn7Program (state7 s inv a b n rest) = some (state8 s inv a b n rest) := by
    have hx := run7 (state7 s inv a b n rest) inv a b n rest m7 hcap hact
    rw [reset_self (state7 s inv a b n rest) (UInt256.ofNat 6791) (frame7 inv a b n rest) rfl rfl] at hx
    exact hx
  have m9 := memory8_output (state8 s inv a b n rest) inv a b n rest m8
  have h8 : runInstructions productColumn8Program (state8 s inv a b n rest) = some (state9 s inv a b n rest) := by
    have hx := run8 (state8 s inv a b n rest) inv a b n rest m8 hcap hact
    rw [reset_self (state8 s inv a b n rest) (UInt256.ofNat 6918) (frame8 inv a b n rest) rfl rfl] at hx
    exact hx
  have m10 := memory9_output (state9 s inv a b n rest) inv a b n rest m9
  have h9 : runInstructions productColumn9Program (state9 s inv a b n rest) = some (state10 s inv a b n rest) := by
    have hx := run9 (state9 s inv a b n rest) inv a b n rest m9 hcap hact
    rw [reset_self (state9 s inv a b n rest) (UInt256.ofNat 7045) (frame9 inv a b n rest) rfl rfl] at hx
    exact hx
  have m11 := memory10_output (state10 s inv a b n rest) inv a b n rest m10
  have h10 : runInstructions productColumn10Program (state10 s inv a b n rest) = some (state11 s inv a b n rest) := by
    have hx := run10 (state10 s inv a b n rest) inv a b n rest m10 hcap hact
    rw [reset_self (state10 s inv a b n rest) (UInt256.ofNat 7172) (frame10 inv a b n rest) rfl rfl] at hx
    exact hx
  have m12 := memory11_output (state11 s inv a b n rest) inv a b n rest m11
  have h11 : runInstructions productColumn11Program (state11 s inv a b n rest) = some (state12 s inv a b n rest) := by
    have hx := run11 (state11 s inv a b n rest) inv a b n rest m11 hcap hact
    rw [reset_self (state11 s inv a b n rest) (UInt256.ofNat 7301) (frame11 inv a b n rest) rfl rfl] at hx
    exact hx
  have m13 := memory12_output (state12 s inv a b n rest) inv a b n rest m12
  have h12 : runInstructions productColumn12Program (state12 s inv a b n rest) = some (state13 s inv a b n rest) := by
    have hx := run12 (state12 s inv a b n rest) inv a b n rest m12 hcap hact
    rw [reset_self (state12 s inv a b n rest) (UInt256.ofNat 7428) (frame12 inv a b n rest) rfl rfl] at hx
    exact hx
  have m14 := memory13_output (state13 s inv a b n rest) inv a b n rest m13
  have h13 : runInstructions productColumn13Program (state13 s inv a b n rest) = some (state14 s inv a b n rest) := by
    have hx := run13 (state13 s inv a b n rest) inv a b n rest m13 hcap hact
    rw [reset_self (state13 s inv a b n rest) (UInt256.ofNat 7550) (frame13 inv a b n rest) rfl rfl] at hx
    exact hx
  have m15 := memory14_output (state14 s inv a b n rest) inv a b n rest m14
  have h14 : runInstructions productColumn14Program (state14 s inv a b n rest) = some (state15 s inv a b n rest) := by
    have hx := run14 (state14 s inv a b n rest) inv a b n rest m14 hcap hact
    rw [reset_self (state14 s inv a b n rest) (UInt256.ofNat 7667) (frame14 inv a b n rest) rfl rfl] at hx
    exact hx
  have m16 := memory15_output (state15 s inv a b n rest) inv a b n rest m15
  have m17 := memory16_output (state16 s inv a b n rest) inv a b n rest m16
  have m18 := memory17_output (state17 s inv a b n rest) inv a b n rest m17
  have m19 := memory18_output (state18 s inv a b n rest) inv a b n rest m18
  have m20 := memory19_output (state19 s inv a b n rest) inv a b n rest m19
  have he3 : CycleSubmission.Prepared.ProductGroup8130.eval3 (state3 s inv a b n rest) = (state4 s inv a b n rest) := by
    change productColumn3Model (state3 s inv a b n rest) ((n 2)) ((((productQ1 inv a b n) * (n 3)) + (((productQ0 inv a b n) * (n 4)) + (((b 0) * (a 4)) + (((b 1) * (a 3)) + (((b 2) * (a 2)) + (((b 3) * (a 1)) + (((b 4) * (a 0)) + (productC4 inv a b n))))))))) (((UInt256.mulMod (b 0) (a 4) P) + ((UInt256.mulMod (b 1) (a 3) P) + ((UInt256.mulMod (b 2) (a 2) P) + ((UInt256.mulMod (b 3) (a 1) P) + ((UInt256.mulMod (b 4) (a 0) P) + (productC4 inv a b n))))))) ((n 2)) ((n 6)) ((n 4)) ((a 1)) ((a 2)) ((n 5)) ((productQ1 inv a b n)) (P) ((productQ0 inv a b n)) ((n 1)) ((UInt256.ofNat (2^240-1))) ((n 0)) ((n 3)) ((a 8)) rest = (state4 s inv a b n rest)
    exact model3_eq (state3 s inv a b n rest) inv a b n rest m3
  have he4 : CycleSubmission.Prepared.ProductGroup8130.eval4 (state4 s inv a b n rest) = (state5 s inv a b n rest) := by
    change productColumn4Model (state4 s inv a b n rest) ((b 1)) ((a 4)) ((((b 2) * (a 3)) + (((b 3) * (a 2)) + (((b 4) * (a 1)) + (((b 5) * (a 0)) + (productC5 inv a b n)))))) ((a 4)) (P) (((UInt256.mulMod (b 2) (a 3) P) + ((UInt256.mulMod (b 3) (a 2) P) + ((UInt256.mulMod (b 4) (a 1) P) + ((UInt256.mulMod (b 5) (a 0) P) + (productC5 inv a b n)))))) ((b 1)) ((n 2)) ((n 6)) ((n 4)) ((a 1)) ((a 2)) ((n 5)) ((productQ1 inv a b n)) (P) ((productQ0 inv a b n)) ((n 1)) ((UInt256.ofNat (2^240-1))) ((n 0)) ((n 3)) ((a 8)) rest = (state5 s inv a b n rest)
    exact model4_eq (state4 s inv a b n rest) inv a b n rest m4
  have he5 : CycleSubmission.Prepared.ProductGroup8130.eval5 (state5 s inv a b n rest) = (state6 s inv a b n rest) := by
    change productColumn5Model (state5 s inv a b n rest) (((b 5) * (a 1))) ((((b 6) * (a 0)) + (productC6 inv a b n))) ((a 1)) (P) (((UInt256.mulMod (b 6) (a 0) P) + (productC6 inv a b n))) ((b 5)) ((n 2)) ((n 6)) ((n 4)) ((a 1)) ((a 2)) ((n 5)) ((productQ1 inv a b n)) (P) ((productQ0 inv a b n)) ((n 1)) ((UInt256.ofNat (2^240-1))) ((n 0)) ((n 3)) ((a 8)) rest = (state6 s inv a b n rest)
    exact model5_eq (state5 s inv a b n rest) inv a b n rest m5
  have hg3 : runInstructions CycleSubmission.Prepared.ProductGroup8130.newProgram (state3 s inv a b n rest) = some (state6 s inv a b n rest) := by
    have raw := (CycleSubmission.Prepared.ProductGroup8130.new_run (state3 s inv a b n rest) ((n 2)) ((((productQ1 inv a b n) * (n 3)) + (((productQ0 inv a b n) * (n 4)) + (((b 0) * (a 4)) + (((b 1) * (a 3)) + (((b 2) * (a 2)) + (((b 3) * (a 1)) + (((b 4) * (a 0)) + (productC4 inv a b n))))))))) (((UInt256.mulMod (b 0) (a 4) P) + ((UInt256.mulMod (b 1) (a 3) P) + ((UInt256.mulMod (b 2) (a 2) P) + ((UInt256.mulMod (b 3) (a 1) P) + ((UInt256.mulMod (b 4) (a 0) P) + (productC4 inv a b n))))))) ((n 2)) ((n 6)) ((n 4)) ((a 1)) ((a 2)) ((n 5)) ((productQ1 inv a b n)) (P) ((productQ0 inv a b n)) ((n 1)) ((UInt256.ofNat (2^240-1))) ((n 0)) ((n 3)) ((a 8)) rest hcap hact).trans
      (congrArg some (CycleSubmission.Prepared.ProductGroup8130.same_state (state3 s inv a b n rest) ((n 2)) ((((productQ1 inv a b n) * (n 3)) + (((productQ0 inv a b n) * (n 4)) + (((b 0) * (a 4)) + (((b 1) * (a 3)) + (((b 2) * (a 2)) + (((b 3) * (a 1)) + (((b 4) * (a 0)) + (productC4 inv a b n))))))))) (((UInt256.mulMod (b 0) (a 4) P) + ((UInt256.mulMod (b 1) (a 3) P) + ((UInt256.mulMod (b 2) (a 2) P) + ((UInt256.mulMod (b 3) (a 1) P) + ((UInt256.mulMod (b 4) (a 0) P) + (productC4 inv a b n))))))) ((n 2)) ((n 6)) ((n 4)) ((a 1)) ((a 2)) ((n 5)) ((productQ1 inv a b n)) (P) ((productQ0 inv a b n)) ((n 1)) ((UInt256.ofNat (2^240-1))) ((n 0)) ((n 3)) ((a 8)) rest).symm)
    rw [CycleSubmission.Prepared.ProductGroup8130.old_eval] at raw
    change runInstructions CycleSubmission.Prepared.ProductGroup8130.newProgram (state3 s inv a b n rest) = some (CycleSubmission.Prepared.ProductGroup8130.eval5 (CycleSubmission.Prepared.ProductGroup8130.eval4 (CycleSubmission.Prepared.ProductGroup8130.eval3 ((state3 s inv a b n rest))))) at raw
    rw [he3,he4,he5] at raw
    exact raw
  have he15 : CycleSubmission.Prepared.ProductGroup9668.eval15 (state15 s inv a b n rest) = (state16 s inv a b n rest) := by
    change productColumn15Model (state15 s inv a b n rest) ((productQ7 inv a b n)) ((((n 5) * (productQ6 inv a b n)) + (((n 6) * (productQ5 inv a b n)) + (((n 7) * (productQ4 inv a b n)) + (((n 8) * (productQ3 inv a b n)) + (((b 3) * (a 8)) + (((b 4) * (a 7)) + (((b 5) * (a 6)) + (((b 6) * (a 5)) + (((b 7) * (a 4)) + (((b 8) * (a 3)) + (productC11 inv a b n)))))))))))) (((UInt256.mulMod (b 3) (a 8) P) + ((UInt256.mulMod (b 4) (a 7) P) + ((UInt256.mulMod (b 5) (a 6) P) + ((UInt256.mulMod (b 6) (a 5) P) + ((UInt256.mulMod (b 7) (a 4) P) + ((UInt256.mulMod (b 8) (a 3) P) + (productC11 inv a b n)))))))) ((a 8)) ((n 6)) ((n 4)) ((productQ6 inv a b n)) ((productQ5 inv a b n)) ((n 5)) ((n 7)) (P) ((n 8)) ((productQ7 inv a b n)) ((UInt256.ofNat (2^240-1))) ((productQ8 inv a b n)) ((n 3)) ((n 2)) rest = (state16 s inv a b n rest)
    exact model15_eq (state15 s inv a b n rest) inv a b n rest m15
  have he16 : CycleSubmission.Prepared.ProductGroup9668.eval16 (state16 s inv a b n rest) = (state17 s inv a b n rest) := by
    change productColumn16Model (state16 s inv a b n rest) (((UInt256.mulMod (b 5) (a 7) P) + ((UInt256.mulMod (b 6) (a 6) P) + ((UInt256.mulMod (b 7) (a 5) P) + ((UInt256.mulMod (b 8) (a 4) P) + (productC12 inv a b n)))))) ((((b 5) * (a 7)) + (((b 6) * (a 6)) + (((b 7) * (a 5)) + (((b 8) * (a 4)) + (productC12 inv a b n)))))) ((a 8)) ((n 6)) ((n 4)) ((productQ6 inv a b n)) ((productQ5 inv a b n)) ((n 5)) ((n 7)) (P) ((n 8)) ((productQ7 inv a b n)) ((UInt256.ofNat (2^240-1))) ((productQ8 inv a b n)) ((n 3)) ((n 2)) rest = (state17 s inv a b n rest)
    exact model16_eq (state16 s inv a b n rest) inv a b n rest m16
  have he17 : CycleSubmission.Prepared.ProductGroup9668.eval17 (state17 s inv a b n rest) = (state18 s inv a b n rest) := by
    change productColumn17Model (state17 s inv a b n rest) ((((b 7) * (a 6)) + (((b 8) * (a 5)) + (productC13 inv a b n)))) ((a 7)) (P) (((UInt256.mulMod (b 7) (a 6) P) + ((UInt256.mulMod (b 8) (a 5) P) + (productC13 inv a b n)))) ((b 6)) ((a 8)) ((n 6)) ((n 4)) ((productQ6 inv a b n)) ((productQ5 inv a b n)) ((n 5)) ((n 7)) (P) ((n 8)) ((productQ7 inv a b n)) ((UInt256.ofNat (2^240-1))) ((productQ8 inv a b n)) ((n 3)) ((n 2)) rest = (state18 s inv a b n rest)
    exact model17_eq (state17 s inv a b n rest) inv a b n rest m17
  have hg15 : runInstructions CycleSubmission.Prepared.ProductGroup9668.newProgram (state15 s inv a b n rest) = some (state18 s inv a b n rest) := by
    have raw := (CycleSubmission.Prepared.ProductGroup9668.new_run (state15 s inv a b n rest) ((productQ7 inv a b n)) ((((n 5) * (productQ6 inv a b n)) + (((n 6) * (productQ5 inv a b n)) + (((n 7) * (productQ4 inv a b n)) + (((n 8) * (productQ3 inv a b n)) + (((b 3) * (a 8)) + (((b 4) * (a 7)) + (((b 5) * (a 6)) + (((b 6) * (a 5)) + (((b 7) * (a 4)) + (((b 8) * (a 3)) + (productC11 inv a b n)))))))))))) (((UInt256.mulMod (b 3) (a 8) P) + ((UInt256.mulMod (b 4) (a 7) P) + ((UInt256.mulMod (b 5) (a 6) P) + ((UInt256.mulMod (b 6) (a 5) P) + ((UInt256.mulMod (b 7) (a 4) P) + ((UInt256.mulMod (b 8) (a 3) P) + (productC11 inv a b n)))))))) ((a 8)) ((n 6)) ((n 4)) ((productQ6 inv a b n)) ((productQ5 inv a b n)) ((n 5)) ((n 7)) (P) ((n 8)) ((productQ7 inv a b n)) ((UInt256.ofNat (2^240-1))) ((productQ8 inv a b n)) ((n 3)) ((n 2)) rest hcap hact).trans
      (congrArg some (CycleSubmission.Prepared.ProductGroup9668.same_state (state15 s inv a b n rest) ((productQ7 inv a b n)) ((((n 5) * (productQ6 inv a b n)) + (((n 6) * (productQ5 inv a b n)) + (((n 7) * (productQ4 inv a b n)) + (((n 8) * (productQ3 inv a b n)) + (((b 3) * (a 8)) + (((b 4) * (a 7)) + (((b 5) * (a 6)) + (((b 6) * (a 5)) + (((b 7) * (a 4)) + (((b 8) * (a 3)) + (productC11 inv a b n)))))))))))) (((UInt256.mulMod (b 3) (a 8) P) + ((UInt256.mulMod (b 4) (a 7) P) + ((UInt256.mulMod (b 5) (a 6) P) + ((UInt256.mulMod (b 6) (a 5) P) + ((UInt256.mulMod (b 7) (a 4) P) + ((UInt256.mulMod (b 8) (a 3) P) + (productC11 inv a b n)))))))) ((a 8)) ((n 6)) ((n 4)) ((productQ6 inv a b n)) ((productQ5 inv a b n)) ((n 5)) ((n 7)) (P) ((n 8)) ((productQ7 inv a b n)) ((UInt256.ofNat (2^240-1))) ((productQ8 inv a b n)) ((n 3)) ((n 2)) rest).symm)
    rw [CycleSubmission.Prepared.ProductGroup9668.old_eval] at raw
    change runInstructions CycleSubmission.Prepared.ProductGroup9668.newProgram (state15 s inv a b n rest) = some (CycleSubmission.Prepared.ProductGroup9668.eval17 (CycleSubmission.Prepared.ProductGroup9668.eval16 (CycleSubmission.Prepared.ProductGroup9668.eval15 ((state15 s inv a b n rest))))) at raw
    rw [he15,he16,he17] at raw
    exact raw
  have he18 : CycleSubmission.Prepared.ProductGroup10052.eval18 (state18 s inv a b n rest) = (state19 s inv a b n rest) := by
    change productColumn18Model (state18 s inv a b n rest) ((b 6)) ((a 8)) ((((b 7) * (a 7)) + (((b 8) * (a 6)) + (productC14 inv a b n)))) ((a 8)) (P) (((UInt256.mulMod (b 7) (a 7) P) + ((UInt256.mulMod (b 8) (a 6) P) + (productC14 inv a b n)))) ((b 6)) ((a 8)) ((n 6)) ((n 4)) ((productQ6 inv a b n)) ((productD2 inv a b n)) ((n 5)) ((n 7)) (P) ((n 8)) ((productQ7 inv a b n)) ((UInt256.ofNat (2^240-1))) ((productQ8 inv a b n)) ((n 3)) ((n 2)) rest = (state19 s inv a b n rest)
    exact model18_eq (state18 s inv a b n rest) inv a b n rest m18
  have he19 : CycleSubmission.Prepared.ProductGroup10052.eval19 (state19 s inv a b n rest) = (state20 s inv a b n rest) := by
    change productColumn19Model (state19 s inv a b n rest) ((productC16 inv a b n)) ((b 8)) ((a 8)) ((n 6)) ((n 4)) ((productD1 inv a b n)) ((productD2 inv a b n)) ((n 5)) ((n 7)) (P) ((n 8)) ((productQ7 inv a b n)) ((UInt256.ofNat (2^240-1))) ((productQ8 inv a b n)) ((n 3)) ((n 2)) rest = (state20 s inv a b n rest)
    exact model19_eq (state19 s inv a b n rest) inv a b n rest m19
  have hg18 : runInstructions CycleSubmission.Prepared.ProductGroup10052.newProgram (state18 s inv a b n rest) = some (state20 s inv a b n rest) := by
    have raw := (CycleSubmission.Prepared.ProductGroup10052.new_run (state18 s inv a b n rest) ((b 6)) ((a 8)) ((((b 7) * (a 7)) + (((b 8) * (a 6)) + (productC14 inv a b n)))) ((a 8)) (P) (((UInt256.mulMod (b 7) (a 7) P) + ((UInt256.mulMod (b 8) (a 6) P) + (productC14 inv a b n)))) ((b 6)) ((a 8)) ((n 6)) ((n 4)) ((productQ6 inv a b n)) ((productD2 inv a b n)) ((n 5)) ((n 7)) (P) ((n 8)) ((productQ7 inv a b n)) ((UInt256.ofNat (2^240-1))) ((productQ8 inv a b n)) ((n 3)) ((n 2)) rest hcap hact).trans
      (congrArg some (CycleSubmission.Prepared.ProductGroup10052.same_state (state18 s inv a b n rest) ((b 6)) ((a 8)) ((((b 7) * (a 7)) + (((b 8) * (a 6)) + (productC14 inv a b n)))) ((a 8)) (P) (((UInt256.mulMod (b 7) (a 7) P) + ((UInt256.mulMod (b 8) (a 6) P) + (productC14 inv a b n)))) ((b 6)) ((a 8)) ((n 6)) ((n 4)) ((productQ6 inv a b n)) ((productD2 inv a b n)) ((n 5)) ((n 7)) (P) ((n 8)) ((productQ7 inv a b n)) ((UInt256.ofNat (2^240-1))) ((productQ8 inv a b n)) ((n 3)) ((n 2)) rest).symm)
    rw [CycleSubmission.Prepared.ProductGroup10052.old_eval] at raw
    change runInstructions CycleSubmission.Prepared.ProductGroup10052.newProgram (state18 s inv a b n rest) = some (CycleSubmission.Prepared.ProductGroup10052.eval19 (CycleSubmission.Prepared.ProductGroup10052.eval18 ((state18 s inv a b n rest)))) at raw
    rw [he18,he19] at raw
    exact raw
  exact (runInstructions_append_some _ _ _ _ _ h0 (runInstructions_append_some _ _ _ _ _ h1 (runInstructions_append_some _ _ _ _ _ h2 (runInstructions_append_some _ _ _ _ _ hg3 (runInstructions_append_some _ _ _ _ _ h6 (runInstructions_append_some _ _ _ _ _ h7 (runInstructions_append_some _ _ _ _ _ h8 (runInstructions_append_some _ _ _ _ _ h9 (runInstructions_append_some _ _ _ _ _ h10 (runInstructions_append_some _ _ _ _ _ h11 (runInstructions_append_some _ _ _ _ _ h12 (runInstructions_append_some _ _ _ _ _ h13 (runInstructions_append_some _ _ _ _ _ h14 (runInstructions_append_some _ _ _ _ _ hg15 hg18))))))))))))))
#print axioms run
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
  exact ⟨m.at768,m.at32,m.at64,m.at96,m.at128,m.at160,m.at1344,m.at1376⟩
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
def block : Block Artifact.artifact .Osaka 5906 program :=
  WindowTwentyOneSlice.block CycleSubmission.Artifact.wellFormed 4333 2040 5906 program
    (by change 4333+2040 ≤ CycleSubmission.Artifact.instructions.length; rw [CycleSubmission.Artifact.instructionCount]; decide)
    (by rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)
noncomputable def gasSteps (s : State) (inv : UInt256) (a b n : Nat → UInt256) (rest : List UInt256)
    (env : Environment Artifact.artifact .Osaka s)
    (h : Memory0 s.memory inv a b n) (hcap : rest.length ≤ 960)
    (hact : 88 ≤ s.activeWords.toNat) :
    GasSteps {s with pc := UInt256.ofNat 5906,stack := frame0 inv a b n rest}
      (state20 s inv a b n rest) :=
  block.steps
    (s := {s with pc := UInt256.ofNat 5906,stack := frame0 inv a b n rest})
    (env.transfer rfl rfl) rfl (run s inv a b n rest h hcap hact)
noncomputable def correct (s : State) (inv : UInt256) (a b n : Nat → UInt256) (rest : List UInt256)
    (env : Environment Artifact.artifact .Osaka s)
    (h : Memory0 s.memory inv a b n) (hcap : rest.length ≤ 960)
    (hact : 88 ≤ s.activeWords.toNat)
    (ha : ∀ i < 9,(a i).toNat < radix)
    (hb : ∀ i < 9,(b i).toNat < radix)
    (hn : ∀ i < 9,(n i).toNat < radix)
    (N : Nat) (hn0 : (n 0).toNat = N % radix)
    (hinv : (N*inv.toNat+1) % 2^256 = 0) :
    PSigma (fun _ : GasSteps
      {s with pc := UInt256.ofNat 5906,stack := frame0 inv a b n rest}
      (state20 s inv a b n rest) =>
    HistoricalSearch.MixedMontgomery.weighted radix 9
      (fun i => (outputWord (state20 s inv a b n rest) i).toNat) * radix^9 =
    HistoricalSearch.MixedMontgomery.weighted radix 9 (fun i => (a i).toNat) *
    HistoricalSearch.MixedMontgomery.weighted radix 9 (fun i => (b i).toNat) +
    HistoricalSearch.MixedMontgomery.weighted radix 9 (fun i => (productq inv a b n i).toNat) *
    HistoricalSearch.MixedMontgomery.weighted radix 9 (fun i => (n i).toNat)) := by
  refine ⟨gasSteps s inv a b n rest env h hcap hact,?_⟩
  rw [output_value s inv a b n rest h]
  exact (productTrace inv a b n).exact_product ha hb hn N hn0 hinv
end CycleSubmission.ProductExecution
