import Challenge.EvmProof.Stepper
import Challenge.Modexp.Submission.Proofs.Cycle.DoubleInput
set_option warningAsError true
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 16000000
set_option maxRecDepth 50000
namespace CycleSubmission.DoubleInputColumn
open EvmSemantics EvmSemantics.EVM YulEvmCompiler
open Challenge.EvmProof.Word Challenge.EvmProof.Stepper
local notation "W" => UInt256
local notation "N" => UInt256.ofNat
def runInstructions : List Instr → State → Option State
  | [], s => some s
  | i :: is, s => do
      let next ← runInstr i s
      runInstructions is next

theorem run_append (a b : List Instr) (s : State) :
    runInstructions (a++b) s = (runInstructions a s).bind (runInstructions b) := by
  induction a generalizing s with
  | nil => rfl
  | cons i is ih =>
    simp only [List.cons_append, runInstructions]
    cases runInstr i s with
    | none => rfl
    | some t => exact ih t

theorem run_append_some (a b : List Instr) (s m t : State)
    (ha : runInstructions a s = some m) (hb : runInstructions b m = some t) :
    runInstructions (a++b) s = some t := by
  rw [run_append, ha]
  exact hb

theorem active_fix (s : State) (off sz : Nat) (hsz : sz ≠ 0)
    (hoff : off+sz ≤ 2816) (hact : 88 ≤ s.activeWords.toNat) :
    N (MachineState.activeWordsAfter s.activeWords.toNat off sz) = s.activeWords := by
  have hle : (off+sz-1)/32+1 ≤ s.activeWords.toNat := by omega
  simp only [MachineState.activeWordsAfter, hsz, if_false, Nat.max_eq_left hle]
  exact (word_eq_ofNat_toNat _).symm

def p0 : List Instr :=
  [.push 2 768,
   .op .MLOAD,
   .op (.Dup ⟨8, by decide⟩),
   .op (.Dup ⟨1, by decide⟩)]

def m0 (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 : W) (rest : List UInt256) : State :=
  let v0 : W := MachineState.readWord s.memory 768
  {s with pc := N 5718, memory := s.memory, stack := v0 :: x7 :: v0 :: x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: rest}

theorem run0 (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions p0
      {s with pc := N 5712, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: rest} =
        some (m0 s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 rest) := by
  have capacity (j : Nat) (hj : j ≤ 30) : rest.length+j < 1024 := by omega
  have ha768 : (768 : W).toNat = 768 := rfl
  have ha2720 : (2720 : W).toNat = 2720 := rfl
  have hf768 := CycleSubmission.DoubleInputColumn.active_fix s 768 32 (by decide) (by norm_num) hact
  have hf2720 := CycleSubmission.DoubleInputColumn.active_fix s 2720 32 (by decide) (by norm_num) hact
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  simp [hz, hzn, p0, m0, runInstructions, runInstr,
    List.exchange, succ_ofNat_mod, ofNat_add_mod, Nat.add_assoc,
    State.activeWordsAfterUInt256, literal_eq_ofNat,
    capacity, ha768, ha2720, hf768, hf2720]

def p1 : List Instr :=
  [.op (.Dup ⟨0, by decide⟩),
   .op (.Dup ⟨0, by decide⟩),
   .op .MUL]

def m1 (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 : W) (rest : List UInt256) : State :=
  let v0 : W := x0 * x0
  {s with pc := N 5721, memory := s.memory, stack := v0 :: x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: rest}

theorem run1 (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions p1
      {s with pc := N 5718, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: rest} =
        some (m1 s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 rest) := by
  have capacity (j : Nat) (hj : j ≤ 30) : rest.length+j < 1024 := by omega
  have ha768 : (768 : W).toNat = 768 := rfl
  have ha2720 : (2720 : W).toNat = 2720 := rfl
  have hf768 := CycleSubmission.DoubleInputColumn.active_fix s 768 32 (by decide) (by norm_num) hact
  have hf2720 := CycleSubmission.DoubleInputColumn.active_fix s 2720 32 (by decide) (by norm_num) hact
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  simp [hz, hzn, p1, m1, runInstructions, runInstr,
    List.exchange, succ_ofNat_mod, ofNat_add_mod, Nat.add_assoc,
    State.activeWordsAfterUInt256, literal_eq_ofNat,
    capacity, ha768, ha2720, hf768, hf2720]

def p2 : List Instr :=
  [.push 2 2720,
   .op .MLOAD,
   .op .MUL,
   .op (.Dup ⟨14, by decide⟩)]

def m2 (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 : W) (rest : List UInt256) : State :=
  let v0 : W := MachineState.readWord s.memory 2720
  let v1 : W := v0 * x0
  {s with pc := N 5727, memory := s.memory, stack := x14 :: v1 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: rest}

theorem run2 (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions p2
      {s with pc := N 5721, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: rest} =
        some (m2 s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 rest) := by
  have capacity (j : Nat) (hj : j ≤ 30) : rest.length+j < 1024 := by omega
  have ha768 : (768 : W).toNat = 768 := rfl
  have ha2720 : (2720 : W).toNat = 2720 := rfl
  have hf768 := CycleSubmission.DoubleInputColumn.active_fix s 768 32 (by decide) (by norm_num) hact
  have hf2720 := CycleSubmission.DoubleInputColumn.active_fix s 2720 32 (by decide) (by norm_num) hact
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  simp [hz, hzn, p2, m2, runInstructions, runInstr,
    List.exchange, succ_ofNat_mod, ofNat_add_mod, Nat.add_assoc,
    State.activeWordsAfterUInt256, literal_eq_ofNat,
    capacity, ha768, ha2720, hf768, hf2720]

def p3 : List Instr :=
  [.op .AND,
   .op (.Swap ⟨11, by decide⟩),
   .op .POP,
   .op (.Dup ⟨10, by decide⟩)]

def m3 (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 : W) (rest : List UInt256) : State :=
  let v0 : W := UInt256.land x0 x1
  {s with pc := N 5731, memory := s.memory, stack := x12 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: v0 :: x14 :: x15 :: x16 :: x17 :: x18 :: rest}

theorem run3 (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions p3
      {s with pc := N 5727, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: x18 :: rest} =
        some (m3 s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 rest) := by
  have capacity (j : Nat) (hj : j ≤ 30) : rest.length+j < 1024 := by omega
  have ha768 : (768 : W).toNat = 768 := rfl
  have ha2720 : (2720 : W).toNat = 2720 := rfl
  have hf768 := CycleSubmission.DoubleInputColumn.active_fix s 768 32 (by decide) (by norm_num) hact
  have hf2720 := CycleSubmission.DoubleInputColumn.active_fix s 2720 32 (by decide) (by norm_num) hact
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  simp [hz, hzn, p3, m3, runInstructions, runInstr,
    List.exchange, succ_ofNat_mod, ofNat_add_mod, Nat.add_assoc,
    State.activeWordsAfterUInt256, literal_eq_ofNat,
    capacity, ha768, ha2720, hf768, hf2720]

def p4 : List Instr :=
  [.op (.Swap ⟨2, by decide⟩),
   .op .MULMOD,
   .op (.Dup ⟨1, by decide⟩),
   .op (.Dup ⟨11, by decide⟩)]

def m4 (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 : W) (rest : List UInt256) : State :=
  let v0 : W := UInt256.mulMod x3 x1 x2
  {s with pc := N 5735, memory := s.memory, stack := x12 :: x0 :: v0 :: x0 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: rest}

theorem run4 (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions p4
      {s with pc := N 5731, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: rest} =
        some (m4 s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 rest) := by
  have capacity (j : Nat) (hj : j ≤ 30) : rest.length+j < 1024 := by omega
  have ha768 : (768 : W).toNat = 768 := rfl
  have ha2720 : (2720 : W).toNat = 2720 := rfl
  have hf768 := CycleSubmission.DoubleInputColumn.active_fix s 768 32 (by decide) (by norm_num) hact
  have hf2720 := CycleSubmission.DoubleInputColumn.active_fix s 2720 32 (by decide) (by norm_num) hact
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  simp [hz, hzn, p4, m4, runInstructions, runInstr,
    List.exchange, succ_ofNat_mod, ofNat_add_mod, Nat.add_assoc,
    State.activeWordsAfterUInt256, literal_eq_ofNat,
    capacity, ha768, ha2720, hf768, hf2720]

def p5 : List Instr :=
  [.op (.Dup ⟨15, by decide⟩),
   .op .MULMOD,
   .op .ADD,
   .push 3 2048]

def m5 (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 : W) (rest : List UInt256) : State :=
  let v0 : W := UInt256.mulMod x15 x0 x1
  let v1 : W := v0 + x2
  {s with pc := N 5742, memory := s.memory, stack := (N 2048) :: v1 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: rest}

theorem run5 (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions p5
      {s with pc := N 5735, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: rest} =
        some (m5 s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 rest) := by
  have capacity (j : Nat) (hj : j ≤ 30) : rest.length+j < 1024 := by omega
  have ha768 : (768 : W).toNat = 768 := rfl
  have ha2720 : (2720 : W).toNat = 2720 := rfl
  have hf768 := CycleSubmission.DoubleInputColumn.active_fix s 768 32 (by decide) (by norm_num) hact
  have hf2720 := CycleSubmission.DoubleInputColumn.active_fix s 2720 32 (by decide) (by norm_num) hact
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  simp [hz, hzn, p5, m5, runInstructions, runInstr,
    List.exchange, succ_ofNat_mod, ofNat_add_mod, Nat.add_assoc,
    State.activeWordsAfterUInt256, literal_eq_ofNat,
    capacity, ha768, ha2720, hf768, hf2720]

def p6 : List Instr :=
  [.op .MULMOD,
   .push 2 768,
   .op .MLOAD,
   .op (.Dup ⟨0, by decide⟩)]

def m6 (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 : W) (rest : List UInt256) : State :=
  let v0 : W := UInt256.mulMod x0 x1 x2
  let v1 : W := MachineState.readWord s.memory 768
  {s with pc := N 5748, memory := s.memory, stack := v1 :: v1 :: v0 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: rest}

theorem run6 (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions p6
      {s with pc := N 5742, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: rest} =
        some (m6 s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 rest) := by
  have capacity (j : Nat) (hj : j ≤ 30) : rest.length+j < 1024 := by omega
  have ha768 : (768 : W).toNat = 768 := rfl
  have ha2720 : (2720 : W).toNat = 2720 := rfl
  have hf768 := CycleSubmission.DoubleInputColumn.active_fix s 768 32 (by decide) (by norm_num) hact
  have hf2720 := CycleSubmission.DoubleInputColumn.active_fix s 2720 32 (by decide) (by norm_num) hact
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  simp [hz, hzn, p6, m6, runInstructions, runInstr,
    List.exchange, succ_ofNat_mod, ofNat_add_mod, Nat.add_assoc,
    State.activeWordsAfterUInt256, literal_eq_ofNat,
    capacity, ha768, ha2720, hf768, hf2720]

def p7 : List Instr :=
  [.op .ADD,
   .op (.Dup ⟨9, by decide⟩),
   .op (.Dup ⟨1, by decide⟩),
   .op (.Dup ⟨7, by decide⟩)]

def m7 (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 : W) (rest : List UInt256) : State :=
  let v0 : W := x0 + x1
  {s with pc := N 5752, memory := s.memory, stack := x6 :: v0 :: x10 :: v0 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: rest}

theorem run7 (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions p7
      {s with pc := N 5748, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: rest} =
        some (m7 s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 rest) := by
  have capacity (j : Nat) (hj : j ≤ 30) : rest.length+j < 1024 := by omega
  have ha768 : (768 : W).toNat = 768 := rfl
  have ha2720 : (2720 : W).toNat = 2720 := rfl
  have hf768 := CycleSubmission.DoubleInputColumn.active_fix s 768 32 (by decide) (by norm_num) hact
  have hf2720 := CycleSubmission.DoubleInputColumn.active_fix s 2720 32 (by decide) (by norm_num) hact
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  simp [hz, hzn, p7, m7, runInstructions, runInstr,
    List.exchange, succ_ofNat_mod, ofNat_add_mod, Nat.add_assoc,
    State.activeWordsAfterUInt256, literal_eq_ofNat,
    capacity, ha768, ha2720, hf768, hf2720]

def p8 : List Instr :=
  [.op .MULMOD,
   .op (.Swap ⟨0, by decide⟩),
   .op (.Dup ⟨6, by decide⟩),
   .op .MUL]

def m8 (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 : W) (rest : List UInt256) : State :=
  let v0 : W := UInt256.mulMod x0 x1 x2
  let v1 : W := x8 * x3
  {s with pc := N 5756, memory := s.memory, stack := v1 :: v0 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: x18 :: rest}

theorem run8 (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions p8
      {s with pc := N 5752, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: x18 :: rest} =
        some (m8 s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 rest) := by
  have capacity (j : Nat) (hj : j ≤ 30) : rest.length+j < 1024 := by omega
  have ha768 : (768 : W).toNat = 768 := rfl
  have ha2720 : (2720 : W).toNat = 2720 := rfl
  have hf768 := CycleSubmission.DoubleInputColumn.active_fix s 768 32 (by decide) (by norm_num) hact
  have hf2720 := CycleSubmission.DoubleInputColumn.active_fix s 2720 32 (by decide) (by norm_num) hact
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  simp [hz, hzn, p8, m8, runInstructions, runInstr,
    List.exchange, succ_ofNat_mod, ofNat_add_mod, Nat.add_assoc,
    State.activeWordsAfterUInt256, literal_eq_ofNat,
    capacity, ha768, ha2720, hf768, hf2720]

def p9 : List Instr :=
  [.op (.Dup ⟨2, by decide⟩),
   .op .ADD,
   .op (.Dup ⟨11, by decide⟩),
   .op (.Dup ⟨13, by decide⟩)]

def m9 (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 : W) (rest : List UInt256) : State :=
  let v0 : W := x2 + x0
  {s with pc := N 5760, memory := s.memory, stack := x12 :: x11 :: v0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: rest}

theorem run9 (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions p9
      {s with pc := N 5756, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: rest} =
        some (m9 s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 rest) := by
  have capacity (j : Nat) (hj : j ≤ 30) : rest.length+j < 1024 := by omega
  have ha768 : (768 : W).toNat = 768 := rfl
  have ha2720 : (2720 : W).toNat = 2720 := rfl
  have hf768 := CycleSubmission.DoubleInputColumn.active_fix s 768 32 (by decide) (by norm_num) hact
  have hf2720 := CycleSubmission.DoubleInputColumn.active_fix s 2720 32 (by decide) (by norm_num) hact
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  simp [hz, hzn, p9, m9, runInstructions, runInstr,
    List.exchange, succ_ofNat_mod, ofNat_add_mod, Nat.add_assoc,
    State.activeWordsAfterUInt256, literal_eq_ofNat,
    capacity, ha768, ha2720, hf768, hf2720]

def p10 : List Instr :=
  [.op .MUL,
   .op .ADD,
   .op (.Swap ⟨1, by decide⟩),
   .op .ADD]

def m10 (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 : W) (rest : List UInt256) : State :=
  let v0 : W := x0 * x1
  let v1 : W := v0 + x2
  let v2 : W := x4 + x3
  {s with pc := N 5764, memory := s.memory, stack := v2 :: v1 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: x18 :: rest}

theorem run10 (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions p10
      {s with pc := N 5760, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: x18 :: rest} =
        some (m10 s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 rest) := by
  have capacity (j : Nat) (hj : j ≤ 30) : rest.length+j < 1024 := by omega
  have ha768 : (768 : W).toNat = 768 := rfl
  have ha2720 : (2720 : W).toNat = 2720 := rfl
  have hf768 := CycleSubmission.DoubleInputColumn.active_fix s 768 32 (by decide) (by norm_num) hact
  have hf2720 := CycleSubmission.DoubleInputColumn.active_fix s 2720 32 (by decide) (by norm_num) hact
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  simp [hz, hzn, p10, m10, runInstructions, runInstr,
    List.exchange, succ_ofNat_mod, ofNat_add_mod, Nat.add_assoc,
    State.activeWordsAfterUInt256, literal_eq_ofNat,
    capacity, ha768, ha2720, hf768, hf2720]

def p11 : List Instr :=
  [.op (.Dup ⟨9, by decide⟩),
   .op (.Dup ⟨12, by decide⟩),
   .op (.Dup ⟨12, by decide⟩),
   .op .MULMOD]

def m11 (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 : W) (rest : List UInt256) : State :=
  let v0 : W := UInt256.mulMod x10 x11 x9
  {s with pc := N 5768, memory := s.memory, stack := v0 :: x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: rest}

theorem run11 (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions p11
      {s with pc := N 5764, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: rest} =
        some (m11 s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 rest) := by
  have capacity (j : Nat) (hj : j ≤ 30) : rest.length+j < 1024 := by omega
  have ha768 : (768 : W).toNat = 768 := rfl
  have ha2720 : (2720 : W).toNat = 2720 := rfl
  have hf768 := CycleSubmission.DoubleInputColumn.active_fix s 768 32 (by decide) (by norm_num) hact
  have hf2720 := CycleSubmission.DoubleInputColumn.active_fix s 2720 32 (by decide) (by norm_num) hact
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  simp [hz, hzn, p11, m11, runInstructions, runInstr,
    List.exchange, succ_ofNat_mod, ofNat_add_mod, Nat.add_assoc,
    State.activeWordsAfterUInt256, literal_eq_ofNat,
    capacity, ha768, ha2720, hf768, hf2720]

def p12 : List Instr :=
  [.op .ADD,
   .op (.Dup ⟨9, by decide⟩),
   .op (.Dup ⟨14, by decide⟩)]

def m12 (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 : W) (rest : List UInt256) : State :=
  let v0 : W := x0 + x1
  {s with pc := N 5771, memory := s.memory, stack := x14 :: x10 :: v0 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: rest}

theorem run12 (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions p12
      {s with pc := N 5768, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: rest} =
        some (m12 s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 rest) := by
  have capacity (j : Nat) (hj : j ≤ 30) : rest.length+j < 1024 := by omega
  have ha768 : (768 : W).toNat = 768 := rfl
  have ha2720 : (2720 : W).toNat = 2720 := rfl
  have hf768 := CycleSubmission.DoubleInputColumn.active_fix s 768 32 (by decide) (by norm_num) hact
  have hf2720 := CycleSubmission.DoubleInputColumn.active_fix s 2720 32 (by decide) (by norm_num) hact
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  simp [hz, hzn, p12, m12, runInstructions, runInstr,
    List.exchange, succ_ofNat_mod, ofNat_add_mod, Nat.add_assoc,
    State.activeWordsAfterUInt256, literal_eq_ofNat,
    capacity, ha768, ha2720, hf768, hf2720]

def p13 : List Instr :=
  [.push 4 2720,
   .op .MLOAD,
   .op (.Dup ⟨2, by decide⟩),
   .op (.Swap ⟨4, by decide⟩)]

def m13 (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 : W) (rest : List UInt256) : State :=
  let v0 : W := MachineState.readWord s.memory 2720
  {s with pc := N 5779, memory := s.memory, stack := x3 :: v0 :: x0 :: x1 :: x2 :: x1 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: rest}

theorem run13 (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions p13
      {s with pc := N 5771, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: rest} =
        some (m13 s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 rest) := by
  have capacity (j : Nat) (hj : j ≤ 30) : rest.length+j < 1024 := by omega
  have ha768 : (768 : W).toNat = 768 := rfl
  have ha2720 : (2720 : W).toNat = 2720 := rfl
  have hf768 := CycleSubmission.DoubleInputColumn.active_fix s 768 32 (by decide) (by norm_num) hact
  have hf2720 := CycleSubmission.DoubleInputColumn.active_fix s 2720 32 (by decide) (by norm_num) hact
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  simp [hz, hzn, p13, m13, runInstructions, runInstr,
    List.exchange, succ_ofNat_mod, ofNat_add_mod, Nat.add_assoc,
    State.activeWordsAfterUInt256, literal_eq_ofNat,
    capacity, ha768, ha2720, hf768, hf2720]

def p14 : List Instr :=
  [.op .MUL,
   .op (.Dup ⟨15, by decide⟩),
   .op .AND,
   .op (.Dup ⟨0, by decide⟩)]

def m14 (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 : W) (rest : List UInt256) : State :=
  let v0 : W := x0 * x1
  let v1 : W := UInt256.land x16 v0
  {s with pc := N 5783, memory := s.memory, stack := v1 :: v1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: x18 :: x19 :: rest}

theorem run14 (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions p14
      {s with pc := N 5779, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: x18 :: x19 :: rest} =
        some (m14 s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 rest) := by
  have capacity (j : Nat) (hj : j ≤ 30) : rest.length+j < 1024 := by omega
  have ha768 : (768 : W).toNat = 768 := rfl
  have ha2720 : (2720 : W).toNat = 2720 := rfl
  have hf768 := CycleSubmission.DoubleInputColumn.active_fix s 768 32 (by decide) (by norm_num) hact
  have hf2720 := CycleSubmission.DoubleInputColumn.active_fix s 2720 32 (by decide) (by norm_num) hact
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  simp [hz, hzn, p14, m14, runInstructions, runInstr,
    List.exchange, succ_ofNat_mod, ofNat_add_mod, Nat.add_assoc,
    State.activeWordsAfterUInt256, literal_eq_ofNat,
    capacity, ha768, ha2720, hf768, hf2720]

def p15 : List Instr :=
  [.op (.Swap ⟨11, by decide⟩),
   .op .POP,
   .op .MULMOD,
   .op .ADD]

def m15 (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 : W) (rest : List UInt256) : State :=
  let v0 : W := UInt256.mulMod x1 x2 x3
  let v1 : W := v0 + x4
  {s with pc := N 5787, memory := s.memory, stack := v1 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x0 :: x13 :: x14 :: x15 :: x16 :: x17 :: x18 :: x19 :: rest}

theorem run15 (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions p15
      {s with pc := N 5783, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: x18 :: x19 :: rest} =
        some (m15 s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 rest) := by
  have capacity (j : Nat) (hj : j ≤ 30) : rest.length+j < 1024 := by omega
  have ha768 : (768 : W).toNat = 768 := rfl
  have ha2720 : (2720 : W).toNat = 2720 := rfl
  have hf768 := CycleSubmission.DoubleInputColumn.active_fix s 768 32 (by decide) (by norm_num) hact
  have hf2720 := CycleSubmission.DoubleInputColumn.active_fix s 2720 32 (by decide) (by norm_num) hact
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  simp [hz, hzn, p15, m15, runInstructions, runInstr,
    List.exchange, succ_ofNat_mod, ofNat_add_mod, Nat.add_assoc,
    State.activeWordsAfterUInt256, literal_eq_ofNat,
    capacity, ha768, ha2720, hf768, hf2720]

def p16 : List Instr :=
  [.push 2 2048,
   .op .MULMOD,
   .push 3 768,
   .op .MLOAD]

def m16 (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 : W) (rest : List UInt256) : State :=
  let v0 : W := UInt256.mulMod (N 2048) x0 x1
  let v1 : W := MachineState.readWord s.memory 768
  {s with pc := N 5796, memory := s.memory, stack := v1 :: v0 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: rest}

theorem run16 (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions p16
      {s with pc := N 5787, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: rest} =
        some (m16 s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 rest) := by
  have capacity (j : Nat) (hj : j ≤ 30) : rest.length+j < 1024 := by omega
  have ha768 : (768 : W).toNat = 768 := rfl
  have ha2720 : (2720 : W).toNat = 2720 := rfl
  have hf768 := CycleSubmission.DoubleInputColumn.active_fix s 768 32 (by decide) (by norm_num) hact
  have hf2720 := CycleSubmission.DoubleInputColumn.active_fix s 2720 32 (by decide) (by norm_num) hact
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  simp [hz, hzn, p16, m16, runInstructions, runInstr,
    List.exchange, succ_ofNat_mod, ofNat_add_mod, Nat.add_assoc,
    State.activeWordsAfterUInt256, literal_eq_ofNat,
    capacity, ha768, ha2720, hf768, hf2720]

def p17 : List Instr :=
  [.op (.Dup ⟨2, by decide⟩),
   .op (.Dup ⟨11, by decide⟩),
   .op .MUL,
   .op (.Dup ⟨6, by decide⟩)]

def m17 (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 : W) (rest : List UInt256) : State :=
  let v0 : W := x10 * x2
  {s with pc := N 5800, memory := s.memory, stack := x5 :: v0 :: x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: rest}

theorem run17 (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions p17
      {s with pc := N 5796, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: rest} =
        some (m17 s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 rest) := by
  have capacity (j : Nat) (hj : j ≤ 30) : rest.length+j < 1024 := by omega
  have ha768 : (768 : W).toNat = 768 := rfl
  have ha2720 : (2720 : W).toNat = 2720 := rfl
  have hf768 := CycleSubmission.DoubleInputColumn.active_fix s 768 32 (by decide) (by norm_num) hact
  have hf2720 := CycleSubmission.DoubleInputColumn.active_fix s 2720 32 (by decide) (by norm_num) hact
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  simp [hz, hzn, p17, m17, runInstructions, runInstr,
    List.exchange, succ_ofNat_mod, ofNat_add_mod, Nat.add_assoc,
    State.activeWordsAfterUInt256, literal_eq_ofNat,
    capacity, ha768, ha2720, hf768, hf2720]

def p18 : List Instr :=
  [.op (.Dup ⟨0, by decide⟩),
   .op .MUL,
   .op (.Dup ⟨11, by decide⟩),
   .op (.Dup ⟨3, by decide⟩)]

def m18 (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 : W) (rest : List UInt256) : State :=
  let v0 : W := x0 * x0
  {s with pc := N 5804, memory := s.memory, stack := x2 :: x11 :: v0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: rest}

theorem run18 (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions p18
      {s with pc := N 5800, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: rest} =
        some (m18 s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 rest) := by
  have capacity (j : Nat) (hj : j ≤ 30) : rest.length+j < 1024 := by omega
  have ha768 : (768 : W).toNat = 768 := rfl
  have ha2720 : (2720 : W).toNat = 2720 := rfl
  have hf768 := CycleSubmission.DoubleInputColumn.active_fix s 768 32 (by decide) (by norm_num) hact
  have hf2720 := CycleSubmission.DoubleInputColumn.active_fix s 2720 32 (by decide) (by norm_num) hact
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  simp [hz, hzn, p18, m18, runInstructions, runInstr,
    List.exchange, succ_ofNat_mod, ofNat_add_mod, Nat.add_assoc,
    State.activeWordsAfterUInt256, literal_eq_ofNat,
    capacity, ha768, ha2720, hf768, hf2720]

def p19 : List Instr :=
  [.op (.Dup ⟨10, by decide⟩),
   .op .MULMOD,
   .op (.Dup ⟨0, by decide⟩),
   .op .ADD]

def m19 (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 : W) (rest : List UInt256) : State :=
  let v0 : W := UInt256.mulMod x10 x0 x1
  let v1 : W := v0 + v0
  {s with pc := N 5808, memory := s.memory, stack := v1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: x18 :: x19 :: rest}

theorem run19 (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions p19
      {s with pc := N 5804, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: x18 :: x19 :: rest} =
        some (m19 s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 rest) := by
  have capacity (j : Nat) (hj : j ≤ 30) : rest.length+j < 1024 := by omega
  have ha768 : (768 : W).toNat = 768 := rfl
  have ha2720 : (2720 : W).toNat = 2720 := rfl
  have hf768 := CycleSubmission.DoubleInputColumn.active_fix s 768 32 (by decide) (by norm_num) hact
  have hf2720 := CycleSubmission.DoubleInputColumn.active_fix s 2720 32 (by decide) (by norm_num) hact
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  simp [hz, hzn, p19, m19, runInstructions, runInstr,
    List.exchange, succ_ofNat_mod, ofNat_add_mod, Nat.add_assoc,
    State.activeWordsAfterUInt256, literal_eq_ofNat,
    capacity, ha768, ha2720, hf768, hf2720]

def p20 : List Instr :=
  [.op (.Swap ⟨2, by decide⟩),
   .op (.Dup ⟨9, by decide⟩),
   .op .MUL,
   .op (.Dup ⟨0, by decide⟩)]

def m20 (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 : W) (rest : List UInt256) : State :=
  let v0 : W := x9 * x3
  {s with pc := N 5812, memory := s.memory, stack := v0 :: v0 :: x1 :: x2 :: x0 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: x18 :: rest}

theorem run20 (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions p20
      {s with pc := N 5808, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: x18 :: rest} =
        some (m20 s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 rest) := by
  have capacity (j : Nat) (hj : j ≤ 30) : rest.length+j < 1024 := by omega
  have ha768 : (768 : W).toNat = 768 := rfl
  have ha2720 : (2720 : W).toNat = 2720 := rfl
  have hf768 := CycleSubmission.DoubleInputColumn.active_fix s 768 32 (by decide) (by norm_num) hact
  have hf2720 := CycleSubmission.DoubleInputColumn.active_fix s 2720 32 (by decide) (by norm_num) hact
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  simp [hz, hzn, p20, m20, runInstructions, runInstr,
    List.exchange, succ_ofNat_mod, ofNat_add_mod, Nat.add_assoc,
    State.activeWordsAfterUInt256, literal_eq_ofNat,
    capacity, ha768, ha2720, hf768, hf2720]

def p21 : List Instr :=
  [.op .ADD,
   .op (.Dup ⟨4, by decide⟩),
   .op .ADD,
   .op .ADD]

def m21 (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 : W) (rest : List UInt256) : State :=
  let v0 : W := x0 + x1
  let v1 : W := x5 + v0
  let v2 : W := v1 + x2
  {s with pc := N 5816, memory := s.memory, stack := v2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: x18 :: x19 :: rest}

theorem run21 (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions p21
      {s with pc := N 5812, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: x18 :: x19 :: rest} =
        some (m21 s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 rest) := by
  have capacity (j : Nat) (hj : j ≤ 30) : rest.length+j < 1024 := by omega
  have ha768 : (768 : W).toNat = 768 := rfl
  have ha2720 : (2720 : W).toNat = 2720 := rfl
  have hf768 := CycleSubmission.DoubleInputColumn.active_fix s 768 32 (by decide) (by norm_num) hact
  have hf2720 := CycleSubmission.DoubleInputColumn.active_fix s 2720 32 (by decide) (by norm_num) hact
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  simp [hz, hzn, p21, m21, runInstructions, runInstr,
    List.exchange, succ_ofNat_mod, ofNat_add_mod, Nat.add_assoc,
    State.activeWordsAfterUInt256, literal_eq_ofNat,
    capacity, ha768, ha2720, hf768, hf2720]

def p22 : List Instr :=
  [.op .ADD,
   .op (.Dup ⟨9, by decide⟩),
   .op (.Dup ⟨13, by decide⟩),
   .op .MUL]

def m22 (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 : W) (rest : List UInt256) : State :=
  let v0 : W := x0 + x1
  let v1 : W := x13 * x10
  {s with pc := N 5820, memory := s.memory, stack := v1 :: v0 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: rest}

theorem run22 (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions p22
      {s with pc := N 5816, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: rest} =
        some (m22 s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 rest) := by
  have capacity (j : Nat) (hj : j ≤ 30) : rest.length+j < 1024 := by omega
  have ha768 : (768 : W).toNat = 768 := rfl
  have ha2720 : (2720 : W).toNat = 2720 := rfl
  have hf768 := CycleSubmission.DoubleInputColumn.active_fix s 768 32 (by decide) (by norm_num) hact
  have hf2720 := CycleSubmission.DoubleInputColumn.active_fix s 2720 32 (by decide) (by norm_num) hact
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  simp [hz, hzn, p22, m22, runInstructions, runInstr,
    List.exchange, succ_ofNat_mod, ofNat_add_mod, Nat.add_assoc,
    State.activeWordsAfterUInt256, literal_eq_ofNat,
    capacity, ha768, ha2720, hf768, hf2720]

def p23 : List Instr :=
  [.op .ADD,
   .op (.Swap ⟨1, by decide⟩),
   .op .ADD,
   .op (.Dup ⟨9, by decide⟩)]

def m23 (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 : W) (rest : List UInt256) : State :=
  let v0 : W := x0 + x1
  let v1 : W := x3 + x2
  {s with pc := N 5824, memory := s.memory, stack := x11 :: v1 :: v0 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: rest}

theorem run23 (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions p23
      {s with pc := N 5820, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: rest} =
        some (m23 s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 rest) := by
  have capacity (j : Nat) (hj : j ≤ 30) : rest.length+j < 1024 := by omega
  have ha768 : (768 : W).toNat = 768 := rfl
  have ha2720 : (2720 : W).toNat = 2720 := rfl
  have hf768 := CycleSubmission.DoubleInputColumn.active_fix s 768 32 (by decide) (by norm_num) hact
  have hf2720 := CycleSubmission.DoubleInputColumn.active_fix s 2720 32 (by decide) (by norm_num) hact
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  simp [hz, hzn, p23, m23, runInstructions, runInstr,
    List.exchange, succ_ofNat_mod, ofNat_add_mod, Nat.add_assoc,
    State.activeWordsAfterUInt256, literal_eq_ofNat,
    capacity, ha768, ha2720, hf768, hf2720]

def p24 : List Instr :=
  [.op (.Dup ⟨6, by decide⟩),
   .op (.Dup ⟨0, by decide⟩),
   .op .MULMOD,
   .op .ADD]

def m24 (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 : W) (rest : List UInt256) : State :=
  let v0 : W := UInt256.mulMod x6 x6 x0
  let v1 : W := v0 + x1
  {s with pc := N 5828, memory := s.memory, stack := v1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: rest}

theorem run24 (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions p24
      {s with pc := N 5824, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: rest} =
        some (m24 s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 rest) := by
  have capacity (j : Nat) (hj : j ≤ 30) : rest.length+j < 1024 := by omega
  have ha768 : (768 : W).toNat = 768 := rfl
  have ha2720 : (2720 : W).toNat = 2720 := rfl
  have hf768 := CycleSubmission.DoubleInputColumn.active_fix s 768 32 (by decide) (by norm_num) hact
  have hf2720 := CycleSubmission.DoubleInputColumn.active_fix s 2720 32 (by decide) (by norm_num) hact
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  simp [hz, hzn, p24, m24, runInstructions, runInstr,
    List.exchange, succ_ofNat_mod, ofNat_add_mod, Nat.add_assoc,
    State.activeWordsAfterUInt256, literal_eq_ofNat,
    capacity, ha768, ha2720, hf768, hf2720]

def p25 : List Instr :=
  [.op (.Dup ⟨9, by decide⟩),
   .op (.Dup ⟨3, by decide⟩),
   .op (.Dup ⟨12, by decide⟩),
   .op .MULMOD]

def m25 (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 : W) (rest : List UInt256) : State :=
  let v0 : W := UInt256.mulMod x10 x2 x9
  {s with pc := N 5832, memory := s.memory, stack := v0 :: x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: rest}

theorem run25 (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions p25
      {s with pc := N 5828, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: rest} =
        some (m25 s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 rest) := by
  have capacity (j : Nat) (hj : j ≤ 30) : rest.length+j < 1024 := by omega
  have ha768 : (768 : W).toNat = 768 := rfl
  have ha2720 : (2720 : W).toNat = 2720 := rfl
  have hf768 := CycleSubmission.DoubleInputColumn.active_fix s 768 32 (by decide) (by norm_num) hact
  have hf2720 := CycleSubmission.DoubleInputColumn.active_fix s 2720 32 (by decide) (by norm_num) hact
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  simp [hz, hzn, p25, m25, runInstructions, runInstr,
    List.exchange, succ_ofNat_mod, ofNat_add_mod, Nat.add_assoc,
    State.activeWordsAfterUInt256, literal_eq_ofNat,
    capacity, ha768, ha2720, hf768, hf2720]

def p26 : List Instr :=
  [.op .ADD,
   .op (.Dup ⟨9, by decide⟩),
   .op (.Dup ⟨12, by decide⟩),
   .op (.Dup ⟨10, by decide⟩)]

def m26 (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 : W) (rest : List UInt256) : State :=
  let v0 : W := x0 + x1
  {s with pc := N 5836, memory := s.memory, stack := x9 :: x12 :: x10 :: v0 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: rest}

theorem run26 (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions p26
      {s with pc := N 5832, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: rest} =
        some (m26 s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 rest) := by
  have capacity (j : Nat) (hj : j ≤ 30) : rest.length+j < 1024 := by omega
  have ha768 : (768 : W).toNat = 768 := rfl
  have ha2720 : (2720 : W).toNat = 2720 := rfl
  have hf768 := CycleSubmission.DoubleInputColumn.active_fix s 768 32 (by decide) (by norm_num) hact
  have hf2720 := CycleSubmission.DoubleInputColumn.active_fix s 2720 32 (by decide) (by norm_num) hact
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  simp [hz, hzn, p26, m26, runInstructions, runInstr,
    List.exchange, succ_ofNat_mod, ofNat_add_mod, Nat.add_assoc,
    State.activeWordsAfterUInt256, literal_eq_ofNat,
    capacity, ha768, ha2720, hf768, hf2720]

def p27 : List Instr :=
  [.op .MULMOD,
   .op .ADD,
   .op (.Dup ⟨9, by decide⟩),
   .op (.Dup ⟨14, by decide⟩)]

def m27 (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 : W) (rest : List UInt256) : State :=
  let v0 : W := UInt256.mulMod x0 x1 x2
  let v1 : W := v0 + x3
  {s with pc := N 5840, memory := s.memory, stack := x16 :: x12 :: v1 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: x18 :: rest}

theorem run27 (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions p27
      {s with pc := N 5836, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: x18 :: rest} =
        some (m27 s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 rest) := by
  have capacity (j : Nat) (hj : j ≤ 30) : rest.length+j < 1024 := by omega
  have ha768 : (768 : W).toNat = 768 := rfl
  have ha2720 : (2720 : W).toNat = 2720 := rfl
  have hf768 := CycleSubmission.DoubleInputColumn.active_fix s 768 32 (by decide) (by norm_num) hact
  have hf2720 := CycleSubmission.DoubleInputColumn.active_fix s 2720 32 (by decide) (by norm_num) hact
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  simp [hz, hzn, p27, m27, runInstructions, runInstr,
    List.exchange, succ_ofNat_mod, ofNat_add_mod, Nat.add_assoc,
    State.activeWordsAfterUInt256, literal_eq_ofNat,
    capacity, ha768, ha2720, hf768, hf2720]

def columnProgram : List Instr := p0 ++ (p1 ++ (p2 ++ (p3 ++ (p4 ++ (p5 ++ (p6 ++ (p7 ++ (p8 ++ (p9 ++ (p10 ++ (p11 ++ (p12 ++ (p13 ++ (p14 ++ (p15 ++ (p16 ++ (p17 ++ (p18 ++ (p19 ++ (p20 ++ (p21 ++ (p22 ++ (p23 ++ (p24 ++ (p25 ++ (p26 ++ (p27)))))))))))))))))))))))))))

def columnModel (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 : W) (rest : List UInt256) : State :=
  let v0 : W := MachineState.readWord s.memory 768
  let v1 : W := v0 * v0
  let v2 : W := MachineState.readWord s.memory 2720
  let v3 : W := v2 * v1
  let v4 : W := UInt256.land x10 v3
  let v5 : W := UInt256.mulMod v0 v0 x7
  let v6 : W := UInt256.mulMod x11 v4 x7
  let v7 : W := v6 + v5
  let v8 : W := UInt256.mulMod (N 2048) v7 x7
  let v9 : W := MachineState.readWord s.memory 768
  let v10 : W := v9 + v9
  let v11 : W := UInt256.mulMod x3 v10 x7
  let v12 : W := x3 * v10
  let v13 : W := v8 + v12
  let v14 : W := x9 * v4
  let v15 : W := v14 + v13
  let v16 : W := v8 + v11
  let v17 : W := UInt256.mulMod v4 x9 x7
  let v18 : W := v17 + v16
  let v19 : W := MachineState.readWord s.memory 2720
  let v20 : W := v15 * v19
  let v21 : W := UInt256.land x10 v20
  let v22 : W := UInt256.mulMod v21 x11 x7
  let v23 : W := v22 + v18
  let v24 : W := UInt256.mulMod (N 2048) v23 x7
  let v25 : W := MachineState.readWord s.memory 768
  let v26 : W := v4 * x0
  let v27 : W := x3 * x3
  let v28 : W := UInt256.mulMod x4 v25 x7
  let v29 : W := v28 + v28
  let v30 : W := x4 * v25
  let v31 : W := v30 + v30
  let v32 : W := v24 + v31
  let v33 : W := v32 + v27
  let v34 : W := v33 + v26
  let v35 : W := x9 * v21
  let v36 : W := v35 + v34
  let v37 : W := v24 + v29
  let v38 : W := UInt256.mulMod x3 x3 x7
  let v39 : W := v38 + v37
  let v40 : W := UInt256.mulMod v4 x0 x7
  let v41 : W := v40 + v39
  let v42 : W := UInt256.mulMod v21 x9 x7
  let v43 : W := v42 + v41
  {s with pc := N 5840, memory := s.memory, stack := x11 :: x7 :: v43 :: v36 :: x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: v21 :: x7 :: v4 :: x9 :: x10 :: x11 :: x12 :: x13 :: rest}

theorem column_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions columnProgram
      {s with pc := N 5712, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: rest} =
        some (columnModel s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 rest) := by
  let v0 : W := MachineState.readWord s.memory 768
  let v1 : W := v0 * v0
  let v2 : W := MachineState.readWord s.memory 2720
  let v3 : W := v2 * v1
  let v4 : W := UInt256.land x10 v3
  let v5 : W := UInt256.mulMod v0 v0 x7
  let v6 : W := UInt256.mulMod x11 v4 x7
  let v7 : W := v6 + v5
  let v8 : W := UInt256.mulMod (N 2048) v7 x7
  let v9 : W := MachineState.readWord s.memory 768
  let v10 : W := v9 + v9
  let v11 : W := UInt256.mulMod x3 v10 x7
  let v12 : W := x3 * v10
  let v13 : W := v8 + v12
  let v14 : W := x9 * v4
  let v15 : W := v14 + v13
  let v16 : W := v8 + v11
  let v17 : W := UInt256.mulMod v4 x9 x7
  let v18 : W := v17 + v16
  let v19 : W := MachineState.readWord s.memory 2720
  let v20 : W := v15 * v19
  let v21 : W := UInt256.land x10 v20
  let v22 : W := UInt256.mulMod v21 x11 x7
  let v23 : W := v22 + v18
  let v24 : W := UInt256.mulMod (N 2048) v23 x7
  let v25 : W := MachineState.readWord s.memory 768
  let v26 : W := v4 * x0
  let v27 : W := x3 * x3
  let v28 : W := UInt256.mulMod x4 v25 x7
  let v29 : W := v28 + v28
  let v30 : W := x4 * v25
  let v31 : W := v30 + v30
  let v32 : W := v24 + v31
  let v33 : W := v32 + v27
  let v34 : W := v33 + v26
  let v35 : W := x9 * v21
  let v36 : W := v35 + v34
  let v37 : W := v24 + v29
  let v38 : W := UInt256.mulMod x3 x3 x7
  let v39 : W := v38 + v37
  let v40 : W := UInt256.mulMod v4 x0 x7
  let v41 : W := v40 + v39
  let v42 : W := UInt256.mulMod v21 x9 x7
  let v43 : W := v42 + v41
  have h0 : runInstructions p0 {s with pc := N 5712, memory := s.memory, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: rest} = some {s with pc := N 5718, memory := s.memory, stack := v0 :: x7 :: v0 :: x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: rest} := by
    simpa only [m0, v0] using
      run0 s (x0) (x1) (x2) (x3) (x4) (x5) (x6) (x7) (x8) (x9) (x10) (x11) (x12) (x13) rest hcap hact
  have h1 : runInstructions p1 {s with pc := N 5718, memory := s.memory, stack := v0 :: x7 :: v0 :: x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: rest} = some {s with pc := N 5721, memory := s.memory, stack := v1 :: v0 :: x7 :: v0 :: x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: rest} := by
    simpa only [m1, v1] using
      run1 s (v0) (x7) (v0) (x0) (x1) (x2) (x3) (x4) (x5) (x6) (x7) (x8) (x9) (x10) (x11) (x12) (x13) rest hcap hact
  have h2 : runInstructions p2 {s with pc := N 5721, memory := s.memory, stack := v1 :: v0 :: x7 :: v0 :: x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: rest} = some {s with pc := N 5727, memory := s.memory, stack := x10 :: v3 :: v0 :: x7 :: v0 :: x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: rest} := by
    simpa only [m2, v2, v3] using
      run2 s (v1) (v0) (x7) (v0) (x0) (x1) (x2) (x3) (x4) (x5) (x6) (x7) (x8) (x9) (x10) (x11) (x12) (x13) rest hcap hact
  have h3 : runInstructions p3 {s with pc := N 5727, memory := s.memory, stack := x10 :: v3 :: v0 :: x7 :: v0 :: x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: rest} = some {s with pc := N 5731, memory := s.memory, stack := x7 :: v0 :: x7 :: v0 :: x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: v4 :: x9 :: x10 :: x11 :: x12 :: x13 :: rest} := by
    simpa only [m3, v4] using
      run3 s (x10) (v3) (v0) (x7) (v0) (x0) (x1) (x2) (x3) (x4) (x5) (x6) (x7) (x8) (x9) (x10) (x11) (x12) (x13) rest hcap hact
  have h4 : runInstructions p4 {s with pc := N 5731, memory := s.memory, stack := x7 :: v0 :: x7 :: v0 :: x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: v4 :: x9 :: x10 :: x11 :: x12 :: x13 :: rest} = some {s with pc := N 5735, memory := s.memory, stack := v4 :: x7 :: v5 :: x7 :: x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: v4 :: x9 :: x10 :: x11 :: x12 :: x13 :: rest} := by
    simpa only [m4, v5] using
      run4 s (x7) (v0) (x7) (v0) (x0) (x1) (x2) (x3) (x4) (x5) (x6) (x7) (v4) (x9) (x10) (x11) (x12) (x13) rest hcap hact
  have h5 : runInstructions p5 {s with pc := N 5735, memory := s.memory, stack := v4 :: x7 :: v5 :: x7 :: x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: v4 :: x9 :: x10 :: x11 :: x12 :: x13 :: rest} = some {s with pc := N 5742, memory := s.memory, stack := N 2048 :: v7 :: x7 :: x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: v4 :: x9 :: x10 :: x11 :: x12 :: x13 :: rest} := by
    simpa only [m5, v6, v7] using
      run5 s (v4) (x7) (v5) (x7) (x0) (x1) (x2) (x3) (x4) (x5) (x6) (x7) (v4) (x9) (x10) (x11) (x12) (x13) rest hcap hact
  have h6 : runInstructions p6 {s with pc := N 5742, memory := s.memory, stack := N 2048 :: v7 :: x7 :: x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: v4 :: x9 :: x10 :: x11 :: x12 :: x13 :: rest} = some {s with pc := N 5748, memory := s.memory, stack := v9 :: v9 :: v8 :: x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: v4 :: x9 :: x10 :: x11 :: x12 :: x13 :: rest} := by
    simpa only [m6, v8, v9] using
      run6 s (N 2048) (v7) (x7) (x0) (x1) (x2) (x3) (x4) (x5) (x6) (x7) (v4) (x9) (x10) (x11) (x12) (x13) rest hcap hact
  have h7 : runInstructions p7 {s with pc := N 5748, memory := s.memory, stack := v9 :: v9 :: v8 :: x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: v4 :: x9 :: x10 :: x11 :: x12 :: x13 :: rest} = some {s with pc := N 5752, memory := s.memory, stack := x3 :: v10 :: x7 :: v10 :: v8 :: x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: v4 :: x9 :: x10 :: x11 :: x12 :: x13 :: rest} := by
    simpa only [m7, v10] using
      run7 s (v9) (v9) (v8) (x0) (x1) (x2) (x3) (x4) (x5) (x6) (x7) (v4) (x9) (x10) (x11) (x12) (x13) rest hcap hact
  have h8 : runInstructions p8 {s with pc := N 5752, memory := s.memory, stack := x3 :: v10 :: x7 :: v10 :: v8 :: x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: v4 :: x9 :: x10 :: x11 :: x12 :: x13 :: rest} = some {s with pc := N 5756, memory := s.memory, stack := v12 :: v11 :: v8 :: x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: v4 :: x9 :: x10 :: x11 :: x12 :: x13 :: rest} := by
    simpa only [m8, v11, v12] using
      run8 s (x3) (v10) (x7) (v10) (v8) (x0) (x1) (x2) (x3) (x4) (x5) (x6) (x7) (v4) (x9) (x10) (x11) (x12) (x13) rest hcap hact
  have h9 : runInstructions p9 {s with pc := N 5756, memory := s.memory, stack := v12 :: v11 :: v8 :: x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: v4 :: x9 :: x10 :: x11 :: x12 :: x13 :: rest} = some {s with pc := N 5760, memory := s.memory, stack := x9 :: v4 :: v13 :: v11 :: v8 :: x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: v4 :: x9 :: x10 :: x11 :: x12 :: x13 :: rest} := by
    simpa only [m9, v13] using
      run9 s (v12) (v11) (v8) (x0) (x1) (x2) (x3) (x4) (x5) (x6) (x7) (v4) (x9) (x10) (x11) (x12) (x13) rest hcap hact
  have h10 : runInstructions p10 {s with pc := N 5760, memory := s.memory, stack := x9 :: v4 :: v13 :: v11 :: v8 :: x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: v4 :: x9 :: x10 :: x11 :: x12 :: x13 :: rest} = some {s with pc := N 5764, memory := s.memory, stack := v16 :: v15 :: x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: v4 :: x9 :: x10 :: x11 :: x12 :: x13 :: rest} := by
    simpa only [m10, v14, v15, v16] using
      run10 s (x9) (v4) (v13) (v11) (v8) (x0) (x1) (x2) (x3) (x4) (x5) (x6) (x7) (v4) (x9) (x10) (x11) (x12) (x13) rest hcap hact
  have h11 : runInstructions p11 {s with pc := N 5764, memory := s.memory, stack := v16 :: v15 :: x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: v4 :: x9 :: x10 :: x11 :: x12 :: x13 :: rest} = some {s with pc := N 5768, memory := s.memory, stack := v17 :: v16 :: v15 :: x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: v4 :: x9 :: x10 :: x11 :: x12 :: x13 :: rest} := by
    simpa only [m11, v17] using
      run11 s (v16) (v15) (x0) (x1) (x2) (x3) (x4) (x5) (x6) (x7) (v4) (x9) (x10) (x11) (x12) (x13) rest hcap hact
  have h12 : runInstructions p12 {s with pc := N 5768, memory := s.memory, stack := v17 :: v16 :: v15 :: x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: v4 :: x9 :: x10 :: x11 :: x12 :: x13 :: rest} = some {s with pc := N 5771, memory := s.memory, stack := x11 :: x7 :: v18 :: v15 :: x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: v4 :: x9 :: x10 :: x11 :: x12 :: x13 :: rest} := by
    simpa only [m12, v18] using
      run12 s (v17) (v16) (v15) (x0) (x1) (x2) (x3) (x4) (x5) (x6) (x7) (v4) (x9) (x10) (x11) (x12) (x13) rest hcap hact
  have h13 : runInstructions p13 {s with pc := N 5771, memory := s.memory, stack := x11 :: x7 :: v18 :: v15 :: x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: v4 :: x9 :: x10 :: x11 :: x12 :: x13 :: rest} = some {s with pc := N 5779, memory := s.memory, stack := v15 :: v19 :: x11 :: x7 :: v18 :: x7 :: x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: v4 :: x9 :: x10 :: x11 :: x12 :: x13 :: rest} := by
    simpa only [m13, v19] using
      run13 s (x11) (x7) (v18) (v15) (x0) (x1) (x2) (x3) (x4) (x5) (x6) (x7) (v4) (x9) (x10) (x11) (x12) (x13) rest hcap hact
  have h14 : runInstructions p14 {s with pc := N 5779, memory := s.memory, stack := v15 :: v19 :: x11 :: x7 :: v18 :: x7 :: x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: v4 :: x9 :: x10 :: x11 :: x12 :: x13 :: rest} = some {s with pc := N 5783, memory := s.memory, stack := v21 :: v21 :: x11 :: x7 :: v18 :: x7 :: x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: v4 :: x9 :: x10 :: x11 :: x12 :: x13 :: rest} := by
    simpa only [m14, v20, v21] using
      run14 s (v15) (v19) (x11) (x7) (v18) (x7) (x0) (x1) (x2) (x3) (x4) (x5) (x6) (x7) (v4) (x9) (x10) (x11) (x12) (x13) rest hcap hact
  have h15 : runInstructions p15 {s with pc := N 5783, memory := s.memory, stack := v21 :: v21 :: x11 :: x7 :: v18 :: x7 :: x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: v4 :: x9 :: x10 :: x11 :: x12 :: x13 :: rest} = some {s with pc := N 5787, memory := s.memory, stack := v23 :: x7 :: x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: v21 :: x7 :: v4 :: x9 :: x10 :: x11 :: x12 :: x13 :: rest} := by
    simpa only [m15, v22, v23] using
      run15 s (v21) (v21) (x11) (x7) (v18) (x7) (x0) (x1) (x2) (x3) (x4) (x5) (x6) (x7) (v4) (x9) (x10) (x11) (x12) (x13) rest hcap hact
  have h16 : runInstructions p16 {s with pc := N 5787, memory := s.memory, stack := v23 :: x7 :: x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: v21 :: x7 :: v4 :: x9 :: x10 :: x11 :: x12 :: x13 :: rest} = some {s with pc := N 5796, memory := s.memory, stack := v25 :: v24 :: x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: v21 :: x7 :: v4 :: x9 :: x10 :: x11 :: x12 :: x13 :: rest} := by
    simpa only [m16, v24, v25] using
      run16 s (v23) (x7) (x0) (x1) (x2) (x3) (x4) (x5) (v21) (x7) (v4) (x9) (x10) (x11) (x12) (x13) rest hcap hact
  have h17 : runInstructions p17 {s with pc := N 5796, memory := s.memory, stack := v25 :: v24 :: x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: v21 :: x7 :: v4 :: x9 :: x10 :: x11 :: x12 :: x13 :: rest} = some {s with pc := N 5800, memory := s.memory, stack := x3 :: v26 :: v25 :: v24 :: x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: v21 :: x7 :: v4 :: x9 :: x10 :: x11 :: x12 :: x13 :: rest} := by
    simpa only [m17, v26] using
      run17 s (v25) (v24) (x0) (x1) (x2) (x3) (x4) (x5) (v21) (x7) (v4) (x9) (x10) (x11) (x12) (x13) rest hcap hact
  have h18 : runInstructions p18 {s with pc := N 5800, memory := s.memory, stack := x3 :: v26 :: v25 :: v24 :: x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: v21 :: x7 :: v4 :: x9 :: x10 :: x11 :: x12 :: x13 :: rest} = some {s with pc := N 5804, memory := s.memory, stack := v25 :: x7 :: v27 :: v26 :: v25 :: v24 :: x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: v21 :: x7 :: v4 :: x9 :: x10 :: x11 :: x12 :: x13 :: rest} := by
    simpa only [m18, v27] using
      run18 s (x3) (v26) (v25) (v24) (x0) (x1) (x2) (x3) (x4) (x5) (v21) (x7) (v4) (x9) (x10) (x11) (x12) (x13) rest hcap hact
  have h19 : runInstructions p19 {s with pc := N 5804, memory := s.memory, stack := v25 :: x7 :: v27 :: v26 :: v25 :: v24 :: x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: v21 :: x7 :: v4 :: x9 :: x10 :: x11 :: x12 :: x13 :: rest} = some {s with pc := N 5808, memory := s.memory, stack := v29 :: v27 :: v26 :: v25 :: v24 :: x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: v21 :: x7 :: v4 :: x9 :: x10 :: x11 :: x12 :: x13 :: rest} := by
    simpa only [m19, v28, v29] using
      run19 s (v25) (x7) (v27) (v26) (v25) (v24) (x0) (x1) (x2) (x3) (x4) (x5) (v21) (x7) (v4) (x9) (x10) (x11) (x12) (x13) rest hcap hact
  have h20 : runInstructions p20 {s with pc := N 5808, memory := s.memory, stack := v29 :: v27 :: v26 :: v25 :: v24 :: x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: v21 :: x7 :: v4 :: x9 :: x10 :: x11 :: x12 :: x13 :: rest} = some {s with pc := N 5812, memory := s.memory, stack := v30 :: v30 :: v27 :: v26 :: v29 :: v24 :: x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: v21 :: x7 :: v4 :: x9 :: x10 :: x11 :: x12 :: x13 :: rest} := by
    simpa only [m20, v30] using
      run20 s (v29) (v27) (v26) (v25) (v24) (x0) (x1) (x2) (x3) (x4) (x5) (v21) (x7) (v4) (x9) (x10) (x11) (x12) (x13) rest hcap hact
  have h21 : runInstructions p21 {s with pc := N 5812, memory := s.memory, stack := v30 :: v30 :: v27 :: v26 :: v29 :: v24 :: x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: v21 :: x7 :: v4 :: x9 :: x10 :: x11 :: x12 :: x13 :: rest} = some {s with pc := N 5816, memory := s.memory, stack := v33 :: v26 :: v29 :: v24 :: x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: v21 :: x7 :: v4 :: x9 :: x10 :: x11 :: x12 :: x13 :: rest} := by
    simpa only [m21, v31, v32, v33] using
      run21 s (v30) (v30) (v27) (v26) (v29) (v24) (x0) (x1) (x2) (x3) (x4) (x5) (v21) (x7) (v4) (x9) (x10) (x11) (x12) (x13) rest hcap hact
  have h22 : runInstructions p22 {s with pc := N 5816, memory := s.memory, stack := v33 :: v26 :: v29 :: v24 :: x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: v21 :: x7 :: v4 :: x9 :: x10 :: x11 :: x12 :: x13 :: rest} = some {s with pc := N 5820, memory := s.memory, stack := v35 :: v34 :: v29 :: v24 :: x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: v21 :: x7 :: v4 :: x9 :: x10 :: x11 :: x12 :: x13 :: rest} := by
    simpa only [m22, v34, v35] using
      run22 s (v33) (v26) (v29) (v24) (x0) (x1) (x2) (x3) (x4) (x5) (v21) (x7) (v4) (x9) (x10) (x11) (x12) (x13) rest hcap hact
  have h23 : runInstructions p23 {s with pc := N 5820, memory := s.memory, stack := v35 :: v34 :: v29 :: v24 :: x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: v21 :: x7 :: v4 :: x9 :: x10 :: x11 :: x12 :: x13 :: rest} = some {s with pc := N 5824, memory := s.memory, stack := x7 :: v37 :: v36 :: x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: v21 :: x7 :: v4 :: x9 :: x10 :: x11 :: x12 :: x13 :: rest} := by
    simpa only [m23, v36, v37] using
      run23 s (v35) (v34) (v29) (v24) (x0) (x1) (x2) (x3) (x4) (x5) (v21) (x7) (v4) (x9) (x10) (x11) (x12) (x13) rest hcap hact
  have h24 : runInstructions p24 {s with pc := N 5824, memory := s.memory, stack := x7 :: v37 :: v36 :: x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: v21 :: x7 :: v4 :: x9 :: x10 :: x11 :: x12 :: x13 :: rest} = some {s with pc := N 5828, memory := s.memory, stack := v39 :: v36 :: x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: v21 :: x7 :: v4 :: x9 :: x10 :: x11 :: x12 :: x13 :: rest} := by
    simpa only [m24, v38, v39] using
      run24 s (x7) (v37) (v36) (x0) (x1) (x2) (x3) (x4) (x5) (v21) (x7) (v4) (x9) (x10) (x11) (x12) (x13) rest hcap hact
  have h25 : runInstructions p25 {s with pc := N 5828, memory := s.memory, stack := v39 :: v36 :: x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: v21 :: x7 :: v4 :: x9 :: x10 :: x11 :: x12 :: x13 :: rest} = some {s with pc := N 5832, memory := s.memory, stack := v40 :: v39 :: v36 :: x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: v21 :: x7 :: v4 :: x9 :: x10 :: x11 :: x12 :: x13 :: rest} := by
    simpa only [m25, v40] using
      run25 s (v39) (v36) (x0) (x1) (x2) (x3) (x4) (x5) (v21) (x7) (v4) (x9) (x10) (x11) (x12) (x13) rest hcap hact
  have h26 : runInstructions p26 {s with pc := N 5832, memory := s.memory, stack := v40 :: v39 :: v36 :: x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: v21 :: x7 :: v4 :: x9 :: x10 :: x11 :: x12 :: x13 :: rest} = some {s with pc := N 5836, memory := s.memory, stack := v21 :: x9 :: x7 :: v41 :: v36 :: x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: v21 :: x7 :: v4 :: x9 :: x10 :: x11 :: x12 :: x13 :: rest} := by
    simpa only [m26, v41] using
      run26 s (v40) (v39) (v36) (x0) (x1) (x2) (x3) (x4) (x5) (v21) (x7) (v4) (x9) (x10) (x11) (x12) (x13) rest hcap hact
  have h27 : runInstructions p27 {s with pc := N 5836, memory := s.memory, stack := v21 :: x9 :: x7 :: v41 :: v36 :: x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: v21 :: x7 :: v4 :: x9 :: x10 :: x11 :: x12 :: x13 :: rest} = some {s with pc := N 5840, memory := s.memory, stack := x11 :: x7 :: v43 :: v36 :: x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: v21 :: x7 :: v4 :: x9 :: x10 :: x11 :: x12 :: x13 :: rest} := by
    simpa only [m27, v42, v43] using
      run27 s (v21) (x9) (x7) (v41) (v36) (x0) (x1) (x2) (x3) (x4) (x5) (v21) (x7) (v4) (x9) (x10) (x11) (x12) (x13) rest hcap hact
  change runInstructions columnProgram _ = some _
  exact (run_append_some _ _ _ _ _ h0 (run_append_some _ _ _ _ _ h1 (run_append_some _ _ _ _ _ h2 (run_append_some _ _ _ _ _ h3 (run_append_some _ _ _ _ _ h4 (run_append_some _ _ _ _ _ h5 (run_append_some _ _ _ _ _ h6 (run_append_some _ _ _ _ _ h7 (run_append_some _ _ _ _ _ h8 (run_append_some _ _ _ _ _ h9 (run_append_some _ _ _ _ _ h10 (run_append_some _ _ _ _ _ h11 (run_append_some _ _ _ _ _ h12 (run_append_some _ _ _ _ _ h13 (run_append_some _ _ _ _ _ h14 (run_append_some _ _ _ _ _ h15 (run_append_some _ _ _ _ _ h16 (run_append_some _ _ _ _ _ h17 (run_append_some _ _ _ _ _ h18 (run_append_some _ _ _ _ _ h19 (run_append_some _ _ _ _ _ h20 (run_append_some _ _ _ _ _ h21 (run_append_some _ _ _ _ _ h22 (run_append_some _ _ _ _ _ h23 (run_append_some _ _ _ _ _ h24 (run_append_some _ _ _ _ _ h25 (run_append_some _ _ _ _ _ h26 h27)))))))))))))))))))))))))))

def parentModel (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 : W) (rest : List W) : State :=
  let v0 : W := MachineState.readWord s.memory 768
  let v1 : W := v0 * v0
  let v2 : W := MachineState.readWord s.memory 2720
  let v3 : W := v2 * v1
  let v4 : W := UInt256.land w10 v3
  let v5 : W := UInt256.mulMod v0 v0 w7
  let v6 : W := UInt256.mulMod w11 v4 w7
  let v7 : W := v6 + v5
  let v8 : W := UInt256.mulMod (N 2048) v7 w7
  let v9 : W := MachineState.readWord s.memory 768
  let v10 : W := UInt256.mulMod w3 v9 w7
  let v11 : W := v10 + v10
  let v12 : W := w3 * v9
  let v13 : W := v12 + v12
  let v14 : W := v8 + v13
  let v15 : W := w9 * v4
  let v16 : W := v15 + v14
  let v17 : W := v8 + v11
  let v18 : W := UInt256.mulMod v4 w9 w7
  let v19 : W := v18 + v17
  let v20 : W := MachineState.readWord s.memory 2720
  let v21 : W := v16 * v20
  let v22 : W := UInt256.land w10 v21
  let v23 : W := UInt256.mulMod v22 w11 w7
  let v24 : W := v23 + v19
  let v25 : W := UInt256.mulMod (N 2048) v24 w7
  let v26 : W := MachineState.readWord s.memory 768
  let v27 : W := v4 * w0
  let v28 : W := w3 * w3
  let v29 : W := UInt256.mulMod w4 v26 w7
  let v30 : W := v29 + v29
  let v31 : W := w4 * v26
  let v32 : W := v31 + v31
  let v33 : W := v25 + v32
  let v34 : W := v33 + v28
  let v35 : W := v34 + v27
  let v36 : W := w9 * v22
  let v37 : W := v36 + v35
  let v38 : W := v25 + v30
  let v39 : W := UInt256.mulMod w3 w3 w7
  let v40 : W := v39 + v38
  let v41 : W := UInt256.mulMod v4 w0 w7
  let v42 : W := v41 + v40
  let v43 : W := UInt256.mulMod v22 w9 w7
  let v44 : W := v43 + v42
  {s with pc := N 5840, memory := s.memory, stack := w11 :: w7 :: v44 :: v37 :: w0 :: w1 :: w2 :: w3 :: w4 :: w5 :: v22 :: w7 :: v4 :: w9 :: w10 :: w11 :: w12 :: w13 :: rest}


/-- The exact first-column model preserves its parent on every radix-240 input digit.
The residue accumulators need only agree after the enclosing MULMOD. -/
theorem column_model_eq (s : State) (x0 x1 x2 x3 x4 x5 x6 x8 x9 x10 x11 x12 x13 : W) (rest : List W)
    (ha : (MachineState.readWord s.memory 768).toNat < 2^240) :
    columnModel s (x0) (x1) (x2) (x3) (x4) (x5) (x6) (N (2^251-1)) (x8) (x9) (x10) (x11) (x12) (x13) rest = parentModel s (x0) (x1) (x2) (x3) (x4) (x5) (x6) (N (2^251-1)) (x8) (x9) (x10) (x11) (x12) (x13) rest := by
  let p : W := N (2^251-1)
  let o0 : W := MachineState.readWord s.memory 768
  let o1 : W := o0 * o0
  let o2 : W := MachineState.readWord s.memory 2720
  let o3 : W := o2 * o1
  let o4 : W := UInt256.land x10 o3
  let o5 : W := UInt256.mulMod o0 o0 p
  let o6 : W := UInt256.mulMod x11 o4 p
  let o7 : W := o6 + o5
  let o8 : W := UInt256.mulMod (N 2048) o7 p
  let o9 : W := MachineState.readWord s.memory 768
  let o10 : W := UInt256.mulMod x3 o9 p
  let o11 : W := o10 + o10
  let o12 : W := x3 * o9
  let o13 : W := o12 + o12
  let o14 : W := o8 + o13
  let o15 : W := x9 * o4
  let o16 : W := o15 + o14
  let o17 : W := o8 + o11
  let o18 : W := UInt256.mulMod o4 x9 p
  let o19 : W := o18 + o17
  let o20 : W := MachineState.readWord s.memory 2720
  let o21 : W := o16 * o20
  let o22 : W := UInt256.land x10 o21
  let o23 : W := UInt256.mulMod o22 x11 p
  let o24 : W := o23 + o19
  let o25 : W := UInt256.mulMod (N 2048) o24 p
  let o26 : W := MachineState.readWord s.memory 768
  let o27 : W := o4 * x0
  let o28 : W := x3 * x3
  let o29 : W := UInt256.mulMod x4 o26 p
  let o30 : W := o29 + o29
  let o31 : W := x4 * o26
  let o32 : W := o31 + o31
  let o33 : W := o25 + o32
  let o34 : W := o33 + o28
  let o35 : W := o34 + o27
  let o36 : W := x9 * o22
  let o37 : W := o36 + o35
  let o38 : W := o25 + o30
  let o39 : W := UInt256.mulMod x3 x3 p
  let o40 : W := o39 + o38
  let o41 : W := UInt256.mulMod o4 x0 p
  let o42 : W := o41 + o40
  let o43 : W := UInt256.mulMod o22 x9 p
  let o44 : W := o43 + o42
  let n0 : W := MachineState.readWord s.memory 768
  let n1 : W := n0 * n0
  let n2 : W := MachineState.readWord s.memory 2720
  let n3 : W := n2 * n1
  let n4 : W := UInt256.land x10 n3
  let n5 : W := UInt256.mulMod n0 n0 p
  let n6 : W := UInt256.mulMod x11 n4 p
  let n7 : W := n6 + n5
  let n8 : W := UInt256.mulMod (N 2048) n7 p
  let n9 : W := MachineState.readWord s.memory 768
  let n10 : W := n9 + n9
  let n11 : W := UInt256.mulMod x3 n10 p
  let n12 : W := x3 * n10
  let n13 : W := n8 + n12
  let n14 : W := x9 * n4
  let n15 : W := n14 + n13
  let n16 : W := n8 + n11
  let n17 : W := UInt256.mulMod n4 x9 p
  let n18 : W := n17 + n16
  let n19 : W := MachineState.readWord s.memory 2720
  let n20 : W := n15 * n19
  let n21 : W := UInt256.land x10 n20
  let n22 : W := UInt256.mulMod n21 x11 p
  let n23 : W := n22 + n18
  let n24 : W := UInt256.mulMod (N 2048) n23 p
  let n25 : W := MachineState.readWord s.memory 768
  let n26 : W := n4 * x0
  let n27 : W := x3 * x3
  let n28 : W := UInt256.mulMod x4 n25 p
  let n29 : W := n28 + n28
  let n30 : W := x4 * n25
  let n31 : W := n30 + n30
  let n32 : W := n24 + n31
  let n33 : W := n32 + n27
  let n34 : W := n33 + n26
  let n35 : W := x9 * n21
  let n36 : W := n35 + n34
  let n37 : W := n24 + n29
  let n38 : W := UInt256.mulMod x3 x3 p
  let n39 : W := n38 + n37
  let n40 : W := UInt256.mulMod n4 x0 p
  let n41 : W := n40 + n39
  let n42 : W := UInt256.mulMod n21 x9 p
  let n43 : W := n42 + n41
  have eq0 : n0 = o0 := by
    simp only [n0, o0]
  have eq1 : n1 = o1 := by
    simp only [n1, o1, eq0]
  have eq2 : n2 = o2 := by
    simp only [n2, o2, eq0, eq1]
  have eq3 : n3 = o3 := by
    simp only [n3, o3, eq0, eq1, eq2]
  have eq4 : n4 = o4 := by
    simp only [n4, o4, eq0, eq1, eq2, eq3]
  have eq5 : n5 = o5 := by
    simp only [n5, o5, eq0, eq1, eq2, eq3, eq4]
  have eq6 : n6 = o6 := by
    simp only [n6, o6, eq0, eq1, eq2, eq3, eq4, eq5]
  have eq7 : n7 = o7 := by
    simp only [n7, o7, eq0, eq1, eq2, eq3, eq4, eq5, eq6]
  have eq8 : n8 = o8 := by
    simp only [n8, o8, eq0, eq1, eq2, eq3, eq4, eq5, eq6, eq7]
  have eq9 : n9 = o9 := by
    simp only [n9, o9, eq0, eq1, eq2, eq3, eq4, eq5, eq6, eq7, eq8]
  have eq12 : n12 = o13 := by
    simpa only [n12, n10, n9, o13, o12, o9] using
      CycleSubmission.DoubleInput.low_double (MachineState.readWord s.memory 768) x3
  have eq13 : n13 = o14 := by
    simp only [n13, o14, eq0, eq1, eq2, eq3, eq4, eq5, eq6, eq7, eq8, eq9, eq12]
  have eq14 : n14 = o15 := by
    simp only [n14, o15, eq0, eq1, eq2, eq3, eq4, eq5, eq6, eq7, eq8, eq9, eq12, eq13]
  have eq15 : n15 = o16 := by
    simp only [n15, o16, eq0, eq1, eq2, eq3, eq4, eq5, eq6, eq7, eq8, eq9, eq12, eq13, eq14]
  have eq19 : n19 = o20 := by
    simp only [n19, o20, eq0, eq1, eq2, eq3, eq4, eq5, eq6, eq7, eq8, eq9, eq12, eq13, eq14, eq15]
  have eq20 : n20 = o21 := by
    simp only [n20, o21, eq0, eq1, eq2, eq3, eq4, eq5, eq6, eq7, eq8, eq9, eq12, eq13, eq14, eq15, eq19]
  have eq21 : n21 = o22 := by
    simp only [n21, o22, eq0, eq1, eq2, eq3, eq4, eq5, eq6, eq7, eq8, eq9, eq12, eq13, eq14, eq15, eq19, eq20]
  have eq22 : n22 = o23 := by
    simp only [n22, o23, eq0, eq1, eq2, eq3, eq4, eq5, eq6, eq7, eq8, eq9, eq12, eq13, eq14, eq15, eq19, eq20, eq21]
  have eq24 : n24 = o25 := by
    simpa only [n24, n23, n22, n18, n17, n16, n11, n10, n9,
      eq21, eq8, eq4, o25, o24, o23, o19, o18, o17, o11, o10, o9] using
      CycleSubmission.DoubleInput.high_double_radix240
        (MachineState.readWord s.memory 768) x3
        (N 2048) o7 o4 x9 o22 x11 (N 2048) ha
  have eq25 : n25 = o26 := by
    simp only [n25, o26, eq0, eq1, eq2, eq3, eq4, eq5, eq6, eq7, eq8, eq9, eq12, eq13, eq14, eq15, eq19, eq20, eq21, eq22, eq24]
  have eq26 : n26 = o27 := by
    simp only [n26, o27, eq0, eq1, eq2, eq3, eq4, eq5, eq6, eq7, eq8, eq9, eq12, eq13, eq14, eq15, eq19, eq20, eq21, eq22, eq24, eq25]
  have eq27 : n27 = o28 := by
    simp only [n27, o28, eq0, eq1, eq2, eq3, eq4, eq5, eq6, eq7, eq8, eq9, eq12, eq13, eq14, eq15, eq19, eq20, eq21, eq22, eq24, eq25, eq26]
  have eq28 : n28 = o29 := by
    simp only [n28, o29, eq0, eq1, eq2, eq3, eq4, eq5, eq6, eq7, eq8, eq9, eq12, eq13, eq14, eq15, eq19, eq20, eq21, eq22, eq24, eq25, eq26, eq27]
  have eq29 : n29 = o30 := by
    simp only [n29, o30, eq0, eq1, eq2, eq3, eq4, eq5, eq6, eq7, eq8, eq9, eq12, eq13, eq14, eq15, eq19, eq20, eq21, eq22, eq24, eq25, eq26, eq27, eq28]
  have eq30 : n30 = o31 := by
    simp only [n30, o31, eq0, eq1, eq2, eq3, eq4, eq5, eq6, eq7, eq8, eq9, eq12, eq13, eq14, eq15, eq19, eq20, eq21, eq22, eq24, eq25, eq26, eq27, eq28, eq29]
  have eq31 : n31 = o32 := by
    simp only [n31, o32, eq0, eq1, eq2, eq3, eq4, eq5, eq6, eq7, eq8, eq9, eq12, eq13, eq14, eq15, eq19, eq20, eq21, eq22, eq24, eq25, eq26, eq27, eq28, eq29, eq30]
  have eq32 : n32 = o33 := by
    simp only [n32, o33, eq0, eq1, eq2, eq3, eq4, eq5, eq6, eq7, eq8, eq9, eq12, eq13, eq14, eq15, eq19, eq20, eq21, eq22, eq24, eq25, eq26, eq27, eq28, eq29, eq30, eq31]
  have eq33 : n33 = o34 := by
    simp only [n33, o34, eq0, eq1, eq2, eq3, eq4, eq5, eq6, eq7, eq8, eq9, eq12, eq13, eq14, eq15, eq19, eq20, eq21, eq22, eq24, eq25, eq26, eq27, eq28, eq29, eq30, eq31, eq32]
  have eq34 : n34 = o35 := by
    simp only [n34, o35, eq0, eq1, eq2, eq3, eq4, eq5, eq6, eq7, eq8, eq9, eq12, eq13, eq14, eq15, eq19, eq20, eq21, eq22, eq24, eq25, eq26, eq27, eq28, eq29, eq30, eq31, eq32, eq33]
  have eq35 : n35 = o36 := by
    simp only [n35, o36, eq0, eq1, eq2, eq3, eq4, eq5, eq6, eq7, eq8, eq9, eq12, eq13, eq14, eq15, eq19, eq20, eq21, eq22, eq24, eq25, eq26, eq27, eq28, eq29, eq30, eq31, eq32, eq33, eq34]
  have eq36 : n36 = o37 := by
    simp only [n36, o37, eq0, eq1, eq2, eq3, eq4, eq5, eq6, eq7, eq8, eq9, eq12, eq13, eq14, eq15, eq19, eq20, eq21, eq22, eq24, eq25, eq26, eq27, eq28, eq29, eq30, eq31, eq32, eq33, eq34, eq35]
  have eq37 : n37 = o38 := by
    simp only [n37, o38, eq0, eq1, eq2, eq3, eq4, eq5, eq6, eq7, eq8, eq9, eq12, eq13, eq14, eq15, eq19, eq20, eq21, eq22, eq24, eq25, eq26, eq27, eq28, eq29, eq30, eq31, eq32, eq33, eq34, eq35, eq36]
  have eq38 : n38 = o39 := by
    simp only [n38, o39, eq0, eq1, eq2, eq3, eq4, eq5, eq6, eq7, eq8, eq9, eq12, eq13, eq14, eq15, eq19, eq20, eq21, eq22, eq24, eq25, eq26, eq27, eq28, eq29, eq30, eq31, eq32, eq33, eq34, eq35, eq36, eq37]
  have eq39 : n39 = o40 := by
    simp only [n39, o40, eq0, eq1, eq2, eq3, eq4, eq5, eq6, eq7, eq8, eq9, eq12, eq13, eq14, eq15, eq19, eq20, eq21, eq22, eq24, eq25, eq26, eq27, eq28, eq29, eq30, eq31, eq32, eq33, eq34, eq35, eq36, eq37, eq38]
  have eq40 : n40 = o41 := by
    simp only [n40, o41, eq0, eq1, eq2, eq3, eq4, eq5, eq6, eq7, eq8, eq9, eq12, eq13, eq14, eq15, eq19, eq20, eq21, eq22, eq24, eq25, eq26, eq27, eq28, eq29, eq30, eq31, eq32, eq33, eq34, eq35, eq36, eq37, eq38, eq39]
  have eq41 : n41 = o42 := by
    simp only [n41, o42, eq0, eq1, eq2, eq3, eq4, eq5, eq6, eq7, eq8, eq9, eq12, eq13, eq14, eq15, eq19, eq20, eq21, eq22, eq24, eq25, eq26, eq27, eq28, eq29, eq30, eq31, eq32, eq33, eq34, eq35, eq36, eq37, eq38, eq39, eq40]
  have eq42 : n42 = o43 := by
    simp only [n42, o43, eq0, eq1, eq2, eq3, eq4, eq5, eq6, eq7, eq8, eq9, eq12, eq13, eq14, eq15, eq19, eq20, eq21, eq22, eq24, eq25, eq26, eq27, eq28, eq29, eq30, eq31, eq32, eq33, eq34, eq35, eq36, eq37, eq38, eq39, eq40, eq41]
  have eq43 : n43 = o44 := by
    simp only [n43, o44, eq0, eq1, eq2, eq3, eq4, eq5, eq6, eq7, eq8, eq9, eq12, eq13, eq14, eq15, eq19, eq20, eq21, eq22, eq24, eq25, eq26, eq27, eq28, eq29, eq30, eq31, eq32, eq33, eq34, eq35, eq36, eq37, eq38, eq39, eq40, eq41, eq42]
  change {s with pc := N 5840, memory := s.memory, stack := x11 :: p :: n43 :: n36 :: x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: n21 :: p :: n4 :: x9 :: x10 :: x11 :: x12 :: x13 :: rest} =
    {s with pc := N 5840, memory := s.memory, stack := x11 :: p :: o44 :: o37 :: x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: o22 :: p :: o4 :: x9 :: x10 :: x11 :: x12 :: x13 :: rest}
  simp only [eq0, eq1, eq2, eq3, eq4, eq5, eq6, eq7, eq8, eq9, eq12, eq13, eq14, eq15, eq19, eq20, eq21, eq22, eq24, eq25, eq26, eq27, eq28, eq29, eq30, eq31, eq32, eq33, eq34, eq35, eq36, eq37, eq38, eq39, eq40, eq41, eq42, eq43]

#print axioms column_model_eq
/-- Exact candidate execution to the existing parent-model output.
Only the loaded a0 word is bounded; every other input stack word is arbitrary. -/
theorem replacement (s : State) (x0 x1 x2 x3 x4 x5 x6 x8 x9 x10 x11 x12 x13 : W)
    (rest : List W) (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat)
    (ha : (MachineState.readWord s.memory 768).toNat < 2^240) :
    runInstructions columnProgram
      {s with
        pc := N 5712
        stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 ::
          N (2^251-1) :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: rest} =
      some (parentModel s x0 x1 x2 x3 x4 x5 x6 (N (2^251-1))
        x8 x9 x10 x11 x12 x13 rest) := by
  exact (column_run s x0 x1 x2 x3 x4 x5 x6 (N (2^251-1))
    x8 x9 x10 x11 x12 x13 rest hcap hact).trans
      (congrArg some (column_model_eq s x0 x1 x2 x3 x4 x5 x6
        x8 x9 x10 x11 x12 x13 rest ha))

#print axioms replacement

#print axioms column_run
end CycleSubmission.DoubleInputColumn
