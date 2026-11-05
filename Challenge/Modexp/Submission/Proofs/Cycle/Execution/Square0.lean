import Challenge.Modexp.Submission.Proofs.Prepared.Arithmetic
import Challenge.Modexp.Submission.Proofs.Fast.Monpro
import Challenge.Modexp.Submission.Proofs.Bytecode.WindowNibbleDefs
set_option warningAsError true
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option maxRecDepth 40000
set_option maxHeartbeats 8000000
namespace CycleSubmission.Execution
open EvmSemantics EvmSemantics.EVM YulEvmCompiler
open Challenge.Modexp.Submission.Proofs.Bytecode.WindowNibbleKernel
open Challenge.Modexp.Submission.Proofs.Fast

open Challenge.EvmProof.Word Challenge.EvmProof.Stepper
local notation "W" => UInt256
local notation "N" => UInt256.ofNat

open CycleSubmission.Prepared.Arithmetic

def sq0Newpart0Program : List Instr :=
  [.push 2 768,
   .op .MLOAD,
   .op (.Dup ⟨8, by decide⟩),
   .op (.Dup ⟨1, by decide⟩),
   .op (.Dup ⟨0, by decide⟩),
   .op (.Dup ⟨0, by decide⟩),
   .op .MUL,
   .push 2 2720,
   .op .MLOAD]

def sq0Newpart0Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 : W) (rest : List W) : State :=
  let v0 : W := MachineState.readWord s.memory 768
  let v1 : W := v0 * v0
  let v2 : W := MachineState.readWord s.memory 2720
  {s with pc := N 5725, memory := s.memory, stack := v2 :: v1 :: v0 :: x7 :: v0 :: x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: rest}

theorem sq0Newpart0_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions sq0Newpart0Program {s with pc := N 5712, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: rest} =
      some (sq0Newpart0Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 19) : rest.length + j < 1024 := by omega
  have ha768 : (768 : W).toNat = 768 := rfl
  have hf768 := Monpro.activeWords_fix s 768 32 (by decide) (by norm_num) hact
  have ha2720 : (2720 : W).toNat = 2720 := rfl
  have hf2720 := Monpro.activeWords_fix s 2720 32 (by decide) (by norm_num) hact
  simp [hz, hzn, sq0Newpart0Program, sq0Newpart0Model, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, capacity, ha768, hf768, ha2720, hf2720]


def sq0Newpart1Program : List Instr :=
  [.op .MUL,
   .op (.Dup ⟨14, by decide⟩),
   .op .AND,
   .op (.Swap ⟨11, by decide⟩),
   .op .POP,
   .op (.Dup ⟨10, by decide⟩),
   .op (.Swap ⟨2, by decide⟩),
   .op .MULMOD]

def sq0Newpart1Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 : W) (rest : List W) : State :=
  let v0 : W := x0 * x1
  let v1 : W := UInt256.land x15 v0
  let v2 : W := UInt256.mulMod x4 x2 x3
  {s with pc := N 5733, memory := s.memory, stack := v2 :: x12 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: v1 :: x14 :: x15 :: x16 :: x17 :: x18 :: rest}

theorem sq0Newpart1_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions sq0Newpart1Program {s with pc := N 5725, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: x18 :: rest} =
      some (sq0Newpart1Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 19) : rest.length + j < 1024 := by omega
  simp [hz, hzn, sq0Newpart1Program, sq0Newpart1Model, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, capacity]


def sq0Newpart2Program : List Instr :=
  [.op (.Dup ⟨1, by decide⟩),
   .op (.Dup ⟨11, by decide⟩),
   .op (.Dup ⟨15, by decide⟩),
   .op .MULMOD,
   .op .ADD,
   .push 3 2048,
   .op .MULMOD,
   .push 2 768,
   .op .MLOAD]

def sq0Newpart2Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 : W) (rest : List W) : State :=
  let v0 : W := UInt256.mulMod x13 x10 x1
  let v1 : W := v0 + x0
  let v2 : W := UInt256.mulMod (N 2048) v1 x1
  let v3 : W := MachineState.readWord s.memory 768
  {s with pc := N 5747, memory := s.memory, stack := v3 :: v2 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: rest}

theorem sq0Newpart2_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions sq0Newpart2Program {s with pc := N 5733, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: rest} =
      some (sq0Newpart2Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 19) : rest.length + j < 1024 := by omega
  have ha768 : (768 : W).toNat = 768 := rfl
  have hf768 := Monpro.activeWords_fix s 768 32 (by decide) (by norm_num) hact
  simp [hz, hzn, sq0Newpart2Program, sq0Newpart2Model, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, capacity, ha768, hf768]


def sq0Newpart3Program : List Instr :=
  [.op (.Dup ⟨9, by decide⟩),
   .op (.Dup ⟨1, by decide⟩),
   .op (.Dup ⟨7, by decide⟩),
   .op .MULMOD,
   .op (.Dup ⟨0, by decide⟩),
   .op .ADD,
   .op (.Swap ⟨0, by decide⟩),
   .op (.Dup ⟨6, by decide⟩)]

def sq0Newpart3Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 : W) (rest : List W) : State :=
  let v0 : W := UInt256.mulMod x5 x0 x9
  let v1 : W := v0 + v0
  {s with pc := N 5755, memory := s.memory, stack := x5 :: x0 :: v1 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: rest}

theorem sq0Newpart3_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions sq0Newpart3Program {s with pc := N 5747, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: rest} =
      some (sq0Newpart3Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 19) : rest.length + j < 1024 := by omega
  simp [hz, hzn, sq0Newpart3Program, sq0Newpart3Model, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, capacity]


def sq0Newpart4Program : List Instr :=
  [.op .MUL,
   .op (.Dup ⟨0, by decide⟩),
   .op .ADD,
   .op (.Dup ⟨2, by decide⟩),
   .op .ADD,
   .op (.Dup ⟨11, by decide⟩),
   .op (.Dup ⟨13, by decide⟩),
   .op .MUL]

def sq0Newpart4Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 : W) (rest : List W) : State :=
  let v0 : W := x0 * x1
  let v1 : W := v0 + v0
  let v2 : W := x3 + v1
  let v3 : W := x13 * x12
  {s with pc := N 5763, memory := s.memory, stack := v3 :: v2 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: rest}

theorem sq0Newpart4_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions sq0Newpart4Program {s with pc := N 5755, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: rest} =
      some (sq0Newpart4Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 19) : rest.length + j < 1024 := by omega
  simp [hz, hzn, sq0Newpart4Program, sq0Newpart4Model, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, capacity]


def sq0Newpart5Program : List Instr :=
  [.op .ADD,
   .op (.Swap ⟨1, by decide⟩),
   .op .ADD,
   .op (.Dup ⟨9, by decide⟩),
   .op (.Dup ⟨12, by decide⟩),
   .op (.Dup ⟨12, by decide⟩),
   .op .MULMOD,
   .op .ADD]

def sq0Newpart5Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 : W) (rest : List W) : State :=
  let v0 : W := x0 + x1
  let v1 : W := x3 + x2
  let v2 : W := UInt256.mulMod x12 x13 x11
  let v3 : W := v2 + v1
  {s with pc := N 5771, memory := s.memory, stack := v3 :: v0 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: rest}

theorem sq0Newpart5_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions sq0Newpart5Program {s with pc := N 5763, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: rest} =
      some (sq0Newpart5Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 19) : rest.length + j < 1024 := by omega
  simp [hz, hzn, sq0Newpart5Program, sq0Newpart5Model, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, capacity]


def sq0Newpart6Program : List Instr :=
  [.op (.Dup ⟨9, by decide⟩),
   .op (.Dup ⟨14, by decide⟩),
   .push 2 2720,
   .op .MLOAD,
   .op (.Dup ⟨2, by decide⟩),
   .op (.Swap ⟨4, by decide⟩),
   .op .MUL,
   .op (.Dup ⟨15, by decide⟩)]

def sq0Newpart6Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 : W) (rest : List W) : State :=
  let v0 : W := MachineState.readWord s.memory 2720
  let v1 : W := x1 * v0
  {s with pc := N 5781, memory := s.memory, stack := x12 :: v1 :: x13 :: x9 :: x0 :: x9 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: rest}

theorem sq0Newpart6_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions sq0Newpart6Program {s with pc := N 5771, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: rest} =
      some (sq0Newpart6Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 20) : rest.length + j < 1024 := by omega
  have ha2720 : (2720 : W).toNat = 2720 := rfl
  have hf2720 := Monpro.activeWords_fix s 2720 32 (by decide) (by norm_num) hact
  simp [hz, hzn, sq0Newpart6Program, sq0Newpart6Model, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, capacity, ha2720, hf2720]


def sq0Newpart7Program : List Instr :=
  [.op .AND,
   .op (.Dup ⟨0, by decide⟩),
   .op (.Swap ⟨11, by decide⟩),
   .op .POP,
   .op .MULMOD,
   .op .ADD,
   .push 2 2048,
   .op .MULMOD]

def sq0Newpart7Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 : W) (rest : List W) : State :=
  let v0 : W := UInt256.land x0 x1
  let v1 : W := UInt256.mulMod v0 x2 x3
  let v2 : W := v1 + x4
  let v3 : W := UInt256.mulMod (N 2048) v2 x5
  {s with pc := N 5791, memory := s.memory, stack := v3 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: v0 :: x13 :: x14 :: x15 :: x16 :: x17 :: x18 :: x19 :: rest}

theorem sq0Newpart7_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions sq0Newpart7Program {s with pc := N 5781, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: x18 :: x19 :: rest} =
      some (sq0Newpart7Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 20) : rest.length + j < 1024 := by omega
  simp [hz, hzn, sq0Newpart7Program, sq0Newpart7Model, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, capacity]


def sq0Newpart8Program : List Instr :=
  [.push 3 768,
   .op .MLOAD,
   .op (.Dup ⟨2, by decide⟩),
   .op (.Dup ⟨11, by decide⟩),
   .op .MUL,
   .op (.Dup ⟨6, by decide⟩),
   .op (.Dup ⟨0, by decide⟩),
   .op .MUL]

def sq0Newpart8Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 : W) (rest : List W) : State :=
  let v0 : W := MachineState.readWord s.memory 768
  let v1 : W := x9 * x1
  let v2 : W := x4 * x4
  {s with pc := N 5802, memory := s.memory, stack := v2 :: v1 :: v0 :: x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: rest}

theorem sq0Newpart8_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions sq0Newpart8Program {s with pc := N 5791, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: rest} =
      some (sq0Newpart8Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 19) : rest.length + j < 1024 := by omega
  have ha768 : (768 : W).toNat = 768 := rfl
  have hf768 := Monpro.activeWords_fix s 768 32 (by decide) (by norm_num) hact
  simp [hz, hzn, sq0Newpart8Program, sq0Newpart8Model, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, capacity, ha768, hf768]


def sq0Newpart9Program : List Instr :=
  [.op (.Dup ⟨11, by decide⟩),
   .op (.Dup ⟨3, by decide⟩),
   .op (.Dup ⟨10, by decide⟩),
   .op .MULMOD,
   .op (.Dup ⟨0, by decide⟩),
   .op .ADD,
   .op (.Swap ⟨2, by decide⟩),
   .op (.Dup ⟨9, by decide⟩)]

def sq0Newpart9Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 : W) (rest : List W) : State :=
  let v0 : W := UInt256.mulMod x8 x2 x11
  let v1 : W := v0 + v0
  {s with pc := N 5810, memory := s.memory, stack := x8 :: x2 :: x0 :: x1 :: v1 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: rest}

theorem sq0Newpart9_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions sq0Newpart9Program {s with pc := N 5802, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: rest} =
      some (sq0Newpart9Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 21) : rest.length + j < 1024 := by omega
  simp [hz, hzn, sq0Newpart9Program, sq0Newpart9Model, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, capacity]


def sq0Newpart10Program : List Instr :=
  [.op .MUL,
   .op (.Dup ⟨0, by decide⟩),
   .op .ADD,
   .op (.Dup ⟨4, by decide⟩),
   .op .ADD,
   .op .ADD,
   .op .ADD,
   .op (.Dup ⟨9, by decide⟩)]

def sq0Newpart10Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 : W) (rest : List W) : State :=
  let v0 : W := x0 * x1
  let v1 : W := v0 + v0
  let v2 : W := x5 + v1
  let v3 : W := v2 + x2
  let v4 : W := v3 + x3
  {s with pc := N 5818, memory := s.memory, stack := x12 :: v4 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: x18 :: x19 :: rest}

theorem sq0Newpart10_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions sq0Newpart10Program {s with pc := N 5810, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: x18 :: x19 :: rest} =
      some (sq0Newpart10Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 20) : rest.length + j < 1024 := by omega
  simp [hz, hzn, sq0Newpart10Program, sq0Newpart10Model, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, capacity]


def sq0Newpart11Program : List Instr :=
  [.op (.Dup ⟨13, by decide⟩),
   .op .MUL,
   .op .ADD,
   .op (.Swap ⟨1, by decide⟩),
   .op .ADD,
   .op (.Dup ⟨9, by decide⟩),
   .op (.Dup ⟨6, by decide⟩),
   .op (.Dup ⟨0, by decide⟩)]

def sq0Newpart11Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 : W) (rest : List W) : State :=
  let v0 : W := x13 * x0
  let v1 : W := v0 + x1
  let v2 : W := x3 + x2
  {s with pc := N 5826, memory := s.memory, stack := x7 :: x7 :: x11 :: v2 :: v1 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: rest}

theorem sq0Newpart11_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions sq0Newpart11Program {s with pc := N 5818, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: rest} =
      some (sq0Newpart11Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 19) : rest.length + j < 1024 := by omega
  simp [hz, hzn, sq0Newpart11Program, sq0Newpart11Model, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, capacity]


def sq0Newpart12Program : List Instr :=
  [.op .MULMOD,
   .op .ADD,
   .op (.Dup ⟨9, by decide⟩),
   .op (.Dup ⟨3, by decide⟩),
   .op (.Dup ⟨12, by decide⟩),
   .op .MULMOD,
   .op .ADD,
   .op (.Dup ⟨9, by decide⟩)]

def sq0Newpart12Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 : W) (rest : List W) : State :=
  let v0 : W := UInt256.mulMod x0 x1 x2
  let v1 : W := v0 + x3
  let v2 : W := UInt256.mulMod x13 x5 x12
  let v3 : W := v2 + v1
  {s with pc := N 5834, memory := s.memory, stack := x12 :: v3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: x18 :: rest}

theorem sq0Newpart12_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions sq0Newpart12Program {s with pc := N 5826, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: x18 :: rest} =
      some (sq0Newpart12Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 19) : rest.length + j < 1024 := by omega
  simp [hz, hzn, sq0Newpart12Program, sq0Newpart12Model, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, capacity]


def sq0Newpart13Program : List Instr :=
  [.op (.Dup ⟨12, by decide⟩),
   .op (.Dup ⟨10, by decide⟩),
   .op .MULMOD,
   .op .ADD,
   .op (.Dup ⟨9, by decide⟩),
   .op (.Dup ⟨14, by decide⟩)]

def sq0Newpart13Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 : W) (rest : List W) : State :=
  let v0 : W := UInt256.mulMod x9 x12 x0
  let v1 : W := v0 + x1
  {s with pc := N 5840, memory := s.memory, stack := x14 :: x10 :: v1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: rest}

theorem sq0Newpart13_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions sq0Newpart13Program {s with pc := N 5834, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: rest} =
      some (sq0Newpart13Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 19) : rest.length + j < 1024 := by omega
  simp [hz, hzn, sq0Newpart13Program, sq0Newpart13Model, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, capacity]


def sq0NewProgram : List Instr :=
  [.push 2 768,
   .op .MLOAD,
   .op (.Dup ⟨8, by decide⟩),
   .op (.Dup ⟨1, by decide⟩),
   .op (.Dup ⟨0, by decide⟩),
   .op (.Dup ⟨0, by decide⟩),
   .op .MUL,
   .push 2 2720,
   .op .MLOAD,
   .op .MUL,
   .op (.Dup ⟨14, by decide⟩),
   .op .AND,
   .op (.Swap ⟨11, by decide⟩),
   .op .POP,
   .op (.Dup ⟨10, by decide⟩),
   .op (.Swap ⟨2, by decide⟩),
   .op .MULMOD,
   .op (.Dup ⟨1, by decide⟩),
   .op (.Dup ⟨11, by decide⟩),
   .op (.Dup ⟨15, by decide⟩),
   .op .MULMOD,
   .op .ADD,
   .push 3 2048,
   .op .MULMOD,
   .push 2 768,
   .op .MLOAD,
   .op (.Dup ⟨9, by decide⟩),
   .op (.Dup ⟨1, by decide⟩),
   .op (.Dup ⟨7, by decide⟩),
   .op .MULMOD,
   .op (.Dup ⟨0, by decide⟩),
   .op .ADD,
   .op (.Swap ⟨0, by decide⟩),
   .op (.Dup ⟨6, by decide⟩),
   .op .MUL,
   .op (.Dup ⟨0, by decide⟩),
   .op .ADD,
   .op (.Dup ⟨2, by decide⟩),
   .op .ADD,
   .op (.Dup ⟨11, by decide⟩),
   .op (.Dup ⟨13, by decide⟩),
   .op .MUL,
   .op .ADD,
   .op (.Swap ⟨1, by decide⟩),
   .op .ADD,
   .op (.Dup ⟨9, by decide⟩),
   .op (.Dup ⟨12, by decide⟩),
   .op (.Dup ⟨12, by decide⟩),
   .op .MULMOD,
   .op .ADD,
   .op (.Dup ⟨9, by decide⟩),
   .op (.Dup ⟨14, by decide⟩),
   .push 2 2720,
   .op .MLOAD,
   .op (.Dup ⟨2, by decide⟩),
   .op (.Swap ⟨4, by decide⟩),
   .op .MUL,
   .op (.Dup ⟨15, by decide⟩),
   .op .AND,
   .op (.Dup ⟨0, by decide⟩),
   .op (.Swap ⟨11, by decide⟩),
   .op .POP,
   .op .MULMOD,
   .op .ADD,
   .push 2 2048,
   .op .MULMOD,
   .push 3 768,
   .op .MLOAD,
   .op (.Dup ⟨2, by decide⟩),
   .op (.Dup ⟨11, by decide⟩),
   .op .MUL,
   .op (.Dup ⟨6, by decide⟩),
   .op (.Dup ⟨0, by decide⟩),
   .op .MUL,
   .op (.Dup ⟨11, by decide⟩),
   .op (.Dup ⟨3, by decide⟩),
   .op (.Dup ⟨10, by decide⟩),
   .op .MULMOD,
   .op (.Dup ⟨0, by decide⟩),
   .op .ADD,
   .op (.Swap ⟨2, by decide⟩),
   .op (.Dup ⟨9, by decide⟩),
   .op .MUL,
   .op (.Dup ⟨0, by decide⟩),
   .op .ADD,
   .op (.Dup ⟨4, by decide⟩),
   .op .ADD,
   .op .ADD,
   .op .ADD,
   .op (.Dup ⟨9, by decide⟩),
   .op (.Dup ⟨13, by decide⟩),
   .op .MUL,
   .op .ADD,
   .op (.Swap ⟨1, by decide⟩),
   .op .ADD,
   .op (.Dup ⟨9, by decide⟩),
   .op (.Dup ⟨6, by decide⟩),
   .op (.Dup ⟨0, by decide⟩),
   .op .MULMOD,
   .op .ADD,
   .op (.Dup ⟨9, by decide⟩),
   .op (.Dup ⟨3, by decide⟩),
   .op (.Dup ⟨12, by decide⟩),
   .op .MULMOD,
   .op .ADD,
   .op (.Dup ⟨9, by decide⟩),
   .op (.Dup ⟨12, by decide⟩),
   .op (.Dup ⟨10, by decide⟩),
   .op .MULMOD,
   .op .ADD,
   .op (.Dup ⟨9, by decide⟩),
   .op (.Dup ⟨14, by decide⟩)]

def sq0NewModel (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 : W) (rest : List W) : State :=
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

theorem sq0New_run (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions sq0NewProgram {s with pc := N 5712, stack := w0 :: w1 :: w2 :: w3 :: w4 :: w5 :: w6 :: w7 :: w8 :: w9 :: w10 :: w11 :: w12 :: w13 :: rest} =
      some (sq0NewModel s w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 rest) := by
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
  have h0 : runInstructions sq0Newpart0Program {s with pc := N 5712, memory := s.memory, stack := w0 :: w1 :: w2 :: w3 :: w4 :: w5 :: w6 :: w7 :: w8 :: w9 :: w10 :: w11 :: w12 :: w13 :: rest} = some {s with pc := N 5725, memory := s.memory, stack := v2 :: v1 :: v0 :: w7 :: v0 :: w0 :: w1 :: w2 :: w3 :: w4 :: w5 :: w6 :: w7 :: w8 :: w9 :: w10 :: w11 :: w12 :: w13 :: rest} := by
    simpa only [sq0Newpart0Model, v0, v1, v2] using sq0Newpart0_run (s) (w0) (w1) (w2) (w3) (w4) (w5) (w6) (w7) (w8) (w9) (w10) (w11) (w12) (w13) rest hcap hact
  have h1 : runInstructions sq0Newpart1Program {s with pc := N 5725, memory := s.memory, stack := v2 :: v1 :: v0 :: w7 :: v0 :: w0 :: w1 :: w2 :: w3 :: w4 :: w5 :: w6 :: w7 :: w8 :: w9 :: w10 :: w11 :: w12 :: w13 :: rest} = some {s with pc := N 5733, memory := s.memory, stack := v5 :: w7 :: w0 :: w1 :: w2 :: w3 :: w4 :: w5 :: w6 :: w7 :: v4 :: w9 :: w10 :: w11 :: w12 :: w13 :: rest} := by
    simpa only [sq0Newpart1Model, v3, v4, v5] using sq0Newpart1_run (s) (v2) (v1) (v0) (w7) (v0) (w0) (w1) (w2) (w3) (w4) (w5) (w6) (w7) (w8) (w9) (w10) (w11) (w12) (w13) rest hcap hact
  have h2 : runInstructions sq0Newpart2Program {s with pc := N 5733, memory := s.memory, stack := v5 :: w7 :: w0 :: w1 :: w2 :: w3 :: w4 :: w5 :: w6 :: w7 :: v4 :: w9 :: w10 :: w11 :: w12 :: w13 :: rest} = some {s with pc := N 5747, memory := s.memory, stack := v9 :: v8 :: w0 :: w1 :: w2 :: w3 :: w4 :: w5 :: w6 :: w7 :: v4 :: w9 :: w10 :: w11 :: w12 :: w13 :: rest} := by
    simpa only [sq0Newpart2Model, v6, v7, v8, v9] using sq0Newpart2_run (s) (v5) (w7) (w0) (w1) (w2) (w3) (w4) (w5) (w6) (w7) (v4) (w9) (w10) (w11) (w12) (w13) rest hcap hact
  have h3 : runInstructions sq0Newpart3Program {s with pc := N 5747, memory := s.memory, stack := v9 :: v8 :: w0 :: w1 :: w2 :: w3 :: w4 :: w5 :: w6 :: w7 :: v4 :: w9 :: w10 :: w11 :: w12 :: w13 :: rest} = some {s with pc := N 5755, memory := s.memory, stack := w3 :: v9 :: v11 :: v8 :: w0 :: w1 :: w2 :: w3 :: w4 :: w5 :: w6 :: w7 :: v4 :: w9 :: w10 :: w11 :: w12 :: w13 :: rest} := by
    simpa only [sq0Newpart3Model, v10, v11] using sq0Newpart3_run (s) (v9) (v8) (w0) (w1) (w2) (w3) (w4) (w5) (w6) (w7) (v4) (w9) (w10) (w11) (w12) (w13) rest hcap hact
  have h4 : runInstructions sq0Newpart4Program {s with pc := N 5755, memory := s.memory, stack := w3 :: v9 :: v11 :: v8 :: w0 :: w1 :: w2 :: w3 :: w4 :: w5 :: w6 :: w7 :: v4 :: w9 :: w10 :: w11 :: w12 :: w13 :: rest} = some {s with pc := N 5763, memory := s.memory, stack := v15 :: v14 :: v11 :: v8 :: w0 :: w1 :: w2 :: w3 :: w4 :: w5 :: w6 :: w7 :: v4 :: w9 :: w10 :: w11 :: w12 :: w13 :: rest} := by
    simpa only [sq0Newpart4Model, v12, v13, v14, v15] using sq0Newpart4_run (s) (w3) (v9) (v11) (v8) (w0) (w1) (w2) (w3) (w4) (w5) (w6) (w7) (v4) (w9) (w10) (w11) (w12) (w13) rest hcap hact
  have h5 : runInstructions sq0Newpart5Program {s with pc := N 5763, memory := s.memory, stack := v15 :: v14 :: v11 :: v8 :: w0 :: w1 :: w2 :: w3 :: w4 :: w5 :: w6 :: w7 :: v4 :: w9 :: w10 :: w11 :: w12 :: w13 :: rest} = some {s with pc := N 5771, memory := s.memory, stack := v19 :: v16 :: w0 :: w1 :: w2 :: w3 :: w4 :: w5 :: w6 :: w7 :: v4 :: w9 :: w10 :: w11 :: w12 :: w13 :: rest} := by
    simpa only [sq0Newpart5Model, v16, v17, v18, v19] using sq0Newpart5_run (s) (v15) (v14) (v11) (v8) (w0) (w1) (w2) (w3) (w4) (w5) (w6) (w7) (v4) (w9) (w10) (w11) (w12) (w13) rest hcap hact
  have h6 : runInstructions sq0Newpart6Program {s with pc := N 5771, memory := s.memory, stack := v19 :: v16 :: w0 :: w1 :: w2 :: w3 :: w4 :: w5 :: w6 :: w7 :: v4 :: w9 :: w10 :: w11 :: w12 :: w13 :: rest} = some {s with pc := N 5781, memory := s.memory, stack := w10 :: v21 :: w11 :: w7 :: v19 :: w7 :: w0 :: w1 :: w2 :: w3 :: w4 :: w5 :: w6 :: w7 :: v4 :: w9 :: w10 :: w11 :: w12 :: w13 :: rest} := by
    simpa only [sq0Newpart6Model, v20, v21] using sq0Newpart6_run (s) (v19) (v16) (w0) (w1) (w2) (w3) (w4) (w5) (w6) (w7) (v4) (w9) (w10) (w11) (w12) (w13) rest hcap hact
  have h7 : runInstructions sq0Newpart7Program {s with pc := N 5781, memory := s.memory, stack := w10 :: v21 :: w11 :: w7 :: v19 :: w7 :: w0 :: w1 :: w2 :: w3 :: w4 :: w5 :: w6 :: w7 :: v4 :: w9 :: w10 :: w11 :: w12 :: w13 :: rest} = some {s with pc := N 5791, memory := s.memory, stack := v25 :: w0 :: w1 :: w2 :: w3 :: w4 :: w5 :: v22 :: w7 :: v4 :: w9 :: w10 :: w11 :: w12 :: w13 :: rest} := by
    simpa only [sq0Newpart7Model, v22, v23, v24, v25] using sq0Newpart7_run (s) (w10) (v21) (w11) (w7) (v19) (w7) (w0) (w1) (w2) (w3) (w4) (w5) (w6) (w7) (v4) (w9) (w10) (w11) (w12) (w13) rest hcap hact
  have h8 : runInstructions sq0Newpart8Program {s with pc := N 5791, memory := s.memory, stack := v25 :: w0 :: w1 :: w2 :: w3 :: w4 :: w5 :: v22 :: w7 :: v4 :: w9 :: w10 :: w11 :: w12 :: w13 :: rest} = some {s with pc := N 5802, memory := s.memory, stack := v28 :: v27 :: v26 :: v25 :: w0 :: w1 :: w2 :: w3 :: w4 :: w5 :: v22 :: w7 :: v4 :: w9 :: w10 :: w11 :: w12 :: w13 :: rest} := by
    simpa only [sq0Newpart8Model, v26, v27, v28] using sq0Newpart8_run (s) (v25) (w0) (w1) (w2) (w3) (w4) (w5) (v22) (w7) (v4) (w9) (w10) (w11) (w12) (w13) rest hcap hact
  have h9 : runInstructions sq0Newpart9Program {s with pc := N 5802, memory := s.memory, stack := v28 :: v27 :: v26 :: v25 :: w0 :: w1 :: w2 :: w3 :: w4 :: w5 :: v22 :: w7 :: v4 :: w9 :: w10 :: w11 :: w12 :: w13 :: rest} = some {s with pc := N 5810, memory := s.memory, stack := w4 :: v26 :: v28 :: v27 :: v30 :: v25 :: w0 :: w1 :: w2 :: w3 :: w4 :: w5 :: v22 :: w7 :: v4 :: w9 :: w10 :: w11 :: w12 :: w13 :: rest} := by
    simpa only [sq0Newpart9Model, v29, v30] using sq0Newpart9_run (s) (v28) (v27) (v26) (v25) (w0) (w1) (w2) (w3) (w4) (w5) (v22) (w7) (v4) (w9) (w10) (w11) (w12) (w13) rest hcap hact
  have h10 : runInstructions sq0Newpart10Program {s with pc := N 5810, memory := s.memory, stack := w4 :: v26 :: v28 :: v27 :: v30 :: v25 :: w0 :: w1 :: w2 :: w3 :: w4 :: w5 :: v22 :: w7 :: v4 :: w9 :: w10 :: w11 :: w12 :: w13 :: rest} = some {s with pc := N 5818, memory := s.memory, stack := v22 :: v35 :: v30 :: v25 :: w0 :: w1 :: w2 :: w3 :: w4 :: w5 :: v22 :: w7 :: v4 :: w9 :: w10 :: w11 :: w12 :: w13 :: rest} := by
    simpa only [sq0Newpart10Model, v31, v32, v33, v34, v35] using sq0Newpart10_run (s) (w4) (v26) (v28) (v27) (v30) (v25) (w0) (w1) (w2) (w3) (w4) (w5) (v22) (w7) (v4) (w9) (w10) (w11) (w12) (w13) rest hcap hact
  have h11 : runInstructions sq0Newpart11Program {s with pc := N 5818, memory := s.memory, stack := v22 :: v35 :: v30 :: v25 :: w0 :: w1 :: w2 :: w3 :: w4 :: w5 :: v22 :: w7 :: v4 :: w9 :: w10 :: w11 :: w12 :: w13 :: rest} = some {s with pc := N 5826, memory := s.memory, stack := w3 :: w3 :: w7 :: v38 :: v37 :: w0 :: w1 :: w2 :: w3 :: w4 :: w5 :: v22 :: w7 :: v4 :: w9 :: w10 :: w11 :: w12 :: w13 :: rest} := by
    simpa only [sq0Newpart11Model, v36, v37, v38] using sq0Newpart11_run (s) (v22) (v35) (v30) (v25) (w0) (w1) (w2) (w3) (w4) (w5) (v22) (w7) (v4) (w9) (w10) (w11) (w12) (w13) rest hcap hact
  have h12 : runInstructions sq0Newpart12Program {s with pc := N 5826, memory := s.memory, stack := w3 :: w3 :: w7 :: v38 :: v37 :: w0 :: w1 :: w2 :: w3 :: w4 :: w5 :: v22 :: w7 :: v4 :: w9 :: w10 :: w11 :: w12 :: w13 :: rest} = some {s with pc := N 5834, memory := s.memory, stack := w7 :: v42 :: v37 :: w0 :: w1 :: w2 :: w3 :: w4 :: w5 :: v22 :: w7 :: v4 :: w9 :: w10 :: w11 :: w12 :: w13 :: rest} := by
    simpa only [sq0Newpart12Model, v39, v40, v41, v42] using sq0Newpart12_run (s) (w3) (w3) (w7) (v38) (v37) (w0) (w1) (w2) (w3) (w4) (w5) (v22) (w7) (v4) (w9) (w10) (w11) (w12) (w13) rest hcap hact
  have h13 : runInstructions sq0Newpart13Program {s with pc := N 5834, memory := s.memory, stack := w7 :: v42 :: v37 :: w0 :: w1 :: w2 :: w3 :: w4 :: w5 :: v22 :: w7 :: v4 :: w9 :: w10 :: w11 :: w12 :: w13 :: rest} = some {s with pc := N 5840, memory := s.memory, stack := w11 :: w7 :: v44 :: v37 :: w0 :: w1 :: w2 :: w3 :: w4 :: w5 :: v22 :: w7 :: v4 :: w9 :: w10 :: w11 :: w12 :: w13 :: rest} := by
    simpa only [sq0Newpart13Model, v43, v44] using sq0Newpart13_run (s) (w7) (v42) (v37) (w0) (w1) (w2) (w3) (w4) (w5) (v22) (w7) (v4) (w9) (w10) (w11) (w12) (w13) rest hcap hact
  exact (runInstructions_append_some _ _ _ _ _ h0 (runInstructions_append_some _ _ _ _ _ h1 (runInstructions_append_some _ _ _ _ _ h2 (runInstructions_append_some _ _ _ _ _ h3 (runInstructions_append_some _ _ _ _ _ h4 (runInstructions_append_some _ _ _ _ _ h5 (runInstructions_append_some _ _ _ _ _ h6 (runInstructions_append_some _ _ _ _ _ h7 (runInstructions_append_some _ _ _ _ _ h8 (runInstructions_append_some _ _ _ _ _ h9 (runInstructions_append_some _ _ _ _ _ h10 (runInstructions_append_some _ _ _ _ _ h11 (runInstructions_append_some _ _ _ _ _ h12 h13)))))))))))))

#print axioms sq0New_run

def squareColumn0Model (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 : W) (rest : List W) : State :=
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
  let v10 : W := w3 * v9
  let v11 : W := v10 + v10
  let v12 : W := UInt256.mulMod w3 v9 w7
  let v13 : W := v12 + v12
  let v14 : W := v8 + v13
  let v15 : W := v8 + v11
  let v16 : W := v4 * w9
  let v17 : W := v16 + v15
  let v18 : W := UInt256.mulMod v4 w9 w7
  let v19 : W := v18 + v14
  let v20 : W := MachineState.readWord s.memory 2720
  let v21 : W := v17 * v20
  let v22 : W := UInt256.land w10 v21
  let v23 : W := UInt256.mulMod v22 w11 w7
  let v24 : W := v23 + v19
  let v25 : W := UInt256.mulMod (N 2048) v24 w7
  let v26 : W := MachineState.readWord s.memory 768
  let v27 : W := w4 * v26
  let v28 : W := v27 + v27
  let v29 : W := UInt256.mulMod w4 v26 w7
  let v30 : W := v29 + v29
  let v31 : W := v25 + v30
  let v32 : W := v25 + v28
  let v33 : W := w3 * w3
  let v34 : W := v33 + v32
  let v35 : W := v4 * w0
  let v36 : W := v35 + v34
  let v37 : W := v22 * w9
  let v38 : W := v37 + v36
  let v39 : W := UInt256.mulMod w3 w3 w7
  let v40 : W := v39 + v31
  let v41 : W := UInt256.mulMod v4 w0 w7
  let v42 : W := v41 + v40
  let v43 : W := UInt256.mulMod v22 w9 w7
  let v44 : W := v43 + v42
  {s with pc := N 5840, memory := s.memory, stack := w11 :: w7 :: v44 :: v38 :: w0 :: w1 :: w2 :: w3 :: w4 :: w5 :: v22 :: w7 :: v4 :: w9 :: w10 :: w11 :: w12 :: w13 :: rest}

def squareColumn0Program : List Instr := sq0NewProgram

private theorem aux_shared0 (w9 : W) (z0 : W) :
    (w9 * z0) = (z0 * w9) := by
  simp (disch := decide) only [addC, addA, addL, mulC, mmC, amC, andC, orC, xorC, eqC, read_disjoint, Challenge.EvmProof.Memory.readWord_writeWord]

private theorem aux_shared1 (z0 z1 : W) :
    (z0 + z1) = (z1 + z0) := by
  simp (disch := decide) only [addC, addA, addL, mulC, mmC, amC, andC, orC, xorC, eqC, read_disjoint, Challenge.EvmProof.Memory.readWord_writeWord]

private theorem prepared_model_eq (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 : W) (rest : List W) :
    squareColumn0Model s w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 rest = sq0NewModel s w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 rest := by
  let o0 : W := MachineState.readWord s.memory 768
  let o1 : W := o0 * o0
  let o2 : W := MachineState.readWord s.memory 2720
  let o3 : W := o2 * o1
  let o4 : W := UInt256.land w10 o3
  let o5 : W := UInt256.mulMod o0 o0 w7
  let o6 : W := UInt256.mulMod w11 o4 w7
  let o7 : W := o6 + o5
  let o8 : W := UInt256.mulMod (N 2048) o7 w7
  let o9 : W := MachineState.readWord s.memory 768
  let o10 : W := w3 * o9
  let o11 : W := o10 + o10
  let o12 : W := UInt256.mulMod w3 o9 w7
  let o13 : W := o12 + o12
  let o14 : W := o8 + o13
  let o15 : W := o8 + o11
  let o16 : W := o4 * w9
  let o17 : W := o16 + o15
  let o18 : W := UInt256.mulMod o4 w9 w7
  let o19 : W := o18 + o14
  let o20 : W := MachineState.readWord s.memory 2720
  let o21 : W := o17 * o20
  let o22 : W := UInt256.land w10 o21
  let o23 : W := UInt256.mulMod o22 w11 w7
  let o24 : W := o23 + o19
  let o25 : W := UInt256.mulMod (N 2048) o24 w7
  let o26 : W := MachineState.readWord s.memory 768
  let o27 : W := w4 * o26
  let o28 : W := o27 + o27
  let o29 : W := UInt256.mulMod w4 o26 w7
  let o30 : W := o29 + o29
  let o31 : W := o25 + o30
  let o32 : W := o25 + o28
  let o33 : W := w3 * w3
  let o34 : W := o33 + o32
  let o35 : W := o4 * w0
  let o36 : W := o35 + o34
  let o37 : W := o22 * w9
  let o38 : W := o37 + o36
  let o39 : W := UInt256.mulMod w3 w3 w7
  let o40 : W := o39 + o31
  let o41 : W := UInt256.mulMod o4 w0 w7
  let o42 : W := o41 + o40
  let o43 : W := UInt256.mulMod o22 w9 w7
  let o44 : W := o43 + o42
  let n0 : W := MachineState.readWord s.memory 768
  let n1 : W := n0 * n0
  let n2 : W := MachineState.readWord s.memory 2720
  let n3 : W := n2 * n1
  let n4 : W := UInt256.land w10 n3
  let n5 : W := UInt256.mulMod n0 n0 w7
  let n6 : W := UInt256.mulMod w11 n4 w7
  let n7 : W := n6 + n5
  let n8 : W := UInt256.mulMod (N 2048) n7 w7
  let n9 : W := MachineState.readWord s.memory 768
  let n10 : W := UInt256.mulMod w3 n9 w7
  let n11 : W := n10 + n10
  let n12 : W := w3 * n9
  let n13 : W := n12 + n12
  let n14 : W := n8 + n13
  let n15 : W := w9 * n4
  let n16 : W := n15 + n14
  let n17 : W := n8 + n11
  let n18 : W := UInt256.mulMod n4 w9 w7
  let n19 : W := n18 + n17
  let n20 : W := MachineState.readWord s.memory 2720
  let n21 : W := n16 * n20
  let n22 : W := UInt256.land w10 n21
  let n23 : W := UInt256.mulMod n22 w11 w7
  let n24 : W := n23 + n19
  let n25 : W := UInt256.mulMod (N 2048) n24 w7
  let n26 : W := MachineState.readWord s.memory 768
  let n27 : W := n4 * w0
  let n28 : W := w3 * w3
  let n29 : W := UInt256.mulMod w4 n26 w7
  let n30 : W := n29 + n29
  let n31 : W := w4 * n26
  let n32 : W := n31 + n31
  let n33 : W := n25 + n32
  let n34 : W := n33 + n28
  let n35 : W := n34 + n27
  let n36 : W := w9 * n22
  let n37 : W := n36 + n35
  let n38 : W := n25 + n30
  let n39 : W := UInt256.mulMod w3 w3 w7
  let n40 : W := n39 + n38
  let n41 : W := UInt256.mulMod n4 w0 w7
  let n42 : W := n41 + n40
  let n43 : W := UInt256.mulMod n22 w9 w7
  let n44 : W := n43 + n42
  have eq_o9 : o9 = o0 := by
    simp only [o9, o0]
  have eq_o20 : o20 = o2 := by
    simp only [o20, o2]
  have eq_o26 : o26 = o0 := by
    simp only [o26, o0]
  have eq_n0 : n0 = o0 := by
    simp only [n0, o0]
  have eq_n1 : n1 = o1 := by
    simp only [n1, o1, eq_n0]
  have eq_n2 : n2 = o2 := by
    simp only [n2, o2]
  have eq_n3 : n3 = o3 := by
    simp only [n3, o3, eq_n2, eq_n1]
  have eq_n4 : n4 = o4 := by
    simp only [n4, o4, eq_n3]
  have eq_n5 : n5 = o5 := by
    simp only [n5, o5, eq_n0]
  have eq_n6 : n6 = o6 := by
    simp only [n6, o6, eq_n4]
  have eq_n7 : n7 = o7 := by
    simp only [n7, o7, eq_n6, eq_n5]
  have eq_n8 : n8 = o8 := by
    simp only [n8, o8, eq_n7]
  have eq_n9 : n9 = o0 := by
    simp only [n9, o0]
  have eq_n10 : n10 = o12 := by
    simp only [n10, o12, eq_n9, eq_o9]
  have eq_n11 : n11 = o13 := by
    simp only [n11, o13, eq_n10]
  have eq_n12 : n12 = o10 := by
    simp only [n12, o10, eq_n9, eq_o9]
  have eq_n13 : n13 = o11 := by
    simp only [n13, o11, eq_n12]
  have eq_n14 : n14 = o15 := by
    simp only [n14, o15, eq_n8, eq_n13]
  have eq_n15 : n15 = o16 := by
    simpa only [n15, o16, eq_n4] using
      (aux_shared0 w9 o4)
  have eq_n16 : n16 = o17 := by
    simp only [n16, o17, eq_n15, eq_n14]
  have eq_n17 : n17 = o14 := by
    simp only [n17, o14, eq_n8, eq_n11]
  have eq_n18 : n18 = o18 := by
    simp only [n18, o18, eq_n4]
  have eq_n19 : n19 = o19 := by
    simp only [n19, o19, eq_n18, eq_n17]
  have eq_n20 : n20 = o2 := by
    simp only [n20, o2]
  have eq_n21 : n21 = o21 := by
    simp only [n21, o21, eq_n16, eq_n20, eq_o20]
  have eq_n22 : n22 = o22 := by
    simp only [n22, o22, eq_n21]
  have eq_n23 : n23 = o23 := by
    simp only [n23, o23, eq_n22]
  have eq_n24 : n24 = o24 := by
    simp only [n24, o24, eq_n23, eq_n19]
  have eq_n25 : n25 = o25 := by
    simp only [n25, o25, eq_n24]
  have eq_n26 : n26 = o0 := by
    simp only [n26, o0]
  have eq_n27 : n27 = o35 := by
    simp only [n27, o35, eq_n4]
  have eq_n28 : n28 = o33 := by
    simp only [n28, o33]
  have eq_n29 : n29 = o29 := by
    simp only [n29, o29, eq_n26, eq_o26]
  have eq_n30 : n30 = o30 := by
    simp only [n30, o30, eq_n29]
  have eq_n31 : n31 = o27 := by
    simp only [n31, o27, eq_n26, eq_o26]
  have eq_n32 : n32 = o28 := by
    simp only [n32, o28, eq_n31]
  have eq_n33 : n33 = o32 := by
    simp only [n33, o32, eq_n25, eq_n32]
  have eq_n34 : n34 = o34 := by
    simpa only [n34, o34, eq_n33, eq_n28] using
      (aux_shared1  o32 o33)
  have eq_n35 : n35 = o36 := by
    simpa only [n35, o36, eq_n34, eq_n27] using
      (aux_shared1  o34 o35)
  have eq_n36 : n36 = o37 := by
    simpa only [n36, o37, eq_n22] using
      (aux_shared0 w9 o22)
  have eq_n37 : n37 = o38 := by
    simp only [n37, o38, eq_n36, eq_n35]
  have eq_n38 : n38 = o31 := by
    simp only [n38, o31, eq_n25, eq_n30]
  have eq_n39 : n39 = o39 := by
    simp only [n39, o39]
  have eq_n40 : n40 = o40 := by
    simp only [n40, o40, eq_n39, eq_n38]
  have eq_n41 : n41 = o41 := by
    simp only [n41, o41, eq_n4]
  have eq_n42 : n42 = o42 := by
    simp only [n42, o42, eq_n41, eq_n40]
  have eq_n43 : n43 = o43 := by
    simp only [n43, o43, eq_n22]
  have eq_n44 : n44 = o44 := by
    simp only [n44, o44, eq_n43, eq_n42]
  change {s with pc := N 5840, memory := s.memory, stack := w11 :: w7 :: o44 :: o38 :: w0 :: w1 :: w2 :: w3 :: w4 :: w5 :: o22 :: w7 :: o4 :: w9 :: w10 :: w11 :: w12 :: w13 :: rest} =
    {s with pc := N 5840, memory := s.memory, stack := w11 :: w7 :: n44 :: n37 :: w0 :: w1 :: w2 :: w3 :: w4 :: w5 :: n22 :: w7 :: n4 :: w9 :: w10 :: w11 :: w12 :: w13 :: rest}
  simp only [eq_o9, eq_o20, eq_o26, eq_n0, eq_n1, eq_n2, eq_n3, eq_n4, eq_n5, eq_n6, eq_n7, eq_n8, eq_n9, eq_n10, eq_n11, eq_n12, eq_n13, eq_n14, eq_n15, eq_n16, eq_n17, eq_n18, eq_n19, eq_n20, eq_n21, eq_n22, eq_n23, eq_n24, eq_n25, eq_n26, eq_n27, eq_n28, eq_n29, eq_n30, eq_n31, eq_n32, eq_n33, eq_n34, eq_n35, eq_n36, eq_n37, eq_n38, eq_n39, eq_n40, eq_n41, eq_n42, eq_n43, eq_n44]
theorem squareColumn0_run (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions squareColumn0Program {s with pc := N 5712, stack := w0 :: w1 :: w2 :: w3 :: w4 :: w5 :: w6 :: w7 :: w8 :: w9 :: w10 :: w11 :: w12 :: w13 :: rest} =
      some (squareColumn0Model s w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 rest) := by
  exact (sq0New_run s w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 rest hcap hact).trans
    (congrArg some (prepared_model_eq s w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 rest).symm)

#print axioms squareColumn0_run
end CycleSubmission.Execution
