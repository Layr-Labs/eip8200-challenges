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

def sq7Newpart0Program : List Instr :=
  [.op .ADD,
   .op (.Dup ⟨4, by decide⟩),
   .push 1 224,
   .op .MLOAD,
   .op .MUL,
   .op .ADD,
   .op (.Dup ⟨14, by decide⟩),
   .push 2 1216,
   .op .MLOAD]

def sq7Newpart0Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 : W) (rest : List W) : State :=
  let v0 : W := x0 + x1
  let v1 : W := MachineState.readWord s.memory 224
  let v2 : W := v1 * x5
  let v3 : W := v2 + v0
  let v4 : W := MachineState.readWord s.memory 1216
  {s with pc := N 6603, memory := s.memory, stack := v4 :: x15 :: v3 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: rest}

theorem sq7Newpart0_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions sq7Newpart0Program {s with pc := N 6591, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: rest} =
      some (sq7Newpart0Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 18) : rest.length + j < 1024 := by omega
  have ha224 : (224 : W).toNat = 224 := rfl
  have hf224 := Monpro.activeWords_fix s 224 32 (by decide) (by norm_num) hact
  have ha1216 : (1216 : W).toNat = 1216 := rfl
  have hf1216 := Monpro.activeWords_fix s 1216 32 (by decide) (by norm_num) hact
  simp [hz, hzn, sq7Newpart0Program, sq7Newpart0Model, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, capacity, ha224, hf224, ha1216, hf1216]


def sq7Newpart1Program : List Instr :=
  [.op .MUL,
   .op .ADD,
   .op (.Dup ⟨2, by decide⟩),
   .push 2 1248,
   .op .MLOAD,
   .op .MUL,
   .op .ADD,
   .op (.Dup ⟨11, by decide⟩)]

def sq7Newpart1Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 : W) (rest : List W) : State :=
  let v0 : W := x0 * x1
  let v1 : W := v0 + x2
  let v2 : W := MachineState.readWord s.memory 1248
  let v3 : W := v2 * x4
  let v4 : W := v3 + v1
  {s with pc := N 6613, memory := s.memory, stack := x13 :: v4 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: rest}

theorem sq7Newpart1_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions sq7Newpart1Program {s with pc := N 6603, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: rest} =
      some (sq7Newpart1Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 18) : rest.length + j < 1024 := by omega
  have ha1248 : (1248 : W).toNat = 1248 := rfl
  have hf1248 := Monpro.activeWords_fix s 1248 32 (by decide) (by norm_num) hact
  simp [hz, hzn, sq7Newpart1Program, sq7Newpart1Model, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, capacity, ha1248, hf1248]


def sq7Newpart2Program : List Instr :=
  [.push 2 1280,
   .op .MLOAD,
   .op .MUL,
   .op .ADD,
   .op (.Swap ⟨0, by decide⟩),
   .op (.Dup ⟨9, by decide⟩),
   .push 1 64,
   .op .MLOAD]

def sq7Newpart2Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 : W) (rest : List W) : State :=
  let v0 : W := MachineState.readWord s.memory 1280
  let v1 : W := v0 * x0
  let v2 : W := v1 + x1
  let v3 : W := MachineState.readWord s.memory 64
  {s with pc := N 6624, memory := s.memory, stack := v3 :: x10 :: x2 :: v2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: rest}

theorem sq7Newpart2_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions sq7Newpart2Program {s with pc := N 6613, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: rest} =
      some (sq7Newpart2Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 18) : rest.length + j < 1024 := by omega
  have ha64 : (64 : W).toNat = 64 := rfl
  have hf64 := Monpro.activeWords_fix s 64 32 (by decide) (by norm_num) hact
  have ha1280 : (1280 : W).toNat = 1280 := rfl
  have hf1280 := Monpro.activeWords_fix s 1280 32 (by decide) (by norm_num) hact
  simp [hz, hzn, sq7Newpart2Program, sq7Newpart2Model, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, capacity, ha64, hf64, ha1280, hf1280]


def sq7Newpart3Program : List Instr :=
  [.op (.Dup ⟨0, by decide⟩),
   .op .MULMOD,
   .op .ADD,
   .op (.Dup ⟨9, by decide⟩),
   .push 2 1088,
   .op .MLOAD,
   .op (.Dup ⟨10, by decide⟩),
   .op .MULMOD]

def sq7Newpart3Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 : W) (rest : List W) : State :=
  let v0 : W := UInt256.mulMod x0 x0 x1
  let v1 : W := v0 + x2
  let v2 : W := MachineState.readWord s.memory 1088
  let v3 : W := UInt256.mulMod x10 v2 x11
  {s with pc := N 6634, memory := s.memory, stack := v3 :: v1 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: rest}

theorem sq7Newpart3_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions sq7Newpart3Program {s with pc := N 6624, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: rest} =
      some (sq7Newpart3Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 19) : rest.length + j < 1024 := by omega
  have ha1088 : (1088 : W).toNat = 1088 := rfl
  have hf1088 := Monpro.activeWords_fix s 1088 32 (by decide) (by norm_num) hact
  simp [hz, hzn, sq7Newpart3Program, sq7Newpart3Model, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, capacity, ha1088, hf1088]


def sq7Newpart4Program : List Instr :=
  [.op .ADD,
   .op (.Dup ⟨9, by decide⟩),
   .op (.Dup ⟨4, by decide⟩),
   .push 1 192,
   .op .MLOAD,
   .op .MULMOD,
   .op .ADD,
   .op (.Dup ⟨9, by decide⟩)]

def sq7Newpart4Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 : W) (rest : List W) : State :=
  let v0 : W := x0 + x1
  let v1 : W := MachineState.readWord s.memory 192
  let v2 : W := UInt256.mulMod v1 x4 x10
  let v3 : W := v2 + v0
  {s with pc := N 6643, memory := s.memory, stack := x10 :: v3 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: rest}

theorem sq7Newpart4_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions sq7Newpart4Program {s with pc := N 6634, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: rest} =
      some (sq7Newpart4Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 19) : rest.length + j < 1024 := by omega
  have ha192 : (192 : W).toNat = 192 := rfl
  have hf192 := Monpro.activeWords_fix s 192 32 (by decide) (by norm_num) hact
  simp [hz, hzn, sq7Newpart4Program, sq7Newpart4Model, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, capacity, ha192, hf192]


def sq7Newpart5Program : List Instr :=
  [.op (.Dup ⟨8, by decide⟩),
   .push 0 0,
   .op .MLOAD,
   .op .MULMOD,
   .op .ADD,
   .op (.Dup ⟨9, by decide⟩),
   .op (.Dup ⟨5, by decide⟩),
   .push 1 224,
   .op .MLOAD]

def sq7Newpart5Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 : W) (rest : List W) : State :=
  let v0 : W := MachineState.readWord s.memory 0
  let v1 : W := UInt256.mulMod v0 x8 x0
  let v2 : W := v1 + x1
  let v3 : W := MachineState.readWord s.memory 224
  {s with pc := N 6653, memory := s.memory, stack := v3 :: x5 :: x10 :: v2 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: rest}

theorem sq7Newpart5_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions sq7Newpart5Program {s with pc := N 6643, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: rest} =
      some (sq7Newpart5Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 19) : rest.length + j < 1024 := by omega
  have ha0 : (0 : W).toNat = 0 := rfl
  have hf0 := Monpro.activeWords_fix s 0 32 (by decide) (by norm_num) hact
  have ha224 : (224 : W).toNat = 224 := rfl
  have hf224 := Monpro.activeWords_fix s 224 32 (by decide) (by norm_num) hact
  simp [hz, hzn, sq7Newpart5Program, sq7Newpart5Model, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, capacity, ha0, hf0, ha224, hf224]


def sq7Newpart6Program : List Instr :=
  [.op .MULMOD,
   .op .ADD,
   .op (.Dup ⟨9, by decide⟩),
   .op (.Dup ⟨15, by decide⟩),
   .push 2 1216,
   .op .MLOAD,
   .op .MULMOD,
   .op .ADD]

def sq7Newpart6Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 : W) (rest : List W) : State :=
  let v0 : W := UInt256.mulMod x0 x1 x2
  let v1 : W := v0 + x3
  let v2 : W := MachineState.readWord s.memory 1216
  let v3 : W := UInt256.mulMod v2 x17 x12
  let v4 : W := v3 + v1
  {s with pc := N 6663, memory := s.memory, stack := v4 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: x18 :: rest}

theorem sq7Newpart6_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions sq7Newpart6Program {s with pc := N 6653, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: x18 :: rest} =
      some (sq7Newpart6Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 19) : rest.length + j < 1024 := by omega
  have ha1216 : (1216 : W).toNat = 1216 := rfl
  have hf1216 := Monpro.activeWords_fix s 1216 32 (by decide) (by norm_num) hact
  simp [hz, hzn, sq7Newpart6Program, sq7Newpart6Model, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, capacity, ha1216, hf1216]


def sq7Newpart7Program : List Instr :=
  [.op (.Dup ⟨9, by decide⟩),
   .op (.Dup ⟨3, by decide⟩),
   .push 2 1248,
   .op .MLOAD,
   .op .MULMOD,
   .op .ADD,
   .op (.Dup ⟨9, by decide⟩),
   .op (.Dup ⟨12, by decide⟩)]

def sq7Newpart7Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 : W) (rest : List W) : State :=
  let v0 : W := MachineState.readWord s.memory 1248
  let v1 : W := UInt256.mulMod v0 x2 x9
  let v2 : W := v1 + x0
  {s with pc := N 6673, memory := s.memory, stack := x11 :: x9 :: v2 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: rest}

theorem sq7Newpart7_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions sq7Newpart7Program {s with pc := N 6663, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: rest} =
      some (sq7Newpart7Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 19) : rest.length + j < 1024 := by omega
  have ha1248 : (1248 : W).toNat = 1248 := rfl
  have hf1248 := Monpro.activeWords_fix s 1248 32 (by decide) (by norm_num) hact
  simp [hz, hzn, sq7Newpart7Program, sq7Newpart7Model, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, capacity, ha1248, hf1248]


def sq7Newpart8Program : List Instr :=
  [.push 2 1280,
   .op .MLOAD,
   .op .MULMOD,
   .op .ADD,
   .op (.Dup ⟨9, by decide⟩),
   .op (.Dup ⟨13, by decide⟩),
   .op (.Dup ⟨3, by decide⟩),
   .push 3 2720,
   .op .MLOAD]

def sq7Newpart8Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 : W) (rest : List W) : State :=
  let v0 : W := MachineState.readWord s.memory 1280
  let v1 : W := UInt256.mulMod v0 x0 x1
  let v2 : W := v1 + x2
  let v3 : W := MachineState.readWord s.memory 2720
  {s with pc := N 6687, memory := s.memory, stack := v3 :: x3 :: x14 :: x11 :: v2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: rest}

theorem sq7Newpart8_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions sq7Newpart8Program {s with pc := N 6673, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: rest} =
      some (sq7Newpart8Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 20) : rest.length + j < 1024 := by omega
  have ha1280 : (1280 : W).toNat = 1280 := rfl
  have hf1280 := Monpro.activeWords_fix s 1280 32 (by decide) (by norm_num) hact
  have ha2720 : (2720 : W).toNat = 2720 := rfl
  have hf2720 := Monpro.activeWords_fix s 2720 32 (by decide) (by norm_num) hact
  simp [hz, hzn, sq7Newpart8Program, sq7Newpart8Model, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, capacity, ha1280, hf1280, ha2720, hf2720]


def sq7Newpart9Program : List Instr :=
  [.op .MUL,
   .op .AND,
   .op (.Dup ⟨0, by decide⟩),
   .op (.Swap ⟨15, by decide⟩),
   .op .MULMOD,
   .op .ADD,
   .push 2 2048,
   .op (.Dup ⟨10, by decide⟩)]

def sq7Newpart9Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 : W) (rest : List W) : State :=
  let v0 : W := x0 * x1
  let v1 : W := UInt256.land v0 x2
  let v2 : W := UInt256.mulMod x17 v1 x3
  let v3 : W := v2 + x4
  {s with pc := N 6697, memory := s.memory, stack := x13 :: (N 2048) :: v3 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: v1 :: x18 :: x19 :: rest}

theorem sq7Newpart9_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions sq7Newpart9Program {s with pc := N 6687, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: x18 :: x19 :: rest} =
      some (sq7Newpart9Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 20) : rest.length + j < 1024 := by omega
  simp [hz, hzn, sq7Newpart9Program, sq7Newpart9Model, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, capacity]


def sq7Newpart10Program : List Instr :=
  [.op (.Swap ⟨2, by decide⟩),
   .op .POP,
   .op .MULMOD,
   .op (.Dup ⟨14, by decide⟩),
   .op (.Dup ⟨9, by decide⟩),
   .push 2 1248,
   .op .MLOAD,
   .op (.Swap ⟨6, by decide⟩)]

def sq7Newpart10Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 : W) (rest : List W) : State :=
  let v0 : W := UInt256.mulMod x1 x2 x0
  let v1 : W := MachineState.readWord s.memory 1248
  {s with pc := N 6707, memory := s.memory, stack := x7 :: x11 :: x17 :: v0 :: x4 :: x5 :: x6 :: v1 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: rest}

theorem sq7Newpart10_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) (hk_x1 : x1 = N 2048) :
    runInstructions sq7Newpart10Program {s with pc := N 6697, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: rest} =
      some (sq7Newpart10Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 18) : rest.length + j < 1024 := by omega
  have ha1248 : (1248 : W).toNat = 1248 := rfl
  have hf1248 := Monpro.activeWords_fix s 1248 32 (by decide) (by norm_num) hact
  simp [hk_x1, hz, hzn, sq7Newpart10Program, sq7Newpart10Model, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, capacity, ha1248, hf1248]


def sq7Newpart11Program : List Instr :=
  [.op (.Dup ⟨0, by decide⟩),
   .op (.Dup ⟨3, by decide⟩),
   .op .MUL,
   .push 1 160,
   .op .MLOAD,
   .op (.Dup ⟨10, by decide⟩),
   .op .MUL,
   .op .ADD]

def sq7Newpart11Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 : W) (rest : List W) : State :=
  let v0 : W := x2 * x0
  let v1 : W := MachineState.readWord s.memory 160
  let v2 : W := x8 * v1
  let v3 : W := v2 + v0
  {s with pc := N 6716, memory := s.memory, stack := v3 :: x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: rest}

theorem sq7Newpart11_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions sq7Newpart11Program {s with pc := N 6707, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: rest} =
      some (sq7Newpart11Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 21) : rest.length + j < 1024 := by omega
  have ha160 : (160 : W).toNat = 160 := rfl
  have hf160 := Monpro.activeWords_fix s 160 32 (by decide) (by norm_num) hact
  simp [hz, hzn, sq7Newpart11Program, sq7Newpart11Model, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, capacity, ha160, hf160]


def sq7Newpart12Program : List Instr :=
  [.push 1 128,
   .op .MLOAD]

def sq7Newpart12Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 : W) (rest : List W) : State :=
  let v0 : W := MachineState.readWord s.memory 128
  {s with pc := N 6719, memory := s.memory, stack := v0 :: x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: x18 :: rest}

theorem sq7Newpart12_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions sq7Newpart12Program {s with pc := N 6716, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: x18 :: rest} =
      some (sq7Newpart12Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 20) : rest.length + j < 1024 := by omega
  have ha128 : (128 : W).toNat = 128 := rfl
  have hf128 := Monpro.activeWords_fix s 128 32 (by decide) (by norm_num) hact
  simp [hz, hzn, sq7Newpart12Program, sq7Newpart12Model, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, capacity, ha128, hf128]


def sq7NewProgram : List Instr :=
  [.op .ADD,
   .op (.Dup ⟨4, by decide⟩),
   .push 1 224,
   .op .MLOAD,
   .op .MUL,
   .op .ADD,
   .op (.Dup ⟨14, by decide⟩),
   .push 2 1216,
   .op .MLOAD,
   .op .MUL,
   .op .ADD,
   .op (.Dup ⟨2, by decide⟩),
   .push 2 1248,
   .op .MLOAD,
   .op .MUL,
   .op .ADD,
   .op (.Dup ⟨11, by decide⟩),
   .push 2 1280,
   .op .MLOAD,
   .op .MUL,
   .op .ADD,
   .op (.Swap ⟨0, by decide⟩),
   .op (.Dup ⟨9, by decide⟩),
   .push 1 64,
   .op .MLOAD,
   .op (.Dup ⟨0, by decide⟩),
   .op .MULMOD,
   .op .ADD,
   .op (.Dup ⟨9, by decide⟩),
   .push 2 1088,
   .op .MLOAD,
   .op (.Dup ⟨10, by decide⟩),
   .op .MULMOD,
   .op .ADD,
   .op (.Dup ⟨9, by decide⟩),
   .op (.Dup ⟨4, by decide⟩),
   .push 1 192,
   .op .MLOAD,
   .op .MULMOD,
   .op .ADD,
   .op (.Dup ⟨9, by decide⟩),
   .op (.Dup ⟨8, by decide⟩),
   .push 0 0,
   .op .MLOAD,
   .op .MULMOD,
   .op .ADD,
   .op (.Dup ⟨9, by decide⟩),
   .op (.Dup ⟨5, by decide⟩),
   .push 1 224,
   .op .MLOAD,
   .op .MULMOD,
   .op .ADD,
   .op (.Dup ⟨9, by decide⟩),
   .op (.Dup ⟨15, by decide⟩),
   .push 2 1216,
   .op .MLOAD,
   .op .MULMOD,
   .op .ADD,
   .op (.Dup ⟨9, by decide⟩),
   .op (.Dup ⟨3, by decide⟩),
   .push 2 1248,
   .op .MLOAD,
   .op .MULMOD,
   .op .ADD,
   .op (.Dup ⟨9, by decide⟩),
   .op (.Dup ⟨12, by decide⟩),
   .push 2 1280,
   .op .MLOAD,
   .op .MULMOD,
   .op .ADD,
   .op (.Dup ⟨9, by decide⟩),
   .op (.Dup ⟨13, by decide⟩),
   .op (.Dup ⟨3, by decide⟩),
   .push 3 2720,
   .op .MLOAD,
   .op .MUL,
   .op .AND,
   .op (.Dup ⟨0, by decide⟩),
   .op (.Swap ⟨15, by decide⟩),
   .op .MULMOD,
   .op .ADD,
   .push 2 2048,
   .op (.Dup ⟨10, by decide⟩),
   .op (.Swap ⟨2, by decide⟩),
   .op .POP,
   .op .MULMOD,
   .op (.Dup ⟨14, by decide⟩),
   .op (.Dup ⟨9, by decide⟩),
   .push 2 1248,
   .op .MLOAD,
   .op (.Swap ⟨6, by decide⟩),
   .op (.Dup ⟨0, by decide⟩),
   .op (.Dup ⟨3, by decide⟩),
   .op .MUL,
   .push 1 160,
   .op .MLOAD,
   .op (.Dup ⟨10, by decide⟩),
   .op .MUL,
   .op .ADD,
   .push 1 128,
   .op .MLOAD]

def sq7NewModel (s : State) (carry w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 : W) (rest : List W) : State :=
  let v0 : W := carry + w0
  let v1 : W := MachineState.readWord s.memory 224
  let v2 : W := v1 * w4
  let v3 : W := v2 + v0
  let v4 : W := MachineState.readWord s.memory 1216
  let v5 : W := v4 * w14
  let v6 : W := v5 + v3
  let v7 : W := MachineState.readWord s.memory 1248
  let v8 : W := v7 * w2
  let v9 : W := v8 + v6
  let v10 : W := MachineState.readWord s.memory 1280
  let v11 : W := v10 * w11
  let v12 : W := v11 + v9
  let v13 : W := MachineState.readWord s.memory 64
  let v14 : W := UInt256.mulMod v13 v13 w9
  let v15 : W := v14 + w1
  let v16 : W := MachineState.readWord s.memory 1088
  let v17 : W := UInt256.mulMod w8 v16 w9
  let v18 : W := v17 + v15
  let v19 : W := MachineState.readWord s.memory 192
  let v20 : W := UInt256.mulMod v19 w3 w9
  let v21 : W := v20 + v18
  let v22 : W := MachineState.readWord s.memory 0
  let v23 : W := UInt256.mulMod v22 w7 w9
  let v24 : W := v23 + v21
  let v25 : W := MachineState.readWord s.memory 224
  let v26 : W := UInt256.mulMod v25 w4 w9
  let v27 : W := v26 + v24
  let v28 : W := MachineState.readWord s.memory 1216
  let v29 : W := UInt256.mulMod v28 w14 w9
  let v30 : W := v29 + v27
  let v31 : W := MachineState.readWord s.memory 1248
  let v32 : W := UInt256.mulMod v31 w2 w9
  let v33 : W := v32 + v30
  let v34 : W := MachineState.readWord s.memory 1280
  let v35 : W := UInt256.mulMod v34 w11 w9
  let v36 : W := v35 + v33
  let v37 : W := MachineState.readWord s.memory 2720
  let v38 : W := v37 * v12
  let v39 : W := UInt256.land v38 w12
  let v40 : W := UInt256.mulMod w13 v39 w9
  let v41 : W := v40 + v36
  let v42 : W := UInt256.mulMod (N 2048) v41 w9
  let v43 : W := MachineState.readWord s.memory 1248
  let v44 : W := w15 * w5
  let v45 : W := MachineState.readWord s.memory 160
  let v46 : W := w6 * v45
  let v47 : W := v46 + v44
  let v48 : W := MachineState.readWord s.memory 128
  {s with pc := N 6719, memory := s.memory, stack := v48 :: v47 :: w5 :: w9 :: w15 :: v42 :: w2 :: w3 :: w4 :: v43 :: w6 :: w7 :: w8 :: w9 :: w10 :: w11 :: w12 :: v39 :: w14 :: w15 :: rest}

theorem sq7New_run (s : State) (carry w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions sq7NewProgram {s with pc := N 6591, stack := carry :: w0 :: w1 :: w2 :: w3 :: w4 :: w5 :: w6 :: w7 :: w8 :: w9 :: w10 :: w11 :: w12 :: w13 :: w14 :: w15 :: rest} =
      some (sq7NewModel s carry w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 rest) := by
  let v0 : W := carry + w0
  let v1 : W := MachineState.readWord s.memory 224
  let v2 : W := v1 * w4
  let v3 : W := v2 + v0
  let v4 : W := MachineState.readWord s.memory 1216
  let v5 : W := v4 * w14
  let v6 : W := v5 + v3
  let v7 : W := MachineState.readWord s.memory 1248
  let v8 : W := v7 * w2
  let v9 : W := v8 + v6
  let v10 : W := MachineState.readWord s.memory 1280
  let v11 : W := v10 * w11
  let v12 : W := v11 + v9
  let v13 : W := MachineState.readWord s.memory 64
  let v14 : W := UInt256.mulMod v13 v13 w9
  let v15 : W := v14 + w1
  let v16 : W := MachineState.readWord s.memory 1088
  let v17 : W := UInt256.mulMod w8 v16 w9
  let v18 : W := v17 + v15
  let v19 : W := MachineState.readWord s.memory 192
  let v20 : W := UInt256.mulMod v19 w3 w9
  let v21 : W := v20 + v18
  let v22 : W := MachineState.readWord s.memory 0
  let v23 : W := UInt256.mulMod v22 w7 w9
  let v24 : W := v23 + v21
  let v25 : W := MachineState.readWord s.memory 224
  let v26 : W := UInt256.mulMod v25 w4 w9
  let v27 : W := v26 + v24
  let v28 : W := MachineState.readWord s.memory 1216
  let v29 : W := UInt256.mulMod v28 w14 w9
  let v30 : W := v29 + v27
  let v31 : W := MachineState.readWord s.memory 1248
  let v32 : W := UInt256.mulMod v31 w2 w9
  let v33 : W := v32 + v30
  let v34 : W := MachineState.readWord s.memory 1280
  let v35 : W := UInt256.mulMod v34 w11 w9
  let v36 : W := v35 + v33
  let v37 : W := MachineState.readWord s.memory 2720
  let v38 : W := v37 * v12
  let v39 : W := UInt256.land v38 w12
  let v40 : W := UInt256.mulMod w13 v39 w9
  let v41 : W := v40 + v36
  let v42 : W := UInt256.mulMod (N 2048) v41 w9
  let v43 : W := MachineState.readWord s.memory 1248
  let v44 : W := w15 * w5
  let v45 : W := MachineState.readWord s.memory 160
  let v46 : W := w6 * v45
  let v47 : W := v46 + v44
  let v48 : W := MachineState.readWord s.memory 128
  have h0 : runInstructions sq7Newpart0Program {s with pc := N 6591, memory := s.memory, stack := carry :: w0 :: w1 :: w2 :: w3 :: w4 :: w5 :: w6 :: w7 :: w8 :: w9 :: w10 :: w11 :: w12 :: w13 :: w14 :: w15 :: rest} = some {s with pc := N 6603, memory := s.memory, stack := v4 :: w14 :: v3 :: w1 :: w2 :: w3 :: w4 :: w5 :: w6 :: w7 :: w8 :: w9 :: w10 :: w11 :: w12 :: w13 :: w14 :: w15 :: rest} := by
    simpa only [sq7Newpart0Model, v0, v1, v2, v3, v4] using sq7Newpart0_run (s) (carry) (w0) (w1) (w2) (w3) (w4) (w5) (w6) (w7) (w8) (w9) (w10) (w11) (w12) (w13) (w14) (w15) rest hcap hact
  have h1 : runInstructions sq7Newpart1Program {s with pc := N 6603, memory := s.memory, stack := v4 :: w14 :: v3 :: w1 :: w2 :: w3 :: w4 :: w5 :: w6 :: w7 :: w8 :: w9 :: w10 :: w11 :: w12 :: w13 :: w14 :: w15 :: rest} = some {s with pc := N 6613, memory := s.memory, stack := w11 :: v9 :: w1 :: w2 :: w3 :: w4 :: w5 :: w6 :: w7 :: w8 :: w9 :: w10 :: w11 :: w12 :: w13 :: w14 :: w15 :: rest} := by
    simpa only [sq7Newpart1Model, v5, v6, v7, v8, v9] using sq7Newpart1_run (s) (v4) (w14) (v3) (w1) (w2) (w3) (w4) (w5) (w6) (w7) (w8) (w9) (w10) (w11) (w12) (w13) (w14) (w15) rest hcap hact
  have h2 : runInstructions sq7Newpart2Program {s with pc := N 6613, memory := s.memory, stack := w11 :: v9 :: w1 :: w2 :: w3 :: w4 :: w5 :: w6 :: w7 :: w8 :: w9 :: w10 :: w11 :: w12 :: w13 :: w14 :: w15 :: rest} = some {s with pc := N 6624, memory := s.memory, stack := v13 :: w9 :: w1 :: v12 :: w2 :: w3 :: w4 :: w5 :: w6 :: w7 :: w8 :: w9 :: w10 :: w11 :: w12 :: w13 :: w14 :: w15 :: rest} := by
    simpa only [sq7Newpart2Model, v10, v11, v12, v13] using sq7Newpart2_run (s) (w11) (v9) (w1) (w2) (w3) (w4) (w5) (w6) (w7) (w8) (w9) (w10) (w11) (w12) (w13) (w14) (w15) rest hcap hact
  have h3 : runInstructions sq7Newpart3Program {s with pc := N 6624, memory := s.memory, stack := v13 :: w9 :: w1 :: v12 :: w2 :: w3 :: w4 :: w5 :: w6 :: w7 :: w8 :: w9 :: w10 :: w11 :: w12 :: w13 :: w14 :: w15 :: rest} = some {s with pc := N 6634, memory := s.memory, stack := v17 :: v15 :: v12 :: w2 :: w3 :: w4 :: w5 :: w6 :: w7 :: w8 :: w9 :: w10 :: w11 :: w12 :: w13 :: w14 :: w15 :: rest} := by
    simpa only [sq7Newpart3Model, v14, v15, v16, v17] using sq7Newpart3_run (s) (v13) (w9) (w1) (v12) (w2) (w3) (w4) (w5) (w6) (w7) (w8) (w9) (w10) (w11) (w12) (w13) (w14) (w15) rest hcap hact
  have h4 : runInstructions sq7Newpart4Program {s with pc := N 6634, memory := s.memory, stack := v17 :: v15 :: v12 :: w2 :: w3 :: w4 :: w5 :: w6 :: w7 :: w8 :: w9 :: w10 :: w11 :: w12 :: w13 :: w14 :: w15 :: rest} = some {s with pc := N 6643, memory := s.memory, stack := w9 :: v21 :: v12 :: w2 :: w3 :: w4 :: w5 :: w6 :: w7 :: w8 :: w9 :: w10 :: w11 :: w12 :: w13 :: w14 :: w15 :: rest} := by
    simpa only [sq7Newpart4Model, v18, v19, v20, v21] using sq7Newpart4_run (s) (v17) (v15) (v12) (w2) (w3) (w4) (w5) (w6) (w7) (w8) (w9) (w10) (w11) (w12) (w13) (w14) (w15) rest hcap hact
  have h5 : runInstructions sq7Newpart5Program {s with pc := N 6643, memory := s.memory, stack := w9 :: v21 :: v12 :: w2 :: w3 :: w4 :: w5 :: w6 :: w7 :: w8 :: w9 :: w10 :: w11 :: w12 :: w13 :: w14 :: w15 :: rest} = some {s with pc := N 6653, memory := s.memory, stack := v25 :: w4 :: w9 :: v24 :: v12 :: w2 :: w3 :: w4 :: w5 :: w6 :: w7 :: w8 :: w9 :: w10 :: w11 :: w12 :: w13 :: w14 :: w15 :: rest} := by
    simpa only [sq7Newpart5Model, v22, v23, v24, v25] using sq7Newpart5_run (s) (w9) (v21) (v12) (w2) (w3) (w4) (w5) (w6) (w7) (w8) (w9) (w10) (w11) (w12) (w13) (w14) (w15) rest hcap hact
  have h6 : runInstructions sq7Newpart6Program {s with pc := N 6653, memory := s.memory, stack := v25 :: w4 :: w9 :: v24 :: v12 :: w2 :: w3 :: w4 :: w5 :: w6 :: w7 :: w8 :: w9 :: w10 :: w11 :: w12 :: w13 :: w14 :: w15 :: rest} = some {s with pc := N 6663, memory := s.memory, stack := v30 :: v12 :: w2 :: w3 :: w4 :: w5 :: w6 :: w7 :: w8 :: w9 :: w10 :: w11 :: w12 :: w13 :: w14 :: w15 :: rest} := by
    simpa only [sq7Newpart6Model, v26, v27, v28, v29, v30] using sq7Newpart6_run (s) (v25) (w4) (w9) (v24) (v12) (w2) (w3) (w4) (w5) (w6) (w7) (w8) (w9) (w10) (w11) (w12) (w13) (w14) (w15) rest hcap hact
  have h7 : runInstructions sq7Newpart7Program {s with pc := N 6663, memory := s.memory, stack := v30 :: v12 :: w2 :: w3 :: w4 :: w5 :: w6 :: w7 :: w8 :: w9 :: w10 :: w11 :: w12 :: w13 :: w14 :: w15 :: rest} = some {s with pc := N 6673, memory := s.memory, stack := w11 :: w9 :: v33 :: v12 :: w2 :: w3 :: w4 :: w5 :: w6 :: w7 :: w8 :: w9 :: w10 :: w11 :: w12 :: w13 :: w14 :: w15 :: rest} := by
    simpa only [sq7Newpart7Model, v31, v32, v33] using sq7Newpart7_run (s) (v30) (v12) (w2) (w3) (w4) (w5) (w6) (w7) (w8) (w9) (w10) (w11) (w12) (w13) (w14) (w15) rest hcap hact
  have h8 : runInstructions sq7Newpart8Program {s with pc := N 6673, memory := s.memory, stack := w11 :: w9 :: v33 :: v12 :: w2 :: w3 :: w4 :: w5 :: w6 :: w7 :: w8 :: w9 :: w10 :: w11 :: w12 :: w13 :: w14 :: w15 :: rest} = some {s with pc := N 6687, memory := s.memory, stack := v37 :: v12 :: w12 :: w9 :: v36 :: v12 :: w2 :: w3 :: w4 :: w5 :: w6 :: w7 :: w8 :: w9 :: w10 :: w11 :: w12 :: w13 :: w14 :: w15 :: rest} := by
    simpa only [sq7Newpart8Model, v34, v35, v36, v37] using sq7Newpart8_run (s) (w11) (w9) (v33) (v12) (w2) (w3) (w4) (w5) (w6) (w7) (w8) (w9) (w10) (w11) (w12) (w13) (w14) (w15) rest hcap hact
  have h9 : runInstructions sq7Newpart9Program {s with pc := N 6687, memory := s.memory, stack := v37 :: v12 :: w12 :: w9 :: v36 :: v12 :: w2 :: w3 :: w4 :: w5 :: w6 :: w7 :: w8 :: w9 :: w10 :: w11 :: w12 :: w13 :: w14 :: w15 :: rest} = some {s with pc := N 6697, memory := s.memory, stack := w9 :: (N 2048) :: v41 :: v12 :: w2 :: w3 :: w4 :: w5 :: w6 :: w7 :: w8 :: w9 :: w10 :: w11 :: w12 :: v39 :: w14 :: w15 :: rest} := by
    simpa only [sq7Newpart9Model, v38, v39, v40, v41] using sq7Newpart9_run (s) (v37) (v12) (w12) (w9) (v36) (v12) (w2) (w3) (w4) (w5) (w6) (w7) (w8) (w9) (w10) (w11) (w12) (w13) (w14) (w15) rest hcap hact
  have h10 : runInstructions sq7Newpart10Program {s with pc := N 6697, memory := s.memory, stack := w9 :: (N 2048) :: v41 :: v12 :: w2 :: w3 :: w4 :: w5 :: w6 :: w7 :: w8 :: w9 :: w10 :: w11 :: w12 :: v39 :: w14 :: w15 :: rest} = some {s with pc := N 6707, memory := s.memory, stack := w5 :: w9 :: w15 :: v42 :: w2 :: w3 :: w4 :: v43 :: w6 :: w7 :: w8 :: w9 :: w10 :: w11 :: w12 :: v39 :: w14 :: w15 :: rest} := by
    simpa only [sq7Newpart10Model, v42, v43] using sq7Newpart10_run (s) (w9) ((N 2048)) (v41) (v12) (w2) (w3) (w4) (w5) (w6) (w7) (w8) (w9) (w10) (w11) (w12) (v39) (w14) (w15) rest hcap hact (by rfl)
  have h11 : runInstructions sq7Newpart11Program {s with pc := N 6707, memory := s.memory, stack := w5 :: w9 :: w15 :: v42 :: w2 :: w3 :: w4 :: v43 :: w6 :: w7 :: w8 :: w9 :: w10 :: w11 :: w12 :: v39 :: w14 :: w15 :: rest} = some {s with pc := N 6716, memory := s.memory, stack := v47 :: w5 :: w9 :: w15 :: v42 :: w2 :: w3 :: w4 :: v43 :: w6 :: w7 :: w8 :: w9 :: w10 :: w11 :: w12 :: v39 :: w14 :: w15 :: rest} := by
    simpa only [sq7Newpart11Model, v44, v45, v46, v47] using sq7Newpart11_run (s) (w5) (w9) (w15) (v42) (w2) (w3) (w4) (v43) (w6) (w7) (w8) (w9) (w10) (w11) (w12) (v39) (w14) (w15) rest hcap hact
  have h12 : runInstructions sq7Newpart12Program {s with pc := N 6716, memory := s.memory, stack := v47 :: w5 :: w9 :: w15 :: v42 :: w2 :: w3 :: w4 :: v43 :: w6 :: w7 :: w8 :: w9 :: w10 :: w11 :: w12 :: v39 :: w14 :: w15 :: rest} = some {s with pc := N 6719, memory := s.memory, stack := v48 :: v47 :: w5 :: w9 :: w15 :: v42 :: w2 :: w3 :: w4 :: v43 :: w6 :: w7 :: w8 :: w9 :: w10 :: w11 :: w12 :: v39 :: w14 :: w15 :: rest} := by
    simpa only [sq7Newpart12Model, v48] using sq7Newpart12_run (s) (v47) (w5) (w9) (w15) (v42) (w2) (w3) (w4) (v43) (w6) (w7) (w8) (w9) (w10) (w11) (w12) (v39) (w14) (w15) rest hcap hact
  exact (runInstructions_append_some _ _ _ _ _ h0 (runInstructions_append_some _ _ _ _ _ h1 (runInstructions_append_some _ _ _ _ _ h2 (runInstructions_append_some _ _ _ _ _ h3 (runInstructions_append_some _ _ _ _ _ h4 (runInstructions_append_some _ _ _ _ _ h5 (runInstructions_append_some _ _ _ _ _ h6 (runInstructions_append_some _ _ _ _ _ h7 (runInstructions_append_some _ _ _ _ _ h8 (runInstructions_append_some _ _ _ _ _ h9 (runInstructions_append_some _ _ _ _ _ h10 (runInstructions_append_some _ _ _ _ _ h11 h12))))))))))))

#print axioms sq7New_run

def squareColumn7Model (s : State) (carry w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 : W) (rest : List W) : State :=
  let v0 : W := carry + w0
  let v1 : W := MachineState.readWord s.memory 224
  let v2 : W := v1 * w4
  let v3 : W := v2 + v0
  let v4 : W := MachineState.readWord s.memory 1216
  let v5 : W := v4 * w14
  let v6 : W := v5 + v3
  let v7 : W := MachineState.readWord s.memory 1248
  let v8 : W := v7 * w2
  let v9 : W := v8 + v6
  let v10 : W := MachineState.readWord s.memory 1280
  let v11 : W := v10 * w11
  let v12 : W := v11 + v9
  let v13 : W := MachineState.readWord s.memory 64
  let v14 : W := UInt256.mulMod v13 v13 w9
  let v15 : W := v14 + w1
  let v16 : W := MachineState.readWord s.memory 1088
  let v17 : W := UInt256.mulMod w8 v16 w9
  let v18 : W := v17 + v15
  let v19 : W := MachineState.readWord s.memory 192
  let v20 : W := UInt256.mulMod v19 w3 w9
  let v21 : W := v20 + v18
  let v22 : W := MachineState.readWord s.memory 0
  let v23 : W := UInt256.mulMod v22 w7 w9
  let v24 : W := v23 + v21
  let v25 : W := MachineState.readWord s.memory 224
  let v26 : W := UInt256.mulMod v25 w4 w9
  let v27 : W := v26 + v24
  let v28 : W := MachineState.readWord s.memory 1216
  let v29 : W := UInt256.mulMod v28 w14 w9
  let v30 : W := v29 + v27
  let v31 : W := MachineState.readWord s.memory 1248
  let v32 : W := UInt256.mulMod v31 w2 w9
  let v33 : W := v32 + v30
  let v34 : W := MachineState.readWord s.memory 1280
  let v35 : W := UInt256.mulMod v34 w11 w9
  let v36 : W := v35 + v33
  let v37 : W := MachineState.readWord s.memory 2720
  let v38 : W := v37 * v12
  let v39 : W := UInt256.land w12 v38
  let v40 : W := UInt256.mulMod w13 v39 w9
  let v41 : W := v40 + v36
  let v42 : W := UInt256.mulMod (N 2048) v41 w9
  let v43 : W := MachineState.readWord s.memory 1248
  let v44 : W := w15 * w5
  let v45 : W := MachineState.readWord s.memory 160
  let v46 : W := w6 * v45
  let v47 : W := v46 + v44
  let v48 : W := MachineState.readWord s.memory 128
  {s with pc := N 6719, memory := s.memory, stack := v48 :: v47 :: w5 :: w9 :: w15 :: v42 :: w2 :: w3 :: w4 :: v43 :: w6 :: w7 :: w8 :: w9 :: w10 :: w11 :: w12 :: v39 :: w14 :: w15 :: rest}

def squareColumn7Program : List Instr := sq7NewProgram

private theorem aux_shared0 (w12 : W) (z0 : W) :
    (UInt256.land z0 w12) = (UInt256.land w12 z0) := by
  simp (disch := decide) only [addC, addA, addL, mulC, mmC, amC, andC, orC, xorC, eqC, read_disjoint, Challenge.EvmProof.Memory.readWord_writeWord]

private theorem prepared_model_eq (s : State) (carry w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 : W) (rest : List W) :
    squareColumn7Model s carry w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 rest = sq7NewModel s carry w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 rest := by
  let o0 : W := carry + w0
  let o1 : W := MachineState.readWord s.memory 224
  let o2 : W := o1 * w4
  let o3 : W := o2 + o0
  let o4 : W := MachineState.readWord s.memory 1216
  let o5 : W := o4 * w14
  let o6 : W := o5 + o3
  let o7 : W := MachineState.readWord s.memory 1248
  let o8 : W := o7 * w2
  let o9 : W := o8 + o6
  let o10 : W := MachineState.readWord s.memory 1280
  let o11 : W := o10 * w11
  let o12 : W := o11 + o9
  let o13 : W := MachineState.readWord s.memory 64
  let o14 : W := UInt256.mulMod o13 o13 w9
  let o15 : W := o14 + w1
  let o16 : W := MachineState.readWord s.memory 1088
  let o17 : W := UInt256.mulMod w8 o16 w9
  let o18 : W := o17 + o15
  let o19 : W := MachineState.readWord s.memory 192
  let o20 : W := UInt256.mulMod o19 w3 w9
  let o21 : W := o20 + o18
  let o22 : W := MachineState.readWord s.memory 0
  let o23 : W := UInt256.mulMod o22 w7 w9
  let o24 : W := o23 + o21
  let o25 : W := MachineState.readWord s.memory 224
  let o26 : W := UInt256.mulMod o25 w4 w9
  let o27 : W := o26 + o24
  let o28 : W := MachineState.readWord s.memory 1216
  let o29 : W := UInt256.mulMod o28 w14 w9
  let o30 : W := o29 + o27
  let o31 : W := MachineState.readWord s.memory 1248
  let o32 : W := UInt256.mulMod o31 w2 w9
  let o33 : W := o32 + o30
  let o34 : W := MachineState.readWord s.memory 1280
  let o35 : W := UInt256.mulMod o34 w11 w9
  let o36 : W := o35 + o33
  let o37 : W := MachineState.readWord s.memory 2720
  let o38 : W := o37 * o12
  let o39 : W := UInt256.land w12 o38
  let o40 : W := UInt256.mulMod w13 o39 w9
  let o41 : W := o40 + o36
  let o42 : W := UInt256.mulMod (N 2048) o41 w9
  let o43 : W := MachineState.readWord s.memory 1248
  let o44 : W := w15 * w5
  let o45 : W := MachineState.readWord s.memory 160
  let o46 : W := w6 * o45
  let o47 : W := o46 + o44
  let o48 : W := MachineState.readWord s.memory 128
  let n0 : W := carry + w0
  let n1 : W := MachineState.readWord s.memory 224
  let n2 : W := n1 * w4
  let n3 : W := n2 + n0
  let n4 : W := MachineState.readWord s.memory 1216
  let n5 : W := n4 * w14
  let n6 : W := n5 + n3
  let n7 : W := MachineState.readWord s.memory 1248
  let n8 : W := n7 * w2
  let n9 : W := n8 + n6
  let n10 : W := MachineState.readWord s.memory 1280
  let n11 : W := n10 * w11
  let n12 : W := n11 + n9
  let n13 : W := MachineState.readWord s.memory 64
  let n14 : W := UInt256.mulMod n13 n13 w9
  let n15 : W := n14 + w1
  let n16 : W := MachineState.readWord s.memory 1088
  let n17 : W := UInt256.mulMod w8 n16 w9
  let n18 : W := n17 + n15
  let n19 : W := MachineState.readWord s.memory 192
  let n20 : W := UInt256.mulMod n19 w3 w9
  let n21 : W := n20 + n18
  let n22 : W := MachineState.readWord s.memory 0
  let n23 : W := UInt256.mulMod n22 w7 w9
  let n24 : W := n23 + n21
  let n25 : W := MachineState.readWord s.memory 224
  let n26 : W := UInt256.mulMod n25 w4 w9
  let n27 : W := n26 + n24
  let n28 : W := MachineState.readWord s.memory 1216
  let n29 : W := UInt256.mulMod n28 w14 w9
  let n30 : W := n29 + n27
  let n31 : W := MachineState.readWord s.memory 1248
  let n32 : W := UInt256.mulMod n31 w2 w9
  let n33 : W := n32 + n30
  let n34 : W := MachineState.readWord s.memory 1280
  let n35 : W := UInt256.mulMod n34 w11 w9
  let n36 : W := n35 + n33
  let n37 : W := MachineState.readWord s.memory 2720
  let n38 : W := n37 * n12
  let n39 : W := UInt256.land n38 w12
  let n40 : W := UInt256.mulMod w13 n39 w9
  let n41 : W := n40 + n36
  let n42 : W := UInt256.mulMod (N 2048) n41 w9
  let n43 : W := MachineState.readWord s.memory 1248
  let n44 : W := w15 * w5
  let n45 : W := MachineState.readWord s.memory 160
  let n46 : W := w6 * n45
  let n47 : W := n46 + n44
  let n48 : W := MachineState.readWord s.memory 128
  have eq_o25 : o25 = o1 := by
    simp only [o25, o1]
  have eq_o28 : o28 = o4 := by
    simp only [o28, o4]
  have eq_o31 : o31 = o7 := by
    simp only [o31, o7]
  have eq_o34 : o34 = o10 := by
    simp only [o34, o10]
  have eq_o43 : o43 = o7 := by
    simp only [o43, o7]
  have eq_n0 : n0 = o0 := by
    simp only [n0, o0]
  have eq_n1 : n1 = o1 := by
    simp only [n1, o1]
  have eq_n2 : n2 = o2 := by
    simp only [n2, o2, eq_n1]
  have eq_n3 : n3 = o3 := by
    simp only [n3, o3, eq_n2, eq_n0]
  have eq_n4 : n4 = o4 := by
    simp only [n4, o4]
  have eq_n5 : n5 = o5 := by
    simp only [n5, o5, eq_n4]
  have eq_n6 : n6 = o6 := by
    simp only [n6, o6, eq_n5, eq_n3]
  have eq_n7 : n7 = o7 := by
    simp only [n7, o7]
  have eq_n8 : n8 = o8 := by
    simp only [n8, o8, eq_n7]
  have eq_n9 : n9 = o9 := by
    simp only [n9, o9, eq_n8, eq_n6]
  have eq_n10 : n10 = o10 := by
    simp only [n10, o10]
  have eq_n11 : n11 = o11 := by
    simp only [n11, o11, eq_n10]
  have eq_n12 : n12 = o12 := by
    simp only [n12, o12, eq_n11, eq_n9]
  have eq_n13 : n13 = o13 := by
    simp only [n13, o13]
  have eq_n14 : n14 = o14 := by
    simp only [n14, o14, eq_n13]
  have eq_n15 : n15 = o15 := by
    simp only [n15, o15, eq_n14]
  have eq_n16 : n16 = o16 := by
    simp only [n16, o16]
  have eq_n17 : n17 = o17 := by
    simp only [n17, o17, eq_n16]
  have eq_n18 : n18 = o18 := by
    simp only [n18, o18, eq_n17, eq_n15]
  have eq_n19 : n19 = o19 := by
    simp only [n19, o19]
  have eq_n20 : n20 = o20 := by
    simp only [n20, o20, eq_n19]
  have eq_n21 : n21 = o21 := by
    simp only [n21, o21, eq_n20, eq_n18]
  have eq_n22 : n22 = o22 := by
    simp only [n22, o22]
  have eq_n23 : n23 = o23 := by
    simp only [n23, o23, eq_n22]
  have eq_n24 : n24 = o24 := by
    simp only [n24, o24, eq_n23, eq_n21]
  have eq_n25 : n25 = o1 := by
    simp only [n25, o1]
  have eq_n26 : n26 = o26 := by
    simp only [n26, o26, eq_n25, eq_o25]
  have eq_n27 : n27 = o27 := by
    simp only [n27, o27, eq_n26, eq_n24]
  have eq_n28 : n28 = o4 := by
    simp only [n28, o4]
  have eq_n29 : n29 = o29 := by
    simp only [n29, o29, eq_n28, eq_o28]
  have eq_n30 : n30 = o30 := by
    simp only [n30, o30, eq_n29, eq_n27]
  have eq_n31 : n31 = o7 := by
    simp only [n31, o7]
  have eq_n32 : n32 = o32 := by
    simp only [n32, o32, eq_n31, eq_o31]
  have eq_n33 : n33 = o33 := by
    simp only [n33, o33, eq_n32, eq_n30]
  have eq_n34 : n34 = o10 := by
    simp only [n34, o10]
  have eq_n35 : n35 = o35 := by
    simp only [n35, o35, eq_n34, eq_o34]
  have eq_n36 : n36 = o36 := by
    simp only [n36, o36, eq_n35, eq_n33]
  have eq_n37 : n37 = o37 := by
    simp only [n37, o37]
  have eq_n38 : n38 = o38 := by
    simp only [n38, o38, eq_n37, eq_n12]
  have eq_n39 : n39 = o39 := by
    simpa only [n39, o39, eq_n38] using
      (aux_shared0 w12 o38)
  have eq_n40 : n40 = o40 := by
    simp only [n40, o40, eq_n39]
  have eq_n41 : n41 = o41 := by
    simp only [n41, o41, eq_n40, eq_n36]
  have eq_n42 : n42 = o42 := by
    simp only [n42, o42, eq_n41]
  have eq_n43 : n43 = o7 := by
    simp only [n43, o7]
  have eq_n44 : n44 = o44 := by
    simp only [n44, o44]
  have eq_n45 : n45 = o45 := by
    simp only [n45, o45]
  have eq_n46 : n46 = o46 := by
    simp only [n46, o46, eq_n45]
  have eq_n47 : n47 = o47 := by
    simp only [n47, o47, eq_n46, eq_n44]
  have eq_n48 : n48 = o48 := by
    simp only [n48, o48]
  change {s with pc := N 6719, memory := s.memory, stack := o48 :: o47 :: w5 :: w9 :: w15 :: o42 :: w2 :: w3 :: w4 :: o43 :: w6 :: w7 :: w8 :: w9 :: w10 :: w11 :: w12 :: o39 :: w14 :: w15 :: rest} =
    {s with pc := N 6719, memory := s.memory, stack := n48 :: n47 :: w5 :: w9 :: w15 :: n42 :: w2 :: w3 :: w4 :: n43 :: w6 :: w7 :: w8 :: w9 :: w10 :: w11 :: w12 :: n39 :: w14 :: w15 :: rest}
  simp only [eq_o25, eq_o28, eq_o31, eq_o34, eq_o43, eq_n0, eq_n1, eq_n2, eq_n3, eq_n4, eq_n5, eq_n6, eq_n7, eq_n8, eq_n9, eq_n10, eq_n11, eq_n12, eq_n13, eq_n14, eq_n15, eq_n16, eq_n17, eq_n18, eq_n19, eq_n20, eq_n21, eq_n22, eq_n23, eq_n24, eq_n25, eq_n26, eq_n27, eq_n28, eq_n29, eq_n30, eq_n31, eq_n32, eq_n33, eq_n34, eq_n35, eq_n36, eq_n37, eq_n38, eq_n39, eq_n40, eq_n41, eq_n42, eq_n43, eq_n44, eq_n45, eq_n46, eq_n47, eq_n48]
theorem squareColumn7_run (s : State) (carry w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions squareColumn7Program {s with pc := N 6591, stack := carry :: w0 :: w1 :: w2 :: w3 :: w4 :: w5 :: w6 :: w7 :: w8 :: w9 :: w10 :: w11 :: w12 :: w13 :: w14 :: w15 :: rest} =
      some (squareColumn7Model s carry w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 rest) := by
  exact (sq7New_run s carry w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 rest hcap hact).trans
    (congrArg some (prepared_model_eq s carry w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 rest).symm)

#print axioms squareColumn7_run
end CycleSubmission.Execution
