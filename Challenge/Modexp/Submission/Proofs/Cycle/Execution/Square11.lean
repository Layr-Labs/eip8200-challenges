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

def sq11Newpart0Program : List Instr :=
  [.op .MULMOD,
   .op .ADD,
   .op (.Dup ⟨0, by decide⟩),
   .op .ADD,
   .op (.Dup ⟨2, by decide⟩),
   .op .ADD,
   .op (.Swap ⟨1, by decide⟩),
   .op .ADD]

def sq11Newpart0Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 : W) (rest : List W) : State :=
  let v0 : W := UInt256.mulMod x0 x1 x2
  let v1 : W := v0 + x3
  let v2 : W := v1 + v1
  let v3 : W := x5 + v2
  let v4 : W := x5 + x4
  {s with pc := N 7118, memory := s.memory, stack := v4 :: v3 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: x18 :: x19 :: rest}

theorem sq11Newpart0_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions sq11Newpart0Program {s with pc := N 7110, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: x18 :: x19 :: rest} =
      some (sq11Newpart0Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 20) : rest.length + j < 1024 := by omega
  simp [hz, hzn, sq11Newpart0Program, sq11Newpart0Model, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, capacity]


def sq11Newpart1Program : List Instr :=
  [.push 0 0,
   .op .MLOAD,
   .op (.Dup ⟨11, by decide⟩),
   .op .MUL,
   .op .ADD,
   .push 1 224,
   .op .MLOAD,
   .op (.Dup ⟨9, by decide⟩)]

def sq11Newpart1Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 : W) (rest : List W) : State :=
  let v0 : W := MachineState.readWord s.memory 0
  let v1 : W := x10 * v0
  let v2 : W := v1 + x0
  let v3 : W := MachineState.readWord s.memory 224
  {s with pc := N 7127, memory := s.memory, stack := x8 :: v3 :: v2 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: rest}

theorem sq11Newpart1_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions sq11Newpart1Program {s with pc := N 7118, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: rest} =
      some (sq11Newpart1Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 18) : rest.length + j < 1024 := by omega
  have ha0 : (0 : W).toNat = 0 := rfl
  have hf0 := Monpro.activeWords_fix s 0 32 (by decide) (by norm_num) hact
  have ha224 : (224 : W).toNat = 224 := rfl
  have hf224 := Monpro.activeWords_fix s 224 32 (by decide) (by norm_num) hact
  simp [hz, hzn, sq11Newpart1Program, sq11Newpart1Model, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, capacity, ha0, hf0, ha224, hf224]


def sq11Newpart2Program : List Instr :=
  [.op .MUL,
   .op .ADD,
   .op (.Dup ⟨3, by decide⟩),
   .op (.Dup ⟨7, by decide⟩),
   .op .MUL,
   .op .ADD,
   .op (.Dup ⟨7, by decide⟩),
   .op (.Dup ⟨6, by decide⟩)]

def sq11Newpart2Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 : W) (rest : List W) : State :=
  let v0 : W := x0 * x1
  let v1 : W := v0 + x2
  let v2 : W := x8 * x5
  let v3 : W := v2 + v1
  {s with pc := N 7135, memory := s.memory, stack := x7 :: x9 :: v3 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: rest}

theorem sq11Newpart2_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions sq11Newpart2Program {s with pc := N 7127, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: rest} =
      some (sq11Newpart2Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 18) : rest.length + j < 1024 := by omega
  simp [hz, hzn, sq11Newpart2Program, sq11Newpart2Model, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, capacity]


def sq11Newpart3Program : List Instr :=
  [.op .MUL,
   .op .ADD,
   .op (.Dup ⟨11, by decide⟩),
   .op (.Dup ⟨5, by decide⟩),
   .op .MUL,
   .op .ADD,
   .op (.Dup ⟨14, by decide⟩),
   .op (.Dup ⟨14, by decide⟩)]

def sq11Newpart3Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 : W) (rest : List W) : State :=
  let v0 : W := x0 * x1
  let v1 : W := v0 + x2
  let v2 : W := x6 * x13
  let v3 : W := v2 + v1
  {s with pc := N 7143, memory := s.memory, stack := x15 :: x16 :: v3 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: rest}

theorem sq11Newpart3_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions sq11Newpart3Program {s with pc := N 7135, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: rest} =
      some (sq11Newpart3Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 18) : rest.length + j < 1024 := by omega
  simp [hz, hzn, sq11Newpart3Program, sq11Newpart3Model, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, capacity]


def sq11Newpart4Program : List Instr :=
  [.op .MUL,
   .op .ADD,
   .op (.Swap ⟨0, by decide⟩),
   .op (.Dup ⟨9, by decide⟩),
   .push 0 0,
   .op .MLOAD,
   .op (.Dup ⟨12, by decide⟩),
   .op .MULMOD]

def sq11Newpart4Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 : W) (rest : List W) : State :=
  let v0 : W := x0 * x1
  let v1 : W := v0 + x2
  let v2 : W := MachineState.readWord s.memory 0
  let v3 : W := UInt256.mulMod x12 v2 x11
  {s with pc := N 7151, memory := s.memory, stack := v3 :: x3 :: v1 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: rest}

theorem sq11Newpart4_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions sq11Newpart4Program {s with pc := N 7143, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: rest} =
      some (sq11Newpart4Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 19) : rest.length + j < 1024 := by omega
  have ha0 : (0 : W).toNat = 0 := rfl
  have hf0 := Monpro.activeWords_fix s 0 32 (by decide) (by norm_num) hact
  simp [hz, hzn, sq11Newpart4Program, sq11Newpart4Model, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, capacity, ha0, hf0]


def sq11Newpart5Program : List Instr :=
  [.op .ADD,
   .op (.Dup ⟨9, by decide⟩),
   .push 1 224,
   .op .MLOAD,
   .op (.Dup ⟨10, by decide⟩),
   .op .MULMOD,
   .op .ADD,
   .op (.Dup ⟨9, by decide⟩)]

def sq11Newpart5Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 : W) (rest : List W) : State :=
  let v0 : W := x0 + x1
  let v1 : W := MachineState.readWord s.memory 224
  let v2 : W := UInt256.mulMod x9 v1 x10
  let v3 : W := v2 + v0
  {s with pc := N 7160, memory := s.memory, stack := x10 :: v3 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: rest}

theorem sq11Newpart5_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions sq11Newpart5Program {s with pc := N 7151, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: rest} =
      some (sq11Newpart5Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 19) : rest.length + j < 1024 := by omega
  have ha224 : (224 : W).toNat = 224 := rfl
  have hf224 := Monpro.activeWords_fix s 224 32 (by decide) (by norm_num) hact
  simp [hz, hzn, sq11Newpart5Program, sq11Newpart5Model, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, capacity, ha224, hf224]


def sq11Newpart6Program : List Instr :=
  [.op (.Dup ⟨4, by decide⟩),
   .op (.Dup ⟨8, by decide⟩),
   .op .MULMOD,
   .op .ADD,
   .op (.Dup ⟨9, by decide⟩),
   .op (.Dup ⟨8, by decide⟩),
   .op (.Dup ⟨7, by decide⟩),
   .op .MULMOD]

def sq11Newpart6Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 : W) (rest : List W) : State :=
  let v0 : W := UInt256.mulMod x7 x4 x0
  let v1 : W := v0 + x1
  let v2 : W := UInt256.mulMod x6 x8 x10
  {s with pc := N 7168, memory := s.memory, stack := v2 :: v1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: rest}

theorem sq11Newpart6_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions sq11Newpart6Program {s with pc := N 7160, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: rest} =
      some (sq11Newpart6Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 19) : rest.length + j < 1024 := by omega
  simp [hz, hzn, sq11Newpart6Program, sq11Newpart6Model, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, capacity]


def sq11Newpart7Program : List Instr :=
  [.op .ADD,
   .op (.Dup ⟨9, by decide⟩),
   .op (.Dup ⟨5, by decide⟩),
   .op (.Dup ⟨13, by decide⟩),
   .op .MULMOD,
   .op .ADD,
   .op (.Dup ⟨9, by decide⟩),
   .op (.Dup ⟨15, by decide⟩)]

def sq11Newpart7Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 : W) (rest : List W) : State :=
  let v0 : W := x0 + x1
  let v1 : W := UInt256.mulMod x12 x5 x10
  let v2 : W := v1 + v0
  {s with pc := N 7176, memory := s.memory, stack := x15 :: x10 :: v2 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: rest}

theorem sq11Newpart7_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions sq11Newpart7Program {s with pc := N 7168, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: rest} =
      some (sq11Newpart7Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 19) : rest.length + j < 1024 := by omega
  simp [hz, hzn, sq11Newpart7Program, sq11Newpart7Model, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, capacity]


def sq11Newpart8Program : List Instr :=
  [.op (.Dup ⟨15, by decide⟩),
   .op .MULMOD,
   .op .ADD,
   .op (.Swap ⟨0, by decide⟩),
   .op (.Dup ⟨12, by decide⟩),
   .op .AND,
   .op (.Dup ⟨0, by decide⟩),
   .push 2 832,
   .op .MSTORE]

def sq11Newpart8Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 : W) (rest : List W) : State :=
  let v0 : W := UInt256.mulMod x15 x0 x1
  let v1 : W := v0 + x2
  let v2 : W := UInt256.land x14 x3
  let v3 : ByteArray := MachineState.writeBytes s.memory (Data.Bytes.natToBytesPadded v2.toNat 32) 832
  {s with pc := N 7187, memory := v3, stack := v2 :: v1 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: rest}

theorem sq11Newpart8_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions sq11Newpart8Program {s with pc := N 7176, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: rest} =
      some (sq11Newpart8Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 19) : rest.length + j < 1024 := by omega
  have ha832 : (832 : W).toNat = 832 := rfl
  have hf832 := Monpro.activeWords_fix s 832 32 (by decide) (by norm_num) hact
  simp [hz, hzn, sq11Newpart8Program, sq11Newpart8Model, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, capacity, ha832, hf832]


def sq11Newpart9Program : List Instr :=
  [.op (.Dup ⟨9, by decide⟩),
   .op (.Swap ⟨1, by decide⟩),
   .op .SUB,
   .op (.Dup ⟨1, by decide⟩),
   .op .ADD,
   .push 3 2048,
   .op .MULMOD,
   .op (.Dup ⟨14, by decide⟩)]

def sq11Newpart9Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 : W) (rest : List W) : State :=
  let v0 : W := x1 - x0
  let v1 : W := x9 + v0
  let v2 : W := UInt256.mulMod (N 2048) v1 x9
  {s with pc := N 7198, memory := s.memory, stack := x15 :: v2 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: rest}

theorem sq11Newpart9_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions sq11Newpart9Program {s with pc := N 7187, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: rest} =
      some (sq11Newpart9Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 17) : rest.length + j < 1024 := by omega
  simp [hz, hzn, sq11Newpart9Program, sq11Newpart9Model, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, capacity]


def sq11Newpart10Program : List Instr :=
  [.op (.Dup ⟨9, by decide⟩),
   .push 1 64,
   .op .MLOAD,
   .op (.Dup ⟨0, by decide⟩),
   .op (.Dup ⟨3, by decide⟩),
   .op .MUL,
   .push 1 160,
   .op .MLOAD]

def sq11Newpart10Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 : W) (rest : List W) : State :=
  let v0 : W := MachineState.readWord s.memory 64
  let v1 : W := x0 * v0
  let v2 : W := MachineState.readWord s.memory 160
  {s with pc := N 7208, memory := s.memory, stack := v2 :: v1 :: v0 :: x9 :: x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: rest}

theorem sq11Newpart10_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions sq11Newpart10Program {s with pc := N 7198, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: rest} =
      some (sq11Newpart10Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 20) : rest.length + j < 1024 := by omega
  have ha64 : (64 : W).toNat = 64 := rfl
  have hf64 := Monpro.activeWords_fix s 64 32 (by decide) (by norm_num) hact
  have ha160 : (160 : W).toNat = 160 := rfl
  have hf160 := Monpro.activeWords_fix s 160 32 (by decide) (by norm_num) hact
  simp [hz, hzn, sq11Newpart10Program, sq11Newpart10Model, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, capacity, ha64, hf64, ha160, hf160]


def sq11Newpart11Program : List Instr :=
  [.push 1 96,
   .op .MLOAD,
   .op .MUL,
   .op .ADD,
   .op (.Dup ⟨0, by decide⟩),
   .op .ADD,
   .op (.Swap ⟨2, by decide⟩),
   .op .MULMOD]

def sq11Newpart11Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 : W) (rest : List W) : State :=
  let v0 : W := MachineState.readWord s.memory 96
  let v1 : W := v0 * x0
  let v2 : W := v1 + x1
  let v3 : W := v2 + v2
  let v4 : W := UInt256.mulMod x4 x2 x3
  {s with pc := N 7217, memory := s.memory, stack := v4 :: v3 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: x18 :: x19 :: rest}

theorem sq11Newpart11_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions sq11Newpart11Program {s with pc := N 7208, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: x18 :: x19 :: rest} =
      some (sq11Newpart11Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 21) : rest.length + j < 1024 := by omega
  have ha96 : (96 : W).toNat = 96 := rfl
  have hf96 := Monpro.activeWords_fix s 96 32 (by decide) (by norm_num) hact
  simp [hz, hzn, sq11Newpart11Program, sq11Newpart11Model, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, capacity, ha96, hf96]


def sq11Newpart12Program : List Instr :=
  [.op (.Dup ⟨10, by decide⟩),
   .push 1 160,
   .op .MLOAD,
   .push 1 96,
   .op .MLOAD,
   .op .MULMOD,
   .op .ADD,
   .op (.Dup ⟨0, by decide⟩)]

def sq11Newpart12Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 : W) (rest : List W) : State :=
  let v0 : W := MachineState.readWord s.memory 160
  let v1 : W := MachineState.readWord s.memory 96
  let v2 : W := UInt256.mulMod v1 v0 x10
  let v3 : W := v2 + x0
  {s with pc := N 7227, memory := s.memory, stack := v3 :: v3 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: rest}

theorem sq11Newpart12_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions sq11Newpart12Program {s with pc := N 7217, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: rest} =
      some (sq11Newpart12Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 20) : rest.length + j < 1024 := by omega
  have ha96 : (96 : W).toNat = 96 := rfl
  have hf96 := Monpro.activeWords_fix s 96 32 (by decide) (by norm_num) hact
  have ha160 : (160 : W).toNat = 160 := rfl
  have hf160 := Monpro.activeWords_fix s 160 32 (by decide) (by norm_num) hact
  simp [hz, hzn, sq11Newpart12Program, sq11Newpart12Model, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, capacity, ha96, hf96, ha160, hf160]


def sq11Newpart13Program : List Instr :=
  [.op .ADD,
   .op (.Dup ⟨2, by decide⟩),
   .op .ADD,
   .op (.Swap ⟨1, by decide⟩),
   .op .ADD,
   .push 1 128,
   .op .MLOAD]

def sq11Newpart13Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 : W) (rest : List W) : State :=
  let v0 : W := x0 + x1
  let v1 : W := x3 + v0
  let v2 : W := x3 + x2
  let v3 : W := MachineState.readWord s.memory 128
  {s with pc := N 7235, memory := s.memory, stack := v3 :: v2 :: v1 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: rest}

theorem sq11Newpart13_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions sq11Newpart13Program {s with pc := N 7227, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: rest} =
      some (sq11Newpart13Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 18) : rest.length + j < 1024 := by omega
  have ha128 : (128 : W).toNat = 128 := rfl
  have hf128 := Monpro.activeWords_fix s 128 32 (by decide) (by norm_num) hact
  simp [hz, hzn, sq11Newpart13Program, sq11Newpart13Model, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, capacity, ha128, hf128]


def sq11NewProgram : List Instr :=
  [.op .MULMOD,
   .op .ADD,
   .op (.Dup ⟨0, by decide⟩),
   .op .ADD,
   .op (.Dup ⟨2, by decide⟩),
   .op .ADD,
   .op (.Swap ⟨1, by decide⟩),
   .op .ADD,
   .push 0 0,
   .op .MLOAD,
   .op (.Dup ⟨11, by decide⟩),
   .op .MUL,
   .op .ADD,
   .push 1 224,
   .op .MLOAD,
   .op (.Dup ⟨9, by decide⟩),
   .op .MUL,
   .op .ADD,
   .op (.Dup ⟨3, by decide⟩),
   .op (.Dup ⟨7, by decide⟩),
   .op .MUL,
   .op .ADD,
   .op (.Dup ⟨7, by decide⟩),
   .op (.Dup ⟨6, by decide⟩),
   .op .MUL,
   .op .ADD,
   .op (.Dup ⟨11, by decide⟩),
   .op (.Dup ⟨5, by decide⟩),
   .op .MUL,
   .op .ADD,
   .op (.Dup ⟨14, by decide⟩),
   .op (.Dup ⟨14, by decide⟩),
   .op .MUL,
   .op .ADD,
   .op (.Swap ⟨0, by decide⟩),
   .op (.Dup ⟨9, by decide⟩),
   .push 0 0,
   .op .MLOAD,
   .op (.Dup ⟨12, by decide⟩),
   .op .MULMOD,
   .op .ADD,
   .op (.Dup ⟨9, by decide⟩),
   .push 1 224,
   .op .MLOAD,
   .op (.Dup ⟨10, by decide⟩),
   .op .MULMOD,
   .op .ADD,
   .op (.Dup ⟨9, by decide⟩),
   .op (.Dup ⟨4, by decide⟩),
   .op (.Dup ⟨8, by decide⟩),
   .op .MULMOD,
   .op .ADD,
   .op (.Dup ⟨9, by decide⟩),
   .op (.Dup ⟨8, by decide⟩),
   .op (.Dup ⟨7, by decide⟩),
   .op .MULMOD,
   .op .ADD,
   .op (.Dup ⟨9, by decide⟩),
   .op (.Dup ⟨5, by decide⟩),
   .op (.Dup ⟨13, by decide⟩),
   .op .MULMOD,
   .op .ADD,
   .op (.Dup ⟨9, by decide⟩),
   .op (.Dup ⟨15, by decide⟩),
   .op (.Dup ⟨15, by decide⟩),
   .op .MULMOD,
   .op .ADD,
   .op (.Swap ⟨0, by decide⟩),
   .op (.Dup ⟨12, by decide⟩),
   .op .AND,
   .op (.Dup ⟨0, by decide⟩),
   .push 2 832,
   .op .MSTORE,
   .op (.Dup ⟨9, by decide⟩),
   .op (.Swap ⟨1, by decide⟩),
   .op .SUB,
   .op (.Dup ⟨1, by decide⟩),
   .op .ADD,
   .push 3 2048,
   .op .MULMOD,
   .op (.Dup ⟨14, by decide⟩),
   .op (.Dup ⟨9, by decide⟩),
   .push 1 64,
   .op .MLOAD,
   .op (.Dup ⟨0, by decide⟩),
   .op (.Dup ⟨3, by decide⟩),
   .op .MUL,
   .push 1 160,
   .op .MLOAD,
   .push 1 96,
   .op .MLOAD,
   .op .MUL,
   .op .ADD,
   .op (.Dup ⟨0, by decide⟩),
   .op .ADD,
   .op (.Swap ⟨2, by decide⟩),
   .op .MULMOD,
   .op (.Dup ⟨10, by decide⟩),
   .push 1 160,
   .op .MLOAD,
   .push 1 96,
   .op .MLOAD,
   .op .MULMOD,
   .op .ADD,
   .op (.Dup ⟨0, by decide⟩),
   .op .ADD,
   .op (.Dup ⟨2, by decide⟩),
   .op .ADD,
   .op (.Swap ⟨1, by decide⟩),
   .op .ADD,
   .push 1 128,
   .op .MLOAD]

def sq11NewModel (s : State) (carry w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 : W) (rest : List W) : State :=
  let v0 : W := UInt256.mulMod carry w0 w1
  let v1 : W := v0 + w2
  let v2 : W := v1 + v1
  let v3 : W := w4 + v2
  let v4 : W := w4 + w3
  let v5 : W := MachineState.readWord s.memory 0
  let v6 : W := w13 * v5
  let v7 : W := v6 + v4
  let v8 : W := MachineState.readWord s.memory 224
  let v9 : W := w11 * v8
  let v10 : W := v9 + v7
  let v11 : W := w9 * w6
  let v12 : W := v11 + v10
  let v13 : W := w8 * w10
  let v14 : W := v13 + v12
  let v15 : W := w7 * w14
  let v16 : W := v15 + v14
  let v17 : W := w16 * w17
  let v18 : W := v17 + v16
  let v19 : W := MachineState.readWord s.memory 0
  let v20 : W := UInt256.mulMod w13 v19 w12
  let v21 : W := v20 + v3
  let v22 : W := MachineState.readWord s.memory 224
  let v23 : W := UInt256.mulMod w11 v22 w12
  let v24 : W := v23 + v21
  let v25 : W := UInt256.mulMod w9 w6 w12
  let v26 : W := v25 + v24
  let v27 : W := UInt256.mulMod w8 w10 w12
  let v28 : W := v27 + v26
  let v29 : W := UInt256.mulMod w14 w7 w12
  let v30 : W := v29 + v28
  let v31 : W := UInt256.mulMod w16 w17 w12
  let v32 : W := v31 + v30
  let v33 : W := UInt256.land w15 v18
  let v34 : ByteArray := MachineState.writeBytes s.memory (Data.Bytes.natToBytesPadded v33.toNat 32) 832
  let v35 : W := v32 - v33
  let v36 : W := w12 + v35
  let v37 : W := UInt256.mulMod (N 2048) v36 w12
  let v38 : W := MachineState.readWord v34 64
  let v39 : W := w18 * v38
  let v40 : W := MachineState.readWord v34 160
  let v41 : W := MachineState.readWord v34 96
  let v42 : W := v41 * v40
  let v43 : W := v42 + v39
  let v44 : W := v43 + v43
  let v45 : W := UInt256.mulMod w18 v38 w12
  let v46 : W := MachineState.readWord v34 160
  let v47 : W := MachineState.readWord v34 96
  let v48 : W := UInt256.mulMod v47 v46 w12
  let v49 : W := v48 + v45
  let v50 : W := v49 + v49
  let v51 : W := v37 + v50
  let v52 : W := v37 + v44
  let v53 : W := MachineState.readWord v34 128
  {s with pc := N 7235, memory := v34, stack := v53 :: v52 :: v51 :: w5 :: w6 :: w7 :: w8 :: w9 :: w10 :: w11 :: w12 :: w13 :: w14 :: w15 :: w16 :: w17 :: w18 :: rest}

theorem sq11New_run (s : State) (carry w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions sq11NewProgram {s with pc := N 7110, stack := carry :: w0 :: w1 :: w2 :: w3 :: w4 :: w5 :: w6 :: w7 :: w8 :: w9 :: w10 :: w11 :: w12 :: w13 :: w14 :: w15 :: w16 :: w17 :: w18 :: rest} =
      some (sq11NewModel s carry w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 rest) := by
  let v0 : W := UInt256.mulMod carry w0 w1
  let v1 : W := v0 + w2
  let v2 : W := v1 + v1
  let v3 : W := w4 + v2
  let v4 : W := w4 + w3
  let v5 : W := MachineState.readWord s.memory 0
  let v6 : W := w13 * v5
  let v7 : W := v6 + v4
  let v8 : W := MachineState.readWord s.memory 224
  let v9 : W := w11 * v8
  let v10 : W := v9 + v7
  let v11 : W := w9 * w6
  let v12 : W := v11 + v10
  let v13 : W := w8 * w10
  let v14 : W := v13 + v12
  let v15 : W := w7 * w14
  let v16 : W := v15 + v14
  let v17 : W := w16 * w17
  let v18 : W := v17 + v16
  let v19 : W := MachineState.readWord s.memory 0
  let v20 : W := UInt256.mulMod w13 v19 w12
  let v21 : W := v20 + v3
  let v22 : W := MachineState.readWord s.memory 224
  let v23 : W := UInt256.mulMod w11 v22 w12
  let v24 : W := v23 + v21
  let v25 : W := UInt256.mulMod w9 w6 w12
  let v26 : W := v25 + v24
  let v27 : W := UInt256.mulMod w8 w10 w12
  let v28 : W := v27 + v26
  let v29 : W := UInt256.mulMod w14 w7 w12
  let v30 : W := v29 + v28
  let v31 : W := UInt256.mulMod w16 w17 w12
  let v32 : W := v31 + v30
  let v33 : W := UInt256.land w15 v18
  let v34 : ByteArray := MachineState.writeBytes s.memory (Data.Bytes.natToBytesPadded v33.toNat 32) 832
  let v35 : W := v32 - v33
  let v36 : W := w12 + v35
  let v37 : W := UInt256.mulMod (N 2048) v36 w12
  let v38 : W := MachineState.readWord v34 64
  let v39 : W := w18 * v38
  let v40 : W := MachineState.readWord v34 160
  let v41 : W := MachineState.readWord v34 96
  let v42 : W := v41 * v40
  let v43 : W := v42 + v39
  let v44 : W := v43 + v43
  let v45 : W := UInt256.mulMod w18 v38 w12
  let v46 : W := MachineState.readWord v34 160
  let v47 : W := MachineState.readWord v34 96
  let v48 : W := UInt256.mulMod v47 v46 w12
  let v49 : W := v48 + v45
  let v50 : W := v49 + v49
  let v51 : W := v37 + v50
  let v52 : W := v37 + v44
  let v53 : W := MachineState.readWord v34 128
  have h0 : runInstructions sq11Newpart0Program {s with pc := N 7110, memory := s.memory, stack := carry :: w0 :: w1 :: w2 :: w3 :: w4 :: w5 :: w6 :: w7 :: w8 :: w9 :: w10 :: w11 :: w12 :: w13 :: w14 :: w15 :: w16 :: w17 :: w18 :: rest} = some {s with pc := N 7118, memory := s.memory, stack := v4 :: v3 :: w5 :: w6 :: w7 :: w8 :: w9 :: w10 :: w11 :: w12 :: w13 :: w14 :: w15 :: w16 :: w17 :: w18 :: rest} := by
    simpa only [sq11Newpart0Model, v0, v1, v2, v3, v4] using sq11Newpart0_run (s) (carry) (w0) (w1) (w2) (w3) (w4) (w5) (w6) (w7) (w8) (w9) (w10) (w11) (w12) (w13) (w14) (w15) (w16) (w17) (w18) rest hcap hact
  have h1 : runInstructions sq11Newpart1Program {s with pc := N 7118, memory := s.memory, stack := v4 :: v3 :: w5 :: w6 :: w7 :: w8 :: w9 :: w10 :: w11 :: w12 :: w13 :: w14 :: w15 :: w16 :: w17 :: w18 :: rest} = some {s with pc := N 7127, memory := s.memory, stack := w11 :: v8 :: v7 :: v3 :: w5 :: w6 :: w7 :: w8 :: w9 :: w10 :: w11 :: w12 :: w13 :: w14 :: w15 :: w16 :: w17 :: w18 :: rest} := by
    simpa only [sq11Newpart1Model, v5, v6, v7, v8] using sq11Newpart1_run (s) (v4) (v3) (w5) (w6) (w7) (w8) (w9) (w10) (w11) (w12) (w13) (w14) (w15) (w16) (w17) (w18) rest hcap hact
  have h2 : runInstructions sq11Newpart2Program {s with pc := N 7127, memory := s.memory, stack := w11 :: v8 :: v7 :: v3 :: w5 :: w6 :: w7 :: w8 :: w9 :: w10 :: w11 :: w12 :: w13 :: w14 :: w15 :: w16 :: w17 :: w18 :: rest} = some {s with pc := N 7135, memory := s.memory, stack := w8 :: w10 :: v12 :: v3 :: w5 :: w6 :: w7 :: w8 :: w9 :: w10 :: w11 :: w12 :: w13 :: w14 :: w15 :: w16 :: w17 :: w18 :: rest} := by
    simpa only [sq11Newpart2Model, v9, v10, v11, v12] using sq11Newpart2_run (s) (w11) (v8) (v7) (v3) (w5) (w6) (w7) (w8) (w9) (w10) (w11) (w12) (w13) (w14) (w15) (w16) (w17) (w18) rest hcap hact
  have h3 : runInstructions sq11Newpart3Program {s with pc := N 7135, memory := s.memory, stack := w8 :: w10 :: v12 :: v3 :: w5 :: w6 :: w7 :: w8 :: w9 :: w10 :: w11 :: w12 :: w13 :: w14 :: w15 :: w16 :: w17 :: w18 :: rest} = some {s with pc := N 7143, memory := s.memory, stack := w16 :: w17 :: v16 :: v3 :: w5 :: w6 :: w7 :: w8 :: w9 :: w10 :: w11 :: w12 :: w13 :: w14 :: w15 :: w16 :: w17 :: w18 :: rest} := by
    simpa only [sq11Newpart3Model, v13, v14, v15, v16] using sq11Newpart3_run (s) (w8) (w10) (v12) (v3) (w5) (w6) (w7) (w8) (w9) (w10) (w11) (w12) (w13) (w14) (w15) (w16) (w17) (w18) rest hcap hact
  have h4 : runInstructions sq11Newpart4Program {s with pc := N 7143, memory := s.memory, stack := w16 :: w17 :: v16 :: v3 :: w5 :: w6 :: w7 :: w8 :: w9 :: w10 :: w11 :: w12 :: w13 :: w14 :: w15 :: w16 :: w17 :: w18 :: rest} = some {s with pc := N 7151, memory := s.memory, stack := v20 :: v3 :: v18 :: w5 :: w6 :: w7 :: w8 :: w9 :: w10 :: w11 :: w12 :: w13 :: w14 :: w15 :: w16 :: w17 :: w18 :: rest} := by
    simpa only [sq11Newpart4Model, v17, v18, v19, v20] using sq11Newpart4_run (s) (w16) (w17) (v16) (v3) (w5) (w6) (w7) (w8) (w9) (w10) (w11) (w12) (w13) (w14) (w15) (w16) (w17) (w18) rest hcap hact
  have h5 : runInstructions sq11Newpart5Program {s with pc := N 7151, memory := s.memory, stack := v20 :: v3 :: v18 :: w5 :: w6 :: w7 :: w8 :: w9 :: w10 :: w11 :: w12 :: w13 :: w14 :: w15 :: w16 :: w17 :: w18 :: rest} = some {s with pc := N 7160, memory := s.memory, stack := w12 :: v24 :: v18 :: w5 :: w6 :: w7 :: w8 :: w9 :: w10 :: w11 :: w12 :: w13 :: w14 :: w15 :: w16 :: w17 :: w18 :: rest} := by
    simpa only [sq11Newpart5Model, v21, v22, v23, v24] using sq11Newpart5_run (s) (v20) (v3) (v18) (w5) (w6) (w7) (w8) (w9) (w10) (w11) (w12) (w13) (w14) (w15) (w16) (w17) (w18) rest hcap hact
  have h6 : runInstructions sq11Newpart6Program {s with pc := N 7160, memory := s.memory, stack := w12 :: v24 :: v18 :: w5 :: w6 :: w7 :: w8 :: w9 :: w10 :: w11 :: w12 :: w13 :: w14 :: w15 :: w16 :: w17 :: w18 :: rest} = some {s with pc := N 7168, memory := s.memory, stack := v27 :: v26 :: v18 :: w5 :: w6 :: w7 :: w8 :: w9 :: w10 :: w11 :: w12 :: w13 :: w14 :: w15 :: w16 :: w17 :: w18 :: rest} := by
    simpa only [sq11Newpart6Model, v25, v26, v27] using sq11Newpart6_run (s) (w12) (v24) (v18) (w5) (w6) (w7) (w8) (w9) (w10) (w11) (w12) (w13) (w14) (w15) (w16) (w17) (w18) rest hcap hact
  have h7 : runInstructions sq11Newpart7Program {s with pc := N 7168, memory := s.memory, stack := v27 :: v26 :: v18 :: w5 :: w6 :: w7 :: w8 :: w9 :: w10 :: w11 :: w12 :: w13 :: w14 :: w15 :: w16 :: w17 :: w18 :: rest} = some {s with pc := N 7176, memory := s.memory, stack := w17 :: w12 :: v30 :: v18 :: w5 :: w6 :: w7 :: w8 :: w9 :: w10 :: w11 :: w12 :: w13 :: w14 :: w15 :: w16 :: w17 :: w18 :: rest} := by
    simpa only [sq11Newpart7Model, v28, v29, v30] using sq11Newpart7_run (s) (v27) (v26) (v18) (w5) (w6) (w7) (w8) (w9) (w10) (w11) (w12) (w13) (w14) (w15) (w16) (w17) (w18) rest hcap hact
  have h8 : runInstructions sq11Newpart8Program {s with pc := N 7176, memory := s.memory, stack := w17 :: w12 :: v30 :: v18 :: w5 :: w6 :: w7 :: w8 :: w9 :: w10 :: w11 :: w12 :: w13 :: w14 :: w15 :: w16 :: w17 :: w18 :: rest} = some {s with pc := N 7187, memory := v34, stack := v33 :: v32 :: w5 :: w6 :: w7 :: w8 :: w9 :: w10 :: w11 :: w12 :: w13 :: w14 :: w15 :: w16 :: w17 :: w18 :: rest} := by
    simpa only [sq11Newpart8Model, v31, v32, v33, v34] using sq11Newpart8_run (s) (w17) (w12) (v30) (v18) (w5) (w6) (w7) (w8) (w9) (w10) (w11) (w12) (w13) (w14) (w15) (w16) (w17) (w18) rest hcap hact
  have h9 : runInstructions sq11Newpart9Program {s with pc := N 7187, memory := v34, stack := v33 :: v32 :: w5 :: w6 :: w7 :: w8 :: w9 :: w10 :: w11 :: w12 :: w13 :: w14 :: w15 :: w16 :: w17 :: w18 :: rest} = some {s with pc := N 7198, memory := v34, stack := w18 :: v37 :: w5 :: w6 :: w7 :: w8 :: w9 :: w10 :: w11 :: w12 :: w13 :: w14 :: w15 :: w16 :: w17 :: w18 :: rest} := by
    simpa only [sq11Newpart9Model, v35, v36, v37] using sq11Newpart9_run ({s with memory := v34}) (v33) (v32) (w5) (w6) (w7) (w8) (w9) (w10) (w11) (w12) (w13) (w14) (w15) (w16) (w17) (w18) rest hcap hact
  have h10 : runInstructions sq11Newpart10Program {s with pc := N 7198, memory := v34, stack := w18 :: v37 :: w5 :: w6 :: w7 :: w8 :: w9 :: w10 :: w11 :: w12 :: w13 :: w14 :: w15 :: w16 :: w17 :: w18 :: rest} = some {s with pc := N 7208, memory := v34, stack := v40 :: v39 :: v38 :: w12 :: w18 :: v37 :: w5 :: w6 :: w7 :: w8 :: w9 :: w10 :: w11 :: w12 :: w13 :: w14 :: w15 :: w16 :: w17 :: w18 :: rest} := by
    simpa only [sq11Newpart10Model, v38, v39, v40] using sq11Newpart10_run ({s with memory := v34}) (w18) (v37) (w5) (w6) (w7) (w8) (w9) (w10) (w11) (w12) (w13) (w14) (w15) (w16) (w17) (w18) rest hcap hact
  have h11 : runInstructions sq11Newpart11Program {s with pc := N 7208, memory := v34, stack := v40 :: v39 :: v38 :: w12 :: w18 :: v37 :: w5 :: w6 :: w7 :: w8 :: w9 :: w10 :: w11 :: w12 :: w13 :: w14 :: w15 :: w16 :: w17 :: w18 :: rest} = some {s with pc := N 7217, memory := v34, stack := v45 :: v44 :: v37 :: w5 :: w6 :: w7 :: w8 :: w9 :: w10 :: w11 :: w12 :: w13 :: w14 :: w15 :: w16 :: w17 :: w18 :: rest} := by
    simpa only [sq11Newpart11Model, v41, v42, v43, v44, v45] using sq11Newpart11_run ({s with memory := v34}) (v40) (v39) (v38) (w12) (w18) (v37) (w5) (w6) (w7) (w8) (w9) (w10) (w11) (w12) (w13) (w14) (w15) (w16) (w17) (w18) rest hcap hact
  have h12 : runInstructions sq11Newpart12Program {s with pc := N 7217, memory := v34, stack := v45 :: v44 :: v37 :: w5 :: w6 :: w7 :: w8 :: w9 :: w10 :: w11 :: w12 :: w13 :: w14 :: w15 :: w16 :: w17 :: w18 :: rest} = some {s with pc := N 7227, memory := v34, stack := v49 :: v49 :: v44 :: v37 :: w5 :: w6 :: w7 :: w8 :: w9 :: w10 :: w11 :: w12 :: w13 :: w14 :: w15 :: w16 :: w17 :: w18 :: rest} := by
    simpa only [sq11Newpart12Model, v46, v47, v48, v49] using sq11Newpart12_run ({s with memory := v34}) (v45) (v44) (v37) (w5) (w6) (w7) (w8) (w9) (w10) (w11) (w12) (w13) (w14) (w15) (w16) (w17) (w18) rest hcap hact
  have h13 : runInstructions sq11Newpart13Program {s with pc := N 7227, memory := v34, stack := v49 :: v49 :: v44 :: v37 :: w5 :: w6 :: w7 :: w8 :: w9 :: w10 :: w11 :: w12 :: w13 :: w14 :: w15 :: w16 :: w17 :: w18 :: rest} = some {s with pc := N 7235, memory := v34, stack := v53 :: v52 :: v51 :: w5 :: w6 :: w7 :: w8 :: w9 :: w10 :: w11 :: w12 :: w13 :: w14 :: w15 :: w16 :: w17 :: w18 :: rest} := by
    simpa only [sq11Newpart13Model, v50, v51, v52, v53] using sq11Newpart13_run ({s with memory := v34}) (v49) (v49) (v44) (v37) (w5) (w6) (w7) (w8) (w9) (w10) (w11) (w12) (w13) (w14) (w15) (w16) (w17) (w18) rest hcap hact
  exact (runInstructions_append_some _ _ _ _ _ h0 (runInstructions_append_some _ _ _ _ _ h1 (runInstructions_append_some _ _ _ _ _ h2 (runInstructions_append_some _ _ _ _ _ h3 (runInstructions_append_some _ _ _ _ _ h4 (runInstructions_append_some _ _ _ _ _ h5 (runInstructions_append_some _ _ _ _ _ h6 (runInstructions_append_some _ _ _ _ _ h7 (runInstructions_append_some _ _ _ _ _ h8 (runInstructions_append_some _ _ _ _ _ h9 (runInstructions_append_some _ _ _ _ _ h10 (runInstructions_append_some _ _ _ _ _ h11 (runInstructions_append_some _ _ _ _ _ h12 h13)))))))))))))

#print axioms sq11New_run

def squareColumn11Model (s : State) (carry w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 : W) (rest : List W) : State :=
  let v0 : W := UInt256.mulMod carry w0 w1
  let v1 : W := v0 + w2
  let v2 : W := v1 + v1
  let v3 : W := w4 + v2
  let v4 : W := w4 + w3
  let v5 : W := MachineState.readWord s.memory 0
  let v6 : W := w13 * v5
  let v7 : W := v6 + v4
  let v8 : W := MachineState.readWord s.memory 224
  let v9 : W := w11 * v8
  let v10 : W := v9 + v7
  let v11 : W := w9 * w6
  let v12 : W := v11 + v10
  let v13 : W := w8 * w10
  let v14 : W := v13 + v12
  let v15 : W := w7 * w14
  let v16 : W := v15 + v14
  let v17 : W := w16 * w17
  let v18 : W := v17 + v16
  let v19 : W := MachineState.readWord s.memory 0
  let v20 : W := UInt256.mulMod w13 v19 w12
  let v21 : W := v20 + v3
  let v22 : W := MachineState.readWord s.memory 224
  let v23 : W := UInt256.mulMod w11 v22 w12
  let v24 : W := v23 + v21
  let v25 : W := UInt256.mulMod w9 w6 w12
  let v26 : W := v25 + v24
  let v27 : W := UInt256.mulMod w8 w10 w12
  let v28 : W := v27 + v26
  let v29 : W := UInt256.mulMod w14 w7 w12
  let v30 : W := v29 + v28
  let v31 : W := UInt256.mulMod w16 w17 w12
  let v32 : W := v31 + v30
  let v33 : W := UInt256.land w15 v18
  let v34 : ByteArray := MachineState.writeBytes s.memory (Data.Bytes.natToBytesPadded v33.toNat 32) 832
  let v35 : W := v32 - v33
  let v36 : W := w12 + v35
  let v37 : W := UInt256.mulMod v36 (N 2048) w12
  let v38 : W := MachineState.readWord v34 64
  let v39 : W := w18 * v38
  let v40 : W := MachineState.readWord v34 160
  let v41 : W := MachineState.readWord v34 96
  let v42 : W := v41 * v40
  let v43 : W := v42 + v39
  let v44 : W := v43 + v43
  let v45 : W := UInt256.mulMod w18 v38 w12
  let v46 : W := MachineState.readWord v34 160
  let v47 : W := MachineState.readWord v34 96
  let v48 : W := UInt256.mulMod v47 v46 w12
  let v49 : W := v48 + v45
  let v50 : W := v49 + v49
  let v51 : W := v37 + v50
  let v52 : W := v37 + v44
  let v53 : W := MachineState.readWord v34 128
  {s with pc := N 7235, memory := v34, stack := v53 :: v52 :: v51 :: w5 :: w6 :: w7 :: w8 :: w9 :: w10 :: w11 :: w12 :: w13 :: w14 :: w15 :: w16 :: w17 :: w18 :: rest}

def squareColumn11Program : List Instr := sq11NewProgram

private theorem aux_shared0 (w12 : W) (z0 : W) :
    (UInt256.mulMod (N 2048) z0 w12) = (UInt256.mulMod z0 (N 2048) w12) := by
  simp (disch := decide) only [addC, addA, addL, mulC, mmC, amC, andC, orC, xorC, eqC, read_disjoint, Challenge.EvmProof.Memory.readWord_writeWord]

private theorem prepared_model_eq (s : State) (carry w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 : W) (rest : List W) :
    squareColumn11Model s carry w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 rest = sq11NewModel s carry w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 rest := by
  let o0 : W := UInt256.mulMod carry w0 w1
  let o1 : W := o0 + w2
  let o2 : W := o1 + o1
  let o3 : W := w4 + o2
  let o4 : W := w4 + w3
  let o5 : W := MachineState.readWord s.memory 0
  let o6 : W := w13 * o5
  let o7 : W := o6 + o4
  let o8 : W := MachineState.readWord s.memory 224
  let o9 : W := w11 * o8
  let o10 : W := o9 + o7
  let o11 : W := w9 * w6
  let o12 : W := o11 + o10
  let o13 : W := w8 * w10
  let o14 : W := o13 + o12
  let o15 : W := w7 * w14
  let o16 : W := o15 + o14
  let o17 : W := w16 * w17
  let o18 : W := o17 + o16
  let o19 : W := MachineState.readWord s.memory 0
  let o20 : W := UInt256.mulMod w13 o19 w12
  let o21 : W := o20 + o3
  let o22 : W := MachineState.readWord s.memory 224
  let o23 : W := UInt256.mulMod w11 o22 w12
  let o24 : W := o23 + o21
  let o25 : W := UInt256.mulMod w9 w6 w12
  let o26 : W := o25 + o24
  let o27 : W := UInt256.mulMod w8 w10 w12
  let o28 : W := o27 + o26
  let o29 : W := UInt256.mulMod w14 w7 w12
  let o30 : W := o29 + o28
  let o31 : W := UInt256.mulMod w16 w17 w12
  let o32 : W := o31 + o30
  let o33 : W := UInt256.land w15 o18
  let o34 : ByteArray := MachineState.writeBytes s.memory (Data.Bytes.natToBytesPadded o33.toNat 32) 832
  let o35 : W := o32 - o33
  let o36 : W := w12 + o35
  let o37 : W := UInt256.mulMod o36 (N 2048) w12
  let o38 : W := MachineState.readWord o34 64
  let o39 : W := w18 * o38
  let o40 : W := MachineState.readWord o34 160
  let o41 : W := MachineState.readWord o34 96
  let o42 : W := o41 * o40
  let o43 : W := o42 + o39
  let o44 : W := o43 + o43
  let o45 : W := UInt256.mulMod w18 o38 w12
  let o46 : W := MachineState.readWord o34 160
  let o47 : W := MachineState.readWord o34 96
  let o48 : W := UInt256.mulMod o47 o46 w12
  let o49 : W := o48 + o45
  let o50 : W := o49 + o49
  let o51 : W := o37 + o50
  let o52 : W := o37 + o44
  let o53 : W := MachineState.readWord o34 128
  let n0 : W := UInt256.mulMod carry w0 w1
  let n1 : W := n0 + w2
  let n2 : W := n1 + n1
  let n3 : W := w4 + n2
  let n4 : W := w4 + w3
  let n5 : W := MachineState.readWord s.memory 0
  let n6 : W := w13 * n5
  let n7 : W := n6 + n4
  let n8 : W := MachineState.readWord s.memory 224
  let n9 : W := w11 * n8
  let n10 : W := n9 + n7
  let n11 : W := w9 * w6
  let n12 : W := n11 + n10
  let n13 : W := w8 * w10
  let n14 : W := n13 + n12
  let n15 : W := w7 * w14
  let n16 : W := n15 + n14
  let n17 : W := w16 * w17
  let n18 : W := n17 + n16
  let n19 : W := MachineState.readWord s.memory 0
  let n20 : W := UInt256.mulMod w13 n19 w12
  let n21 : W := n20 + n3
  let n22 : W := MachineState.readWord s.memory 224
  let n23 : W := UInt256.mulMod w11 n22 w12
  let n24 : W := n23 + n21
  let n25 : W := UInt256.mulMod w9 w6 w12
  let n26 : W := n25 + n24
  let n27 : W := UInt256.mulMod w8 w10 w12
  let n28 : W := n27 + n26
  let n29 : W := UInt256.mulMod w14 w7 w12
  let n30 : W := n29 + n28
  let n31 : W := UInt256.mulMod w16 w17 w12
  let n32 : W := n31 + n30
  let n33 : W := UInt256.land w15 n18
  let n34 : ByteArray := MachineState.writeBytes s.memory (Data.Bytes.natToBytesPadded n33.toNat 32) 832
  let n35 : W := n32 - n33
  let n36 : W := w12 + n35
  let n37 : W := UInt256.mulMod (N 2048) n36 w12
  let n38 : W := MachineState.readWord n34 64
  let n39 : W := w18 * n38
  let n40 : W := MachineState.readWord n34 160
  let n41 : W := MachineState.readWord n34 96
  let n42 : W := n41 * n40
  let n43 : W := n42 + n39
  let n44 : W := n43 + n43
  let n45 : W := UInt256.mulMod w18 n38 w12
  let n46 : W := MachineState.readWord n34 160
  let n47 : W := MachineState.readWord n34 96
  let n48 : W := UInt256.mulMod n47 n46 w12
  let n49 : W := n48 + n45
  let n50 : W := n49 + n49
  let n51 : W := n37 + n50
  let n52 : W := n37 + n44
  let n53 : W := MachineState.readWord n34 128
  have eq_o19 : o19 = o5 := by
    simp only [o19, o5]
  have eq_o22 : o22 = o8 := by
    simp only [o22, o8]
  have eq_o46 : o46 = o40 := by
    simp only [o46, o40]
  have eq_o47 : o47 = o41 := by
    simp only [o47, o41]
  have eq_n0 : n0 = o0 := by
    simp only [n0, o0]
  have eq_n1 : n1 = o1 := by
    simp only [n1, o1, eq_n0]
  have eq_n2 : n2 = o2 := by
    simp only [n2, o2, eq_n1]
  have eq_n3 : n3 = o3 := by
    simp only [n3, o3, eq_n2]
  have eq_n4 : n4 = o4 := by
    simp only [n4, o4]
  have eq_n5 : n5 = o5 := by
    simp only [n5, o5]
  have eq_n6 : n6 = o6 := by
    simp only [n6, o6, eq_n5]
  have eq_n7 : n7 = o7 := by
    simp only [n7, o7, eq_n6, eq_n4]
  have eq_n8 : n8 = o8 := by
    simp only [n8, o8]
  have eq_n9 : n9 = o9 := by
    simp only [n9, o9, eq_n8]
  have eq_n10 : n10 = o10 := by
    simp only [n10, o10, eq_n9, eq_n7]
  have eq_n11 : n11 = o11 := by
    simp only [n11, o11]
  have eq_n12 : n12 = o12 := by
    simp only [n12, o12, eq_n11, eq_n10]
  have eq_n13 : n13 = o13 := by
    simp only [n13, o13]
  have eq_n14 : n14 = o14 := by
    simp only [n14, o14, eq_n13, eq_n12]
  have eq_n15 : n15 = o15 := by
    simp only [n15, o15]
  have eq_n16 : n16 = o16 := by
    simp only [n16, o16, eq_n15, eq_n14]
  have eq_n17 : n17 = o17 := by
    simp only [n17, o17]
  have eq_n18 : n18 = o18 := by
    simp only [n18, o18, eq_n17, eq_n16]
  have eq_n19 : n19 = o5 := by
    simp only [n19, o5]
  have eq_n20 : n20 = o20 := by
    simp only [n20, o20, eq_n19, eq_o19]
  have eq_n21 : n21 = o21 := by
    simp only [n21, o21, eq_n20, eq_n3]
  have eq_n22 : n22 = o8 := by
    simp only [n22, o8]
  have eq_n23 : n23 = o23 := by
    simp only [n23, o23, eq_n22, eq_o22]
  have eq_n24 : n24 = o24 := by
    simp only [n24, o24, eq_n23, eq_n21]
  have eq_n25 : n25 = o25 := by
    simp only [n25, o25]
  have eq_n26 : n26 = o26 := by
    simp only [n26, o26, eq_n25, eq_n24]
  have eq_n27 : n27 = o27 := by
    simp only [n27, o27]
  have eq_n28 : n28 = o28 := by
    simp only [n28, o28, eq_n27, eq_n26]
  have eq_n29 : n29 = o29 := by
    simp only [n29, o29]
  have eq_n30 : n30 = o30 := by
    simp only [n30, o30, eq_n29, eq_n28]
  have eq_n31 : n31 = o31 := by
    simp only [n31, o31]
  have eq_n32 : n32 = o32 := by
    simp only [n32, o32, eq_n31, eq_n30]
  have eq_n33 : n33 = o33 := by
    simp only [n33, o33, eq_n18]
  have eq_n34 : n34 = o34 := by
    simp only [n34, o34, eq_n33]
  have eq_n35 : n35 = o35 := by
    simp only [n35, o35, eq_n32, eq_n33]
  have eq_n36 : n36 = o36 := by
    simp only [n36, o36, eq_n35]
  have eq_n37 : n37 = o37 := by
    simpa only [n37, o37, eq_n36] using
      (aux_shared0 w12 o36)
  have eq_n38 : n38 = o38 := by
    simp only [n38, o38, eq_n34]
  have eq_n39 : n39 = o39 := by
    simp only [n39, o39, eq_n38]
  have eq_n40 : n40 = o40 := by
    simp only [n40, o40, eq_n34]
  have eq_n41 : n41 = o41 := by
    simp only [n41, o41, eq_n34]
  have eq_n42 : n42 = o42 := by
    simp only [n42, o42, eq_n41, eq_n40]
  have eq_n43 : n43 = o43 := by
    simp only [n43, o43, eq_n42, eq_n39]
  have eq_n44 : n44 = o44 := by
    simp only [n44, o44, eq_n43]
  have eq_n45 : n45 = o45 := by
    simp only [n45, o45, eq_n38]
  have eq_n46 : n46 = o40 := by
    simp only [n46, o40, eq_n34]
  have eq_n47 : n47 = o41 := by
    simp only [n47, o41, eq_n34]
  have eq_n48 : n48 = o48 := by
    simp only [n48, o48, eq_n47, eq_n46, eq_o47, eq_o46]
  have eq_n49 : n49 = o49 := by
    simp only [n49, o49, eq_n48, eq_n45]
  have eq_n50 : n50 = o50 := by
    simp only [n50, o50, eq_n49]
  have eq_n51 : n51 = o51 := by
    simp only [n51, o51, eq_n37, eq_n50]
  have eq_n52 : n52 = o52 := by
    simp only [n52, o52, eq_n37, eq_n44]
  have eq_n53 : n53 = o53 := by
    simp only [n53, o53, eq_n34]
  change {s with pc := N 7235, memory := o34, stack := o53 :: o52 :: o51 :: w5 :: w6 :: w7 :: w8 :: w9 :: w10 :: w11 :: w12 :: w13 :: w14 :: w15 :: w16 :: w17 :: w18 :: rest} =
    {s with pc := N 7235, memory := n34, stack := n53 :: n52 :: n51 :: w5 :: w6 :: w7 :: w8 :: w9 :: w10 :: w11 :: w12 :: w13 :: w14 :: w15 :: w16 :: w17 :: w18 :: rest}
  simp only [eq_o19, eq_o22, eq_o46, eq_o47, eq_n0, eq_n1, eq_n2, eq_n3, eq_n4, eq_n5, eq_n6, eq_n7, eq_n8, eq_n9, eq_n10, eq_n11, eq_n12, eq_n13, eq_n14, eq_n15, eq_n16, eq_n17, eq_n18, eq_n19, eq_n20, eq_n21, eq_n22, eq_n23, eq_n24, eq_n25, eq_n26, eq_n27, eq_n28, eq_n29, eq_n30, eq_n31, eq_n32, eq_n33, eq_n34, eq_n35, eq_n36, eq_n37, eq_n38, eq_n39, eq_n40, eq_n41, eq_n42, eq_n43, eq_n44, eq_n45, eq_n46, eq_n47, eq_n48, eq_n49, eq_n50, eq_n51, eq_n52, eq_n53]
theorem squareColumn11_run (s : State) (carry w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions squareColumn11Program {s with pc := N 7110, stack := carry :: w0 :: w1 :: w2 :: w3 :: w4 :: w5 :: w6 :: w7 :: w8 :: w9 :: w10 :: w11 :: w12 :: w13 :: w14 :: w15 :: w16 :: w17 :: w18 :: rest} =
      some (squareColumn11Model s carry w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 rest) := by
  exact (sq11New_run s carry w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 rest hcap hact).trans
    (congrArg some (prepared_model_eq s carry w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 rest).symm)

#print axioms squareColumn11_run
end CycleSubmission.Execution
