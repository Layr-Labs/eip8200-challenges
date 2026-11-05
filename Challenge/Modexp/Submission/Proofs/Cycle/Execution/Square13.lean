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

def sq13Newpart0Program : List Instr :=
  [.op .ADD,
   .op (.Dup ⟨7, by decide⟩),
   .op (.Dup ⟨14, by decide⟩),
   .op .MUL,
   .op .ADD,
   .op (.Swap ⟨0, by decide⟩),
   .op (.Dup ⟨9, by decide⟩),
   .op (.Dup ⟨7, by decide⟩)]

def sq13Newpart0Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 : W) (rest : List W) : State :=
  let v0 : W := x0 + x1
  let v1 : W := x14 * x8
  let v2 : W := v1 + v0
  {s with pc := N 7400, memory := s.memory, stack := x7 :: x10 :: x2 :: v2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: rest}

theorem sq13Newpart0_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions sq13Newpart0Program {s with pc := N 7392, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: rest} =
      some (sq13Newpart0Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 18) : rest.length + j < 1024 := by omega
  simp [hz, hzn, sq13Newpart0Program, sq13Newpart0Model, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, capacity]


def sq13Newpart1Program : List Instr :=
  [.op (.Dup ⟨12, by decide⟩),
   .op .MULMOD,
   .op .ADD,
   .op (.Dup ⟨9, by decide⟩),
   .op (.Dup ⟨6, by decide⟩),
   .op (.Dup ⟨10, by decide⟩),
   .op .MULMOD,
   .op .ADD]

def sq13Newpart1Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 : W) (rest : List W) : State :=
  let v0 : W := UInt256.mulMod x12 x0 x1
  let v1 : W := v0 + x2
  let v2 : W := UInt256.mulMod x10 x7 x11
  let v3 : W := v2 + v1
  {s with pc := N 7408, memory := s.memory, stack := v3 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: rest}

theorem sq13Newpart1_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions sq13Newpart1Program {s with pc := N 7400, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: rest} =
      some (sq13Newpart1Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 19) : rest.length + j < 1024 := by omega
  simp [hz, hzn, sq13Newpart1Program, sq13Newpart1Model, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, capacity]


def sq13Newpart2Program : List Instr :=
  [.op (.Dup ⟨9, by decide⟩),
   .op (.Dup ⟨4, by decide⟩),
   .op (.Dup ⟨13, by decide⟩),
   .op .MULMOD,
   .op .ADD,
   .op (.Dup ⟨9, by decide⟩),
   .op (.Dup ⟨8, by decide⟩),
   .op (.Dup ⟨15, by decide⟩)]

def sq13Newpart2Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 : W) (rest : List W) : State :=
  let v0 : W := UInt256.mulMod x11 x3 x9
  let v1 : W := v0 + x0
  {s with pc := N 7416, memory := s.memory, stack := x13 :: x7 :: x9 :: v1 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: rest}

theorem sq13Newpart2_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions sq13Newpart2Program {s with pc := N 7408, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: rest} =
      some (sq13Newpart2Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 19) : rest.length + j < 1024 := by omega
  simp [hz, hzn, sq13Newpart2Program, sq13Newpart2Model, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, capacity]


def sq13Newpart3Program : List Instr :=
  [.op .MULMOD,
   .op .ADD,
   .op (.Swap ⟨0, by decide⟩),
   .op (.Dup ⟨12, by decide⟩),
   .op .AND,
   .op (.Dup ⟨0, by decide⟩),
   .push 1 64,
   .op .MSTORE]

def sq13Newpart3Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 : W) (rest : List W) : State :=
  let v0 : W := UInt256.mulMod x0 x1 x2
  let v1 : W := v0 + x3
  let v2 : W := UInt256.land x15 x4
  let v3 : ByteArray := MachineState.writeBytes s.memory (Data.Bytes.natToBytesPadded v2.toNat 32) 64
  {s with pc := N 7425, memory := v3, stack := v2 :: v1 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: x18 :: rest}

theorem sq13Newpart3_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions sq13Newpart3Program {s with pc := N 7416, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: x18 :: rest} =
      some (sq13Newpart3Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 19) : rest.length + j < 1024 := by omega
  have ha64 : (64 : W).toNat = 64 := rfl
  have hf64 := Monpro.activeWords_fix s 64 32 (by decide) (by norm_num) hact
  simp [hz, hzn, sq13Newpart3Program, sq13Newpart3Model, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, capacity, ha64, hf64]


def sq13Newpart4Program : List Instr :=
  [.op (.Dup ⟨9, by decide⟩),
   .op (.Swap ⟨1, by decide⟩),
   .op .SUB,
   .op (.Dup ⟨1, by decide⟩),
   .op .ADD,
   .push 2 2048,
   .op .MULMOD,
   .push 2 832,
   .op .MLOAD]

def sq13Newpart4Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 : W) (rest : List W) : State :=
  let v0 : W := x1 - x0
  let v1 : W := x9 + v0
  let v2 : W := UInt256.mulMod (N 2048) v1 x9
  let v3 : W := MachineState.readWord s.memory 832
  {s with pc := N 7438, memory := s.memory, stack := v3 :: v2 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: rest}

theorem sq13Newpart4_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions sq13Newpart4Program {s with pc := N 7425, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: rest} =
      some (sq13Newpart4Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 17) : rest.length + j < 1024 := by omega
  have ha832 : (832 : W).toNat = 832 := rfl
  have hf832 := Monpro.activeWords_fix s 832 32 (by decide) (by norm_num) hact
  simp [hz, hzn, sq13Newpart4Program, sq13Newpart4Model, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, capacity, ha832, hf832]


def sq13Newpart5Program : List Instr :=
  [.op (.Swap ⟨5, by decide⟩),
   .op .POP,
   .op (.Dup ⟨14, by decide⟩),
   .op (.Dup ⟨9, by decide⟩),
   .push 1 128,
   .op .MLOAD,
   .op (.Dup ⟨0, by decide⟩),
   .op (.Dup ⟨3, by decide⟩)]

def sq13Newpart5Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 : W) (rest : List W) : State :=
  let v0 : W := MachineState.readWord s.memory 128
  {s with pc := N 7447, memory := s.memory, stack := x15 :: v0 :: v0 :: x9 :: x15 :: x1 :: x2 :: x3 :: x4 :: x5 :: x0 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: rest}

theorem sq13Newpart5_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions sq13Newpart5Program {s with pc := N 7438, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: rest} =
      some (sq13Newpart5Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 20) : rest.length + j < 1024 := by omega
  have ha128 : (128 : W).toNat = 128 := rfl
  have hf128 := Monpro.activeWords_fix s 128 32 (by decide) (by norm_num) hact
  simp [hz, hzn, sq13Newpart5Program, sq13Newpart5Model, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, capacity, ha128, hf128]


def sq13Newpart6Program : List Instr :=
  [.op .MUL,
   .op (.Dup ⟨0, by decide⟩),
   .op .ADD,
   .op (.Swap ⟨2, by decide⟩),
   .op .MULMOD,
   .op (.Dup ⟨0, by decide⟩),
   .op .ADD,
   .op (.Dup ⟨2, by decide⟩)]

def sq13Newpart6Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 : W) (rest : List W) : State :=
  let v0 : W := x0 * x1
  let v1 : W := v0 + v0
  let v2 : W := UInt256.mulMod x4 x2 x3
  let v3 : W := v2 + v2
  {s with pc := N 7455, memory := s.memory, stack := x5 :: v3 :: v1 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: x18 :: x19 :: rest}

theorem sq13Newpart6_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions sq13Newpart6Program {s with pc := N 7447, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: x18 :: x19 :: rest} =
      some (sq13Newpart6Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 20) : rest.length + j < 1024 := by omega
  simp [hz, hzn, sq13Newpart6Program, sq13Newpart6Model, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, capacity]


def sq13Newpart7Program : List Instr :=
  [.op .ADD,
   .op (.Swap ⟨1, by decide⟩),
   .op .ADD,
   .push 1 160,
   .op .MLOAD,
   .op (.Dup ⟨0, by decide⟩),
   .op .MUL,
   .op .ADD]

def sq13Newpart7Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 : W) (rest : List W) : State :=
  let v0 : W := x0 + x1
  let v1 : W := x3 + x2
  let v2 : W := MachineState.readWord s.memory 160
  let v3 : W := v2 * v2
  let v4 : W := v3 + v1
  {s with pc := N 7464, memory := s.memory, stack := v4 :: v0 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: rest}

theorem sq13Newpart7_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions sq13Newpart7Program {s with pc := N 7455, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: rest} =
      some (sq13Newpart7Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 18) : rest.length + j < 1024 := by omega
  have ha160 : (160 : W).toNat = 160 := rfl
  have hf160 := Monpro.activeWords_fix s 160 32 (by decide) (by norm_num) hact
  simp [hz, hzn, sq13Newpart7Program, sq13Newpart7Model, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, capacity, ha160, hf160]


def sq13Newpart8Program : List Instr :=
  [.op (.Dup ⟨5, by decide⟩),
   .op (.Dup ⟨11, by decide⟩),
   .op .MUL,
   .op .ADD,
   .op (.Dup ⟨11, by decide⟩),
   .op (.Dup ⟨9, by decide⟩),
   .op .MUL,
   .op .ADD]

def sq13Newpart8Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 : W) (rest : List W) : State :=
  let v0 : W := x10 * x5
  let v1 : W := v0 + x0
  let v2 : W := x8 * x11
  let v3 : W := v2 + v1
  {s with pc := N 7472, memory := s.memory, stack := v3 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: rest}

theorem sq13Newpart8_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions sq13Newpart8Program {s with pc := N 7464, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: rest} =
      some (sq13Newpart8Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 18) : rest.length + j < 1024 := by omega
  simp [hz, hzn, sq13Newpart8Program, sq13Newpart8Model, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, capacity]


def sq13Newpart9Program : List Instr :=
  [.op (.Dup ⟨3, by decide⟩),
   .op (.Dup ⟨14, by decide⟩),
   .op .MUL,
   .op .ADD,
   .op (.Swap ⟨0, by decide⟩),
   .op (.Dup ⟨9, by decide⟩),
   .push 1 160,
   .op .MLOAD]

def sq13Newpart9Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 : W) (rest : List W) : State :=
  let v0 : W := x13 * x3
  let v1 : W := v0 + x0
  let v2 : W := MachineState.readWord s.memory 160
  {s with pc := N 7481, memory := s.memory, stack := v2 :: x9 :: x1 :: v1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: rest}

theorem sq13Newpart9_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions sq13Newpart9Program {s with pc := N 7472, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: rest} =
      some (sq13Newpart9Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 18) : rest.length + j < 1024 := by omega
  have ha160 : (160 : W).toNat = 160 := rfl
  have hf160 := Monpro.activeWords_fix s 160 32 (by decide) (by norm_num) hact
  simp [hz, hzn, sq13Newpart9Program, sq13Newpart9Model, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, capacity, ha160, hf160]


def sq13Newpart10Program : List Instr :=
  [.op (.Dup ⟨0, by decide⟩),
   .op .MULMOD,
   .op .ADD,
   .op (.Dup ⟨9, by decide⟩),
   .op (.Dup ⟨6, by decide⟩),
   .op (.Dup ⟨12, by decide⟩),
   .op .MULMOD,
   .op .ADD]

def sq13Newpart10Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 : W) (rest : List W) : State :=
  let v0 : W := UInt256.mulMod x0 x0 x1
  let v1 : W := v0 + x2
  let v2 : W := UInt256.mulMod x12 x7 x11
  let v3 : W := v2 + v1
  {s with pc := N 7489, memory := s.memory, stack := v3 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: rest}

theorem sq13Newpart10_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions sq13Newpart10Program {s with pc := N 7481, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: rest} =
      some (sq13Newpart10Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 19) : rest.length + j < 1024 := by omega
  simp [hz, hzn, sq13Newpart10Program, sq13Newpart10Model, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, capacity]


def sq13Newpart11Program : List Instr :=
  [.op (.Dup ⟨9, by decide⟩),
   .op (.Dup ⟨12, by decide⟩),
   .op (.Dup ⟨10, by decide⟩),
   .op .MULMOD,
   .op .ADD,
   .op (.Dup ⟨9, by decide⟩),
   .op (.Dup ⟨14, by decide⟩),
   .op (.Dup ⟨5, by decide⟩)]

def sq13Newpart11Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 : W) (rest : List W) : State :=
  let v0 : W := UInt256.mulMod x8 x11 x9
  let v1 : W := v0 + x0
  {s with pc := N 7497, memory := s.memory, stack := x3 :: x13 :: x9 :: v1 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: rest}

theorem sq13Newpart11_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions sq13Newpart11Program {s with pc := N 7489, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: rest} =
      some (sq13Newpart11Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 19) : rest.length + j < 1024 := by omega
  simp [hz, hzn, sq13Newpart11Program, sq13Newpart11Model, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, capacity]


def sq13Newpart12Program : List Instr :=
  [.op .MULMOD,
   .op .ADD,
   .op (.Swap ⟨0, by decide⟩),
   .op (.Dup ⟨12, by decide⟩),
   .op .AND,
   .op (.Dup ⟨0, by decide⟩),
   .push 1 96,
   .op .MSTORE]

def sq13Newpart12Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 : W) (rest : List W) : State :=
  let v0 : W := UInt256.mulMod x0 x1 x2
  let v1 : W := v0 + x3
  let v2 : W := UInt256.land x15 x4
  let v3 : ByteArray := MachineState.writeBytes s.memory (Data.Bytes.natToBytesPadded v2.toNat 32) 96
  {s with pc := N 7506, memory := v3, stack := v2 :: v1 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: x18 :: rest}

theorem sq13Newpart12_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions sq13Newpart12Program {s with pc := N 7497, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: x18 :: rest} =
      some (sq13Newpart12Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 19) : rest.length + j < 1024 := by omega
  have ha96 : (96 : W).toNat = 96 := rfl
  have hf96 := Monpro.activeWords_fix s 96 32 (by decide) (by norm_num) hact
  simp [hz, hzn, sq13Newpart12Program, sq13Newpart12Model, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, capacity, ha96, hf96]


def sq13Newpart13Program : List Instr :=
  [.op (.Dup ⟨9, by decide⟩),
   .op (.Swap ⟨1, by decide⟩),
   .op .SUB,
   .op (.Dup ⟨1, by decide⟩),
   .op .ADD,
   .push 2 2048,
   .op .MULMOD]

def sq13Newpart13Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 : W) (rest : List W) : State :=
  let v0 : W := x1 - x0
  let v1 : W := x9 + v0
  let v2 : W := UInt256.mulMod (N 2048) v1 x9
  {s with pc := N 7515, memory := s.memory, stack := v2 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: rest}

theorem sq13Newpart13_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions sq13Newpart13Program {s with pc := N 7506, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: rest} =
      some (sq13Newpart13Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 17) : rest.length + j < 1024 := by omega
  simp [hz, hzn, sq13Newpart13Program, sq13Newpart13Model, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, capacity]


def sq13NewProgram : List Instr :=
  [.op .ADD,
   .op (.Dup ⟨7, by decide⟩),
   .op (.Dup ⟨14, by decide⟩),
   .op .MUL,
   .op .ADD,
   .op (.Swap ⟨0, by decide⟩),
   .op (.Dup ⟨9, by decide⟩),
   .op (.Dup ⟨7, by decide⟩),
   .op (.Dup ⟨12, by decide⟩),
   .op .MULMOD,
   .op .ADD,
   .op (.Dup ⟨9, by decide⟩),
   .op (.Dup ⟨6, by decide⟩),
   .op (.Dup ⟨10, by decide⟩),
   .op .MULMOD,
   .op .ADD,
   .op (.Dup ⟨9, by decide⟩),
   .op (.Dup ⟨4, by decide⟩),
   .op (.Dup ⟨13, by decide⟩),
   .op .MULMOD,
   .op .ADD,
   .op (.Dup ⟨9, by decide⟩),
   .op (.Dup ⟨8, by decide⟩),
   .op (.Dup ⟨15, by decide⟩),
   .op .MULMOD,
   .op .ADD,
   .op (.Swap ⟨0, by decide⟩),
   .op (.Dup ⟨12, by decide⟩),
   .op .AND,
   .op (.Dup ⟨0, by decide⟩),
   .push 1 64,
   .op .MSTORE,
   .op (.Dup ⟨9, by decide⟩),
   .op (.Swap ⟨1, by decide⟩),
   .op .SUB,
   .op (.Dup ⟨1, by decide⟩),
   .op .ADD,
   .push 2 2048,
   .op .MULMOD,
   .push 2 832,
   .op .MLOAD,
   .op (.Swap ⟨5, by decide⟩),
   .op .POP,
   .op (.Dup ⟨14, by decide⟩),
   .op (.Dup ⟨9, by decide⟩),
   .push 1 128,
   .op .MLOAD,
   .op (.Dup ⟨0, by decide⟩),
   .op (.Dup ⟨3, by decide⟩),
   .op .MUL,
   .op (.Dup ⟨0, by decide⟩),
   .op .ADD,
   .op (.Swap ⟨2, by decide⟩),
   .op .MULMOD,
   .op (.Dup ⟨0, by decide⟩),
   .op .ADD,
   .op (.Dup ⟨2, by decide⟩),
   .op .ADD,
   .op (.Swap ⟨1, by decide⟩),
   .op .ADD,
   .push 1 160,
   .op .MLOAD,
   .op (.Dup ⟨0, by decide⟩),
   .op .MUL,
   .op .ADD,
   .op (.Dup ⟨5, by decide⟩),
   .op (.Dup ⟨11, by decide⟩),
   .op .MUL,
   .op .ADD,
   .op (.Dup ⟨11, by decide⟩),
   .op (.Dup ⟨9, by decide⟩),
   .op .MUL,
   .op .ADD,
   .op (.Dup ⟨3, by decide⟩),
   .op (.Dup ⟨14, by decide⟩),
   .op .MUL,
   .op .ADD,
   .op (.Swap ⟨0, by decide⟩),
   .op (.Dup ⟨9, by decide⟩),
   .push 1 160,
   .op .MLOAD,
   .op (.Dup ⟨0, by decide⟩),
   .op .MULMOD,
   .op .ADD,
   .op (.Dup ⟨9, by decide⟩),
   .op (.Dup ⟨6, by decide⟩),
   .op (.Dup ⟨12, by decide⟩),
   .op .MULMOD,
   .op .ADD,
   .op (.Dup ⟨9, by decide⟩),
   .op (.Dup ⟨12, by decide⟩),
   .op (.Dup ⟨10, by decide⟩),
   .op .MULMOD,
   .op .ADD,
   .op (.Dup ⟨9, by decide⟩),
   .op (.Dup ⟨14, by decide⟩),
   .op (.Dup ⟨5, by decide⟩),
   .op .MULMOD,
   .op .ADD,
   .op (.Swap ⟨0, by decide⟩),
   .op (.Dup ⟨12, by decide⟩),
   .op .AND,
   .op (.Dup ⟨0, by decide⟩),
   .push 1 96,
   .op .MSTORE,
   .op (.Dup ⟨9, by decide⟩),
   .op (.Swap ⟨1, by decide⟩),
   .op .SUB,
   .op (.Dup ⟨1, by decide⟩),
   .op .ADD,
   .push 2 2048,
   .op .MULMOD]

def sq13NewModel (s : State) (carry w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 : W) (rest : List W) : State :=
  let v0 : W := carry + w0
  let v1 : W := w13 * w7
  let v2 : W := v1 + v0
  let v3 : W := UInt256.mulMod w10 w6 w9
  let v4 : W := v3 + w1
  let v5 : W := UInt256.mulMod w8 w5 w9
  let v6 : W := v5 + v4
  let v7 : W := UInt256.mulMod w11 w3 w9
  let v8 : W := v7 + v6
  let v9 : W := UInt256.mulMod w13 w7 w9
  let v10 : W := v9 + v8
  let v11 : W := UInt256.land w12 v2
  let v12 : ByteArray := MachineState.writeBytes s.memory (Data.Bytes.natToBytesPadded v11.toNat 32) 64
  let v13 : W := v10 - v11
  let v14 : W := w9 + v13
  let v15 : W := UInt256.mulMod (N 2048) v14 w9
  let v16 : W := MachineState.readWord v12 832
  let v17 : W := MachineState.readWord v12 128
  let v18 : W := w15 * v17
  let v19 : W := v18 + v18
  let v20 : W := UInt256.mulMod w15 v17 w9
  let v21 : W := v20 + v20
  let v22 : W := v15 + v21
  let v23 : W := v15 + v19
  let v24 : W := MachineState.readWord v12 160
  let v25 : W := v24 * v24
  let v26 : W := v25 + v23
  let v27 : W := w10 * w5
  let v28 : W := v27 + v26
  let v29 : W := w8 * w11
  let v30 : W := v29 + v28
  let v31 : W := w13 * w3
  let v32 : W := v31 + v30
  let v33 : W := MachineState.readWord v12 160
  let v34 : W := UInt256.mulMod v33 v33 w9
  let v35 : W := v34 + v22
  let v36 : W := UInt256.mulMod w10 w5 w9
  let v37 : W := v36 + v35
  let v38 : W := UInt256.mulMod w8 w11 w9
  let v39 : W := v38 + v37
  let v40 : W := UInt256.mulMod w3 w13 w9
  let v41 : W := v40 + v39
  let v42 : W := UInt256.land w12 v32
  let v43 : ByteArray := MachineState.writeBytes v12 (Data.Bytes.natToBytesPadded v42.toNat 32) 96
  let v44 : W := v41 - v42
  let v45 : W := w9 + v44
  let v46 : W := UInt256.mulMod (N 2048) v45 w9
  {s with pc := N 7515, memory := v43, stack := v46 :: w2 :: w3 :: w4 :: w5 :: v16 :: w7 :: w8 :: w9 :: w10 :: w11 :: w12 :: w13 :: w14 :: w15 :: rest}

theorem sq13New_run (s : State) (carry w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions sq13NewProgram {s with pc := N 7392, stack := carry :: w0 :: w1 :: w2 :: w3 :: w4 :: w5 :: w6 :: w7 :: w8 :: w9 :: w10 :: w11 :: w12 :: w13 :: w14 :: w15 :: rest} =
      some (sq13NewModel s carry w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 rest) := by
  let v0 : W := carry + w0
  let v1 : W := w13 * w7
  let v2 : W := v1 + v0
  let v3 : W := UInt256.mulMod w10 w6 w9
  let v4 : W := v3 + w1
  let v5 : W := UInt256.mulMod w8 w5 w9
  let v6 : W := v5 + v4
  let v7 : W := UInt256.mulMod w11 w3 w9
  let v8 : W := v7 + v6
  let v9 : W := UInt256.mulMod w13 w7 w9
  let v10 : W := v9 + v8
  let v11 : W := UInt256.land w12 v2
  let v12 : ByteArray := MachineState.writeBytes s.memory (Data.Bytes.natToBytesPadded v11.toNat 32) 64
  let v13 : W := v10 - v11
  let v14 : W := w9 + v13
  let v15 : W := UInt256.mulMod (N 2048) v14 w9
  let v16 : W := MachineState.readWord v12 832
  let v17 : W := MachineState.readWord v12 128
  let v18 : W := w15 * v17
  let v19 : W := v18 + v18
  let v20 : W := UInt256.mulMod w15 v17 w9
  let v21 : W := v20 + v20
  let v22 : W := v15 + v21
  let v23 : W := v15 + v19
  let v24 : W := MachineState.readWord v12 160
  let v25 : W := v24 * v24
  let v26 : W := v25 + v23
  let v27 : W := w10 * w5
  let v28 : W := v27 + v26
  let v29 : W := w8 * w11
  let v30 : W := v29 + v28
  let v31 : W := w13 * w3
  let v32 : W := v31 + v30
  let v33 : W := MachineState.readWord v12 160
  let v34 : W := UInt256.mulMod v33 v33 w9
  let v35 : W := v34 + v22
  let v36 : W := UInt256.mulMod w10 w5 w9
  let v37 : W := v36 + v35
  let v38 : W := UInt256.mulMod w8 w11 w9
  let v39 : W := v38 + v37
  let v40 : W := UInt256.mulMod w3 w13 w9
  let v41 : W := v40 + v39
  let v42 : W := UInt256.land w12 v32
  let v43 : ByteArray := MachineState.writeBytes v12 (Data.Bytes.natToBytesPadded v42.toNat 32) 96
  let v44 : W := v41 - v42
  let v45 : W := w9 + v44
  let v46 : W := UInt256.mulMod (N 2048) v45 w9
  have h0 : runInstructions sq13Newpart0Program {s with pc := N 7392, memory := s.memory, stack := carry :: w0 :: w1 :: w2 :: w3 :: w4 :: w5 :: w6 :: w7 :: w8 :: w9 :: w10 :: w11 :: w12 :: w13 :: w14 :: w15 :: rest} = some {s with pc := N 7400, memory := s.memory, stack := w6 :: w9 :: w1 :: v2 :: w2 :: w3 :: w4 :: w5 :: w6 :: w7 :: w8 :: w9 :: w10 :: w11 :: w12 :: w13 :: w14 :: w15 :: rest} := by
    simpa only [sq13Newpart0Model, v0, v1, v2] using sq13Newpart0_run (s) (carry) (w0) (w1) (w2) (w3) (w4) (w5) (w6) (w7) (w8) (w9) (w10) (w11) (w12) (w13) (w14) (w15) rest hcap hact
  have h1 : runInstructions sq13Newpart1Program {s with pc := N 7400, memory := s.memory, stack := w6 :: w9 :: w1 :: v2 :: w2 :: w3 :: w4 :: w5 :: w6 :: w7 :: w8 :: w9 :: w10 :: w11 :: w12 :: w13 :: w14 :: w15 :: rest} = some {s with pc := N 7408, memory := s.memory, stack := v6 :: v2 :: w2 :: w3 :: w4 :: w5 :: w6 :: w7 :: w8 :: w9 :: w10 :: w11 :: w12 :: w13 :: w14 :: w15 :: rest} := by
    simpa only [sq13Newpart1Model, v3, v4, v5, v6] using sq13Newpart1_run (s) (w6) (w9) (w1) (v2) (w2) (w3) (w4) (w5) (w6) (w7) (w8) (w9) (w10) (w11) (w12) (w13) (w14) (w15) rest hcap hact
  have h2 : runInstructions sq13Newpart2Program {s with pc := N 7408, memory := s.memory, stack := v6 :: v2 :: w2 :: w3 :: w4 :: w5 :: w6 :: w7 :: w8 :: w9 :: w10 :: w11 :: w12 :: w13 :: w14 :: w15 :: rest} = some {s with pc := N 7416, memory := s.memory, stack := w13 :: w7 :: w9 :: v8 :: v2 :: w2 :: w3 :: w4 :: w5 :: w6 :: w7 :: w8 :: w9 :: w10 :: w11 :: w12 :: w13 :: w14 :: w15 :: rest} := by
    simpa only [sq13Newpart2Model, v7, v8] using sq13Newpart2_run (s) (v6) (v2) (w2) (w3) (w4) (w5) (w6) (w7) (w8) (w9) (w10) (w11) (w12) (w13) (w14) (w15) rest hcap hact
  have h3 : runInstructions sq13Newpart3Program {s with pc := N 7416, memory := s.memory, stack := w13 :: w7 :: w9 :: v8 :: v2 :: w2 :: w3 :: w4 :: w5 :: w6 :: w7 :: w8 :: w9 :: w10 :: w11 :: w12 :: w13 :: w14 :: w15 :: rest} = some {s with pc := N 7425, memory := v12, stack := v11 :: v10 :: w2 :: w3 :: w4 :: w5 :: w6 :: w7 :: w8 :: w9 :: w10 :: w11 :: w12 :: w13 :: w14 :: w15 :: rest} := by
    simpa only [sq13Newpart3Model, v9, v10, v11, v12] using sq13Newpart3_run (s) (w13) (w7) (w9) (v8) (v2) (w2) (w3) (w4) (w5) (w6) (w7) (w8) (w9) (w10) (w11) (w12) (w13) (w14) (w15) rest hcap hact
  have h4 : runInstructions sq13Newpart4Program {s with pc := N 7425, memory := v12, stack := v11 :: v10 :: w2 :: w3 :: w4 :: w5 :: w6 :: w7 :: w8 :: w9 :: w10 :: w11 :: w12 :: w13 :: w14 :: w15 :: rest} = some {s with pc := N 7438, memory := v12, stack := v16 :: v15 :: w2 :: w3 :: w4 :: w5 :: w6 :: w7 :: w8 :: w9 :: w10 :: w11 :: w12 :: w13 :: w14 :: w15 :: rest} := by
    simpa only [sq13Newpart4Model, v13, v14, v15, v16] using sq13Newpart4_run ({s with memory := v12}) (v11) (v10) (w2) (w3) (w4) (w5) (w6) (w7) (w8) (w9) (w10) (w11) (w12) (w13) (w14) (w15) rest hcap hact
  have h5 : runInstructions sq13Newpart5Program {s with pc := N 7438, memory := v12, stack := v16 :: v15 :: w2 :: w3 :: w4 :: w5 :: w6 :: w7 :: w8 :: w9 :: w10 :: w11 :: w12 :: w13 :: w14 :: w15 :: rest} = some {s with pc := N 7447, memory := v12, stack := w15 :: v17 :: v17 :: w9 :: w15 :: v15 :: w2 :: w3 :: w4 :: w5 :: v16 :: w7 :: w8 :: w9 :: w10 :: w11 :: w12 :: w13 :: w14 :: w15 :: rest} := by
    simpa only [sq13Newpart5Model, v17] using sq13Newpart5_run ({s with memory := v12}) (v16) (v15) (w2) (w3) (w4) (w5) (w6) (w7) (w8) (w9) (w10) (w11) (w12) (w13) (w14) (w15) rest hcap hact
  have h6 : runInstructions sq13Newpart6Program {s with pc := N 7447, memory := v12, stack := w15 :: v17 :: v17 :: w9 :: w15 :: v15 :: w2 :: w3 :: w4 :: w5 :: v16 :: w7 :: w8 :: w9 :: w10 :: w11 :: w12 :: w13 :: w14 :: w15 :: rest} = some {s with pc := N 7455, memory := v12, stack := v15 :: v21 :: v19 :: v15 :: w2 :: w3 :: w4 :: w5 :: v16 :: w7 :: w8 :: w9 :: w10 :: w11 :: w12 :: w13 :: w14 :: w15 :: rest} := by
    simpa only [sq13Newpart6Model, v18, v19, v20, v21] using sq13Newpart6_run ({s with memory := v12}) (w15) (v17) (v17) (w9) (w15) (v15) (w2) (w3) (w4) (w5) (v16) (w7) (w8) (w9) (w10) (w11) (w12) (w13) (w14) (w15) rest hcap hact
  have h7 : runInstructions sq13Newpart7Program {s with pc := N 7455, memory := v12, stack := v15 :: v21 :: v19 :: v15 :: w2 :: w3 :: w4 :: w5 :: v16 :: w7 :: w8 :: w9 :: w10 :: w11 :: w12 :: w13 :: w14 :: w15 :: rest} = some {s with pc := N 7464, memory := v12, stack := v26 :: v22 :: w2 :: w3 :: w4 :: w5 :: v16 :: w7 :: w8 :: w9 :: w10 :: w11 :: w12 :: w13 :: w14 :: w15 :: rest} := by
    simpa only [sq13Newpart7Model, v22, v23, v24, v25, v26] using sq13Newpart7_run ({s with memory := v12}) (v15) (v21) (v19) (v15) (w2) (w3) (w4) (w5) (v16) (w7) (w8) (w9) (w10) (w11) (w12) (w13) (w14) (w15) rest hcap hact
  have h8 : runInstructions sq13Newpart8Program {s with pc := N 7464, memory := v12, stack := v26 :: v22 :: w2 :: w3 :: w4 :: w5 :: v16 :: w7 :: w8 :: w9 :: w10 :: w11 :: w12 :: w13 :: w14 :: w15 :: rest} = some {s with pc := N 7472, memory := v12, stack := v30 :: v22 :: w2 :: w3 :: w4 :: w5 :: v16 :: w7 :: w8 :: w9 :: w10 :: w11 :: w12 :: w13 :: w14 :: w15 :: rest} := by
    simpa only [sq13Newpart8Model, v27, v28, v29, v30] using sq13Newpart8_run ({s with memory := v12}) (v26) (v22) (w2) (w3) (w4) (w5) (v16) (w7) (w8) (w9) (w10) (w11) (w12) (w13) (w14) (w15) rest hcap hact
  have h9 : runInstructions sq13Newpart9Program {s with pc := N 7472, memory := v12, stack := v30 :: v22 :: w2 :: w3 :: w4 :: w5 :: v16 :: w7 :: w8 :: w9 :: w10 :: w11 :: w12 :: w13 :: w14 :: w15 :: rest} = some {s with pc := N 7481, memory := v12, stack := v33 :: w9 :: v22 :: v32 :: w2 :: w3 :: w4 :: w5 :: v16 :: w7 :: w8 :: w9 :: w10 :: w11 :: w12 :: w13 :: w14 :: w15 :: rest} := by
    simpa only [sq13Newpart9Model, v31, v32, v33] using sq13Newpart9_run ({s with memory := v12}) (v30) (v22) (w2) (w3) (w4) (w5) (v16) (w7) (w8) (w9) (w10) (w11) (w12) (w13) (w14) (w15) rest hcap hact
  have h10 : runInstructions sq13Newpart10Program {s with pc := N 7481, memory := v12, stack := v33 :: w9 :: v22 :: v32 :: w2 :: w3 :: w4 :: w5 :: v16 :: w7 :: w8 :: w9 :: w10 :: w11 :: w12 :: w13 :: w14 :: w15 :: rest} = some {s with pc := N 7489, memory := v12, stack := v37 :: v32 :: w2 :: w3 :: w4 :: w5 :: v16 :: w7 :: w8 :: w9 :: w10 :: w11 :: w12 :: w13 :: w14 :: w15 :: rest} := by
    simpa only [sq13Newpart10Model, v34, v35, v36, v37] using sq13Newpart10_run ({s with memory := v12}) (v33) (w9) (v22) (v32) (w2) (w3) (w4) (w5) (v16) (w7) (w8) (w9) (w10) (w11) (w12) (w13) (w14) (w15) rest hcap hact
  have h11 : runInstructions sq13Newpart11Program {s with pc := N 7489, memory := v12, stack := v37 :: v32 :: w2 :: w3 :: w4 :: w5 :: v16 :: w7 :: w8 :: w9 :: w10 :: w11 :: w12 :: w13 :: w14 :: w15 :: rest} = some {s with pc := N 7497, memory := v12, stack := w3 :: w13 :: w9 :: v39 :: v32 :: w2 :: w3 :: w4 :: w5 :: v16 :: w7 :: w8 :: w9 :: w10 :: w11 :: w12 :: w13 :: w14 :: w15 :: rest} := by
    simpa only [sq13Newpart11Model, v38, v39] using sq13Newpart11_run ({s with memory := v12}) (v37) (v32) (w2) (w3) (w4) (w5) (v16) (w7) (w8) (w9) (w10) (w11) (w12) (w13) (w14) (w15) rest hcap hact
  have h12 : runInstructions sq13Newpart12Program {s with pc := N 7497, memory := v12, stack := w3 :: w13 :: w9 :: v39 :: v32 :: w2 :: w3 :: w4 :: w5 :: v16 :: w7 :: w8 :: w9 :: w10 :: w11 :: w12 :: w13 :: w14 :: w15 :: rest} = some {s with pc := N 7506, memory := v43, stack := v42 :: v41 :: w2 :: w3 :: w4 :: w5 :: v16 :: w7 :: w8 :: w9 :: w10 :: w11 :: w12 :: w13 :: w14 :: w15 :: rest} := by
    simpa only [sq13Newpart12Model, v40, v41, v42, v43] using sq13Newpart12_run ({s with memory := v12}) (w3) (w13) (w9) (v39) (v32) (w2) (w3) (w4) (w5) (v16) (w7) (w8) (w9) (w10) (w11) (w12) (w13) (w14) (w15) rest hcap hact
  have h13 : runInstructions sq13Newpart13Program {s with pc := N 7506, memory := v43, stack := v42 :: v41 :: w2 :: w3 :: w4 :: w5 :: v16 :: w7 :: w8 :: w9 :: w10 :: w11 :: w12 :: w13 :: w14 :: w15 :: rest} = some {s with pc := N 7515, memory := v43, stack := v46 :: w2 :: w3 :: w4 :: w5 :: v16 :: w7 :: w8 :: w9 :: w10 :: w11 :: w12 :: w13 :: w14 :: w15 :: rest} := by
    simpa only [sq13Newpart13Model, v44, v45, v46] using sq13Newpart13_run ({s with memory := v43}) (v42) (v41) (w2) (w3) (w4) (w5) (v16) (w7) (w8) (w9) (w10) (w11) (w12) (w13) (w14) (w15) rest hcap hact
  exact (runInstructions_append_some _ _ _ _ _ h0 (runInstructions_append_some _ _ _ _ _ h1 (runInstructions_append_some _ _ _ _ _ h2 (runInstructions_append_some _ _ _ _ _ h3 (runInstructions_append_some _ _ _ _ _ h4 (runInstructions_append_some _ _ _ _ _ h5 (runInstructions_append_some _ _ _ _ _ h6 (runInstructions_append_some _ _ _ _ _ h7 (runInstructions_append_some _ _ _ _ _ h8 (runInstructions_append_some _ _ _ _ _ h9 (runInstructions_append_some _ _ _ _ _ h10 (runInstructions_append_some _ _ _ _ _ h11 (runInstructions_append_some _ _ _ _ _ h12 h13)))))))))))))

#print axioms sq13New_run

def squareColumn13Model (s : State) (carry w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 : W) (rest : List W) : State :=
  let v0 : W := carry + w0
  let v1 : W := w13 * w7
  let v2 : W := v1 + v0
  let v3 : W := UInt256.mulMod w10 w6 w9
  let v4 : W := v3 + w1
  let v5 : W := UInt256.mulMod w8 w5 w9
  let v6 : W := v5 + v4
  let v7 : W := UInt256.mulMod w11 w3 w9
  let v8 : W := v7 + v6
  let v9 : W := UInt256.mulMod w13 w7 w9
  let v10 : W := v9 + v8
  let v11 : W := UInt256.land w12 v2
  let v12 : ByteArray := MachineState.writeBytes s.memory (Data.Bytes.natToBytesPadded v11.toNat 32) 64
  let v13 : W := v10 - v11
  let v14 : W := w9 + v13
  let v15 : W := UInt256.mulMod v14 (N 2048) w9
  let v16 : W := MachineState.readWord v12 832
  let v17 : W := MachineState.readWord v12 128
  let v18 : W := w15 * v17
  let v19 : W := v18 + v18
  let v20 : W := UInt256.mulMod w15 v17 w9
  let v21 : W := v20 + v20
  let v22 : W := v15 + v21
  let v23 : W := v15 + v19
  let v24 : W := MachineState.readWord v12 160
  let v25 : W := v24 * v24
  let v26 : W := v25 + v23
  let v27 : W := w10 * w5
  let v28 : W := v27 + v26
  let v29 : W := w8 * w11
  let v30 : W := v29 + v28
  let v31 : W := w13 * w3
  let v32 : W := v31 + v30
  let v33 : W := MachineState.readWord v12 160
  let v34 : W := UInt256.mulMod v33 v33 w9
  let v35 : W := v34 + v22
  let v36 : W := UInt256.mulMod w10 w5 w9
  let v37 : W := v36 + v35
  let v38 : W := UInt256.mulMod w8 w11 w9
  let v39 : W := v38 + v37
  let v40 : W := UInt256.mulMod w3 w13 w9
  let v41 : W := v40 + v39
  let v42 : W := UInt256.land w12 v32
  let v43 : ByteArray := MachineState.writeBytes v12 (Data.Bytes.natToBytesPadded v42.toNat 32) 96
  let v44 : W := v41 - v42
  let v45 : W := w9 + v44
  let v46 : W := UInt256.mulMod v45 (N 2048) w9
  {s with pc := N 7515, memory := v43, stack := v46 :: w2 :: w3 :: w4 :: w5 :: v16 :: w7 :: w8 :: w9 :: w10 :: w11 :: w12 :: w13 :: w14 :: w15 :: rest}

def squareColumn13Program : List Instr := sq13NewProgram

private theorem aux_shared0 (w9 : W) (z0 : W) :
    (UInt256.mulMod (N 2048) z0 w9) = (UInt256.mulMod z0 (N 2048) w9) := by
  simp (disch := decide) only [addC, addA, addL, mulC, mmC, amC, andC, orC, xorC, eqC, read_disjoint, Challenge.EvmProof.Memory.readWord_writeWord]

private theorem prepared_model_eq (s : State) (carry w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 : W) (rest : List W) :
    squareColumn13Model s carry w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 rest = sq13NewModel s carry w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 rest := by
  let o0 : W := carry + w0
  let o1 : W := w13 * w7
  let o2 : W := o1 + o0
  let o3 : W := UInt256.mulMod w10 w6 w9
  let o4 : W := o3 + w1
  let o5 : W := UInt256.mulMod w8 w5 w9
  let o6 : W := o5 + o4
  let o7 : W := UInt256.mulMod w11 w3 w9
  let o8 : W := o7 + o6
  let o9 : W := UInt256.mulMod w13 w7 w9
  let o10 : W := o9 + o8
  let o11 : W := UInt256.land w12 o2
  let o12 : ByteArray := MachineState.writeBytes s.memory (Data.Bytes.natToBytesPadded o11.toNat 32) 64
  let o13 : W := o10 - o11
  let o14 : W := w9 + o13
  let o15 : W := UInt256.mulMod o14 (N 2048) w9
  let o16 : W := MachineState.readWord o12 832
  let o17 : W := MachineState.readWord o12 128
  let o18 : W := w15 * o17
  let o19 : W := o18 + o18
  let o20 : W := UInt256.mulMod w15 o17 w9
  let o21 : W := o20 + o20
  let o22 : W := o15 + o21
  let o23 : W := o15 + o19
  let o24 : W := MachineState.readWord o12 160
  let o25 : W := o24 * o24
  let o26 : W := o25 + o23
  let o27 : W := w10 * w5
  let o28 : W := o27 + o26
  let o29 : W := w8 * w11
  let o30 : W := o29 + o28
  let o31 : W := w13 * w3
  let o32 : W := o31 + o30
  let o33 : W := MachineState.readWord o12 160
  let o34 : W := UInt256.mulMod o33 o33 w9
  let o35 : W := o34 + o22
  let o36 : W := UInt256.mulMod w10 w5 w9
  let o37 : W := o36 + o35
  let o38 : W := UInt256.mulMod w8 w11 w9
  let o39 : W := o38 + o37
  let o40 : W := UInt256.mulMod w3 w13 w9
  let o41 : W := o40 + o39
  let o42 : W := UInt256.land w12 o32
  let o43 : ByteArray := MachineState.writeBytes o12 (Data.Bytes.natToBytesPadded o42.toNat 32) 96
  let o44 : W := o41 - o42
  let o45 : W := w9 + o44
  let o46 : W := UInt256.mulMod o45 (N 2048) w9
  let n0 : W := carry + w0
  let n1 : W := w13 * w7
  let n2 : W := n1 + n0
  let n3 : W := UInt256.mulMod w10 w6 w9
  let n4 : W := n3 + w1
  let n5 : W := UInt256.mulMod w8 w5 w9
  let n6 : W := n5 + n4
  let n7 : W := UInt256.mulMod w11 w3 w9
  let n8 : W := n7 + n6
  let n9 : W := UInt256.mulMod w13 w7 w9
  let n10 : W := n9 + n8
  let n11 : W := UInt256.land w12 n2
  let n12 : ByteArray := MachineState.writeBytes s.memory (Data.Bytes.natToBytesPadded n11.toNat 32) 64
  let n13 : W := n10 - n11
  let n14 : W := w9 + n13
  let n15 : W := UInt256.mulMod (N 2048) n14 w9
  let n16 : W := MachineState.readWord n12 832
  let n17 : W := MachineState.readWord n12 128
  let n18 : W := w15 * n17
  let n19 : W := n18 + n18
  let n20 : W := UInt256.mulMod w15 n17 w9
  let n21 : W := n20 + n20
  let n22 : W := n15 + n21
  let n23 : W := n15 + n19
  let n24 : W := MachineState.readWord n12 160
  let n25 : W := n24 * n24
  let n26 : W := n25 + n23
  let n27 : W := w10 * w5
  let n28 : W := n27 + n26
  let n29 : W := w8 * w11
  let n30 : W := n29 + n28
  let n31 : W := w13 * w3
  let n32 : W := n31 + n30
  let n33 : W := MachineState.readWord n12 160
  let n34 : W := UInt256.mulMod n33 n33 w9
  let n35 : W := n34 + n22
  let n36 : W := UInt256.mulMod w10 w5 w9
  let n37 : W := n36 + n35
  let n38 : W := UInt256.mulMod w8 w11 w9
  let n39 : W := n38 + n37
  let n40 : W := UInt256.mulMod w3 w13 w9
  let n41 : W := n40 + n39
  let n42 : W := UInt256.land w12 n32
  let n43 : ByteArray := MachineState.writeBytes n12 (Data.Bytes.natToBytesPadded n42.toNat 32) 96
  let n44 : W := n41 - n42
  let n45 : W := w9 + n44
  let n46 : W := UInt256.mulMod (N 2048) n45 w9
  have eq_o33 : o33 = o24 := by
    simp only [o33, o24]
  have eq_n0 : n0 = o0 := by
    simp only [n0, o0]
  have eq_n1 : n1 = o1 := by
    simp only [n1, o1]
  have eq_n2 : n2 = o2 := by
    simp only [n2, o2, eq_n1, eq_n0]
  have eq_n3 : n3 = o3 := by
    simp only [n3, o3]
  have eq_n4 : n4 = o4 := by
    simp only [n4, o4, eq_n3]
  have eq_n5 : n5 = o5 := by
    simp only [n5, o5]
  have eq_n6 : n6 = o6 := by
    simp only [n6, o6, eq_n5, eq_n4]
  have eq_n7 : n7 = o7 := by
    simp only [n7, o7]
  have eq_n8 : n8 = o8 := by
    simp only [n8, o8, eq_n7, eq_n6]
  have eq_n9 : n9 = o9 := by
    simp only [n9, o9]
  have eq_n10 : n10 = o10 := by
    simp only [n10, o10, eq_n9, eq_n8]
  have eq_n11 : n11 = o11 := by
    simp only [n11, o11, eq_n2]
  have eq_n12 : n12 = o12 := by
    simp only [n12, o12, eq_n11]
  have eq_n13 : n13 = o13 := by
    simp only [n13, o13, eq_n10, eq_n11]
  have eq_n14 : n14 = o14 := by
    simp only [n14, o14, eq_n13]
  have eq_n15 : n15 = o15 := by
    simpa only [n15, o15, eq_n14] using
      (aux_shared0 w9 o14)
  have eq_n16 : n16 = o16 := by
    simp only [n16, o16, eq_n12]
  have eq_n17 : n17 = o17 := by
    simp only [n17, o17, eq_n12]
  have eq_n18 : n18 = o18 := by
    simp only [n18, o18, eq_n17]
  have eq_n19 : n19 = o19 := by
    simp only [n19, o19, eq_n18]
  have eq_n20 : n20 = o20 := by
    simp only [n20, o20, eq_n17]
  have eq_n21 : n21 = o21 := by
    simp only [n21, o21, eq_n20]
  have eq_n22 : n22 = o22 := by
    simp only [n22, o22, eq_n15, eq_n21]
  have eq_n23 : n23 = o23 := by
    simp only [n23, o23, eq_n15, eq_n19]
  have eq_n24 : n24 = o24 := by
    simp only [n24, o24, eq_n12]
  have eq_n25 : n25 = o25 := by
    simp only [n25, o25, eq_n24]
  have eq_n26 : n26 = o26 := by
    simp only [n26, o26, eq_n25, eq_n23]
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
  have eq_n33 : n33 = o24 := by
    simp only [n33, o24, eq_n12]
  have eq_n34 : n34 = o34 := by
    simp only [n34, o34, eq_n33, eq_o33]
  have eq_n35 : n35 = o35 := by
    simp only [n35, o35, eq_n34, eq_n22]
  have eq_n36 : n36 = o36 := by
    simp only [n36, o36]
  have eq_n37 : n37 = o37 := by
    simp only [n37, o37, eq_n36, eq_n35]
  have eq_n38 : n38 = o38 := by
    simp only [n38, o38]
  have eq_n39 : n39 = o39 := by
    simp only [n39, o39, eq_n38, eq_n37]
  have eq_n40 : n40 = o40 := by
    simp only [n40, o40]
  have eq_n41 : n41 = o41 := by
    simp only [n41, o41, eq_n40, eq_n39]
  have eq_n42 : n42 = o42 := by
    simp only [n42, o42, eq_n32]
  have eq_n43 : n43 = o43 := by
    simp only [n43, o43, eq_n12, eq_n42]
  have eq_n44 : n44 = o44 := by
    simp only [n44, o44, eq_n41, eq_n42]
  have eq_n45 : n45 = o45 := by
    simp only [n45, o45, eq_n44]
  have eq_n46 : n46 = o46 := by
    simpa only [n46, o46, eq_n45] using
      (aux_shared0 w9 o45)
  change {s with pc := N 7515, memory := o43, stack := o46 :: w2 :: w3 :: w4 :: w5 :: o16 :: w7 :: w8 :: w9 :: w10 :: w11 :: w12 :: w13 :: w14 :: w15 :: rest} =
    {s with pc := N 7515, memory := n43, stack := n46 :: w2 :: w3 :: w4 :: w5 :: n16 :: w7 :: w8 :: w9 :: w10 :: w11 :: w12 :: w13 :: w14 :: w15 :: rest}
  simp only [eq_o33, eq_n0, eq_n1, eq_n2, eq_n3, eq_n4, eq_n5, eq_n6, eq_n7, eq_n8, eq_n9, eq_n10, eq_n11, eq_n12, eq_n13, eq_n14, eq_n15, eq_n16, eq_n17, eq_n18, eq_n19, eq_n20, eq_n21, eq_n22, eq_n23, eq_n24, eq_n25, eq_n26, eq_n27, eq_n28, eq_n29, eq_n30, eq_n31, eq_n32, eq_n33, eq_n34, eq_n35, eq_n36, eq_n37, eq_n38, eq_n39, eq_n40, eq_n41, eq_n42, eq_n43, eq_n44, eq_n45, eq_n46]
theorem squareColumn13_run (s : State) (carry w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions squareColumn13Program {s with pc := N 7392, stack := carry :: w0 :: w1 :: w2 :: w3 :: w4 :: w5 :: w6 :: w7 :: w8 :: w9 :: w10 :: w11 :: w12 :: w13 :: w14 :: w15 :: rest} =
      some (squareColumn13Model s carry w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 rest) := by
  exact (sq13New_run s carry w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 rest hcap hact).trans
    (congrArg some (prepared_model_eq s carry w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 rest).symm)

#print axioms squareColumn13_run
end CycleSubmission.Execution
