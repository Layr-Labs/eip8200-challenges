import Challenge.Modexp.Submission.Proofs.Prepared.StackArgs
import Challenge.Modexp.Submission.Proofs.Prepared.Arithmetic
import Challenge.Modexp.Submission.Proofs.Fast.Monpro
import Challenge.Modexp.Submission.Proofs.Bytecode.WindowNibbleDefs
open CycleSubmission.SharedStackArgs

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

def pr7Newpart0Program : List Instr :=
  [
  .op (.Swap ⟨4, by decide⟩),
   .op .MULMOD,
   .op .ADD,
   .op (.Dup ⟨10, by decide⟩),
   .push 1 96,
   .op .MLOAD,
   .push 2 1856,
   .op .MLOAD]

def pr7Newpart0Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 : W) (rest : List W) : State :=
  let v0 : W := UInt256.mulMod x5 x1 x2
  let v1 : W := v0 + x3
  let v2 : W := MachineState.readWord s.memory 96
  let v3 : W := MachineState.readWord s.memory 1856
  {s with pc := N 8515, memory := s.memory, stack := v3 :: v2 :: x13 :: v1 :: x4 :: x0 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: x18 :: x19 :: rest}

theorem pr7Newpart0_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions pr7Newpart0Program {s with pc := N 8504, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: x18 :: x19 :: rest} =
      some (pr7Newpart0Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 20) : rest.length + j < 1024 := by omega
  have ha96 : (96 : W).toNat = 96 := rfl
  have hf96 := Monpro.activeWords_fix s 96 32 (by decide) (by norm_num) hact
  have ha1856 : (1856 : W).toNat = 1856 := rfl
  have hf1856 := Monpro.activeWords_fix s 1856 32 (by decide) (by norm_num) hact
  simp [hz, hzn, pr7Newpart0Program, pr7Newpart0Model, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, capacity, ha96, hf96, ha1856, hf1856]


def pr7Newpart1Program : List Instr :=
  [
  .op (.Swap ⟨4, by decide⟩),
   .op (.Dup ⟨1, by decide⟩),
   .op (.Dup ⟨6, by decide⟩),
   .op .MUL,
   .op .ADD,
   .op (.Swap ⟨4, by decide⟩),
   .op .MULMOD,
   .op .ADD]

def pr7Newpart1Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 : W) (rest : List W) : State :=
  let v0 : W := x0 * x1
  let v1 : W := v0 + x5
  let v2 : W := UInt256.mulMod x0 x1 x2
  let v3 : W := v2 + x3
  {s with pc := N 8523, memory := s.memory, stack := v3 :: x4 :: v1 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: x18 :: x19 :: rest}

theorem pr7Newpart1_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions pr7Newpart1Program {s with pc := N 8515, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: x18 :: x19 :: rest} =
      some (pr7Newpart1Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 22) : rest.length + j < 1024 := by omega
  simp [hz, hzn, pr7Newpart1Program, pr7Newpart1Model, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, capacity]


def pr7Newpart2Program : List Instr :=
  [
  .push 1 160,
   .op .MLOAD,
   .push 1 128,
   .op .MLOAD,
   .push 2 1824,
   .op .MLOAD,
   .op (.Dup ⟨13, by decide⟩),
   .op (.Dup ⟨1, by decide⟩)]

def pr7Newpart2Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 : W) (rest : List W) : State :=
  let v0 : W := MachineState.readWord s.memory 160
  let v1 : W := MachineState.readWord s.memory 128
  let v2 : W := MachineState.readWord s.memory 1824
  {s with pc := N 8535, memory := s.memory, stack := v2 :: x10 :: v2 :: v1 :: v0 :: x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: rest}

theorem pr7Newpart2_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions pr7Newpart2Program {s with pc := N 8523, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: rest} =
      some (pr7Newpart2Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 22) : rest.length + j < 1024 := by omega
  have ha128 : (128 : W).toNat = 128 := rfl
  have hf128 := Monpro.activeWords_fix s 128 32 (by decide) (by norm_num) hact
  have ha160 : (160 : W).toNat = 160 := rfl
  have hf160 := Monpro.activeWords_fix s 160 32 (by decide) (by norm_num) hact
  have ha1824 : (1824 : W).toNat = 1824 := rfl
  have hf1824 := Monpro.activeWords_fix s 1824 32 (by decide) (by norm_num) hact
  simp [hz, hzn, pr7Newpart2Program, pr7Newpart2Model, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, capacity, ha128, hf128, ha160, hf160, ha1824, hf1824]


def pr7Newpart3Program : List Instr :=
  [
  .op (.Dup ⟨3, by decide⟩),
   .op .MULMOD,
   .op (.Swap ⟨1, by decide⟩),
   .op .MUL,
   .push 2 1792,
   .op .MLOAD,
   .op (.Swap ⟨5, by decide⟩),
   .op .ADD]

def pr7Newpart3Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 : W) (rest : List W) : State :=
  let v0 : W := UInt256.mulMod x3 x0 x1
  let v1 : W := x3 * x2
  let v2 : W := MachineState.readWord s.memory 1792
  let v3 : W := x7 + v1
  {s with pc := N 8545, memory := s.memory, stack := v3 :: v0 :: x4 :: x5 :: x6 :: v2 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: x18 :: x19 :: x20 :: x21 :: rest}

theorem pr7Newpart3_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions pr7Newpart3Program {s with pc := N 8535, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: x18 :: x19 :: x20 :: x21 :: rest} =
      some (pr7Newpart3Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 23) : rest.length + j < 1024 := by omega
  have ha1792 : (1792 : W).toNat = 1792 := rfl
  have hf1792 := Monpro.activeWords_fix s 1792 32 (by decide) (by norm_num) hact
  simp [hz, hzn, pr7Newpart3Program, pr7Newpart3Model, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, capacity, ha1792, hf1792]


def pr7Newpart4Program : List Instr :=
  [
  .op (.Swap ⟨2, by decide⟩),
   .op .ADD,
   .op (.Dup ⟨12, by decide⟩),
   .op (.Dup ⟨2, by decide⟩),
   .op (.Dup ⟨6, by decide⟩),
   .op .MULMOD,
   .op .ADD,
   .op (.Swap ⟨3, by decide⟩)]

def pr7Newpart4Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 : W) (rest : List W) : State :=
  let v0 : W := x3 + x1
  let v1 : W := UInt256.mulMod x5 x2 x13
  let v2 : W := v1 + v0
  {s with pc := N 8553, memory := s.memory, stack := x5 :: x2 :: x0 :: x4 :: v2 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: x18 :: x19 :: rest}

theorem pr7Newpart4_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions pr7Newpart4Program {s with pc := N 8545, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: x18 :: x19 :: rest} =
      some (pr7Newpart4Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 22) : rest.length + j < 1024 := by omega
  simp [hz, hzn, pr7Newpart4Program, pr7Newpart4Model, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, capacity]


def pr7Newpart5Program : List Instr :=
  [
  .op .MUL,
   .op .ADD,
   .op (.Dup ⟨11, by decide⟩),
   .op (.Dup ⟨10, by decide⟩),
   .op .MUL,
   .op .ADD,
   .op (.Dup ⟨4, by decide⟩),
   .op (.Dup ⟨2, by decide⟩)]

def pr7Newpart5Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 : W) (rest : List W) : State :=
  let v0 : W := x0 * x1
  let v1 : W := v0 + x2
  let v2 : W := x11 * x13
  let v3 : W := v2 + v1
  {s with pc := N 8561, memory := s.memory, stack := x3 :: x6 :: v3 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: x18 :: rest}

theorem pr7Newpart5_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions pr7Newpart5Program {s with pc := N 8553, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: x18 :: rest} =
      some (pr7Newpart5Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 19) : rest.length + j < 1024 := by omega
  simp [hz, hzn, pr7Newpart5Program, pr7Newpart5Model, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, capacity]


def pr7Newpart6Program : List Instr :=
  [
  .op .MUL,
   .op .ADD,
   .op (.Dup ⟨8, by decide⟩),
   .push 1 192,
   .op .MLOAD,
   .op .MUL,
   .op .ADD,
   .op (.Dup ⟨5, by decide⟩)]

def pr7Newpart6Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 : W) (rest : List W) : State :=
  let v0 : W := x0 * x1
  let v1 : W := v0 + x2
  let v2 : W := MachineState.readWord s.memory 192
  let v3 : W := v2 * x10
  let v4 : W := v3 + v1
  {s with pc := N 8570, memory := s.memory, stack := x7 :: v4 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: x18 :: rest}

theorem pr7Newpart6_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions pr7Newpart6Program {s with pc := N 8561, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: x18 :: rest} =
      some (pr7Newpart6Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 19) : rest.length + j < 1024 := by omega
  have ha192 : (192 : W).toNat = 192 := rfl
  have hf192 := Monpro.activeWords_fix s 192 32 (by decide) (by norm_num) hact
  simp [hz, hzn, pr7Newpart6Program, pr7Newpart6Model, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, capacity, ha192, hf192]


def pr7Newpart7Program : List Instr :=
  [
  .push 0 0,
   .op .MLOAD,
   .op .MUL,
   .op .ADD,
   .op (.Dup ⟨15, by decide⟩),
   .push 1 224,
   .op .MLOAD,
   .op .MUL]

def pr7Newpart7Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 : W) (rest : List W) : State :=
  let v0 : W := MachineState.readWord s.memory 0
  let v1 : W := v0 * x0
  let v2 : W := v1 + x1
  let v3 : W := MachineState.readWord s.memory 224
  let v4 : W := v3 * x16
  {s with pc := N 8579, memory := s.memory, stack := v4 :: v2 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: rest}

theorem pr7Newpart7_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions pr7Newpart7Program {s with pc := N 8570, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: rest} =
      some (pr7Newpart7Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 19) : rest.length + j < 1024 := by omega
  have ha0 : (0 : W).toNat = 0 := rfl
  have hf0 := Monpro.activeWords_fix s 0 32 (by decide) (by norm_num) hact
  have ha224 : (224 : W).toNat = 224 := rfl
  have hf224 := Monpro.activeWords_fix s 224 32 (by decide) (by norm_num) hact
  simp [hz, hzn, pr7Newpart7Program, pr7Newpart7Model, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, capacity, ha0, hf0, ha224, hf224]


def pr7Newpart8Program : List Instr :=
  [
  .op .ADD,
   .op (.Dup ⟨3, by decide⟩),
   .push 2 1216,
   .op .MLOAD,
   .op .MUL,
   .op .ADD,
   .op (.Dup ⟨12, by decide⟩),
   .push 2 1248,
   .op .MLOAD]

def pr7Newpart8Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 : W) (rest : List W) : State :=
  let v0 : W := x0 + x1
  let v1 : W := MachineState.readWord s.memory 1216
  let v2 : W := v1 * x4
  let v3 : W := v2 + v0
  let v4 : W := MachineState.readWord s.memory 1248
  {s with pc := N 8592, memory := s.memory, stack := v4 :: x13 :: v3 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: rest}

theorem pr7Newpart8_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions pr7Newpart8Program {s with pc := N 8579, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: rest} =
      some (pr7Newpart8Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 19) : rest.length + j < 1024 := by omega
  have ha1216 : (1216 : W).toNat = 1216 := rfl
  have hf1216 := Monpro.activeWords_fix s 1216 32 (by decide) (by norm_num) hact
  have ha1248 : (1248 : W).toNat = 1248 := rfl
  have hf1248 := Monpro.activeWords_fix s 1248 32 (by decide) (by norm_num) hact
  simp [hz, hzn, pr7Newpart8Program, pr7Newpart8Model, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, capacity, ha1216, hf1216, ha1248, hf1248]


def pr7Newpart9Program : List Instr :=
  [
  .op .MUL,
   .op .ADD,
   .op (.Swap ⟨1, by decide⟩),
   .op (.Dup ⟨10, by decide⟩),
   .op (.Dup ⟨12, by decide⟩),
   .op (.Dup ⟨11, by decide⟩),
   .op .MULMOD,
   .op .ADD]

def pr7Newpart9Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 : W) (rest : List W) : State :=
  let v0 : W := x0 * x1
  let v1 : W := v0 + x2
  let v2 : W := UInt256.mulMod x11 x13 x12
  let v3 : W := v2 + x4
  {s with pc := N 8600, memory := s.memory, stack := v3 :: x3 :: v1 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: x18 :: rest}

theorem pr7Newpart9_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions pr7Newpart9Program {s with pc := N 8592, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: x18 :: rest} =
      some (pr7Newpart9Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 20) : rest.length + j < 1024 := by omega
  simp [hz, hzn, pr7Newpart9Program, pr7Newpart9Model, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, capacity]


def pr7Newpart10Program : List Instr :=
  [
  .op (.Dup ⟨10, by decide⟩),
   .op (.Dup ⟨5, by decide⟩),
   .op (.Dup ⟨3, by decide⟩),
   .op .MULMOD,
   .op .ADD,
   .op (.Swap ⟨0, by decide⟩),
   .push 2 1088,
   .op .MSTORE]

def pr7Newpart10Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 : W) (rest : List W) : State :=
  let v0 : W := UInt256.mulMod x1 x4 x10
  let v1 : W := v0 + x0
  let v2 : ByteArray := MachineState.writeBytes s.memory (Data.Bytes.natToBytesPadded x1.toNat 32) 1088
  {s with pc := N 8610, memory := v2, stack := v1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: rest}

theorem pr7Newpart10_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions pr7Newpart10Program {s with pc := N 8600, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: rest} =
      some (pr7Newpart10Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 20) : rest.length + j < 1024 := by omega
  have ha1088 : (1088 : W).toNat = 1088 := rfl
  have hf1088 := Monpro.activeWords_fix s 1088 32 (by decide) (by norm_num) hact
  simp [hz, hzn, pr7Newpart10Program, pr7Newpart10Model, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, capacity, ha1088, hf1088]


def pr7Newpart11Program : List Instr :=
  [
  .op (.Dup ⟨9, by decide⟩),
   .op (.Dup ⟨8, by decide⟩),
   .push 1 192,
   .op .MLOAD,
   .op .MULMOD,
   .op .ADD,
   .op (.Dup ⟨9, by decide⟩),
   .op (.Dup ⟨5, by decide⟩)]

def pr7Newpart11Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 : W) (rest : List W) : State :=
  let v0 : W := MachineState.readWord s.memory 192
  let v1 : W := UInt256.mulMod v0 x7 x9
  let v2 : W := v1 + x0
  {s with pc := N 8619, memory := s.memory, stack := x4 :: x9 :: v2 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: rest}

theorem pr7Newpart11_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions pr7Newpart11Program {s with pc := N 8610, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: rest} =
      some (pr7Newpart11Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 19) : rest.length + j < 1024 := by omega
  have ha192 : (192 : W).toNat = 192 := rfl
  have hf192 := Monpro.activeWords_fix s 192 32 (by decide) (by norm_num) hact
  simp [hz, hzn, pr7Newpart11Program, pr7Newpart11Model, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, capacity, ha192, hf192]


def pr7Newpart12Program : List Instr :=
  [
  .push 0 0,
   .op .MLOAD,
   .op .MULMOD,
   .op .ADD,
   .op (.Dup ⟨9, by decide⟩),
   .op (.Dup ⟨15, by decide⟩),
   .push 1 224,
   .op .MLOAD]

def pr7Newpart12Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 : W) (rest : List W) : State :=
  let v0 : W := MachineState.readWord s.memory 0
  let v1 : W := UInt256.mulMod v0 x0 x1
  let v2 : W := v1 + x2
  let v3 : W := MachineState.readWord s.memory 224
  {s with pc := N 8628, memory := s.memory, stack := v3 :: x16 :: x11 :: v2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: rest}

theorem pr7Newpart12_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions pr7Newpart12Program {s with pc := N 8619, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: rest} =
      some (pr7Newpart12Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 19) : rest.length + j < 1024 := by omega
  have ha0 : (0 : W).toNat = 0 := rfl
  have hf0 := Monpro.activeWords_fix s 0 32 (by decide) (by norm_num) hact
  have ha224 : (224 : W).toNat = 224 := rfl
  have hf224 := Monpro.activeWords_fix s 224 32 (by decide) (by norm_num) hact
  simp [hz, hzn, pr7Newpart12Program, pr7Newpart12Model, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, capacity, ha0, hf0, ha224, hf224]


def pr7Newpart13Program : List Instr :=
  [
  .op .MULMOD,
   .op .ADD,
   .op (.Dup ⟨9, by decide⟩)]

def pr7Newpart13Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 : W) (rest : List W) : State :=
  let v0 : W := UInt256.mulMod x0 x1 x2
  let v1 : W := v0 + x3
  {s with pc := N 8631, memory := s.memory, stack := x12 :: v1 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: x18 :: rest}

theorem pr7Newpart13_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions pr7Newpart13Program {s with pc := N 8628, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: x18 :: rest} =
      some (pr7Newpart13Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 19) : rest.length + j < 1024 := by omega
  simp [hz, hzn, pr7Newpart13Program, pr7Newpart13Model, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, capacity]


def pr7NewProgram : List Instr :=
  [
  .op (.Swap ⟨4, by decide⟩),
   .op .MULMOD,
   .op .ADD,
   .op (.Dup ⟨10, by decide⟩),
   .push 1 96,
   .op .MLOAD,
   .push 2 1856,
   .op .MLOAD,
   .op (.Swap ⟨4, by decide⟩),
   .op (.Dup ⟨1, by decide⟩),
   .op (.Dup ⟨6, by decide⟩),
   .op .MUL,
   .op .ADD,
   .op (.Swap ⟨4, by decide⟩),
   .op .MULMOD,
   .op .ADD,
   .push 1 160,
   .op .MLOAD,
   .push 1 128,
   .op .MLOAD,
   .push 2 1824,
   .op .MLOAD,
   .op (.Dup ⟨13, by decide⟩),
   .op (.Dup ⟨1, by decide⟩),
   .op (.Dup ⟨3, by decide⟩),
   .op .MULMOD,
   .op (.Swap ⟨1, by decide⟩),
   .op .MUL,
   .push 2 1792,
   .op .MLOAD,
   .op (.Swap ⟨5, by decide⟩),
   .op .ADD,
   .op (.Swap ⟨2, by decide⟩),
   .op .ADD,
   .op (.Dup ⟨12, by decide⟩),
   .op (.Dup ⟨2, by decide⟩),
   .op (.Dup ⟨6, by decide⟩),
   .op .MULMOD,
   .op .ADD,
   .op (.Swap ⟨3, by decide⟩),
   .op .MUL,
   .op .ADD,
   .op (.Dup ⟨11, by decide⟩),
   .op (.Dup ⟨10, by decide⟩),
   .op .MUL,
   .op .ADD,
   .op (.Dup ⟨4, by decide⟩),
   .op (.Dup ⟨2, by decide⟩),
   .op .MUL,
   .op .ADD,
   .op (.Dup ⟨8, by decide⟩),
   .push 1 192,
   .op .MLOAD,
   .op .MUL,
   .op .ADD,
   .op (.Dup ⟨5, by decide⟩),
   .push 0 0,
   .op .MLOAD,
   .op .MUL,
   .op .ADD,
   .op (.Dup ⟨15, by decide⟩),
   .push 1 224,
   .op .MLOAD,
   .op .MUL,
   .op .ADD,
   .op (.Dup ⟨3, by decide⟩),
   .push 2 1216,
   .op .MLOAD,
   .op .MUL,
   .op .ADD,
   .op (.Dup ⟨12, by decide⟩),
   .push 2 1248,
   .op .MLOAD,
   .op .MUL,
   .op .ADD,
   .op (.Swap ⟨1, by decide⟩),
   .op (.Dup ⟨10, by decide⟩),
   .op (.Dup ⟨12, by decide⟩),
   .op (.Dup ⟨11, by decide⟩),
   .op .MULMOD,
   .op .ADD,
   .op (.Dup ⟨10, by decide⟩),
   .op (.Dup ⟨5, by decide⟩),
   .op (.Dup ⟨3, by decide⟩),
   .op .MULMOD,
   .op .ADD,
   .op (.Swap ⟨0, by decide⟩),
   .push 2 1088,
   .op .MSTORE,
   .op (.Dup ⟨9, by decide⟩),
   .op (.Dup ⟨8, by decide⟩),
   .push 1 192,
   .op .MLOAD,
   .op .MULMOD,
   .op .ADD,
   .op (.Dup ⟨9, by decide⟩),
   .op (.Dup ⟨5, by decide⟩),
   .push 0 0,
   .op .MLOAD,
   .op .MULMOD,
   .op .ADD,
   .op (.Dup ⟨9, by decide⟩),
   .op (.Dup ⟨15, by decide⟩),
   .push 1 224,
   .op .MLOAD,
   .op .MULMOD,
   .op .ADD,
   .op (.Dup ⟨9, by decide⟩)]

def pr7NewModel (s : State) (carry w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 : W) (rest : List W) : State :=
  let v0 : W := UInt256.mulMod w4 w0 w1
  let v1 : W := v0 + w2
  let v2 : W := MachineState.readWord s.memory 96
  let v3 : W := MachineState.readWord s.memory 1856
  let v4 : W := v3 * v2
  let v5 : W := v4 + carry
  let v6 : W := UInt256.mulMod v3 v2 w12
  let v7 : W := v6 + v1
  let v8 : W := MachineState.readWord s.memory 160
  let v9 : W := MachineState.readWord s.memory 128
  let v10 : W := MachineState.readWord s.memory 1824
  let v11 : W := UInt256.mulMod v9 v10 w12
  let v12 : W := v9 * v10
  let v13 : W := MachineState.readWord s.memory 1792
  let v14 : W := v5 + v12
  let v15 : W := v7 + v11
  let v16 : W := UInt256.mulMod v13 v8 w12
  let v17 : W := v16 + v15
  let v18 : W := v13 * v8
  let v19 : W := v18 + v14
  let v20 : W := w11 * w13
  let v21 : W := v20 + v19
  let v22 : W := w3 * w6
  let v23 : W := v22 + v21
  let v24 : W := MachineState.readWord s.memory 192
  let v25 : W := v24 * w10
  let v26 : W := v25 + v23
  let v27 : W := MachineState.readWord s.memory 0
  let v28 : W := v27 * w7
  let v29 : W := v28 + v26
  let v30 : W := MachineState.readWord s.memory 224
  let v31 : W := v30 * w17
  let v32 : W := v31 + v29
  let v33 : W := MachineState.readWord s.memory 1216
  let v34 : W := v33 * w5
  let v35 : W := v34 + v32
  let v36 : W := MachineState.readWord s.memory 1248
  let v37 : W := v36 * w14
  let v38 : W := v37 + v35
  let v39 : W := UInt256.mulMod w11 w13 w12
  let v40 : W := v39 + v17
  let v41 : W := UInt256.mulMod w3 w6 w12
  let v42 : W := v41 + v40
  let v43 : ByteArray := MachineState.writeBytes s.memory (Data.Bytes.natToBytesPadded w3.toNat 32) 1088
  let v44 : W := MachineState.readWord v43 192
  let v45 : W := UInt256.mulMod v44 w10 w12
  let v46 : W := v45 + v42
  let v47 : W := MachineState.readWord v43 0
  let v48 : W := UInt256.mulMod v47 w7 w12
  let v49 : W := v48 + v46
  let v50 : W := MachineState.readWord v43 224
  let v51 : W := UInt256.mulMod v50 w17 w12
  let v52 : W := v51 + v49
  {s with pc := N 8631, memory := v43, stack := w12 :: v52 :: v38 :: w5 :: w6 :: w7 :: w8 :: w9 :: w10 :: w11 :: w12 :: w13 :: w14 :: w15 :: w16 :: w17 :: w18 :: rest}

theorem pr7New_run (s : State) (carry w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions pr7NewProgram {s with pc := N 8504, stack := carry :: w0 :: w1 :: w2 :: w3 :: w4 :: w5 :: w6 :: w7 :: w8 :: w9 :: w10 :: w11 :: w12 :: w13 :: w14 :: w15 :: w16 :: w17 :: w18 :: rest} =
      some (pr7NewModel s carry w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 rest) := by
  let v0 : W := UInt256.mulMod w4 w0 w1
  let v1 : W := v0 + w2
  let v2 : W := MachineState.readWord s.memory 96
  let v3 : W := MachineState.readWord s.memory 1856
  let v4 : W := v3 * v2
  let v5 : W := v4 + carry
  let v6 : W := UInt256.mulMod v3 v2 w12
  let v7 : W := v6 + v1
  let v8 : W := MachineState.readWord s.memory 160
  let v9 : W := MachineState.readWord s.memory 128
  let v10 : W := MachineState.readWord s.memory 1824
  let v11 : W := UInt256.mulMod v9 v10 w12
  let v12 : W := v9 * v10
  let v13 : W := MachineState.readWord s.memory 1792
  let v14 : W := v5 + v12
  let v15 : W := v7 + v11
  let v16 : W := UInt256.mulMod v13 v8 w12
  let v17 : W := v16 + v15
  let v18 : W := v13 * v8
  let v19 : W := v18 + v14
  let v20 : W := w11 * w13
  let v21 : W := v20 + v19
  let v22 : W := w3 * w6
  let v23 : W := v22 + v21
  let v24 : W := MachineState.readWord s.memory 192
  let v25 : W := v24 * w10
  let v26 : W := v25 + v23
  let v27 : W := MachineState.readWord s.memory 0
  let v28 : W := v27 * w7
  let v29 : W := v28 + v26
  let v30 : W := MachineState.readWord s.memory 224
  let v31 : W := v30 * w17
  let v32 : W := v31 + v29
  let v33 : W := MachineState.readWord s.memory 1216
  let v34 : W := v33 * w5
  let v35 : W := v34 + v32
  let v36 : W := MachineState.readWord s.memory 1248
  let v37 : W := v36 * w14
  let v38 : W := v37 + v35
  let v39 : W := UInt256.mulMod w11 w13 w12
  let v40 : W := v39 + v17
  let v41 : W := UInt256.mulMod w3 w6 w12
  let v42 : W := v41 + v40
  let v43 : ByteArray := MachineState.writeBytes s.memory (Data.Bytes.natToBytesPadded w3.toNat 32) 1088
  let v44 : W := MachineState.readWord v43 192
  let v45 : W := UInt256.mulMod v44 w10 w12
  let v46 : W := v45 + v42
  let v47 : W := MachineState.readWord v43 0
  let v48 : W := UInt256.mulMod v47 w7 w12
  let v49 : W := v48 + v46
  let v50 : W := MachineState.readWord v43 224
  let v51 : W := UInt256.mulMod v50 w17 w12
  let v52 : W := v51 + v49
  have h0 : runInstructions pr7Newpart0Program {s with pc := N 8504, memory := s.memory, stack := carry :: w0 :: w1 :: w2 :: w3 :: w4 :: w5 :: w6 :: w7 :: w8 :: w9 :: w10 :: w11 :: w12 :: w13 :: w14 :: w15 :: w16 :: w17 :: w18 :: rest} = some {s with pc := N 8515, memory := s.memory, stack := v3 :: v2 :: w12 :: v1 :: w3 :: carry :: w5 :: w6 :: w7 :: w8 :: w9 :: w10 :: w11 :: w12 :: w13 :: w14 :: w15 :: w16 :: w17 :: w18 :: rest} := by
    simpa only [pr7Newpart0Model, v0, v1, v2, v3] using pr7Newpart0_run (s) (carry) (w0) (w1) (w2) (w3) (w4) (w5) (w6) (w7) (w8) (w9) (w10) (w11) (w12) (w13) (w14) (w15) (w16) (w17) (w18) rest hcap hact
  have h1 : runInstructions pr7Newpart1Program {s with pc := N 8515, memory := s.memory, stack := v3 :: v2 :: w12 :: v1 :: w3 :: carry :: w5 :: w6 :: w7 :: w8 :: w9 :: w10 :: w11 :: w12 :: w13 :: w14 :: w15 :: w16 :: w17 :: w18 :: rest} = some {s with pc := N 8523, memory := s.memory, stack := v7 :: w3 :: v5 :: w5 :: w6 :: w7 :: w8 :: w9 :: w10 :: w11 :: w12 :: w13 :: w14 :: w15 :: w16 :: w17 :: w18 :: rest} := by
    simpa only [pr7Newpart1Model, v4, v5, v6, v7] using pr7Newpart1_run (s) (v3) (v2) (w12) (v1) (w3) (carry) (w5) (w6) (w7) (w8) (w9) (w10) (w11) (w12) (w13) (w14) (w15) (w16) (w17) (w18) rest hcap hact
  have h2 : runInstructions pr7Newpart2Program {s with pc := N 8523, memory := s.memory, stack := v7 :: w3 :: v5 :: w5 :: w6 :: w7 :: w8 :: w9 :: w10 :: w11 :: w12 :: w13 :: w14 :: w15 :: w16 :: w17 :: w18 :: rest} = some {s with pc := N 8535, memory := s.memory, stack := v10 :: w12 :: v10 :: v9 :: v8 :: v7 :: w3 :: v5 :: w5 :: w6 :: w7 :: w8 :: w9 :: w10 :: w11 :: w12 :: w13 :: w14 :: w15 :: w16 :: w17 :: w18 :: rest} := by
    simpa only [pr7Newpart2Model, v8, v9, v10] using pr7Newpart2_run (s) (v7) (w3) (v5) (w5) (w6) (w7) (w8) (w9) (w10) (w11) (w12) (w13) (w14) (w15) (w16) (w17) (w18) rest hcap hact
  have h3 : runInstructions pr7Newpart3Program {s with pc := N 8535, memory := s.memory, stack := v10 :: w12 :: v10 :: v9 :: v8 :: v7 :: w3 :: v5 :: w5 :: w6 :: w7 :: w8 :: w9 :: w10 :: w11 :: w12 :: w13 :: w14 :: w15 :: w16 :: w17 :: w18 :: rest} = some {s with pc := N 8545, memory := s.memory, stack := v14 :: v11 :: v8 :: v7 :: w3 :: v13 :: w5 :: w6 :: w7 :: w8 :: w9 :: w10 :: w11 :: w12 :: w13 :: w14 :: w15 :: w16 :: w17 :: w18 :: rest} := by
    simpa only [pr7Newpart3Model, v11, v12, v13, v14] using pr7Newpart3_run (s) (v10) (w12) (v10) (v9) (v8) (v7) (w3) (v5) (w5) (w6) (w7) (w8) (w9) (w10) (w11) (w12) (w13) (w14) (w15) (w16) (w17) (w18) rest hcap hact
  have h4 : runInstructions pr7Newpart4Program {s with pc := N 8545, memory := s.memory, stack := v14 :: v11 :: v8 :: v7 :: w3 :: v13 :: w5 :: w6 :: w7 :: w8 :: w9 :: w10 :: w11 :: w12 :: w13 :: w14 :: w15 :: w16 :: w17 :: w18 :: rest} = some {s with pc := N 8553, memory := s.memory, stack := v13 :: v8 :: v14 :: w3 :: v17 :: w5 :: w6 :: w7 :: w8 :: w9 :: w10 :: w11 :: w12 :: w13 :: w14 :: w15 :: w16 :: w17 :: w18 :: rest} := by
    simpa only [pr7Newpart4Model, v15, v16, v17] using pr7Newpart4_run (s) (v14) (v11) (v8) (v7) (w3) (v13) (w5) (w6) (w7) (w8) (w9) (w10) (w11) (w12) (w13) (w14) (w15) (w16) (w17) (w18) rest hcap hact
  have h5 : runInstructions pr7Newpart5Program {s with pc := N 8553, memory := s.memory, stack := v13 :: v8 :: v14 :: w3 :: v17 :: w5 :: w6 :: w7 :: w8 :: w9 :: w10 :: w11 :: w12 :: w13 :: w14 :: w15 :: w16 :: w17 :: w18 :: rest} = some {s with pc := N 8561, memory := s.memory, stack := w3 :: w6 :: v21 :: w3 :: v17 :: w5 :: w6 :: w7 :: w8 :: w9 :: w10 :: w11 :: w12 :: w13 :: w14 :: w15 :: w16 :: w17 :: w18 :: rest} := by
    simpa only [pr7Newpart5Model, v18, v19, v20, v21] using pr7Newpart5_run (s) (v13) (v8) (v14) (w3) (v17) (w5) (w6) (w7) (w8) (w9) (w10) (w11) (w12) (w13) (w14) (w15) (w16) (w17) (w18) rest hcap hact
  have h6 : runInstructions pr7Newpart6Program {s with pc := N 8561, memory := s.memory, stack := w3 :: w6 :: v21 :: w3 :: v17 :: w5 :: w6 :: w7 :: w8 :: w9 :: w10 :: w11 :: w12 :: w13 :: w14 :: w15 :: w16 :: w17 :: w18 :: rest} = some {s with pc := N 8570, memory := s.memory, stack := w7 :: v26 :: w3 :: v17 :: w5 :: w6 :: w7 :: w8 :: w9 :: w10 :: w11 :: w12 :: w13 :: w14 :: w15 :: w16 :: w17 :: w18 :: rest} := by
    simpa only [pr7Newpart6Model, v22, v23, v24, v25, v26] using pr7Newpart6_run (s) (w3) (w6) (v21) (w3) (v17) (w5) (w6) (w7) (w8) (w9) (w10) (w11) (w12) (w13) (w14) (w15) (w16) (w17) (w18) rest hcap hact
  have h7 : runInstructions pr7Newpart7Program {s with pc := N 8570, memory := s.memory, stack := w7 :: v26 :: w3 :: v17 :: w5 :: w6 :: w7 :: w8 :: w9 :: w10 :: w11 :: w12 :: w13 :: w14 :: w15 :: w16 :: w17 :: w18 :: rest} = some {s with pc := N 8579, memory := s.memory, stack := v31 :: v29 :: w3 :: v17 :: w5 :: w6 :: w7 :: w8 :: w9 :: w10 :: w11 :: w12 :: w13 :: w14 :: w15 :: w16 :: w17 :: w18 :: rest} := by
    simpa only [pr7Newpart7Model, v27, v28, v29, v30, v31] using pr7Newpart7_run (s) (w7) (v26) (w3) (v17) (w5) (w6) (w7) (w8) (w9) (w10) (w11) (w12) (w13) (w14) (w15) (w16) (w17) (w18) rest hcap hact
  have h8 : runInstructions pr7Newpart8Program {s with pc := N 8579, memory := s.memory, stack := v31 :: v29 :: w3 :: v17 :: w5 :: w6 :: w7 :: w8 :: w9 :: w10 :: w11 :: w12 :: w13 :: w14 :: w15 :: w16 :: w17 :: w18 :: rest} = some {s with pc := N 8592, memory := s.memory, stack := v36 :: w14 :: v35 :: w3 :: v17 :: w5 :: w6 :: w7 :: w8 :: w9 :: w10 :: w11 :: w12 :: w13 :: w14 :: w15 :: w16 :: w17 :: w18 :: rest} := by
    simpa only [pr7Newpart8Model, v32, v33, v34, v35, v36] using pr7Newpart8_run (s) (v31) (v29) (w3) (v17) (w5) (w6) (w7) (w8) (w9) (w10) (w11) (w12) (w13) (w14) (w15) (w16) (w17) (w18) rest hcap hact
  have h9 : runInstructions pr7Newpart9Program {s with pc := N 8592, memory := s.memory, stack := v36 :: w14 :: v35 :: w3 :: v17 :: w5 :: w6 :: w7 :: w8 :: w9 :: w10 :: w11 :: w12 :: w13 :: w14 :: w15 :: w16 :: w17 :: w18 :: rest} = some {s with pc := N 8600, memory := s.memory, stack := v40 :: w3 :: v38 :: w5 :: w6 :: w7 :: w8 :: w9 :: w10 :: w11 :: w12 :: w13 :: w14 :: w15 :: w16 :: w17 :: w18 :: rest} := by
    simpa only [pr7Newpart9Model, v37, v38, v39, v40] using pr7Newpart9_run (s) (v36) (w14) (v35) (w3) (v17) (w5) (w6) (w7) (w8) (w9) (w10) (w11) (w12) (w13) (w14) (w15) (w16) (w17) (w18) rest hcap hact
  have h10 : runInstructions pr7Newpart10Program {s with pc := N 8600, memory := s.memory, stack := v40 :: w3 :: v38 :: w5 :: w6 :: w7 :: w8 :: w9 :: w10 :: w11 :: w12 :: w13 :: w14 :: w15 :: w16 :: w17 :: w18 :: rest} = some {s with pc := N 8610, memory := v43, stack := v42 :: v38 :: w5 :: w6 :: w7 :: w8 :: w9 :: w10 :: w11 :: w12 :: w13 :: w14 :: w15 :: w16 :: w17 :: w18 :: rest} := by
    simpa only [pr7Newpart10Model, v41, v42, v43] using pr7Newpart10_run (s) (v40) (w3) (v38) (w5) (w6) (w7) (w8) (w9) (w10) (w11) (w12) (w13) (w14) (w15) (w16) (w17) (w18) rest hcap hact
  have h11 : runInstructions pr7Newpart11Program {s with pc := N 8610, memory := v43, stack := v42 :: v38 :: w5 :: w6 :: w7 :: w8 :: w9 :: w10 :: w11 :: w12 :: w13 :: w14 :: w15 :: w16 :: w17 :: w18 :: rest} = some {s with pc := N 8619, memory := v43, stack := w7 :: w12 :: v46 :: v38 :: w5 :: w6 :: w7 :: w8 :: w9 :: w10 :: w11 :: w12 :: w13 :: w14 :: w15 :: w16 :: w17 :: w18 :: rest} := by
    simpa only [pr7Newpart11Model, v44, v45, v46] using pr7Newpart11_run ({s with memory := v43}) (v42) (v38) (w5) (w6) (w7) (w8) (w9) (w10) (w11) (w12) (w13) (w14) (w15) (w16) (w17) (w18) rest hcap hact
  have h12 : runInstructions pr7Newpart12Program {s with pc := N 8619, memory := v43, stack := w7 :: w12 :: v46 :: v38 :: w5 :: w6 :: w7 :: w8 :: w9 :: w10 :: w11 :: w12 :: w13 :: w14 :: w15 :: w16 :: w17 :: w18 :: rest} = some {s with pc := N 8628, memory := v43, stack := v50 :: w17 :: w12 :: v49 :: v38 :: w5 :: w6 :: w7 :: w8 :: w9 :: w10 :: w11 :: w12 :: w13 :: w14 :: w15 :: w16 :: w17 :: w18 :: rest} := by
    simpa only [pr7Newpart12Model, v47, v48, v49, v50] using pr7Newpart12_run ({s with memory := v43}) (w7) (w12) (v46) (v38) (w5) (w6) (w7) (w8) (w9) (w10) (w11) (w12) (w13) (w14) (w15) (w16) (w17) (w18) rest hcap hact
  have h13 : runInstructions pr7Newpart13Program {s with pc := N 8628, memory := v43, stack := v50 :: w17 :: w12 :: v49 :: v38 :: w5 :: w6 :: w7 :: w8 :: w9 :: w10 :: w11 :: w12 :: w13 :: w14 :: w15 :: w16 :: w17 :: w18 :: rest} = some {s with pc := N 8631, memory := v43, stack := w12 :: v52 :: v38 :: w5 :: w6 :: w7 :: w8 :: w9 :: w10 :: w11 :: w12 :: w13 :: w14 :: w15 :: w16 :: w17 :: w18 :: rest} := by
    simpa only [pr7Newpart13Model, v51, v52] using pr7Newpart13_run ({s with memory := v43}) (v50) (w17) (w12) (v49) (v38) (w5) (w6) (w7) (w8) (w9) (w10) (w11) (w12) (w13) (w14) (w15) (w16) (w17) (w18) rest hcap hact
  exact (runInstructions_append_some _ _ _ _ _ h0 (runInstructions_append_some _ _ _ _ _ h1 (runInstructions_append_some _ _ _ _ _ h2 (runInstructions_append_some _ _ _ _ _ h3 (runInstructions_append_some _ _ _ _ _ h4 (runInstructions_append_some _ _ _ _ _ h5 (runInstructions_append_some _ _ _ _ _ h6 (runInstructions_append_some _ _ _ _ _ h7 (runInstructions_append_some _ _ _ _ _ h8 (runInstructions_append_some _ _ _ _ _ h9 (runInstructions_append_some _ _ _ _ _ h10 (runInstructions_append_some _ _ _ _ _ h11 (runInstructions_append_some _ _ _ _ _ h12 h13)))))))))))))

#print axioms pr7New_run

def productColumn7Model (s : State) (carry w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 : W) (rest : List W) : State :=
  let v0 : W := UInt256.mulMod w4 w0 w1
  let v1 : W := v0 + w2
  let v2 : W := MachineState.readWord s.memory 96
  let v3 : W := MachineState.readWord s.memory 1856
  let v4 : W := v3 * v2
  let v5 : W := v4 + carry
  let v6 : W := UInt256.mulMod v3 v2 w12
  let v7 : W := v6 + v1
  let v8 : W := MachineState.readWord s.memory 128
  let v9 : W := MachineState.readWord s.memory 1824
  let v10 : W := v9 * v8
  let v11 : W := v10 + v5
  let v12 : W := UInt256.mulMod v9 v8 w12
  let v13 : W := v12 + v7
  let v14 : W := MachineState.readWord s.memory 160
  let v15 : W := MachineState.readWord s.memory 1792
  let v16 : W := v15 * v14
  let v17 : W := v16 + v11
  let v18 : W := UInt256.mulMod v15 v14 w12
  let v19 : W := v18 + v13
  let v20 : W := w11 * w13
  let v21 : W := v20 + v17
  let v22 : W := w3 * w6
  let v23 : W := v22 + v21
  let v24 : W := MachineState.readWord s.memory 192
  let v25 : W := v24 * w10
  let v26 : W := v25 + v23
  let v27 : W := MachineState.readWord s.memory 0
  let v28 : W := v27 * w7
  let v29 : W := v28 + v26
  let v30 : W := MachineState.readWord s.memory 224
  let v31 : W := v30 * w17
  let v32 : W := v31 + v29
  let v33 : W := MachineState.readWord s.memory 1216
  let v34 : W := v33 * w5
  let v35 : W := v34 + v32
  let v36 : W := MachineState.readWord s.memory 1248
  let v37 : W := v36 * w14
  let v38 : W := v37 + v35
  let v39 : W := UInt256.mulMod w11 w13 w12
  let v40 : W := v39 + v19
  let v41 : W := UInt256.mulMod w3 w6 w12
  let v42 : W := v41 + v40
  let v43 : ByteArray := MachineState.writeBytes s.memory (Data.Bytes.natToBytesPadded w3.toNat 32) 1088
  let v44 : W := MachineState.readWord v43 192
  let v45 : W := UInt256.mulMod v44 w10 w12
  let v46 : W := v45 + v42
  let v47 : W := MachineState.readWord v43 0
  let v48 : W := UInt256.mulMod v47 w7 w12
  let v49 : W := v48 + v46
  let v50 : W := MachineState.readWord v43 224
  let v51 : W := UInt256.mulMod v50 w17 w12
  let v52 : W := v51 + v49
  {s with pc := N 8631, memory := v43, stack := w12 :: v52 :: v38 :: w5 :: w6 :: w7 :: w8 :: w9 :: w10 :: w11 :: w12 :: w13 :: w14 :: w15 :: w16 :: w17 :: w18 :: rest}

def productColumn7Program : List Instr := pr7NewProgram

private theorem aux_shared0 (s : State) (w3 : W) :
    (MachineState.readWord (MachineState.writeBytes s.memory (Data.Bytes.natToBytesPadded w3.toNat 32) 1088) 192) = (MachineState.readWord s.memory 192) := by
  simp (disch := decide) only [addC, addA, addL, mulC, mmC, amC, andC, orC, xorC, eqC, read_disjoint, Challenge.EvmProof.Memory.readWord_writeWord]

private theorem aux_shared1 (s : State) (w3 : W) :
    (MachineState.readWord (MachineState.writeBytes s.memory (Data.Bytes.natToBytesPadded w3.toNat 32) 1088) 0) = (MachineState.readWord s.memory 0) := by
  simp (disch := decide) only [addC, addA, addL, mulC, mmC, amC, andC, orC, xorC, eqC, read_disjoint, Challenge.EvmProof.Memory.readWord_writeWord]

private theorem aux_shared2 (s : State) (w3 : W) :
    (MachineState.readWord (MachineState.writeBytes s.memory (Data.Bytes.natToBytesPadded w3.toNat 32) 1088) 224) = (MachineState.readWord s.memory 224) := by
  simp (disch := decide) only [addC, addA, addL, mulC, mmC, amC, andC, orC, xorC, eqC, read_disjoint, Challenge.EvmProof.Memory.readWord_writeWord]

private theorem aux_shared3 (w12 : W) (z0 z1 : W) :
    (UInt256.mulMod z0 z1 w12) = (UInt256.mulMod z1 z0 w12) := by
  simp (disch := decide) only [addC, addA, addL, mulC, mmC, amC, andC, orC, xorC, eqC, read_disjoint, Challenge.EvmProof.Memory.readWord_writeWord]

private theorem aux_shared4 (z0 z1 : W) :
    (z0 * z1) = (z1 * z0) := by
  simp (disch := decide) only [addC, addA, addL, mulC, mmC, amC, andC, orC, xorC, eqC, read_disjoint, Challenge.EvmProof.Memory.readWord_writeWord]

private theorem aux_shared5 (z0 z1 : W) :
    (z0 + z1) = (z1 + z0) := by
  simp (disch := decide) only [addC, addA, addL, mulC, mmC, amC, andC, orC, xorC, eqC, read_disjoint, Challenge.EvmProof.Memory.readWord_writeWord]

private theorem prepared_model_eq (s : State) (carry w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 : W) (rest : List W) :
    productColumn7Model s carry w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 rest = pr7NewModel s carry w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 rest := by
  let o0 : W := UInt256.mulMod w4 w0 w1
  let o1 : W := o0 + w2
  let o2 : W := MachineState.readWord s.memory 96
  let o3 : W := MachineState.readWord s.memory 1856
  let o4 : W := o3 * o2
  let o5 : W := o4 + carry
  let o6 : W := UInt256.mulMod o3 o2 w12
  let o7 : W := o6 + o1
  let o8 : W := MachineState.readWord s.memory 128
  let o9 : W := MachineState.readWord s.memory 1824
  let o10 : W := o9 * o8
  let o11 : W := o10 + o5
  let o12 : W := UInt256.mulMod o9 o8 w12
  let o13 : W := o12 + o7
  let o14 : W := MachineState.readWord s.memory 160
  let o15 : W := MachineState.readWord s.memory 1792
  let o16 : W := o15 * o14
  let o17 : W := o16 + o11
  let o18 : W := UInt256.mulMod o15 o14 w12
  let o19 : W := o18 + o13
  let o20 : W := w11 * w13
  let o21 : W := o20 + o17
  let o22 : W := w3 * w6
  let o23 : W := o22 + o21
  let o24 : W := MachineState.readWord s.memory 192
  let o25 : W := o24 * w10
  let o26 : W := o25 + o23
  let o27 : W := MachineState.readWord s.memory 0
  let o28 : W := o27 * w7
  let o29 : W := o28 + o26
  let o30 : W := MachineState.readWord s.memory 224
  let o31 : W := o30 * w17
  let o32 : W := o31 + o29
  let o33 : W := MachineState.readWord s.memory 1216
  let o34 : W := o33 * w5
  let o35 : W := o34 + o32
  let o36 : W := MachineState.readWord s.memory 1248
  let o37 : W := o36 * w14
  let o38 : W := o37 + o35
  let o39 : W := UInt256.mulMod w11 w13 w12
  let o40 : W := o39 + o19
  let o41 : W := UInt256.mulMod w3 w6 w12
  let o42 : W := o41 + o40
  let o43 : ByteArray := MachineState.writeBytes s.memory (Data.Bytes.natToBytesPadded w3.toNat 32) 1088
  let o44 : W := MachineState.readWord o43 192
  let o45 : W := UInt256.mulMod o44 w10 w12
  let o46 : W := o45 + o42
  let o47 : W := MachineState.readWord o43 0
  let o48 : W := UInt256.mulMod o47 w7 w12
  let o49 : W := o48 + o46
  let o50 : W := MachineState.readWord o43 224
  let o51 : W := UInt256.mulMod o50 w17 w12
  let o52 : W := o51 + o49
  let n0 : W := UInt256.mulMod w4 w0 w1
  let n1 : W := n0 + w2
  let n2 : W := MachineState.readWord s.memory 96
  let n3 : W := MachineState.readWord s.memory 1856
  let n4 : W := n3 * n2
  let n5 : W := n4 + carry
  let n6 : W := UInt256.mulMod n3 n2 w12
  let n7 : W := n6 + n1
  let n8 : W := MachineState.readWord s.memory 160
  let n9 : W := MachineState.readWord s.memory 128
  let n10 : W := MachineState.readWord s.memory 1824
  let n11 : W := UInt256.mulMod n9 n10 w12
  let n12 : W := n9 * n10
  let n13 : W := MachineState.readWord s.memory 1792
  let n14 : W := n5 + n12
  let n15 : W := n7 + n11
  let n16 : W := UInt256.mulMod n13 n8 w12
  let n17 : W := n16 + n15
  let n18 : W := n13 * n8
  let n19 : W := n18 + n14
  let n20 : W := w11 * w13
  let n21 : W := n20 + n19
  let n22 : W := w3 * w6
  let n23 : W := n22 + n21
  let n24 : W := MachineState.readWord s.memory 192
  let n25 : W := n24 * w10
  let n26 : W := n25 + n23
  let n27 : W := MachineState.readWord s.memory 0
  let n28 : W := n27 * w7
  let n29 : W := n28 + n26
  let n30 : W := MachineState.readWord s.memory 224
  let n31 : W := n30 * w17
  let n32 : W := n31 + n29
  let n33 : W := MachineState.readWord s.memory 1216
  let n34 : W := n33 * w5
  let n35 : W := n34 + n32
  let n36 : W := MachineState.readWord s.memory 1248
  let n37 : W := n36 * w14
  let n38 : W := n37 + n35
  let n39 : W := UInt256.mulMod w11 w13 w12
  let n40 : W := n39 + n17
  let n41 : W := UInt256.mulMod w3 w6 w12
  let n42 : W := n41 + n40
  let n43 : ByteArray := MachineState.writeBytes s.memory (Data.Bytes.natToBytesPadded w3.toNat 32) 1088
  let n44 : W := MachineState.readWord n43 192
  let n45 : W := UInt256.mulMod n44 w10 w12
  let n46 : W := n45 + n42
  let n47 : W := MachineState.readWord n43 0
  let n48 : W := UInt256.mulMod n47 w7 w12
  let n49 : W := n48 + n46
  let n50 : W := MachineState.readWord n43 224
  let n51 : W := UInt256.mulMod n50 w17 w12
  let n52 : W := n51 + n49
  have eq_o44 : o44 = o24 := by
    simpa only [o44, o43, o24] using
      (aux_shared0 s w3 )
  have eq_o47 : o47 = o27 := by
    simpa only [o47, o43, o27] using
      (aux_shared1 s w3 )
  have eq_o50 : o50 = o30 := by
    simpa only [o50, o43, o30] using
      (aux_shared2 s w3 )
  have eq_n0 : n0 = o0 := by
    simp only [n0, o0]
  have eq_n1 : n1 = o1 := by
    simp only [n1, o1, eq_n0]
  have eq_n2 : n2 = o2 := by
    simp only [n2, o2]
  have eq_n3 : n3 = o3 := by
    simp only [n3, o3]
  have eq_n4 : n4 = o4 := by
    simp only [n4, o4, eq_n3, eq_n2]
  have eq_n5 : n5 = o5 := by
    simp only [n5, o5, eq_n4]
  have eq_n6 : n6 = o6 := by
    simp only [n6, o6, eq_n3, eq_n2]
  have eq_n7 : n7 = o7 := by
    simp only [n7, o7, eq_n6, eq_n1]
  have eq_n8 : n8 = o14 := by
    simp only [n8, o14]
  have eq_n9 : n9 = o8 := by
    simp only [n9, o8]
  have eq_n10 : n10 = o9 := by
    simp only [n10, o9]
  have eq_n11 : n11 = o12 := by
    simpa only [n11, o12, eq_n9, eq_n10] using
      (aux_shared3 w12 o8 o9)
  have eq_n12 : n12 = o10 := by
    simpa only [n12, o10, eq_n9, eq_n10] using
      (aux_shared4  o8 o9)
  have eq_n13 : n13 = o15 := by
    simp only [n13, o15]
  have eq_n14 : n14 = o11 := by
    simpa only [n14, o11, eq_n5, eq_n12] using
      (aux_shared5  o5 o10)
  have eq_n15 : n15 = o13 := by
    simpa only [n15, o13, eq_n7, eq_n11] using
      (aux_shared5  o7 o12)
  have eq_n16 : n16 = o18 := by
    simp only [n16, o18, eq_n13, eq_n8]
  have eq_n17 : n17 = o19 := by
    simp only [n17, o19, eq_n16, eq_n15]
  have eq_n18 : n18 = o16 := by
    simp only [n18, o16, eq_n13, eq_n8]
  have eq_n19 : n19 = o17 := by
    simp only [n19, o17, eq_n18, eq_n14]
  have eq_n20 : n20 = o20 := by
    simp only [n20, o20]
  have eq_n21 : n21 = o21 := by
    simp only [n21, o21, eq_n20, eq_n19]
  have eq_n22 : n22 = o22 := by
    simp only [n22, o22]
  have eq_n23 : n23 = o23 := by
    simp only [n23, o23, eq_n22, eq_n21]
  have eq_n24 : n24 = o24 := by
    simp only [n24, o24]
  have eq_n25 : n25 = o25 := by
    simp only [n25, o25, eq_n24]
  have eq_n26 : n26 = o26 := by
    simp only [n26, o26, eq_n25, eq_n23]
  have eq_n27 : n27 = o27 := by
    simp only [n27, o27]
  have eq_n28 : n28 = o28 := by
    simp only [n28, o28, eq_n27]
  have eq_n29 : n29 = o29 := by
    simp only [n29, o29, eq_n28, eq_n26]
  have eq_n30 : n30 = o30 := by
    simp only [n30, o30]
  have eq_n31 : n31 = o31 := by
    simp only [n31, o31, eq_n30]
  have eq_n32 : n32 = o32 := by
    simp only [n32, o32, eq_n31, eq_n29]
  have eq_n33 : n33 = o33 := by
    simp only [n33, o33]
  have eq_n34 : n34 = o34 := by
    simp only [n34, o34, eq_n33]
  have eq_n35 : n35 = o35 := by
    simp only [n35, o35, eq_n34, eq_n32]
  have eq_n36 : n36 = o36 := by
    simp only [n36, o36]
  have eq_n37 : n37 = o37 := by
    simp only [n37, o37, eq_n36]
  have eq_n38 : n38 = o38 := by
    simp only [n38, o38, eq_n37, eq_n35]
  have eq_n39 : n39 = o39 := by
    simp only [n39, o39]
  have eq_n40 : n40 = o40 := by
    simp only [n40, o40, eq_n39, eq_n17]
  have eq_n41 : n41 = o41 := by
    simp only [n41, o41]
  have eq_n42 : n42 = o42 := by
    simp only [n42, o42, eq_n41, eq_n40]
  have eq_n43 : n43 = o43 := by
    simp only [n43, o43]
  have eq_n44 : n44 = o24 := by
    simpa only [n44, n43, o24] using
      (aux_shared0 s w3 )
  have eq_n45 : n45 = o45 := by
    simp only [n45, o45, eq_n44, eq_o44]
  have eq_n46 : n46 = o46 := by
    simp only [n46, o46, eq_n45, eq_n42]
  have eq_n47 : n47 = o27 := by
    simpa only [n47, n43, o27] using
      (aux_shared1 s w3 )
  have eq_n48 : n48 = o48 := by
    simp only [n48, o48, eq_n47, eq_o47]
  have eq_n49 : n49 = o49 := by
    simp only [n49, o49, eq_n48, eq_n46]
  have eq_n50 : n50 = o30 := by
    simpa only [n50, n43, o30] using
      (aux_shared2 s w3 )
  have eq_n51 : n51 = o51 := by
    simp only [n51, o51, eq_n50, eq_o50]
  have eq_n52 : n52 = o52 := by
    simp only [n52, o52, eq_n51, eq_n49]
  change {s with pc := N 8631, memory := o43, stack := w12 :: o52 :: o38 :: w5 :: w6 :: w7 :: w8 :: w9 :: w10 :: w11 :: w12 :: w13 :: w14 :: w15 :: w16 :: w17 :: w18 :: rest} =
    {s with pc := N 8631, memory := n43, stack := w12 :: n52 :: n38 :: w5 :: w6 :: w7 :: w8 :: w9 :: w10 :: w11 :: w12 :: w13 :: w14 :: w15 :: w16 :: w17 :: w18 :: rest}
  simp only [eq_o44, eq_o47, eq_o50, eq_n0, eq_n1, eq_n2, eq_n3, eq_n4, eq_n5, eq_n6, eq_n7, eq_n8, eq_n9, eq_n10, eq_n11, eq_n12, eq_n13, eq_n14, eq_n15, eq_n16, eq_n17, eq_n18, eq_n19, eq_n20, eq_n21, eq_n22, eq_n23, eq_n24, eq_n25, eq_n26, eq_n27, eq_n28, eq_n29, eq_n30, eq_n31, eq_n32, eq_n33, eq_n34, eq_n35, eq_n36, eq_n37, eq_n38, eq_n39, eq_n40, eq_n41, eq_n42, eq_n43, eq_n44, eq_n45, eq_n46, eq_n47, eq_n48, eq_n49, eq_n50, eq_n51, eq_n52]
theorem productColumn7_run (s : State) (carry w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions productColumn7Program {s with pc := N 8504, stack := carry :: w0 :: w1 :: w2 :: w3 :: w4 :: w5 :: w6 :: w7 :: w8 :: w9 :: w10 :: w11 :: w12 :: w13 :: w14 :: w15 :: w16 :: w17 :: w18 :: rest} =
      some (productColumn7Model s carry w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 rest) := by
  exact (pr7New_run s carry w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 rest hcap hact).trans
    (congrArg some (prepared_model_eq s carry w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 rest).symm)

#print axioms productColumn7_run
end CycleSubmission.Execution
