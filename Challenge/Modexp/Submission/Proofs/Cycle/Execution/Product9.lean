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

def pr9Newpart0Program : List Instr :=
  [.op (.Dup dA5),
   .op .MUL,
   .op .ADD,
   .op (.Swap sA3),
   .op .MULMOD,
   .op .ADD,
   .op (.Dup dA9),
   .push 1 128,
   .op .MLOAD]

def pr9Newpart0Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 : W) (rest : List W) : State :=
  let v0 : W := x5 * x0
  let v1 : W := v0 + x1
  let v2 : W := UInt256.mulMod x5 x2 x3
  let v3 : W := v2 + x4
  let v4 : W := MachineState.readWord s.memory 128
  {s with pc := N 8953, memory := s.memory, stack := v4 :: x13 :: v3 :: v1 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: x18 :: x19 :: rest}

theorem pr9Newpart0_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions pr9Newpart0Program {s with pc := N 8943, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: x18 :: x19 :: rest} =
      some (pr9Newpart0Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 21) : rest.length + j < 1024 := by omega
  have ha128 : (128 : W).toNat = 128 := rfl
  have hf128 := Monpro.activeWords_fix s 128 32 (by decide) (by norm_num) hact
  simp [hz, hzn, pr9Newpart0Program, pr9Newpart0Model, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, capacity, ha128, hf128]


def pr9Newpart1Program : List Instr :=
  [.push 2 1856,
   .op .MLOAD,
   .op (.Swap sA3),
   .op (.Dup dA1),
   .op (.Dup dA5),
   .op .MUL,
   .op .ADD,
   .op (.Swap sA3)]

def pr9Newpart1Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 : W) (rest : List W) : State :=
  let v0 : W := MachineState.readWord s.memory 1856
  let v1 : W := v0 * x0
  let v2 : W := v1 + x3
  {s with pc := N 8963, memory := s.memory, stack := v0 :: x0 :: x1 :: x2 :: v2 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: rest}

theorem pr9Newpart1_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions pr9Newpart1Program {s with pc := N 8953, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: rest} =
      some (pr9Newpart1Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 21) : rest.length + j < 1024 := by omega
  have ha1856 : (1856 : W).toNat = 1856 := rfl
  have hf1856 := Monpro.activeWords_fix s 1856 32 (by decide) (by norm_num) hact
  simp [hz, hzn, pr9Newpart1Program, pr9Newpart1Model, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, capacity, ha1856, hf1856]


def pr9Newpart2Program : List Instr :=
  [.op .MULMOD,
   .op .ADD,
   .push 1 160,
   .op .MLOAD,
   .push 2 1824,
   .op .MLOAD,
   .op (.Dup dA11),
   .op (.Dup dA1)]

def pr9Newpart2Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 : W) (rest : List W) : State :=
  let v0 : W := UInt256.mulMod x0 x1 x2
  let v1 : W := v0 + x3
  let v2 : W := MachineState.readWord s.memory 160
  let v3 : W := MachineState.readWord s.memory 1824
  {s with pc := N 8974, memory := s.memory, stack := v3 :: x12 :: v3 :: v2 :: v1 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: x18 :: rest}

theorem pr9Newpart2_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions pr9Newpart2Program {s with pc := N 8963, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: x18 :: rest} =
      some (pr9Newpart2Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 20) : rest.length + j < 1024 := by omega
  have ha160 : (160 : W).toNat = 160 := rfl
  have hf160 := Monpro.activeWords_fix s 160 32 (by decide) (by norm_num) hact
  have ha1824 : (1824 : W).toNat = 1824 := rfl
  have hf1824 := Monpro.activeWords_fix s 1824 32 (by decide) (by norm_num) hact
  simp [hz, hzn, pr9Newpart2Program, pr9Newpart2Model, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, capacity, ha160, hf160, ha1824, hf1824]


def pr9Newpart3Program : List Instr :=
  [.op (.Dup dA3),
   .op .MULMOD,
   .op (.Swap sA1),
   .op .MUL,
   .push 2 1792,
   .op .MLOAD,
   .op (.Swap sA3),
   .op .ADD]

def pr9Newpart3Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 : W) (rest : List W) : State :=
  let v0 : W := UInt256.mulMod x3 x0 x1
  let v1 : W := x3 * x2
  let v2 : W := MachineState.readWord s.memory 1792
  let v3 : W := x5 + v1
  {s with pc := N 8984, memory := s.memory, stack := v3 :: v0 :: x4 :: v2 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: x18 :: x19 :: rest}

theorem pr9Newpart3_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions pr9Newpart3Program {s with pc := N 8974, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: x18 :: x19 :: rest} =
      some (pr9Newpart3Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 21) : rest.length + j < 1024 := by omega
  have ha1792 : (1792 : W).toNat = 1792 := rfl
  have hf1792 := Monpro.activeWords_fix s 1792 32 (by decide) (by norm_num) hact
  simp [hz, hzn, pr9Newpart3Program, pr9Newpart3Model, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, capacity, ha1792, hf1792]


def pr9Newpart4Program : List Instr :=
  [.op (.Swap sA1),
   .op .ADD,
   .op (.Dup dA10),
   .op (.Dup dA3),
   .op (.Dup dA5),
   .op .MULMOD,
   .op .ADD,
   .op (.Swap sA1)]

def pr9Newpart4Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 : W) (rest : List W) : State :=
  let v0 : W := x2 + x1
  let v1 : W := UInt256.mulMod x4 x3 x11
  let v2 : W := v1 + v0
  {s with pc := N 8992, memory := s.memory, stack := x3 :: x0 :: v2 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: rest}

theorem pr9Newpart4_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions pr9Newpart4Program {s with pc := N 8984, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: rest} =
      some (pr9Newpart4Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 20) : rest.length + j < 1024 := by omega
  simp [hz, hzn, pr9Newpart4Program, pr9Newpart4Model, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, capacity]


def pr9Newpart5Program : List Instr :=
  [.op (.Dup dA3),
   .op .MUL,
   .op .ADD,
   .push 2 1600,
   .op .MLOAD,
   .op (.Swap sA10),
   .op (.Dup dA11),
   .op (.Swap sA2)]

def pr9Newpart5Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 : W) (rest : List W) : State :=
  let v0 : W := x3 * x0
  let v1 : W := v0 + x1
  let v2 : W := MachineState.readWord s.memory 1600
  {s with pc := N 9002, memory := s.memory, stack := x2 :: x11 :: v1 :: v2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: v2 :: x12 :: x13 :: x14 :: x15 :: x16 :: rest}

theorem pr9Newpart5_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions pr9Newpart5Program {s with pc := N 8992, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: rest} =
      some (pr9Newpart5Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 18) : rest.length + j < 1024 := by omega
  have ha1600 : (1600 : W).toNat = 1600 := rfl
  have hf1600 := Monpro.activeWords_fix s 1600 32 (by decide) (by norm_num) hact
  simp [hz, hzn, pr9Newpart5Program, pr9Newpart5Model, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, capacity, ha1600, hf1600]


def pr9Newpart6Program : List Instr :=
  [.op (.Dup dA11),
   .op (.Dup dA2),
   .op (.Dup dA5),
   .op .MULMOD,
   .op .ADD,
   .op (.Swap sA2),
   .op .MUL,
   .op .ADD]

def pr9Newpart6Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 : W) (rest : List W) : State :=
  let v0 : W := UInt256.mulMod x3 x1 x11
  let v1 : W := v0 + x0
  let v2 : W := x3 * x1
  let v3 : W := v2 + x2
  {s with pc := N 9010, memory := s.memory, stack := v3 :: v1 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: rest}

theorem pr9Newpart6_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions pr9Newpart6Program {s with pc := N 9002, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: rest} =
      some (pr9Newpart6Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 21) : rest.length + j < 1024 := by omega
  simp [hz, hzn, pr9Newpart6Program, pr9Newpart6Model, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, capacity]


def pr9Newpart7Program : List Instr :=
  [.push 2 1088,
   .op .MLOAD,
   .op (.Dup dA9),
   .op .MUL,
   .op .ADD,
   .push 1 192,
   .op .MLOAD,
   .op (.Dup dA4)]

def pr9Newpart7Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 : W) (rest : List W) : State :=
  let v0 : W := MachineState.readWord s.memory 1088
  let v1 : W := x8 * v0
  let v2 : W := v1 + x0
  let v3 : W := MachineState.readWord s.memory 192
  {s with pc := N 9021, memory := s.memory, stack := x3 :: v3 :: v2 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: rest}

theorem pr9Newpart7_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions pr9Newpart7Program {s with pc := N 9010, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: rest} =
      some (pr9Newpart7Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 18) : rest.length + j < 1024 := by omega
  have ha192 : (192 : W).toNat = 192 := rfl
  have hf192 := Monpro.activeWords_fix s 192 32 (by decide) (by norm_num) hact
  have ha1088 : (1088 : W).toNat = 1088 := rfl
  have hf1088 := Monpro.activeWords_fix s 1088 32 (by decide) (by norm_num) hact
  simp [hz, hzn, pr9Newpart7Program, pr9Newpart7Model, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, capacity, ha192, hf192, ha1088, hf1088]


def pr9Newpart8Program : List Instr :=
  [.op .MUL,
   .op .ADD,
   .push 0 0,
   .op .MLOAD,
   .op (.Dup dA8),
   .op .MUL,
   .op .ADD,
   .push 1 224,
   .op .MLOAD]

def pr9Newpart8Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 : W) (rest : List W) : State :=
  let v0 : W := x0 * x1
  let v1 : W := v0 + x2
  let v2 : W := MachineState.readWord s.memory 0
  let v3 : W := x9 * v2
  let v4 : W := v3 + v1
  let v5 : W := MachineState.readWord s.memory 224
  {s with pc := N 9031, memory := s.memory, stack := v5 :: v4 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: rest}

theorem pr9Newpart8_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions pr9Newpart8Program {s with pc := N 9021, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: rest} =
      some (pr9Newpart8Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 18) : rest.length + j < 1024 := by omega
  have ha0 : (0 : W).toNat = 0 := rfl
  have hf0 := Monpro.activeWords_fix s 0 32 (by decide) (by norm_num) hact
  have ha224 : (224 : W).toNat = 224 := rfl
  have hf224 := Monpro.activeWords_fix s 224 32 (by decide) (by norm_num) hact
  simp [hz, hzn, pr9Newpart8Program, pr9Newpart8Model, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, capacity, ha0, hf0, ha224, hf224]


def pr9Newpart9Program : List Instr :=
  [.op (.Dup dA5),
   .op .MUL,
   .op .ADD,
   .push 2 1216,
   .op .MLOAD,
   .op (.Dup dA15),
   .op .MUL,
   .op .ADD]

def pr9Newpart9Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 : W) (rest : List W) : State :=
  let v0 : W := x5 * x0
  let v1 : W := v0 + x1
  let v2 : W := MachineState.readWord s.memory 1216
  let v3 : W := x15 * v2
  let v4 : W := v3 + v1
  {s with pc := N 9041, memory := s.memory, stack := v4 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: rest}

theorem pr9Newpart9_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions pr9Newpart9Program {s with pc := N 9031, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: rest} =
      some (pr9Newpart9Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 18) : rest.length + j < 1024 := by omega
  have ha1216 : (1216 : W).toNat = 1216 := rfl
  have hf1216 := Monpro.activeWords_fix s 1216 32 (by decide) (by norm_num) hact
  simp [hz, hzn, pr9Newpart9Program, pr9Newpart9Model, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, capacity, ha1216, hf1216]


def pr9Newpart10Program : List Instr :=
  [.op (.Dup dA15),
   .push 2 1248,
   .op .MLOAD,
   .op .MUL,
   .op .ADD,
   .push 2 1280,
   .op .MLOAD,
   .op (.Dup dA12)]

def pr9Newpart10Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 : W) (rest : List W) : State :=
  let v0 : W := MachineState.readWord s.memory 1248
  let v1 : W := v0 * x15
  let v2 : W := v1 + x0
  let v3 : W := MachineState.readWord s.memory 1280
  {s with pc := N 9053, memory := s.memory, stack := x11 :: v3 :: v2 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: rest}

theorem pr9Newpart10_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions pr9Newpart10Program {s with pc := N 9041, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: rest} =
      some (pr9Newpart10Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 18) : rest.length + j < 1024 := by omega
  have ha1248 : (1248 : W).toNat = 1248 := rfl
  have hf1248 := Monpro.activeWords_fix s 1248 32 (by decide) (by norm_num) hact
  have ha1280 : (1280 : W).toNat = 1280 := rfl
  have hf1280 := Monpro.activeWords_fix s 1280 32 (by decide) (by norm_num) hact
  simp [hz, hzn, pr9Newpart10Program, pr9Newpart10Model, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, capacity, ha1248, hf1248, ha1280, hf1280]


def pr9Newpart11Program : List Instr :=
  [.op .MUL,
   .op .ADD,
   .op (.Swap sA0),
   .op (.Dup dA9),
   .push 2 1088,
   .op .MLOAD,
   .op (.Dup dA10),
   .op .MULMOD]

def pr9Newpart11Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 : W) (rest : List W) : State :=
  let v0 : W := x0 * x1
  let v1 : W := v0 + x2
  let v2 : W := MachineState.readWord s.memory 1088
  let v3 : W := UInt256.mulMod x10 v2 x11
  {s with pc := N 9063, memory := s.memory, stack := v3 :: x3 :: v1 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: rest}

theorem pr9Newpart11_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions pr9Newpart11Program {s with pc := N 9053, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: rest} =
      some (pr9Newpart11Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 19) : rest.length + j < 1024 := by omega
  have ha1088 : (1088 : W).toNat = 1088 := rfl
  have hf1088 := Monpro.activeWords_fix s 1088 32 (by decide) (by norm_num) hact
  simp [hz, hzn, pr9Newpart11Program, pr9Newpart11Model, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, capacity, ha1088, hf1088]


def pr9Newpart12Program : List Instr :=
  [.op .ADD,
   .op (.Dup dA9),
   .push 1 192,
   .op .MLOAD,
   .op (.Dup dA5),
   .op .MULMOD]

def pr9Newpart12Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 : W) (rest : List W) : State :=
  let v0 : W := x0 + x1
  let v1 : W := MachineState.readWord s.memory 192
  let v2 : W := UInt256.mulMod x4 v1 x10
  {s with pc := N 9070, memory := s.memory, stack := v2 :: v0 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: rest}

theorem pr9Newpart12_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions pr9Newpart12Program {s with pc := N 9063, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: rest} =
      some (pr9Newpart12Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 19) : rest.length + j < 1024 := by omega
  have ha192 : (192 : W).toNat = 192 := rfl
  have hf192 := Monpro.activeWords_fix s 192 32 (by decide) (by norm_num) hact
  simp [hz, hzn, pr9Newpart12Program, pr9Newpart12Model, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, capacity, ha192, hf192]


def pr9NewProgram : List Instr :=
  [.op (.Dup dA5),
   .op .MUL,
   .op .ADD,
   .op (.Swap sA3),
   .op .MULMOD,
   .op .ADD,
   .op (.Dup dA9),
   .push 1 128,
   .op .MLOAD,
   .push 2 1856,
   .op .MLOAD,
   .op (.Swap sA3),
   .op (.Dup dA1),
   .op (.Dup dA5),
   .op .MUL,
   .op .ADD,
   .op (.Swap sA3),
   .op .MULMOD,
   .op .ADD,
   .push 1 160,
   .op .MLOAD,
   .push 2 1824,
   .op .MLOAD,
   .op (.Dup dA11),
   .op (.Dup dA1),
   .op (.Dup dA3),
   .op .MULMOD,
   .op (.Swap sA1),
   .op .MUL,
   .push 2 1792,
   .op .MLOAD,
   .op (.Swap sA3),
   .op .ADD,
   .op (.Swap sA1),
   .op .ADD,
   .op (.Dup dA10),
   .op (.Dup dA3),
   .op (.Dup dA5),
   .op .MULMOD,
   .op .ADD,
   .op (.Swap sA1),
   .op (.Dup dA3),
   .op .MUL,
   .op .ADD,
   .push 2 1600,
   .op .MLOAD,
   .op (.Swap sA10),
   .op (.Dup dA11),
   .op (.Swap sA2),
   .op (.Dup dA11),
   .op (.Dup dA2),
   .op (.Dup dA5),
   .op .MULMOD,
   .op .ADD,
   .op (.Swap sA2),
   .op .MUL,
   .op .ADD,
   .push 2 1088,
   .op .MLOAD,
   .op (.Dup dA9),
   .op .MUL,
   .op .ADD,
   .push 1 192,
   .op .MLOAD,
   .op (.Dup dA4),
   .op .MUL,
   .op .ADD,
   .push 0 0,
   .op .MLOAD,
   .op (.Dup dA8),
   .op .MUL,
   .op .ADD,
   .push 1 224,
   .op .MLOAD,
   .op (.Dup dA5),
   .op .MUL,
   .op .ADD,
   .push 2 1216,
   .op .MLOAD,
   .op (.Dup dA15),
   .op .MUL,
   .op .ADD,
   .op (.Dup dA15),
   .push 2 1248,
   .op .MLOAD,
   .op .MUL,
   .op .ADD,
   .push 2 1280,
   .op .MLOAD,
   .op (.Dup dA12),
   .op .MUL,
   .op .ADD,
   .op (.Swap sA0),
   .op (.Dup dA9),
   .push 2 1088,
   .op .MLOAD,
   .op (.Dup dA10),
   .op .MULMOD,
   .op .ADD,
   .op (.Dup dA9),
   .push 1 192,
   .op .MLOAD,
   .op (.Dup dA5),
   .op .MULMOD]

def pr9NewModel (s : State) (carry w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 : W) (rest : List W) : State :=
  let v0 : W := w4 * carry
  let v1 : W := v0 + w0
  let v2 : W := UInt256.mulMod w4 w1 w2
  let v3 : W := v2 + w3
  let v4 : W := MachineState.readWord s.memory 128
  let v5 : W := MachineState.readWord s.memory 1856
  let v6 : W := v5 * v4
  let v7 : W := v6 + v1
  let v8 : W := UInt256.mulMod v5 v4 w12
  let v9 : W := v8 + v3
  let v10 : W := MachineState.readWord s.memory 160
  let v11 : W := MachineState.readWord s.memory 1824
  let v12 : W := UInt256.mulMod v10 v11 w12
  let v13 : W := v10 * v11
  let v14 : W := MachineState.readWord s.memory 1792
  let v15 : W := v7 + v13
  let v16 : W := v9 + v12
  let v17 : W := UInt256.mulMod w5 v14 w12
  let v18 : W := v17 + v16
  let v19 : W := w5 * v14
  let v20 : W := v19 + v15
  let v21 : W := MachineState.readWord s.memory 1600
  let v22 : W := UInt256.mulMod v21 w13 w12
  let v23 : W := v22 + v18
  let v24 : W := v21 * w13
  let v25 : W := v24 + v20
  let v26 : W := MachineState.readWord s.memory 1088
  let v27 : W := w11 * v26
  let v28 : W := v27 + v25
  let v29 : W := MachineState.readWord s.memory 192
  let v30 : W := w6 * v29
  let v31 : W := v30 + v28
  let v32 : W := MachineState.readWord s.memory 0
  let v33 : W := w10 * v32
  let v34 : W := v33 + v31
  let v35 : W := MachineState.readWord s.memory 224
  let v36 : W := w7 * v35
  let v37 : W := v36 + v34
  let v38 : W := MachineState.readWord s.memory 1216
  let v39 : W := w17 * v38
  let v40 : W := v39 + v37
  let v41 : W := MachineState.readWord s.memory 1248
  let v42 : W := v41 * w18
  let v43 : W := v42 + v40
  let v44 : W := MachineState.readWord s.memory 1280
  let v45 : W := w14 * v44
  let v46 : W := v45 + v43
  let v47 : W := MachineState.readWord s.memory 1088
  let v48 : W := UInt256.mulMod w11 v47 w12
  let v49 : W := v48 + v23
  let v50 : W := MachineState.readWord s.memory 192
  let v51 : W := UInt256.mulMod w6 v50 w12
  {s with pc := N 9070, memory := s.memory, stack := v51 :: v49 :: v46 :: w5 :: w6 :: w7 :: w8 :: w9 :: w10 :: w11 :: w12 :: v21 :: w14 :: w15 :: w16 :: w17 :: w18 :: rest}

theorem pr9New_run (s : State) (carry w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions pr9NewProgram {s with pc := N 8943, stack := carry :: w0 :: w1 :: w2 :: w3 :: w4 :: w5 :: w6 :: w7 :: w8 :: w9 :: w10 :: w11 :: w12 :: w13 :: w14 :: w15 :: w16 :: w17 :: w18 :: rest} =
      some (pr9NewModel s carry w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 rest) := by
  let v0 : W := w4 * carry
  let v1 : W := v0 + w0
  let v2 : W := UInt256.mulMod w4 w1 w2
  let v3 : W := v2 + w3
  let v4 : W := MachineState.readWord s.memory 128
  let v5 : W := MachineState.readWord s.memory 1856
  let v6 : W := v5 * v4
  let v7 : W := v6 + v1
  let v8 : W := UInt256.mulMod v5 v4 w12
  let v9 : W := v8 + v3
  let v10 : W := MachineState.readWord s.memory 160
  let v11 : W := MachineState.readWord s.memory 1824
  let v12 : W := UInt256.mulMod v10 v11 w12
  let v13 : W := v10 * v11
  let v14 : W := MachineState.readWord s.memory 1792
  let v15 : W := v7 + v13
  let v16 : W := v9 + v12
  let v17 : W := UInt256.mulMod w5 v14 w12
  let v18 : W := v17 + v16
  let v19 : W := w5 * v14
  let v20 : W := v19 + v15
  let v21 : W := MachineState.readWord s.memory 1600
  let v22 : W := UInt256.mulMod v21 w13 w12
  let v23 : W := v22 + v18
  let v24 : W := v21 * w13
  let v25 : W := v24 + v20
  let v26 : W := MachineState.readWord s.memory 1088
  let v27 : W := w11 * v26
  let v28 : W := v27 + v25
  let v29 : W := MachineState.readWord s.memory 192
  let v30 : W := w6 * v29
  let v31 : W := v30 + v28
  let v32 : W := MachineState.readWord s.memory 0
  let v33 : W := w10 * v32
  let v34 : W := v33 + v31
  let v35 : W := MachineState.readWord s.memory 224
  let v36 : W := w7 * v35
  let v37 : W := v36 + v34
  let v38 : W := MachineState.readWord s.memory 1216
  let v39 : W := w17 * v38
  let v40 : W := v39 + v37
  let v41 : W := MachineState.readWord s.memory 1248
  let v42 : W := v41 * w18
  let v43 : W := v42 + v40
  let v44 : W := MachineState.readWord s.memory 1280
  let v45 : W := w14 * v44
  let v46 : W := v45 + v43
  let v47 : W := MachineState.readWord s.memory 1088
  let v48 : W := UInt256.mulMod w11 v47 w12
  let v49 : W := v48 + v23
  let v50 : W := MachineState.readWord s.memory 192
  let v51 : W := UInt256.mulMod w6 v50 w12
  have h0 : runInstructions pr9Newpart0Program {s with pc := N 8943, memory := s.memory, stack := carry :: w0 :: w1 :: w2 :: w3 :: w4 :: w5 :: w6 :: w7 :: w8 :: w9 :: w10 :: w11 :: w12 :: w13 :: w14 :: w15 :: w16 :: w17 :: w18 :: rest} = some {s with pc := N 8953, memory := s.memory, stack := v4 :: w12 :: v3 :: v1 :: w5 :: w6 :: w7 :: w8 :: w9 :: w10 :: w11 :: w12 :: w13 :: w14 :: w15 :: w16 :: w17 :: w18 :: rest} := by
    simpa only [pr9Newpart0Model, v0, v1, v2, v3, v4] using pr9Newpart0_run (s) (carry) (w0) (w1) (w2) (w3) (w4) (w5) (w6) (w7) (w8) (w9) (w10) (w11) (w12) (w13) (w14) (w15) (w16) (w17) (w18) rest hcap hact
  have h1 : runInstructions pr9Newpart1Program {s with pc := N 8953, memory := s.memory, stack := v4 :: w12 :: v3 :: v1 :: w5 :: w6 :: w7 :: w8 :: w9 :: w10 :: w11 :: w12 :: w13 :: w14 :: w15 :: w16 :: w17 :: w18 :: rest} = some {s with pc := N 8963, memory := s.memory, stack := v5 :: v4 :: w12 :: v3 :: v7 :: w5 :: w6 :: w7 :: w8 :: w9 :: w10 :: w11 :: w12 :: w13 :: w14 :: w15 :: w16 :: w17 :: w18 :: rest} := by
    simpa only [pr9Newpart1Model, v5, v6, v7] using pr9Newpart1_run (s) (v4) (w12) (v3) (v1) (w5) (w6) (w7) (w8) (w9) (w10) (w11) (w12) (w13) (w14) (w15) (w16) (w17) (w18) rest hcap hact
  have h2 : runInstructions pr9Newpart2Program {s with pc := N 8963, memory := s.memory, stack := v5 :: v4 :: w12 :: v3 :: v7 :: w5 :: w6 :: w7 :: w8 :: w9 :: w10 :: w11 :: w12 :: w13 :: w14 :: w15 :: w16 :: w17 :: w18 :: rest} = some {s with pc := N 8974, memory := s.memory, stack := v11 :: w12 :: v11 :: v10 :: v9 :: v7 :: w5 :: w6 :: w7 :: w8 :: w9 :: w10 :: w11 :: w12 :: w13 :: w14 :: w15 :: w16 :: w17 :: w18 :: rest} := by
    simpa only [pr9Newpart2Model, v8, v9, v10, v11] using pr9Newpart2_run (s) (v5) (v4) (w12) (v3) (v7) (w5) (w6) (w7) (w8) (w9) (w10) (w11) (w12) (w13) (w14) (w15) (w16) (w17) (w18) rest hcap hact
  have h3 : runInstructions pr9Newpart3Program {s with pc := N 8974, memory := s.memory, stack := v11 :: w12 :: v11 :: v10 :: v9 :: v7 :: w5 :: w6 :: w7 :: w8 :: w9 :: w10 :: w11 :: w12 :: w13 :: w14 :: w15 :: w16 :: w17 :: w18 :: rest} = some {s with pc := N 8984, memory := s.memory, stack := v15 :: v12 :: v9 :: v14 :: w5 :: w6 :: w7 :: w8 :: w9 :: w10 :: w11 :: w12 :: w13 :: w14 :: w15 :: w16 :: w17 :: w18 :: rest} := by
    simpa only [pr9Newpart3Model, v12, v13, v14, v15] using pr9Newpart3_run (s) (v11) (w12) (v11) (v10) (v9) (v7) (w5) (w6) (w7) (w8) (w9) (w10) (w11) (w12) (w13) (w14) (w15) (w16) (w17) (w18) rest hcap hact
  have h4 : runInstructions pr9Newpart4Program {s with pc := N 8984, memory := s.memory, stack := v15 :: v12 :: v9 :: v14 :: w5 :: w6 :: w7 :: w8 :: w9 :: w10 :: w11 :: w12 :: w13 :: w14 :: w15 :: w16 :: w17 :: w18 :: rest} = some {s with pc := N 8992, memory := s.memory, stack := v14 :: v15 :: v18 :: w5 :: w6 :: w7 :: w8 :: w9 :: w10 :: w11 :: w12 :: w13 :: w14 :: w15 :: w16 :: w17 :: w18 :: rest} := by
    simpa only [pr9Newpart4Model, v16, v17, v18] using pr9Newpart4_run (s) (v15) (v12) (v9) (v14) (w5) (w6) (w7) (w8) (w9) (w10) (w11) (w12) (w13) (w14) (w15) (w16) (w17) (w18) rest hcap hact
  have h5 : runInstructions pr9Newpart5Program {s with pc := N 8992, memory := s.memory, stack := v14 :: v15 :: v18 :: w5 :: w6 :: w7 :: w8 :: w9 :: w10 :: w11 :: w12 :: w13 :: w14 :: w15 :: w16 :: w17 :: w18 :: rest} = some {s with pc := N 9002, memory := s.memory, stack := v18 :: w13 :: v20 :: v21 :: w5 :: w6 :: w7 :: w8 :: w9 :: w10 :: w11 :: w12 :: v21 :: w14 :: w15 :: w16 :: w17 :: w18 :: rest} := by
    simpa only [pr9Newpart5Model, v19, v20, v21] using pr9Newpart5_run (s) (v14) (v15) (v18) (w5) (w6) (w7) (w8) (w9) (w10) (w11) (w12) (w13) (w14) (w15) (w16) (w17) (w18) rest hcap hact
  have h6 : runInstructions pr9Newpart6Program {s with pc := N 9002, memory := s.memory, stack := v18 :: w13 :: v20 :: v21 :: w5 :: w6 :: w7 :: w8 :: w9 :: w10 :: w11 :: w12 :: v21 :: w14 :: w15 :: w16 :: w17 :: w18 :: rest} = some {s with pc := N 9010, memory := s.memory, stack := v25 :: v23 :: w5 :: w6 :: w7 :: w8 :: w9 :: w10 :: w11 :: w12 :: v21 :: w14 :: w15 :: w16 :: w17 :: w18 :: rest} := by
    simpa only [pr9Newpart6Model, v22, v23, v24, v25] using pr9Newpart6_run (s) (v18) (w13) (v20) (v21) (w5) (w6) (w7) (w8) (w9) (w10) (w11) (w12) (v21) (w14) (w15) (w16) (w17) (w18) rest hcap hact
  have h7 : runInstructions pr9Newpart7Program {s with pc := N 9010, memory := s.memory, stack := v25 :: v23 :: w5 :: w6 :: w7 :: w8 :: w9 :: w10 :: w11 :: w12 :: v21 :: w14 :: w15 :: w16 :: w17 :: w18 :: rest} = some {s with pc := N 9021, memory := s.memory, stack := w6 :: v29 :: v28 :: v23 :: w5 :: w6 :: w7 :: w8 :: w9 :: w10 :: w11 :: w12 :: v21 :: w14 :: w15 :: w16 :: w17 :: w18 :: rest} := by
    simpa only [pr9Newpart7Model, v26, v27, v28, v29] using pr9Newpart7_run (s) (v25) (v23) (w5) (w6) (w7) (w8) (w9) (w10) (w11) (w12) (v21) (w14) (w15) (w16) (w17) (w18) rest hcap hact
  have h8 : runInstructions pr9Newpart8Program {s with pc := N 9021, memory := s.memory, stack := w6 :: v29 :: v28 :: v23 :: w5 :: w6 :: w7 :: w8 :: w9 :: w10 :: w11 :: w12 :: v21 :: w14 :: w15 :: w16 :: w17 :: w18 :: rest} = some {s with pc := N 9031, memory := s.memory, stack := v35 :: v34 :: v23 :: w5 :: w6 :: w7 :: w8 :: w9 :: w10 :: w11 :: w12 :: v21 :: w14 :: w15 :: w16 :: w17 :: w18 :: rest} := by
    simpa only [pr9Newpart8Model, v30, v31, v32, v33, v34, v35] using pr9Newpart8_run (s) (w6) (v29) (v28) (v23) (w5) (w6) (w7) (w8) (w9) (w10) (w11) (w12) (v21) (w14) (w15) (w16) (w17) (w18) rest hcap hact
  have h9 : runInstructions pr9Newpart9Program {s with pc := N 9031, memory := s.memory, stack := v35 :: v34 :: v23 :: w5 :: w6 :: w7 :: w8 :: w9 :: w10 :: w11 :: w12 :: v21 :: w14 :: w15 :: w16 :: w17 :: w18 :: rest} = some {s with pc := N 9041, memory := s.memory, stack := v40 :: v23 :: w5 :: w6 :: w7 :: w8 :: w9 :: w10 :: w11 :: w12 :: v21 :: w14 :: w15 :: w16 :: w17 :: w18 :: rest} := by
    simpa only [pr9Newpart9Model, v36, v37, v38, v39, v40] using pr9Newpart9_run (s) (v35) (v34) (v23) (w5) (w6) (w7) (w8) (w9) (w10) (w11) (w12) (v21) (w14) (w15) (w16) (w17) (w18) rest hcap hact
  have h10 : runInstructions pr9Newpart10Program {s with pc := N 9041, memory := s.memory, stack := v40 :: v23 :: w5 :: w6 :: w7 :: w8 :: w9 :: w10 :: w11 :: w12 :: v21 :: w14 :: w15 :: w16 :: w17 :: w18 :: rest} = some {s with pc := N 9053, memory := s.memory, stack := w14 :: v44 :: v43 :: v23 :: w5 :: w6 :: w7 :: w8 :: w9 :: w10 :: w11 :: w12 :: v21 :: w14 :: w15 :: w16 :: w17 :: w18 :: rest} := by
    simpa only [pr9Newpart10Model, v41, v42, v43, v44] using pr9Newpart10_run (s) (v40) (v23) (w5) (w6) (w7) (w8) (w9) (w10) (w11) (w12) (v21) (w14) (w15) (w16) (w17) (w18) rest hcap hact
  have h11 : runInstructions pr9Newpart11Program {s with pc := N 9053, memory := s.memory, stack := w14 :: v44 :: v43 :: v23 :: w5 :: w6 :: w7 :: w8 :: w9 :: w10 :: w11 :: w12 :: v21 :: w14 :: w15 :: w16 :: w17 :: w18 :: rest} = some {s with pc := N 9063, memory := s.memory, stack := v48 :: v23 :: v46 :: w5 :: w6 :: w7 :: w8 :: w9 :: w10 :: w11 :: w12 :: v21 :: w14 :: w15 :: w16 :: w17 :: w18 :: rest} := by
    simpa only [pr9Newpart11Model, v45, v46, v47, v48] using pr9Newpart11_run (s) (w14) (v44) (v43) (v23) (w5) (w6) (w7) (w8) (w9) (w10) (w11) (w12) (v21) (w14) (w15) (w16) (w17) (w18) rest hcap hact
  have h12 : runInstructions pr9Newpart12Program {s with pc := N 9063, memory := s.memory, stack := v48 :: v23 :: v46 :: w5 :: w6 :: w7 :: w8 :: w9 :: w10 :: w11 :: w12 :: v21 :: w14 :: w15 :: w16 :: w17 :: w18 :: rest} = some {s with pc := N 9070, memory := s.memory, stack := v51 :: v49 :: v46 :: w5 :: w6 :: w7 :: w8 :: w9 :: w10 :: w11 :: w12 :: v21 :: w14 :: w15 :: w16 :: w17 :: w18 :: rest} := by
    simpa only [pr9Newpart12Model, v49, v50, v51] using pr9Newpart12_run (s) (v48) (v23) (v46) (w5) (w6) (w7) (w8) (w9) (w10) (w11) (w12) (v21) (w14) (w15) (w16) (w17) (w18) rest hcap hact
  exact (runInstructions_append_some _ _ _ _ _ h0 (runInstructions_append_some _ _ _ _ _ h1 (runInstructions_append_some _ _ _ _ _ h2 (runInstructions_append_some _ _ _ _ _ h3 (runInstructions_append_some _ _ _ _ _ h4 (runInstructions_append_some _ _ _ _ _ h5 (runInstructions_append_some _ _ _ _ _ h6 (runInstructions_append_some _ _ _ _ _ h7 (runInstructions_append_some _ _ _ _ _ h8 (runInstructions_append_some _ _ _ _ _ h9 (runInstructions_append_some _ _ _ _ _ h10 (runInstructions_append_some _ _ _ _ _ h11 h12))))))))))))

#print axioms pr9New_run

def productColumn9Model (s : State) (carry w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 : W) (rest : List W) : State :=
  let v0 : W := w4 * carry
  let v1 : W := v0 + w0
  let v2 : W := UInt256.mulMod w4 w1 w2
  let v3 : W := v2 + w3
  let v4 : W := MachineState.readWord s.memory 128
  let v5 : W := MachineState.readWord s.memory 1856
  let v6 : W := v5 * v4
  let v7 : W := v6 + v1
  let v8 : W := UInt256.mulMod v5 v4 w12
  let v9 : W := v8 + v3
  let v10 : W := MachineState.readWord s.memory 160
  let v11 : W := MachineState.readWord s.memory 1824
  let v12 : W := v11 * v10
  let v13 : W := v12 + v7
  let v14 : W := UInt256.mulMod v11 v10 w12
  let v15 : W := v14 + v9
  let v16 : W := MachineState.readWord s.memory 1792
  let v17 : W := v16 * w5
  let v18 : W := v17 + v13
  let v19 : W := UInt256.mulMod v16 w5 w12
  let v20 : W := v19 + v15
  let v21 : W := MachineState.readWord s.memory 1600
  let v22 : W := UInt256.mulMod v21 w13 w12
  let v23 : W := v22 + v20
  let v24 : W := v21 * w13
  let v25 : W := v24 + v18
  let v26 : W := MachineState.readWord s.memory 1088
  let v27 : W := w11 * v26
  let v28 : W := v27 + v25
  let v29 : W := MachineState.readWord s.memory 192
  let v30 : W := w6 * v29
  let v31 : W := v30 + v28
  let v32 : W := MachineState.readWord s.memory 0
  let v33 : W := w10 * v32
  let v34 : W := v33 + v31
  let v35 : W := MachineState.readWord s.memory 224
  let v36 : W := w7 * v35
  let v37 : W := v36 + v34
  let v38 : W := MachineState.readWord s.memory 1216
  let v39 : W := w17 * v38
  let v40 : W := v39 + v37
  let v41 : W := MachineState.readWord s.memory 1248
  let v42 : W := v41 * w18
  let v43 : W := v42 + v40
  let v44 : W := MachineState.readWord s.memory 1280
  let v45 : W := w14 * v44
  let v46 : W := v45 + v43
  let v47 : W := MachineState.readWord s.memory 1088
  let v48 : W := UInt256.mulMod w11 v47 w12
  let v49 : W := v48 + v23
  let v50 : W := MachineState.readWord s.memory 192
  let v51 : W := UInt256.mulMod w6 v50 w12
  {s with pc := N 9070, memory := s.memory, stack := v51 :: v49 :: v46 :: w5 :: w6 :: w7 :: w8 :: w9 :: w10 :: w11 :: w12 :: v21 :: w14 :: w15 :: w16 :: w17 :: w18 :: rest}

def productColumn9Program : List Instr := pr9NewProgram

private theorem aux_shared0 (w12 : W) (z0 z1 : W) :
    (UInt256.mulMod z0 z1 w12) = (UInt256.mulMod z1 z0 w12) := by
  simp (disch := decide) only [addC, addA, addL, mulC, mmC, amC, andC, orC, xorC, eqC, read_disjoint, Challenge.EvmProof.Memory.readWord_writeWord]

private theorem aux_shared1 (z0 z1 : W) :
    (z0 * z1) = (z1 * z0) := by
  simp (disch := decide) only [addC, addA, addL, mulC, mmC, amC, andC, orC, xorC, eqC, read_disjoint, Challenge.EvmProof.Memory.readWord_writeWord]

private theorem aux_shared2 (z0 z1 : W) :
    (z0 + z1) = (z1 + z0) := by
  simp (disch := decide) only [addC, addA, addL, mulC, mmC, amC, andC, orC, xorC, eqC, read_disjoint, Challenge.EvmProof.Memory.readWord_writeWord]

private theorem aux_shared3 (w5 w12 : W) (z0 : W) :
    (UInt256.mulMod w5 z0 w12) = (UInt256.mulMod z0 w5 w12) := by
  simp (disch := decide) only [addC, addA, addL, mulC, mmC, amC, andC, orC, xorC, eqC, read_disjoint, Challenge.EvmProof.Memory.readWord_writeWord]

private theorem aux_shared4 (w5 : W) (z0 : W) :
    (w5 * z0) = (z0 * w5) := by
  simp (disch := decide) only [addC, addA, addL, mulC, mmC, amC, andC, orC, xorC, eqC, read_disjoint, Challenge.EvmProof.Memory.readWord_writeWord]

private theorem prepared_model_eq (s : State) (carry w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 : W) (rest : List W) :
    productColumn9Model s carry w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 rest = pr9NewModel s carry w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 rest := by
  let o0 : W := w4 * carry
  let o1 : W := o0 + w0
  let o2 : W := UInt256.mulMod w4 w1 w2
  let o3 : W := o2 + w3
  let o4 : W := MachineState.readWord s.memory 128
  let o5 : W := MachineState.readWord s.memory 1856
  let o6 : W := o5 * o4
  let o7 : W := o6 + o1
  let o8 : W := UInt256.mulMod o5 o4 w12
  let o9 : W := o8 + o3
  let o10 : W := MachineState.readWord s.memory 160
  let o11 : W := MachineState.readWord s.memory 1824
  let o12 : W := o11 * o10
  let o13 : W := o12 + o7
  let o14 : W := UInt256.mulMod o11 o10 w12
  let o15 : W := o14 + o9
  let o16 : W := MachineState.readWord s.memory 1792
  let o17 : W := o16 * w5
  let o18 : W := o17 + o13
  let o19 : W := UInt256.mulMod o16 w5 w12
  let o20 : W := o19 + o15
  let o21 : W := MachineState.readWord s.memory 1600
  let o22 : W := UInt256.mulMod o21 w13 w12
  let o23 : W := o22 + o20
  let o24 : W := o21 * w13
  let o25 : W := o24 + o18
  let o26 : W := MachineState.readWord s.memory 1088
  let o27 : W := w11 * o26
  let o28 : W := o27 + o25
  let o29 : W := MachineState.readWord s.memory 192
  let o30 : W := w6 * o29
  let o31 : W := o30 + o28
  let o32 : W := MachineState.readWord s.memory 0
  let o33 : W := w10 * o32
  let o34 : W := o33 + o31
  let o35 : W := MachineState.readWord s.memory 224
  let o36 : W := w7 * o35
  let o37 : W := o36 + o34
  let o38 : W := MachineState.readWord s.memory 1216
  let o39 : W := w17 * o38
  let o40 : W := o39 + o37
  let o41 : W := MachineState.readWord s.memory 1248
  let o42 : W := o41 * w18
  let o43 : W := o42 + o40
  let o44 : W := MachineState.readWord s.memory 1280
  let o45 : W := w14 * o44
  let o46 : W := o45 + o43
  let o47 : W := MachineState.readWord s.memory 1088
  let o48 : W := UInt256.mulMod w11 o47 w12
  let o49 : W := o48 + o23
  let o50 : W := MachineState.readWord s.memory 192
  let o51 : W := UInt256.mulMod w6 o50 w12
  let n0 : W := w4 * carry
  let n1 : W := n0 + w0
  let n2 : W := UInt256.mulMod w4 w1 w2
  let n3 : W := n2 + w3
  let n4 : W := MachineState.readWord s.memory 128
  let n5 : W := MachineState.readWord s.memory 1856
  let n6 : W := n5 * n4
  let n7 : W := n6 + n1
  let n8 : W := UInt256.mulMod n5 n4 w12
  let n9 : W := n8 + n3
  let n10 : W := MachineState.readWord s.memory 160
  let n11 : W := MachineState.readWord s.memory 1824
  let n12 : W := UInt256.mulMod n10 n11 w12
  let n13 : W := n10 * n11
  let n14 : W := MachineState.readWord s.memory 1792
  let n15 : W := n7 + n13
  let n16 : W := n9 + n12
  let n17 : W := UInt256.mulMod w5 n14 w12
  let n18 : W := n17 + n16
  let n19 : W := w5 * n14
  let n20 : W := n19 + n15
  let n21 : W := MachineState.readWord s.memory 1600
  let n22 : W := UInt256.mulMod n21 w13 w12
  let n23 : W := n22 + n18
  let n24 : W := n21 * w13
  let n25 : W := n24 + n20
  let n26 : W := MachineState.readWord s.memory 1088
  let n27 : W := w11 * n26
  let n28 : W := n27 + n25
  let n29 : W := MachineState.readWord s.memory 192
  let n30 : W := w6 * n29
  let n31 : W := n30 + n28
  let n32 : W := MachineState.readWord s.memory 0
  let n33 : W := w10 * n32
  let n34 : W := n33 + n31
  let n35 : W := MachineState.readWord s.memory 224
  let n36 : W := w7 * n35
  let n37 : W := n36 + n34
  let n38 : W := MachineState.readWord s.memory 1216
  let n39 : W := w17 * n38
  let n40 : W := n39 + n37
  let n41 : W := MachineState.readWord s.memory 1248
  let n42 : W := n41 * w18
  let n43 : W := n42 + n40
  let n44 : W := MachineState.readWord s.memory 1280
  let n45 : W := w14 * n44
  let n46 : W := n45 + n43
  let n47 : W := MachineState.readWord s.memory 1088
  let n48 : W := UInt256.mulMod w11 n47 w12
  let n49 : W := n48 + n23
  let n50 : W := MachineState.readWord s.memory 192
  let n51 : W := UInt256.mulMod w6 n50 w12
  have eq_o47 : o47 = o26 := by
    simp only [o47, o26]
  have eq_o50 : o50 = o29 := by
    simp only [o50, o29]
  have eq_n0 : n0 = o0 := by
    simp only [n0, o0]
  have eq_n1 : n1 = o1 := by
    simp only [n1, o1, eq_n0]
  have eq_n2 : n2 = o2 := by
    simp only [n2, o2]
  have eq_n3 : n3 = o3 := by
    simp only [n3, o3, eq_n2]
  have eq_n4 : n4 = o4 := by
    simp only [n4, o4]
  have eq_n5 : n5 = o5 := by
    simp only [n5, o5]
  have eq_n6 : n6 = o6 := by
    simp only [n6, o6, eq_n5, eq_n4]
  have eq_n7 : n7 = o7 := by
    simp only [n7, o7, eq_n6, eq_n1]
  have eq_n8 : n8 = o8 := by
    simp only [n8, o8, eq_n5, eq_n4]
  have eq_n9 : n9 = o9 := by
    simp only [n9, o9, eq_n8, eq_n3]
  have eq_n10 : n10 = o10 := by
    simp only [n10, o10]
  have eq_n11 : n11 = o11 := by
    simp only [n11, o11]
  have eq_n12 : n12 = o14 := by
    simpa only [n12, o14, eq_n10, eq_n11] using
      (aux_shared0 w12 o10 o11)
  have eq_n13 : n13 = o12 := by
    simpa only [n13, o12, eq_n10, eq_n11] using
      (aux_shared1  o10 o11)
  have eq_n14 : n14 = o16 := by
    simp only [n14, o16]
  have eq_n15 : n15 = o13 := by
    simpa only [n15, o13, eq_n7, eq_n13] using
      (aux_shared2  o7 o12)
  have eq_n16 : n16 = o15 := by
    simpa only [n16, o15, eq_n9, eq_n12] using
      (aux_shared2  o9 o14)
  have eq_n17 : n17 = o19 := by
    simpa only [n17, o19, eq_n14] using
      (aux_shared3 w5 w12 o16)
  have eq_n18 : n18 = o20 := by
    simp only [n18, o20, eq_n17, eq_n16]
  have eq_n19 : n19 = o17 := by
    simpa only [n19, o17, eq_n14] using
      (aux_shared4 w5 o16)
  have eq_n20 : n20 = o18 := by
    simp only [n20, o18, eq_n19, eq_n15]
  have eq_n21 : n21 = o21 := by
    simp only [n21, o21]
  have eq_n22 : n22 = o22 := by
    simp only [n22, o22, eq_n21]
  have eq_n23 : n23 = o23 := by
    simp only [n23, o23, eq_n22, eq_n18]
  have eq_n24 : n24 = o24 := by
    simp only [n24, o24, eq_n21]
  have eq_n25 : n25 = o25 := by
    simp only [n25, o25, eq_n24, eq_n20]
  have eq_n26 : n26 = o26 := by
    simp only [n26, o26]
  have eq_n27 : n27 = o27 := by
    simp only [n27, o27, eq_n26]
  have eq_n28 : n28 = o28 := by
    simp only [n28, o28, eq_n27, eq_n25]
  have eq_n29 : n29 = o29 := by
    simp only [n29, o29]
  have eq_n30 : n30 = o30 := by
    simp only [n30, o30, eq_n29]
  have eq_n31 : n31 = o31 := by
    simp only [n31, o31, eq_n30, eq_n28]
  have eq_n32 : n32 = o32 := by
    simp only [n32, o32]
  have eq_n33 : n33 = o33 := by
    simp only [n33, o33, eq_n32]
  have eq_n34 : n34 = o34 := by
    simp only [n34, o34, eq_n33, eq_n31]
  have eq_n35 : n35 = o35 := by
    simp only [n35, o35]
  have eq_n36 : n36 = o36 := by
    simp only [n36, o36, eq_n35]
  have eq_n37 : n37 = o37 := by
    simp only [n37, o37, eq_n36, eq_n34]
  have eq_n38 : n38 = o38 := by
    simp only [n38, o38]
  have eq_n39 : n39 = o39 := by
    simp only [n39, o39, eq_n38]
  have eq_n40 : n40 = o40 := by
    simp only [n40, o40, eq_n39, eq_n37]
  have eq_n41 : n41 = o41 := by
    simp only [n41, o41]
  have eq_n42 : n42 = o42 := by
    simp only [n42, o42, eq_n41]
  have eq_n43 : n43 = o43 := by
    simp only [n43, o43, eq_n42, eq_n40]
  have eq_n44 : n44 = o44 := by
    simp only [n44, o44]
  have eq_n45 : n45 = o45 := by
    simp only [n45, o45, eq_n44]
  have eq_n46 : n46 = o46 := by
    simp only [n46, o46, eq_n45, eq_n43]
  have eq_n47 : n47 = o26 := by
    simp only [n47, o26]
  have eq_n48 : n48 = o48 := by
    simp only [n48, o48, eq_n47, eq_o47]
  have eq_n49 : n49 = o49 := by
    simp only [n49, o49, eq_n48, eq_n23]
  have eq_n50 : n50 = o29 := by
    simp only [n50, o29]
  have eq_n51 : n51 = o51 := by
    simp only [n51, o51, eq_n50, eq_o50]
  change {s with pc := N 9070, memory := s.memory, stack := o51 :: o49 :: o46 :: w5 :: w6 :: w7 :: w8 :: w9 :: w10 :: w11 :: w12 :: o21 :: w14 :: w15 :: w16 :: w17 :: w18 :: rest} =
    {s with pc := N 9070, memory := s.memory, stack := n51 :: n49 :: n46 :: w5 :: w6 :: w7 :: w8 :: w9 :: w10 :: w11 :: w12 :: n21 :: w14 :: w15 :: w16 :: w17 :: w18 :: rest}
  simp only [eq_o47, eq_o50, eq_n0, eq_n1, eq_n2, eq_n3, eq_n4, eq_n5, eq_n6, eq_n7, eq_n8, eq_n9, eq_n10, eq_n11, eq_n12, eq_n13, eq_n14, eq_n15, eq_n16, eq_n17, eq_n18, eq_n19, eq_n20, eq_n21, eq_n22, eq_n23, eq_n24, eq_n25, eq_n26, eq_n27, eq_n28, eq_n29, eq_n30, eq_n31, eq_n32, eq_n33, eq_n34, eq_n35, eq_n36, eq_n37, eq_n38, eq_n39, eq_n40, eq_n41, eq_n42, eq_n43, eq_n44, eq_n45, eq_n46, eq_n47, eq_n48, eq_n49, eq_n50, eq_n51]
theorem productColumn9_run (s : State) (carry w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions productColumn9Program {s with pc := N 8943, stack := carry :: w0 :: w1 :: w2 :: w3 :: w4 :: w5 :: w6 :: w7 :: w8 :: w9 :: w10 :: w11 :: w12 :: w13 :: w14 :: w15 :: w16 :: w17 :: w18 :: rest} =
      some (productColumn9Model s carry w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 rest) := by
  exact (pr9New_run s carry w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 rest hcap hact).trans
    (congrArg some (prepared_model_eq s carry w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 rest).symm)

#print axioms productColumn9_run
end CycleSubmission.Execution
