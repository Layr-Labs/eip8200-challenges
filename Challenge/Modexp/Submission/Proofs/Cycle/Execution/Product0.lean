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

def pr0Newpart0Program : List Instr :=
  [.push 2 768,
   .op .MLOAD,
   .op (.Dup dA8),
   .push 2 1792,
   .op .MLOAD,
   .op (.Dup dA0),
   .op (.Dup dA3),
   .op .MUL]

def pr0Newpart0Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 : W) (rest : List W) : State :=
  let v0 : W := MachineState.readWord s.memory 768
  let v1 : W := MachineState.readWord s.memory 1792
  let v2 : W := v0 * v1
  {s with pc := N 7769, memory := s.memory, stack := v2 :: v1 :: x7 :: v0 :: x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: rest}

theorem pr0Newpart0_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions pr0Newpart0Program {s with pc := N 7757, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: rest} =
      some (pr0Newpart0Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 19) : rest.length + j < 1024 := by omega
  have ha768 : (768 : W).toNat = 768 := rfl
  have hf768 := Monpro.activeWords_fix s 768 32 (by decide) (by norm_num) hact
  have ha1792 : (1792 : W).toNat = 1792 := rfl
  have hf1792 := Monpro.activeWords_fix s 1792 32 (by decide) (by norm_num) hact
  simp [hz, hzn, pr0Newpart0Program, pr0Newpart0Model, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, capacity, ha768, hf768, ha1792, hf1792]


def pr0Newpart1Program : List Instr :=
  [.push 2 2720,
   .op .MLOAD,
   .op .MUL,
   .op (.Dup dA14),
   .op .AND,
   .op (.Swap sA11),
   .op .POP,
   .op (.Dup dA10)]

def pr0Newpart1Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 : W) (rest : List W) : State :=
  let v0 : W := MachineState.readWord s.memory 2720
  let v1 : W := v0 * x0
  let v2 : W := UInt256.land x14 v1
  {s with pc := N 7779, memory := s.memory, stack := x11 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: v2 :: x13 :: x14 :: x15 :: x16 :: x17 :: rest}

theorem pr0Newpart1_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions pr0Newpart1Program {s with pc := N 7769, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: rest} =
      some (pr0Newpart1Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 19) : rest.length + j < 1024 := by omega
  have ha2720 : (2720 : W).toNat = 2720 := rfl
  have hf2720 := Monpro.activeWords_fix s 2720 32 (by decide) (by norm_num) hact
  simp [hz, hzn, pr0Newpart1Program, pr0Newpart1Model, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, capacity, ha2720, hf2720]


def pr0Newpart2Program : List Instr :=
  [.op (.Swap sA2),
   .op .MULMOD,
   .op (.Dup dA1),
   .op (.Dup dA11),
   .op (.Dup dA15),
   .op .MULMOD,
   .op .ADD,
   .push 2 2048]

def pr0Newpart2Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 : W) (rest : List W) : State :=
  let v0 : W := UInt256.mulMod x3 x1 x2
  let v1 : W := UInt256.mulMod x15 x12 x0
  let v2 : W := v1 + v0
  {s with pc := N 7789, memory := s.memory, stack := (N 2048) :: v2 :: x0 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: rest}

theorem pr0Newpart2_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions pr0Newpart2Program {s with pc := N 7779, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: rest} =
      some (pr0Newpart2Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 19) : rest.length + j < 1024 := by omega
  simp [hz, hzn, pr0Newpart2Program, pr0Newpart2Model, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, capacity]


def pr0Newpart3Program : List Instr :=
  [.op .MULMOD,
   .op (.Dup dA0),
   .op (.Dup dA9),
   .push 2 768,
   .op .MLOAD,
   .push 2 1824,
   .op .MLOAD,
   .op (.Swap sA3)]

def pr0Newpart3Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 : W) (rest : List W) : State :=
  let v0 : W := UInt256.mulMod x0 x1 x2
  let v1 : W := MachineState.readWord s.memory 768
  let v2 : W := MachineState.readWord s.memory 1824
  {s with pc := N 7801, memory := s.memory, stack := v0 :: v1 :: x10 :: v0 :: v2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: rest}

theorem pr0Newpart3_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) (hk_x0 : x0 = N 2048) :
    runInstructions pr0Newpart3Program {s with pc := N 7789, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: rest} =
      some (pr0Newpart3Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 19) : rest.length + j < 1024 := by omega
  have ha768 : (768 : W).toNat = 768 := rfl
  have hf768 := Monpro.activeWords_fix s 768 32 (by decide) (by norm_num) hact
  have ha1824 : (1824 : W).toNat = 1824 := rfl
  have hf1824 := Monpro.activeWords_fix s 1824 32 (by decide) (by norm_num) hact
  simp [hk_x0, hz, hzn, pr0Newpart3Program, pr0Newpart3Model, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, capacity, ha768, hf768, ha1824, hf1824]


def pr0Newpart4Program : List Instr :=
  [.op (.Dup dA1),
   .op (.Dup dA5),
   .op .MUL,
   .op .ADD,
   .op (.Swap sA3),
   .op .MULMOD,
   .op .ADD,
   .op (.Dup dA9)]

def pr0Newpart4Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 : W) (rest : List W) : State :=
  let v0 : W := x4 * x1
  let v1 : W := v0 + x0
  let v2 : W := UInt256.mulMod x4 x1 x2
  let v3 : W := v2 + x3
  {s with pc := N 7809, memory := s.memory, stack := x12 :: v3 :: v1 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: x18 :: rest}

theorem pr0Newpart4_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions pr0Newpart4Program {s with pc := N 7801, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: x18 :: rest} =
      some (pr0Newpart4Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 21) : rest.length + j < 1024 := by omega
  simp [hz, hzn, pr0Newpart4Program, pr0Newpart4Model, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, capacity]


def pr0Newpart5Program : List Instr :=
  [.op (.Dup dA11),
   .op (.Dup dA13),
   .op .MUL,
   .push 2 1792,
   .op .MLOAD,
   .op (.Swap sA3),
   .op .ADD,
   .op (.Dup dA3)]

def pr0Newpart5Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 : W) (rest : List W) : State :=
  let v0 : W := x12 * x11
  let v1 : W := MachineState.readWord s.memory 1792
  let v2 : W := x2 + v0
  {s with pc := N 7819, memory := s.memory, stack := v1 :: v2 :: x0 :: x1 :: v1 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: rest}

theorem pr0Newpart5_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions pr0Newpart5Program {s with pc := N 7809, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: rest} =
      some (pr0Newpart5Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 19) : rest.length + j < 1024 := by omega
  have ha1792 : (1792 : W).toNat = 1792 := rfl
  have hf1792 := Monpro.activeWords_fix s 1792 32 (by decide) (by norm_num) hact
  simp [hz, hzn, pr0Newpart5Program, pr0Newpart5Model, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, capacity, ha1792, hf1792]


def pr0Newpart6Program : List Instr :=
  [.op (.Dup dA8),
   .op .MUL,
   .op .ADD,
   .op (.Swap sA2),
   .op (.Dup dA7),
   .op .MULMOD,
   .op .ADD,
   .op (.Dup dA9)]

def pr0Newpart6Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 : W) (rest : List W) : State :=
  let v0 : W := x8 * x0
  let v1 : W := v0 + x1
  let v2 : W := UInt256.mulMod x8 x4 x2
  let v3 : W := v2 + x3
  {s with pc := N 7827, memory := s.memory, stack := x12 :: v3 :: v1 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: x18 :: rest}

theorem pr0Newpart6_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions pr0Newpart6Program {s with pc := N 7819, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: x18 :: rest} =
      some (pr0Newpart6Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 20) : rest.length + j < 1024 := by omega
  simp [hz, hzn, pr0Newpart6Program, pr0Newpart6Model, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, capacity]


def pr0Newpart7Program : List Instr :=
  [.op (.Dup dA11),
   .op (.Dup dA13),
   .op .MULMOD,
   .op .ADD,
   .op (.Dup dA9),
   .op (.Dup dA14),
   .push 2 2720,
   .op .MLOAD]

def pr0Newpart7Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 : W) (rest : List W) : State :=
  let v0 : W := UInt256.mulMod x12 x11 x0
  let v1 : W := v0 + x1
  let v2 : W := MachineState.readWord s.memory 2720
  {s with pc := N 7837, memory := s.memory, stack := v2 :: x14 :: x10 :: v1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: rest}

theorem pr0Newpart7_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions pr0Newpart7Program {s with pc := N 7827, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: rest} =
      some (pr0Newpart7Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 19) : rest.length + j < 1024 := by omega
  have ha2720 : (2720 : W).toNat = 2720 := rfl
  have hf2720 := Monpro.activeWords_fix s 2720 32 (by decide) (by norm_num) hact
  simp [hz, hzn, pr0Newpart7Program, pr0Newpart7Model, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, capacity, ha2720, hf2720]


def pr0Newpart8Program : List Instr :=
  [.op (.Dup dA2),
   .op (.Swap sA4),
   .op .MUL,
   .op (.Dup dA15),
   .op .AND,
   .op (.Dup dA0),
   .op (.Swap sA11),
   .op .POP]

def pr0Newpart8Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 : W) (rest : List W) : State :=
  let v0 : W := x4 * x0
  let v1 : W := UInt256.land x15 v0
  {s with pc := N 7845, memory := s.memory, stack := v1 :: x1 :: x2 :: x3 :: x2 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: v1 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: x18 :: rest}

theorem pr0Newpart8_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions pr0Newpart8Program {s with pc := N 7837, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: x18 :: rest} =
      some (pr0Newpart8Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 20) : rest.length + j < 1024 := by omega
  simp [hz, hzn, pr0Newpart8Program, pr0Newpart8Model, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, capacity]


def pr0Newpart9Program : List Instr :=
  [.op .MULMOD,
   .op .ADD,
   .push 2 2048,
   .op .MULMOD,
   .push 2 1824,
   .op .MLOAD,
   .push 2 768,
   .op .MLOAD]

def pr0Newpart9Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 : W) (rest : List W) : State :=
  let v0 : W := UInt256.mulMod x0 x1 x2
  let v1 : W := v0 + x3
  let v2 : W := UInt256.mulMod (N 2048) v1 x4
  let v3 : W := MachineState.readWord s.memory 1824
  let v4 : W := MachineState.readWord s.memory 768
  {s with pc := N 7859, memory := s.memory, stack := v4 :: v3 :: v2 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: x18 :: rest}

theorem pr0Newpart9_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions pr0Newpart9Program {s with pc := N 7845, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: x18 :: rest} =
      some (pr0Newpart9Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 19) : rest.length + j < 1024 := by omega
  have ha768 : (768 : W).toNat = 768 := rfl
  have hf768 := Monpro.activeWords_fix s 768 32 (by decide) (by norm_num) hact
  have ha1824 : (1824 : W).toNat = 1824 := rfl
  have hf1824 := Monpro.activeWords_fix s 1824 32 (by decide) (by norm_num) hact
  simp [hz, hzn, pr0Newpart9Program, pr0Newpart9Model, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, capacity, ha768, hf768, ha1824, hf1824]


def pr0Newpart10Program : List Instr :=
  [.push 2 1856,
   .op .MLOAD,
   .op (.Dup dA11),
   .op (.Dup dA1),
   .op (.Dup dA3),
   .op .MULMOD,
   .op (.Swap sA1),
   .op .MUL]

def pr0Newpart10Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 : W) (rest : List W) : State :=
  let v0 : W := MachineState.readWord s.memory 1856
  let v1 : W := UInt256.mulMod x0 v0 x10
  let v2 : W := x0 * v0
  {s with pc := N 7869, memory := s.memory, stack := v2 :: v1 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: rest}

theorem pr0Newpart10_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions pr0Newpart10Program {s with pc := N 7859, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: rest} =
      some (pr0Newpart10Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 21) : rest.length + j < 1024 := by omega
  have ha1856 : (1856 : W).toNat = 1856 := rfl
  have hf1856 := Monpro.activeWords_fix s 1856 32 (by decide) (by norm_num) hact
  simp [hz, hzn, pr0Newpart10Program, pr0Newpart10Model, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, capacity, ha1856, hf1856]


def pr0Newpart11Program : List Instr :=
  [.op (.Dup dA3),
   .op .ADD,
   .op (.Dup dA11),
   .op (.Dup dA3),
   .op (.Dup dA9),
   .op .MULMOD,
   .op (.Swap sA2),
   .op (.Dup dA8)]

def pr0Newpart11Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 : W) (rest : List W) : State :=
  let v0 : W := x3 + x0
  let v1 : W := UInt256.mulMod x7 x2 x11
  {s with pc := N 7877, memory := s.memory, stack := x7 :: x2 :: v0 :: x1 :: v1 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: rest}

theorem pr0Newpart11_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions pr0Newpart11Program {s with pc := N 7869, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: rest} =
      some (pr0Newpart11Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 21) : rest.length + j < 1024 := by omega
  simp [hz, hzn, pr0Newpart11Program, pr0Newpart11Model, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, capacity]


def pr0Newpart12Program : List Instr :=
  [.op .MUL,
   .op .ADD,
   .op (.Swap sA2),
   .op .ADD,
   .op .ADD]

def pr0Newpart12Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 : W) (rest : List W) : State :=
  let v0 : W := x0 * x1
  let v1 : W := v0 + x2
  let v2 : W := x5 + x3
  let v3 : W := v2 + x4
  {s with pc := N 7882, memory := s.memory, stack := v3 :: v1 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: x18 :: x19 :: rest}

theorem pr0Newpart12_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions pr0Newpart12Program {s with pc := N 7877, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: x18 :: x19 :: rest} =
      some (pr0Newpart12Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 20) : rest.length + j < 1024 := by omega
  simp [hz, hzn, pr0Newpart12Program, pr0Newpart12Model, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, capacity]


def pr0NewProgram : List Instr :=
  [.push 2 768,
   .op .MLOAD,
   .op (.Dup dA8),
   .push 2 1792,
   .op .MLOAD,
   .op (.Dup dA0),
   .op (.Dup dA3),
   .op .MUL,
   .push 2 2720,
   .op .MLOAD,
   .op .MUL,
   .op (.Dup dA14),
   .op .AND,
   .op (.Swap sA11),
   .op .POP,
   .op (.Dup dA10),
   .op (.Swap sA2),
   .op .MULMOD,
   .op (.Dup dA1),
   .op (.Dup dA11),
   .op (.Dup dA15),
   .op .MULMOD,
   .op .ADD,
   .push 2 2048,
   .op .MULMOD,
   .op (.Dup dA0),
   .op (.Dup dA9),
   .push 2 768,
   .op .MLOAD,
   .push 2 1824,
   .op .MLOAD,
   .op (.Swap sA3),
   .op (.Dup dA1),
   .op (.Dup dA5),
   .op .MUL,
   .op .ADD,
   .op (.Swap sA3),
   .op .MULMOD,
   .op .ADD,
   .op (.Dup dA9),
   .op (.Dup dA11),
   .op (.Dup dA13),
   .op .MUL,
   .push 2 1792,
   .op .MLOAD,
   .op (.Swap sA3),
   .op .ADD,
   .op (.Dup dA3),
   .op (.Dup dA8),
   .op .MUL,
   .op .ADD,
   .op (.Swap sA2),
   .op (.Dup dA7),
   .op .MULMOD,
   .op .ADD,
   .op (.Dup dA9),
   .op (.Dup dA11),
   .op (.Dup dA13),
   .op .MULMOD,
   .op .ADD,
   .op (.Dup dA9),
   .op (.Dup dA14),
   .push 2 2720,
   .op .MLOAD,
   .op (.Dup dA2),
   .op (.Swap sA4),
   .op .MUL,
   .op (.Dup dA15),
   .op .AND,
   .op (.Dup dA0),
   .op (.Swap sA11),
   .op .POP,
   .op .MULMOD,
   .op .ADD,
   .push 2 2048,
   .op .MULMOD,
   .push 2 1824,
   .op .MLOAD,
   .push 2 768,
   .op .MLOAD,
   .push 2 1856,
   .op .MLOAD,
   .op (.Dup dA11),
   .op (.Dup dA1),
   .op (.Dup dA3),
   .op .MULMOD,
   .op (.Swap sA1),
   .op .MUL,
   .op (.Dup dA3),
   .op .ADD,
   .op (.Dup dA11),
   .op (.Dup dA3),
   .op (.Dup dA9),
   .op .MULMOD,
   .op (.Swap sA2),
   .op (.Dup dA8),
   .op .MUL,
   .op .ADD,
   .op (.Swap sA2),
   .op .ADD,
   .op .ADD]

def pr0NewModel (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 : W) (rest : List W) : State :=
  let v0 : W := MachineState.readWord s.memory 768
  let v1 : W := MachineState.readWord s.memory 1792
  let v2 : W := v0 * v1
  let v3 : W := MachineState.readWord s.memory 2720
  let v4 : W := v3 * v2
  let v5 : W := UInt256.land w10 v4
  let v6 : W := UInt256.mulMod v0 v1 w7
  let v7 : W := UInt256.mulMod w11 v5 w7
  let v8 : W := v7 + v6
  let v9 : W := UInt256.mulMod (N 2048) v8 w7
  let v10 : W := MachineState.readWord s.memory 768
  let v11 : W := MachineState.readWord s.memory 1824
  let v12 : W := v11 * v10
  let v13 : W := v12 + v9
  let v14 : W := UInt256.mulMod v11 v10 w7
  let v15 : W := v14 + v9
  let v16 : W := w9 * v5
  let v17 : W := MachineState.readWord s.memory 1792
  let v18 : W := v13 + v16
  let v19 : W := w3 * v17
  let v20 : W := v19 + v18
  let v21 : W := UInt256.mulMod w3 v17 w7
  let v22 : W := v21 + v15
  let v23 : W := UInt256.mulMod w9 v5 w7
  let v24 : W := v23 + v22
  let v25 : W := MachineState.readWord s.memory 2720
  let v26 : W := v20 * v25
  let v27 : W := UInt256.land w10 v26
  let v28 : W := UInt256.mulMod v27 w11 w7
  let v29 : W := v28 + v24
  let v30 : W := UInt256.mulMod (N 2048) v29 w7
  let v31 : W := MachineState.readWord s.memory 1824
  let v32 : W := MachineState.readWord s.memory 768
  let v33 : W := MachineState.readWord s.memory 1856
  let v34 : W := UInt256.mulMod v32 v33 w7
  let v35 : W := v32 * v33
  let v36 : W := v30 + v35
  let v37 : W := UInt256.mulMod w3 v31 w7
  let v38 : W := w3 * v31
  let v39 : W := v38 + v36
  let v40 : W := v30 + v34
  let v41 : W := v40 + v37
  {s with pc := N 7882, memory := s.memory, stack := v41 :: v39 :: w0 :: w1 :: w2 :: w3 :: w4 :: w5 :: v27 :: w7 :: v5 :: w9 :: w10 :: w11 :: w12 :: w13 :: rest}

theorem pr0New_run (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions pr0NewProgram {s with pc := N 7757, stack := w0 :: w1 :: w2 :: w3 :: w4 :: w5 :: w6 :: w7 :: w8 :: w9 :: w10 :: w11 :: w12 :: w13 :: rest} =
      some (pr0NewModel s w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 rest) := by
  let v0 : W := MachineState.readWord s.memory 768
  let v1 : W := MachineState.readWord s.memory 1792
  let v2 : W := v0 * v1
  let v3 : W := MachineState.readWord s.memory 2720
  let v4 : W := v3 * v2
  let v5 : W := UInt256.land w10 v4
  let v6 : W := UInt256.mulMod v0 v1 w7
  let v7 : W := UInt256.mulMod w11 v5 w7
  let v8 : W := v7 + v6
  let v9 : W := UInt256.mulMod (N 2048) v8 w7
  let v10 : W := MachineState.readWord s.memory 768
  let v11 : W := MachineState.readWord s.memory 1824
  let v12 : W := v11 * v10
  let v13 : W := v12 + v9
  let v14 : W := UInt256.mulMod v11 v10 w7
  let v15 : W := v14 + v9
  let v16 : W := w9 * v5
  let v17 : W := MachineState.readWord s.memory 1792
  let v18 : W := v13 + v16
  let v19 : W := w3 * v17
  let v20 : W := v19 + v18
  let v21 : W := UInt256.mulMod w3 v17 w7
  let v22 : W := v21 + v15
  let v23 : W := UInt256.mulMod w9 v5 w7
  let v24 : W := v23 + v22
  let v25 : W := MachineState.readWord s.memory 2720
  let v26 : W := v20 * v25
  let v27 : W := UInt256.land w10 v26
  let v28 : W := UInt256.mulMod v27 w11 w7
  let v29 : W := v28 + v24
  let v30 : W := UInt256.mulMod (N 2048) v29 w7
  let v31 : W := MachineState.readWord s.memory 1824
  let v32 : W := MachineState.readWord s.memory 768
  let v33 : W := MachineState.readWord s.memory 1856
  let v34 : W := UInt256.mulMod v32 v33 w7
  let v35 : W := v32 * v33
  let v36 : W := v30 + v35
  let v37 : W := UInt256.mulMod w3 v31 w7
  let v38 : W := w3 * v31
  let v39 : W := v38 + v36
  let v40 : W := v30 + v34
  let v41 : W := v40 + v37
  have h0 : runInstructions pr0Newpart0Program {s with pc := N 7757, memory := s.memory, stack := w0 :: w1 :: w2 :: w3 :: w4 :: w5 :: w6 :: w7 :: w8 :: w9 :: w10 :: w11 :: w12 :: w13 :: rest} = some {s with pc := N 7769, memory := s.memory, stack := v2 :: v1 :: w7 :: v0 :: w0 :: w1 :: w2 :: w3 :: w4 :: w5 :: w6 :: w7 :: w8 :: w9 :: w10 :: w11 :: w12 :: w13 :: rest} := by
    simpa only [pr0Newpart0Model, v0, v1, v2] using pr0Newpart0_run (s) (w0) (w1) (w2) (w3) (w4) (w5) (w6) (w7) (w8) (w9) (w10) (w11) (w12) (w13) rest hcap hact
  have h1 : runInstructions pr0Newpart1Program {s with pc := N 7769, memory := s.memory, stack := v2 :: v1 :: w7 :: v0 :: w0 :: w1 :: w2 :: w3 :: w4 :: w5 :: w6 :: w7 :: w8 :: w9 :: w10 :: w11 :: w12 :: w13 :: rest} = some {s with pc := N 7779, memory := s.memory, stack := w7 :: v1 :: w7 :: v0 :: w0 :: w1 :: w2 :: w3 :: w4 :: w5 :: w6 :: w7 :: v5 :: w9 :: w10 :: w11 :: w12 :: w13 :: rest} := by
    simpa only [pr0Newpart1Model, v3, v4, v5] using pr0Newpart1_run (s) (v2) (v1) (w7) (v0) (w0) (w1) (w2) (w3) (w4) (w5) (w6) (w7) (w8) (w9) (w10) (w11) (w12) (w13) rest hcap hact
  have h2 : runInstructions pr0Newpart2Program {s with pc := N 7779, memory := s.memory, stack := w7 :: v1 :: w7 :: v0 :: w0 :: w1 :: w2 :: w3 :: w4 :: w5 :: w6 :: w7 :: v5 :: w9 :: w10 :: w11 :: w12 :: w13 :: rest} = some {s with pc := N 7789, memory := s.memory, stack := (N 2048) :: v8 :: w7 :: w0 :: w1 :: w2 :: w3 :: w4 :: w5 :: w6 :: w7 :: v5 :: w9 :: w10 :: w11 :: w12 :: w13 :: rest} := by
    simpa only [pr0Newpart2Model, v6, v7, v8] using pr0Newpart2_run (s) (w7) (v1) (w7) (v0) (w0) (w1) (w2) (w3) (w4) (w5) (w6) (w7) (v5) (w9) (w10) (w11) (w12) (w13) rest hcap hact
  have h3 : runInstructions pr0Newpart3Program {s with pc := N 7789, memory := s.memory, stack := (N 2048) :: v8 :: w7 :: w0 :: w1 :: w2 :: w3 :: w4 :: w5 :: w6 :: w7 :: v5 :: w9 :: w10 :: w11 :: w12 :: w13 :: rest} = some {s with pc := N 7801, memory := s.memory, stack := v9 :: v10 :: w7 :: v9 :: v11 :: w0 :: w1 :: w2 :: w3 :: w4 :: w5 :: w6 :: w7 :: v5 :: w9 :: w10 :: w11 :: w12 :: w13 :: rest} := by
    simpa only [pr0Newpart3Model, v9, v10, v11] using pr0Newpart3_run (s) ((N 2048)) (v8) (w7) (w0) (w1) (w2) (w3) (w4) (w5) (w6) (w7) (v5) (w9) (w10) (w11) (w12) (w13) rest hcap hact (by rfl)
  have h4 : runInstructions pr0Newpart4Program {s with pc := N 7801, memory := s.memory, stack := v9 :: v10 :: w7 :: v9 :: v11 :: w0 :: w1 :: w2 :: w3 :: w4 :: w5 :: w6 :: w7 :: v5 :: w9 :: w10 :: w11 :: w12 :: w13 :: rest} = some {s with pc := N 7809, memory := s.memory, stack := w7 :: v15 :: v13 :: w0 :: w1 :: w2 :: w3 :: w4 :: w5 :: w6 :: w7 :: v5 :: w9 :: w10 :: w11 :: w12 :: w13 :: rest} := by
    simpa only [pr0Newpart4Model, v12, v13, v14, v15] using pr0Newpart4_run (s) (v9) (v10) (w7) (v9) (v11) (w0) (w1) (w2) (w3) (w4) (w5) (w6) (w7) (v5) (w9) (w10) (w11) (w12) (w13) rest hcap hact
  have h5 : runInstructions pr0Newpart5Program {s with pc := N 7809, memory := s.memory, stack := w7 :: v15 :: v13 :: w0 :: w1 :: w2 :: w3 :: w4 :: w5 :: w6 :: w7 :: v5 :: w9 :: w10 :: w11 :: w12 :: w13 :: rest} = some {s with pc := N 7819, memory := s.memory, stack := v17 :: v18 :: w7 :: v15 :: v17 :: w0 :: w1 :: w2 :: w3 :: w4 :: w5 :: w6 :: w7 :: v5 :: w9 :: w10 :: w11 :: w12 :: w13 :: rest} := by
    simpa only [pr0Newpart5Model, v16, v17, v18] using pr0Newpart5_run (s) (w7) (v15) (v13) (w0) (w1) (w2) (w3) (w4) (w5) (w6) (w7) (v5) (w9) (w10) (w11) (w12) (w13) rest hcap hact
  have h6 : runInstructions pr0Newpart6Program {s with pc := N 7819, memory := s.memory, stack := v17 :: v18 :: w7 :: v15 :: v17 :: w0 :: w1 :: w2 :: w3 :: w4 :: w5 :: w6 :: w7 :: v5 :: w9 :: w10 :: w11 :: w12 :: w13 :: rest} = some {s with pc := N 7827, memory := s.memory, stack := w7 :: v22 :: v20 :: w0 :: w1 :: w2 :: w3 :: w4 :: w5 :: w6 :: w7 :: v5 :: w9 :: w10 :: w11 :: w12 :: w13 :: rest} := by
    simpa only [pr0Newpart6Model, v19, v20, v21, v22] using pr0Newpart6_run (s) (v17) (v18) (w7) (v15) (v17) (w0) (w1) (w2) (w3) (w4) (w5) (w6) (w7) (v5) (w9) (w10) (w11) (w12) (w13) rest hcap hact
  have h7 : runInstructions pr0Newpart7Program {s with pc := N 7827, memory := s.memory, stack := w7 :: v22 :: v20 :: w0 :: w1 :: w2 :: w3 :: w4 :: w5 :: w6 :: w7 :: v5 :: w9 :: w10 :: w11 :: w12 :: w13 :: rest} = some {s with pc := N 7837, memory := s.memory, stack := v25 :: w11 :: w7 :: v24 :: v20 :: w0 :: w1 :: w2 :: w3 :: w4 :: w5 :: w6 :: w7 :: v5 :: w9 :: w10 :: w11 :: w12 :: w13 :: rest} := by
    simpa only [pr0Newpart7Model, v23, v24, v25] using pr0Newpart7_run (s) (w7) (v22) (v20) (w0) (w1) (w2) (w3) (w4) (w5) (w6) (w7) (v5) (w9) (w10) (w11) (w12) (w13) rest hcap hact
  have h8 : runInstructions pr0Newpart8Program {s with pc := N 7837, memory := s.memory, stack := v25 :: w11 :: w7 :: v24 :: v20 :: w0 :: w1 :: w2 :: w3 :: w4 :: w5 :: w6 :: w7 :: v5 :: w9 :: w10 :: w11 :: w12 :: w13 :: rest} = some {s with pc := N 7845, memory := s.memory, stack := v27 :: w11 :: w7 :: v24 :: w7 :: w0 :: w1 :: w2 :: w3 :: w4 :: w5 :: v27 :: w7 :: v5 :: w9 :: w10 :: w11 :: w12 :: w13 :: rest} := by
    simpa only [pr0Newpart8Model, v26, v27] using pr0Newpart8_run (s) (v25) (w11) (w7) (v24) (v20) (w0) (w1) (w2) (w3) (w4) (w5) (w6) (w7) (v5) (w9) (w10) (w11) (w12) (w13) rest hcap hact
  have h9 : runInstructions pr0Newpart9Program {s with pc := N 7845, memory := s.memory, stack := v27 :: w11 :: w7 :: v24 :: w7 :: w0 :: w1 :: w2 :: w3 :: w4 :: w5 :: v27 :: w7 :: v5 :: w9 :: w10 :: w11 :: w12 :: w13 :: rest} = some {s with pc := N 7859, memory := s.memory, stack := v32 :: v31 :: v30 :: w0 :: w1 :: w2 :: w3 :: w4 :: w5 :: v27 :: w7 :: v5 :: w9 :: w10 :: w11 :: w12 :: w13 :: rest} := by
    simpa only [pr0Newpart9Model, v28, v29, v30, v31, v32] using pr0Newpart9_run (s) (v27) (w11) (w7) (v24) (w7) (w0) (w1) (w2) (w3) (w4) (w5) (v27) (w7) (v5) (w9) (w10) (w11) (w12) (w13) rest hcap hact
  have h10 : runInstructions pr0Newpart10Program {s with pc := N 7859, memory := s.memory, stack := v32 :: v31 :: v30 :: w0 :: w1 :: w2 :: w3 :: w4 :: w5 :: v27 :: w7 :: v5 :: w9 :: w10 :: w11 :: w12 :: w13 :: rest} = some {s with pc := N 7869, memory := s.memory, stack := v35 :: v34 :: v31 :: v30 :: w0 :: w1 :: w2 :: w3 :: w4 :: w5 :: v27 :: w7 :: v5 :: w9 :: w10 :: w11 :: w12 :: w13 :: rest} := by
    simpa only [pr0Newpart10Model, v33, v34, v35] using pr0Newpart10_run (s) (v32) (v31) (v30) (w0) (w1) (w2) (w3) (w4) (w5) (v27) (w7) (v5) (w9) (w10) (w11) (w12) (w13) rest hcap hact
  have h11 : runInstructions pr0Newpart11Program {s with pc := N 7869, memory := s.memory, stack := v35 :: v34 :: v31 :: v30 :: w0 :: w1 :: w2 :: w3 :: w4 :: w5 :: v27 :: w7 :: v5 :: w9 :: w10 :: w11 :: w12 :: w13 :: rest} = some {s with pc := N 7877, memory := s.memory, stack := w3 :: v31 :: v36 :: v34 :: v37 :: v30 :: w0 :: w1 :: w2 :: w3 :: w4 :: w5 :: v27 :: w7 :: v5 :: w9 :: w10 :: w11 :: w12 :: w13 :: rest} := by
    simpa only [pr0Newpart11Model, v36, v37] using pr0Newpart11_run (s) (v35) (v34) (v31) (v30) (w0) (w1) (w2) (w3) (w4) (w5) (v27) (w7) (v5) (w9) (w10) (w11) (w12) (w13) rest hcap hact
  have h12 : runInstructions pr0Newpart12Program {s with pc := N 7877, memory := s.memory, stack := w3 :: v31 :: v36 :: v34 :: v37 :: v30 :: w0 :: w1 :: w2 :: w3 :: w4 :: w5 :: v27 :: w7 :: v5 :: w9 :: w10 :: w11 :: w12 :: w13 :: rest} = some {s with pc := N 7882, memory := s.memory, stack := v41 :: v39 :: w0 :: w1 :: w2 :: w3 :: w4 :: w5 :: v27 :: w7 :: v5 :: w9 :: w10 :: w11 :: w12 :: w13 :: rest} := by
    simpa only [pr0Newpart12Model, v38, v39, v40, v41] using pr0Newpart12_run (s) (w3) (v31) (v36) (v34) (v37) (v30) (w0) (w1) (w2) (w3) (w4) (w5) (v27) (w7) (v5) (w9) (w10) (w11) (w12) (w13) rest hcap hact
  exact (runInstructions_append_some _ _ _ _ _ h0 (runInstructions_append_some _ _ _ _ _ h1 (runInstructions_append_some _ _ _ _ _ h2 (runInstructions_append_some _ _ _ _ _ h3 (runInstructions_append_some _ _ _ _ _ h4 (runInstructions_append_some _ _ _ _ _ h5 (runInstructions_append_some _ _ _ _ _ h6 (runInstructions_append_some _ _ _ _ _ h7 (runInstructions_append_some _ _ _ _ _ h8 (runInstructions_append_some _ _ _ _ _ h9 (runInstructions_append_some _ _ _ _ _ h10 (runInstructions_append_some _ _ _ _ _ h11 h12))))))))))))

#print axioms pr0New_run

def productColumn0Model (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 : W) (rest : List W) : State :=
  let v0 : W := MachineState.readWord s.memory 768
  let v1 : W := MachineState.readWord s.memory 1792
  let v2 : W := v0 * v1
  let v3 : W := MachineState.readWord s.memory 2720
  let v4 : W := v3 * v2
  let v5 : W := UInt256.land w10 v4
  let v6 : W := UInt256.mulMod v0 v1 w7
  let v7 : W := UInt256.mulMod w11 v5 w7
  let v8 : W := v7 + v6
  let v9 : W := UInt256.mulMod (N 2048) v8 w7
  let v10 : W := MachineState.readWord s.memory 768
  let v11 : W := MachineState.readWord s.memory 1824
  let v12 : W := v11 * v10
  let v13 : W := v12 + v9
  let v14 : W := UInt256.mulMod v11 v10 w7
  let v15 : W := v14 + v9
  let v16 : W := MachineState.readWord s.memory 1792
  let v17 : W := v16 * w3
  let v18 : W := v17 + v13
  let v19 : W := UInt256.mulMod v16 w3 w7
  let v20 : W := v19 + v15
  let v21 : W := v5 * w9
  let v22 : W := v21 + v18
  let v23 : W := UInt256.mulMod v5 w9 w7
  let v24 : W := v23 + v20
  let v25 : W := MachineState.readWord s.memory 2720
  let v26 : W := v22 * v25
  let v27 : W := UInt256.land w10 v26
  let v28 : W := UInt256.mulMod v27 w11 w7
  let v29 : W := v28 + v24
  let v30 : W := UInt256.mulMod (N 2048) v29 w7
  let v31 : W := MachineState.readWord s.memory 768
  let v32 : W := MachineState.readWord s.memory 1856
  let v33 : W := v32 * v31
  let v34 : W := v33 + v30
  let v35 : W := UInt256.mulMod v32 v31 w7
  let v36 : W := v35 + v30
  let v37 : W := MachineState.readWord s.memory 1824
  let v38 : W := v37 * w3
  let v39 : W := v38 + v34
  let v40 : W := UInt256.mulMod v37 w3 w7
  let v41 : W := v40 + v36
  {s with pc := N 7882, memory := s.memory, stack := v41 :: v39 :: w0 :: w1 :: w2 :: w3 :: w4 :: w5 :: v27 :: w7 :: v5 :: w9 :: w10 :: w11 :: w12 :: w13 :: rest}

def productColumn0Program : List Instr := pr0NewProgram

private theorem aux_shared0 (w9 : W) (z0 : W) :
    (w9 * z0) = (z0 * w9) := by
  simp (disch := decide) only [addC, addA, addL, mulC, mmC, amC, andC, orC, xorC, eqC, read_disjoint, Challenge.EvmProof.Memory.readWord_writeWord]

private theorem aux_shared1 (w3 : W) (z0 : W) :
    (w3 * z0) = (z0 * w3) := by
  simp (disch := decide) only [addC, addA, addL, mulC, mmC, amC, andC, orC, xorC, eqC, read_disjoint, Challenge.EvmProof.Memory.readWord_writeWord]

private theorem aux_shared2 (z0 z1 z2 : W) :
    (z0 + (z1 + z2)) = (z2 + (z0 + z1)) := by
  simp (disch := decide) only [addC, addA, addL, mulC, mmC, amC, andC, orC, xorC, eqC, read_disjoint, Challenge.EvmProof.Memory.readWord_writeWord]

private theorem aux_shared3 (w3 w7 : W) (z0 : W) :
    (UInt256.mulMod w3 z0 w7) = (UInt256.mulMod z0 w3 w7) := by
  simp (disch := decide) only [addC, addA, addL, mulC, mmC, amC, andC, orC, xorC, eqC, read_disjoint, Challenge.EvmProof.Memory.readWord_writeWord]

private theorem aux_shared4 (w7 w9 : W) (z0 : W) :
    (UInt256.mulMod w9 z0 w7) = (UInt256.mulMod z0 w9 w7) := by
  simp (disch := decide) only [addC, addA, addL, mulC, mmC, amC, andC, orC, xorC, eqC, read_disjoint, Challenge.EvmProof.Memory.readWord_writeWord]

private theorem aux_shared5 (w7 : W) (z0 z1 : W) :
    (UInt256.mulMod z0 z1 w7) = (UInt256.mulMod z1 z0 w7) := by
  simp (disch := decide) only [addC, addA, addL, mulC, mmC, amC, andC, orC, xorC, eqC, read_disjoint, Challenge.EvmProof.Memory.readWord_writeWord]

private theorem aux_shared6 (z0 z1 : W) :
    (z0 * z1) = (z1 * z0) := by
  simp (disch := decide) only [addC, addA, addL, mulC, mmC, amC, andC, orC, xorC, eqC, read_disjoint, Challenge.EvmProof.Memory.readWord_writeWord]

private theorem aux_shared7 (z0 z1 : W) :
    (z0 + z1) = (z1 + z0) := by
  simp (disch := decide) only [addC, addA, addL, mulC, mmC, amC, andC, orC, xorC, eqC, read_disjoint, Challenge.EvmProof.Memory.readWord_writeWord]

private theorem prepared_model_eq (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 : W) (rest : List W) :
    productColumn0Model s w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 rest = pr0NewModel s w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 rest := by
  let o0 : W := MachineState.readWord s.memory 768
  let o1 : W := MachineState.readWord s.memory 1792
  let o2 : W := o0 * o1
  let o3 : W := MachineState.readWord s.memory 2720
  let o4 : W := o3 * o2
  let o5 : W := UInt256.land w10 o4
  let o6 : W := UInt256.mulMod o0 o1 w7
  let o7 : W := UInt256.mulMod w11 o5 w7
  let o8 : W := o7 + o6
  let o9 : W := UInt256.mulMod (N 2048) o8 w7
  let o10 : W := MachineState.readWord s.memory 768
  let o11 : W := MachineState.readWord s.memory 1824
  let o12 : W := o11 * o10
  let o13 : W := o12 + o9
  let o14 : W := UInt256.mulMod o11 o10 w7
  let o15 : W := o14 + o9
  let o16 : W := MachineState.readWord s.memory 1792
  let o17 : W := o16 * w3
  let o18 : W := o17 + o13
  let o19 : W := UInt256.mulMod o16 w3 w7
  let o20 : W := o19 + o15
  let o21 : W := o5 * w9
  let o22 : W := o21 + o18
  let o23 : W := UInt256.mulMod o5 w9 w7
  let o24 : W := o23 + o20
  let o25 : W := MachineState.readWord s.memory 2720
  let o26 : W := o22 * o25
  let o27 : W := UInt256.land w10 o26
  let o28 : W := UInt256.mulMod o27 w11 w7
  let o29 : W := o28 + o24
  let o30 : W := UInt256.mulMod (N 2048) o29 w7
  let o31 : W := MachineState.readWord s.memory 768
  let o32 : W := MachineState.readWord s.memory 1856
  let o33 : W := o32 * o31
  let o34 : W := o33 + o30
  let o35 : W := UInt256.mulMod o32 o31 w7
  let o36 : W := o35 + o30
  let o37 : W := MachineState.readWord s.memory 1824
  let o38 : W := o37 * w3
  let o39 : W := o38 + o34
  let o40 : W := UInt256.mulMod o37 w3 w7
  let o41 : W := o40 + o36
  let n0 : W := MachineState.readWord s.memory 768
  let n1 : W := MachineState.readWord s.memory 1792
  let n2 : W := n0 * n1
  let n3 : W := MachineState.readWord s.memory 2720
  let n4 : W := n3 * n2
  let n5 : W := UInt256.land w10 n4
  let n6 : W := UInt256.mulMod n0 n1 w7
  let n7 : W := UInt256.mulMod w11 n5 w7
  let n8 : W := n7 + n6
  let n9 : W := UInt256.mulMod (N 2048) n8 w7
  let n10 : W := MachineState.readWord s.memory 768
  let n11 : W := MachineState.readWord s.memory 1824
  let n12 : W := n11 * n10
  let n13 : W := n12 + n9
  let n14 : W := UInt256.mulMod n11 n10 w7
  let n15 : W := n14 + n9
  let n16 : W := w9 * n5
  let n17 : W := MachineState.readWord s.memory 1792
  let n18 : W := n13 + n16
  let n19 : W := w3 * n17
  let n20 : W := n19 + n18
  let n21 : W := UInt256.mulMod w3 n17 w7
  let n22 : W := n21 + n15
  let n23 : W := UInt256.mulMod w9 n5 w7
  let n24 : W := n23 + n22
  let n25 : W := MachineState.readWord s.memory 2720
  let n26 : W := n20 * n25
  let n27 : W := UInt256.land w10 n26
  let n28 : W := UInt256.mulMod n27 w11 w7
  let n29 : W := n28 + n24
  let n30 : W := UInt256.mulMod (N 2048) n29 w7
  let n31 : W := MachineState.readWord s.memory 1824
  let n32 : W := MachineState.readWord s.memory 768
  let n33 : W := MachineState.readWord s.memory 1856
  let n34 : W := UInt256.mulMod n32 n33 w7
  let n35 : W := n32 * n33
  let n36 : W := n30 + n35
  let n37 : W := UInt256.mulMod w3 n31 w7
  let n38 : W := w3 * n31
  let n39 : W := n38 + n36
  let n40 : W := n30 + n34
  let n41 : W := n40 + n37
  have eq_o10 : o10 = o0 := by
    simp only [o10, o0]
  have eq_o16 : o16 = o1 := by
    simp only [o16, o1]
  have eq_o25 : o25 = o3 := by
    simp only [o25, o3]
  have eq_o31 : o31 = o0 := by
    simp only [o31, o0]
  have eq_o37 : o37 = o11 := by
    simp only [o37, o11]
  have eq_n0 : n0 = o0 := by
    simp only [n0, o0]
  have eq_n1 : n1 = o1 := by
    simp only [n1, o1]
  have eq_n2 : n2 = o2 := by
    simp only [n2, o2, eq_n0, eq_n1]
  have eq_n3 : n3 = o3 := by
    simp only [n3, o3]
  have eq_n4 : n4 = o4 := by
    simp only [n4, o4, eq_n3, eq_n2]
  have eq_n5 : n5 = o5 := by
    simp only [n5, o5, eq_n4]
  have eq_n6 : n6 = o6 := by
    simp only [n6, o6, eq_n0, eq_n1]
  have eq_n7 : n7 = o7 := by
    simp only [n7, o7, eq_n5]
  have eq_n8 : n8 = o8 := by
    simp only [n8, o8, eq_n7, eq_n6]
  have eq_n9 : n9 = o9 := by
    simp only [n9, o9, eq_n8]
  have eq_n10 : n10 = o0 := by
    simp only [n10, o0]
  have eq_n11 : n11 = o11 := by
    simp only [n11, o11]
  have eq_n12 : n12 = o12 := by
    simp only [n12, o12, eq_n11, eq_n10, eq_o10]
  have eq_n13 : n13 = o13 := by
    simp only [n13, o13, eq_n12, eq_n9]
  have eq_n14 : n14 = o14 := by
    simp only [n14, o14, eq_n11, eq_n10, eq_o10]
  have eq_n15 : n15 = o15 := by
    simp only [n15, o15, eq_n14, eq_n9]
  have eq_n16 : n16 = o21 := by
    simpa only [n16, o21, eq_n5] using
      (aux_shared0 w9 o5)
  have eq_n17 : n17 = o1 := by
    simp only [n17, o1]
  have eq_n19 : n19 = o17 := by
    simpa only [n19, o17, eq_n17, eq_o16] using
      (aux_shared1 w3 o1)
  have eq_n20 : n20 = o22 := by
    simpa only [n20, n18, o22, o18, eq_n19, eq_n13, eq_n16] using
      (aux_shared2  o17 o13 o21)
  have eq_n21 : n21 = o19 := by
    simpa only [n21, o19, eq_n17, eq_o16] using
      (aux_shared3 w3 w7 o1)
  have eq_n22 : n22 = o20 := by
    simp only [n22, o20, eq_n21, eq_n15]
  have eq_n23 : n23 = o23 := by
    simpa only [n23, o23, eq_n5] using
      (aux_shared4 w7 w9 o5)
  have eq_n24 : n24 = o24 := by
    simp only [n24, o24, eq_n23, eq_n22]
  have eq_n25 : n25 = o3 := by
    simp only [n25, o3]
  have eq_n26 : n26 = o26 := by
    simp only [n26, o26, eq_n20, eq_n25, eq_o25]
  have eq_n27 : n27 = o27 := by
    simp only [n27, o27, eq_n26]
  have eq_n28 : n28 = o28 := by
    simp only [n28, o28, eq_n27]
  have eq_n29 : n29 = o29 := by
    simp only [n29, o29, eq_n28, eq_n24]
  have eq_n30 : n30 = o30 := by
    simp only [n30, o30, eq_n29]
  have eq_n31 : n31 = o11 := by
    simp only [n31, o11]
  have eq_n32 : n32 = o0 := by
    simp only [n32, o0]
  have eq_n33 : n33 = o32 := by
    simp only [n33, o32]
  have eq_n34 : n34 = o35 := by
    simpa only [n34, o35, eq_n32, eq_n33, eq_o31] using
      (aux_shared5 w7 o0 o32)
  have eq_n35 : n35 = o33 := by
    simpa only [n35, o33, eq_n32, eq_n33, eq_o31] using
      (aux_shared6  o0 o32)
  have eq_n36 : n36 = o34 := by
    simpa only [n36, o34, eq_n30, eq_n35] using
      (aux_shared7  o30 o33)
  have eq_n37 : n37 = o40 := by
    simpa only [n37, o40, eq_n31, eq_o37] using
      (aux_shared3 w3 w7 o11)
  have eq_n38 : n38 = o38 := by
    simpa only [n38, o38, eq_n31, eq_o37] using
      (aux_shared1 w3 o11)
  have eq_n39 : n39 = o39 := by
    simp only [n39, o39, eq_n38, eq_n36]
  have eq_n40 : n40 = o36 := by
    simpa only [n40, o36, eq_n30, eq_n34] using
      (aux_shared7  o30 o35)
  have eq_n41 : n41 = o41 := by
    simpa only [n41, o41, eq_n40, eq_n37] using
      (aux_shared7  o36 o40)
  change {s with pc := N 7882, memory := s.memory, stack := o41 :: o39 :: w0 :: w1 :: w2 :: w3 :: w4 :: w5 :: o27 :: w7 :: o5 :: w9 :: w10 :: w11 :: w12 :: w13 :: rest} =
    {s with pc := N 7882, memory := s.memory, stack := n41 :: n39 :: w0 :: w1 :: w2 :: w3 :: w4 :: w5 :: n27 :: w7 :: n5 :: w9 :: w10 :: w11 :: w12 :: w13 :: rest}
  simp only [eq_o10, eq_o16, eq_o25, eq_o31, eq_o37, eq_n0, eq_n1, eq_n2, eq_n3, eq_n4, eq_n5, eq_n6, eq_n7, eq_n8, eq_n9, eq_n10, eq_n11, eq_n12, eq_n13, eq_n14, eq_n15, eq_n16, eq_n17, eq_n19, eq_n20, eq_n21, eq_n22, eq_n23, eq_n24, eq_n25, eq_n26, eq_n27, eq_n28, eq_n29, eq_n30, eq_n31, eq_n32, eq_n33, eq_n34, eq_n35, eq_n36, eq_n37, eq_n38, eq_n39, eq_n40, eq_n41]
theorem productColumn0_run (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions productColumn0Program {s with pc := N 7757, stack := w0 :: w1 :: w2 :: w3 :: w4 :: w5 :: w6 :: w7 :: w8 :: w9 :: w10 :: w11 :: w12 :: w13 :: rest} =
      some (productColumn0Model s w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 rest) := by
  exact (pr0New_run s w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 rest hcap hact).trans
    (congrArg some (prepared_model_eq s w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 rest).symm)

#print axioms productColumn0_run
end CycleSubmission.Execution
