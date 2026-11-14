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

def pr1Newpart0Program : List Instr :=
  [
  .op (.Dup dA9),
   .op (.Dup dA7),
   .push 2 1792,
   .op .MLOAD,
   .op (.Swap sA3),
   .op (.Dup dA1),
   .op (.Dup dA5),
   .op .MUL]

def pr1Newpart0Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 : W) (rest : List W) : State :=
  let v0 : W := MachineState.readWord s.memory 1792
  let v1 : W := v0 * x6
  {s with pc := N 5849, memory := s.memory, stack := v1 :: x1 :: x6 :: x9 :: x0 :: v0 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: rest}

theorem pr1Newpart0_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions pr1Newpart0Program {s with pc := N 5839, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: rest} =
      some (pr1Newpart0Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 21) : rest.length + j < 1024 := by omega
  have ha1792 : (1792 : W).toNat = 1792 := rfl
  have hf1792 := Monpro.activeWords_fix s 1792 32 (by decide) (by norm_num) hact
  simp [hz, hzn, pr1Newpart0Program, pr1Newpart0Model, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, capacity, ha1792, hf1792]


def pr1Newpart1Program : List Instr :=
  [
  .op .ADD,
   .op (.Dup dA5),
   .op (.Dup dA14),
   .op .MUL,
   .op .ADD,
   .op (.Dup dA11),
   .op (.Dup dA15),
   .op .MUL]

def pr1Newpart1Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 : W) (rest : List W) : State :=
  let v0 : W := x0 + x1
  let v1 : W := x14 * x6
  let v2 : W := v1 + v0
  let v3 : W := x15 * x12
  {s with pc := N 5857, memory := s.memory, stack := v3 :: v2 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: x18 :: x19 :: rest}

theorem pr1Newpart1_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions pr1Newpart1Program {s with pc := N 5849, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: x18 :: x19 :: rest} =
      some (pr1Newpart1Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 21) : rest.length + j < 1024 := by omega
  simp [hz, hzn, pr1Newpart1Program, pr1Newpart1Model, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, capacity]


def pr1Newpart2Program : List Instr :=
  [
  .op .ADD,
   .op (.Swap sA3),
   .op .MULMOD,
   .op .ADD,
   .op (.Dup dA9),
   .op (.Dup dA3),
   .op (.Dup dA12),
   .op .MULMOD]

def pr1Newpart2Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 : W) (rest : List W) : State :=
  let v0 : W := x0 + x1
  let v1 : W := UInt256.mulMod x5 x2 x3
  let v2 : W := v1 + x4
  let v3 : W := UInt256.mulMod x14 x6 x13
  {s with pc := N 5865, memory := s.memory, stack := v3 :: v2 :: v0 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: x18 :: x19 :: rest}

theorem pr1Newpart2_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions pr1Newpart2Program {s with pc := N 5857, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: x18 :: x19 :: rest} =
      some (pr1Newpart2Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 20) : rest.length + j < 1024 := by omega
  simp [hz, hzn, pr1Newpart2Program, pr1Newpart2Model, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, capacity]


def pr1Newpart3Program : List Instr :=
  [
  .op .ADD,
   .op (.Dup dA9),
   .op (.Dup dA9),
   .op (.Dup dA13),
   .op .MULMOD,
   .op .ADD,
   .op (.Dup dA9),
   .op (.Dup dA14)]

def pr1Newpart3Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 : W) (rest : List W) : State :=
  let v0 : W := x0 + x1
  let v1 : W := UInt256.mulMod x12 x9 x10
  let v2 : W := v1 + v0
  {s with pc := N 5873, memory := s.memory, stack := x14 :: x10 :: v2 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: rest}

theorem pr1Newpart3_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions pr1Newpart3Program {s with pc := N 5865, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: rest} =
      some (pr1Newpart3Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 19) : rest.length + j < 1024 := by omega
  simp [hz, hzn, pr1Newpart3Program, pr1Newpart3Model, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, capacity]


def pr1Newpart4Program : List Instr :=
  [
  .push 2 2720,
   .op .MLOAD,
   .op (.Dup dA2),
   .op (.Swap sA4),
   .op .MUL,
   .op (.Dup dA15),
   .op .AND,
   .op (.Dup dA0)]

def pr1Newpart4Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 : W) (rest : List W) : State :=
  let v0 : W := MachineState.readWord s.memory 2720
  let v1 : W := x3 * v0
  let v2 : W := UInt256.land x14 v1
  {s with pc := N 5883, memory := s.memory, stack := v2 :: v2 :: x0 :: x1 :: x2 :: x1 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: rest}

theorem pr1Newpart4_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions pr1Newpart4Program {s with pc := N 5873, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: rest} =
      some (pr1Newpart4Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 20) : rest.length + j < 1024 := by omega
  have ha2720 : (2720 : W).toNat = 2720 := rfl
  have hf2720 := Monpro.activeWords_fix s 2720 32 (by decide) (by norm_num) hact
  simp [hz, hzn, pr1Newpart4Program, pr1Newpart4Model, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, capacity, ha2720, hf2720]


def pr1Newpart5Program : List Instr :=
  [
  .push 1 192,
   .op .MSTORE,
   .op .MULMOD,
   .op .ADD,
   .push 2 2048,
   .op .MULMOD,
   .push 2 1856,
   .op .MLOAD]

def pr1Newpart5Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 : W) (rest : List W) : State :=
  let v0 : ByteArray := MachineState.writeBytes s.memory (Data.Bytes.natToBytesPadded x0.toNat 32) 192
  let v1 : W := UInt256.mulMod x1 x2 x3
  let v2 : W := v1 + x4
  let v3 : W := UInt256.mulMod (N 2048) v2 x5
  let v4 : W := MachineState.readWord v0 1856
  {s with pc := N 5896, memory := v0, stack := v4 :: v3 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: x18 :: x19 :: rest}

theorem pr1Newpart5_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions pr1Newpart5Program {s with pc := N 5883, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: x18 :: x19 :: rest} =
      some (pr1Newpart5Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 21) : rest.length + j < 1024 := by omega
  have ha192 : (192 : W).toNat = 192 := rfl
  have hf192 := Monpro.activeWords_fix s 192 32 (by decide) (by norm_num) hact
  have ha1856 : (1856 : W).toNat = 1856 := rfl
  have hf1856 := Monpro.activeWords_fix s 1856 32 (by decide) (by norm_num) hact
  simp [hz, hzn, pr1Newpart5Program, pr1Newpart5Model, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, capacity, ha192, hf192, ha1856, hf1856]


def pr1Newpart6Program : List Instr :=
  [
  .push 2 768,
   .op .MLOAD,
   .push 2 1888,
   .op .MLOAD,
   .op (.Dup dA11),
   .op (.Dup dA1),
   .op (.Dup dA3),
   .op .MULMOD]

def pr1Newpart6Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 : W) (rest : List W) : State :=
  let v0 : W := MachineState.readWord s.memory 768
  let v1 : W := MachineState.readWord s.memory 1888
  let v2 : W := UInt256.mulMod v0 v1 x9
  {s with pc := N 5908, memory := s.memory, stack := v2 :: v1 :: v0 :: x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: rest}

theorem pr1Newpart6_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions pr1Newpart6Program {s with pc := N 5896, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: rest} =
      some (pr1Newpart6Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 21) : rest.length + j < 1024 := by omega
  have ha768 : (768 : W).toNat = 768 := rfl
  have hf768 := Monpro.activeWords_fix s 768 32 (by decide) (by norm_num) hact
  have ha1888 : (1888 : W).toNat = 1888 := rfl
  have hf1888 := Monpro.activeWords_fix s 1888 32 (by decide) (by norm_num) hact
  simp [hz, hzn, pr1Newpart6Program, pr1Newpart6Model, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, capacity, ha768, hf768, ha1888, hf1888]


def pr1Newpart7Program : List Instr :=
  [
  .op (.Swap sA1),
   .op .MUL,
   .op (.Dup dA3),
   .op .ADD,
   .op (.Dup dA11),
   .op (.Dup dA3),
   .op (.Dup dA9),
   .op .MULMOD]

def pr1Newpart7Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 : W) (rest : List W) : State :=
  let v0 : W := x2 * x1
  let v1 : W := x4 + v0
  let v2 : W := UInt256.mulMod x8 x3 x12
  {s with pc := N 5916, memory := s.memory, stack := v2 :: v1 :: x0 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: x18 :: rest}

theorem pr1Newpart7_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions pr1Newpart7Program {s with pc := N 5908, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: x18 :: rest} =
      some (pr1Newpart7Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 21) : rest.length + j < 1024 := by omega
  simp [hz, hzn, pr1Newpart7Program, pr1Newpart7Model, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, capacity]


def pr1Newpart8Program : List Instr :=
  [
  .op (.Swap sA2),
   .op (.Dup dA8),
   .op .MUL,
   .op .ADD,
   .op (.Swap sA2),
   .op .ADD,
   .op .ADD,
   .push 1 32,
   .op .MLOAD]

def pr1Newpart8Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 : W) (rest : List W) : State :=
  let v0 : W := x8 * x3
  let v1 : W := v0 + x1
  let v2 : W := x4 + x2
  let v3 : W := v2 + x0
  let v4 : W := MachineState.readWord s.memory 32
  {s with pc := N 5926, memory := s.memory, stack := v4 :: v3 :: v1 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: x18 :: rest}

theorem pr1Newpart8_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions pr1Newpart8Program {s with pc := N 5916, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: x18 :: rest} =
      some (pr1Newpart8Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 20) : rest.length + j < 1024 := by omega
  have ha32 : (32 : W).toNat = 32 := rfl
  have hf32 := Monpro.activeWords_fix s 32 32 (by decide) (by norm_num) hact
  simp [hz, hzn, pr1Newpart8Program, pr1Newpart8Model, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, capacity, ha32, hf32]


def pr1Newpart9Program : List Instr :=
  [
  .push 2 1824,
   .op .MLOAD,
   .op (.Dup dA11),
   .op (.Dup dA1),
   .op (.Dup dA10),
   .op .MULMOD,
   .push 2 1792,
   .op .MLOAD]

def pr1Newpart9Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 : W) (rest : List W) : State :=
  let v0 : W := MachineState.readWord s.memory 1824
  let v1 : W := UInt256.mulMod x7 v0 x10
  let v2 : W := MachineState.readWord s.memory 1792
  {s with pc := N 5938, memory := s.memory, stack := v2 :: v1 :: v0 :: x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: rest}

theorem pr1Newpart9_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions pr1Newpart9Program {s with pc := N 5926, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: rest} =
      some (pr1Newpart9Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 21) : rest.length + j < 1024 := by omega
  have ha1792 : (1792 : W).toNat = 1792 := rfl
  have hf1792 := Monpro.activeWords_fix s 1792 32 (by decide) (by norm_num) hact
  have ha1824 : (1824 : W).toNat = 1824 := rfl
  have hf1824 := Monpro.activeWords_fix s 1824 32 (by decide) (by norm_num) hact
  simp [hz, hzn, pr1Newpart9Program, pr1Newpart9Model, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, capacity, ha1792, hf1792, ha1824, hf1824]


def pr1Newpart10Program : List Instr :=
  [
  .op (.Dup dA13),
   .op (.Dup dA1),
   .op (.Dup dA5),
   .op .MULMOD,
   .op (.Swap sA2),
   .op (.Dup dA11),
   .op .MUL,
   .op (.Swap sA3)]

def pr1Newpart10Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 : W) (rest : List W) : State :=
  let v0 : W := UInt256.mulMod x3 x0 x13
  let v1 : W := x10 * x2
  {s with pc := N 5946, memory := s.memory, stack := x3 :: x0 :: x1 :: v0 :: v1 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: x18 :: x19 :: rest}

theorem pr1Newpart10_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions pr1Newpart10Program {s with pc := N 5938, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: x18 :: x19 :: rest} =
      some (pr1Newpart10Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 23) : rest.length + j < 1024 := by omega
  simp [hz, hzn, pr1Newpart10Program, pr1Newpart10Model, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, capacity]


def pr1Newpart11Program : List Instr :=
  [
  .op .MUL,
   .op (.Swap sA3),
   .op .ADD,
   .op .ADD,
   .op (.Swap sA2),
   .op .ADD,
   .op .ADD,
   .op (.Dup dA14)]

def pr1Newpart11Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 : W) (rest : List W) : State :=
  let v0 : W := x0 * x1
  let v1 : W := x5 + x2
  let v2 : W := v1 + x3
  let v3 : W := x6 + x4
  let v4 : W := v3 + v0
  {s with pc := N 5954, memory := s.memory, stack := x19 :: v4 :: v2 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: x18 :: x19 :: x20 :: rest}

theorem pr1Newpart11_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions pr1Newpart11Program {s with pc := N 5946, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: x18 :: x19 :: x20 :: rest} =
      some (pr1Newpart11Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 21) : rest.length + j < 1024 := by omega
  simp [hz, hzn, pr1Newpart11Program, pr1Newpart11Model, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, capacity]


def pr1Newpart12Program : List Instr :=
  [
  .op (.Dup dA11),
   .op .MUL,
   .op .ADD,
   .op (.Dup dA2),
   .op (.Dup dA9),
   .op .MUL,
   .op .ADD,
   .op (.Dup dA11)]

def pr1Newpart12Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 : W) (rest : List W) : State :=
  let v0 : W := x11 * x0
  let v1 : W := v0 + x1
  let v2 : W := x9 * x3
  let v3 : W := v2 + v1
  {s with pc := N 5962, memory := s.memory, stack := x12 :: v3 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: rest}

theorem pr1Newpart12_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions pr1Newpart12Program {s with pc := N 5954, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: rest} =
      some (pr1Newpart12Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 18) : rest.length + j < 1024 := by omega
  simp [hz, hzn, pr1Newpart12Program, pr1Newpart12Model, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, capacity]


def pr1Newpart13Program : List Instr :=
  [
  .push 1 192,
   .op .MLOAD]

def pr1Newpart13Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 : W) (rest : List W) : State :=
  let v0 : W := MachineState.readWord s.memory 192
  {s with pc := N 5965, memory := s.memory, stack := v0 :: x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: rest}

theorem pr1Newpart13_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions pr1Newpart13Program {s with pc := N 5962, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: rest} =
      some (pr1Newpart13Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 18) : rest.length + j < 1024 := by omega
  have ha192 : (192 : W).toNat = 192 := rfl
  have hf192 := Monpro.activeWords_fix s 192 32 (by decide) (by norm_num) hact
  simp [hz, hzn, pr1Newpart13Program, pr1Newpart13Model, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, capacity, ha192, hf192]


def pr1NewProgram : List Instr :=
  [
  .op (.Dup dA9),
   .op (.Dup dA7),
   .push 2 1792,
   .op .MLOAD,
   .op (.Swap sA3),
   .op (.Dup dA1),
   .op (.Dup dA5),
   .op .MUL,
   .op .ADD,
   .op (.Dup dA5),
   .op (.Dup dA14),
   .op .MUL,
   .op .ADD,
   .op (.Dup dA11),
   .op (.Dup dA15),
   .op .MUL,
   .op .ADD,
   .op (.Swap sA3),
   .op .MULMOD,
   .op .ADD,
   .op (.Dup dA9),
   .op (.Dup dA3),
   .op (.Dup dA12),
   .op .MULMOD,
   .op .ADD,
   .op (.Dup dA9),
   .op (.Dup dA9),
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
   .push 1 192,
   .op .MSTORE,
   .op .MULMOD,
   .op .ADD,
   .push 2 2048,
   .op .MULMOD,
   .push 2 1856,
   .op .MLOAD,
   .push 2 768,
   .op .MLOAD,
   .push 2 1888,
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
   .op .ADD,
   .push 1 32,
   .op .MLOAD,
   .push 2 1824,
   .op .MLOAD,
   .op (.Dup dA11),
   .op (.Dup dA1),
   .op (.Dup dA10),
   .op .MULMOD,
   .push 2 1792,
   .op .MLOAD,
   .op (.Dup dA13),
   .op (.Dup dA1),
   .op (.Dup dA5),
   .op .MULMOD,
   .op (.Swap sA2),
   .op (.Dup dA11),
   .op .MUL,
   .op (.Swap sA3),
   .op .MUL,
   .op (.Swap sA3),
   .op .ADD,
   .op .ADD,
   .op (.Swap sA2),
   .op .ADD,
   .op .ADD,
   .op (.Dup dA14),
   .op (.Dup dA11),
   .op .MUL,
   .op .ADD,
   .op (.Dup dA2),
   .op (.Dup dA9),
   .op .MUL,
   .op .ADD,
   .op (.Dup dA11),
   .push 1 192,
   .op .MLOAD]

def pr1NewModel (s : State) (carry w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 : W) (rest : List W) : State :=
  let v0 : W := MachineState.readWord s.memory 1792
  let v1 : W := v0 * w5
  let v2 : W := v1 + w0
  let v3 : W := w9 * w1
  let v4 : W := v3 + v2
  let v5 : W := w10 * w7
  let v6 : W := v5 + v4
  let v7 : W := UInt256.mulMod v0 w5 w8
  let v8 : W := v7 + carry
  let v9 : W := UInt256.mulMod w9 w1 w8
  let v10 : W := v9 + v8
  let v11 : W := UInt256.mulMod w10 w7 w8
  let v12 : W := v11 + v10
  let v13 : W := MachineState.readWord s.memory 2720
  let v14 : W := v6 * v13
  let v15 : W := UInt256.land w11 v14
  let v16 : ByteArray := MachineState.writeBytes s.memory (Data.Bytes.natToBytesPadded v15.toNat 32) 192
  let v17 : W := UInt256.mulMod v15 w12 w8
  let v18 : W := v17 + v12
  let v19 : W := UInt256.mulMod (N 2048) v18 w8
  let v20 : W := MachineState.readWord v16 1856
  let v21 : W := MachineState.readWord v16 768
  let v22 : W := MachineState.readWord v16 1888
  let v23 : W := UInt256.mulMod v21 v22 w8
  let v24 : W := v21 * v22
  let v25 : W := v19 + v24
  let v26 : W := UInt256.mulMod w4 v20 w8
  let v27 : W := w4 * v20
  let v28 : W := v27 + v25
  let v29 : W := v19 + v23
  let v30 : W := v29 + v26
  let v31 : W := MachineState.readWord v16 32
  let v32 : W := MachineState.readWord v16 1824
  let v33 : W := UInt256.mulMod w5 v32 w8
  let v34 : W := MachineState.readWord v16 1792
  let v35 : W := UInt256.mulMod v31 v34 w8
  let v36 : W := w5 * v32
  let v37 : W := v31 * v34
  let v38 : W := v30 + v33
  let v39 : W := v38 + v35
  let v40 : W := v28 + v36
  let v41 : W := v40 + v37
  let v42 : W := w9 * w13
  let v43 : W := v42 + v41
  let v44 : W := w7 * w1
  let v45 : W := v44 + v43
  let v46 : W := MachineState.readWord v16 192
  {s with pc := N 5965, memory := v16, stack := v46 :: w10 :: v45 :: v39 :: w1 :: w2 :: w3 :: w4 :: w5 :: w6 :: w7 :: w8 :: w9 :: w10 :: w11 :: w12 :: w13 :: w14 :: rest}

theorem pr1New_run (s : State) (carry w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions pr1NewProgram {s with pc := N 5839, stack := carry :: w0 :: w1 :: w2 :: w3 :: w4 :: w5 :: w6 :: w7 :: w8 :: w9 :: w10 :: w11 :: w12 :: w13 :: w14 :: rest} =
      some (pr1NewModel s carry w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 rest) := by
  let v0 : W := MachineState.readWord s.memory 1792
  let v1 : W := v0 * w5
  let v2 : W := v1 + w0
  let v3 : W := w9 * w1
  let v4 : W := v3 + v2
  let v5 : W := w10 * w7
  let v6 : W := v5 + v4
  let v7 : W := UInt256.mulMod v0 w5 w8
  let v8 : W := v7 + carry
  let v9 : W := UInt256.mulMod w9 w1 w8
  let v10 : W := v9 + v8
  let v11 : W := UInt256.mulMod w10 w7 w8
  let v12 : W := v11 + v10
  let v13 : W := MachineState.readWord s.memory 2720
  let v14 : W := v6 * v13
  let v15 : W := UInt256.land w11 v14
  let v16 : ByteArray := MachineState.writeBytes s.memory (Data.Bytes.natToBytesPadded v15.toNat 32) 192
  let v17 : W := UInt256.mulMod v15 w12 w8
  let v18 : W := v17 + v12
  let v19 : W := UInt256.mulMod (N 2048) v18 w8
  let v20 : W := MachineState.readWord v16 1856
  let v21 : W := MachineState.readWord v16 768
  let v22 : W := MachineState.readWord v16 1888
  let v23 : W := UInt256.mulMod v21 v22 w8
  let v24 : W := v21 * v22
  let v25 : W := v19 + v24
  let v26 : W := UInt256.mulMod w4 v20 w8
  let v27 : W := w4 * v20
  let v28 : W := v27 + v25
  let v29 : W := v19 + v23
  let v30 : W := v29 + v26
  let v31 : W := MachineState.readWord v16 32
  let v32 : W := MachineState.readWord v16 1824
  let v33 : W := UInt256.mulMod w5 v32 w8
  let v34 : W := MachineState.readWord v16 1792
  let v35 : W := UInt256.mulMod v31 v34 w8
  let v36 : W := w5 * v32
  let v37 : W := v31 * v34
  let v38 : W := v30 + v33
  let v39 : W := v38 + v35
  let v40 : W := v28 + v36
  let v41 : W := v40 + v37
  let v42 : W := w9 * w13
  let v43 : W := v42 + v41
  let v44 : W := w7 * w1
  let v45 : W := v44 + v43
  let v46 : W := MachineState.readWord v16 192
  have h0 : runInstructions pr1Newpart0Program {s with pc := N 5839, memory := s.memory, stack := carry :: w0 :: w1 :: w2 :: w3 :: w4 :: w5 :: w6 :: w7 :: w8 :: w9 :: w10 :: w11 :: w12 :: w13 :: w14 :: rest} = some {s with pc := N 5849, memory := s.memory, stack := v1 :: w0 :: w5 :: w8 :: carry :: v0 :: w1 :: w2 :: w3 :: w4 :: w5 :: w6 :: w7 :: w8 :: w9 :: w10 :: w11 :: w12 :: w13 :: w14 :: rest} := by
    simpa only [pr1Newpart0Model, v0, v1] using pr1Newpart0_run (s) (carry) (w0) (w1) (w2) (w3) (w4) (w5) (w6) (w7) (w8) (w9) (w10) (w11) (w12) (w13) (w14) rest hcap hact
  have h1 : runInstructions pr1Newpart1Program {s with pc := N 5849, memory := s.memory, stack := v1 :: w0 :: w5 :: w8 :: carry :: v0 :: w1 :: w2 :: w3 :: w4 :: w5 :: w6 :: w7 :: w8 :: w9 :: w10 :: w11 :: w12 :: w13 :: w14 :: rest} = some {s with pc := N 5857, memory := s.memory, stack := v5 :: v4 :: w5 :: w8 :: carry :: v0 :: w1 :: w2 :: w3 :: w4 :: w5 :: w6 :: w7 :: w8 :: w9 :: w10 :: w11 :: w12 :: w13 :: w14 :: rest} := by
    simpa only [pr1Newpart1Model, v2, v3, v4, v5] using pr1Newpart1_run (s) (v1) (w0) (w5) (w8) (carry) (v0) (w1) (w2) (w3) (w4) (w5) (w6) (w7) (w8) (w9) (w10) (w11) (w12) (w13) (w14) rest hcap hact
  have h2 : runInstructions pr1Newpart2Program {s with pc := N 5857, memory := s.memory, stack := v5 :: v4 :: w5 :: w8 :: carry :: v0 :: w1 :: w2 :: w3 :: w4 :: w5 :: w6 :: w7 :: w8 :: w9 :: w10 :: w11 :: w12 :: w13 :: w14 :: rest} = some {s with pc := N 5865, memory := s.memory, stack := v9 :: v8 :: v6 :: w1 :: w2 :: w3 :: w4 :: w5 :: w6 :: w7 :: w8 :: w9 :: w10 :: w11 :: w12 :: w13 :: w14 :: rest} := by
    simpa only [pr1Newpart2Model, v6, v7, v8, v9] using pr1Newpart2_run (s) (v5) (v4) (w5) (w8) (carry) (v0) (w1) (w2) (w3) (w4) (w5) (w6) (w7) (w8) (w9) (w10) (w11) (w12) (w13) (w14) rest hcap hact
  have h3 : runInstructions pr1Newpart3Program {s with pc := N 5865, memory := s.memory, stack := v9 :: v8 :: v6 :: w1 :: w2 :: w3 :: w4 :: w5 :: w6 :: w7 :: w8 :: w9 :: w10 :: w11 :: w12 :: w13 :: w14 :: rest} = some {s with pc := N 5873, memory := s.memory, stack := w12 :: w8 :: v12 :: v6 :: w1 :: w2 :: w3 :: w4 :: w5 :: w6 :: w7 :: w8 :: w9 :: w10 :: w11 :: w12 :: w13 :: w14 :: rest} := by
    simpa only [pr1Newpart3Model, v10, v11, v12] using pr1Newpart3_run (s) (v9) (v8) (v6) (w1) (w2) (w3) (w4) (w5) (w6) (w7) (w8) (w9) (w10) (w11) (w12) (w13) (w14) rest hcap hact
  have h4 : runInstructions pr1Newpart4Program {s with pc := N 5873, memory := s.memory, stack := w12 :: w8 :: v12 :: v6 :: w1 :: w2 :: w3 :: w4 :: w5 :: w6 :: w7 :: w8 :: w9 :: w10 :: w11 :: w12 :: w13 :: w14 :: rest} = some {s with pc := N 5883, memory := s.memory, stack := v15 :: v15 :: w12 :: w8 :: v12 :: w8 :: w1 :: w2 :: w3 :: w4 :: w5 :: w6 :: w7 :: w8 :: w9 :: w10 :: w11 :: w12 :: w13 :: w14 :: rest} := by
    simpa only [pr1Newpart4Model, v13, v14, v15] using pr1Newpart4_run (s) (w12) (w8) (v12) (v6) (w1) (w2) (w3) (w4) (w5) (w6) (w7) (w8) (w9) (w10) (w11) (w12) (w13) (w14) rest hcap hact
  have h5 : runInstructions pr1Newpart5Program {s with pc := N 5883, memory := s.memory, stack := v15 :: v15 :: w12 :: w8 :: v12 :: w8 :: w1 :: w2 :: w3 :: w4 :: w5 :: w6 :: w7 :: w8 :: w9 :: w10 :: w11 :: w12 :: w13 :: w14 :: rest} = some {s with pc := N 5896, memory := v16, stack := v20 :: v19 :: w1 :: w2 :: w3 :: w4 :: w5 :: w6 :: w7 :: w8 :: w9 :: w10 :: w11 :: w12 :: w13 :: w14 :: rest} := by
    simpa only [pr1Newpart5Model, v16, v17, v18, v19, v20] using pr1Newpart5_run (s) (v15) (v15) (w12) (w8) (v12) (w8) (w1) (w2) (w3) (w4) (w5) (w6) (w7) (w8) (w9) (w10) (w11) (w12) (w13) (w14) rest hcap hact
  have h6 : runInstructions pr1Newpart6Program {s with pc := N 5896, memory := v16, stack := v20 :: v19 :: w1 :: w2 :: w3 :: w4 :: w5 :: w6 :: w7 :: w8 :: w9 :: w10 :: w11 :: w12 :: w13 :: w14 :: rest} = some {s with pc := N 5908, memory := v16, stack := v23 :: v22 :: v21 :: v20 :: v19 :: w1 :: w2 :: w3 :: w4 :: w5 :: w6 :: w7 :: w8 :: w9 :: w10 :: w11 :: w12 :: w13 :: w14 :: rest} := by
    simpa only [pr1Newpart6Model, v21, v22, v23] using pr1Newpart6_run ({s with memory := v16}) (v20) (v19) (w1) (w2) (w3) (w4) (w5) (w6) (w7) (w8) (w9) (w10) (w11) (w12) (w13) (w14) rest hcap hact
  have h7 : runInstructions pr1Newpart7Program {s with pc := N 5908, memory := v16, stack := v23 :: v22 :: v21 :: v20 :: v19 :: w1 :: w2 :: w3 :: w4 :: w5 :: w6 :: w7 :: w8 :: w9 :: w10 :: w11 :: w12 :: w13 :: w14 :: rest} = some {s with pc := N 5916, memory := v16, stack := v26 :: v25 :: v23 :: v20 :: v19 :: w1 :: w2 :: w3 :: w4 :: w5 :: w6 :: w7 :: w8 :: w9 :: w10 :: w11 :: w12 :: w13 :: w14 :: rest} := by
    simpa only [pr1Newpart7Model, v24, v25, v26] using pr1Newpart7_run ({s with memory := v16}) (v23) (v22) (v21) (v20) (v19) (w1) (w2) (w3) (w4) (w5) (w6) (w7) (w8) (w9) (w10) (w11) (w12) (w13) (w14) rest hcap hact
  have h8 : runInstructions pr1Newpart8Program {s with pc := N 5916, memory := v16, stack := v26 :: v25 :: v23 :: v20 :: v19 :: w1 :: w2 :: w3 :: w4 :: w5 :: w6 :: w7 :: w8 :: w9 :: w10 :: w11 :: w12 :: w13 :: w14 :: rest} = some {s with pc := N 5926, memory := v16, stack := v31 :: v30 :: v28 :: w1 :: w2 :: w3 :: w4 :: w5 :: w6 :: w7 :: w8 :: w9 :: w10 :: w11 :: w12 :: w13 :: w14 :: rest} := by
    simpa only [pr1Newpart8Model, v27, v28, v29, v30, v31] using pr1Newpart8_run ({s with memory := v16}) (v26) (v25) (v23) (v20) (v19) (w1) (w2) (w3) (w4) (w5) (w6) (w7) (w8) (w9) (w10) (w11) (w12) (w13) (w14) rest hcap hact
  have h9 : runInstructions pr1Newpart9Program {s with pc := N 5926, memory := v16, stack := v31 :: v30 :: v28 :: w1 :: w2 :: w3 :: w4 :: w5 :: w6 :: w7 :: w8 :: w9 :: w10 :: w11 :: w12 :: w13 :: w14 :: rest} = some {s with pc := N 5938, memory := v16, stack := v34 :: v33 :: v32 :: v31 :: v30 :: v28 :: w1 :: w2 :: w3 :: w4 :: w5 :: w6 :: w7 :: w8 :: w9 :: w10 :: w11 :: w12 :: w13 :: w14 :: rest} := by
    simpa only [pr1Newpart9Model, v32, v33, v34] using pr1Newpart9_run ({s with memory := v16}) (v31) (v30) (v28) (w1) (w2) (w3) (w4) (w5) (w6) (w7) (w8) (w9) (w10) (w11) (w12) (w13) (w14) rest hcap hact
  have h10 : runInstructions pr1Newpart10Program {s with pc := N 5938, memory := v16, stack := v34 :: v33 :: v32 :: v31 :: v30 :: v28 :: w1 :: w2 :: w3 :: w4 :: w5 :: w6 :: w7 :: w8 :: w9 :: w10 :: w11 :: w12 :: w13 :: w14 :: rest} = some {s with pc := N 5946, memory := v16, stack := v31 :: v34 :: v33 :: v35 :: v36 :: v30 :: v28 :: w1 :: w2 :: w3 :: w4 :: w5 :: w6 :: w7 :: w8 :: w9 :: w10 :: w11 :: w12 :: w13 :: w14 :: rest} := by
    simpa only [pr1Newpart10Model, v35, v36] using pr1Newpart10_run ({s with memory := v16}) (v34) (v33) (v32) (v31) (v30) (v28) (w1) (w2) (w3) (w4) (w5) (w6) (w7) (w8) (w9) (w10) (w11) (w12) (w13) (w14) rest hcap hact
  have h11 : runInstructions pr1Newpart11Program {s with pc := N 5946, memory := v16, stack := v31 :: v34 :: v33 :: v35 :: v36 :: v30 :: v28 :: w1 :: w2 :: w3 :: w4 :: w5 :: w6 :: w7 :: w8 :: w9 :: w10 :: w11 :: w12 :: w13 :: w14 :: rest} = some {s with pc := N 5954, memory := v16, stack := w13 :: v41 :: v39 :: w1 :: w2 :: w3 :: w4 :: w5 :: w6 :: w7 :: w8 :: w9 :: w10 :: w11 :: w12 :: w13 :: w14 :: rest} := by
    simpa only [pr1Newpart11Model, v37, v38, v39, v40, v41] using pr1Newpart11_run ({s with memory := v16}) (v31) (v34) (v33) (v35) (v36) (v30) (v28) (w1) (w2) (w3) (w4) (w5) (w6) (w7) (w8) (w9) (w10) (w11) (w12) (w13) (w14) rest hcap hact
  have h12 : runInstructions pr1Newpart12Program {s with pc := N 5954, memory := v16, stack := w13 :: v41 :: v39 :: w1 :: w2 :: w3 :: w4 :: w5 :: w6 :: w7 :: w8 :: w9 :: w10 :: w11 :: w12 :: w13 :: w14 :: rest} = some {s with pc := N 5962, memory := v16, stack := w10 :: v45 :: v39 :: w1 :: w2 :: w3 :: w4 :: w5 :: w6 :: w7 :: w8 :: w9 :: w10 :: w11 :: w12 :: w13 :: w14 :: rest} := by
    simpa only [pr1Newpart12Model, v42, v43, v44, v45] using pr1Newpart12_run ({s with memory := v16}) (w13) (v41) (v39) (w1) (w2) (w3) (w4) (w5) (w6) (w7) (w8) (w9) (w10) (w11) (w12) (w13) (w14) rest hcap hact
  have h13 : runInstructions pr1Newpart13Program {s with pc := N 5962, memory := v16, stack := w10 :: v45 :: v39 :: w1 :: w2 :: w3 :: w4 :: w5 :: w6 :: w7 :: w8 :: w9 :: w10 :: w11 :: w12 :: w13 :: w14 :: rest} = some {s with pc := N 5965, memory := v16, stack := v46 :: w10 :: v45 :: v39 :: w1 :: w2 :: w3 :: w4 :: w5 :: w6 :: w7 :: w8 :: w9 :: w10 :: w11 :: w12 :: w13 :: w14 :: rest} := by
    simpa only [pr1Newpart13Model, v46] using pr1Newpart13_run ({s with memory := v16}) (w10) (v45) (v39) (w1) (w2) (w3) (w4) (w5) (w6) (w7) (w8) (w9) (w10) (w11) (w12) (w13) (w14) rest hcap hact
  exact (runInstructions_append_some _ _ _ _ _ h0 (runInstructions_append_some _ _ _ _ _ h1 (runInstructions_append_some _ _ _ _ _ h2 (runInstructions_append_some _ _ _ _ _ h3 (runInstructions_append_some _ _ _ _ _ h4 (runInstructions_append_some _ _ _ _ _ h5 (runInstructions_append_some _ _ _ _ _ h6 (runInstructions_append_some _ _ _ _ _ h7 (runInstructions_append_some _ _ _ _ _ h8 (runInstructions_append_some _ _ _ _ _ h9 (runInstructions_append_some _ _ _ _ _ h10 (runInstructions_append_some _ _ _ _ _ h11 (runInstructions_append_some _ _ _ _ _ h12 h13)))))))))))))

#print axioms pr1New_run

def productColumn1Model (s : State) (carry w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 : W) (rest : List W) : State :=
  let v0 : W := MachineState.readWord s.memory 1792
  let v1 : W := v0 * w5
  let v2 : W := v1 + w0
  let v3 : W := UInt256.mulMod v0 w5 w8
  let v4 : W := v3 + carry
  let v5 : W := w9 * w1
  let v6 : W := v5 + v2
  let v7 : W := w7 * w10
  let v8 : W := v7 + v6
  let v9 : W := UInt256.mulMod w9 w1 w8
  let v10 : W := v9 + v4
  let v11 : W := UInt256.mulMod w7 w10 w8
  let v12 : W := v11 + v10
  let v13 : W := MachineState.readWord s.memory 2720
  let v14 : W := v8 * v13
  let v15 : W := UInt256.land w11 v14
  let v16 : ByteArray := MachineState.writeBytes s.memory (Data.Bytes.natToBytesPadded v15.toNat 32) 192
  let v17 : W := UInt256.mulMod v15 w12 w8
  let v18 : W := v17 + v12
  let v19 : W := UInt256.mulMod (N 2048) v18 w8
  let v20 : W := MachineState.readWord v16 768
  let v21 : W := MachineState.readWord v16 1888
  let v22 : W := v21 * v20
  let v23 : W := v22 + v19
  let v24 : W := UInt256.mulMod v21 v20 w8
  let v25 : W := v24 + v19
  let v26 : W := MachineState.readWord v16 1856
  let v27 : W := v26 * w4
  let v28 : W := v27 + v23
  let v29 : W := UInt256.mulMod v26 w4 w8
  let v30 : W := v29 + v25
  let v31 : W := MachineState.readWord v16 1824
  let v32 : W := v31 * w5
  let v33 : W := v32 + v28
  let v34 : W := UInt256.mulMod v31 w5 w8
  let v35 : W := v34 + v30
  let v36 : W := MachineState.readWord v16 32
  let v37 : W := MachineState.readWord v16 1792
  let v38 : W := v37 * v36
  let v39 : W := v38 + v33
  let v40 : W := UInt256.mulMod v37 v36 w8
  let v41 : W := v40 + v35
  let v42 : W := w9 * w13
  let v43 : W := v42 + v39
  let v44 : W := w7 * w1
  let v45 : W := v44 + v43
  let v46 : W := MachineState.readWord v16 192
  {s with pc := N 5965, memory := v16, stack := v46 :: w10 :: v45 :: v41 :: w1 :: w2 :: w3 :: w4 :: w5 :: w6 :: w7 :: w8 :: w9 :: w10 :: w11 :: w12 :: w13 :: w14 :: rest}

def productColumn1Program : List Instr := pr1NewProgram

private theorem aux_shared0 (s : State) (z0 : W) :
    (MachineState.readWord (MachineState.writeBytes s.memory (Data.Bytes.natToBytesPadded z0.toNat 32) 192) 1792) = (MachineState.readWord s.memory 1792) := by
  simp (disch := decide) only [addC, addA, addL, mulC, mmC, amC, andC, orC, xorC, eqC, read_disjoint, Challenge.EvmProof.Memory.readWord_writeWord]

private theorem aux_shared1 (s : State) (w12 : W) (z0 : W) :
    (MachineState.readWord (MachineState.writeBytes s.memory (Data.Bytes.natToBytesPadded (UInt256.land w12 z0).toNat 32) 192) 192) = (UInt256.land w12 z0) := by
  simp (disch := decide) only [addC, addA, addL, mulC, mmC, amC, andC, orC, xorC, eqC, read_disjoint, Challenge.EvmProof.Memory.readWord_writeWord]

private theorem aux_shared2 (w8 w11 : W) :
    (w11 * w8) = (w8 * w11) := by
  simp (disch := decide) only [addC, addA, addL, mulC, mmC, amC, andC, orC, xorC, eqC, read_disjoint, Challenge.EvmProof.Memory.readWord_writeWord]

private theorem aux_shared3 (w8 w9 w11 : W) :
    (UInt256.mulMod w11 w8 w9) = (UInt256.mulMod w8 w11 w9) := by
  simp (disch := decide) only [addC, addA, addL, mulC, mmC, amC, andC, orC, xorC, eqC, read_disjoint, Challenge.EvmProof.Memory.readWord_writeWord]

private theorem aux_shared4 (w9 : W) (z0 z1 : W) :
    (UInt256.mulMod z0 z1 w9) = (UInt256.mulMod z1 z0 w9) := by
  simp (disch := decide) only [addC, addA, addL, mulC, mmC, amC, andC, orC, xorC, eqC, read_disjoint, Challenge.EvmProof.Memory.readWord_writeWord]

private theorem aux_shared5 (z0 z1 : W) :
    (z0 * z1) = (z1 * z0) := by
  simp (disch := decide) only [addC, addA, addL, mulC, mmC, amC, andC, orC, xorC, eqC, read_disjoint, Challenge.EvmProof.Memory.readWord_writeWord]

private theorem aux_shared6 (z0 z1 : W) :
    (z0 + z1) = (z1 + z0) := by
  simp (disch := decide) only [addC, addA, addL, mulC, mmC, amC, andC, orC, xorC, eqC, read_disjoint, Challenge.EvmProof.Memory.readWord_writeWord]

private theorem aux_shared7 (w5 w9 : W) (z0 : W) :
    (UInt256.mulMod w5 z0 w9) = (UInt256.mulMod z0 w5 w9) := by
  simp (disch := decide) only [addC, addA, addL, mulC, mmC, amC, andC, orC, xorC, eqC, read_disjoint, Challenge.EvmProof.Memory.readWord_writeWord]

private theorem aux_shared8 (w5 : W) (z0 : W) :
    (w5 * z0) = (z0 * w5) := by
  simp (disch := decide) only [addC, addA, addL, mulC, mmC, amC, andC, orC, xorC, eqC, read_disjoint, Challenge.EvmProof.Memory.readWord_writeWord]

private theorem aux_shared9 (w6 w9 : W) (z0 : W) :
    (UInt256.mulMod w6 z0 w9) = (UInt256.mulMod z0 w6 w9) := by
  simp (disch := decide) only [addC, addA, addL, mulC, mmC, amC, andC, orC, xorC, eqC, read_disjoint, Challenge.EvmProof.Memory.readWord_writeWord]

private theorem aux_shared10 (w6 : W) (z0 : W) :
    (w6 * z0) = (z0 * w6) := by
  simp (disch := decide) only [addC, addA, addL, mulC, mmC, amC, andC, orC, xorC, eqC, read_disjoint, Challenge.EvmProof.Memory.readWord_writeWord]

private theorem prepared_model_eq (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 : W) (rest : List W) :
    productColumn1Model s w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 rest = pr1NewModel s w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 rest := by
  let o0 : W := MachineState.readWord s.memory 1792
  let o1 : W := o0 * w6
  let o2 : W := o1 + w1
  let o3 : W := UInt256.mulMod o0 w6 w9
  let o4 : W := o3 + w0
  let o5 : W := w10 * w2
  let o6 : W := o5 + o2
  let o7 : W := w8 * w11
  let o8 : W := o7 + o6
  let o9 : W := UInt256.mulMod w10 w2 w9
  let o10 : W := o9 + o4
  let o11 : W := UInt256.mulMod w8 w11 w9
  let o12 : W := o11 + o10
  let o13 : W := MachineState.readWord s.memory 2720
  let o14 : W := o8 * o13
  let o15 : W := UInt256.land w12 o14
  let o16 : ByteArray := MachineState.writeBytes s.memory (Data.Bytes.natToBytesPadded o15.toNat 32) 192
  let o17 : W := UInt256.mulMod o15 w13 w9
  let o18 : W := o17 + o12
  let o19 : W := UInt256.mulMod (N 2048) o18 w9
  let o20 : W := MachineState.readWord o16 768
  let o21 : W := MachineState.readWord o16 1888
  let o22 : W := o21 * o20
  let o23 : W := o22 + o19
  let o24 : W := UInt256.mulMod o21 o20 w9
  let o25 : W := o24 + o19
  let o26 : W := MachineState.readWord o16 1856
  let o27 : W := o26 * w5
  let o28 : W := o27 + o23
  let o29 : W := UInt256.mulMod o26 w5 w9
  let o30 : W := o29 + o25
  let o31 : W := MachineState.readWord o16 1824
  let o32 : W := o31 * w6
  let o33 : W := o32 + o28
  let o34 : W := UInt256.mulMod o31 w6 w9
  let o35 : W := o34 + o30
  let o36 : W := MachineState.readWord o16 32
  let o37 : W := MachineState.readWord o16 1792
  let o38 : W := o37 * o36
  let o39 : W := o38 + o33
  let o40 : W := UInt256.mulMod o37 o36 w9
  let o41 : W := o40 + o35
  let o42 : W := w10 * w14
  let o43 : W := o42 + o39
  let o44 : W := w8 * w2
  let o45 : W := o44 + o43
  let o46 : W := MachineState.readWord o16 192
  let n0 : W := MachineState.readWord s.memory 1792
  let n1 : W := n0 * w6
  let n2 : W := n1 + w1
  let n3 : W := w10 * w2
  let n4 : W := n3 + n2
  let n5 : W := w11 * w8
  let n6 : W := n5 + n4
  let n7 : W := UInt256.mulMod n0 w6 w9
  let n8 : W := n7 + w0
  let n9 : W := UInt256.mulMod w10 w2 w9
  let n10 : W := n9 + n8
  let n11 : W := UInt256.mulMod w11 w8 w9
  let n12 : W := n11 + n10
  let n13 : W := MachineState.readWord s.memory 2720
  let n14 : W := n6 * n13
  let n15 : W := UInt256.land w12 n14
  let n16 : ByteArray := MachineState.writeBytes s.memory (Data.Bytes.natToBytesPadded n15.toNat 32) 192
  let n17 : W := UInt256.mulMod n15 w13 w9
  let n18 : W := n17 + n12
  let n19 : W := UInt256.mulMod (N 2048) n18 w9
  let n20 : W := MachineState.readWord n16 1856
  let n21 : W := MachineState.readWord n16 768
  let n22 : W := MachineState.readWord n16 1888
  let n23 : W := UInt256.mulMod n21 n22 w9
  let n24 : W := n21 * n22
  let n25 : W := n19 + n24
  let n26 : W := UInt256.mulMod w5 n20 w9
  let n27 : W := w5 * n20
  let n28 : W := n27 + n25
  let n29 : W := n19 + n23
  let n30 : W := n29 + n26
  let n31 : W := MachineState.readWord n16 32
  let n32 : W := MachineState.readWord n16 1824
  let n33 : W := UInt256.mulMod w6 n32 w9
  let n34 : W := MachineState.readWord n16 1792
  let n35 : W := UInt256.mulMod n31 n34 w9
  let n36 : W := w6 * n32
  let n37 : W := n31 * n34
  let n38 : W := n30 + n33
  let n39 : W := n38 + n35
  let n40 : W := n28 + n36
  let n41 : W := n40 + n37
  let n42 : W := w10 * w14
  let n43 : W := n42 + n41
  let n44 : W := w8 * w2
  let n45 : W := n44 + n43
  let n46 : W := MachineState.readWord n16 192
  have eq_o37 : o37 = o0 := by
    simpa only [o37, o16, o0] using
      (aux_shared0 s  o15)
  have eq_o46 : o46 = o15 := by
    simpa only [o46, o16, o15] using
      (aux_shared1 s w12 o14)
  have eq_n0 : n0 = o0 := by
    simp only [n0, o0]
  have eq_n1 : n1 = o1 := by
    simp only [n1, o1, eq_n0]
  have eq_n2 : n2 = o2 := by
    simp only [n2, o2, eq_n1]
  have eq_n3 : n3 = o5 := by
    simp only [n3, o5]
  have eq_n4 : n4 = o6 := by
    simp only [n4, o6, eq_n3, eq_n2]
  have eq_n5 : n5 = o7 := by
    simpa only [n5, o7] using
      (aux_shared2 w8 w11 )
  have eq_n6 : n6 = o8 := by
    simp only [n6, o8, eq_n5, eq_n4]
  have eq_n7 : n7 = o3 := by
    simp only [n7, o3, eq_n0]
  have eq_n8 : n8 = o4 := by
    simp only [n8, o4, eq_n7]
  have eq_n9 : n9 = o9 := by
    simp only [n9, o9]
  have eq_n10 : n10 = o10 := by
    simp only [n10, o10, eq_n9, eq_n8]
  have eq_n11 : n11 = o11 := by
    simpa only [n11, o11] using
      (aux_shared3 w8 w9 w11 )
  have eq_n12 : n12 = o12 := by
    simp only [n12, o12, eq_n11, eq_n10]
  have eq_n13 : n13 = o13 := by
    simp only [n13, o13]
  have eq_n14 : n14 = o14 := by
    simp only [n14, o14, eq_n6, eq_n13]
  have eq_n15 : n15 = o15 := by
    simp only [n15, o15, eq_n14]
  have eq_n16 : n16 = o16 := by
    simp only [n16, o16, eq_n15]
  have eq_n17 : n17 = o17 := by
    simp only [n17, o17, eq_n15]
  have eq_n18 : n18 = o18 := by
    simp only [n18, o18, eq_n17, eq_n12]
  have eq_n19 : n19 = o19 := by
    simp only [n19, o19, eq_n18]
  have eq_n20 : n20 = o26 := by
    simp only [n20, o26, eq_n16]
  have eq_n21 : n21 = o20 := by
    simp only [n21, o20, eq_n16]
  have eq_n22 : n22 = o21 := by
    simp only [n22, o21, eq_n16]
  have eq_n23 : n23 = o24 := by
    simpa only [n23, o24, eq_n21, eq_n22] using
      (aux_shared4 w9 o20 o21)
  have eq_n24 : n24 = o22 := by
    simpa only [n24, o22, eq_n21, eq_n22] using
      (aux_shared5  o20 o21)
  have eq_n25 : n25 = o23 := by
    simpa only [n25, o23, eq_n19, eq_n24] using
      (aux_shared6  o19 o22)
  have eq_n26 : n26 = o29 := by
    simpa only [n26, o29, eq_n20] using
      (aux_shared7 w5 w9 o26)
  have eq_n27 : n27 = o27 := by
    simpa only [n27, o27, eq_n20] using
      (aux_shared8 w5 o26)
  have eq_n28 : n28 = o28 := by
    simp only [n28, o28, eq_n27, eq_n25]
  have eq_n29 : n29 = o25 := by
    simpa only [n29, o25, eq_n19, eq_n23] using
      (aux_shared6  o19 o24)
  have eq_n30 : n30 = o30 := by
    simpa only [n30, o30, eq_n29, eq_n26] using
      (aux_shared6  o25 o29)
  have eq_n31 : n31 = o36 := by
    simp only [n31, o36, eq_n16]
  have eq_n32 : n32 = o31 := by
    simp only [n32, o31, eq_n16]
  have eq_n33 : n33 = o34 := by
    simpa only [n33, o34, eq_n32] using
      (aux_shared9 w6 w9 o31)
  have eq_n34 : n34 = o0 := by
    simpa only [n34, n16, o0, eq_n15] using
      (aux_shared0 s  o15)
  have eq_n35 : n35 = o40 := by
    simpa only [n35, o40, eq_n31, eq_n34, eq_o37] using
      (aux_shared4 w9 o36 o0)
  have eq_n36 : n36 = o32 := by
    simpa only [n36, o32, eq_n32] using
      (aux_shared10 w6 o31)
  have eq_n37 : n37 = o38 := by
    simpa only [n37, o38, eq_n31, eq_n34, eq_o37] using
      (aux_shared5  o36 o0)
  have eq_n38 : n38 = o35 := by
    simpa only [n38, o35, eq_n30, eq_n33] using
      (aux_shared6  o30 o34)
  have eq_n39 : n39 = o41 := by
    simpa only [n39, o41, eq_n38, eq_n35] using
      (aux_shared6  o35 o40)
  have eq_n40 : n40 = o33 := by
    simpa only [n40, o33, eq_n28, eq_n36] using
      (aux_shared6  o28 o32)
  have eq_n41 : n41 = o39 := by
    simpa only [n41, o39, eq_n40, eq_n37] using
      (aux_shared6  o33 o38)
  have eq_n42 : n42 = o42 := by
    simp only [n42, o42]
  have eq_n43 : n43 = o43 := by
    simp only [n43, o43, eq_n42, eq_n41]
  have eq_n44 : n44 = o44 := by
    simp only [n44, o44]
  have eq_n45 : n45 = o45 := by
    simp only [n45, o45, eq_n44, eq_n43]
  have eq_n46 : n46 = o15 := by
    simpa only [n46, n16, n15, o15, eq_n14] using
      (aux_shared1 s w12 o14)
  change {s with pc := N 5965, memory := o16, stack := o46 :: w11 :: o45 :: o41 :: w2 :: w3 :: w4 :: w5 :: w6 :: w7 :: w8 :: w9 :: w10 :: w11 :: w12 :: w13 :: w14 :: w15 :: rest} =
    {s with pc := N 5965, memory := n16, stack := n46 :: w11 :: n45 :: n39 :: w2 :: w3 :: w4 :: w5 :: w6 :: w7 :: w8 :: w9 :: w10 :: w11 :: w12 :: w13 :: w14 :: w15 :: rest}
  simp only [eq_o37, eq_o46, eq_n0, eq_n1, eq_n2, eq_n3, eq_n4, eq_n5, eq_n6, eq_n7, eq_n8, eq_n9, eq_n10, eq_n11, eq_n12, eq_n13, eq_n14, eq_n15, eq_n16, eq_n17, eq_n18, eq_n19, eq_n20, eq_n21, eq_n22, eq_n23, eq_n24, eq_n25, eq_n26, eq_n27, eq_n28, eq_n29, eq_n30, eq_n31, eq_n32, eq_n33, eq_n34, eq_n35, eq_n36, eq_n37, eq_n38, eq_n39, eq_n40, eq_n41, eq_n42, eq_n43, eq_n44, eq_n45, eq_n46]
theorem productColumn1_run (s : State) (carry w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions productColumn1Program {s with pc := N 5839, stack := carry :: w0 :: w1 :: w2 :: w3 :: w4 :: w5 :: w6 :: w7 :: w8 :: w9 :: w10 :: w11 :: w12 :: w13 :: w14 :: rest} =
      some (productColumn1Model s carry w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 rest) := by
  exact (pr1New_run s carry w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 rest hcap hact).trans
    (congrArg some (prepared_model_eq s carry w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 rest).symm)

#print axioms productColumn1_run
end CycleSubmission.Execution
