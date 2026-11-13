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

def pr12Newpart0Program : List Instr :=
  [
  .op .MULMOD,
   .op .ADD,
   .op (.Dup ⟨9, by decide⟩),
   .push 2 1216,
   .op .MLOAD,
   .op (.Dup ⟨6, by decide⟩),
   .op .MULMOD,
   .op .ADD]

def pr12Newpart0Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 : W) (rest : List W) : State :=
  let v0 : W := UInt256.mulMod x0 x1 x2
  let v1 : W := v0 + x3
  let v2 : W := MachineState.readWord s.memory 1216
  let v3 : W := UInt256.mulMod x7 v2 x12
  let v4 : W := v3 + v1
  {s with pc := N 9355, memory := s.memory, stack := v4 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: x18 :: rest}

theorem pr12Newpart0_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions pr12Newpart0Program {s with pc := N 9345, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: x18 :: rest} =
      some (pr12Newpart0Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 19) : rest.length + j < 1024 := by omega
  have ha1216 : (1216 : W).toNat = 1216 := rfl
  have hf1216 := Monpro.activeWords_fix s 1216 32 (by decide) (by norm_num) hact
  simp [hz, hzn, pr12Newpart0Program, pr12Newpart0Model, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, capacity, ha1216, hf1216]


def pr12Newpart1Program : List Instr :=
  [
  .op (.Dup ⟨9, by decide⟩),
   .op (.Dup ⟨15, by decide⟩),
   .op (.Dup ⟨7, by decide⟩),
   .op .MULMOD,
   .op .ADD,
   .op (.Dup ⟨15, by decide⟩),
   .op (.Dup ⟨10, by decide⟩),
   .op (.Swap ⟨0, by decide⟩)]

def pr12Newpart1Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 : W) (rest : List W) : State :=
  let v0 : W := UInt256.mulMod x5 x14 x9
  let v1 : W := v0 + x0
  {s with pc := N 9363, memory := s.memory, stack := x15 :: x9 :: v1 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: rest}

theorem pr12Newpart1_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions pr12Newpart1Program {s with pc := N 9355, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: rest} =
      some (pr12Newpart1Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 19) : rest.length + j < 1024 := by omega
  simp [hz, hzn, pr12Newpart1Program, pr12Newpart1Model, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, capacity]


def pr12Newpart2Program : List Instr :=
  [
  .push 2 1280,
   .op .MLOAD,
   .op .MULMOD,
   .op .ADD,
   .op (.Dup ⟨9, by decide⟩),
   .op (.Dup ⟨14, by decide⟩),
   .op (.Dup ⟨13, by decide⟩),
   .op .MULMOD]

def pr12Newpart2Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 : W) (rest : List W) : State :=
  let v0 : W := MachineState.readWord s.memory 1280
  let v1 : W := UInt256.mulMod v0 x0 x1
  let v2 : W := v1 + x2
  let v3 : W := UInt256.mulMod x13 x15 x11
  {s with pc := N 9373, memory := s.memory, stack := v3 :: v2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: rest}

theorem pr12Newpart2_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions pr12Newpart2Program {s with pc := N 9363, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: rest} =
      some (pr12Newpart2Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 19) : rest.length + j < 1024 := by omega
  have ha1280 : (1280 : W).toNat = 1280 := rfl
  have hf1280 := Monpro.activeWords_fix s 1280 32 (by decide) (by norm_num) hact
  simp [hz, hzn, pr12Newpart2Program, pr12Newpart2Model, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, capacity, ha1280, hf1280]


def pr12Newpart3Program : List Instr :=
  [
  .op .ADD,
   .op (.Swap ⟨0, by decide⟩),
   .op (.Dup ⟨12, by decide⟩),
   .op .AND,
   .op (.Dup ⟨0, by decide⟩),
   .push 2 768,
   .op .MSTORE,
   .op (.Dup ⟨9, by decide⟩)]

def pr12Newpart3Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 : W) (rest : List W) : State :=
  let v0 : W := x0 + x1
  let v1 : W := UInt256.land x13 x2
  let v2 : ByteArray := MachineState.writeBytes s.memory (Data.Bytes.natToBytesPadded v1.toNat 32) 768
  {s with pc := N 9383, memory := v2, stack := x10 :: v1 :: v0 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: rest}

theorem pr12Newpart3_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions pr12Newpart3Program {s with pc := N 9373, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: rest} =
      some (pr12Newpart3Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 18) : rest.length + j < 1024 := by omega
  have ha768 : (768 : W).toNat = 768 := rfl
  have hf768 := Monpro.activeWords_fix s 768 32 (by decide) (by norm_num) hact
  simp [hz, hzn, pr12Newpart3Program, pr12Newpart3Model, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, capacity, ha768, hf768]


def pr12Newpart4Program : List Instr :=
  [
  .op (.Swap ⟨1, by decide⟩),
   .op .SUB,
   .op (.Dup ⟨1, by decide⟩),
   .op .ADD,
   .push 2 2048,
   .op .MULMOD,
   .push 2 1280,
   .op .MLOAD]

def pr12Newpart4Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 : W) (rest : List W) : State :=
  let v0 : W := x2 - x1
  let v1 : W := x0 + v0
  let v2 : W := UInt256.mulMod (N 2048) v1 x0
  let v3 : W := MachineState.readWord s.memory 1280
  {s with pc := N 9395, memory := s.memory, stack := v3 :: v2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: rest}

theorem pr12Newpart4_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions pr12Newpart4Program {s with pc := N 9383, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: rest} =
      some (pr12Newpart4Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 17) : rest.length + j < 1024 := by omega
  have ha1280 : (1280 : W).toNat = 1280 := rfl
  have hf1280 := Monpro.activeWords_fix s 1280 32 (by decide) (by norm_num) hact
  simp [hz, hzn, pr12Newpart4Program, pr12Newpart4Model, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, capacity, ha1280, hf1280]


def pr12Newpart5Program : List Instr :=
  [
  .op (.Swap ⟨10, by decide⟩),
   .op .POP,
   .push 2 2048,
   .op .MLOAD,
   .op (.Dup ⟨1, by decide⟩),
   .op (.Dup ⟨10, by decide⟩),
   .op (.Dup ⟨2, by decide⟩),
   .op (.Dup ⟨9, by decide⟩)]

def pr12Newpart5Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 : W) (rest : List W) : State :=
  let v0 : W := MachineState.readWord s.memory 2048
  {s with pc := N 9405, memory := s.memory, stack := x6 :: v0 :: x9 :: x1 :: v0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x0 :: x12 :: x13 :: x14 :: x15 :: rest}

theorem pr12Newpart5_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions pr12Newpart5Program {s with pc := N 9395, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: rest} =
      some (pr12Newpart5Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 20) : rest.length + j < 1024 := by omega
  have ha2048 : (2048 : W).toNat = 2048 := rfl
  have hf2048 := Monpro.activeWords_fix s 2048 32 (by decide) (by norm_num) hact
  simp [hz, hzn, pr12Newpart5Program, pr12Newpart5Model, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, capacity, ha2048, hf2048]


def pr12Newpart6Program : List Instr :=
  [
  .op .MULMOD,
   .op .ADD,
   .op (.Swap ⟨6, by decide⟩),
   .op .MUL,
   .op .ADD,
   .push 2 1216,
   .op .MLOAD,
   .op (.Swap ⟨5, by decide⟩)]

def pr12Newpart6Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 : W) (rest : List W) : State :=
  let v0 : W := UInt256.mulMod x0 x1 x2
  let v1 : W := v0 + x3
  let v2 : W := x10 * x4
  let v3 : W := v2 + x5
  let v4 : W := MachineState.readWord s.memory 1216
  {s with pc := N 9415, memory := s.memory, stack := v1 :: v3 :: x6 :: x7 :: x8 :: x9 :: v4 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: x18 :: x19 :: rest}

theorem pr12Newpart6_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions pr12Newpart6Program {s with pc := N 9405, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: x18 :: x19 :: rest} =
      some (pr12Newpart6Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 20) : rest.length + j < 1024 := by omega
  have ha1216 : (1216 : W).toNat = 1216 := rfl
  have hf1216 := Monpro.activeWords_fix s 1216 32 (by decide) (by norm_num) hact
  simp [hz, hzn, pr12Newpart6Program, pr12Newpart6Model, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, capacity, ha1216, hf1216]


def pr12Newpart7Program : List Instr :=
  [
  .op (.Dup ⟨9, by decide⟩),
   .push 1 32,
   .op .MLOAD,
   .push 2 2016,
   .op .MLOAD,
   .op (.Swap ⟨3, by decide⟩),
   .op (.Dup ⟨1, by decide⟩),
   .op (.Dup ⟨5, by decide⟩)]

def pr12Newpart7Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 : W) (rest : List W) : State :=
  let v0 : W := MachineState.readWord s.memory 32
  let v1 : W := MachineState.readWord s.memory 2016
  {s with pc := N 9426, memory := s.memory, stack := v1 :: v0 :: x1 :: v0 :: x9 :: x0 :: v1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: rest}

theorem pr12Newpart7_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions pr12Newpart7Program {s with pc := N 9415, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: rest} =
      some (pr12Newpart7Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 21) : rest.length + j < 1024 := by omega
  have ha32 : (32 : W).toNat = 32 := rfl
  have hf32 := Monpro.activeWords_fix s 32 32 (by decide) (by norm_num) hact
  have ha2016 : (2016 : W).toNat = 2016 := rfl
  have hf2016 := Monpro.activeWords_fix s 2016 32 (by decide) (by norm_num) hact
  simp [hz, hzn, pr12Newpart7Program, pr12Newpart7Model, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, capacity, ha32, hf32, ha2016, hf2016]


def pr12Newpart8Program : List Instr :=
  [
  .op .MUL,
   .op .ADD,
   .op (.Swap ⟨3, by decide⟩),
   .op .MULMOD,
   .op .ADD,
   .op (.Dup ⟨9, by decide⟩),
   .push 1 64,
   .op .MLOAD]

def pr12Newpart8Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 : W) (rest : List W) : State :=
  let v0 : W := x0 * x1
  let v1 : W := v0 + x2
  let v2 : W := UInt256.mulMod x6 x3 x4
  let v3 : W := v2 + x5
  let v4 : W := MachineState.readWord s.memory 64
  {s with pc := N 9435, memory := s.memory, stack := v4 :: x14 :: v3 :: v1 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: x18 :: x19 :: x20 :: rest}

theorem pr12Newpart8_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions pr12Newpart8Program {s with pc := N 9426, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: x18 :: x19 :: x20 :: rest} =
      some (pr12Newpart8Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 21) : rest.length + j < 1024 := by omega
  have ha64 : (64 : W).toNat = 64 := rfl
  have hf64 := Monpro.activeWords_fix s 64 32 (by decide) (by norm_num) hact
  simp [hz, hzn, pr12Newpart8Program, pr12Newpart8Model, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, capacity, ha64, hf64]


def pr12Newpart9Program : List Instr :=
  [
  .push 2 1984,
   .op .MLOAD,
   .op (.Swap ⟨3, by decide⟩),
   .op (.Dup ⟨1, by decide⟩),
   .op (.Dup ⟨5, by decide⟩),
   .op .MUL,
   .op .ADD,
   .op (.Swap ⟨3, by decide⟩)]

def pr12Newpart9Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 : W) (rest : List W) : State :=
  let v0 : W := MachineState.readWord s.memory 1984
  let v1 : W := v0 * x0
  let v2 : W := v1 + x3
  {s with pc := N 9445, memory := s.memory, stack := v0 :: x0 :: x1 :: x2 :: v2 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: rest}

theorem pr12Newpart9_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions pr12Newpart9Program {s with pc := N 9435, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: rest} =
      some (pr12Newpart9Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 21) : rest.length + j < 1024 := by omega
  have ha1984 : (1984 : W).toNat = 1984 := rfl
  have hf1984 := Monpro.activeWords_fix s 1984 32 (by decide) (by norm_num) hact
  simp [hz, hzn, pr12Newpart9Program, pr12Newpart9Model, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, capacity, ha1984, hf1984]


def pr12Newpart10Program : List Instr :=
  [
  .op .MULMOD,
   .op .ADD,
   .op (.Dup ⟨9, by decide⟩),
   .push 1 96,
   .op .MLOAD,
   .push 2 1952,
   .op .MLOAD,
   .op (.Swap ⟨3, by decide⟩)]

def pr12Newpart10Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 : W) (rest : List W) : State :=
  let v0 : W := UInt256.mulMod x0 x1 x2
  let v1 : W := v0 + x3
  let v2 : W := MachineState.readWord s.memory 96
  let v3 : W := MachineState.readWord s.memory 1952
  {s with pc := N 9456, memory := s.memory, stack := x4 :: v2 :: x12 :: v1 :: v3 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: x18 :: rest}

theorem pr12Newpart10_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions pr12Newpart10Program {s with pc := N 9445, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: x18 :: rest} =
      some (pr12Newpart10Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 19) : rest.length + j < 1024 := by omega
  have ha96 : (96 : W).toNat = 96 := rfl
  have hf96 := Monpro.activeWords_fix s 96 32 (by decide) (by norm_num) hact
  have ha1952 : (1952 : W).toNat = 1952 := rfl
  have hf1952 := Monpro.activeWords_fix s 1952 32 (by decide) (by norm_num) hact
  simp [hz, hzn, pr12Newpart10Program, pr12Newpart10Model, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, capacity, ha96, hf96, ha1952, hf1952]


def pr12Newpart11Program : List Instr :=
  [
  .op (.Dup ⟨1, by decide⟩),
   .op (.Dup ⟨5, by decide⟩),
   .op .MUL,
   .op .ADD,
   .op (.Swap ⟨3, by decide⟩),
   .op .MULMOD,
   .op .ADD,
   .op (.Dup ⟨9, by decide⟩)]

def pr12Newpart11Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 : W) (rest : List W) : State :=
  let v0 : W := x4 * x1
  let v1 : W := v0 + x0
  let v2 : W := UInt256.mulMod x4 x1 x2
  let v3 : W := v2 + x3
  {s with pc := N 9464, memory := s.memory, stack := x12 :: v3 :: v1 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: x18 :: rest}

theorem pr12Newpart11_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions pr12Newpart11Program {s with pc := N 9456, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: x18 :: rest} =
      some (pr12Newpart11Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 21) : rest.length + j < 1024 := by omega
  simp [hz, hzn, pr12Newpart11Program, pr12Newpart11Model, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, capacity]


def pr12Newpart12Program : List Instr :=
  [.push 1 128,
   .op .MLOAD]

def pr12Newpart12Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 : W) (rest : List W) : State :=
  let v0 : W := MachineState.readWord s.memory 128
  {s with pc := N 9467, memory := s.memory, stack := v0 :: x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: rest}

theorem pr12Newpart12_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions pr12Newpart12Program {s with pc := N 9464, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: rest} =
      some (pr12Newpart12Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 18) : rest.length + j < 1024 := by omega
  have ha128 : (128 : W).toNat = 128 := rfl
  have hf128 := Monpro.activeWords_fix s 128 32 (by decide) (by norm_num) hact
  simp [hz, hzn, pr12Newpart12Program, pr12Newpart12Model, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, capacity, ha128, hf128]


def pr12NewProgram : List Instr :=
  [
  .op .MULMOD,
   .op .ADD,
   .op (.Dup ⟨9, by decide⟩),
   .push 2 1216,
   .op .MLOAD,
   .op (.Dup ⟨6, by decide⟩),
   .op .MULMOD,
   .op .ADD,
   .op (.Dup ⟨9, by decide⟩),
   .op (.Dup ⟨15, by decide⟩),
   .op (.Dup ⟨7, by decide⟩),
   .op .MULMOD,
   .op .ADD,
   .op (.Dup ⟨15, by decide⟩),
   .op (.Dup ⟨10, by decide⟩),
   .op (.Swap ⟨0, by decide⟩),
   .push 2 1280,
   .op .MLOAD,
   .op .MULMOD,
   .op .ADD,
   .op (.Dup ⟨9, by decide⟩),
   .op (.Dup ⟨14, by decide⟩),
   .op (.Dup ⟨13, by decide⟩),
   .op .MULMOD,
   .op .ADD,
   .op (.Swap ⟨0, by decide⟩),
   .op (.Dup ⟨12, by decide⟩),
   .op .AND,
   .op (.Dup ⟨0, by decide⟩),
   .push 2 768,
   .op .MSTORE,
   .op (.Dup ⟨9, by decide⟩),
   .op (.Swap ⟨1, by decide⟩),
   .op .SUB,
   .op (.Dup ⟨1, by decide⟩),
   .op .ADD,
   .push 2 2048,
   .op .MULMOD,
   .push 2 1280,
   .op .MLOAD,
   .op (.Swap ⟨10, by decide⟩),
   .op .POP,
   .push 2 2048,
   .op .MLOAD,
   .op (.Dup ⟨1, by decide⟩),
   .op (.Dup ⟨10, by decide⟩),
   .op (.Dup ⟨2, by decide⟩),
   .op (.Dup ⟨9, by decide⟩),
   .op .MULMOD,
   .op .ADD,
   .op (.Swap ⟨6, by decide⟩),
   .op .MUL,
   .op .ADD,
   .push 2 1216,
   .op .MLOAD,
   .op (.Swap ⟨5, by decide⟩),
   .op (.Dup ⟨9, by decide⟩),
   .push 1 32,
   .op .MLOAD,
   .push 2 2016,
   .op .MLOAD,
   .op (.Swap ⟨3, by decide⟩),
   .op (.Dup ⟨1, by decide⟩),
   .op (.Dup ⟨5, by decide⟩),
   .op .MUL,
   .op .ADD,
   .op (.Swap ⟨3, by decide⟩),
   .op .MULMOD,
   .op .ADD,
   .op (.Dup ⟨9, by decide⟩),
   .push 1 64,
   .op .MLOAD,
   .push 2 1984,
   .op .MLOAD,
   .op (.Swap ⟨3, by decide⟩),
   .op (.Dup ⟨1, by decide⟩),
   .op (.Dup ⟨5, by decide⟩),
   .op .MUL,
   .op .ADD,
   .op (.Swap ⟨3, by decide⟩),
   .op .MULMOD,
   .op .ADD,
   .op (.Dup ⟨9, by decide⟩),
   .push 1 96,
   .op .MLOAD,
   .push 2 1952,
   .op .MLOAD,
   .op (.Swap ⟨3, by decide⟩),
   .op (.Dup ⟨1, by decide⟩),
   .op (.Dup ⟨5, by decide⟩),
   .op .MUL,
   .op .ADD,
   .op (.Swap ⟨3, by decide⟩),
   .op .MULMOD,
   .op .ADD,
   .op (.Dup ⟨9, by decide⟩),
   .push 1 128,
   .op .MLOAD]

def pr12NewModel (s : State) (carry w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 : W) (rest : List W) : State :=
  let v0 : W := UInt256.mulMod carry w0 w1
  let v1 : W := v0 + w2
  let v2 : W := MachineState.readWord s.memory 1216
  let v3 : W := UInt256.mulMod w6 v2 w11
  let v4 : W := v3 + v1
  let v5 : W := UInt256.mulMod w7 w16 w11
  let v6 : W := v5 + v4
  let v7 : W := MachineState.readWord s.memory 1280
  let v8 : W := UInt256.mulMod v7 w17 w11
  let v9 : W := v8 + v6
  let v10 : W := UInt256.mulMod w13 w15 w11
  let v11 : W := v10 + v9
  let v12 : W := UInt256.land w14 w3
  let v13 : ByteArray := MachineState.writeBytes s.memory (Data.Bytes.natToBytesPadded v12.toNat 32) 768
  let v14 : W := v11 - v12
  let v15 : W := w11 + v14
  let v16 : W := UInt256.mulMod (N 2048) v15 w11
  let v17 : W := MachineState.readWord v13 1280
  let v18 : W := MachineState.readWord v13 2048
  let v19 : W := UInt256.mulMod w8 v18 w11
  let v20 : W := v19 + v16
  let v21 : W := w8 * v18
  let v22 : W := v21 + v16
  let v23 : W := MachineState.readWord v13 1216
  let v24 : W := MachineState.readWord v13 32
  let v25 : W := MachineState.readWord v13 2016
  let v26 : W := v25 * v24
  let v27 : W := v26 + v22
  let v28 : W := UInt256.mulMod v25 v24 w11
  let v29 : W := v28 + v20
  let v30 : W := MachineState.readWord v13 64
  let v31 : W := MachineState.readWord v13 1984
  let v32 : W := v31 * v30
  let v33 : W := v32 + v27
  let v34 : W := UInt256.mulMod v31 v30 w11
  let v35 : W := v34 + v29
  let v36 : W := MachineState.readWord v13 96
  let v37 : W := MachineState.readWord v13 1952
  let v38 : W := v37 * v36
  let v39 : W := v38 + v33
  let v40 : W := UInt256.mulMod v37 v36 w11
  let v41 : W := v40 + v35
  let v42 : W := MachineState.readWord v13 128
  {s with pc := N 9467, memory := v13, stack := v42 :: w11 :: v41 :: v39 :: w4 :: w5 :: w6 :: w7 :: v23 :: w9 :: w10 :: w11 :: w12 :: v17 :: w14 :: w15 :: w16 :: w17 :: rest}

theorem pr12New_run (s : State) (carry w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions pr12NewProgram {s with pc := N 9345, stack := carry :: w0 :: w1 :: w2 :: w3 :: w4 :: w5 :: w6 :: w7 :: w8 :: w9 :: w10 :: w11 :: w12 :: w13 :: w14 :: w15 :: w16 :: w17 :: rest} =
      some (pr12NewModel s carry w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 rest) := by
  let v0 : W := UInt256.mulMod carry w0 w1
  let v1 : W := v0 + w2
  let v2 : W := MachineState.readWord s.memory 1216
  let v3 : W := UInt256.mulMod w6 v2 w11
  let v4 : W := v3 + v1
  let v5 : W := UInt256.mulMod w7 w16 w11
  let v6 : W := v5 + v4
  let v7 : W := MachineState.readWord s.memory 1280
  let v8 : W := UInt256.mulMod v7 w17 w11
  let v9 : W := v8 + v6
  let v10 : W := UInt256.mulMod w13 w15 w11
  let v11 : W := v10 + v9
  let v12 : W := UInt256.land w14 w3
  let v13 : ByteArray := MachineState.writeBytes s.memory (Data.Bytes.natToBytesPadded v12.toNat 32) 768
  let v14 : W := v11 - v12
  let v15 : W := w11 + v14
  let v16 : W := UInt256.mulMod (N 2048) v15 w11
  let v17 : W := MachineState.readWord v13 1280
  let v18 : W := MachineState.readWord v13 2048
  let v19 : W := UInt256.mulMod w8 v18 w11
  let v20 : W := v19 + v16
  let v21 : W := w8 * v18
  let v22 : W := v21 + v16
  let v23 : W := MachineState.readWord v13 1216
  let v24 : W := MachineState.readWord v13 32
  let v25 : W := MachineState.readWord v13 2016
  let v26 : W := v25 * v24
  let v27 : W := v26 + v22
  let v28 : W := UInt256.mulMod v25 v24 w11
  let v29 : W := v28 + v20
  let v30 : W := MachineState.readWord v13 64
  let v31 : W := MachineState.readWord v13 1984
  let v32 : W := v31 * v30
  let v33 : W := v32 + v27
  let v34 : W := UInt256.mulMod v31 v30 w11
  let v35 : W := v34 + v29
  let v36 : W := MachineState.readWord v13 96
  let v37 : W := MachineState.readWord v13 1952
  let v38 : W := v37 * v36
  let v39 : W := v38 + v33
  let v40 : W := UInt256.mulMod v37 v36 w11
  let v41 : W := v40 + v35
  let v42 : W := MachineState.readWord v13 128
  have h0 : runInstructions pr12Newpart0Program {s with pc := N 9345, memory := s.memory, stack := carry :: w0 :: w1 :: w2 :: w3 :: w4 :: w5 :: w6 :: w7 :: w8 :: w9 :: w10 :: w11 :: w12 :: w13 :: w14 :: w15 :: w16 :: w17 :: rest} = some {s with pc := N 9355, memory := s.memory, stack := v4 :: w3 :: w4 :: w5 :: w6 :: w7 :: w8 :: w9 :: w10 :: w11 :: w12 :: w13 :: w14 :: w15 :: w16 :: w17 :: rest} := by
    simpa only [pr12Newpart0Model, v0, v1, v2, v3, v4] using pr12Newpart0_run (s) (carry) (w0) (w1) (w2) (w3) (w4) (w5) (w6) (w7) (w8) (w9) (w10) (w11) (w12) (w13) (w14) (w15) (w16) (w17) rest hcap hact
  have h1 : runInstructions pr12Newpart1Program {s with pc := N 9355, memory := s.memory, stack := v4 :: w3 :: w4 :: w5 :: w6 :: w7 :: w8 :: w9 :: w10 :: w11 :: w12 :: w13 :: w14 :: w15 :: w16 :: w17 :: rest} = some {s with pc := N 9363, memory := s.memory, stack := w17 :: w11 :: v6 :: w3 :: w4 :: w5 :: w6 :: w7 :: w8 :: w9 :: w10 :: w11 :: w12 :: w13 :: w14 :: w15 :: w16 :: w17 :: rest} := by
    simpa only [pr12Newpart1Model, v5, v6] using pr12Newpart1_run (s) (v4) (w3) (w4) (w5) (w6) (w7) (w8) (w9) (w10) (w11) (w12) (w13) (w14) (w15) (w16) (w17) rest hcap hact
  have h2 : runInstructions pr12Newpart2Program {s with pc := N 9363, memory := s.memory, stack := w17 :: w11 :: v6 :: w3 :: w4 :: w5 :: w6 :: w7 :: w8 :: w9 :: w10 :: w11 :: w12 :: w13 :: w14 :: w15 :: w16 :: w17 :: rest} = some {s with pc := N 9373, memory := s.memory, stack := v10 :: v9 :: w3 :: w4 :: w5 :: w6 :: w7 :: w8 :: w9 :: w10 :: w11 :: w12 :: w13 :: w14 :: w15 :: w16 :: w17 :: rest} := by
    simpa only [pr12Newpart2Model, v7, v8, v9, v10] using pr12Newpart2_run (s) (w17) (w11) (v6) (w3) (w4) (w5) (w6) (w7) (w8) (w9) (w10) (w11) (w12) (w13) (w14) (w15) (w16) (w17) rest hcap hact
  have h3 : runInstructions pr12Newpart3Program {s with pc := N 9373, memory := s.memory, stack := v10 :: v9 :: w3 :: w4 :: w5 :: w6 :: w7 :: w8 :: w9 :: w10 :: w11 :: w12 :: w13 :: w14 :: w15 :: w16 :: w17 :: rest} = some {s with pc := N 9383, memory := v13, stack := w11 :: v12 :: v11 :: w4 :: w5 :: w6 :: w7 :: w8 :: w9 :: w10 :: w11 :: w12 :: w13 :: w14 :: w15 :: w16 :: w17 :: rest} := by
    simpa only [pr12Newpart3Model, v11, v12, v13] using pr12Newpart3_run (s) (v10) (v9) (w3) (w4) (w5) (w6) (w7) (w8) (w9) (w10) (w11) (w12) (w13) (w14) (w15) (w16) (w17) rest hcap hact
  have h4 : runInstructions pr12Newpart4Program {s with pc := N 9383, memory := v13, stack := w11 :: v12 :: v11 :: w4 :: w5 :: w6 :: w7 :: w8 :: w9 :: w10 :: w11 :: w12 :: w13 :: w14 :: w15 :: w16 :: w17 :: rest} = some {s with pc := N 9395, memory := v13, stack := v17 :: v16 :: w4 :: w5 :: w6 :: w7 :: w8 :: w9 :: w10 :: w11 :: w12 :: w13 :: w14 :: w15 :: w16 :: w17 :: rest} := by
    simpa only [pr12Newpart4Model, v14, v15, v16, v17] using pr12Newpart4_run ({s with memory := v13}) (w11) (v12) (v11) (w4) (w5) (w6) (w7) (w8) (w9) (w10) (w11) (w12) (w13) (w14) (w15) (w16) (w17) rest hcap hact
  have h5 : runInstructions pr12Newpart5Program {s with pc := N 9395, memory := v13, stack := v17 :: v16 :: w4 :: w5 :: w6 :: w7 :: w8 :: w9 :: w10 :: w11 :: w12 :: w13 :: w14 :: w15 :: w16 :: w17 :: rest} = some {s with pc := N 9405, memory := v13, stack := w8 :: v18 :: w11 :: v16 :: v18 :: v16 :: w4 :: w5 :: w6 :: w7 :: w8 :: w9 :: w10 :: w11 :: w12 :: v17 :: w14 :: w15 :: w16 :: w17 :: rest} := by
    simpa only [pr12Newpart5Model, v18] using pr12Newpart5_run ({s with memory := v13}) (v17) (v16) (w4) (w5) (w6) (w7) (w8) (w9) (w10) (w11) (w12) (w13) (w14) (w15) (w16) (w17) rest hcap hact
  have h6 : runInstructions pr12Newpart6Program {s with pc := N 9405, memory := v13, stack := w8 :: v18 :: w11 :: v16 :: v18 :: v16 :: w4 :: w5 :: w6 :: w7 :: w8 :: w9 :: w10 :: w11 :: w12 :: v17 :: w14 :: w15 :: w16 :: w17 :: rest} = some {s with pc := N 9415, memory := v13, stack := v20 :: v22 :: w4 :: w5 :: w6 :: w7 :: v23 :: w9 :: w10 :: w11 :: w12 :: v17 :: w14 :: w15 :: w16 :: w17 :: rest} := by
    simpa only [pr12Newpart6Model, v19, v20, v21, v22, v23] using pr12Newpart6_run ({s with memory := v13}) (w8) (v18) (w11) (v16) (v18) (v16) (w4) (w5) (w6) (w7) (w8) (w9) (w10) (w11) (w12) (v17) (w14) (w15) (w16) (w17) rest hcap hact
  have h7 : runInstructions pr12Newpart7Program {s with pc := N 9415, memory := v13, stack := v20 :: v22 :: w4 :: w5 :: w6 :: w7 :: v23 :: w9 :: w10 :: w11 :: w12 :: v17 :: w14 :: w15 :: w16 :: w17 :: rest} = some {s with pc := N 9426, memory := v13, stack := v25 :: v24 :: v22 :: v24 :: w11 :: v20 :: v25 :: w4 :: w5 :: w6 :: w7 :: v23 :: w9 :: w10 :: w11 :: w12 :: v17 :: w14 :: w15 :: w16 :: w17 :: rest} := by
    simpa only [pr12Newpart7Model, v24, v25] using pr12Newpart7_run ({s with memory := v13}) (v20) (v22) (w4) (w5) (w6) (w7) (v23) (w9) (w10) (w11) (w12) (v17) (w14) (w15) (w16) (w17) rest hcap hact
  have h8 : runInstructions pr12Newpart8Program {s with pc := N 9426, memory := v13, stack := v25 :: v24 :: v22 :: v24 :: w11 :: v20 :: v25 :: w4 :: w5 :: w6 :: w7 :: v23 :: w9 :: w10 :: w11 :: w12 :: v17 :: w14 :: w15 :: w16 :: w17 :: rest} = some {s with pc := N 9435, memory := v13, stack := v30 :: w11 :: v29 :: v27 :: w4 :: w5 :: w6 :: w7 :: v23 :: w9 :: w10 :: w11 :: w12 :: v17 :: w14 :: w15 :: w16 :: w17 :: rest} := by
    simpa only [pr12Newpart8Model, v26, v27, v28, v29, v30] using pr12Newpart8_run ({s with memory := v13}) (v25) (v24) (v22) (v24) (w11) (v20) (v25) (w4) (w5) (w6) (w7) (v23) (w9) (w10) (w11) (w12) (v17) (w14) (w15) (w16) (w17) rest hcap hact
  have h9 : runInstructions pr12Newpart9Program {s with pc := N 9435, memory := v13, stack := v30 :: w11 :: v29 :: v27 :: w4 :: w5 :: w6 :: w7 :: v23 :: w9 :: w10 :: w11 :: w12 :: v17 :: w14 :: w15 :: w16 :: w17 :: rest} = some {s with pc := N 9445, memory := v13, stack := v31 :: v30 :: w11 :: v29 :: v33 :: w4 :: w5 :: w6 :: w7 :: v23 :: w9 :: w10 :: w11 :: w12 :: v17 :: w14 :: w15 :: w16 :: w17 :: rest} := by
    simpa only [pr12Newpart9Model, v31, v32, v33] using pr12Newpart9_run ({s with memory := v13}) (v30) (w11) (v29) (v27) (w4) (w5) (w6) (w7) (v23) (w9) (w10) (w11) (w12) (v17) (w14) (w15) (w16) (w17) rest hcap hact
  have h10 : runInstructions pr12Newpart10Program {s with pc := N 9445, memory := v13, stack := v31 :: v30 :: w11 :: v29 :: v33 :: w4 :: w5 :: w6 :: w7 :: v23 :: w9 :: w10 :: w11 :: w12 :: v17 :: w14 :: w15 :: w16 :: w17 :: rest} = some {s with pc := N 9456, memory := v13, stack := v33 :: v36 :: w11 :: v35 :: v37 :: w4 :: w5 :: w6 :: w7 :: v23 :: w9 :: w10 :: w11 :: w12 :: v17 :: w14 :: w15 :: w16 :: w17 :: rest} := by
    simpa only [pr12Newpart10Model, v34, v35, v36, v37] using pr12Newpart10_run ({s with memory := v13}) (v31) (v30) (w11) (v29) (v33) (w4) (w5) (w6) (w7) (v23) (w9) (w10) (w11) (w12) (v17) (w14) (w15) (w16) (w17) rest hcap hact
  have h11 : runInstructions pr12Newpart11Program {s with pc := N 9456, memory := v13, stack := v33 :: v36 :: w11 :: v35 :: v37 :: w4 :: w5 :: w6 :: w7 :: v23 :: w9 :: w10 :: w11 :: w12 :: v17 :: w14 :: w15 :: w16 :: w17 :: rest} = some {s with pc := N 9464, memory := v13, stack := w11 :: v41 :: v39 :: w4 :: w5 :: w6 :: w7 :: v23 :: w9 :: w10 :: w11 :: w12 :: v17 :: w14 :: w15 :: w16 :: w17 :: rest} := by
    simpa only [pr12Newpart11Model, v38, v39, v40, v41] using pr12Newpart11_run ({s with memory := v13}) (v33) (v36) (w11) (v35) (v37) (w4) (w5) (w6) (w7) (v23) (w9) (w10) (w11) (w12) (v17) (w14) (w15) (w16) (w17) rest hcap hact
  have h12 : runInstructions pr12Newpart12Program {s with pc := N 9464, memory := v13, stack := w11 :: v41 :: v39 :: w4 :: w5 :: w6 :: w7 :: v23 :: w9 :: w10 :: w11 :: w12 :: v17 :: w14 :: w15 :: w16 :: w17 :: rest} = some {s with pc := N 9467, memory := v13, stack := v42 :: w11 :: v41 :: v39 :: w4 :: w5 :: w6 :: w7 :: v23 :: w9 :: w10 :: w11 :: w12 :: v17 :: w14 :: w15 :: w16 :: w17 :: rest} := by
    simpa only [pr12Newpart12Model, v42] using pr12Newpart12_run ({s with memory := v13}) (w11) (v41) (v39) (w4) (w5) (w6) (w7) (v23) (w9) (w10) (w11) (w12) (v17) (w14) (w15) (w16) (w17) rest hcap hact
  exact (runInstructions_append_some _ _ _ _ _ h0 (runInstructions_append_some _ _ _ _ _ h1 (runInstructions_append_some _ _ _ _ _ h2 (runInstructions_append_some _ _ _ _ _ h3 (runInstructions_append_some _ _ _ _ _ h4 (runInstructions_append_some _ _ _ _ _ h5 (runInstructions_append_some _ _ _ _ _ h6 (runInstructions_append_some _ _ _ _ _ h7 (runInstructions_append_some _ _ _ _ _ h8 (runInstructions_append_some _ _ _ _ _ h9 (runInstructions_append_some _ _ _ _ _ h10 (runInstructions_append_some _ _ _ _ _ h11 h12))))))))))))

#print axioms pr12New_run

def productColumn12Model (s : State) (carry w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 : W) (rest : List W) : State :=
  let v0 : W := UInt256.mulMod carry w0 w1
  let v1 : W := v0 + w2
  let v2 : W := MachineState.readWord s.memory 1216
  let v3 : W := UInt256.mulMod w6 v2 w11
  let v4 : W := v3 + v1
  let v5 : W := UInt256.mulMod w7 w16 w11
  let v6 : W := v5 + v4
  let v7 : W := MachineState.readWord s.memory 1280
  let v8 : W := UInt256.mulMod v7 w17 w11
  let v9 : W := v8 + v6
  let v10 : W := UInt256.mulMod w13 w15 w11
  let v11 : W := v10 + v9
  let v12 : W := UInt256.land w14 w3
  let v13 : ByteArray := MachineState.writeBytes s.memory (Data.Bytes.natToBytesPadded v12.toNat 32) 768
  let v14 : W := v11 - v12
  let v15 : W := w11 + v14
  let v16 : W := UInt256.mulMod v15 (N 2048) w11
  let v17 : W := MachineState.readWord v13 1280
  let v18 : W := MachineState.readWord v13 2048
  let v19 : W := UInt256.mulMod w8 v18 w11
  let v20 : W := v19 + v16
  let v21 : W := w8 * v18
  let v22 : W := v21 + v16
  let v23 : W := MachineState.readWord v13 1216
  let v24 : W := MachineState.readWord v13 32
  let v25 : W := MachineState.readWord v13 2016
  let v26 : W := v25 * v24
  let v27 : W := v26 + v22
  let v28 : W := UInt256.mulMod v25 v24 w11
  let v29 : W := v28 + v20
  let v30 : W := MachineState.readWord v13 64
  let v31 : W := MachineState.readWord v13 1984
  let v32 : W := v31 * v30
  let v33 : W := v32 + v27
  let v34 : W := UInt256.mulMod v31 v30 w11
  let v35 : W := v34 + v29
  let v36 : W := MachineState.readWord v13 96
  let v37 : W := MachineState.readWord v13 1952
  let v38 : W := v37 * v36
  let v39 : W := v38 + v33
  let v40 : W := UInt256.mulMod v37 v36 w11
  let v41 : W := v40 + v35
  let v42 : W := MachineState.readWord v13 128
  {s with pc := N 9467, memory := v13, stack := v42 :: w11 :: v41 :: v39 :: w4 :: w5 :: w6 :: w7 :: v23 :: w9 :: w10 :: w11 :: w12 :: v17 :: w14 :: w15 :: w16 :: w17 :: rest}

def productColumn12Program : List Instr := pr12NewProgram

private theorem aux_shared0 (s : State) (z0 : W) :
    (MachineState.readWord (MachineState.writeBytes s.memory (Data.Bytes.natToBytesPadded z0.toNat 32) 768) 1280) = (MachineState.readWord s.memory 1280) := by
  simp (disch := decide) only [addC, addA, addL, mulC, mmC, amC, andC, orC, xorC, eqC, read_disjoint, Challenge.EvmProof.Memory.readWord_writeWord]

private theorem aux_shared1 (s : State) (z0 : W) :
    (MachineState.readWord (MachineState.writeBytes s.memory (Data.Bytes.natToBytesPadded z0.toNat 32) 768) 1216) = (MachineState.readWord s.memory 1216) := by
  simp (disch := decide) only [addC, addA, addL, mulC, mmC, amC, andC, orC, xorC, eqC, read_disjoint, Challenge.EvmProof.Memory.readWord_writeWord]

private theorem aux_shared2 (w11 : W) (z0 : W) :
    (UInt256.mulMod (N 2048) z0 w11) = (UInt256.mulMod z0 (N 2048) w11) := by
  simp (disch := decide) only [addC, addA, addL, mulC, mmC, amC, andC, orC, xorC, eqC, read_disjoint, Challenge.EvmProof.Memory.readWord_writeWord]

private theorem prepared_model_eq (s : State) (carry w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 : W) (rest : List W) :
    productColumn12Model s carry w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 rest = pr12NewModel s carry w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 rest := by
  let o0 : W := UInt256.mulMod carry w0 w1
  let o1 : W := o0 + w2
  let o2 : W := MachineState.readWord s.memory 1216
  let o3 : W := UInt256.mulMod w6 o2 w11
  let o4 : W := o3 + o1
  let o5 : W := UInt256.mulMod w7 w16 w11
  let o6 : W := o5 + o4
  let o7 : W := MachineState.readWord s.memory 1280
  let o8 : W := UInt256.mulMod o7 w17 w11
  let o9 : W := o8 + o6
  let o10 : W := UInt256.mulMod w13 w15 w11
  let o11 : W := o10 + o9
  let o12 : W := UInt256.land w14 w3
  let o13 : ByteArray := MachineState.writeBytes s.memory (Data.Bytes.natToBytesPadded o12.toNat 32) 768
  let o14 : W := o11 - o12
  let o15 : W := w11 + o14
  let o16 : W := UInt256.mulMod o15 (N 2048) w11
  let o17 : W := MachineState.readWord o13 1280
  let o18 : W := MachineState.readWord o13 2048
  let o19 : W := UInt256.mulMod w8 o18 w11
  let o20 : W := o19 + o16
  let o21 : W := w8 * o18
  let o22 : W := o21 + o16
  let o23 : W := MachineState.readWord o13 1216
  let o24 : W := MachineState.readWord o13 32
  let o25 : W := MachineState.readWord o13 2016
  let o26 : W := o25 * o24
  let o27 : W := o26 + o22
  let o28 : W := UInt256.mulMod o25 o24 w11
  let o29 : W := o28 + o20
  let o30 : W := MachineState.readWord o13 64
  let o31 : W := MachineState.readWord o13 1984
  let o32 : W := o31 * o30
  let o33 : W := o32 + o27
  let o34 : W := UInt256.mulMod o31 o30 w11
  let o35 : W := o34 + o29
  let o36 : W := MachineState.readWord o13 96
  let o37 : W := MachineState.readWord o13 1952
  let o38 : W := o37 * o36
  let o39 : W := o38 + o33
  let o40 : W := UInt256.mulMod o37 o36 w11
  let o41 : W := o40 + o35
  let o42 : W := MachineState.readWord o13 128
  let n0 : W := UInt256.mulMod carry w0 w1
  let n1 : W := n0 + w2
  let n2 : W := MachineState.readWord s.memory 1216
  let n3 : W := UInt256.mulMod w6 n2 w11
  let n4 : W := n3 + n1
  let n5 : W := UInt256.mulMod w7 w16 w11
  let n6 : W := n5 + n4
  let n7 : W := MachineState.readWord s.memory 1280
  let n8 : W := UInt256.mulMod n7 w17 w11
  let n9 : W := n8 + n6
  let n10 : W := UInt256.mulMod w13 w15 w11
  let n11 : W := n10 + n9
  let n12 : W := UInt256.land w14 w3
  let n13 : ByteArray := MachineState.writeBytes s.memory (Data.Bytes.natToBytesPadded n12.toNat 32) 768
  let n14 : W := n11 - n12
  let n15 : W := w11 + n14
  let n16 : W := UInt256.mulMod (N 2048) n15 w11
  let n17 : W := MachineState.readWord n13 1280
  let n18 : W := MachineState.readWord n13 2048
  let n19 : W := UInt256.mulMod w8 n18 w11
  let n20 : W := n19 + n16
  let n21 : W := w8 * n18
  let n22 : W := n21 + n16
  let n23 : W := MachineState.readWord n13 1216
  let n24 : W := MachineState.readWord n13 32
  let n25 : W := MachineState.readWord n13 2016
  let n26 : W := n25 * n24
  let n27 : W := n26 + n22
  let n28 : W := UInt256.mulMod n25 n24 w11
  let n29 : W := n28 + n20
  let n30 : W := MachineState.readWord n13 64
  let n31 : W := MachineState.readWord n13 1984
  let n32 : W := n31 * n30
  let n33 : W := n32 + n27
  let n34 : W := UInt256.mulMod n31 n30 w11
  let n35 : W := n34 + n29
  let n36 : W := MachineState.readWord n13 96
  let n37 : W := MachineState.readWord n13 1952
  let n38 : W := n37 * n36
  let n39 : W := n38 + n33
  let n40 : W := UInt256.mulMod n37 n36 w11
  let n41 : W := n40 + n35
  let n42 : W := MachineState.readWord n13 128
  have eq_o17 : o17 = o7 := by
    simpa only [o17, o13, o7] using
      (aux_shared0 s  o12)
  have eq_o23 : o23 = o2 := by
    simpa only [o23, o13, o2] using
      (aux_shared1 s  o12)
  have eq_n0 : n0 = o0 := by
    simp only [n0, o0]
  have eq_n1 : n1 = o1 := by
    simp only [n1, o1, eq_n0]
  have eq_n2 : n2 = o2 := by
    simp only [n2, o2]
  have eq_n3 : n3 = o3 := by
    simp only [n3, o3, eq_n2]
  have eq_n4 : n4 = o4 := by
    simp only [n4, o4, eq_n3, eq_n1]
  have eq_n5 : n5 = o5 := by
    simp only [n5, o5]
  have eq_n6 : n6 = o6 := by
    simp only [n6, o6, eq_n5, eq_n4]
  have eq_n7 : n7 = o7 := by
    simp only [n7, o7]
  have eq_n8 : n8 = o8 := by
    simp only [n8, o8, eq_n7]
  have eq_n9 : n9 = o9 := by
    simp only [n9, o9, eq_n8, eq_n6]
  have eq_n10 : n10 = o10 := by
    simp only [n10, o10]
  have eq_n11 : n11 = o11 := by
    simp only [n11, o11, eq_n10, eq_n9]
  have eq_n12 : n12 = o12 := by
    simp only [n12, o12]
  have eq_n13 : n13 = o13 := by
    simp only [n13, o13, eq_n12]
  have eq_n14 : n14 = o14 := by
    simp only [n14, o14, eq_n11, eq_n12]
  have eq_n15 : n15 = o15 := by
    simp only [n15, o15, eq_n14]
  have eq_n16 : n16 = o16 := by
    simpa only [n16, o16, eq_n15] using
      (aux_shared2 w11 o15)
  have eq_n17 : n17 = o7 := by
    simpa only [n17, n13, o7, eq_n12] using
      (aux_shared0 s  o12)
  have eq_n18 : n18 = o18 := by
    simp only [n18, o18, eq_n13]
  have eq_n19 : n19 = o19 := by
    simp only [n19, o19, eq_n18]
  have eq_n20 : n20 = o20 := by
    simp only [n20, o20, eq_n19, eq_n16]
  have eq_n21 : n21 = o21 := by
    simp only [n21, o21, eq_n18]
  have eq_n22 : n22 = o22 := by
    simp only [n22, o22, eq_n21, eq_n16]
  have eq_n23 : n23 = o2 := by
    simpa only [n23, n13, o2, eq_n12] using
      (aux_shared1 s  o12)
  have eq_n24 : n24 = o24 := by
    simp only [n24, o24, eq_n13]
  have eq_n25 : n25 = o25 := by
    simp only [n25, o25, eq_n13]
  have eq_n26 : n26 = o26 := by
    simp only [n26, o26, eq_n25, eq_n24]
  have eq_n27 : n27 = o27 := by
    simp only [n27, o27, eq_n26, eq_n22]
  have eq_n28 : n28 = o28 := by
    simp only [n28, o28, eq_n25, eq_n24]
  have eq_n29 : n29 = o29 := by
    simp only [n29, o29, eq_n28, eq_n20]
  have eq_n30 : n30 = o30 := by
    simp only [n30, o30, eq_n13]
  have eq_n31 : n31 = o31 := by
    simp only [n31, o31, eq_n13]
  have eq_n32 : n32 = o32 := by
    simp only [n32, o32, eq_n31, eq_n30]
  have eq_n33 : n33 = o33 := by
    simp only [n33, o33, eq_n32, eq_n27]
  have eq_n34 : n34 = o34 := by
    simp only [n34, o34, eq_n31, eq_n30]
  have eq_n35 : n35 = o35 := by
    simp only [n35, o35, eq_n34, eq_n29]
  have eq_n36 : n36 = o36 := by
    simp only [n36, o36, eq_n13]
  have eq_n37 : n37 = o37 := by
    simp only [n37, o37, eq_n13]
  have eq_n38 : n38 = o38 := by
    simp only [n38, o38, eq_n37, eq_n36]
  have eq_n39 : n39 = o39 := by
    simp only [n39, o39, eq_n38, eq_n33]
  have eq_n40 : n40 = o40 := by
    simp only [n40, o40, eq_n37, eq_n36]
  have eq_n41 : n41 = o41 := by
    simp only [n41, o41, eq_n40, eq_n35]
  have eq_n42 : n42 = o42 := by
    simp only [n42, o42, eq_n13]
  change {s with pc := N 9467, memory := o13, stack := o42 :: w11 :: o41 :: o39 :: w4 :: w5 :: w6 :: w7 :: o23 :: w9 :: w10 :: w11 :: w12 :: o17 :: w14 :: w15 :: w16 :: w17 :: rest} =
    {s with pc := N 9467, memory := n13, stack := n42 :: w11 :: n41 :: n39 :: w4 :: w5 :: w6 :: w7 :: n23 :: w9 :: w10 :: w11 :: w12 :: n17 :: w14 :: w15 :: w16 :: w17 :: rest}
  simp only [eq_o17, eq_o23, eq_n0, eq_n1, eq_n2, eq_n3, eq_n4, eq_n5, eq_n6, eq_n7, eq_n8, eq_n9, eq_n10, eq_n11, eq_n12, eq_n13, eq_n14, eq_n15, eq_n16, eq_n17, eq_n18, eq_n19, eq_n20, eq_n21, eq_n22, eq_n23, eq_n24, eq_n25, eq_n26, eq_n27, eq_n28, eq_n29, eq_n30, eq_n31, eq_n32, eq_n33, eq_n34, eq_n35, eq_n36, eq_n37, eq_n38, eq_n39, eq_n40, eq_n41, eq_n42]
theorem productColumn12_run (s : State) (carry w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions productColumn12Program {s with pc := N 9345, stack := carry :: w0 :: w1 :: w2 :: w3 :: w4 :: w5 :: w6 :: w7 :: w8 :: w9 :: w10 :: w11 :: w12 :: w13 :: w14 :: w15 :: w16 :: w17 :: rest} =
      some (productColumn12Model s carry w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 rest) := by
  exact (pr12New_run s carry w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 rest hcap hact).trans
    (congrArg some (prepared_model_eq s carry w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 rest).symm)

#print axioms productColumn12_run
end CycleSubmission.Execution
