import Challenge.Modexp.Submission.Proofs.Prepared.R9Shared.RawPrelude
open CycleSubmission.SharedStackArgs
set_option maxRecDepth 40000
set_option maxHeartbeats 8000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
namespace R9InvConsumeExec
open EvmSemantics EvmSemantics.EVM YulEvmCompiler
open Challenge.EvmProof.Word Challenge.EvmProof.Stepper
open CycleSubmission.Prepared.Arithmetic
open Challenge.Modexp.Submission.Proofs.Bytecode.WindowNibbleKernel
open Challenge.Modexp.Submission.Proofs.Fast
local notation "W" => UInt256
local notation "N" => UInt256.ofNat

def stage4Part0Program : List Instr :=
  [
  .push 1 64,
   .op .MLOAD,
   .op (.Dup dA9),
   .push 2 768,
   .op .MLOAD,
   .op (.Dup dA0),
   .op (.Dup dA3),
   .op .MUL]
def stage4Part0Model (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 : W) (rest : List W) : State :=
  let v0 : W := MachineState.readWord (s.memory) 64
  let v1 : W := MachineState.readWord (s.memory) 768
  let v2 : W := v0 * v1
  {s with pc := N 3849, memory := s.memory, stack := v2 :: v1 :: w8 :: v0 :: w0 :: w1 :: w2 :: w3 :: w4 :: w5 :: w6 :: w7 :: w8 :: w9 :: w10 :: w11 :: w12 :: w13 :: w14 :: w15 :: rest}

theorem stage4Part0_run (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions stage4Part0Program {s with pc := N 3838, memory := s.memory, stack := w0 :: w1 :: w2 :: w3 :: w4 :: w5 :: w6 :: w7 :: w8 :: w9 :: w10 :: w11 :: w12 :: w13 :: w14 :: w15 :: rest} = some (stage4Part0Model s w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 63) : rest.length+j < 1024 := by omega
  have ha64 : (64 : W).toNat = 64 := rfl
  have hf64 := Monpro.activeWords_fix s 64 32 (by decide) (by norm_num) hact
  have ha768 : (768 : W).toNat = 768 := rfl
  have hf768 := Monpro.activeWords_fix s 768 32 (by decide) (by norm_num) hact
  simp [hz, hzn, stage4Part0Program, stage4Part0Model, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, capacity, ha64, hf64, ha768, hf768]

def stage4Part1Program : List Instr :=
  [
  .push 1 32,
   .op .MLOAD,
   .op (.Dup dA9),
   .op .MUL,
   .op .ADD,
   .op (.Swap sA2),
   .op .MULMOD,
   .op (.Dup dA10)]
def stage4Part1Model (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 : W) (rest : List W) : State :=
  let v0 : W := MachineState.readWord (s.memory) 32
  let v1 : W := w8 * v0
  let v2 : W := v1 + w0
  let v3 : W := UInt256.mulMod w3 w1 w2
  {s with pc := N 3858, memory := s.memory, stack := w12 :: v3 :: v2 :: w4 :: w5 :: w6 :: w7 :: w8 :: w9 :: w10 :: w11 :: w12 :: w13 :: w14 :: w15 :: w16 :: w17 :: w18 :: w19 :: rest}

theorem stage4Part1_run (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions stage4Part1Program {s with pc := N 3849, memory := s.memory, stack := w0 :: w1 :: w2 :: w3 :: w4 :: w5 :: w6 :: w7 :: w8 :: w9 :: w10 :: w11 :: w12 :: w13 :: w14 :: w15 :: w16 :: w17 :: w18 :: w19 :: rest} = some (stage4Part1Model s w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 63) : rest.length+j < 1024 := by omega
  have ha32 : (32 : W).toNat = 32 := rfl
  have hf32 := Monpro.activeWords_fix s 32 32 (by decide) (by norm_num) hact
  simp [hz, hzn, stage4Part1Program, stage4Part1Model, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, capacity, ha32, hf32]

def stage4Part2Program : List Instr :=
  [
  .push 1 32,
   .op .MLOAD,
   .op (.Dup dA8),
   .op .MULMOD,
   .op .ADD,
   .op (.Dup dA2),
   .op .ADD,
   .op (.Swap sA1)]
def stage4Part2Model (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 : W) (rest : List W) : State :=
  let v0 : W := MachineState.readWord (s.memory) 32
  let v1 : W := UInt256.mulMod w7 v0 w0
  let v2 : W := v1 + w1
  let v3 : W := w3 + v2
  {s with pc := N 3867, memory := s.memory, stack := w3 :: w2 :: v3 :: w4 :: w5 :: w6 :: w7 :: w8 :: w9 :: w10 :: w11 :: w12 :: w13 :: w14 :: w15 :: w16 :: w17 :: w18 :: rest}

theorem stage4Part2_run (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions stage4Part2Program {s with pc := N 3858, memory := s.memory, stack := w0 :: w1 :: w2 :: w3 :: w4 :: w5 :: w6 :: w7 :: w8 :: w9 :: w10 :: w11 :: w12 :: w13 :: w14 :: w15 :: w16 :: w17 :: w18 :: rest} = some (stage4Part2Model s w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 63) : rest.length+j < 1024 := by omega
  have ha32 : (32 : W).toNat = 32 := rfl
  have hf32 := Monpro.activeWords_fix s 32 32 (by decide) (by norm_num) hact
  simp [hz, hzn, stage4Part2Program, stage4Part2Model, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, capacity, ha32, hf32]

def stage4Part3Program : List Instr :=
  [
  .op .ADD,
   .op (.Dup dA6),
   .op (.Dup dA0),
   .op .MUL,
   .op .ADD,
   .op (.Dup dA4),
   .op (.Dup dA11),
   .op .MUL]
def stage4Part3Model (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 : W) (rest : List W) : State :=
  let v0 : W := w0 + w1
  let v1 : W := w7 * w7
  let v2 : W := v1 + v0
  let v3 : W := w11 * w5
  {s with pc := N 3875, memory := s.memory, stack := v3 :: v2 :: w2 :: w3 :: w4 :: w5 :: w6 :: w7 :: w8 :: w9 :: w10 :: w11 :: w12 :: w13 :: w14 :: w15 :: w16 :: w17 :: rest}

theorem stage4Part3_run (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions stage4Part3Program {s with pc := N 3867, memory := s.memory, stack := w0 :: w1 :: w2 :: w3 :: w4 :: w5 :: w6 :: w7 :: w8 :: w9 :: w10 :: w11 :: w12 :: w13 :: w14 :: w15 :: w16 :: w17 :: rest} = some (stage4Part3Model s w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 63) : rest.length+j < 1024 := by omega
  simp [hz, hzn, stage4Part3Program, stage4Part3Model, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, capacity]

def stage4Part4Program : List Instr :=
  [
  .op .ADD,
   .op (.Dup dA14),
   .op (.Dup dA9),
   .op .MUL,
   .op .ADD,
   .op (.Dup dA2),
   .push 1 192,
   .op .MLOAD]
def stage4Part4Model (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 : W) (rest : List W) : State :=
  let v0 : W := w0 + w1
  let v1 : W := w9 * w15
  let v2 : W := v1 + v0
  let v3 : W := MachineState.readWord (s.memory) 192
  {s with pc := N 3884, memory := s.memory, stack := v3 :: w3 :: v2 :: w2 :: w3 :: w4 :: w5 :: w6 :: w7 :: w8 :: w9 :: w10 :: w11 :: w12 :: w13 :: w14 :: w15 :: w16 :: w17 :: rest}

theorem stage4Part4_run (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions stage4Part4Program {s with pc := N 3875, memory := s.memory, stack := w0 :: w1 :: w2 :: w3 :: w4 :: w5 :: w6 :: w7 :: w8 :: w9 :: w10 :: w11 :: w12 :: w13 :: w14 :: w15 :: w16 :: w17 :: rest} = some (stage4Part4Model s w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 63) : rest.length+j < 1024 := by omega
  have ha192 : (192 : W).toNat = 192 := rfl
  have hf192 := Monpro.activeWords_fix s 192 32 (by decide) (by norm_num) hact
  simp [hz, hzn, stage4Part4Program, stage4Part4Model, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, capacity, ha192, hf192]

def stage4Part5Program : List Instr :=
  [
  .op .MUL,
   .op .ADD,
   .op (.Dup dA11),
   .push 0 0,
   .op .MLOAD,
   .op .MUL,
   .op .ADD,
   .op (.Swap sA0)]
def stage4Part5Model (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 : W) (rest : List W) : State :=
  let v0 : W := w0 * w1
  let v1 : W := v0 + w2
  let v2 : W := MachineState.readWord (s.memory) 0
  let v3 : W := v2 * w13
  let v4 : W := v3 + v1
  {s with pc := N 3892, memory := s.memory, stack := w3 :: v4 :: w4 :: w5 :: w6 :: w7 :: w8 :: w9 :: w10 :: w11 :: w12 :: w13 :: w14 :: w15 :: w16 :: w17 :: w18 :: rest}

theorem stage4Part5_run (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions stage4Part5Program {s with pc := N 3884, memory := s.memory, stack := w0 :: w1 :: w2 :: w3 :: w4 :: w5 :: w6 :: w7 :: w8 :: w9 :: w10 :: w11 :: w12 :: w13 :: w14 :: w15 :: w16 :: w17 :: w18 :: rest} = some (stage4Part5Model s w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 63) : rest.length+j < 1024 := by omega
  have ha0 : (0 : W).toNat = 0 := rfl
  have hf0 := Monpro.activeWords_fix s 0 32 (by decide) (by norm_num) hact
  simp [hz, hzn, stage4Part5Program, stage4Part5Model, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, capacity, ha0, hf0]

def stage4Part6Program : List Instr :=
  [
  .op (.Dup dA9),
   .op (.Dup dA7),
   .op (.Dup dA0),
   .op (.Dup dA0),
   .op .ADD,
   .op (.Swap sA8),
   .op .MULMOD,
   .op .ADD]
def stage4Part6Model (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 : W) (rest : List W) : State :=
  let v0 : W := w6 + w6
  let v1 : W := UInt256.mulMod w6 w6 w9
  let v2 : W := v1 + w0
  {s with pc := N 3900, memory := s.memory, stack := v2 :: w1 :: w2 :: w3 :: w4 :: w5 :: v0 :: w7 :: w8 :: w9 :: w10 :: w11 :: w12 :: w13 :: w14 :: w15 :: w16 :: rest}

theorem stage4Part6_run (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions stage4Part6Program {s with pc := N 3892, memory := s.memory, stack := w0 :: w1 :: w2 :: w3 :: w4 :: w5 :: w6 :: w7 :: w8 :: w9 :: w10 :: w11 :: w12 :: w13 :: w14 :: w15 :: w16 :: rest} = some (stage4Part6Model s w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 63) : rest.length+j < 1024 := by omega
  simp [hz, hzn, stage4Part6Program, stage4Part6Model, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, capacity]

def stage4Part7Program : List Instr :=
  [
  .op (.Dup dA9),
   .op (.Dup dA5),
   .op (.Dup dA12),
   .op .MULMOD,
   .op .ADD,
   .op (.Dup dA9),
   .op (.Dup dA15),
   .op (.Dup dA10)]
def stage4Part7Model (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 : W) (rest : List W) : State :=
  let v0 : W := UInt256.mulMod w10 w4 w9
  let v1 : W := v0 + w0
  {s with pc := N 3908, memory := s.memory, stack := w8 :: w14 :: w9 :: v1 :: w1 :: w2 :: w3 :: w4 :: w5 :: w6 :: w7 :: w8 :: w9 :: w10 :: w11 :: w12 :: w13 :: w14 :: w15 :: w16 :: rest}

theorem stage4Part7_run (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions stage4Part7Program {s with pc := N 3900, memory := s.memory, stack := w0 :: w1 :: w2 :: w3 :: w4 :: w5 :: w6 :: w7 :: w8 :: w9 :: w10 :: w11 :: w12 :: w13 :: w14 :: w15 :: w16 :: rest} = some (stage4Part7Model s w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 63) : rest.length+j < 1024 := by omega
  simp [hz, hzn, stage4Part7Program, stage4Part7Model, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, capacity]

def stage4Part8Program : List Instr :=
  [
  .op .MULMOD,
   .op .ADD,
   .op (.Dup dA9),
   .op (.Dup dA3),
   .push 1 192,
   .op .MLOAD,
   .op .MULMOD,
   .op .ADD]
def stage4Part8Model (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 : W) (rest : List W) : State :=
  let v0 : W := UInt256.mulMod w0 w1 w2
  let v1 : W := v0 + w3
  let v2 : W := MachineState.readWord (s.memory) 192
  let v3 : W := UInt256.mulMod v2 w5 w12
  let v4 : W := v3 + v1
  {s with pc := N 3917, memory := s.memory, stack := v4 :: w4 :: w5 :: w6 :: w7 :: w8 :: w9 :: w10 :: w11 :: w12 :: w13 :: w14 :: w15 :: w16 :: w17 :: w18 :: w19 :: rest}

theorem stage4Part8_run (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions stage4Part8Program {s with pc := N 3908, memory := s.memory, stack := w0 :: w1 :: w2 :: w3 :: w4 :: w5 :: w6 :: w7 :: w8 :: w9 :: w10 :: w11 :: w12 :: w13 :: w14 :: w15 :: w16 :: w17 :: w18 :: w19 :: rest} = some (stage4Part8Model s w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 63) : rest.length+j < 1024 := by omega
  have ha192 : (192 : W).toNat = 192 := rfl
  have hf192 := Monpro.activeWords_fix s 192 32 (by decide) (by norm_num) hact
  simp [hz, hzn, stage4Part8Program, stage4Part8Model, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, capacity, ha192, hf192]

def stage4Part9Program : List Instr :=
  [
  .op (.Dup dA9),
   .op (.Dup dA12),
   .push 0 0,
   .op .MLOAD,
   .op .MULMOD,
   .op .ADD,
   .op (.Dup dA9),
   .op (.Dup dA14)]
def stage4Part9Model (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 : W) (rest : List W) : State :=
  let v0 : W := MachineState.readWord (s.memory) 0
  let v1 : W := UInt256.mulMod v0 w11 w9
  let v2 : W := v1 + w0
  {s with pc := N 3925, memory := s.memory, stack := w13 :: w9 :: v2 :: w1 :: w2 :: w3 :: w4 :: w5 :: w6 :: w7 :: w8 :: w9 :: w10 :: w11 :: w12 :: w13 :: w14 :: w15 :: w16 :: rest}

theorem stage4Part9_run (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions stage4Part9Program {s with pc := N 3917, memory := s.memory, stack := w0 :: w1 :: w2 :: w3 :: w4 :: w5 :: w6 :: w7 :: w8 :: w9 :: w10 :: w11 :: w12 :: w13 :: w14 :: w15 :: w16 :: rest} = some (stage4Part9Model s w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 63) : rest.length+j < 1024 := by omega
  have ha0 : (0 : W).toNat = 0 := rfl
  have hf0 := Monpro.activeWords_fix s 0 32 (by decide) (by norm_num) hact
  simp [hz, hzn, stage4Part9Program, stage4Part9Model, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, capacity, ha0, hf0]

def stage4Part10Program : List Instr :=
  [
  .push 2 2720,
   .op .MLOAD,
   .op (.Dup dA2),
   .op (.Swap sA4),
   .op .MUL,
   .push 30 1766847064778384329583297500742918515827483896875618958121606201292619775,
   .op .AND,
   .op (.Dup dA0)]
def stage4Part10Model (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 : W) (rest : List W) : State :=
  let v0 : W := MachineState.readWord (s.memory) 2720
  let v1 : W := w3 * v0
  let v2 : W := UInt256.land (N 1766847064778384329583297500742918515827483896875618958121606201292619775) v1
  {s with pc := N 3965, memory := s.memory, stack := v2 :: v2 :: w0 :: w1 :: w2 :: w1 :: w4 :: w5 :: w6 :: w7 :: w8 :: w9 :: w10 :: w11 :: w12 :: w13 :: w14 :: w15 :: w16 :: w17 :: w18 :: rest}

theorem stage4Part10_run (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions stage4Part10Program {s with pc := N 3925, memory := s.memory, stack := w0 :: w1 :: w2 :: w3 :: w4 :: w5 :: w6 :: w7 :: w8 :: w9 :: w10 :: w11 :: w12 :: w13 :: w14 :: w15 :: w16 :: w17 :: w18 :: rest} = some (stage4Part10Model s w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 63) : rest.length+j < 1024 := by omega
  have ha2720 : (2720 : W).toNat = 2720 := rfl
  have hf2720 := Monpro.activeWords_fix s 2720 32 (by decide) (by norm_num) hact
  simp [hz, hzn, stage4Part10Program, stage4Part10Model, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, capacity, ha2720, hf2720]

def stage4Part11Program : List Instr :=
  [
  .push 1 224,
   .op .MSTORE,
   .op .MULMOD,
   .op .ADD,
   .push 2 2048,
   .op .MULMOD]
def stage4Part11Model (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 w20 : W) (rest : List W) : State :=
  let v0 : ByteArray := MachineState.writeBytes (s.memory) (Data.Bytes.natToBytesPadded w0.toNat 32) 224
  let v1 : W := UInt256.mulMod w1 w2 w3
  let v2 : W := v1 + w4
  let v3 : W := UInt256.mulMod (N 2048) v2 w5
  {s with pc := N 3974, memory := v0, stack := v3 :: w6 :: w7 :: w8 :: w9 :: w10 :: w11 :: w12 :: w13 :: w14 :: w15 :: w16 :: w17 :: w18 :: w19 :: w20 :: rest}

theorem stage4Part11_run (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 w20 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions stage4Part11Program {s with pc := N 3965, memory := s.memory, stack := w0 :: w1 :: w2 :: w3 :: w4 :: w5 :: w6 :: w7 :: w8 :: w9 :: w10 :: w11 :: w12 :: w13 :: w14 :: w15 :: w16 :: w17 :: w18 :: w19 :: w20 :: rest} = some (stage4Part11Model s w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 w20 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 63) : rest.length+j < 1024 := by omega
  have ha224 : (224 : W).toNat = 224 := rfl
  have hf224 := Monpro.activeWords_fix s 224 32 (by decide) (by norm_num) hact
  simp [hz, hzn, stage4Part11Program, stage4Part11Model, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, capacity, ha224, hf224]

def stage4Program : List Instr := (stage4Part0Program ++ (stage4Part1Program ++ (stage4Part2Program ++ (stage4Part3Program ++ (stage4Part4Program ++ (stage4Part5Program ++ (stage4Part6Program ++ (stage4Part7Program ++ (stage4Part8Program ++ (stage4Part9Program ++ (stage4Part10Program ++ stage4Part11Program)))))))))))
def stage4Model (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 : W) (rest : List W) : State :=
  let v0 : W := MachineState.readWord (s.memory) 64
  let v1 : W := MachineState.readWord (s.memory) 768
  let v2 : W := v0 * v1
  let v3 : W := MachineState.readWord (s.memory) 32
  let v4 : W := w4 * v3
  let v5 : W := v4 + v2
  let v6 : W := UInt256.mulMod v0 v1 w8
  let v7 : W := MachineState.readWord (s.memory) 32
  let v8 : W := UInt256.mulMod w4 v7 w8
  let v9 : W := v8 + v6
  let v10 : W := w0 + v9
  let v11 : W := w0 + v5
  let v12 : W := w5 * w5
  let v13 : W := v12 + v11
  let v14 : W := w9 * w3
  let v15 : W := v14 + v13
  let v16 : W := w7 * w13
  let v17 : W := v16 + v15
  let v18 : W := MachineState.readWord (s.memory) 192
  let v19 : W := v18 * w1
  let v20 : W := v19 + v17
  let v21 : W := MachineState.readWord (s.memory) 0
  let v22 : W := v21 * w10
  let v23 : W := v22 + v20
  let v24 : W := w5 + w5
  let v25 : W := UInt256.mulMod w5 w5 w8
  let v26 : W := v25 + v10
  let v27 : W := UInt256.mulMod w9 w3 w8
  let v28 : W := v27 + v26
  let v29 : W := UInt256.mulMod w7 w13 w8
  let v30 : W := v29 + v28
  let v31 : W := MachineState.readWord (s.memory) 192
  let v32 : W := UInt256.mulMod v31 w1 w8
  let v33 : W := v32 + v30
  let v34 : W := MachineState.readWord (s.memory) 0
  let v35 : W := UInt256.mulMod v34 w10 w8
  let v36 : W := v35 + v33
  let v37 : W := MachineState.readWord (s.memory) 2720
  let v38 : W := v23 * v37
  let v39 : W := UInt256.land (N 1766847064778384329583297500742918515827483896875618958121606201292619775) v38
  let v40 : ByteArray := MachineState.writeBytes (s.memory) (Data.Bytes.natToBytesPadded v39.toNat 32) 224
  let v41 : W := UInt256.mulMod v39 w12 w8
  let v42 : W := v41 + v36
  let v43 : W := UInt256.mulMod (N 2048) v42 w8
  {s with pc := N 3974, memory := v40, stack := v43 :: w1 :: w2 :: w3 :: w4 :: v24 :: w6 :: w7 :: w8 :: w9 :: w10 :: w11 :: w12 :: w13 :: w14 :: w15 :: rest}

theorem stage4_run (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions stage4Program {s with pc := N 3838, memory := s.memory, stack := w0 :: w1 :: w2 :: w3 :: w4 :: w5 :: w6 :: w7 :: w8 :: w9 :: w10 :: w11 :: w12 :: w13 :: w14 :: w15 :: rest} = some (stage4Model s w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 rest) := by
  let v0 : W := MachineState.readWord (s.memory) 64
  let v1 : W := MachineState.readWord (s.memory) 768
  let v2 : W := v0 * v1
  let v3 : W := MachineState.readWord (s.memory) 32
  let v4 : W := w4 * v3
  let v5 : W := v4 + v2
  let v6 : W := UInt256.mulMod v0 v1 w8
  let v7 : W := MachineState.readWord (s.memory) 32
  let v8 : W := UInt256.mulMod w4 v7 w8
  let v9 : W := v8 + v6
  let v10 : W := w0 + v9
  let v11 : W := w0 + v5
  let v12 : W := w5 * w5
  let v13 : W := v12 + v11
  let v14 : W := w9 * w3
  let v15 : W := v14 + v13
  let v16 : W := w7 * w13
  let v17 : W := v16 + v15
  let v18 : W := MachineState.readWord (s.memory) 192
  let v19 : W := v18 * w1
  let v20 : W := v19 + v17
  let v21 : W := MachineState.readWord (s.memory) 0
  let v22 : W := v21 * w10
  let v23 : W := v22 + v20
  let v24 : W := w5 + w5
  let v25 : W := UInt256.mulMod w5 w5 w8
  let v26 : W := v25 + v10
  let v27 : W := UInt256.mulMod w9 w3 w8
  let v28 : W := v27 + v26
  let v29 : W := UInt256.mulMod w7 w13 w8
  let v30 : W := v29 + v28
  let v31 : W := MachineState.readWord (s.memory) 192
  let v32 : W := UInt256.mulMod v31 w1 w8
  let v33 : W := v32 + v30
  let v34 : W := MachineState.readWord (s.memory) 0
  let v35 : W := UInt256.mulMod v34 w10 w8
  let v36 : W := v35 + v33
  let v37 : W := MachineState.readWord (s.memory) 2720
  let v38 : W := v23 * v37
  let v39 : W := UInt256.land (N 1766847064778384329583297500742918515827483896875618958121606201292619775) v38
  let v40 : ByteArray := MachineState.writeBytes (s.memory) (Data.Bytes.natToBytesPadded v39.toNat 32) 224
  let v41 : W := UInt256.mulMod v39 w12 w8
  let v42 : W := v41 + v36
  let v43 : W := UInt256.mulMod (N 2048) v42 w8
  have h0 : runInstructions stage4Part0Program {s with pc := N 3838, memory := s.memory, stack := w0 :: w1 :: w2 :: w3 :: w4 :: w5 :: w6 :: w7 :: w8 :: w9 :: w10 :: w11 :: w12 :: w13 :: w14 :: w15 :: rest} = some {s with pc := N 3849, memory := s.memory, stack := v2 :: v1 :: w8 :: v0 :: w0 :: w1 :: w2 :: w3 :: w4 :: w5 :: w6 :: w7 :: w8 :: w9 :: w10 :: w11 :: w12 :: w13 :: w14 :: w15 :: rest} := by
    simpa only [stage4Part0Model, v0, v1, v2] using stage4Part0_run ({s with memory := s.memory}) w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 rest hcap hact
  have h1 : runInstructions stage4Part1Program {s with pc := N 3849, memory := s.memory, stack := v2 :: v1 :: w8 :: v0 :: w0 :: w1 :: w2 :: w3 :: w4 :: w5 :: w6 :: w7 :: w8 :: w9 :: w10 :: w11 :: w12 :: w13 :: w14 :: w15 :: rest} = some {s with pc := N 3858, memory := s.memory, stack := w8 :: v6 :: v5 :: w0 :: w1 :: w2 :: w3 :: w4 :: w5 :: w6 :: w7 :: w8 :: w9 :: w10 :: w11 :: w12 :: w13 :: w14 :: w15 :: rest} := by
    simpa only [stage4Part1Model, v3, v4, v5, v6] using stage4Part1_run ({s with memory := s.memory}) v2 v1 w8 v0 w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 rest hcap hact
  have h2 : runInstructions stage4Part2Program {s with pc := N 3858, memory := s.memory, stack := w8 :: v6 :: v5 :: w0 :: w1 :: w2 :: w3 :: w4 :: w5 :: w6 :: w7 :: w8 :: w9 :: w10 :: w11 :: w12 :: w13 :: w14 :: w15 :: rest} = some {s with pc := N 3867, memory := s.memory, stack := w0 :: v5 :: v10 :: w1 :: w2 :: w3 :: w4 :: w5 :: w6 :: w7 :: w8 :: w9 :: w10 :: w11 :: w12 :: w13 :: w14 :: w15 :: rest} := by
    simpa only [stage4Part2Model, v7, v8, v9, v10] using stage4Part2_run ({s with memory := s.memory}) w8 v6 v5 w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 rest hcap hact
  have h3 : runInstructions stage4Part3Program {s with pc := N 3867, memory := s.memory, stack := w0 :: v5 :: v10 :: w1 :: w2 :: w3 :: w4 :: w5 :: w6 :: w7 :: w8 :: w9 :: w10 :: w11 :: w12 :: w13 :: w14 :: w15 :: rest} = some {s with pc := N 3875, memory := s.memory, stack := v14 :: v13 :: v10 :: w1 :: w2 :: w3 :: w4 :: w5 :: w6 :: w7 :: w8 :: w9 :: w10 :: w11 :: w12 :: w13 :: w14 :: w15 :: rest} := by
    simpa only [stage4Part3Model, v11, v12, v13, v14] using stage4Part3_run ({s with memory := s.memory}) w0 v5 v10 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 rest hcap hact
  have h4 : runInstructions stage4Part4Program {s with pc := N 3875, memory := s.memory, stack := v14 :: v13 :: v10 :: w1 :: w2 :: w3 :: w4 :: w5 :: w6 :: w7 :: w8 :: w9 :: w10 :: w11 :: w12 :: w13 :: w14 :: w15 :: rest} = some {s with pc := N 3884, memory := s.memory, stack := v18 :: w1 :: v17 :: v10 :: w1 :: w2 :: w3 :: w4 :: w5 :: w6 :: w7 :: w8 :: w9 :: w10 :: w11 :: w12 :: w13 :: w14 :: w15 :: rest} := by
    simpa only [stage4Part4Model, v15, v16, v17, v18] using stage4Part4_run ({s with memory := s.memory}) v14 v13 v10 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 rest hcap hact
  have h5 : runInstructions stage4Part5Program {s with pc := N 3884, memory := s.memory, stack := v18 :: w1 :: v17 :: v10 :: w1 :: w2 :: w3 :: w4 :: w5 :: w6 :: w7 :: w8 :: w9 :: w10 :: w11 :: w12 :: w13 :: w14 :: w15 :: rest} = some {s with pc := N 3892, memory := s.memory, stack := v10 :: v23 :: w1 :: w2 :: w3 :: w4 :: w5 :: w6 :: w7 :: w8 :: w9 :: w10 :: w11 :: w12 :: w13 :: w14 :: w15 :: rest} := by
    simpa only [stage4Part5Model, v19, v20, v21, v22, v23] using stage4Part5_run ({s with memory := s.memory}) v18 w1 v17 v10 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 rest hcap hact
  have h6 : runInstructions stage4Part6Program {s with pc := N 3892, memory := s.memory, stack := v10 :: v23 :: w1 :: w2 :: w3 :: w4 :: w5 :: w6 :: w7 :: w8 :: w9 :: w10 :: w11 :: w12 :: w13 :: w14 :: w15 :: rest} = some {s with pc := N 3900, memory := s.memory, stack := v26 :: v23 :: w1 :: w2 :: w3 :: w4 :: v24 :: w6 :: w7 :: w8 :: w9 :: w10 :: w11 :: w12 :: w13 :: w14 :: w15 :: rest} := by
    simpa only [stage4Part6Model, v24, v25, v26] using stage4Part6_run ({s with memory := s.memory}) v10 v23 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 rest hcap hact
  have h7 : runInstructions stage4Part7Program {s with pc := N 3900, memory := s.memory, stack := v26 :: v23 :: w1 :: w2 :: w3 :: w4 :: v24 :: w6 :: w7 :: w8 :: w9 :: w10 :: w11 :: w12 :: w13 :: w14 :: w15 :: rest} = some {s with pc := N 3908, memory := s.memory, stack := w7 :: w13 :: w8 :: v28 :: v23 :: w1 :: w2 :: w3 :: w4 :: v24 :: w6 :: w7 :: w8 :: w9 :: w10 :: w11 :: w12 :: w13 :: w14 :: w15 :: rest} := by
    simpa only [stage4Part7Model, v27, v28] using stage4Part7_run ({s with memory := s.memory}) v26 v23 w1 w2 w3 w4 v24 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 rest hcap hact
  have h8 : runInstructions stage4Part8Program {s with pc := N 3908, memory := s.memory, stack := w7 :: w13 :: w8 :: v28 :: v23 :: w1 :: w2 :: w3 :: w4 :: v24 :: w6 :: w7 :: w8 :: w9 :: w10 :: w11 :: w12 :: w13 :: w14 :: w15 :: rest} = some {s with pc := N 3917, memory := s.memory, stack := v33 :: v23 :: w1 :: w2 :: w3 :: w4 :: v24 :: w6 :: w7 :: w8 :: w9 :: w10 :: w11 :: w12 :: w13 :: w14 :: w15 :: rest} := by
    simpa only [stage4Part8Model, v29, v30, v31, v32, v33] using stage4Part8_run ({s with memory := s.memory}) w7 w13 w8 v28 v23 w1 w2 w3 w4 v24 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 rest hcap hact
  have h9 : runInstructions stage4Part9Program {s with pc := N 3917, memory := s.memory, stack := v33 :: v23 :: w1 :: w2 :: w3 :: w4 :: v24 :: w6 :: w7 :: w8 :: w9 :: w10 :: w11 :: w12 :: w13 :: w14 :: w15 :: rest} = some {s with pc := N 3925, memory := s.memory, stack := w12 :: w8 :: v36 :: v23 :: w1 :: w2 :: w3 :: w4 :: v24 :: w6 :: w7 :: w8 :: w9 :: w10 :: w11 :: w12 :: w13 :: w14 :: w15 :: rest} := by
    simpa only [stage4Part9Model, v34, v35, v36] using stage4Part9_run ({s with memory := s.memory}) v33 v23 w1 w2 w3 w4 v24 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 rest hcap hact
  have h10 : runInstructions stage4Part10Program {s with pc := N 3925, memory := s.memory, stack := w12 :: w8 :: v36 :: v23 :: w1 :: w2 :: w3 :: w4 :: v24 :: w6 :: w7 :: w8 :: w9 :: w10 :: w11 :: w12 :: w13 :: w14 :: w15 :: rest} = some {s with pc := N 3965, memory := s.memory, stack := v39 :: v39 :: w12 :: w8 :: v36 :: w8 :: w1 :: w2 :: w3 :: w4 :: v24 :: w6 :: w7 :: w8 :: w9 :: w10 :: w11 :: w12 :: w13 :: w14 :: w15 :: rest} := by
    simpa only [stage4Part10Model, v37, v38, v39] using stage4Part10_run ({s with memory := s.memory}) w12 w8 v36 v23 w1 w2 w3 w4 v24 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 rest hcap hact
  have h11 : runInstructions stage4Part11Program {s with pc := N 3965, memory := s.memory, stack := v39 :: v39 :: w12 :: w8 :: v36 :: w8 :: w1 :: w2 :: w3 :: w4 :: v24 :: w6 :: w7 :: w8 :: w9 :: w10 :: w11 :: w12 :: w13 :: w14 :: w15 :: rest} = some {s with pc := N 3974, memory := v40, stack := v43 :: w1 :: w2 :: w3 :: w4 :: v24 :: w6 :: w7 :: w8 :: w9 :: w10 :: w11 :: w12 :: w13 :: w14 :: w15 :: rest} := by
    simpa only [stage4Part11Model, v40, v41, v42, v43] using stage4Part11_run ({s with memory := s.memory}) v39 v39 w12 w8 v36 w8 w1 w2 w3 w4 v24 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 rest hcap hact
  exact (runInstructions_append_some _ _ _ _ _ h0 (runInstructions_append_some _ _ _ _ _ h1 (runInstructions_append_some _ _ _ _ _ h2 (runInstructions_append_some _ _ _ _ _ h3 (runInstructions_append_some _ _ _ _ _ h4 (runInstructions_append_some _ _ _ _ _ h5 (runInstructions_append_some _ _ _ _ _ h6 (runInstructions_append_some _ _ _ _ _ h7 (runInstructions_append_some _ _ _ _ _ h8 (runInstructions_append_some _ _ _ _ _ h9 (runInstructions_append_some _ _ _ _ _ h10 h11)))))))))))

end R9InvConsumeExec
