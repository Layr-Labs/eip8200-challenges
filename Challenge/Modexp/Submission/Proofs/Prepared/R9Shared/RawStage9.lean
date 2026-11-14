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

def stage9Part0Program : List Instr :=
  [
  .op (.Dup dA15),
   .op (.Dup dA9),
   .push 2 1248,
   .op .MLOAD,
   .op (.Swap sA6),
   .op (.Dup dA0),
   .op (.Dup dA3),
   .op .MUL]
def stage9Part0Model (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 : W) (rest : List W) : State :=
  let v0 : W := MachineState.readWord (s.memory) 1248
  let v1 : W := w15 * w4
  {s with pc := N 4755, memory := s.memory, stack := v1 :: w4 :: w8 :: w15 :: w0 :: w1 :: w2 :: w3 :: v0 :: w5 :: w6 :: w7 :: w8 :: w9 :: w10 :: w11 :: w12 :: w13 :: w14 :: w15 :: rest}

theorem stage9Part0_run (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions stage9Part0Program {s with pc := N 4745, memory := s.memory, stack := w0 :: w1 :: w2 :: w3 :: w4 :: w5 :: w6 :: w7 :: w8 :: w9 :: w10 :: w11 :: w12 :: w13 :: w14 :: w15 :: rest} = some (stage9Part0Model s w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 63) : rest.length+j < 1024 := by omega
  have ha1248 : (1248 : W).toNat = 1248 := rfl
  have hf1248 := Monpro.activeWords_fix s 1248 32 (by decide) (by norm_num) hact
  simp [hz, hzn, stage9Part0Program, stage9Part0Model, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, capacity, ha1248, hf1248]

def stage9Part1Program : List Instr :=
  [
  .push 1 160,
   .op .MLOAD,
   .op (.Dup dA10),
   .op .MUL,
   .op .ADD,
   .push 1 128,
   .op .MLOAD]
def stage9Part1Model (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 : W) (rest : List W) : State :=
  let v0 : W := MachineState.readWord (s.memory) 160
  let v1 : W := w9 * v0
  let v2 : W := v1 + w0
  let v3 : W := MachineState.readWord (s.memory) 128
  {s with pc := N 4764, memory := s.memory, stack := v3 :: v2 :: w1 :: w2 :: w3 :: w4 :: w5 :: w6 :: w7 :: w8 :: w9 :: w10 :: w11 :: w12 :: w13 :: w14 :: w15 :: w16 :: w17 :: w18 :: w19 :: rest}

theorem stage9Part1_run (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions stage9Part1Program {s with pc := N 4755, memory := s.memory, stack := w0 :: w1 :: w2 :: w3 :: w4 :: w5 :: w6 :: w7 :: w8 :: w9 :: w10 :: w11 :: w12 :: w13 :: w14 :: w15 :: w16 :: w17 :: w18 :: w19 :: rest} = some (stage9Part1Model s w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 63) : rest.length+j < 1024 := by omega
  have ha128 : (128 : W).toNat = 128 := rfl
  have hf128 := Monpro.activeWords_fix s 128 32 (by decide) (by norm_num) hact
  have ha160 : (160 : W).toNat = 160 := rfl
  have hf160 := Monpro.activeWords_fix s 160 32 (by decide) (by norm_num) hact
  simp [hz, hzn, stage9Part1Program, stage9Part1Model, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, capacity, ha128, hf128, ha160, hf160]

def stage9Part2Program : List Instr :=
  [
  .push 1 32,
   .op .MLOAD,
   .op .MUL,
   .op .ADD,
   .op (.Dup dA15),
   .push 1 64,
   .op .MLOAD]
def stage9Part2Model (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 w20 : W) (rest : List W) : State :=
  let v0 : W := MachineState.readWord (s.memory) 32
  let v1 : W := v0 * w0
  let v2 : W := v1 + w1
  let v3 : W := MachineState.readWord (s.memory) 64
  {s with pc := N 4773, memory := s.memory, stack := v3 :: w16 :: v2 :: w2 :: w3 :: w4 :: w5 :: w6 :: w7 :: w8 :: w9 :: w10 :: w11 :: w12 :: w13 :: w14 :: w15 :: w16 :: w17 :: w18 :: w19 :: w20 :: rest}

theorem stage9Part2_run (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 w20 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions stage9Part2Program {s with pc := N 4764, memory := s.memory, stack := w0 :: w1 :: w2 :: w3 :: w4 :: w5 :: w6 :: w7 :: w8 :: w9 :: w10 :: w11 :: w12 :: w13 :: w14 :: w15 :: w16 :: w17 :: w18 :: w19 :: w20 :: rest} = some (stage9Part2Model s w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 w20 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 63) : rest.length+j < 1024 := by omega
  have ha32 : (32 : W).toNat = 32 := rfl
  have hf32 := Monpro.activeWords_fix s 32 32 (by decide) (by norm_num) hact
  have ha64 : (64 : W).toNat = 64 := rfl
  have hf64 := Monpro.activeWords_fix s 64 32 (by decide) (by norm_num) hact
  simp [hz, hzn, stage9Part2Program, stage9Part2Model, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, capacity, ha32, hf32, ha64, hf64]

def stage9Part3Program : List Instr :=
  [
  .op .MUL,
   .op .ADD,
   .op (.Swap sA2),
   .op .MULMOD,
   .op (.Dup dA10),
   .push 1 160,
   .op .MLOAD,
   .op (.Dup dA9)]
def stage9Part3Model (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 w20 w21 : W) (rest : List W) : State :=
  let v0 : W := w0 * w1
  let v1 : W := v0 + w2
  let v2 : W := UInt256.mulMod w5 w3 w4
  let v3 : W := MachineState.readWord (s.memory) 160
  {s with pc := N 4782, memory := s.memory, stack := w11 :: v3 :: w14 :: v2 :: v1 :: w6 :: w7 :: w8 :: w9 :: w10 :: w11 :: w12 :: w13 :: w14 :: w15 :: w16 :: w17 :: w18 :: w19 :: w20 :: w21 :: rest}

theorem stage9Part3_run (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 w20 w21 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions stage9Part3Program {s with pc := N 4773, memory := s.memory, stack := w0 :: w1 :: w2 :: w3 :: w4 :: w5 :: w6 :: w7 :: w8 :: w9 :: w10 :: w11 :: w12 :: w13 :: w14 :: w15 :: w16 :: w17 :: w18 :: w19 :: w20 :: w21 :: rest} = some (stage9Part3Model s w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 w20 w21 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 63) : rest.length+j < 1024 := by omega
  have ha160 : (160 : W).toNat = 160 := rfl
  have hf160 := Monpro.activeWords_fix s 160 32 (by decide) (by norm_num) hact
  simp [hz, hzn, stage9Part3Program, stage9Part3Model, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, capacity, ha160, hf160]

def stage9Part4Program : List Instr :=
  [
  .op .MULMOD,
   .op .ADD,
   .op (.Dup dA10),
   .push 1 128,
   .op .MLOAD,
   .push 1 32,
   .op .MLOAD,
   .op .MULMOD]
def stage9Part4Model (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 w20 : W) (rest : List W) : State :=
  let v0 : W := UInt256.mulMod w0 w1 w2
  let v1 : W := v0 + w3
  let v2 : W := MachineState.readWord (s.memory) 128
  let v3 : W := MachineState.readWord (s.memory) 32
  let v4 : W := UInt256.mulMod v3 v2 w13
  {s with pc := N 4792, memory := s.memory, stack := v4 :: v1 :: w4 :: w5 :: w6 :: w7 :: w8 :: w9 :: w10 :: w11 :: w12 :: w13 :: w14 :: w15 :: w16 :: w17 :: w18 :: w19 :: w20 :: rest}

theorem stage9Part4_run (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 w20 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions stage9Part4Program {s with pc := N 4782, memory := s.memory, stack := w0 :: w1 :: w2 :: w3 :: w4 :: w5 :: w6 :: w7 :: w8 :: w9 :: w10 :: w11 :: w12 :: w13 :: w14 :: w15 :: w16 :: w17 :: w18 :: w19 :: w20 :: rest} = some (stage9Part4Model s w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 w20 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 63) : rest.length+j < 1024 := by omega
  have ha32 : (32 : W).toNat = 32 := rfl
  have hf32 := Monpro.activeWords_fix s 32 32 (by decide) (by norm_num) hact
  have ha128 : (128 : W).toNat = 128 := rfl
  have hf128 := Monpro.activeWords_fix s 128 32 (by decide) (by norm_num) hact
  simp [hz, hzn, stage9Part4Program, stage9Part4Model, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, capacity, ha32, hf32, ha128, hf128]

def stage9Part5Program : List Instr :=
  [
  .op .ADD,
   .op (.Dup dA10),
   .op (.Dup dA14),
   .push 1 64,
   .op .MLOAD,
   .op .MULMOD,
   .op .ADD]
def stage9Part5Model (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 : W) (rest : List W) : State :=
  let v0 : W := w0 + w1
  let v1 : W := MachineState.readWord (s.memory) 64
  let v2 : W := UInt256.mulMod v1 w14 w11
  let v3 : W := v2 + v0
  {s with pc := N 4800, memory := s.memory, stack := v3 :: w2 :: w3 :: w4 :: w5 :: w6 :: w7 :: w8 :: w9 :: w10 :: w11 :: w12 :: w13 :: w14 :: w15 :: w16 :: w17 :: w18 :: rest}

theorem stage9Part5_run (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions stage9Part5Program {s with pc := N 4792, memory := s.memory, stack := w0 :: w1 :: w2 :: w3 :: w4 :: w5 :: w6 :: w7 :: w8 :: w9 :: w10 :: w11 :: w12 :: w13 :: w14 :: w15 :: w16 :: w17 :: w18 :: rest} = some (stage9Part5Model s w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 63) : rest.length+j < 1024 := by omega
  have ha64 : (64 : W).toNat = 64 := rfl
  have hf64 := Monpro.activeWords_fix s 64 32 (by decide) (by norm_num) hact
  simp [hz, hzn, stage9Part5Program, stage9Part5Model, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, capacity, ha64, hf64]

def stage9Part6Program : List Instr :=
  [
  .op (.Dup dA2),
   .op .ADD,
   .op (.Swap sA1),
   .op .ADD,
   .push 2 1088,
   .op .MLOAD,
   .op (.Dup dA11),
   .op .MUL]
def stage9Part6Model (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 : W) (rest : List W) : State :=
  let v0 : W := w2 + w0
  let v1 : W := w2 + w1
  let v2 : W := MachineState.readWord (s.memory) 1088
  let v3 : W := w11 * v2
  {s with pc := N 4810, memory := s.memory, stack := v3 :: v1 :: v0 :: w3 :: w4 :: w5 :: w6 :: w7 :: w8 :: w9 :: w10 :: w11 :: w12 :: w13 :: w14 :: w15 :: w16 :: w17 :: rest}

theorem stage9Part6_run (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions stage9Part6Program {s with pc := N 4800, memory := s.memory, stack := w0 :: w1 :: w2 :: w3 :: w4 :: w5 :: w6 :: w7 :: w8 :: w9 :: w10 :: w11 :: w12 :: w13 :: w14 :: w15 :: w16 :: w17 :: rest} = some (stage9Part6Model s w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 63) : rest.length+j < 1024 := by omega
  have ha1088 : (1088 : W).toNat = 1088 := rfl
  have hf1088 := Monpro.activeWords_fix s 1088 32 (by decide) (by norm_num) hact
  simp [hz, hzn, stage9Part6Program, stage9Part6Model, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, capacity, ha1088, hf1088]

def stage9Part7Program : List Instr :=
  [
  .op .ADD,
   .push 1 192,
   .op .MLOAD,
   .op (.Dup dA9),
   .op .MUL,
   .op .ADD,
   .op (.Dup dA3)]
def stage9Part7Model (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 : W) (rest : List W) : State :=
  let v0 : W := w0 + w1
  let v1 : W := MachineState.readWord (s.memory) 192
  let v2 : W := w9 * v1
  let v3 : W := v2 + v0
  {s with pc := N 4818, memory := s.memory, stack := w4 :: v3 :: w2 :: w3 :: w4 :: w5 :: w6 :: w7 :: w8 :: w9 :: w10 :: w11 :: w12 :: w13 :: w14 :: w15 :: w16 :: w17 :: rest}

theorem stage9Part7_run (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions stage9Part7Program {s with pc := N 4810, memory := s.memory, stack := w0 :: w1 :: w2 :: w3 :: w4 :: w5 :: w6 :: w7 :: w8 :: w9 :: w10 :: w11 :: w12 :: w13 :: w14 :: w15 :: w16 :: w17 :: rest} = some (stage9Part7Model s w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 63) : rest.length+j < 1024 := by omega
  have ha192 : (192 : W).toNat = 192 := rfl
  have hf192 := Monpro.activeWords_fix s 192 32 (by decide) (by norm_num) hact
  simp [hz, hzn, stage9Part7Program, stage9Part7Model, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, capacity, ha192, hf192]

def stage9Part8Program : List Instr :=
  [
  .push 0 0,
   .op .MLOAD,
   .op .MUL,
   .op .ADD,
   .op (.Dup dA7),
   .push 1 224,
   .op .MLOAD,
   .op .MUL]
def stage9Part8Model (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 : W) (rest : List W) : State :=
  let v0 : W := MachineState.readWord (s.memory) 0
  let v1 : W := v0 * w0
  let v2 : W := v1 + w1
  let v3 : W := MachineState.readWord (s.memory) 224
  let v4 : W := v3 * w8
  {s with pc := N 4827, memory := s.memory, stack := v4 :: v2 :: w2 :: w3 :: w4 :: w5 :: w6 :: w7 :: w8 :: w9 :: w10 :: w11 :: w12 :: w13 :: w14 :: w15 :: w16 :: w17 :: rest}

theorem stage9Part8_run (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions stage9Part8Program {s with pc := N 4818, memory := s.memory, stack := w0 :: w1 :: w2 :: w3 :: w4 :: w5 :: w6 :: w7 :: w8 :: w9 :: w10 :: w11 :: w12 :: w13 :: w14 :: w15 :: w16 :: w17 :: rest} = some (stage9Part8Model s w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 63) : rest.length+j < 1024 := by omega
  have ha0 : (0 : W).toNat = 0 := rfl
  have hf0 := Monpro.activeWords_fix s 0 32 (by decide) (by norm_num) hact
  have ha224 : (224 : W).toNat = 224 := rfl
  have hf224 := Monpro.activeWords_fix s 224 32 (by decide) (by norm_num) hact
  simp [hz, hzn, stage9Part8Program, stage9Part8Model, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, capacity, ha0, hf0, ha224, hf224]

def stage9Part9Program : List Instr :=
  [
  .op .ADD,
   .op (.Dup dA4),
   .push 2 1216,
   .op .MLOAD,
   .op .MUL,
   .op .ADD,
   .op (.Dup dA14),
   .op (.Dup dA6)]
def stage9Part9Model (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 : W) (rest : List W) : State :=
  let v0 : W := w0 + w1
  let v1 : W := MachineState.readWord (s.memory) 1216
  let v2 : W := v1 * w5
  let v3 : W := v2 + v0
  {s with pc := N 4837, memory := s.memory, stack := w6 :: w15 :: v3 :: w2 :: w3 :: w4 :: w5 :: w6 :: w7 :: w8 :: w9 :: w10 :: w11 :: w12 :: w13 :: w14 :: w15 :: w16 :: w17 :: rest}

theorem stage9Part9_run (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions stage9Part9Program {s with pc := N 4827, memory := s.memory, stack := w0 :: w1 :: w2 :: w3 :: w4 :: w5 :: w6 :: w7 :: w8 :: w9 :: w10 :: w11 :: w12 :: w13 :: w14 :: w15 :: w16 :: w17 :: rest} = some (stage9Part9Model s w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 63) : rest.length+j < 1024 := by omega
  have ha1216 : (1216 : W).toNat = 1216 := rfl
  have hf1216 := Monpro.activeWords_fix s 1216 32 (by decide) (by norm_num) hact
  simp [hz, hzn, stage9Part9Program, stage9Part9Model, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, capacity, ha1216, hf1216]

def stage9Part10Program : List Instr :=
  [
  .op .MUL,
   .op .ADD,
   .op (.Dup dA2),
   .push 2 1280,
   .op .MLOAD,
   .op .MUL,
   .op .ADD,
   .op (.Dup dA11)]
def stage9Part10Model (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 : W) (rest : List W) : State :=
  let v0 : W := w0 * w1
  let v1 : W := v0 + w2
  let v2 : W := MachineState.readWord (s.memory) 1280
  let v3 : W := v2 * w4
  let v4 : W := v3 + v1
  {s with pc := N 4847, memory := s.memory, stack := w13 :: v4 :: w3 :: w4 :: w5 :: w6 :: w7 :: w8 :: w9 :: w10 :: w11 :: w12 :: w13 :: w14 :: w15 :: w16 :: w17 :: w18 :: rest}

theorem stage9Part10_run (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions stage9Part10Program {s with pc := N 4837, memory := s.memory, stack := w0 :: w1 :: w2 :: w3 :: w4 :: w5 :: w6 :: w7 :: w8 :: w9 :: w10 :: w11 :: w12 :: w13 :: w14 :: w15 :: w16 :: w17 :: w18 :: rest} = some (stage9Part10Model s w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 63) : rest.length+j < 1024 := by omega
  have ha1280 : (1280 : W).toNat = 1280 := rfl
  have hf1280 := Monpro.activeWords_fix s 1280 32 (by decide) (by norm_num) hact
  simp [hz, hzn, stage9Part10Program, stage9Part10Model, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, capacity, ha1280, hf1280]

def stage9Part11Program : List Instr :=
  [
  .op (.Dup dA14),
   .op .MUL,
   .op .ADD,
   .op (.Swap sA0),
   .op (.Dup dA9),
   .push 2 1088,
   .op .MLOAD,
   .op (.Dup dA12)]
def stage9Part11Model (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 : W) (rest : List W) : State :=
  let v0 : W := w14 * w0
  let v1 : W := v0 + w1
  let v2 : W := MachineState.readWord (s.memory) 1088
  {s with pc := N 4857, memory := s.memory, stack := w11 :: v2 :: w10 :: w2 :: v1 :: w3 :: w4 :: w5 :: w6 :: w7 :: w8 :: w9 :: w10 :: w11 :: w12 :: w13 :: w14 :: w15 :: w16 :: w17 :: rest}

theorem stage9Part11_run (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions stage9Part11Program {s with pc := N 4847, memory := s.memory, stack := w0 :: w1 :: w2 :: w3 :: w4 :: w5 :: w6 :: w7 :: w8 :: w9 :: w10 :: w11 :: w12 :: w13 :: w14 :: w15 :: w16 :: w17 :: rest} = some (stage9Part11Model s w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 63) : rest.length+j < 1024 := by omega
  have ha1088 : (1088 : W).toNat = 1088 := rfl
  have hf1088 := Monpro.activeWords_fix s 1088 32 (by decide) (by norm_num) hact
  simp [hz, hzn, stage9Part11Program, stage9Part11Model, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, capacity, ha1088, hf1088]

def stage9Part12Program : List Instr :=
  [
  .op .MULMOD,
   .op .ADD,
   .op (.Dup dA9),
   .push 1 192,
   .op .MLOAD,
   .op (.Dup dA10),
   .op .MULMOD,
   .op .ADD]
def stage9Part12Model (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 : W) (rest : List W) : State :=
  let v0 : W := UInt256.mulMod w0 w1 w2
  let v1 : W := v0 + w3
  let v2 : W := MachineState.readWord (s.memory) 192
  let v3 : W := UInt256.mulMod w11 v2 w12
  let v4 : W := v3 + v1
  {s with pc := N 4866, memory := s.memory, stack := v4 :: w4 :: w5 :: w6 :: w7 :: w8 :: w9 :: w10 :: w11 :: w12 :: w13 :: w14 :: w15 :: w16 :: w17 :: w18 :: w19 :: rest}

theorem stage9Part12_run (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions stage9Part12Program {s with pc := N 4857, memory := s.memory, stack := w0 :: w1 :: w2 :: w3 :: w4 :: w5 :: w6 :: w7 :: w8 :: w9 :: w10 :: w11 :: w12 :: w13 :: w14 :: w15 :: w16 :: w17 :: w18 :: w19 :: rest} = some (stage9Part12Model s w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 63) : rest.length+j < 1024 := by omega
  have ha192 : (192 : W).toNat = 192 := rfl
  have hf192 := Monpro.activeWords_fix s 192 32 (by decide) (by norm_num) hact
  simp [hz, hzn, stage9Part12Program, stage9Part12Model, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, capacity, ha192, hf192]

def stage9Part13Program : List Instr :=
  [
  .op (.Dup dA9),
   .op (.Dup dA4),
   .push 0 0,
   .op .MLOAD,
   .op .MULMOD,
   .op .ADD,
   .op (.Dup dA9),
   .op (.Dup dA8)]
def stage9Part13Model (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 : W) (rest : List W) : State :=
  let v0 : W := MachineState.readWord (s.memory) 0
  let v1 : W := UInt256.mulMod v0 w3 w9
  let v2 : W := v1 + w0
  {s with pc := N 4874, memory := s.memory, stack := w7 :: w9 :: v2 :: w1 :: w2 :: w3 :: w4 :: w5 :: w6 :: w7 :: w8 :: w9 :: w10 :: w11 :: w12 :: w13 :: w14 :: w15 :: w16 :: rest}

theorem stage9Part13_run (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions stage9Part13Program {s with pc := N 4866, memory := s.memory, stack := w0 :: w1 :: w2 :: w3 :: w4 :: w5 :: w6 :: w7 :: w8 :: w9 :: w10 :: w11 :: w12 :: w13 :: w14 :: w15 :: w16 :: rest} = some (stage9Part13Model s w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 63) : rest.length+j < 1024 := by omega
  have ha0 : (0 : W).toNat = 0 := rfl
  have hf0 := Monpro.activeWords_fix s 0 32 (by decide) (by norm_num) hact
  simp [hz, hzn, stage9Part13Program, stage9Part13Model, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, capacity, ha0, hf0]

def stage9Part14Program : List Instr :=
  [
  .push 1 224,
   .op .MLOAD,
   .op .MULMOD,
   .op .ADD,
   .op (.Dup dA9),
   .op (.Dup dA5),
   .push 2 1216,
   .op .MLOAD]
def stage9Part14Model (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 : W) (rest : List W) : State :=
  let v0 : W := MachineState.readWord (s.memory) 224
  let v1 : W := UInt256.mulMod v0 w0 w1
  let v2 : W := v1 + w2
  let v3 : W := MachineState.readWord (s.memory) 1216
  {s with pc := N 4885, memory := s.memory, stack := v3 :: w6 :: w11 :: v2 :: w3 :: w4 :: w5 :: w6 :: w7 :: w8 :: w9 :: w10 :: w11 :: w12 :: w13 :: w14 :: w15 :: w16 :: w17 :: w18 :: rest}

theorem stage9Part14_run (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions stage9Part14Program {s with pc := N 4874, memory := s.memory, stack := w0 :: w1 :: w2 :: w3 :: w4 :: w5 :: w6 :: w7 :: w8 :: w9 :: w10 :: w11 :: w12 :: w13 :: w14 :: w15 :: w16 :: w17 :: w18 :: rest} = some (stage9Part14Model s w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 63) : rest.length+j < 1024 := by omega
  have ha224 : (224 : W).toNat = 224 := rfl
  have hf224 := Monpro.activeWords_fix s 224 32 (by decide) (by norm_num) hact
  have ha1216 : (1216 : W).toNat = 1216 := rfl
  have hf1216 := Monpro.activeWords_fix s 1216 32 (by decide) (by norm_num) hact
  simp [hz, hzn, stage9Part14Program, stage9Part14Model, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, capacity, ha224, hf224, ha1216, hf1216]

def stage9Part15Program : List Instr :=
  [
  .op .MULMOD,
   .op .ADD,
   .op (.Dup dA9),
   .op (.Dup dA15),
   .op (.Dup dA7),
   .op .MULMOD,
   .op .ADD,
   .op (.Dup dA9)]
def stage9Part15Model (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 : W) (rest : List W) : State :=
  let v0 : W := UInt256.mulMod w0 w1 w2
  let v1 : W := v0 + w3
  let v2 : W := UInt256.mulMod w8 w17 w12
  let v3 : W := v2 + v1
  {s with pc := N 4893, memory := s.memory, stack := w12 :: v3 :: w4 :: w5 :: w6 :: w7 :: w8 :: w9 :: w10 :: w11 :: w12 :: w13 :: w14 :: w15 :: w16 :: w17 :: w18 :: w19 :: rest}

theorem stage9Part15_run (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions stage9Part15Program {s with pc := N 4885, memory := s.memory, stack := w0 :: w1 :: w2 :: w3 :: w4 :: w5 :: w6 :: w7 :: w8 :: w9 :: w10 :: w11 :: w12 :: w13 :: w14 :: w15 :: w16 :: w17 :: w18 :: w19 :: rest} = some (stage9Part15Model s w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 63) : rest.length+j < 1024 := by omega
  simp [hz, hzn, stage9Part15Program, stage9Part15Model, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, capacity]

def stage9Part16Program : List Instr :=
  [
  .op (.Dup dA3),
   .push 2 1280,
   .op .MLOAD,
   .op .MULMOD,
   .op .ADD,
   .op (.Dup dA9),
   .op (.Dup dA12),
   .op (.Dup dA15)]
def stage9Part16Model (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 : W) (rest : List W) : State :=
  let v0 : W := MachineState.readWord (s.memory) 1280
  let v1 : W := UInt256.mulMod v0 w3 w0
  let v2 : W := v1 + w1
  {s with pc := N 4903, memory := s.memory, stack := w14 :: w12 :: w10 :: v2 :: w2 :: w3 :: w4 :: w5 :: w6 :: w7 :: w8 :: w9 :: w10 :: w11 :: w12 :: w13 :: w14 :: w15 :: w16 :: w17 :: rest}

theorem stage9Part16_run (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions stage9Part16Program {s with pc := N 4893, memory := s.memory, stack := w0 :: w1 :: w2 :: w3 :: w4 :: w5 :: w6 :: w7 :: w8 :: w9 :: w10 :: w11 :: w12 :: w13 :: w14 :: w15 :: w16 :: w17 :: rest} = some (stage9Part16Model s w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 63) : rest.length+j < 1024 := by omega
  have ha1280 : (1280 : W).toNat = 1280 := rfl
  have hf1280 := Monpro.activeWords_fix s 1280 32 (by decide) (by norm_num) hact
  simp [hz, hzn, stage9Part16Program, stage9Part16Model, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, capacity, ha1280, hf1280]

def stage9Part17Program : List Instr :=
  [
  .op .MULMOD,
   .op .ADD,
   .op (.Swap sA0),
   .op (.Dup dA15),
   .op .AND,
   .op (.Dup dA0),
   .push 2 768,
   .op .MSTORE]
def stage9Part17Model (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 : W) (rest : List W) : State :=
  let v0 : W := UInt256.mulMod w0 w1 w2
  let v1 : W := v0 + w3
  let v2 : W := UInt256.land w18 w4
  let v3 : ByteArray := MachineState.writeBytes (s.memory) (Data.Bytes.natToBytesPadded v2.toNat 32) 768
  {s with pc := N 4913, memory := v3, stack := v2 :: v1 :: w5 :: w6 :: w7 :: w8 :: w9 :: w10 :: w11 :: w12 :: w13 :: w14 :: w15 :: w16 :: w17 :: w18 :: w19 :: rest}

theorem stage9Part17_run (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions stage9Part17Program {s with pc := N 4903, memory := s.memory, stack := w0 :: w1 :: w2 :: w3 :: w4 :: w5 :: w6 :: w7 :: w8 :: w9 :: w10 :: w11 :: w12 :: w13 :: w14 :: w15 :: w16 :: w17 :: w18 :: w19 :: rest} = some (stage9Part17Model s w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 63) : rest.length+j < 1024 := by omega
  have ha768 : (768 : W).toNat = 768 := rfl
  have hf768 := Monpro.activeWords_fix s 768 32 (by decide) (by norm_num) hact
  simp [hz, hzn, stage9Part17Program, stage9Part17Model, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, capacity, ha768, hf768]

def stage9Part18Program : List Instr :=
  [
  .op (.Dup dA9),
   .op (.Swap sA1),
   .op .SUB,
   .op (.Dup dA1),
   .op .ADD,
   .push 2 2048,
   .op .MULMOD]
def stage9Part18Model (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 : W) (rest : List W) : State :=
  let v0 : W := w1 - w0
  let v1 : W := w9 + v0
  let v2 : W := UInt256.mulMod (N 2048) v1 w9
  {s with pc := N 4922, memory := s.memory, stack := v2 :: w2 :: w3 :: w4 :: w5 :: w6 :: w7 :: w8 :: w9 :: w10 :: w11 :: w12 :: w13 :: w14 :: w15 :: w16 :: rest}

theorem stage9Part18_run (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions stage9Part18Program {s with pc := N 4913, memory := s.memory, stack := w0 :: w1 :: w2 :: w3 :: w4 :: w5 :: w6 :: w7 :: w8 :: w9 :: w10 :: w11 :: w12 :: w13 :: w14 :: w15 :: w16 :: rest} = some (stage9Part18Model s w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 63) : rest.length+j < 1024 := by omega
  simp [hz, hzn, stage9Part18Program, stage9Part18Model, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, capacity]

def stage9Program : List Instr := (stage9Part0Program ++ (stage9Part1Program ++ (stage9Part2Program ++ (stage9Part3Program ++ (stage9Part4Program ++ (stage9Part5Program ++ (stage9Part6Program ++ (stage9Part7Program ++ (stage9Part8Program ++ (stage9Part9Program ++ (stage9Part10Program ++ (stage9Part11Program ++ (stage9Part12Program ++ (stage9Part13Program ++ (stage9Part14Program ++ (stage9Part15Program ++ (stage9Part16Program ++ (stage9Part17Program ++ stage9Part18Program))))))))))))))))))
def stage9Model (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 : W) (rest : List W) : State :=
  let v0 : W := MachineState.readWord (s.memory) 1248
  let v1 : W := w15 * w4
  let v2 : W := MachineState.readWord (s.memory) 160
  let v3 : W := w5 * v2
  let v4 : W := v3 + v1
  let v5 : W := MachineState.readWord (s.memory) 128
  let v6 : W := MachineState.readWord (s.memory) 32
  let v7 : W := v6 * v5
  let v8 : W := v7 + v4
  let v9 : W := MachineState.readWord (s.memory) 64
  let v10 : W := v9 * w11
  let v11 : W := v10 + v8
  let v12 : W := UInt256.mulMod w15 w4 w8
  let v13 : W := MachineState.readWord (s.memory) 160
  let v14 : W := UInt256.mulMod w5 v13 w8
  let v15 : W := v14 + v12
  let v16 : W := MachineState.readWord (s.memory) 128
  let v17 : W := MachineState.readWord (s.memory) 32
  let v18 : W := UInt256.mulMod v17 v16 w8
  let v19 : W := v18 + v15
  let v20 : W := MachineState.readWord (s.memory) 64
  let v21 : W := UInt256.mulMod v20 w11 w8
  let v22 : W := v21 + v19
  let v23 : W := w0 + v22
  let v24 : W := w0 + v11
  let v25 : W := MachineState.readWord (s.memory) 1088
  let v26 : W := w9 * v25
  let v27 : W := v26 + v24
  let v28 : W := MachineState.readWord (s.memory) 192
  let v29 : W := w7 * v28
  let v30 : W := v29 + v27
  let v31 : W := MachineState.readWord (s.memory) 0
  let v32 : W := v31 * w2
  let v33 : W := v32 + v30
  let v34 : W := MachineState.readWord (s.memory) 224
  let v35 : W := v34 * w6
  let v36 : W := v35 + v33
  let v37 : W := MachineState.readWord (s.memory) 1216
  let v38 : W := v37 * w3
  let v39 : W := v38 + v36
  let v40 : W := v0 * w13
  let v41 : W := v40 + v39
  let v42 : W := MachineState.readWord (s.memory) 1280
  let v43 : W := v42 * w1
  let v44 : W := v43 + v41
  let v45 : W := w12 * w10
  let v46 : W := v45 + v44
  let v47 : W := MachineState.readWord (s.memory) 1088
  let v48 : W := UInt256.mulMod w9 v47 w8
  let v49 : W := v48 + v23
  let v50 : W := MachineState.readWord (s.memory) 192
  let v51 : W := UInt256.mulMod w7 v50 w8
  let v52 : W := v51 + v49
  let v53 : W := MachineState.readWord (s.memory) 0
  let v54 : W := UInt256.mulMod v53 w2 w8
  let v55 : W := v54 + v52
  let v56 : W := MachineState.readWord (s.memory) 224
  let v57 : W := UInt256.mulMod v56 w6 w8
  let v58 : W := v57 + v55
  let v59 : W := MachineState.readWord (s.memory) 1216
  let v60 : W := UInt256.mulMod v59 w3 w8
  let v61 : W := v60 + v58
  let v62 : W := UInt256.mulMod v0 w13 w8
  let v63 : W := v62 + v61
  let v64 : W := MachineState.readWord (s.memory) 1280
  let v65 : W := UInt256.mulMod v64 w1 w8
  let v66 : W := v65 + v63
  let v67 : W := UInt256.mulMod w12 w10 w8
  let v68 : W := v67 + v66
  let v69 : W := UInt256.land w14 v46
  let v70 : ByteArray := MachineState.writeBytes (s.memory) (Data.Bytes.natToBytesPadded v69.toNat 32) 768
  let v71 : W := v68 - v69
  let v72 : W := w8 + v71
  let v73 : W := UInt256.mulMod (N 2048) v72 w8
  {s with pc := N 4922, memory := v70, stack := v73 :: w1 :: w2 :: w3 :: v0 :: w5 :: w6 :: w7 :: w8 :: w9 :: w10 :: w11 :: w12 :: w13 :: w14 :: w15 :: rest}

theorem stage9_run (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions stage9Program {s with pc := N 4745, memory := s.memory, stack := w0 :: w1 :: w2 :: w3 :: w4 :: w5 :: w6 :: w7 :: w8 :: w9 :: w10 :: w11 :: w12 :: w13 :: w14 :: w15 :: rest} = some (stage9Model s w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 rest) := by
  let v0 : W := MachineState.readWord (s.memory) 1248
  let v1 : W := w15 * w4
  let v2 : W := MachineState.readWord (s.memory) 160
  let v3 : W := w5 * v2
  let v4 : W := v3 + v1
  let v5 : W := MachineState.readWord (s.memory) 128
  let v6 : W := MachineState.readWord (s.memory) 32
  let v7 : W := v6 * v5
  let v8 : W := v7 + v4
  let v9 : W := MachineState.readWord (s.memory) 64
  let v10 : W := v9 * w11
  let v11 : W := v10 + v8
  let v12 : W := UInt256.mulMod w15 w4 w8
  let v13 : W := MachineState.readWord (s.memory) 160
  let v14 : W := UInt256.mulMod w5 v13 w8
  let v15 : W := v14 + v12
  let v16 : W := MachineState.readWord (s.memory) 128
  let v17 : W := MachineState.readWord (s.memory) 32
  let v18 : W := UInt256.mulMod v17 v16 w8
  let v19 : W := v18 + v15
  let v20 : W := MachineState.readWord (s.memory) 64
  let v21 : W := UInt256.mulMod v20 w11 w8
  let v22 : W := v21 + v19
  let v23 : W := w0 + v22
  let v24 : W := w0 + v11
  let v25 : W := MachineState.readWord (s.memory) 1088
  let v26 : W := w9 * v25
  let v27 : W := v26 + v24
  let v28 : W := MachineState.readWord (s.memory) 192
  let v29 : W := w7 * v28
  let v30 : W := v29 + v27
  let v31 : W := MachineState.readWord (s.memory) 0
  let v32 : W := v31 * w2
  let v33 : W := v32 + v30
  let v34 : W := MachineState.readWord (s.memory) 224
  let v35 : W := v34 * w6
  let v36 : W := v35 + v33
  let v37 : W := MachineState.readWord (s.memory) 1216
  let v38 : W := v37 * w3
  let v39 : W := v38 + v36
  let v40 : W := v0 * w13
  let v41 : W := v40 + v39
  let v42 : W := MachineState.readWord (s.memory) 1280
  let v43 : W := v42 * w1
  let v44 : W := v43 + v41
  let v45 : W := w12 * w10
  let v46 : W := v45 + v44
  let v47 : W := MachineState.readWord (s.memory) 1088
  let v48 : W := UInt256.mulMod w9 v47 w8
  let v49 : W := v48 + v23
  let v50 : W := MachineState.readWord (s.memory) 192
  let v51 : W := UInt256.mulMod w7 v50 w8
  let v52 : W := v51 + v49
  let v53 : W := MachineState.readWord (s.memory) 0
  let v54 : W := UInt256.mulMod v53 w2 w8
  let v55 : W := v54 + v52
  let v56 : W := MachineState.readWord (s.memory) 224
  let v57 : W := UInt256.mulMod v56 w6 w8
  let v58 : W := v57 + v55
  let v59 : W := MachineState.readWord (s.memory) 1216
  let v60 : W := UInt256.mulMod v59 w3 w8
  let v61 : W := v60 + v58
  let v62 : W := UInt256.mulMod v0 w13 w8
  let v63 : W := v62 + v61
  let v64 : W := MachineState.readWord (s.memory) 1280
  let v65 : W := UInt256.mulMod v64 w1 w8
  let v66 : W := v65 + v63
  let v67 : W := UInt256.mulMod w12 w10 w8
  let v68 : W := v67 + v66
  let v69 : W := UInt256.land w14 v46
  let v70 : ByteArray := MachineState.writeBytes (s.memory) (Data.Bytes.natToBytesPadded v69.toNat 32) 768
  let v71 : W := v68 - v69
  let v72 : W := w8 + v71
  let v73 : W := UInt256.mulMod (N 2048) v72 w8
  have h0 : runInstructions stage9Part0Program {s with pc := N 4745, memory := s.memory, stack := w0 :: w1 :: w2 :: w3 :: w4 :: w5 :: w6 :: w7 :: w8 :: w9 :: w10 :: w11 :: w12 :: w13 :: w14 :: w15 :: rest} = some {s with pc := N 4755, memory := s.memory, stack := v1 :: w4 :: w8 :: w15 :: w0 :: w1 :: w2 :: w3 :: v0 :: w5 :: w6 :: w7 :: w8 :: w9 :: w10 :: w11 :: w12 :: w13 :: w14 :: w15 :: rest} := by
    simpa only [stage9Part0Model, v0, v1] using stage9Part0_run ({s with memory := s.memory}) w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 rest hcap hact
  have h1 : runInstructions stage9Part1Program {s with pc := N 4755, memory := s.memory, stack := v1 :: w4 :: w8 :: w15 :: w0 :: w1 :: w2 :: w3 :: v0 :: w5 :: w6 :: w7 :: w8 :: w9 :: w10 :: w11 :: w12 :: w13 :: w14 :: w15 :: rest} = some {s with pc := N 4764, memory := s.memory, stack := v5 :: v4 :: w4 :: w8 :: w15 :: w0 :: w1 :: w2 :: w3 :: v0 :: w5 :: w6 :: w7 :: w8 :: w9 :: w10 :: w11 :: w12 :: w13 :: w14 :: w15 :: rest} := by
    simpa only [stage9Part1Model, v2, v3, v4, v5] using stage9Part1_run ({s with memory := s.memory}) v1 w4 w8 w15 w0 w1 w2 w3 v0 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 rest hcap hact
  have h2 : runInstructions stage9Part2Program {s with pc := N 4764, memory := s.memory, stack := v5 :: v4 :: w4 :: w8 :: w15 :: w0 :: w1 :: w2 :: w3 :: v0 :: w5 :: w6 :: w7 :: w8 :: w9 :: w10 :: w11 :: w12 :: w13 :: w14 :: w15 :: rest} = some {s with pc := N 4773, memory := s.memory, stack := v9 :: w11 :: v8 :: w4 :: w8 :: w15 :: w0 :: w1 :: w2 :: w3 :: v0 :: w5 :: w6 :: w7 :: w8 :: w9 :: w10 :: w11 :: w12 :: w13 :: w14 :: w15 :: rest} := by
    simpa only [stage9Part2Model, v6, v7, v8, v9] using stage9Part2_run ({s with memory := s.memory}) v5 v4 w4 w8 w15 w0 w1 w2 w3 v0 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 rest hcap hact
  have h3 : runInstructions stage9Part3Program {s with pc := N 4773, memory := s.memory, stack := v9 :: w11 :: v8 :: w4 :: w8 :: w15 :: w0 :: w1 :: w2 :: w3 :: v0 :: w5 :: w6 :: w7 :: w8 :: w9 :: w10 :: w11 :: w12 :: w13 :: w14 :: w15 :: rest} = some {s with pc := N 4782, memory := s.memory, stack := w5 :: v13 :: w8 :: v12 :: v11 :: w0 :: w1 :: w2 :: w3 :: v0 :: w5 :: w6 :: w7 :: w8 :: w9 :: w10 :: w11 :: w12 :: w13 :: w14 :: w15 :: rest} := by
    simpa only [stage9Part3Model, v10, v11, v12, v13] using stage9Part3_run ({s with memory := s.memory}) v9 w11 v8 w4 w8 w15 w0 w1 w2 w3 v0 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 rest hcap hact
  have h4 : runInstructions stage9Part4Program {s with pc := N 4782, memory := s.memory, stack := w5 :: v13 :: w8 :: v12 :: v11 :: w0 :: w1 :: w2 :: w3 :: v0 :: w5 :: w6 :: w7 :: w8 :: w9 :: w10 :: w11 :: w12 :: w13 :: w14 :: w15 :: rest} = some {s with pc := N 4792, memory := s.memory, stack := v18 :: v15 :: v11 :: w0 :: w1 :: w2 :: w3 :: v0 :: w5 :: w6 :: w7 :: w8 :: w9 :: w10 :: w11 :: w12 :: w13 :: w14 :: w15 :: rest} := by
    simpa only [stage9Part4Model, v14, v15, v16, v17, v18] using stage9Part4_run ({s with memory := s.memory}) w5 v13 w8 v12 v11 w0 w1 w2 w3 v0 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 rest hcap hact
  have h5 : runInstructions stage9Part5Program {s with pc := N 4792, memory := s.memory, stack := v18 :: v15 :: v11 :: w0 :: w1 :: w2 :: w3 :: v0 :: w5 :: w6 :: w7 :: w8 :: w9 :: w10 :: w11 :: w12 :: w13 :: w14 :: w15 :: rest} = some {s with pc := N 4800, memory := s.memory, stack := v22 :: v11 :: w0 :: w1 :: w2 :: w3 :: v0 :: w5 :: w6 :: w7 :: w8 :: w9 :: w10 :: w11 :: w12 :: w13 :: w14 :: w15 :: rest} := by
    simpa only [stage9Part5Model, v19, v20, v21, v22] using stage9Part5_run ({s with memory := s.memory}) v18 v15 v11 w0 w1 w2 w3 v0 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 rest hcap hact
  have h6 : runInstructions stage9Part6Program {s with pc := N 4800, memory := s.memory, stack := v22 :: v11 :: w0 :: w1 :: w2 :: w3 :: v0 :: w5 :: w6 :: w7 :: w8 :: w9 :: w10 :: w11 :: w12 :: w13 :: w14 :: w15 :: rest} = some {s with pc := N 4810, memory := s.memory, stack := v26 :: v24 :: v23 :: w1 :: w2 :: w3 :: v0 :: w5 :: w6 :: w7 :: w8 :: w9 :: w10 :: w11 :: w12 :: w13 :: w14 :: w15 :: rest} := by
    simpa only [stage9Part6Model, v23, v24, v25, v26] using stage9Part6_run ({s with memory := s.memory}) v22 v11 w0 w1 w2 w3 v0 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 rest hcap hact
  have h7 : runInstructions stage9Part7Program {s with pc := N 4810, memory := s.memory, stack := v26 :: v24 :: v23 :: w1 :: w2 :: w3 :: v0 :: w5 :: w6 :: w7 :: w8 :: w9 :: w10 :: w11 :: w12 :: w13 :: w14 :: w15 :: rest} = some {s with pc := N 4818, memory := s.memory, stack := w2 :: v30 :: v23 :: w1 :: w2 :: w3 :: v0 :: w5 :: w6 :: w7 :: w8 :: w9 :: w10 :: w11 :: w12 :: w13 :: w14 :: w15 :: rest} := by
    simpa only [stage9Part7Model, v27, v28, v29, v30] using stage9Part7_run ({s with memory := s.memory}) v26 v24 v23 w1 w2 w3 v0 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 rest hcap hact
  have h8 : runInstructions stage9Part8Program {s with pc := N 4818, memory := s.memory, stack := w2 :: v30 :: v23 :: w1 :: w2 :: w3 :: v0 :: w5 :: w6 :: w7 :: w8 :: w9 :: w10 :: w11 :: w12 :: w13 :: w14 :: w15 :: rest} = some {s with pc := N 4827, memory := s.memory, stack := v35 :: v33 :: v23 :: w1 :: w2 :: w3 :: v0 :: w5 :: w6 :: w7 :: w8 :: w9 :: w10 :: w11 :: w12 :: w13 :: w14 :: w15 :: rest} := by
    simpa only [stage9Part8Model, v31, v32, v33, v34, v35] using stage9Part8_run ({s with memory := s.memory}) w2 v30 v23 w1 w2 w3 v0 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 rest hcap hact
  have h9 : runInstructions stage9Part9Program {s with pc := N 4827, memory := s.memory, stack := v35 :: v33 :: v23 :: w1 :: w2 :: w3 :: v0 :: w5 :: w6 :: w7 :: w8 :: w9 :: w10 :: w11 :: w12 :: w13 :: w14 :: w15 :: rest} = some {s with pc := N 4837, memory := s.memory, stack := v0 :: w13 :: v39 :: v23 :: w1 :: w2 :: w3 :: v0 :: w5 :: w6 :: w7 :: w8 :: w9 :: w10 :: w11 :: w12 :: w13 :: w14 :: w15 :: rest} := by
    simpa only [stage9Part9Model, v36, v37, v38, v39] using stage9Part9_run ({s with memory := s.memory}) v35 v33 v23 w1 w2 w3 v0 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 rest hcap hact
  have h10 : runInstructions stage9Part10Program {s with pc := N 4837, memory := s.memory, stack := v0 :: w13 :: v39 :: v23 :: w1 :: w2 :: w3 :: v0 :: w5 :: w6 :: w7 :: w8 :: w9 :: w10 :: w11 :: w12 :: w13 :: w14 :: w15 :: rest} = some {s with pc := N 4847, memory := s.memory, stack := w10 :: v44 :: v23 :: w1 :: w2 :: w3 :: v0 :: w5 :: w6 :: w7 :: w8 :: w9 :: w10 :: w11 :: w12 :: w13 :: w14 :: w15 :: rest} := by
    simpa only [stage9Part10Model, v40, v41, v42, v43, v44] using stage9Part10_run ({s with memory := s.memory}) v0 w13 v39 v23 w1 w2 w3 v0 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 rest hcap hact
  have h11 : runInstructions stage9Part11Program {s with pc := N 4847, memory := s.memory, stack := w10 :: v44 :: v23 :: w1 :: w2 :: w3 :: v0 :: w5 :: w6 :: w7 :: w8 :: w9 :: w10 :: w11 :: w12 :: w13 :: w14 :: w15 :: rest} = some {s with pc := N 4857, memory := s.memory, stack := w9 :: v47 :: w8 :: v23 :: v46 :: w1 :: w2 :: w3 :: v0 :: w5 :: w6 :: w7 :: w8 :: w9 :: w10 :: w11 :: w12 :: w13 :: w14 :: w15 :: rest} := by
    simpa only [stage9Part11Model, v45, v46, v47] using stage9Part11_run ({s with memory := s.memory}) w10 v44 v23 w1 w2 w3 v0 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 rest hcap hact
  have h12 : runInstructions stage9Part12Program {s with pc := N 4857, memory := s.memory, stack := w9 :: v47 :: w8 :: v23 :: v46 :: w1 :: w2 :: w3 :: v0 :: w5 :: w6 :: w7 :: w8 :: w9 :: w10 :: w11 :: w12 :: w13 :: w14 :: w15 :: rest} = some {s with pc := N 4866, memory := s.memory, stack := v52 :: v46 :: w1 :: w2 :: w3 :: v0 :: w5 :: w6 :: w7 :: w8 :: w9 :: w10 :: w11 :: w12 :: w13 :: w14 :: w15 :: rest} := by
    simpa only [stage9Part12Model, v48, v49, v50, v51, v52] using stage9Part12_run ({s with memory := s.memory}) w9 v47 w8 v23 v46 w1 w2 w3 v0 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 rest hcap hact
  have h13 : runInstructions stage9Part13Program {s with pc := N 4866, memory := s.memory, stack := v52 :: v46 :: w1 :: w2 :: w3 :: v0 :: w5 :: w6 :: w7 :: w8 :: w9 :: w10 :: w11 :: w12 :: w13 :: w14 :: w15 :: rest} = some {s with pc := N 4874, memory := s.memory, stack := w6 :: w8 :: v55 :: v46 :: w1 :: w2 :: w3 :: v0 :: w5 :: w6 :: w7 :: w8 :: w9 :: w10 :: w11 :: w12 :: w13 :: w14 :: w15 :: rest} := by
    simpa only [stage9Part13Model, v53, v54, v55] using stage9Part13_run ({s with memory := s.memory}) v52 v46 w1 w2 w3 v0 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 rest hcap hact
  have h14 : runInstructions stage9Part14Program {s with pc := N 4874, memory := s.memory, stack := w6 :: w8 :: v55 :: v46 :: w1 :: w2 :: w3 :: v0 :: w5 :: w6 :: w7 :: w8 :: w9 :: w10 :: w11 :: w12 :: w13 :: w14 :: w15 :: rest} = some {s with pc := N 4885, memory := s.memory, stack := v59 :: w3 :: w8 :: v58 :: v46 :: w1 :: w2 :: w3 :: v0 :: w5 :: w6 :: w7 :: w8 :: w9 :: w10 :: w11 :: w12 :: w13 :: w14 :: w15 :: rest} := by
    simpa only [stage9Part14Model, v56, v57, v58, v59] using stage9Part14_run ({s with memory := s.memory}) w6 w8 v55 v46 w1 w2 w3 v0 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 rest hcap hact
  have h15 : runInstructions stage9Part15Program {s with pc := N 4885, memory := s.memory, stack := v59 :: w3 :: w8 :: v58 :: v46 :: w1 :: w2 :: w3 :: v0 :: w5 :: w6 :: w7 :: w8 :: w9 :: w10 :: w11 :: w12 :: w13 :: w14 :: w15 :: rest} = some {s with pc := N 4893, memory := s.memory, stack := w8 :: v63 :: v46 :: w1 :: w2 :: w3 :: v0 :: w5 :: w6 :: w7 :: w8 :: w9 :: w10 :: w11 :: w12 :: w13 :: w14 :: w15 :: rest} := by
    simpa only [stage9Part15Model, v60, v61, v62, v63] using stage9Part15_run ({s with memory := s.memory}) v59 w3 w8 v58 v46 w1 w2 w3 v0 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 rest hcap hact
  have h16 : runInstructions stage9Part16Program {s with pc := N 4893, memory := s.memory, stack := w8 :: v63 :: v46 :: w1 :: w2 :: w3 :: v0 :: w5 :: w6 :: w7 :: w8 :: w9 :: w10 :: w11 :: w12 :: w13 :: w14 :: w15 :: rest} = some {s with pc := N 4903, memory := s.memory, stack := w12 :: w10 :: w8 :: v66 :: v46 :: w1 :: w2 :: w3 :: v0 :: w5 :: w6 :: w7 :: w8 :: w9 :: w10 :: w11 :: w12 :: w13 :: w14 :: w15 :: rest} := by
    simpa only [stage9Part16Model, v64, v65, v66] using stage9Part16_run ({s with memory := s.memory}) w8 v63 v46 w1 w2 w3 v0 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 rest hcap hact
  have h17 : runInstructions stage9Part17Program {s with pc := N 4903, memory := s.memory, stack := w12 :: w10 :: w8 :: v66 :: v46 :: w1 :: w2 :: w3 :: v0 :: w5 :: w6 :: w7 :: w8 :: w9 :: w10 :: w11 :: w12 :: w13 :: w14 :: w15 :: rest} = some {s with pc := N 4913, memory := v70, stack := v69 :: v68 :: w1 :: w2 :: w3 :: v0 :: w5 :: w6 :: w7 :: w8 :: w9 :: w10 :: w11 :: w12 :: w13 :: w14 :: w15 :: rest} := by
    simpa only [stage9Part17Model, v67, v68, v69, v70] using stage9Part17_run ({s with memory := s.memory}) w12 w10 w8 v66 v46 w1 w2 w3 v0 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 rest hcap hact
  have h18 : runInstructions stage9Part18Program {s with pc := N 4913, memory := v70, stack := v69 :: v68 :: w1 :: w2 :: w3 :: v0 :: w5 :: w6 :: w7 :: w8 :: w9 :: w10 :: w11 :: w12 :: w13 :: w14 :: w15 :: rest} = some {s with pc := N 4922, memory := v70, stack := v73 :: w1 :: w2 :: w3 :: v0 :: w5 :: w6 :: w7 :: w8 :: w9 :: w10 :: w11 :: w12 :: w13 :: w14 :: w15 :: rest} := by
    simpa only [stage9Part18Model, v71, v72, v73] using stage9Part18_run ({s with memory := v70}) v69 v68 w1 w2 w3 v0 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 rest hcap hact
  exact (runInstructions_append_some _ _ _ _ _ h0 (runInstructions_append_some _ _ _ _ _ h1 (runInstructions_append_some _ _ _ _ _ h2 (runInstructions_append_some _ _ _ _ _ h3 (runInstructions_append_some _ _ _ _ _ h4 (runInstructions_append_some _ _ _ _ _ h5 (runInstructions_append_some _ _ _ _ _ h6 (runInstructions_append_some _ _ _ _ _ h7 (runInstructions_append_some _ _ _ _ _ h8 (runInstructions_append_some _ _ _ _ _ h9 (runInstructions_append_some _ _ _ _ _ h10 (runInstructions_append_some _ _ _ _ _ h11 (runInstructions_append_some _ _ _ _ _ h12 (runInstructions_append_some _ _ _ _ _ h13 (runInstructions_append_some _ _ _ _ _ h14 (runInstructions_append_some _ _ _ _ _ h15 (runInstructions_append_some _ _ _ _ _ h16 (runInstructions_append_some _ _ _ _ _ h17 h18))))))))))))))))))

end R9InvConsumeExec
