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

def stage3Part0Program : List Instr :=
  [
  .push 1 32,
   .op .MLOAD,
   .op (.Dup dA9),
   .push 2 768,
   .op .MLOAD,
   .op (.Dup dA0),
   .op (.Dup dA3),
   .op .MUL]
def stage3Part0Model (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 : W) (rest : List W) : State :=
  let v0 : W := MachineState.readWord (s.memory) 32
  let v1 : W := MachineState.readWord (s.memory) 768
  let v2 : W := v0 * v1
  {s with pc := N 3741, memory := s.memory, stack := v2 :: v1 :: w8 :: v0 :: w0 :: w1 :: w2 :: w3 :: w4 :: w5 :: w6 :: w7 :: w8 :: w9 :: w10 :: w11 :: w12 :: w13 :: w14 :: w15 :: rest}

theorem stage3Part0_run (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions stage3Part0Program {s with pc := N 3730, memory := s.memory, stack := w0 :: w1 :: w2 :: w3 :: w4 :: w5 :: w6 :: w7 :: w8 :: w9 :: w10 :: w11 :: w12 :: w13 :: w14 :: w15 :: rest} = some (stage3Part0Model s w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 63) : rest.length+j < 1024 := by omega
  have ha32 : (32 : W).toNat = 32 := rfl
  have hf32 := Monpro.activeWords_fix s 32 32 (by decide) (by norm_num) hact
  have ha768 : (768 : W).toNat = 768 := rfl
  have hf768 := Monpro.activeWords_fix s 768 32 (by decide) (by norm_num) hact
  simp [hz, hzn, stage3Part0Program, stage3Part0Model, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, capacity, ha32, hf32, ha768, hf768]

def stage3Part1Program : List Instr :=
  [
  .op (.Dup dA9),
   .op (.Dup dA9),
   .op .MUL,
   .op .ADD,
   .op (.Swap sA2),
   .op .MULMOD,
   .op (.Dup dA10),
   .op (.Dup dA8)]
def stage3Part1Model (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 : W) (rest : List W) : State :=
  let v0 : W := w8 * w9
  let v1 : W := v0 + w0
  let v2 : W := UInt256.mulMod w3 w1 w2
  {s with pc := N 3749, memory := s.memory, stack := w9 :: w12 :: v2 :: v1 :: w4 :: w5 :: w6 :: w7 :: w8 :: w9 :: w10 :: w11 :: w12 :: w13 :: w14 :: w15 :: w16 :: w17 :: w18 :: w19 :: rest}

theorem stage3Part1_run (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions stage3Part1Program {s with pc := N 3741, memory := s.memory, stack := w0 :: w1 :: w2 :: w3 :: w4 :: w5 :: w6 :: w7 :: w8 :: w9 :: w10 :: w11 :: w12 :: w13 :: w14 :: w15 :: w16 :: w17 :: w18 :: w19 :: rest} = some (stage3Part1Model s w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 63) : rest.length+j < 1024 := by omega
  simp [hz, hzn, stage3Part1Program, stage3Part1Model, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, capacity]

def stage3Part2Program : List Instr :=
  [
  .op (.Dup dA8),
   .op .MULMOD,
   .op .ADD,
   .op (.Dup dA2),
   .op .ADD,
   .op (.Swap sA1),
   .op .ADD,
   .op (.Dup dA14)]
def stage3Part2Model (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 : W) (rest : List W) : State :=
  let v0 : W := UInt256.mulMod w8 w0 w1
  let v1 : W := v0 + w2
  let v2 : W := w4 + v1
  let v3 : W := w4 + w3
  {s with pc := N 3757, memory := s.memory, stack := w17 :: v3 :: v2 :: w5 :: w6 :: w7 :: w8 :: w9 :: w10 :: w11 :: w12 :: w13 :: w14 :: w15 :: w16 :: w17 :: w18 :: w19 :: rest}

theorem stage3Part2_run (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions stage3Part2Program {s with pc := N 3749, memory := s.memory, stack := w0 :: w1 :: w2 :: w3 :: w4 :: w5 :: w6 :: w7 :: w8 :: w9 :: w10 :: w11 :: w12 :: w13 :: w14 :: w15 :: w16 :: w17 :: w18 :: w19 :: rest} = some (stage3Part2Model s w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 63) : rest.length+j < 1024 := by omega
  simp [hz, hzn, stage3Part2Program, stage3Part2Model, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, capacity]

def stage3Part3Program : List Instr :=
  [
  .op (.Dup dA11),
   .op .MUL,
   .op .ADD,
   .op (.Dup dA2),
   .op (.Dup dA9),
   .op .MUL,
   .op .ADD,
   .op (.Dup dA11)]
def stage3Part3Model (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 : W) (rest : List W) : State :=
  let v0 : W := w11 * w0
  let v1 : W := v0 + w1
  let v2 : W := w9 * w3
  let v3 : W := v2 + v1
  {s with pc := N 3765, memory := s.memory, stack := w12 :: v3 :: w2 :: w3 :: w4 :: w5 :: w6 :: w7 :: w8 :: w9 :: w10 :: w11 :: w12 :: w13 :: w14 :: w15 :: w16 :: w17 :: rest}

theorem stage3Part3_run (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions stage3Part3Program {s with pc := N 3757, memory := s.memory, stack := w0 :: w1 :: w2 :: w3 :: w4 :: w5 :: w6 :: w7 :: w8 :: w9 :: w10 :: w11 :: w12 :: w13 :: w14 :: w15 :: w16 :: w17 :: rest} = some (stage3Part3Model s w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 63) : rest.length+j < 1024 := by omega
  simp [hz, hzn, stage3Part3Program, stage3Part3Model, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, capacity]

def stage3Part4Program : List Instr :=
  [
  .push 1 192,
   .op .MLOAD,
   .op .MUL,
   .op .ADD,
   .op (.Swap sA0),
   .op (.Dup dA9),
   .op (.Dup dA15),
   .op (.Dup dA12)]
def stage3Part4Model (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 : W) (rest : List W) : State :=
  let v0 : W := MachineState.readWord (s.memory) 192
  let v1 : W := v0 * w0
  let v2 : W := v1 + w1
  {s with pc := N 3774, memory := s.memory, stack := w11 :: w15 :: w10 :: w2 :: v2 :: w3 :: w4 :: w5 :: w6 :: w7 :: w8 :: w9 :: w10 :: w11 :: w12 :: w13 :: w14 :: w15 :: w16 :: w17 :: rest}

theorem stage3Part4_run (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions stage3Part4Program {s with pc := N 3765, memory := s.memory, stack := w0 :: w1 :: w2 :: w3 :: w4 :: w5 :: w6 :: w7 :: w8 :: w9 :: w10 :: w11 :: w12 :: w13 :: w14 :: w15 :: w16 :: w17 :: rest} = some (stage3Part4Model s w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 63) : rest.length+j < 1024 := by omega
  have ha192 : (192 : W).toNat = 192 := rfl
  have hf192 := Monpro.activeWords_fix s 192 32 (by decide) (by norm_num) hact
  simp [hz, hzn, stage3Part4Program, stage3Part4Model, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, capacity, ha192, hf192]

def stage3Part5Program : List Instr :=
  [
  .op .MULMOD,
   .op .ADD,
   .op (.Dup dA9),
   .op (.Dup dA3),
   .op (.Dup dA10),
   .op .MULMOD,
   .op .ADD,
   .op (.Dup dA9)]
def stage3Part5Model (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 : W) (rest : List W) : State :=
  let v0 : W := UInt256.mulMod w0 w1 w2
  let v1 : W := v0 + w3
  let v2 : W := UInt256.mulMod w11 w5 w12
  let v3 : W := v2 + v1
  {s with pc := N 3782, memory := s.memory, stack := w12 :: v3 :: w4 :: w5 :: w6 :: w7 :: w8 :: w9 :: w10 :: w11 :: w12 :: w13 :: w14 :: w15 :: w16 :: w17 :: w18 :: w19 :: rest}

theorem stage3Part5_run (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions stage3Part5Program {s with pc := N 3774, memory := s.memory, stack := w0 :: w1 :: w2 :: w3 :: w4 :: w5 :: w6 :: w7 :: w8 :: w9 :: w10 :: w11 :: w12 :: w13 :: w14 :: w15 :: w16 :: w17 :: w18 :: w19 :: rest} = some (stage3Part5Model s w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 63) : rest.length+j < 1024 := by omega
  simp [hz, hzn, stage3Part5Program, stage3Part5Model, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, capacity]

def stage3Part6Program : List Instr :=
  [
  .op (.Dup dA12),
   .push 1 192,
   .op .MLOAD,
   .op .MULMOD,
   .op .ADD,
   .op (.Dup dA9),
   .op (.Dup dA14),
   .push 2 2720,
   .op .MLOAD]
def stage3Part6Model (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 : W) (rest : List W) : State :=
  let v0 : W := MachineState.readWord (s.memory) 192
  let v1 : W := UInt256.mulMod v0 w12 w0
  let v2 : W := v1 + w1
  let v3 : W := MachineState.readWord (s.memory) 2720
  {s with pc := N 3794, memory := s.memory, stack := v3 :: w14 :: w10 :: v2 :: w2 :: w3 :: w4 :: w5 :: w6 :: w7 :: w8 :: w9 :: w10 :: w11 :: w12 :: w13 :: w14 :: w15 :: w16 :: w17 :: rest}

theorem stage3Part6_run (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions stage3Part6Program {s with pc := N 3782, memory := s.memory, stack := w0 :: w1 :: w2 :: w3 :: w4 :: w5 :: w6 :: w7 :: w8 :: w9 :: w10 :: w11 :: w12 :: w13 :: w14 :: w15 :: w16 :: w17 :: rest} = some (stage3Part6Model s w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 63) : rest.length+j < 1024 := by omega
  have ha192 : (192 : W).toNat = 192 := rfl
  have hf192 := Monpro.activeWords_fix s 192 32 (by decide) (by norm_num) hact
  have ha2720 : (2720 : W).toNat = 2720 := rfl
  have hf2720 := Monpro.activeWords_fix s 2720 32 (by decide) (by norm_num) hact
  simp [hz, hzn, stage3Part6Program, stage3Part6Model, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, capacity, ha192, hf192, ha2720, hf2720]

def stage3Part7Program : List Instr :=
  [
  .op (.Dup dA2),
   .op (.Swap sA4),
   .op .MUL,
   .push 30 1766847064778384329583297500742918515827483896875618958121606201292619775,
   .op .AND,
   .op (.Dup dA0),
   .push 0 0,
   .op .MSTORE]
def stage3Part7Model (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 : W) (rest : List W) : State :=
  let v0 : W := w4 * w0
  let v1 : W := UInt256.land (N 1766847064778384329583297500742918515827483896875618958121606201292619775) v0
  let v2 : ByteArray := MachineState.writeBytes (s.memory) (Data.Bytes.natToBytesPadded v1.toNat 32) 0
  {s with pc := N 3832, memory := v2, stack := v1 :: w1 :: w2 :: w3 :: w2 :: w5 :: w6 :: w7 :: w8 :: w9 :: w10 :: w11 :: w12 :: w13 :: w14 :: w15 :: w16 :: w17 :: w18 :: w19 :: rest}

theorem stage3Part7_run (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions stage3Part7Program {s with pc := N 3794, memory := s.memory, stack := w0 :: w1 :: w2 :: w3 :: w4 :: w5 :: w6 :: w7 :: w8 :: w9 :: w10 :: w11 :: w12 :: w13 :: w14 :: w15 :: w16 :: w17 :: w18 :: w19 :: rest} = some (stage3Part7Model s w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 63) : rest.length+j < 1024 := by omega
  have ha0 : (0 : W).toNat = 0 := rfl
  have hf0 := Monpro.activeWords_fix s 0 32 (by decide) (by norm_num) hact
  simp [hz, hzn, stage3Part7Program, stage3Part7Model, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, capacity, ha0, hf0]

def stage3Part8Program : List Instr :=
  [
  .op .MULMOD,
   .op .ADD,
   .push 2 2048,
   .op .MULMOD]
def stage3Part8Model (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 : W) (rest : List W) : State :=
  let v0 : W := UInt256.mulMod w0 w1 w2
  let v1 : W := v0 + w3
  let v2 : W := UInt256.mulMod (N 2048) v1 w4
  {s with pc := N 3838, memory := s.memory, stack := v2 :: w5 :: w6 :: w7 :: w8 :: w9 :: w10 :: w11 :: w12 :: w13 :: w14 :: w15 :: w16 :: w17 :: w18 :: w19 :: rest}

theorem stage3Part8_run (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions stage3Part8Program {s with pc := N 3832, memory := s.memory, stack := w0 :: w1 :: w2 :: w3 :: w4 :: w5 :: w6 :: w7 :: w8 :: w9 :: w10 :: w11 :: w12 :: w13 :: w14 :: w15 :: w16 :: w17 :: w18 :: w19 :: rest} = some (stage3Part8Model s w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 63) : rest.length+j < 1024 := by omega
  simp [hz, hzn, stage3Part8Program, stage3Part8Model, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, capacity]

def stage3Program : List Instr := (stage3Part0Program ++ (stage3Part1Program ++ (stage3Part2Program ++ (stage3Part3Program ++ (stage3Part4Program ++ (stage3Part5Program ++ (stage3Part6Program ++ (stage3Part7Program ++ stage3Part8Program))))))))
def stage3Model (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 : W) (rest : List W) : State :=
  let v0 : W := MachineState.readWord (s.memory) 32
  let v1 : W := MachineState.readWord (s.memory) 768
  let v2 : W := v0 * v1
  let v3 : W := w4 * w5
  let v4 : W := v3 + v2
  let v5 : W := UInt256.mulMod v0 v1 w8
  let v6 : W := UInt256.mulMod w4 w5 w8
  let v7 : W := v6 + v5
  let v8 : W := w0 + v7
  let v9 : W := w0 + v4
  let v10 : W := w9 * w13
  let v11 : W := v10 + v9
  let v12 : W := w7 * w1
  let v13 : W := v12 + v11
  let v14 : W := MachineState.readWord (s.memory) 192
  let v15 : W := v14 * w10
  let v16 : W := v15 + v13
  let v17 : W := UInt256.mulMod w9 w13 w8
  let v18 : W := v17 + v8
  let v19 : W := UInt256.mulMod w7 w1 w8
  let v20 : W := v19 + v18
  let v21 : W := MachineState.readWord (s.memory) 192
  let v22 : W := UInt256.mulMod v21 w10 w8
  let v23 : W := v22 + v20
  let v24 : W := MachineState.readWord (s.memory) 2720
  let v25 : W := v16 * v24
  let v26 : W := UInt256.land (N 1766847064778384329583297500742918515827483896875618958121606201292619775) v25
  let v27 : ByteArray := MachineState.writeBytes (s.memory) (Data.Bytes.natToBytesPadded v26.toNat 32) 0
  let v28 : W := UInt256.mulMod v26 w12 w8
  let v29 : W := v28 + v23
  let v30 : W := UInt256.mulMod (N 2048) v29 w8
  {s with pc := N 3838, memory := v27, stack := v30 :: w1 :: w2 :: w3 :: w4 :: w5 :: w6 :: w7 :: w8 :: w9 :: w10 :: w11 :: w12 :: w13 :: w14 :: w15 :: rest}

theorem stage3_run (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions stage3Program {s with pc := N 3730, memory := s.memory, stack := w0 :: w1 :: w2 :: w3 :: w4 :: w5 :: w6 :: w7 :: w8 :: w9 :: w10 :: w11 :: w12 :: w13 :: w14 :: w15 :: rest} = some (stage3Model s w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 rest) := by
  let v0 : W := MachineState.readWord (s.memory) 32
  let v1 : W := MachineState.readWord (s.memory) 768
  let v2 : W := v0 * v1
  let v3 : W := w4 * w5
  let v4 : W := v3 + v2
  let v5 : W := UInt256.mulMod v0 v1 w8
  let v6 : W := UInt256.mulMod w4 w5 w8
  let v7 : W := v6 + v5
  let v8 : W := w0 + v7
  let v9 : W := w0 + v4
  let v10 : W := w9 * w13
  let v11 : W := v10 + v9
  let v12 : W := w7 * w1
  let v13 : W := v12 + v11
  let v14 : W := MachineState.readWord (s.memory) 192
  let v15 : W := v14 * w10
  let v16 : W := v15 + v13
  let v17 : W := UInt256.mulMod w9 w13 w8
  let v18 : W := v17 + v8
  let v19 : W := UInt256.mulMod w7 w1 w8
  let v20 : W := v19 + v18
  let v21 : W := MachineState.readWord (s.memory) 192
  let v22 : W := UInt256.mulMod v21 w10 w8
  let v23 : W := v22 + v20
  let v24 : W := MachineState.readWord (s.memory) 2720
  let v25 : W := v16 * v24
  let v26 : W := UInt256.land (N 1766847064778384329583297500742918515827483896875618958121606201292619775) v25
  let v27 : ByteArray := MachineState.writeBytes (s.memory) (Data.Bytes.natToBytesPadded v26.toNat 32) 0
  let v28 : W := UInt256.mulMod v26 w12 w8
  let v29 : W := v28 + v23
  let v30 : W := UInt256.mulMod (N 2048) v29 w8
  have h0 : runInstructions stage3Part0Program {s with pc := N 3730, memory := s.memory, stack := w0 :: w1 :: w2 :: w3 :: w4 :: w5 :: w6 :: w7 :: w8 :: w9 :: w10 :: w11 :: w12 :: w13 :: w14 :: w15 :: rest} = some {s with pc := N 3741, memory := s.memory, stack := v2 :: v1 :: w8 :: v0 :: w0 :: w1 :: w2 :: w3 :: w4 :: w5 :: w6 :: w7 :: w8 :: w9 :: w10 :: w11 :: w12 :: w13 :: w14 :: w15 :: rest} := by
    simpa only [stage3Part0Model, v0, v1, v2] using stage3Part0_run ({s with memory := s.memory}) w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 rest hcap hact
  have h1 : runInstructions stage3Part1Program {s with pc := N 3741, memory := s.memory, stack := v2 :: v1 :: w8 :: v0 :: w0 :: w1 :: w2 :: w3 :: w4 :: w5 :: w6 :: w7 :: w8 :: w9 :: w10 :: w11 :: w12 :: w13 :: w14 :: w15 :: rest} = some {s with pc := N 3749, memory := s.memory, stack := w5 :: w8 :: v5 :: v4 :: w0 :: w1 :: w2 :: w3 :: w4 :: w5 :: w6 :: w7 :: w8 :: w9 :: w10 :: w11 :: w12 :: w13 :: w14 :: w15 :: rest} := by
    simpa only [stage3Part1Model, v3, v4, v5] using stage3Part1_run ({s with memory := s.memory}) v2 v1 w8 v0 w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 rest hcap hact
  have h2 : runInstructions stage3Part2Program {s with pc := N 3749, memory := s.memory, stack := w5 :: w8 :: v5 :: v4 :: w0 :: w1 :: w2 :: w3 :: w4 :: w5 :: w6 :: w7 :: w8 :: w9 :: w10 :: w11 :: w12 :: w13 :: w14 :: w15 :: rest} = some {s with pc := N 3757, memory := s.memory, stack := w13 :: v9 :: v8 :: w1 :: w2 :: w3 :: w4 :: w5 :: w6 :: w7 :: w8 :: w9 :: w10 :: w11 :: w12 :: w13 :: w14 :: w15 :: rest} := by
    simpa only [stage3Part2Model, v6, v7, v8, v9] using stage3Part2_run ({s with memory := s.memory}) w5 w8 v5 v4 w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 rest hcap hact
  have h3 : runInstructions stage3Part3Program {s with pc := N 3757, memory := s.memory, stack := w13 :: v9 :: v8 :: w1 :: w2 :: w3 :: w4 :: w5 :: w6 :: w7 :: w8 :: w9 :: w10 :: w11 :: w12 :: w13 :: w14 :: w15 :: rest} = some {s with pc := N 3765, memory := s.memory, stack := w10 :: v13 :: v8 :: w1 :: w2 :: w3 :: w4 :: w5 :: w6 :: w7 :: w8 :: w9 :: w10 :: w11 :: w12 :: w13 :: w14 :: w15 :: rest} := by
    simpa only [stage3Part3Model, v10, v11, v12, v13] using stage3Part3_run ({s with memory := s.memory}) w13 v9 v8 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 rest hcap hact
  have h4 : runInstructions stage3Part4Program {s with pc := N 3765, memory := s.memory, stack := w10 :: v13 :: v8 :: w1 :: w2 :: w3 :: w4 :: w5 :: w6 :: w7 :: w8 :: w9 :: w10 :: w11 :: w12 :: w13 :: w14 :: w15 :: rest} = some {s with pc := N 3774, memory := s.memory, stack := w9 :: w13 :: w8 :: v8 :: v16 :: w1 :: w2 :: w3 :: w4 :: w5 :: w6 :: w7 :: w8 :: w9 :: w10 :: w11 :: w12 :: w13 :: w14 :: w15 :: rest} := by
    simpa only [stage3Part4Model, v14, v15, v16] using stage3Part4_run ({s with memory := s.memory}) w10 v13 v8 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 rest hcap hact
  have h5 : runInstructions stage3Part5Program {s with pc := N 3774, memory := s.memory, stack := w9 :: w13 :: w8 :: v8 :: v16 :: w1 :: w2 :: w3 :: w4 :: w5 :: w6 :: w7 :: w8 :: w9 :: w10 :: w11 :: w12 :: w13 :: w14 :: w15 :: rest} = some {s with pc := N 3782, memory := s.memory, stack := w8 :: v20 :: v16 :: w1 :: w2 :: w3 :: w4 :: w5 :: w6 :: w7 :: w8 :: w9 :: w10 :: w11 :: w12 :: w13 :: w14 :: w15 :: rest} := by
    simpa only [stage3Part5Model, v17, v18, v19, v20] using stage3Part5_run ({s with memory := s.memory}) w9 w13 w8 v8 v16 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 rest hcap hact
  have h6 : runInstructions stage3Part6Program {s with pc := N 3782, memory := s.memory, stack := w8 :: v20 :: v16 :: w1 :: w2 :: w3 :: w4 :: w5 :: w6 :: w7 :: w8 :: w9 :: w10 :: w11 :: w12 :: w13 :: w14 :: w15 :: rest} = some {s with pc := N 3794, memory := s.memory, stack := v24 :: w12 :: w8 :: v23 :: v16 :: w1 :: w2 :: w3 :: w4 :: w5 :: w6 :: w7 :: w8 :: w9 :: w10 :: w11 :: w12 :: w13 :: w14 :: w15 :: rest} := by
    simpa only [stage3Part6Model, v21, v22, v23, v24] using stage3Part6_run ({s with memory := s.memory}) w8 v20 v16 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 rest hcap hact
  have h7 : runInstructions stage3Part7Program {s with pc := N 3794, memory := s.memory, stack := v24 :: w12 :: w8 :: v23 :: v16 :: w1 :: w2 :: w3 :: w4 :: w5 :: w6 :: w7 :: w8 :: w9 :: w10 :: w11 :: w12 :: w13 :: w14 :: w15 :: rest} = some {s with pc := N 3832, memory := v27, stack := v26 :: w12 :: w8 :: v23 :: w8 :: w1 :: w2 :: w3 :: w4 :: w5 :: w6 :: w7 :: w8 :: w9 :: w10 :: w11 :: w12 :: w13 :: w14 :: w15 :: rest} := by
    simpa only [stage3Part7Model, v25, v26, v27] using stage3Part7_run ({s with memory := s.memory}) v24 w12 w8 v23 v16 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 rest hcap hact
  have h8 : runInstructions stage3Part8Program {s with pc := N 3832, memory := v27, stack := v26 :: w12 :: w8 :: v23 :: w8 :: w1 :: w2 :: w3 :: w4 :: w5 :: w6 :: w7 :: w8 :: w9 :: w10 :: w11 :: w12 :: w13 :: w14 :: w15 :: rest} = some {s with pc := N 3838, memory := v27, stack := v30 :: w1 :: w2 :: w3 :: w4 :: w5 :: w6 :: w7 :: w8 :: w9 :: w10 :: w11 :: w12 :: w13 :: w14 :: w15 :: rest} := by
    simpa only [stage3Part8Model, v28, v29, v30] using stage3Part8_run ({s with memory := v27}) v26 w12 w8 v23 w8 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 rest hcap hact
  exact (runInstructions_append_some _ _ _ _ _ h0 (runInstructions_append_some _ _ _ _ _ h1 (runInstructions_append_some _ _ _ _ _ h2 (runInstructions_append_some _ _ _ _ _ h3 (runInstructions_append_some _ _ _ _ _ h4 (runInstructions_append_some _ _ _ _ _ h5 (runInstructions_append_some _ _ _ _ _ h6 (runInstructions_append_some _ _ _ _ _ h7 h8))))))))

end R9InvConsumeExec
