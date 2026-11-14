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
def stage7Part0Program : List Instr :=
  [
  .push 2 1568,
   .op .MLOAD,
   .op (.Swap sA7),
   .push 1 160,
   .op .MLOAD,
   .op (.Dup dA10),
   .push 2 768,
   .op .MLOAD]
def stage7Part0Model (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 : W) (rest : List W) : State :=
  let v0 : W := MachineState.readWord (s.memory) 1568
  let v1 : W := MachineState.readWord (s.memory) 160
  let v2 : W := MachineState.readWord (s.memory) 768
  {s with pc := N 4317,memory := s.memory,stack := v2::w8::v1::w7::w0::w1::w2::w3::w4::w5::w6::v0::w8::w9::w10::w11::w12::w13::w14::w15::rest}
theorem stage7Part0_run (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions stage7Part0Program {s with pc := N 4304,memory := s.memory,stack := w0::w1::w2::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::rest} = some (stage7Part0Model s w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 63) : rest.length+j < 1024 := by omega
  have ha160 : (160 : W).toNat = 160 := rfl
  have hf160 := Monpro.activeWords_fix s 160 32 (by decide) (by norm_num) hact
  have ha768 : (768 : W).toNat = 768 := rfl
  have hf768 := Monpro.activeWords_fix s 768 32 (by decide) (by norm_num) hact
  have ha1568 : (1568 : W).toNat = 1568 := rfl
  have hf1568 := Monpro.activeWords_fix s 1568 32 (by decide) (by norm_num) hact
  simp [hz,hzn,stage7Part0Program,stage7Part0Model,runInstructions,runInstr,List.exchange,succ_ofNat_mod,ofNat_add_mod,Nat.add_assoc,State.activeWordsAfterUInt256,literal_eq_ofNat,capacity,ha160,hf160,ha768,hf768,ha1568,hf1568]
def stage7Part1Program : List Instr :=
  [
  .op (.Dup dA15),
   .op (.Dup dA1),
   .op (.Dup dA4),
   .op .MUL,
   .op (.Dup dA10),
   .push 1 128,
   .op .MLOAD,
   .op .MUL,
   .op .ADD]
def stage7Part1Model (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 : W) (rest : List W) : State :=
  let v0 : W := w2 * w0
  let v1 : W := MachineState.readWord (s.memory) 128
  let v2 : W := v1 * w8
  let v3 : W := v2 + v0
  {s with pc := N 4327,memory := s.memory,stack := v3::w15::w0::w1::w2::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::w16::w17::w18::w19::rest}
theorem stage7Part1_run (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions stage7Part1Program {s with pc := N 4317,memory := s.memory,stack := w0::w1::w2::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::w16::w17::w18::w19::rest} = some (stage7Part1Model s w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 63) : rest.length+j < 1024 := by omega
  have ha128 : (128 : W).toNat = 128 := rfl
  have hf128 := Monpro.activeWords_fix s 128 32 (by decide) (by norm_num) hact
  simp [hz,hzn,stage7Part1Program,stage7Part1Model,runInstructions,runInstr,List.exchange,succ_ofNat_mod,ofNat_add_mod,Nat.add_assoc,State.activeWordsAfterUInt256,literal_eq_ofNat,capacity,ha128,hf128]
def stage7Part2Program : List Instr :=
  [
  .op (.Swap sA0),
   .op (.Dup dA11),
   .op .MUL,
   .op .ADD,
   .push 1 64,
   .op .MLOAD]
def stage7Part2Model (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 w20 w21 : W) (rest : List W) : State :=
  let v0 : W := w11 * w1
  let v1 : W := v0 + w0
  let v2 : W := MachineState.readWord (s.memory) 64
  {s with pc := N 4334,memory := s.memory,stack := v2::v1::w2::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::w16::w17::w18::w19::w20::w21::rest}
theorem stage7Part2_run (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 w20 w21 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions stage7Part2Program {s with pc := N 4327,memory := s.memory,stack := w0::w1::w2::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::w16::w17::w18::w19::w20::w21::rest} = some (stage7Part2Model s w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 w20 w21 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 63) : rest.length+j < 1024 := by omega
  have ha64 : (64 : W).toNat = 64 := rfl
  have hf64 := Monpro.activeWords_fix s 64 32 (by decide) (by norm_num) hact
  simp [hz,hzn,stage7Part2Program,stage7Part2Model,runInstructions,runInstr,List.exchange,succ_ofNat_mod,ofNat_add_mod,Nat.add_assoc,State.activeWordsAfterUInt256,literal_eq_ofNat,capacity,ha64,hf64]
def stage7Part3Program : List Instr :=
  [
  .push 1 32,
   .op .MLOAD,
   .op .MUL,
   .op .ADD,
   .op (.Swap sA2),
   .op .MULMOD,
   .op (.Dup dA11)]
def stage7Part3Model (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 w20 w21 : W) (rest : List W) : State :=
  let v0 : W := MachineState.readWord (s.memory) 32
  let v1 : W := v0 * w0
  let v2 : W := v1 + w1
  let v3 : W := UInt256.mulMod w4 w2 w3
  {s with pc := N 4342,memory := s.memory,stack := w14::v3::v2::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::w16::w17::w18::w19::w20::w21::rest}
theorem stage7Part3_run (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 w20 w21 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions stage7Part3Program {s with pc := N 4334,memory := s.memory,stack := w0::w1::w2::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::w16::w17::w18::w19::w20::w21::rest} = some (stage7Part3Model s w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 w20 w21 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 63) : rest.length+j < 1024 := by omega
  have ha32 : (32 : W).toNat = 32 := rfl
  have hf32 := Monpro.activeWords_fix s 32 32 (by decide) (by norm_num) hact
  simp [hz,hzn,stage7Part3Program,stage7Part3Model,runInstructions,runInstr,List.exchange,succ_ofNat_mod,ofNat_add_mod,Nat.add_assoc,State.activeWordsAfterUInt256,literal_eq_ofNat,capacity,ha32,hf32]
def stage7Part4Program : List Instr :=
  [
  .push 1 128,
   .op .MLOAD,
   .op (.Dup dA9),
   .op .MULMOD,
   .op .ADD,
   .op (.Dup dA11),
   .op (.Dup dA15)]
def stage7Part4Model (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 : W) (rest : List W) : State :=
  let v0 : W := MachineState.readWord (s.memory) 128
  let v1 : W := UInt256.mulMod w8 v0 w0
  let v2 : W := v1 + w1
  {s with pc := N 4350,memory := s.memory,stack := w15::w12::v2::w2::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::w16::w17::w18::w19::rest}
theorem stage7Part4_run (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions stage7Part4Program {s with pc := N 4342,memory := s.memory,stack := w0::w1::w2::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::w16::w17::w18::w19::rest} = some (stage7Part4Model s w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 63) : rest.length+j < 1024 := by omega
  have ha128 : (128 : W).toNat = 128 := rfl
  have hf128 := Monpro.activeWords_fix s 128 32 (by decide) (by norm_num) hact
  simp [hz,hzn,stage7Part4Program,stage7Part4Model,runInstructions,runInstr,List.exchange,succ_ofNat_mod,ofNat_add_mod,Nat.add_assoc,State.activeWordsAfterUInt256,literal_eq_ofNat,capacity,ha128,hf128]
def stage7Part5Program : List Instr :=
  [
  .op (.Dup dA10),
   .op .MULMOD,
   .op .ADD,
   .op (.Dup dA11),
   .push 1 64,
   .op .MLOAD,
   .push 1 32,
   .op .MLOAD]
def stage7Part5Model (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 w20 : W) (rest : List W) : State :=
  let v0 : W := UInt256.mulMod w10 w0 w1
  let v1 : W := v0 + w2
  let v2 : W := MachineState.readWord (s.memory) 64
  let v3 : W := MachineState.readWord (s.memory) 32
  {s with pc := N 4360,memory := s.memory,stack := v3::v2::w13::v1::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::w16::w17::w18::w19::w20::rest}
theorem stage7Part5_run (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 w20 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions stage7Part5Program {s with pc := N 4350,memory := s.memory,stack := w0::w1::w2::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::w16::w17::w18::w19::w20::rest} = some (stage7Part5Model s w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 w20 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 63) : rest.length+j < 1024 := by omega
  have ha32 : (32 : W).toNat = 32 := rfl
  have hf32 := Monpro.activeWords_fix s 32 32 (by decide) (by norm_num) hact
  have ha64 : (64 : W).toNat = 64 := rfl
  have hf64 := Monpro.activeWords_fix s 64 32 (by decide) (by norm_num) hact
  simp [hz,hzn,stage7Part5Program,stage7Part5Model,runInstructions,runInstr,List.exchange,succ_ofNat_mod,ofNat_add_mod,Nat.add_assoc,State.activeWordsAfterUInt256,literal_eq_ofNat,capacity,ha32,hf32,ha64,hf64]
def stage7Part6Program : List Instr :=
  [
  .op .MULMOD,
   .op .ADD,
   .op (.Dup dA3),
   .op .ADD,
   .op (.Swap sA2),
   .op .ADD,
   .op (.Dup dA11),
   .op (.Dup dA10)]
def stage7Part6Model (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 w20 w21 : W) (rest : List W) : State :=
  let v0 : W := UInt256.mulMod w0 w1 w2
  let v1 : W := v0 + w3
  let v2 : W := w6 + v1
  let v3 : W := w6 + w4
  {s with pc := N 4368,memory := s.memory,stack := w13::w15::v3::w5::v2::w7::w8::w9::w10::w11::w12::w13::w14::w15::w16::w17::w18::w19::w20::w21::rest}
theorem stage7Part6_run (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 w20 w21 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions stage7Part6Program {s with pc := N 4360,memory := s.memory,stack := w0::w1::w2::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::w16::w17::w18::w19::w20::w21::rest} = some (stage7Part6Model s w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 w20 w21 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 63) : rest.length+j < 1024 := by omega
  simp [hz,hzn,stage7Part6Program,stage7Part6Model,runInstructions,runInstr,List.exchange,succ_ofNat_mod,ofNat_add_mod,Nat.add_assoc,State.activeWordsAfterUInt256,literal_eq_ofNat,capacity]
def stage7Part7Program : List Instr :=
  [
  .op .MUL,
   .op .ADD,
   .op (.Dup dA4),
   .op (.Dup dA2),
   .op .MUL,
   .op .ADD,
   .op (.Dup dA8)]
def stage7Part7Model (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 : W) (rest : List W) : State :=
  let v0 : W := w0 * w1
  let v1 : W := v0 + w2
  let v2 : W := w3 * w6
  let v3 : W := v2 + v1
  {s with pc := N 4375,memory := s.memory,stack := w10::v3::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::w16::w17::w18::w19::rest}
theorem stage7Part7_run (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions stage7Part7Program {s with pc := N 4368,memory := s.memory,stack := w0::w1::w2::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::w16::w17::w18::w19::rest} = some (stage7Part7Model s w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 63) : rest.length+j < 1024 := by omega
  simp [hz,hzn,stage7Part7Program,stage7Part7Model,runInstructions,runInstr,List.exchange,succ_ofNat_mod,ofNat_add_mod,Nat.add_assoc,State.activeWordsAfterUInt256,literal_eq_ofNat,capacity]
def stage7Part8Program : List Instr :=
  [
  .push 1 192,
   .op .MLOAD,
   .op .MUL,
   .op .ADD,
   .op (.Dup dA5),
   .push 0 0,
   .op .MLOAD,
   .op .MUL]
def stage7Part8Model (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 : W) (rest : List W) : State :=
  let v0 : W := MachineState.readWord (s.memory) 192
  let v1 : W := v0 * w0
  let v2 : W := v1 + w1
  let v3 : W := MachineState.readWord (s.memory) 0
  let v4 : W := v3 * w6
  {s with pc := N 4384,memory := s.memory,stack := v4::v2::w2::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::w16::w17::w18::rest}
theorem stage7Part8_run (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions stage7Part8Program {s with pc := N 4375,memory := s.memory,stack := w0::w1::w2::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::w16::w17::w18::rest} = some (stage7Part8Model s w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 63) : rest.length+j < 1024 := by omega
  have ha0 : (0 : W).toNat = 0 := rfl
  have hf0 := Monpro.activeWords_fix s 0 32 (by decide) (by norm_num) hact
  have ha192 : (192 : W).toNat = 192 := rfl
  have hf192 := Monpro.activeWords_fix s 192 32 (by decide) (by norm_num) hact
  simp [hz,hzn,stage7Part8Program,stage7Part8Model,runInstructions,runInstr,List.exchange,succ_ofNat_mod,ofNat_add_mod,Nat.add_assoc,State.activeWordsAfterUInt256,literal_eq_ofNat,capacity,ha0,hf0,ha192,hf192]
def stage7Part9Program : List Instr :=
  [
  .op .ADD,
   .op (.Dup dA15),
   .push 1 224,
   .op .MLOAD,
   .op .MUL,
   .op .ADD,
   .op (.Dup dA3)]
def stage7Part9Model (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 : W) (rest : List W) : State :=
  let v0 : W := w0 + w1
  let v1 : W := MachineState.readWord (s.memory) 224
  let v2 : W := v1 * w16
  let v3 : W := v2 + v0
  {s with pc := N 4392,memory := s.memory,stack := w4::v3::w2::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::w16::w17::w18::rest}
theorem stage7Part9_run (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions stage7Part9Program {s with pc := N 4384,memory := s.memory,stack := w0::w1::w2::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::w16::w17::w18::rest} = some (stage7Part9Model s w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 63) : rest.length+j < 1024 := by omega
  have ha224 : (224 : W).toNat = 224 := rfl
  have hf224 := Monpro.activeWords_fix s 224 32 (by decide) (by norm_num) hact
  simp [hz,hzn,stage7Part9Program,stage7Part9Model,runInstructions,runInstr,List.exchange,succ_ofNat_mod,ofNat_add_mod,Nat.add_assoc,State.activeWordsAfterUInt256,literal_eq_ofNat,capacity,ha224,hf224]
def stage7Part10Program : List Instr :=
  [
  .push 2 1216,
   .op .MLOAD,
   .op .MUL,
   .op .ADD,
   .op (.Dup dA12),
   .push 2 1248,
   .op .MLOAD,
   .op .MUL]
def stage7Part10Model (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 : W) (rest : List W) : State :=
  let v0 : W := MachineState.readWord (s.memory) 1216
  let v1 : W := v0 * w0
  let v2 : W := v1 + w1
  let v3 : W := MachineState.readWord (s.memory) 1248
  let v4 : W := v3 * w13
  {s with pc := N 4404,memory := s.memory,stack := v4::v2::w2::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::w16::w17::w18::rest}
theorem stage7Part10_run (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions stage7Part10Program {s with pc := N 4392,memory := s.memory,stack := w0::w1::w2::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::w16::w17::w18::rest} = some (stage7Part10Model s w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 63) : rest.length+j < 1024 := by omega
  have ha1216 : (1216 : W).toNat = 1216 := rfl
  have hf1216 := Monpro.activeWords_fix s 1216 32 (by decide) (by norm_num) hact
  have ha1248 : (1248 : W).toNat = 1248 := rfl
  have hf1248 := Monpro.activeWords_fix s 1248 32 (by decide) (by norm_num) hact
  simp [hz,hzn,stage7Part10Program,stage7Part10Model,runInstructions,runInstr,List.exchange,succ_ofNat_mod,ofNat_add_mod,Nat.add_assoc,State.activeWordsAfterUInt256,literal_eq_ofNat,capacity,ha1216,hf1216,ha1248,hf1248]
def stage7Part11Program : List Instr :=
  [
  .op .ADD,
   .op (.Swap sA1),
   .op (.Dup dA10),
   .op (.Dup dA12),
   .op (.Dup dA11),
   .op .MULMOD,
   .op .ADD,
   .op (.Dup dA10)]
def stage7Part11Model (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 : W) (rest : List W) : State :=
  let v0 : W := w0 + w1
  let v1 : W := UInt256.mulMod w10 w12 w11
  let v2 : W := v1 + w3
  {s with pc := N 4412,memory := s.memory,stack := w11::v2::w2::v0::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::w16::w17::w18::rest}
theorem stage7Part11_run (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions stage7Part11Program {s with pc := N 4404,memory := s.memory,stack := w0::w1::w2::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::w16::w17::w18::rest} = some (stage7Part11Model s w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 63) : rest.length+j < 1024 := by omega
  simp [hz,hzn,stage7Part11Program,stage7Part11Model,runInstructions,runInstr,List.exchange,succ_ofNat_mod,ofNat_add_mod,Nat.add_assoc,State.activeWordsAfterUInt256,literal_eq_ofNat,capacity]
def stage7Part12Program : List Instr :=
  [
  .op (.Dup dA5),
   .op (.Dup dA3),
   .op .MULMOD,
   .op .ADD,
   .op (.Swap sA0),
   .push 2 1088,
   .op .MSTORE,
   .op (.Dup dA9)]
def stage7Part12Model (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 : W) (rest : List W) : State :=
  let v0 : W := UInt256.mulMod w2 w5 w0
  let v1 : W := v0 + w1
  let v2 : ByteArray := MachineState.writeBytes (s.memory) (Data.Bytes.natToBytesPadded w2.toNat 32) 1088
  {s with pc := N 4422,memory := v2,stack := w11::v1::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::w16::w17::w18::rest}
theorem stage7Part12_run (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions stage7Part12Program {s with pc := N 4412,memory := s.memory,stack := w0::w1::w2::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::w16::w17::w18::rest} = some (stage7Part12Model s w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 63) : rest.length+j < 1024 := by omega
  have ha1088 : (1088 : W).toNat = 1088 := rfl
  have hf1088 := Monpro.activeWords_fix s 1088 32 (by decide) (by norm_num) hact
  simp [hz,hzn,stage7Part12Program,stage7Part12Model,runInstructions,runInstr,List.exchange,succ_ofNat_mod,ofNat_add_mod,Nat.add_assoc,State.activeWordsAfterUInt256,literal_eq_ofNat,capacity,ha1088,hf1088]
def stage7Part13Program : List Instr :=
  [
  .op (.Dup dA8),
   .push 1 192,
   .op .MLOAD,
   .op .MULMOD,
   .op .ADD,
   .op (.Dup dA9),
   .op (.Dup dA5)]
def stage7Part13Model (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 : W) (rest : List W) : State :=
  let v0 : W := MachineState.readWord (s.memory) 192
  let v1 : W := UInt256.mulMod v0 w8 w0
  let v2 : W := v1 + w1
  {s with pc := N 4430,memory := s.memory,stack := w5::w10::v2::w2::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::w16::w17::rest}
theorem stage7Part13_run (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions stage7Part13Program {s with pc := N 4422,memory := s.memory,stack := w0::w1::w2::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::w16::w17::rest} = some (stage7Part13Model s w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 63) : rest.length+j < 1024 := by omega
  have ha192 : (192 : W).toNat = 192 := rfl
  have hf192 := Monpro.activeWords_fix s 192 32 (by decide) (by norm_num) hact
  simp [hz,hzn,stage7Part13Program,stage7Part13Model,runInstructions,runInstr,List.exchange,succ_ofNat_mod,ofNat_add_mod,Nat.add_assoc,State.activeWordsAfterUInt256,literal_eq_ofNat,capacity,ha192,hf192]
def stage7Part14Program : List Instr :=
  [
  .push 0 0,
   .op .MLOAD,
   .op .MULMOD,
   .op .ADD,
   .op (.Dup dA9),
   .op (.Dup dA15),
   .push 1 224,
   .op .MLOAD]
def stage7Part14Model (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 : W) (rest : List W) : State :=
  let v0 : W := MachineState.readWord (s.memory) 0
  let v1 : W := UInt256.mulMod v0 w0 w1
  let v2 : W := v1 + w2
  let v3 : W := MachineState.readWord (s.memory) 224
  {s with pc := N 4439,memory := s.memory,stack := v3::w16::w11::v2::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::w16::w17::w18::rest}
theorem stage7Part14_run (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions stage7Part14Program {s with pc := N 4430,memory := s.memory,stack := w0::w1::w2::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::w16::w17::w18::rest} = some (stage7Part14Model s w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 63) : rest.length+j < 1024 := by omega
  have ha0 : (0 : W).toNat = 0 := rfl
  have hf0 := Monpro.activeWords_fix s 0 32 (by decide) (by norm_num) hact
  have ha224 : (224 : W).toNat = 224 := rfl
  have hf224 := Monpro.activeWords_fix s 224 32 (by decide) (by norm_num) hact
  simp [hz,hzn,stage7Part14Program,stage7Part14Model,runInstructions,runInstr,List.exchange,succ_ofNat_mod,ofNat_add_mod,Nat.add_assoc,State.activeWordsAfterUInt256,literal_eq_ofNat,capacity,ha0,hf0,ha224,hf224]
def stage7Part15Program : List Instr :=
  [
  .op .MULMOD,
   .op .ADD,
   .op (.Dup dA9),
   .op (.Dup dA3),
   .push 2 1216,
   .op .MLOAD,
   .op .MULMOD,
   .op .ADD]
def stage7Part15Model (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 : W) (rest : List W) : State :=
  let v0 : W := UInt256.mulMod w0 w1 w2
  let v1 : W := v0 + w3
  let v2 : W := MachineState.readWord (s.memory) 1216
  let v3 : W := UInt256.mulMod v2 w5 w12
  let v4 : W := v3 + v1
  {s with pc := N 4449,memory := s.memory,stack := v4::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::w16::w17::w18::w19::rest}
theorem stage7Part15_run (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions stage7Part15Program {s with pc := N 4439,memory := s.memory,stack := w0::w1::w2::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::w16::w17::w18::w19::rest} = some (stage7Part15Model s w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 63) : rest.length+j < 1024 := by omega
  have ha1216 : (1216 : W).toNat = 1216 := rfl
  have hf1216 := Monpro.activeWords_fix s 1216 32 (by decide) (by norm_num) hact
  simp [hz,hzn,stage7Part15Program,stage7Part15Model,runInstructions,runInstr,List.exchange,succ_ofNat_mod,ofNat_add_mod,Nat.add_assoc,State.activeWordsAfterUInt256,literal_eq_ofNat,capacity,ha1216,hf1216]
def stage7Part16Program : List Instr :=
  [
  .op (.Dup dA9),
   .op (.Dup dA12),
   .push 2 1248,
   .op .MLOAD,
   .op .MULMOD,
   .op .ADD,
   .op (.Dup dA9),
   .op (.Dup dA14)]
def stage7Part16Model (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 : W) (rest : List W) : State :=
  let v0 : W := MachineState.readWord (s.memory) 1248
  let v1 : W := UInt256.mulMod v0 w11 w9
  let v2 : W := v1 + w0
  {s with pc := N 4459,memory := s.memory,stack := w13::w9::v2::w1::w2::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::w16::rest}
theorem stage7Part16_run (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions stage7Part16Program {s with pc := N 4449,memory := s.memory,stack := w0::w1::w2::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::w16::rest} = some (stage7Part16Model s w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 63) : rest.length+j < 1024 := by omega
  have ha1248 : (1248 : W).toNat = 1248 := rfl
  have hf1248 := Monpro.activeWords_fix s 1248 32 (by decide) (by norm_num) hact
  simp [hz,hzn,stage7Part16Program,stage7Part16Model,runInstructions,runInstr,List.exchange,succ_ofNat_mod,ofNat_add_mod,Nat.add_assoc,State.activeWordsAfterUInt256,literal_eq_ofNat,capacity,ha1248,hf1248]
def stage7Part17Program : List Instr :=
  [
  .push 2 2720,
   .op .MLOAD,
   .op (.Dup dA2),
   .op (.Swap sA4),
   .op .MUL,
   .push 30 1766847064778384329583297500742918515827483896875618958121606201292619775,
   .op .AND,
   .op (.Dup dA0)]
def stage7Part17Model (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 : W) (rest : List W) : State :=
  let v0 : W := MachineState.readWord (s.memory) 2720
  let v1 : W := w3 * v0
  let v2 : W := UInt256.land (N 1766847064778384329583297500742918515827483896875618958121606201292619775) v1
  {s with pc := N 4499,memory := s.memory,stack := v2::v2::w0::w1::w2::w1::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::w16::w17::w18::rest}
theorem stage7Part17_run (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions stage7Part17Program {s with pc := N 4459,memory := s.memory,stack := w0::w1::w2::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::w16::w17::w18::rest} = some (stage7Part17Model s w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 63) : rest.length+j < 1024 := by omega
  have ha2720 : (2720 : W).toNat = 2720 := rfl
  have hf2720 := Monpro.activeWords_fix s 2720 32 (by decide) (by norm_num) hact
  simp [hz,hzn,stage7Part17Program,stage7Part17Model,runInstructions,runInstr,List.exchange,succ_ofNat_mod,ofNat_add_mod,Nat.add_assoc,State.activeWordsAfterUInt256,literal_eq_ofNat,capacity,ha2720,hf2720]
def stage7Part18Program : List Instr :=
  [
  .push 2 1280,
   .op .MSTORE,
   .op .MULMOD,
   .op .ADD,
   .push 2 2048,
   .op .MULMOD]
def stage7Part18Model (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 w20 : W) (rest : List W) : State :=
  let v0 : ByteArray := MachineState.writeBytes (s.memory) (Data.Bytes.natToBytesPadded w0.toNat 32) 1280
  let v1 : W := UInt256.mulMod w1 w2 w3
  let v2 : W := v1 + w4
  let v3 : W := UInt256.mulMod (N 2048) v2 w5
  {s with pc := N 4509,memory := v0,stack := v3::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::w16::w17::w18::w19::w20::rest}
theorem stage7Part18_run (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 w20 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions stage7Part18Program {s with pc := N 4499,memory := s.memory,stack := w0::w1::w2::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::w16::w17::w18::w19::w20::rest} = some (stage7Part18Model s w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 w20 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 63) : rest.length+j < 1024 := by omega
  have ha1280 : (1280 : W).toNat = 1280 := rfl
  have hf1280 := Monpro.activeWords_fix s 1280 32 (by decide) (by norm_num) hact
  simp [hz,hzn,stage7Part18Program,stage7Part18Model,runInstructions,runInstr,List.exchange,succ_ofNat_mod,ofNat_add_mod,Nat.add_assoc,State.activeWordsAfterUInt256,literal_eq_ofNat,capacity,ha1280,hf1280]
def stage7Program : List Instr := (stage7Part0Program++(stage7Part1Program++(stage7Part2Program++(stage7Part3Program++(stage7Part4Program++(stage7Part5Program++(stage7Part6Program++(stage7Part7Program++(stage7Part8Program++(stage7Part9Program++(stage7Part10Program++(stage7Part11Program++(stage7Part12Program++(stage7Part13Program++(stage7Part14Program++(stage7Part15Program++(stage7Part16Program++(stage7Part17Program++stage7Part18Program))))))))))))))))))
def stage7Model (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 : W) (rest : List W) : State :=
  let v0 : W := MachineState.readWord (s.memory) 1568
  let v1 : W := MachineState.readWord (s.memory) 160
  let v2 : W := MachineState.readWord (s.memory) 768
  let v3 : W := v1 * v2
  let v4 : W := MachineState.readWord (s.memory) 128
  let v5 : W := v4 * w4
  let v6 : W := v5 + v3
  let v7 : W := w5 * w11
  let v8 : W := v7 + v6
  let v9 : W := MachineState.readWord (s.memory) 64
  let v10 : W := MachineState.readWord (s.memory) 32
  let v11 : W := v10 * v9
  let v12 : W := v11 + v8
  let v13 : W := UInt256.mulMod v1 v2 w8
  let v14 : W := MachineState.readWord (s.memory) 128
  let v15 : W := UInt256.mulMod w4 v14 w8
  let v16 : W := v15 + v13
  let v17 : W := UInt256.mulMod w5 w11 w8
  let v18 : W := v17 + v16
  let v19 : W := MachineState.readWord (s.memory) 64
  let v20 : W := MachineState.readWord (s.memory) 32
  let v21 : W := UInt256.mulMod v20 v19 w8
  let v22 : W := v21 + v18
  let v23 : W := w0 + v22
  let v24 : W := w0 + v12
  let v25 : W := v0 * w9
  let v26 : W := v25 + v24
  let v27 : W := w7 * w2
  let v28 : W := v27 + v26
  let v29 : W := MachineState.readWord (s.memory) 192
  let v30 : W := v29 * w6
  let v31 : W := v30 + v28
  let v32 : W := MachineState.readWord (s.memory) 0
  let v33 : W := v32 * w3
  let v34 : W := v33 + v31
  let v35 : W := MachineState.readWord (s.memory) 224
  let v36 : W := v35 * w13
  let v37 : W := v36 + v34
  let v38 : W := MachineState.readWord (s.memory) 1216
  let v39 : W := v38 * w1
  let v40 : W := v39 + v37
  let v41 : W := MachineState.readWord (s.memory) 1248
  let v42 : W := v41 * w10
  let v43 : W := v42 + v40
  let v44 : W := UInt256.mulMod v0 w9 w8
  let v45 : W := v44 + v23
  let v46 : W := UInt256.mulMod w7 w2 w8
  let v47 : W := v46 + v45
  let v48 : ByteArray := MachineState.writeBytes (s.memory) (Data.Bytes.natToBytesPadded w7.toNat 32) 1088
  let v49 : W := MachineState.readWord v48 192
  let v50 : W := UInt256.mulMod v49 w6 w8
  let v51 : W := v50 + v47
  let v52 : W := MachineState.readWord v48 0
  let v53 : W := UInt256.mulMod v52 w3 w8
  let v54 : W := v53 + v51
  let v55 : W := MachineState.readWord v48 224
  let v56 : W := UInt256.mulMod v55 w13 w8
  let v57 : W := v56 + v54
  let v58 : W := MachineState.readWord v48 1216
  let v59 : W := UInt256.mulMod v58 w1 w8
  let v60 : W := v59 + v57
  let v61 : W := MachineState.readWord v48 1248
  let v62 : W := UInt256.mulMod v61 w10 w8
  let v63 : W := v62 + v60
  let v64 : W := MachineState.readWord v48 2720
  let v65 : W := v43 * v64
  let v66 : W := UInt256.land (N 1766847064778384329583297500742918515827483896875618958121606201292619775) v65
  let v67 : ByteArray := MachineState.writeBytes v48 (Data.Bytes.natToBytesPadded v66.toNat 32) 1280
  let v68 : W := UInt256.mulMod v66 w12 w8
  let v69 : W := v68 + v63
  let v70 : W := UInt256.mulMod (N 2048) v69 w8
  {s with pc := N 4509,memory := v67,stack := v70::w1::w2::w3::w4::w5::w6::v0::w8::w9::w10::w11::w12::w13::w14::w15::rest}
theorem stage7_run (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions stage7Program {s with pc := N 4304,memory := s.memory,stack := w0::w1::w2::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::rest} = some (stage7Model s w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 rest) := by
  let v0 : W := MachineState.readWord (s.memory) 1568
  let v1 : W := MachineState.readWord (s.memory) 160
  let v2 : W := MachineState.readWord (s.memory) 768
  let v3 : W := v1 * v2
  let v4 : W := MachineState.readWord (s.memory) 128
  let v5 : W := v4 * w4
  let v6 : W := v5 + v3
  let v7 : W := w5 * w11
  let v8 : W := v7 + v6
  let v9 : W := MachineState.readWord (s.memory) 64
  let v10 : W := MachineState.readWord (s.memory) 32
  let v11 : W := v10 * v9
  let v12 : W := v11 + v8
  let v13 : W := UInt256.mulMod v1 v2 w8
  let v14 : W := MachineState.readWord (s.memory) 128
  let v15 : W := UInt256.mulMod w4 v14 w8
  let v16 : W := v15 + v13
  let v17 : W := UInt256.mulMod w5 w11 w8
  let v18 : W := v17 + v16
  let v19 : W := MachineState.readWord (s.memory) 64
  let v20 : W := MachineState.readWord (s.memory) 32
  let v21 : W := UInt256.mulMod v20 v19 w8
  let v22 : W := v21 + v18
  let v23 : W := w0 + v22
  let v24 : W := w0 + v12
  let v25 : W := v0 * w9
  let v26 : W := v25 + v24
  let v27 : W := w7 * w2
  let v28 : W := v27 + v26
  let v29 : W := MachineState.readWord (s.memory) 192
  let v30 : W := v29 * w6
  let v31 : W := v30 + v28
  let v32 : W := MachineState.readWord (s.memory) 0
  let v33 : W := v32 * w3
  let v34 : W := v33 + v31
  let v35 : W := MachineState.readWord (s.memory) 224
  let v36 : W := v35 * w13
  let v37 : W := v36 + v34
  let v38 : W := MachineState.readWord (s.memory) 1216
  let v39 : W := v38 * w1
  let v40 : W := v39 + v37
  let v41 : W := MachineState.readWord (s.memory) 1248
  let v42 : W := v41 * w10
  let v43 : W := v42 + v40
  let v44 : W := UInt256.mulMod v0 w9 w8
  let v45 : W := v44 + v23
  let v46 : W := UInt256.mulMod w7 w2 w8
  let v47 : W := v46 + v45
  let v48 : ByteArray := MachineState.writeBytes (s.memory) (Data.Bytes.natToBytesPadded w7.toNat 32) 1088
  let v49 : W := MachineState.readWord v48 192
  let v50 : W := UInt256.mulMod v49 w6 w8
  let v51 : W := v50 + v47
  let v52 : W := MachineState.readWord v48 0
  let v53 : W := UInt256.mulMod v52 w3 w8
  let v54 : W := v53 + v51
  let v55 : W := MachineState.readWord v48 224
  let v56 : W := UInt256.mulMod v55 w13 w8
  let v57 : W := v56 + v54
  let v58 : W := MachineState.readWord v48 1216
  let v59 : W := UInt256.mulMod v58 w1 w8
  let v60 : W := v59 + v57
  let v61 : W := MachineState.readWord v48 1248
  let v62 : W := UInt256.mulMod v61 w10 w8
  let v63 : W := v62 + v60
  let v64 : W := MachineState.readWord v48 2720
  let v65 : W := v43 * v64
  let v66 : W := UInt256.land (N 1766847064778384329583297500742918515827483896875618958121606201292619775) v65
  let v67 : ByteArray := MachineState.writeBytes v48 (Data.Bytes.natToBytesPadded v66.toNat 32) 1280
  let v68 : W := UInt256.mulMod v66 w12 w8
  let v69 : W := v68 + v63
  let v70 : W := UInt256.mulMod (N 2048) v69 w8
  have h0 : runInstructions stage7Part0Program {s with pc := N 4304,memory := s.memory,stack := w0::w1::w2::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::rest} = some {s with pc := N 4317,memory := s.memory,stack := v2::w8::v1::w7::w0::w1::w2::w3::w4::w5::w6::v0::w8::w9::w10::w11::w12::w13::w14::w15::rest} := by
    simpa only [stage7Part0Model,v0,v1,v2] using stage7Part0_run ({s with memory := s.memory}) w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 rest hcap hact
  have h1 : runInstructions stage7Part1Program {s with pc := N 4317,memory := s.memory,stack := v2::w8::v1::w7::w0::w1::w2::w3::w4::w5::w6::v0::w8::w9::w10::w11::w12::w13::w14::w15::rest} = some {s with pc := N 4327,memory := s.memory,stack := v6::w11::v2::w8::v1::w7::w0::w1::w2::w3::w4::w5::w6::v0::w8::w9::w10::w11::w12::w13::w14::w15::rest} := by
    simpa only [stage7Part1Model,v3,v4,v5,v6] using stage7Part1_run ({s with memory := s.memory}) v2 w8 v1 w7 w0 w1 w2 w3 w4 w5 w6 v0 w8 w9 w10 w11 w12 w13 w14 w15 rest hcap hact
  have h2 : runInstructions stage7Part2Program {s with pc := N 4327,memory := s.memory,stack := v6::w11::v2::w8::v1::w7::w0::w1::w2::w3::w4::w5::w6::v0::w8::w9::w10::w11::w12::w13::w14::w15::rest} = some {s with pc := N 4334,memory := s.memory,stack := v9::v8::v2::w8::v1::w7::w0::w1::w2::w3::w4::w5::w6::v0::w8::w9::w10::w11::w12::w13::w14::w15::rest} := by
    simpa only [stage7Part2Model,v7,v8,v9] using stage7Part2_run ({s with memory := s.memory}) v6 w11 v2 w8 v1 w7 w0 w1 w2 w3 w4 w5 w6 v0 w8 w9 w10 w11 w12 w13 w14 w15 rest hcap hact
  have h3 : runInstructions stage7Part3Program {s with pc := N 4334,memory := s.memory,stack := v9::v8::v2::w8::v1::w7::w0::w1::w2::w3::w4::w5::w6::v0::w8::w9::w10::w11::w12::w13::w14::w15::rest} = some {s with pc := N 4342,memory := s.memory,stack := w8::v13::v12::w7::w0::w1::w2::w3::w4::w5::w6::v0::w8::w9::w10::w11::w12::w13::w14::w15::rest} := by
    simpa only [stage7Part3Model,v10,v11,v12,v13] using stage7Part3_run ({s with memory := s.memory}) v9 v8 v2 w8 v1 w7 w0 w1 w2 w3 w4 w5 w6 v0 w8 w9 w10 w11 w12 w13 w14 w15 rest hcap hact
  have h4 : runInstructions stage7Part4Program {s with pc := N 4342,memory := s.memory,stack := w8::v13::v12::w7::w0::w1::w2::w3::w4::w5::w6::v0::w8::w9::w10::w11::w12::w13::w14::w15::rest} = some {s with pc := N 4350,memory := s.memory,stack := w11::w8::v16::v12::w7::w0::w1::w2::w3::w4::w5::w6::v0::w8::w9::w10::w11::w12::w13::w14::w15::rest} := by
    simpa only [stage7Part4Model,v14,v15,v16] using stage7Part4_run ({s with memory := s.memory}) w8 v13 v12 w7 w0 w1 w2 w3 w4 w5 w6 v0 w8 w9 w10 w11 w12 w13 w14 w15 rest hcap hact
  have h5 : runInstructions stage7Part5Program {s with pc := N 4350,memory := s.memory,stack := w11::w8::v16::v12::w7::w0::w1::w2::w3::w4::w5::w6::v0::w8::w9::w10::w11::w12::w13::w14::w15::rest} = some {s with pc := N 4360,memory := s.memory,stack := v20::v19::w8::v18::v12::w7::w0::w1::w2::w3::w4::w5::w6::v0::w8::w9::w10::w11::w12::w13::w14::w15::rest} := by
    simpa only [stage7Part5Model,v17,v18,v19,v20] using stage7Part5_run ({s with memory := s.memory}) w11 w8 v16 v12 w7 w0 w1 w2 w3 w4 w5 w6 v0 w8 w9 w10 w11 w12 w13 w14 w15 rest hcap hact
  have h6 : runInstructions stage7Part6Program {s with pc := N 4360,memory := s.memory,stack := v20::v19::w8::v18::v12::w7::w0::w1::w2::w3::w4::w5::w6::v0::w8::w9::w10::w11::w12::w13::w14::w15::rest} = some {s with pc := N 4368,memory := s.memory,stack := v0::w9::v24::w7::v23::w1::w2::w3::w4::w5::w6::v0::w8::w9::w10::w11::w12::w13::w14::w15::rest} := by
    simpa only [stage7Part6Model,v21,v22,v23,v24] using stage7Part6_run ({s with memory := s.memory}) v20 v19 w8 v18 v12 w7 w0 w1 w2 w3 w4 w5 w6 v0 w8 w9 w10 w11 w12 w13 w14 w15 rest hcap hact
  have h7 : runInstructions stage7Part7Program {s with pc := N 4368,memory := s.memory,stack := v0::w9::v24::w7::v23::w1::w2::w3::w4::w5::w6::v0::w8::w9::w10::w11::w12::w13::w14::w15::rest} = some {s with pc := N 4375,memory := s.memory,stack := w6::v28::w7::v23::w1::w2::w3::w4::w5::w6::v0::w8::w9::w10::w11::w12::w13::w14::w15::rest} := by
    simpa only [stage7Part7Model,v25,v26,v27,v28] using stage7Part7_run ({s with memory := s.memory}) v0 w9 v24 w7 v23 w1 w2 w3 w4 w5 w6 v0 w8 w9 w10 w11 w12 w13 w14 w15 rest hcap hact
  have h8 : runInstructions stage7Part8Program {s with pc := N 4375,memory := s.memory,stack := w6::v28::w7::v23::w1::w2::w3::w4::w5::w6::v0::w8::w9::w10::w11::w12::w13::w14::w15::rest} = some {s with pc := N 4384,memory := s.memory,stack := v33::v31::w7::v23::w1::w2::w3::w4::w5::w6::v0::w8::w9::w10::w11::w12::w13::w14::w15::rest} := by
    simpa only [stage7Part8Model,v29,v30,v31,v32,v33] using stage7Part8_run ({s with memory := s.memory}) w6 v28 w7 v23 w1 w2 w3 w4 w5 w6 v0 w8 w9 w10 w11 w12 w13 w14 w15 rest hcap hact
  have h9 : runInstructions stage7Part9Program {s with pc := N 4384,memory := s.memory,stack := v33::v31::w7::v23::w1::w2::w3::w4::w5::w6::v0::w8::w9::w10::w11::w12::w13::w14::w15::rest} = some {s with pc := N 4392,memory := s.memory,stack := w1::v37::w7::v23::w1::w2::w3::w4::w5::w6::v0::w8::w9::w10::w11::w12::w13::w14::w15::rest} := by
    simpa only [stage7Part9Model,v34,v35,v36,v37] using stage7Part9_run ({s with memory := s.memory}) v33 v31 w7 v23 w1 w2 w3 w4 w5 w6 v0 w8 w9 w10 w11 w12 w13 w14 w15 rest hcap hact
  have h10 : runInstructions stage7Part10Program {s with pc := N 4392,memory := s.memory,stack := w1::v37::w7::v23::w1::w2::w3::w4::w5::w6::v0::w8::w9::w10::w11::w12::w13::w14::w15::rest} = some {s with pc := N 4404,memory := s.memory,stack := v42::v40::w7::v23::w1::w2::w3::w4::w5::w6::v0::w8::w9::w10::w11::w12::w13::w14::w15::rest} := by
    simpa only [stage7Part10Model,v38,v39,v40,v41,v42] using stage7Part10_run ({s with memory := s.memory}) w1 v37 w7 v23 w1 w2 w3 w4 w5 w6 v0 w8 w9 w10 w11 w12 w13 w14 w15 rest hcap hact
  have h11 : runInstructions stage7Part11Program {s with pc := N 4404,memory := s.memory,stack := v42::v40::w7::v23::w1::w2::w3::w4::w5::w6::v0::w8::w9::w10::w11::w12::w13::w14::w15::rest} = some {s with pc := N 4412,memory := s.memory,stack := w8::v45::w7::v43::w1::w2::w3::w4::w5::w6::v0::w8::w9::w10::w11::w12::w13::w14::w15::rest} := by
    simpa only [stage7Part11Model,v43,v44,v45] using stage7Part11_run ({s with memory := s.memory}) v42 v40 w7 v23 w1 w2 w3 w4 w5 w6 v0 w8 w9 w10 w11 w12 w13 w14 w15 rest hcap hact
  have h12 : runInstructions stage7Part12Program {s with pc := N 4412,memory := s.memory,stack := w8::v45::w7::v43::w1::w2::w3::w4::w5::w6::v0::w8::w9::w10::w11::w12::w13::w14::w15::rest} = some {s with pc := N 4422,memory := v48,stack := w8::v47::v43::w1::w2::w3::w4::w5::w6::v0::w8::w9::w10::w11::w12::w13::w14::w15::rest} := by
    simpa only [stage7Part12Model,v46,v47,v48] using stage7Part12_run ({s with memory := s.memory}) w8 v45 w7 v43 w1 w2 w3 w4 w5 w6 v0 w8 w9 w10 w11 w12 w13 w14 w15 rest hcap hact
  have h13 : runInstructions stage7Part13Program {s with pc := N 4422,memory := v48,stack := w8::v47::v43::w1::w2::w3::w4::w5::w6::v0::w8::w9::w10::w11::w12::w13::w14::w15::rest} = some {s with pc := N 4430,memory := v48,stack := w3::w8::v51::v43::w1::w2::w3::w4::w5::w6::v0::w8::w9::w10::w11::w12::w13::w14::w15::rest} := by
    simpa only [stage7Part13Model,v49,v50,v51] using stage7Part13_run ({s with memory := v48}) w8 v47 v43 w1 w2 w3 w4 w5 w6 v0 w8 w9 w10 w11 w12 w13 w14 w15 rest hcap hact
  have h14 : runInstructions stage7Part14Program {s with pc := N 4430,memory := v48,stack := w3::w8::v51::v43::w1::w2::w3::w4::w5::w6::v0::w8::w9::w10::w11::w12::w13::w14::w15::rest} = some {s with pc := N 4439,memory := v48,stack := v55::w13::w8::v54::v43::w1::w2::w3::w4::w5::w6::v0::w8::w9::w10::w11::w12::w13::w14::w15::rest} := by
    simpa only [stage7Part14Model,v52,v53,v54,v55] using stage7Part14_run ({s with memory := v48}) w3 w8 v51 v43 w1 w2 w3 w4 w5 w6 v0 w8 w9 w10 w11 w12 w13 w14 w15 rest hcap hact
  have h15 : runInstructions stage7Part15Program {s with pc := N 4439,memory := v48,stack := v55::w13::w8::v54::v43::w1::w2::w3::w4::w5::w6::v0::w8::w9::w10::w11::w12::w13::w14::w15::rest} = some {s with pc := N 4449,memory := v48,stack := v60::v43::w1::w2::w3::w4::w5::w6::v0::w8::w9::w10::w11::w12::w13::w14::w15::rest} := by
    simpa only [stage7Part15Model,v56,v57,v58,v59,v60] using stage7Part15_run ({s with memory := v48}) v55 w13 w8 v54 v43 w1 w2 w3 w4 w5 w6 v0 w8 w9 w10 w11 w12 w13 w14 w15 rest hcap hact
  have h16 : runInstructions stage7Part16Program {s with pc := N 4449,memory := v48,stack := v60::v43::w1::w2::w3::w4::w5::w6::v0::w8::w9::w10::w11::w12::w13::w14::w15::rest} = some {s with pc := N 4459,memory := v48,stack := w12::w8::v63::v43::w1::w2::w3::w4::w5::w6::v0::w8::w9::w10::w11::w12::w13::w14::w15::rest} := by
    simpa only [stage7Part16Model,v61,v62,v63] using stage7Part16_run ({s with memory := v48}) v60 v43 w1 w2 w3 w4 w5 w6 v0 w8 w9 w10 w11 w12 w13 w14 w15 rest hcap hact
  have h17 : runInstructions stage7Part17Program {s with pc := N 4459,memory := v48,stack := w12::w8::v63::v43::w1::w2::w3::w4::w5::w6::v0::w8::w9::w10::w11::w12::w13::w14::w15::rest} = some {s with pc := N 4499,memory := v48,stack := v66::v66::w12::w8::v63::w8::w1::w2::w3::w4::w5::w6::v0::w8::w9::w10::w11::w12::w13::w14::w15::rest} := by
    simpa only [stage7Part17Model,v64,v65,v66] using stage7Part17_run ({s with memory := v48}) w12 w8 v63 v43 w1 w2 w3 w4 w5 w6 v0 w8 w9 w10 w11 w12 w13 w14 w15 rest hcap hact
  have h18 : runInstructions stage7Part18Program {s with pc := N 4499,memory := v48,stack := v66::v66::w12::w8::v63::w8::w1::w2::w3::w4::w5::w6::v0::w8::w9::w10::w11::w12::w13::w14::w15::rest} = some {s with pc := N 4509,memory := v67,stack := v70::w1::w2::w3::w4::w5::w6::v0::w8::w9::w10::w11::w12::w13::w14::w15::rest} := by
    simpa only [stage7Part18Model,v67,v68,v69,v70] using stage7Part18_run ({s with memory := v48}) v66 v66 w12 w8 v63 w8 w1 w2 w3 w4 w5 w6 v0 w8 w9 w10 w11 w12 w13 w14 w15 rest hcap hact
  exact (runInstructions_append_some _ _ _ _ _ h0 (runInstructions_append_some _ _ _ _ _ h1 (runInstructions_append_some _ _ _ _ _ h2 (runInstructions_append_some _ _ _ _ _ h3 (runInstructions_append_some _ _ _ _ _ h4 (runInstructions_append_some _ _ _ _ _ h5 (runInstructions_append_some _ _ _ _ _ h6 (runInstructions_append_some _ _ _ _ _ h7 (runInstructions_append_some _ _ _ _ _ h8 (runInstructions_append_some _ _ _ _ _ h9 (runInstructions_append_some _ _ _ _ _ h10 (runInstructions_append_some _ _ _ _ _ h11 (runInstructions_append_some _ _ _ _ _ h12 (runInstructions_append_some _ _ _ _ _ h13 (runInstructions_append_some _ _ _ _ _ h14 (runInstructions_append_some _ _ _ _ _ h15 (runInstructions_append_some _ _ _ _ _ h16 (runInstructions_append_some _ _ _ _ _ h17 h18))))))))))))))))))
end R9InvConsumeExec
