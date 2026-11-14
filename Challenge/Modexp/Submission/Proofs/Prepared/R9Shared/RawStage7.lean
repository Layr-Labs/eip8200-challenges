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
def stage7Part0Program : List Instr := [.push 2 1568,.op .MLOAD,.op (.Swap sA7),.op (.Dup dA15),.op (.Dup dA10),.push 2 768,.op .MLOAD]
def stage7Part0Model (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 : W) (rest : List W) : State :=
  let v0 : W := MachineState.readWord (s.memory) 1568
  let v1 : W := MachineState.readWord (s.memory) 768
  {s with pc := N 4301,memory := s.memory,stack := v1::w8::w14::w7::w0::w1::w2::w3::w4::w5::w6::v0::w8::w9::w10::w11::w12::w13::w14::w15::rest}
theorem stage7Part0_run (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions stage7Part0Program {s with pc := N 4290,memory := s.memory,stack := w0::w1::w2::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::rest} = some (stage7Part0Model s w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 63) : rest.length+j < 1024 := by omega
  have ha768 : (768 : W).toNat = 768 := rfl
  have hf768 := Monpro.activeWords_fix s 768 32 (by decide) (by norm_num) hact
  have ha1568 : (1568 : W).toNat = 1568 := rfl
  have hf1568 := Monpro.activeWords_fix s 1568 32 (by decide) (by norm_num) hact
  simp [hz,hzn,stage7Part0Program,stage7Part0Model,runInstructions,runInstr,List.exchange,succ_ofNat_mod,ofNat_add_mod,Nat.add_assoc,State.activeWordsAfterUInt256,literal_eq_ofNat,capacity,ha768,hf768,ha1568,hf1568]
def stage7Part1Program : List Instr := [.op (.Dup dA15),.op (.Dup dA1),.op (.Dup dA4),.op .MUL,.op (.Dup dA10),.push 1 128,.op .MLOAD,.op .MUL,.op .ADD]
def stage7Part1Model (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 : W) (rest : List W) : State :=
  let v0 : W := w2 * w0
  let v1 : W := MachineState.readWord (s.memory) 128
  let v2 : W := v1 * w8
  let v3 : W := v2 + v0
  {s with pc := N 4311,memory := s.memory,stack := v3::w15::w0::w1::w2::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::w16::w17::w18::w19::rest}
theorem stage7Part1_run (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions stage7Part1Program {s with pc := N 4301,memory := s.memory,stack := w0::w1::w2::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::w16::w17::w18::w19::rest} = some (stage7Part1Model s w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 63) : rest.length+j < 1024 := by omega
  have ha128 : (128 : W).toNat = 128 := rfl
  have hf128 := Monpro.activeWords_fix s 128 32 (by decide) (by norm_num) hact
  simp [hz,hzn,stage7Part1Program,stage7Part1Model,runInstructions,runInstr,List.exchange,succ_ofNat_mod,ofNat_add_mod,Nat.add_assoc,State.activeWordsAfterUInt256,literal_eq_ofNat,capacity,ha128,hf128]
def stage7Part2Program : List Instr := [.op (.Swap sA0),.op (.Dup dA11),.op .MUL,.op .ADD,.push 1 64,.op .MLOAD]
def stage7Part2Model (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 w20 w21 : W) (rest : List W) : State :=
  let v0 : W := w11 * w1
  let v1 : W := v0 + w0
  let v2 : W := MachineState.readWord (s.memory) 64
  {s with pc := N 4318,memory := s.memory,stack := v2::v1::w2::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::w16::w17::w18::w19::w20::w21::rest}
theorem stage7Part2_run (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 w20 w21 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions stage7Part2Program {s with pc := N 4311,memory := s.memory,stack := w0::w1::w2::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::w16::w17::w18::w19::w20::w21::rest} = some (stage7Part2Model s w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 w20 w21 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 63) : rest.length+j < 1024 := by omega
  have ha64 : (64 : W).toNat = 64 := rfl
  have hf64 := Monpro.activeWords_fix s 64 32 (by decide) (by norm_num) hact
  simp [hz,hzn,stage7Part2Program,stage7Part2Model,runInstructions,runInstr,List.exchange,succ_ofNat_mod,ofNat_add_mod,Nat.add_assoc,State.activeWordsAfterUInt256,literal_eq_ofNat,capacity,ha64,hf64]
def stage7Part3Program : List Instr := [.push 1 32,.op .MLOAD,.op .MUL,.op .ADD,.op (.Swap sA2),.op .MULMOD,.op (.Dup dA11)]
def stage7Part3Model (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 w20 w21 : W) (rest : List W) : State :=
  let v0 : W := MachineState.readWord (s.memory) 32
  let v1 : W := v0 * w0
  let v2 : W := v1 + w1
  let v3 : W := UInt256.mulMod w4 w2 w3
  {s with pc := N 4326,memory := s.memory,stack := w14::v3::v2::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::w16::w17::w18::w19::w20::w21::rest}
theorem stage7Part3_run (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 w20 w21 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions stage7Part3Program {s with pc := N 4318,memory := s.memory,stack := w0::w1::w2::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::w16::w17::w18::w19::w20::w21::rest} = some (stage7Part3Model s w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 w20 w21 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 63) : rest.length+j < 1024 := by omega
  have ha32 : (32 : W).toNat = 32 := rfl
  have hf32 := Monpro.activeWords_fix s 32 32 (by decide) (by norm_num) hact
  simp [hz,hzn,stage7Part3Program,stage7Part3Model,runInstructions,runInstr,List.exchange,succ_ofNat_mod,ofNat_add_mod,Nat.add_assoc,State.activeWordsAfterUInt256,literal_eq_ofNat,capacity,ha32,hf32]
def stage7Part4Program : List Instr := [.push 1 128,.op .MLOAD,.op (.Dup dA9),.op .MULMOD,.op .ADD,.op (.Dup dA11),.op (.Dup dA15)]
def stage7Part4Model (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 : W) (rest : List W) : State :=
  let v0 : W := MachineState.readWord (s.memory) 128
  let v1 : W := UInt256.mulMod w8 v0 w0
  let v2 : W := v1 + w1
  {s with pc := N 4334,memory := s.memory,stack := w15::w12::v2::w2::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::w16::w17::w18::w19::rest}
theorem stage7Part4_run (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions stage7Part4Program {s with pc := N 4326,memory := s.memory,stack := w0::w1::w2::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::w16::w17::w18::w19::rest} = some (stage7Part4Model s w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 63) : rest.length+j < 1024 := by omega
  have ha128 : (128 : W).toNat = 128 := rfl
  have hf128 := Monpro.activeWords_fix s 128 32 (by decide) (by norm_num) hact
  simp [hz,hzn,stage7Part4Program,stage7Part4Model,runInstructions,runInstr,List.exchange,succ_ofNat_mod,ofNat_add_mod,Nat.add_assoc,State.activeWordsAfterUInt256,literal_eq_ofNat,capacity,ha128,hf128]
def stage7Part5Program : List Instr := [.op (.Dup dA10),.op .MULMOD,.op .ADD,.op (.Dup dA11),.push 1 64,.op .MLOAD,.push 1 32,.op .MLOAD]
def stage7Part5Model (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 w20 : W) (rest : List W) : State :=
  let v0 : W := UInt256.mulMod w10 w0 w1
  let v1 : W := v0 + w2
  let v2 : W := MachineState.readWord (s.memory) 64
  let v3 : W := MachineState.readWord (s.memory) 32
  {s with pc := N 4344,memory := s.memory,stack := v3::v2::w13::v1::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::w16::w17::w18::w19::w20::rest}
theorem stage7Part5_run (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 w20 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions stage7Part5Program {s with pc := N 4334,memory := s.memory,stack := w0::w1::w2::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::w16::w17::w18::w19::w20::rest} = some (stage7Part5Model s w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 w20 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 63) : rest.length+j < 1024 := by omega
  have ha32 : (32 : W).toNat = 32 := rfl
  have hf32 := Monpro.activeWords_fix s 32 32 (by decide) (by norm_num) hact
  have ha64 : (64 : W).toNat = 64 := rfl
  have hf64 := Monpro.activeWords_fix s 64 32 (by decide) (by norm_num) hact
  simp [hz,hzn,stage7Part5Program,stage7Part5Model,runInstructions,runInstr,List.exchange,succ_ofNat_mod,ofNat_add_mod,Nat.add_assoc,State.activeWordsAfterUInt256,literal_eq_ofNat,capacity,ha32,hf32,ha64,hf64]
def stage7Part6Program : List Instr := [.op .MULMOD,.op .ADD,.op (.Dup dA3),.op .ADD,.op (.Swap sA2),.op .ADD,.op (.Dup dA11),.op (.Dup dA10)]
def stage7Part6Model (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 w20 w21 : W) (rest : List W) : State :=
  let v0 : W := UInt256.mulMod w0 w1 w2
  let v1 : W := v0 + w3
  let v2 : W := w6 + v1
  let v3 : W := w6 + w4
  {s with pc := N 4352,memory := s.memory,stack := w13::w15::v3::w5::v2::w7::w8::w9::w10::w11::w12::w13::w14::w15::w16::w17::w18::w19::w20::w21::rest}
theorem stage7Part6_run (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 w20 w21 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions stage7Part6Program {s with pc := N 4344,memory := s.memory,stack := w0::w1::w2::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::w16::w17::w18::w19::w20::w21::rest} = some (stage7Part6Model s w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 w20 w21 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 63) : rest.length+j < 1024 := by omega
  simp [hz,hzn,stage7Part6Program,stage7Part6Model,runInstructions,runInstr,List.exchange,succ_ofNat_mod,ofNat_add_mod,Nat.add_assoc,State.activeWordsAfterUInt256,literal_eq_ofNat,capacity]
def stage7Part7Program : List Instr := [.op .MUL,.op .ADD,.op (.Dup dA4),.op (.Dup dA2),.op .MUL,.op .ADD,.op (.Dup dA8)]
def stage7Part7Model (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 : W) (rest : List W) : State :=
  let v0 : W := w0 * w1
  let v1 : W := v0 + w2
  let v2 : W := w3 * w6
  let v3 : W := v2 + v1
  {s with pc := N 4359,memory := s.memory,stack := w10::v3::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::w16::w17::w18::w19::rest}
theorem stage7Part7_run (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions stage7Part7Program {s with pc := N 4352,memory := s.memory,stack := w0::w1::w2::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::w16::w17::w18::w19::rest} = some (stage7Part7Model s w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 63) : rest.length+j < 1024 := by omega
  simp [hz,hzn,stage7Part7Program,stage7Part7Model,runInstructions,runInstr,List.exchange,succ_ofNat_mod,ofNat_add_mod,Nat.add_assoc,State.activeWordsAfterUInt256,literal_eq_ofNat,capacity]
def stage7Part8Program : List Instr := [.push 1 192,.op .MLOAD,.op .MUL,.op .ADD,.op (.Dup dA5),.push 0 0,.op .MLOAD,.op .MUL]
def stage7Part8Model (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 : W) (rest : List W) : State :=
  let v0 : W := MachineState.readWord (s.memory) 192
  let v1 : W := v0 * w0
  let v2 : W := v1 + w1
  let v3 : W := MachineState.readWord (s.memory) 0
  let v4 : W := v3 * w6
  {s with pc := N 4368,memory := s.memory,stack := v4::v2::w2::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::w16::w17::w18::rest}
theorem stage7Part8_run (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions stage7Part8Program {s with pc := N 4359,memory := s.memory,stack := w0::w1::w2::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::w16::w17::w18::rest} = some (stage7Part8Model s w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 63) : rest.length+j < 1024 := by omega
  have ha0 : (0 : W).toNat = 0 := rfl
  have hf0 := Monpro.activeWords_fix s 0 32 (by decide) (by norm_num) hact
  have ha192 : (192 : W).toNat = 192 := rfl
  have hf192 := Monpro.activeWords_fix s 192 32 (by decide) (by norm_num) hact
  simp [hz,hzn,stage7Part8Program,stage7Part8Model,runInstructions,runInstr,List.exchange,succ_ofNat_mod,ofNat_add_mod,Nat.add_assoc,State.activeWordsAfterUInt256,literal_eq_ofNat,capacity,ha0,hf0,ha192,hf192]
def stage7Part9Program : List Instr := [.op .ADD,.op (.Dup dA15),.push 1 224,.op .MLOAD,.op .MUL,.op .ADD,.op (.Dup dA3)]
def stage7Part9Model (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 : W) (rest : List W) : State :=
  let v0 : W := w0 + w1
  let v1 : W := MachineState.readWord (s.memory) 224
  let v2 : W := v1 * w16
  let v3 : W := v2 + v0
  {s with pc := N 4376,memory := s.memory,stack := w4::v3::w2::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::w16::w17::w18::rest}
theorem stage7Part9_run (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions stage7Part9Program {s with pc := N 4368,memory := s.memory,stack := w0::w1::w2::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::w16::w17::w18::rest} = some (stage7Part9Model s w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 63) : rest.length+j < 1024 := by omega
  have ha224 : (224 : W).toNat = 224 := rfl
  have hf224 := Monpro.activeWords_fix s 224 32 (by decide) (by norm_num) hact
  simp [hz,hzn,stage7Part9Program,stage7Part9Model,runInstructions,runInstr,List.exchange,succ_ofNat_mod,ofNat_add_mod,Nat.add_assoc,State.activeWordsAfterUInt256,literal_eq_ofNat,capacity,ha224,hf224]
def stage7Part10Program : List Instr := [.push 2 1216,.op .MLOAD,.op .MUL,.op .ADD,.op (.Dup dA12),.push 2 1248,.op .MLOAD,.op .MUL]
def stage7Part10Model (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 : W) (rest : List W) : State :=
  let v0 : W := MachineState.readWord (s.memory) 1216
  let v1 : W := v0 * w0
  let v2 : W := v1 + w1
  let v3 : W := MachineState.readWord (s.memory) 1248
  let v4 : W := v3 * w13
  {s with pc := N 4388,memory := s.memory,stack := v4::v2::w2::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::w16::w17::w18::rest}
theorem stage7Part10_run (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions stage7Part10Program {s with pc := N 4376,memory := s.memory,stack := w0::w1::w2::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::w16::w17::w18::rest} = some (stage7Part10Model s w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 63) : rest.length+j < 1024 := by omega
  have ha1216 : (1216 : W).toNat = 1216 := rfl
  have hf1216 := Monpro.activeWords_fix s 1216 32 (by decide) (by norm_num) hact
  have ha1248 : (1248 : W).toNat = 1248 := rfl
  have hf1248 := Monpro.activeWords_fix s 1248 32 (by decide) (by norm_num) hact
  simp [hz,hzn,stage7Part10Program,stage7Part10Model,runInstructions,runInstr,List.exchange,succ_ofNat_mod,ofNat_add_mod,Nat.add_assoc,State.activeWordsAfterUInt256,literal_eq_ofNat,capacity,ha1216,hf1216,ha1248,hf1248]
def stage7Part11Program : List Instr := [.op .ADD,.op (.Swap sA1),.op (.Dup dA10),.op (.Dup dA12),.op (.Dup dA11),.op .MULMOD,.op .ADD,.op (.Dup dA10)]
def stage7Part11Model (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 : W) (rest : List W) : State :=
  let v0 : W := w0 + w1
  let v1 : W := UInt256.mulMod w10 w12 w11
  let v2 : W := v1 + w3
  {s with pc := N 4396,memory := s.memory,stack := w11::v2::w2::v0::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::w16::w17::w18::rest}
theorem stage7Part11_run (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions stage7Part11Program {s with pc := N 4388,memory := s.memory,stack := w0::w1::w2::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::w16::w17::w18::rest} = some (stage7Part11Model s w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 63) : rest.length+j < 1024 := by omega
  simp [hz,hzn,stage7Part11Program,stage7Part11Model,runInstructions,runInstr,List.exchange,succ_ofNat_mod,ofNat_add_mod,Nat.add_assoc,State.activeWordsAfterUInt256,literal_eq_ofNat,capacity]
def stage7Part12Program : List Instr := [.op (.Dup dA5),.op (.Dup dA3),.op .MULMOD,.op .ADD,.op (.Swap sA0),.push 2 1088,.op .MSTORE,.op (.Dup dA9)]
def stage7Part12Model (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 : W) (rest : List W) : State :=
  let v0 : W := UInt256.mulMod w2 w5 w0
  let v1 : W := v0 + w1
  let v2 : ByteArray := MachineState.writeBytes (s.memory) (Data.Bytes.natToBytesPadded w2.toNat 32) 1088
  {s with pc := N 4406,memory := v2,stack := w11::v1::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::w16::w17::w18::rest}
theorem stage7Part12_run (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions stage7Part12Program {s with pc := N 4396,memory := s.memory,stack := w0::w1::w2::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::w16::w17::w18::rest} = some (stage7Part12Model s w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 63) : rest.length+j < 1024 := by omega
  have ha1088 : (1088 : W).toNat = 1088 := rfl
  have hf1088 := Monpro.activeWords_fix s 1088 32 (by decide) (by norm_num) hact
  simp [hz,hzn,stage7Part12Program,stage7Part12Model,runInstructions,runInstr,List.exchange,succ_ofNat_mod,ofNat_add_mod,Nat.add_assoc,State.activeWordsAfterUInt256,literal_eq_ofNat,capacity,ha1088,hf1088]
def stage7Part13Program : List Instr := [.op (.Dup dA8),.push 1 192,.op .MLOAD,.op .MULMOD,.op .ADD,.op (.Dup dA9),.op (.Dup dA5)]
def stage7Part13Model (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 : W) (rest : List W) : State :=
  let v0 : W := MachineState.readWord (s.memory) 192
  let v1 : W := UInt256.mulMod v0 w8 w0
  let v2 : W := v1 + w1
  {s with pc := N 4414,memory := s.memory,stack := w5::w10::v2::w2::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::w16::w17::rest}
theorem stage7Part13_run (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions stage7Part13Program {s with pc := N 4406,memory := s.memory,stack := w0::w1::w2::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::w16::w17::rest} = some (stage7Part13Model s w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 63) : rest.length+j < 1024 := by omega
  have ha192 : (192 : W).toNat = 192 := rfl
  have hf192 := Monpro.activeWords_fix s 192 32 (by decide) (by norm_num) hact
  simp [hz,hzn,stage7Part13Program,stage7Part13Model,runInstructions,runInstr,List.exchange,succ_ofNat_mod,ofNat_add_mod,Nat.add_assoc,State.activeWordsAfterUInt256,literal_eq_ofNat,capacity,ha192,hf192]
def stage7Part14Program : List Instr := [.push 0 0,.op .MLOAD,.op .MULMOD,.op .ADD,.op (.Dup dA9),.op (.Dup dA15),.push 1 224,.op .MLOAD]
def stage7Part14Model (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 : W) (rest : List W) : State :=
  let v0 : W := MachineState.readWord (s.memory) 0
  let v1 : W := UInt256.mulMod v0 w0 w1
  let v2 : W := v1 + w2
  let v3 : W := MachineState.readWord (s.memory) 224
  {s with pc := N 4423,memory := s.memory,stack := v3::w16::w11::v2::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::w16::w17::w18::rest}
theorem stage7Part14_run (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions stage7Part14Program {s with pc := N 4414,memory := s.memory,stack := w0::w1::w2::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::w16::w17::w18::rest} = some (stage7Part14Model s w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 63) : rest.length+j < 1024 := by omega
  have ha0 : (0 : W).toNat = 0 := rfl
  have hf0 := Monpro.activeWords_fix s 0 32 (by decide) (by norm_num) hact
  have ha224 : (224 : W).toNat = 224 := rfl
  have hf224 := Monpro.activeWords_fix s 224 32 (by decide) (by norm_num) hact
  simp [hz,hzn,stage7Part14Program,stage7Part14Model,runInstructions,runInstr,List.exchange,succ_ofNat_mod,ofNat_add_mod,Nat.add_assoc,State.activeWordsAfterUInt256,literal_eq_ofNat,capacity,ha0,hf0,ha224,hf224]
def stage7Part15Program : List Instr := [.op .MULMOD,.op .ADD,.op (.Dup dA9),.op (.Dup dA3),.push 2 1216,.op .MLOAD,.op .MULMOD,.op .ADD]
def stage7Part15Model (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 : W) (rest : List W) : State :=
  let v0 : W := UInt256.mulMod w0 w1 w2
  let v1 : W := v0 + w3
  let v2 : W := MachineState.readWord (s.memory) 1216
  let v3 : W := UInt256.mulMod v2 w5 w12
  let v4 : W := v3 + v1
  {s with pc := N 4433,memory := s.memory,stack := v4::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::w16::w17::w18::w19::rest}
theorem stage7Part15_run (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions stage7Part15Program {s with pc := N 4423,memory := s.memory,stack := w0::w1::w2::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::w16::w17::w18::w19::rest} = some (stage7Part15Model s w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 63) : rest.length+j < 1024 := by omega
  have ha1216 : (1216 : W).toNat = 1216 := rfl
  have hf1216 := Monpro.activeWords_fix s 1216 32 (by decide) (by norm_num) hact
  simp [hz,hzn,stage7Part15Program,stage7Part15Model,runInstructions,runInstr,List.exchange,succ_ofNat_mod,ofNat_add_mod,Nat.add_assoc,State.activeWordsAfterUInt256,literal_eq_ofNat,capacity,ha1216,hf1216]
def stage7Part16Program : List Instr := [.op (.Dup dA9),.op (.Dup dA12),.push 2 1248,.op .MLOAD,.op .MULMOD,.op .ADD,.op (.Dup dA9),.op (.Dup dA14)]
def stage7Part16Model (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 : W) (rest : List W) : State :=
  let v0 : W := MachineState.readWord (s.memory) 1248
  let v1 : W := UInt256.mulMod v0 w11 w9
  let v2 : W := v1 + w0
  {s with pc := N 4443,memory := s.memory,stack := w13::w9::v2::w1::w2::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::w16::rest}
theorem stage7Part16_run (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions stage7Part16Program {s with pc := N 4433,memory := s.memory,stack := w0::w1::w2::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::w16::rest} = some (stage7Part16Model s w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 63) : rest.length+j < 1024 := by omega
  have ha1248 : (1248 : W).toNat = 1248 := rfl
  have hf1248 := Monpro.activeWords_fix s 1248 32 (by decide) (by norm_num) hact
  simp [hz,hzn,stage7Part16Program,stage7Part16Model,runInstructions,runInstr,List.exchange,succ_ofNat_mod,ofNat_add_mod,Nat.add_assoc,State.activeWordsAfterUInt256,literal_eq_ofNat,capacity,ha1248,hf1248]
def stage7Part17Program : List Instr := [.push 2 2720,.op .MLOAD,.op (.Dup dA2),.op (.Swap sA4),.op .MUL,.push 30 1766847064778384329583297500742918515827483896875618958121606201292619775,.op .AND,.op (.Dup dA0)]
def stage7Part17Model (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 : W) (rest : List W) : State :=
  let v0 : W := MachineState.readWord (s.memory) 2720
  let v1 : W := w3 * v0
  let v2 : W := UInt256.land (N 1766847064778384329583297500742918515827483896875618958121606201292619775) v1
  {s with pc := N 4483,memory := s.memory,stack := v2::v2::w0::w1::w2::w1::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::w16::w17::w18::rest}
theorem stage7Part17_run (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions stage7Part17Program {s with pc := N 4443,memory := s.memory,stack := w0::w1::w2::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::w16::w17::w18::rest} = some (stage7Part17Model s w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 63) : rest.length+j < 1024 := by omega
  have ha2720 : (2720 : W).toNat = 2720 := rfl
  have hf2720 := Monpro.activeWords_fix s 2720 32 (by decide) (by norm_num) hact
  simp [hz,hzn,stage7Part17Program,stage7Part17Model,runInstructions,runInstr,List.exchange,succ_ofNat_mod,ofNat_add_mod,Nat.add_assoc,State.activeWordsAfterUInt256,literal_eq_ofNat,capacity,ha2720,hf2720]
def stage7Part18Program : List Instr := [.push 2 1280,.op .MSTORE,.op .MULMOD,.op .ADD,.push 2 2048,.op .MULMOD]
def stage7Part18Model (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 w20 : W) (rest : List W) : State :=
  let v0 : ByteArray := MachineState.writeBytes (s.memory) (Data.Bytes.natToBytesPadded w0.toNat 32) 1280
  let v1 : W := UInt256.mulMod w1 w2 w3
  let v2 : W := v1 + w4
  let v3 : W := UInt256.mulMod (N 2048) v2 w5
  {s with pc := N 4493,memory := v0,stack := v3::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::w16::w17::w18::w19::w20::rest}
theorem stage7Part18_run (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 w20 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions stage7Part18Program {s with pc := N 4483,memory := s.memory,stack := w0::w1::w2::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::w16::w17::w18::w19::w20::rest} = some (stage7Part18Model s w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 w20 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 63) : rest.length+j < 1024 := by omega
  have ha1280 : (1280 : W).toNat = 1280 := rfl
  have hf1280 := Monpro.activeWords_fix s 1280 32 (by decide) (by norm_num) hact
  have ha2048 : (2048 : W).toNat = 2048 := rfl
  have hf2048 := Monpro.activeWords_fix s 2048 32 (by decide) (by norm_num) hact
  simp [hz,hzn,stage7Part18Program,stage7Part18Model,runInstructions,runInstr,List.exchange,succ_ofNat_mod,ofNat_add_mod,Nat.add_assoc,State.activeWordsAfterUInt256,literal_eq_ofNat,capacity,ha1280,hf1280,ha2048,hf2048]
def stage7Program : List Instr := (stage7Part0Program++(stage7Part1Program++(stage7Part2Program++(stage7Part3Program++(stage7Part4Program++(stage7Part5Program++(stage7Part6Program++(stage7Part7Program++(stage7Part8Program++(stage7Part9Program++(stage7Part10Program++(stage7Part11Program++(stage7Part12Program++(stage7Part13Program++(stage7Part14Program++(stage7Part15Program++(stage7Part16Program++(stage7Part17Program++stage7Part18Program))))))))))))))))))
def stage7Model (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 : W) (rest : List W) : State :=
  let v0 : W := MachineState.readWord (s.memory) 1568
  let v1 : W := MachineState.readWord (s.memory) 768
  let v2 : W := w14 * v1
  let v3 : W := MachineState.readWord (s.memory) 128
  let v4 : W := v3 * w4
  let v5 : W := v4 + v2
  let v6 : W := w5 * w11
  let v7 : W := v6 + v5
  let v8 : W := MachineState.readWord (s.memory) 64
  let v9 : W := MachineState.readWord (s.memory) 32
  let v10 : W := v9 * v8
  let v11 : W := v10 + v7
  let v12 : W := UInt256.mulMod w14 v1 w8
  let v13 : W := MachineState.readWord (s.memory) 128
  let v14 : W := UInt256.mulMod w4 v13 w8
  let v15 : W := v14 + v12
  let v16 : W := UInt256.mulMod w5 w11 w8
  let v17 : W := v16 + v15
  let v18 : W := MachineState.readWord (s.memory) 64
  let v19 : W := MachineState.readWord (s.memory) 32
  let v20 : W := UInt256.mulMod v19 v18 w8
  let v21 : W := v20 + v17
  let v22 : W := w0 + v21
  let v23 : W := w0 + v11
  let v24 : W := v0 * w9
  let v25 : W := v24 + v23
  let v26 : W := w7 * w2
  let v27 : W := v26 + v25
  let v28 : W := MachineState.readWord (s.memory) 192
  let v29 : W := v28 * w6
  let v30 : W := v29 + v27
  let v31 : W := MachineState.readWord (s.memory) 0
  let v32 : W := v31 * w3
  let v33 : W := v32 + v30
  let v34 : W := MachineState.readWord (s.memory) 224
  let v35 : W := v34 * w13
  let v36 : W := v35 + v33
  let v37 : W := MachineState.readWord (s.memory) 1216
  let v38 : W := v37 * w1
  let v39 : W := v38 + v36
  let v40 : W := MachineState.readWord (s.memory) 1248
  let v41 : W := v40 * w10
  let v42 : W := v41 + v39
  let v43 : W := UInt256.mulMod v0 w9 w8
  let v44 : W := v43 + v22
  let v45 : W := UInt256.mulMod w7 w2 w8
  let v46 : W := v45 + v44
  let v47 : ByteArray := MachineState.writeBytes (s.memory) (Data.Bytes.natToBytesPadded w7.toNat 32) 1088
  let v48 : W := MachineState.readWord v47 192
  let v49 : W := UInt256.mulMod v48 w6 w8
  let v50 : W := v49 + v46
  let v51 : W := MachineState.readWord v47 0
  let v52 : W := UInt256.mulMod v51 w3 w8
  let v53 : W := v52 + v50
  let v54 : W := MachineState.readWord v47 224
  let v55 : W := UInt256.mulMod v54 w13 w8
  let v56 : W := v55 + v53
  let v57 : W := MachineState.readWord v47 1216
  let v58 : W := UInt256.mulMod v57 w1 w8
  let v59 : W := v58 + v56
  let v60 : W := MachineState.readWord v47 1248
  let v61 : W := UInt256.mulMod v60 w10 w8
  let v62 : W := v61 + v59
  let v63 : W := MachineState.readWord v47 2720
  let v64 : W := v42 * v63
  let v65 : W := UInt256.land (N 1766847064778384329583297500742918515827483896875618958121606201292619775) v64
  let v66 : ByteArray := MachineState.writeBytes v47 (Data.Bytes.natToBytesPadded v65.toNat 32) 1280
  let v67 : W := UInt256.mulMod v65 w12 w8
  let v68 : W := v67 + v62
  let v69 : W := UInt256.mulMod (N 2048) v68 w8
  {s with pc := N 4493,memory := v66,stack := v69::w1::w2::w3::w4::w5::w6::v0::w8::w9::w10::w11::w12::w13::w14::w15::rest}
theorem stage7_run (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions stage7Program {s with pc := N 4290,memory := s.memory,stack := w0::w1::w2::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::rest} = some (stage7Model s w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 rest) := by
  let v0 : W := MachineState.readWord (s.memory) 1568
  let v1 : W := MachineState.readWord (s.memory) 768
  let v2 : W := w14 * v1
  let v3 : W := MachineState.readWord (s.memory) 128
  let v4 : W := v3 * w4
  let v5 : W := v4 + v2
  let v6 : W := w5 * w11
  let v7 : W := v6 + v5
  let v8 : W := MachineState.readWord (s.memory) 64
  let v9 : W := MachineState.readWord (s.memory) 32
  let v10 : W := v9 * v8
  let v11 : W := v10 + v7
  let v12 : W := UInt256.mulMod w14 v1 w8
  let v13 : W := MachineState.readWord (s.memory) 128
  let v14 : W := UInt256.mulMod w4 v13 w8
  let v15 : W := v14 + v12
  let v16 : W := UInt256.mulMod w5 w11 w8
  let v17 : W := v16 + v15
  let v18 : W := MachineState.readWord (s.memory) 64
  let v19 : W := MachineState.readWord (s.memory) 32
  let v20 : W := UInt256.mulMod v19 v18 w8
  let v21 : W := v20 + v17
  let v22 : W := w0 + v21
  let v23 : W := w0 + v11
  let v24 : W := v0 * w9
  let v25 : W := v24 + v23
  let v26 : W := w7 * w2
  let v27 : W := v26 + v25
  let v28 : W := MachineState.readWord (s.memory) 192
  let v29 : W := v28 * w6
  let v30 : W := v29 + v27
  let v31 : W := MachineState.readWord (s.memory) 0
  let v32 : W := v31 * w3
  let v33 : W := v32 + v30
  let v34 : W := MachineState.readWord (s.memory) 224
  let v35 : W := v34 * w13
  let v36 : W := v35 + v33
  let v37 : W := MachineState.readWord (s.memory) 1216
  let v38 : W := v37 * w1
  let v39 : W := v38 + v36
  let v40 : W := MachineState.readWord (s.memory) 1248
  let v41 : W := v40 * w10
  let v42 : W := v41 + v39
  let v43 : W := UInt256.mulMod v0 w9 w8
  let v44 : W := v43 + v22
  let v45 : W := UInt256.mulMod w7 w2 w8
  let v46 : W := v45 + v44
  let v47 : ByteArray := MachineState.writeBytes (s.memory) (Data.Bytes.natToBytesPadded w7.toNat 32) 1088
  let v48 : W := MachineState.readWord v47 192
  let v49 : W := UInt256.mulMod v48 w6 w8
  let v50 : W := v49 + v46
  let v51 : W := MachineState.readWord v47 0
  let v52 : W := UInt256.mulMod v51 w3 w8
  let v53 : W := v52 + v50
  let v54 : W := MachineState.readWord v47 224
  let v55 : W := UInt256.mulMod v54 w13 w8
  let v56 : W := v55 + v53
  let v57 : W := MachineState.readWord v47 1216
  let v58 : W := UInt256.mulMod v57 w1 w8
  let v59 : W := v58 + v56
  let v60 : W := MachineState.readWord v47 1248
  let v61 : W := UInt256.mulMod v60 w10 w8
  let v62 : W := v61 + v59
  let v63 : W := MachineState.readWord v47 2720
  let v64 : W := v42 * v63
  let v65 : W := UInt256.land (N 1766847064778384329583297500742918515827483896875618958121606201292619775) v64
  let v66 : ByteArray := MachineState.writeBytes v47 (Data.Bytes.natToBytesPadded v65.toNat 32) 1280
  let v67 : W := UInt256.mulMod v65 w12 w8
  let v68 : W := v67 + v62
  let v69 : W := UInt256.mulMod (N 2048) v68 w8
  have h0 : runInstructions stage7Part0Program {s with pc := N 4290,memory := s.memory,stack := w0::w1::w2::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::rest} = some {s with pc := N 4301,memory := s.memory,stack := v1::w8::w14::w7::w0::w1::w2::w3::w4::w5::w6::v0::w8::w9::w10::w11::w12::w13::w14::w15::rest} := by
    simpa only [stage7Part0Model,v0,v1] using stage7Part0_run ({s with memory := s.memory}) w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 rest hcap hact
  have h1 : runInstructions stage7Part1Program {s with pc := N 4301,memory := s.memory,stack := v1::w8::w14::w7::w0::w1::w2::w3::w4::w5::w6::v0::w8::w9::w10::w11::w12::w13::w14::w15::rest} = some {s with pc := N 4311,memory := s.memory,stack := v5::w11::v1::w8::w14::w7::w0::w1::w2::w3::w4::w5::w6::v0::w8::w9::w10::w11::w12::w13::w14::w15::rest} := by
    simpa only [stage7Part1Model,v2,v3,v4,v5] using stage7Part1_run ({s with memory := s.memory}) v1 w8 w14 w7 w0 w1 w2 w3 w4 w5 w6 v0 w8 w9 w10 w11 w12 w13 w14 w15 rest hcap hact
  have h2 : runInstructions stage7Part2Program {s with pc := N 4311,memory := s.memory,stack := v5::w11::v1::w8::w14::w7::w0::w1::w2::w3::w4::w5::w6::v0::w8::w9::w10::w11::w12::w13::w14::w15::rest} = some {s with pc := N 4318,memory := s.memory,stack := v8::v7::v1::w8::w14::w7::w0::w1::w2::w3::w4::w5::w6::v0::w8::w9::w10::w11::w12::w13::w14::w15::rest} := by
    simpa only [stage7Part2Model,v6,v7,v8] using stage7Part2_run ({s with memory := s.memory}) v5 w11 v1 w8 w14 w7 w0 w1 w2 w3 w4 w5 w6 v0 w8 w9 w10 w11 w12 w13 w14 w15 rest hcap hact
  have h3 : runInstructions stage7Part3Program {s with pc := N 4318,memory := s.memory,stack := v8::v7::v1::w8::w14::w7::w0::w1::w2::w3::w4::w5::w6::v0::w8::w9::w10::w11::w12::w13::w14::w15::rest} = some {s with pc := N 4326,memory := s.memory,stack := w8::v12::v11::w7::w0::w1::w2::w3::w4::w5::w6::v0::w8::w9::w10::w11::w12::w13::w14::w15::rest} := by
    simpa only [stage7Part3Model,v9,v10,v11,v12] using stage7Part3_run ({s with memory := s.memory}) v8 v7 v1 w8 w14 w7 w0 w1 w2 w3 w4 w5 w6 v0 w8 w9 w10 w11 w12 w13 w14 w15 rest hcap hact
  have h4 : runInstructions stage7Part4Program {s with pc := N 4326,memory := s.memory,stack := w8::v12::v11::w7::w0::w1::w2::w3::w4::w5::w6::v0::w8::w9::w10::w11::w12::w13::w14::w15::rest} = some {s with pc := N 4334,memory := s.memory,stack := w11::w8::v15::v11::w7::w0::w1::w2::w3::w4::w5::w6::v0::w8::w9::w10::w11::w12::w13::w14::w15::rest} := by
    simpa only [stage7Part4Model,v13,v14,v15] using stage7Part4_run ({s with memory := s.memory}) w8 v12 v11 w7 w0 w1 w2 w3 w4 w5 w6 v0 w8 w9 w10 w11 w12 w13 w14 w15 rest hcap hact
  have h5 : runInstructions stage7Part5Program {s with pc := N 4334,memory := s.memory,stack := w11::w8::v15::v11::w7::w0::w1::w2::w3::w4::w5::w6::v0::w8::w9::w10::w11::w12::w13::w14::w15::rest} = some {s with pc := N 4344,memory := s.memory,stack := v19::v18::w8::v17::v11::w7::w0::w1::w2::w3::w4::w5::w6::v0::w8::w9::w10::w11::w12::w13::w14::w15::rest} := by
    simpa only [stage7Part5Model,v16,v17,v18,v19] using stage7Part5_run ({s with memory := s.memory}) w11 w8 v15 v11 w7 w0 w1 w2 w3 w4 w5 w6 v0 w8 w9 w10 w11 w12 w13 w14 w15 rest hcap hact
  have h6 : runInstructions stage7Part6Program {s with pc := N 4344,memory := s.memory,stack := v19::v18::w8::v17::v11::w7::w0::w1::w2::w3::w4::w5::w6::v0::w8::w9::w10::w11::w12::w13::w14::w15::rest} = some {s with pc := N 4352,memory := s.memory,stack := v0::w9::v23::w7::v22::w1::w2::w3::w4::w5::w6::v0::w8::w9::w10::w11::w12::w13::w14::w15::rest} := by
    simpa only [stage7Part6Model,v20,v21,v22,v23] using stage7Part6_run ({s with memory := s.memory}) v19 v18 w8 v17 v11 w7 w0 w1 w2 w3 w4 w5 w6 v0 w8 w9 w10 w11 w12 w13 w14 w15 rest hcap hact
  have h7 : runInstructions stage7Part7Program {s with pc := N 4352,memory := s.memory,stack := v0::w9::v23::w7::v22::w1::w2::w3::w4::w5::w6::v0::w8::w9::w10::w11::w12::w13::w14::w15::rest} = some {s with pc := N 4359,memory := s.memory,stack := w6::v27::w7::v22::w1::w2::w3::w4::w5::w6::v0::w8::w9::w10::w11::w12::w13::w14::w15::rest} := by
    simpa only [stage7Part7Model,v24,v25,v26,v27] using stage7Part7_run ({s with memory := s.memory}) v0 w9 v23 w7 v22 w1 w2 w3 w4 w5 w6 v0 w8 w9 w10 w11 w12 w13 w14 w15 rest hcap hact
  have h8 : runInstructions stage7Part8Program {s with pc := N 4359,memory := s.memory,stack := w6::v27::w7::v22::w1::w2::w3::w4::w5::w6::v0::w8::w9::w10::w11::w12::w13::w14::w15::rest} = some {s with pc := N 4368,memory := s.memory,stack := v32::v30::w7::v22::w1::w2::w3::w4::w5::w6::v0::w8::w9::w10::w11::w12::w13::w14::w15::rest} := by
    simpa only [stage7Part8Model,v28,v29,v30,v31,v32] using stage7Part8_run ({s with memory := s.memory}) w6 v27 w7 v22 w1 w2 w3 w4 w5 w6 v0 w8 w9 w10 w11 w12 w13 w14 w15 rest hcap hact
  have h9 : runInstructions stage7Part9Program {s with pc := N 4368,memory := s.memory,stack := v32::v30::w7::v22::w1::w2::w3::w4::w5::w6::v0::w8::w9::w10::w11::w12::w13::w14::w15::rest} = some {s with pc := N 4376,memory := s.memory,stack := w1::v36::w7::v22::w1::w2::w3::w4::w5::w6::v0::w8::w9::w10::w11::w12::w13::w14::w15::rest} := by
    simpa only [stage7Part9Model,v33,v34,v35,v36] using stage7Part9_run ({s with memory := s.memory}) v32 v30 w7 v22 w1 w2 w3 w4 w5 w6 v0 w8 w9 w10 w11 w12 w13 w14 w15 rest hcap hact
  have h10 : runInstructions stage7Part10Program {s with pc := N 4376,memory := s.memory,stack := w1::v36::w7::v22::w1::w2::w3::w4::w5::w6::v0::w8::w9::w10::w11::w12::w13::w14::w15::rest} = some {s with pc := N 4388,memory := s.memory,stack := v41::v39::w7::v22::w1::w2::w3::w4::w5::w6::v0::w8::w9::w10::w11::w12::w13::w14::w15::rest} := by
    simpa only [stage7Part10Model,v37,v38,v39,v40,v41] using stage7Part10_run ({s with memory := s.memory}) w1 v36 w7 v22 w1 w2 w3 w4 w5 w6 v0 w8 w9 w10 w11 w12 w13 w14 w15 rest hcap hact
  have h11 : runInstructions stage7Part11Program {s with pc := N 4388,memory := s.memory,stack := v41::v39::w7::v22::w1::w2::w3::w4::w5::w6::v0::w8::w9::w10::w11::w12::w13::w14::w15::rest} = some {s with pc := N 4396,memory := s.memory,stack := w8::v44::w7::v42::w1::w2::w3::w4::w5::w6::v0::w8::w9::w10::w11::w12::w13::w14::w15::rest} := by
    simpa only [stage7Part11Model,v42,v43,v44] using stage7Part11_run ({s with memory := s.memory}) v41 v39 w7 v22 w1 w2 w3 w4 w5 w6 v0 w8 w9 w10 w11 w12 w13 w14 w15 rest hcap hact
  have h12 : runInstructions stage7Part12Program {s with pc := N 4396,memory := s.memory,stack := w8::v44::w7::v42::w1::w2::w3::w4::w5::w6::v0::w8::w9::w10::w11::w12::w13::w14::w15::rest} = some {s with pc := N 4406,memory := v47,stack := w8::v46::v42::w1::w2::w3::w4::w5::w6::v0::w8::w9::w10::w11::w12::w13::w14::w15::rest} := by
    simpa only [stage7Part12Model,v45,v46,v47] using stage7Part12_run ({s with memory := s.memory}) w8 v44 w7 v42 w1 w2 w3 w4 w5 w6 v0 w8 w9 w10 w11 w12 w13 w14 w15 rest hcap hact
  have h13 : runInstructions stage7Part13Program {s with pc := N 4406,memory := v47,stack := w8::v46::v42::w1::w2::w3::w4::w5::w6::v0::w8::w9::w10::w11::w12::w13::w14::w15::rest} = some {s with pc := N 4414,memory := v47,stack := w3::w8::v50::v42::w1::w2::w3::w4::w5::w6::v0::w8::w9::w10::w11::w12::w13::w14::w15::rest} := by
    simpa only [stage7Part13Model,v48,v49,v50] using stage7Part13_run ({s with memory := v47}) w8 v46 v42 w1 w2 w3 w4 w5 w6 v0 w8 w9 w10 w11 w12 w13 w14 w15 rest hcap hact
  have h14 : runInstructions stage7Part14Program {s with pc := N 4414,memory := v47,stack := w3::w8::v50::v42::w1::w2::w3::w4::w5::w6::v0::w8::w9::w10::w11::w12::w13::w14::w15::rest} = some {s with pc := N 4423,memory := v47,stack := v54::w13::w8::v53::v42::w1::w2::w3::w4::w5::w6::v0::w8::w9::w10::w11::w12::w13::w14::w15::rest} := by
    simpa only [stage7Part14Model,v51,v52,v53,v54] using stage7Part14_run ({s with memory := v47}) w3 w8 v50 v42 w1 w2 w3 w4 w5 w6 v0 w8 w9 w10 w11 w12 w13 w14 w15 rest hcap hact
  have h15 : runInstructions stage7Part15Program {s with pc := N 4423,memory := v47,stack := v54::w13::w8::v53::v42::w1::w2::w3::w4::w5::w6::v0::w8::w9::w10::w11::w12::w13::w14::w15::rest} = some {s with pc := N 4433,memory := v47,stack := v59::v42::w1::w2::w3::w4::w5::w6::v0::w8::w9::w10::w11::w12::w13::w14::w15::rest} := by
    simpa only [stage7Part15Model,v55,v56,v57,v58,v59] using stage7Part15_run ({s with memory := v47}) v54 w13 w8 v53 v42 w1 w2 w3 w4 w5 w6 v0 w8 w9 w10 w11 w12 w13 w14 w15 rest hcap hact
  have h16 : runInstructions stage7Part16Program {s with pc := N 4433,memory := v47,stack := v59::v42::w1::w2::w3::w4::w5::w6::v0::w8::w9::w10::w11::w12::w13::w14::w15::rest} = some {s with pc := N 4443,memory := v47,stack := w12::w8::v62::v42::w1::w2::w3::w4::w5::w6::v0::w8::w9::w10::w11::w12::w13::w14::w15::rest} := by
    simpa only [stage7Part16Model,v60,v61,v62] using stage7Part16_run ({s with memory := v47}) v59 v42 w1 w2 w3 w4 w5 w6 v0 w8 w9 w10 w11 w12 w13 w14 w15 rest hcap hact
  have h17 : runInstructions stage7Part17Program {s with pc := N 4443,memory := v47,stack := w12::w8::v62::v42::w1::w2::w3::w4::w5::w6::v0::w8::w9::w10::w11::w12::w13::w14::w15::rest} = some {s with pc := N 4483,memory := v47,stack := v65::v65::w12::w8::v62::w8::w1::w2::w3::w4::w5::w6::v0::w8::w9::w10::w11::w12::w13::w14::w15::rest} := by
    simpa only [stage7Part17Model,v63,v64,v65] using stage7Part17_run ({s with memory := v47}) w12 w8 v62 v42 w1 w2 w3 w4 w5 w6 v0 w8 w9 w10 w11 w12 w13 w14 w15 rest hcap hact
  have h18 : runInstructions stage7Part18Program {s with pc := N 4483,memory := v47,stack := v65::v65::w12::w8::v62::w8::w1::w2::w3::w4::w5::w6::v0::w8::w9::w10::w11::w12::w13::w14::w15::rest} = some {s with pc := N 4493,memory := v66,stack := v69::w1::w2::w3::w4::w5::w6::v0::w8::w9::w10::w11::w12::w13::w14::w15::rest} := by
    simpa only [stage7Part18Model,v66,v67,v68,v69] using stage7Part18_run ({s with memory := v47}) v65 v65 w12 w8 v62 w8 w1 w2 w3 w4 w5 w6 v0 w8 w9 w10 w11 w12 w13 w14 w15 rest hcap hact
  exact (runInstructions_append_some _ _ _ _ _ h0 (runInstructions_append_some _ _ _ _ _ h1 (runInstructions_append_some _ _ _ _ _ h2 (runInstructions_append_some _ _ _ _ _ h3 (runInstructions_append_some _ _ _ _ _ h4 (runInstructions_append_some _ _ _ _ _ h5 (runInstructions_append_some _ _ _ _ _ h6 (runInstructions_append_some _ _ _ _ _ h7 (runInstructions_append_some _ _ _ _ _ h8 (runInstructions_append_some _ _ _ _ _ h9 (runInstructions_append_some _ _ _ _ _ h10 (runInstructions_append_some _ _ _ _ _ h11 (runInstructions_append_some _ _ _ _ _ h12 (runInstructions_append_some _ _ _ _ _ h13 (runInstructions_append_some _ _ _ _ _ h14 (runInstructions_append_some _ _ _ _ _ h15 (runInstructions_append_some _ _ _ _ _ h16 (runInstructions_append_some _ _ _ _ _ h17 h18))))))))))))))))))
#print axioms stage7_run
end R9InvConsumeExec
