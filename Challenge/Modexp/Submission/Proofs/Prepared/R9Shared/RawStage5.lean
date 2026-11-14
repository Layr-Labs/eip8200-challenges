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
def stage5Part0Program : List Instr := [.op (.Dup dA11),.op (.Dup dA9),.push 2 768,.op .MLOAD,.op (.Dup dA0),.op (.Dup dA3),.op .MUL]
def stage5Part0Model (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 : W) (rest : List W) : State :=
  let v0 : W := MachineState.readWord (s.memory) 768
  let v1 : W := w11 * v0
  {s with pc := N 3967,memory := s.memory,stack := v1::v0::w8::w11::w0::w1::w2::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::rest}
theorem stage5Part0_run (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions stage5Part0Program {s with pc := N 3958,memory := s.memory,stack := w0::w1::w2::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::rest} = some (stage5Part0Model s w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 63) : rest.length+j < 1024 := by omega
  have ha768 : (768 : W).toNat = 768 := rfl
  have hf768 := Monpro.activeWords_fix s 768 32 (by decide) (by norm_num) hact
  simp [hz,hzn,stage5Part0Program,stage5Part0Model,runInstructions,runInstr,List.exchange,succ_ofNat_mod,ofNat_add_mod,Nat.add_assoc,State.activeWordsAfterUInt256,literal_eq_ofNat,capacity,ha768,hf768]
def stage5Part1Program : List Instr := [.push 1 64,.op .MLOAD,.op (.Dup dA9),.op .MUL,.op .ADD,.push 1 32,.op .MLOAD,.op (.Dup dA10)]
def stage5Part1Model (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 : W) (rest : List W) : State :=
  let v0 : W := MachineState.readWord (s.memory) 64
  let v1 : W := w8 * v0
  let v2 : W := v1 + w0
  let v3 : W := MachineState.readWord (s.memory) 32
  {s with pc := N 3977,memory := s.memory,stack := w9::v3::v2::w1::w2::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::w16::w17::w18::w19::rest}
theorem stage5Part1_run (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions stage5Part1Program {s with pc := N 3967,memory := s.memory,stack := w0::w1::w2::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::w16::w17::w18::w19::rest} = some (stage5Part1Model s w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 63) : rest.length+j < 1024 := by omega
  have ha32 : (32 : W).toNat = 32 := rfl
  have hf32 := Monpro.activeWords_fix s 32 32 (by decide) (by norm_num) hact
  have ha64 : (64 : W).toNat = 64 := rfl
  have hf64 := Monpro.activeWords_fix s 64 32 (by decide) (by norm_num) hact
  simp [hz,hzn,stage5Part1Program,stage5Part1Model,runInstructions,runInstr,List.exchange,succ_ofNat_mod,ofNat_add_mod,Nat.add_assoc,State.activeWordsAfterUInt256,literal_eq_ofNat,capacity,ha32,hf32,ha64,hf64]
def stage5Part2Program : List Instr := [.op .MUL,.op .ADD,.op (.Swap sA2),.op .MULMOD,.op (.Dup dA10),.push 1 64,.op .MLOAD,.op (.Dup dA8)]
def stage5Part2Model (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 w20 w21 : W) (rest : List W) : State :=
  let v0 : W := w0 * w1
  let v1 : W := v0 + w2
  let v2 : W := UInt256.mulMod w5 w3 w4
  let v3 : W := MachineState.readWord (s.memory) 64
  {s with pc := N 3986,memory := s.memory,stack := w10::v3::w14::v2::v1::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::w16::w17::w18::w19::w20::w21::rest}
theorem stage5Part2_run (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 w20 w21 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions stage5Part2Program {s with pc := N 3977,memory := s.memory,stack := w0::w1::w2::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::w16::w17::w18::w19::w20::w21::rest} = some (stage5Part2Model s w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 w20 w21 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 63) : rest.length+j < 1024 := by omega
  have ha64 : (64 : W).toNat = 64 := rfl
  have hf64 := Monpro.activeWords_fix s 64 32 (by decide) (by norm_num) hact
  simp [hz,hzn,stage5Part2Program,stage5Part2Model,runInstructions,runInstr,List.exchange,succ_ofNat_mod,ofNat_add_mod,Nat.add_assoc,State.activeWordsAfterUInt256,literal_eq_ofNat,capacity,ha64,hf64]
def stage5Part3Program : List Instr := [.op .MULMOD,.op .ADD,.op (.Dup dA10),.push 1 32,.op .MLOAD,.op (.Dup dA9),.op .MULMOD,.op .ADD]
def stage5Part3Model (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 w20 : W) (rest : List W) : State :=
  let v0 : W := UInt256.mulMod w0 w1 w2
  let v1 : W := v0 + w3
  let v2 : W := MachineState.readWord (s.memory) 32
  let v3 : W := UInt256.mulMod w10 v2 w13
  let v4 : W := v3 + v1
  {s with pc := N 3995,memory := s.memory,stack := v4::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::w16::w17::w18::w19::w20::rest}
theorem stage5Part3_run (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 w20 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions stage5Part3Program {s with pc := N 3986,memory := s.memory,stack := w0::w1::w2::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::w16::w17::w18::w19::w20::rest} = some (stage5Part3Model s w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 w20 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 63) : rest.length+j < 1024 := by omega
  have ha32 : (32 : W).toNat = 32 := rfl
  have hf32 := Monpro.activeWords_fix s 32 32 (by decide) (by norm_num) hact
  simp [hz,hzn,stage5Part3Program,stage5Part3Model,runInstructions,runInstr,List.exchange,succ_ofNat_mod,ofNat_add_mod,Nat.add_assoc,State.activeWordsAfterUInt256,literal_eq_ofNat,capacity,ha32,hf32]
def stage5Part4Program : List Instr := [.op (.Dup dA2),.op .ADD,.op (.Swap sA1),.op .ADD,.op (.Dup dA7),.op (.Dup dA11),.op .MUL,.op .ADD]
def stage5Part4Model (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 : W) (rest : List W) : State :=
  let v0 : W := w2 + w0
  let v1 : W := w2 + w1
  let v2 : W := w11 * w8
  let v3 : W := v2 + v1
  {s with pc := N 4003,memory := s.memory,stack := v3::v0::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::w16::w17::rest}
theorem stage5Part4_run (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions stage5Part4Program {s with pc := N 3995,memory := s.memory,stack := w0::w1::w2::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::w16::w17::rest} = some (stage5Part4Model s w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 63) : rest.length+j < 1024 := by omega
  simp [hz,hzn,stage5Part4Program,stage5Part4Model,runInstructions,runInstr,List.exchange,succ_ofNat_mod,ofNat_add_mod,Nat.add_assoc,State.activeWordsAfterUInt256,literal_eq_ofNat,capacity]
def stage5Part5Program : List Instr := [.op (.Dup dA4),.op (.Dup dA9),.op .MUL,.op .ADD,.op (.Dup dA14),.push 1 192,.op .MLOAD,.op .MUL]
def stage5Part5Model (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 : W) (rest : List W) : State :=
  let v0 : W := w8 * w4
  let v1 : W := v0 + w0
  let v2 : W := MachineState.readWord (s.memory) 192
  let v3 : W := v2 * w14
  {s with pc := N 4012,memory := s.memory,stack := v3::v1::w1::w2::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::w16::rest}
theorem stage5Part5_run (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions stage5Part5Program {s with pc := N 4003,memory := s.memory,stack := w0::w1::w2::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::w16::rest} = some (stage5Part5Model s w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 63) : rest.length+j < 1024 := by omega
  have ha192 : (192 : W).toNat = 192 := rfl
  have hf192 := Monpro.activeWords_fix s 192 32 (by decide) (by norm_num) hact
  simp [hz,hzn,stage5Part5Program,stage5Part5Model,runInstructions,runInstr,List.exchange,succ_ofNat_mod,ofNat_add_mod,Nat.add_assoc,State.activeWordsAfterUInt256,literal_eq_ofNat,capacity,ha192,hf192]
def stage5Part6Program : List Instr := [.op .ADD,.op (.Dup dA2),.push 0 0,.op .MLOAD,.op .MUL,.op .ADD,.op (.Dup dA11)]
def stage5Part6Model (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 : W) (rest : List W) : State :=
  let v0 : W := w0 + w1
  let v1 : W := MachineState.readWord (s.memory) 0
  let v2 : W := v1 * w3
  let v3 : W := v2 + v0
  {s with pc := N 4019,memory := s.memory,stack := w12::v3::w2::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::w16::w17::rest}
theorem stage5Part6_run (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions stage5Part6Program {s with pc := N 4012,memory := s.memory,stack := w0::w1::w2::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::w16::w17::rest} = some (stage5Part6Model s w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 63) : rest.length+j < 1024 := by omega
  have ha0 : (0 : W).toNat = 0 := rfl
  have hf0 := Monpro.activeWords_fix s 0 32 (by decide) (by norm_num) hact
  simp [hz,hzn,stage5Part6Program,stage5Part6Model,runInstructions,runInstr,List.exchange,succ_ofNat_mod,ofNat_add_mod,Nat.add_assoc,State.activeWordsAfterUInt256,literal_eq_ofNat,capacity,ha0,hf0]
def stage5Part7Program : List Instr := [.push 1 224,.op .MLOAD,.op .MUL,.op .ADD,.op (.Swap sA0),.op (.Dup dA9),.op (.Dup dA8),.op (.Dup dA12)]
def stage5Part7Model (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 : W) (rest : List W) : State :=
  let v0 : W := MachineState.readWord (s.memory) 224
  let v1 : W := v0 * w0
  let v2 : W := v1 + w1
  {s with pc := N 4028,memory := s.memory,stack := w11::w8::w10::w2::v2::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::w16::w17::rest}
theorem stage5Part7_run (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions stage5Part7Program {s with pc := N 4019,memory := s.memory,stack := w0::w1::w2::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::w16::w17::rest} = some (stage5Part7Model s w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 63) : rest.length+j < 1024 := by omega
  have ha224 : (224 : W).toNat = 224 := rfl
  have hf224 := Monpro.activeWords_fix s 224 32 (by decide) (by norm_num) hact
  simp [hz,hzn,stage5Part7Program,stage5Part7Model,runInstructions,runInstr,List.exchange,succ_ofNat_mod,ofNat_add_mod,Nat.add_assoc,State.activeWordsAfterUInt256,literal_eq_ofNat,capacity,ha224,hf224]
def stage5Part8Program : List Instr := [.op .MULMOD,.op .ADD,.op (.Dup dA9),.op (.Dup dA5),.op (.Dup dA10),.op .MULMOD,.op .ADD,.op (.Dup dA9)]
def stage5Part8Model (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 : W) (rest : List W) : State :=
  let v0 : W := UInt256.mulMod w0 w1 w2
  let v1 : W := v0 + w3
  let v2 : W := UInt256.mulMod w11 w7 w12
  let v3 : W := v2 + v1
  {s with pc := N 4036,memory := s.memory,stack := w12::v3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::w16::w17::w18::w19::rest}
theorem stage5Part8_run (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions stage5Part8Program {s with pc := N 4028,memory := s.memory,stack := w0::w1::w2::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::w16::w17::w18::w19::rest} = some (stage5Part8Model s w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 63) : rest.length+j < 1024 := by omega
  simp [hz,hzn,stage5Part8Program,stage5Part8Model,runInstructions,runInstr,List.exchange,succ_ofNat_mod,ofNat_add_mod,Nat.add_assoc,State.activeWordsAfterUInt256,literal_eq_ofNat,capacity]
def stage5Part9Program : List Instr := [.op (.Dup dA15),.push 1 192,.op .MLOAD,.op .MULMOD,.op .ADD,.op (.Dup dA9),.op (.Dup dA3)]
def stage5Part9Model (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 : W) (rest : List W) : State :=
  let v0 : W := MachineState.readWord (s.memory) 192
  let v1 : W := UInt256.mulMod v0 w15 w0
  let v2 : W := v1 + w1
  {s with pc := N 4044,memory := s.memory,stack := w3::w10::v2::w2::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::w16::w17::rest}
theorem stage5Part9_run (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions stage5Part9Program {s with pc := N 4036,memory := s.memory,stack := w0::w1::w2::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::w16::w17::rest} = some (stage5Part9Model s w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 63) : rest.length+j < 1024 := by omega
  have ha192 : (192 : W).toNat = 192 := rfl
  have hf192 := Monpro.activeWords_fix s 192 32 (by decide) (by norm_num) hact
  simp [hz,hzn,stage5Part9Program,stage5Part9Model,runInstructions,runInstr,List.exchange,succ_ofNat_mod,ofNat_add_mod,Nat.add_assoc,State.activeWordsAfterUInt256,literal_eq_ofNat,capacity,ha192,hf192]
def stage5Part10Program : List Instr := [.push 0 0,.op .MLOAD,.op .MULMOD,.op .ADD,.op (.Dup dA9),.op (.Dup dA12),.push 1 224,.op .MLOAD]
def stage5Part10Model (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 : W) (rest : List W) : State :=
  let v0 : W := MachineState.readWord (s.memory) 0
  let v1 : W := UInt256.mulMod v0 w0 w1
  let v2 : W := v1 + w2
  let v3 : W := MachineState.readWord (s.memory) 224
  {s with pc := N 4053,memory := s.memory,stack := v3::w13::w11::v2::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::w16::w17::w18::rest}
theorem stage5Part10_run (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions stage5Part10Program {s with pc := N 4044,memory := s.memory,stack := w0::w1::w2::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::w16::w17::w18::rest} = some (stage5Part10Model s w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 63) : rest.length+j < 1024 := by omega
  have ha0 : (0 : W).toNat = 0 := rfl
  have hf0 := Monpro.activeWords_fix s 0 32 (by decide) (by norm_num) hact
  have ha224 : (224 : W).toNat = 224 := rfl
  have hf224 := Monpro.activeWords_fix s 224 32 (by decide) (by norm_num) hact
  simp [hz,hzn,stage5Part10Program,stage5Part10Model,runInstructions,runInstr,List.exchange,succ_ofNat_mod,ofNat_add_mod,Nat.add_assoc,State.activeWordsAfterUInt256,literal_eq_ofNat,capacity,ha0,hf0,ha224,hf224]
def stage5Part11Program : List Instr := [.op .MULMOD,.op .ADD,.op (.Dup dA9),.op (.Dup dA14),.push 2 2720,.op .MLOAD,.op (.Dup dA2),.op (.Swap sA4),.op .MUL]
def stage5Part11Model (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 : W) (rest : List W) : State :=
  let v0 : W := UInt256.mulMod w0 w1 w2
  let v1 : W := v0 + w3
  let v2 : W := MachineState.readWord (s.memory) 2720
  let v3 : W := w4 * v2
  {s with pc := N 4064,memory := s.memory,stack := v3::w16::w12::v1::w12::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::w16::w17::w18::w19::rest}
theorem stage5Part11_run (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions stage5Part11Program {s with pc := N 4053,memory := s.memory,stack := w0::w1::w2::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::w16::w17::w18::w19::rest} = some (stage5Part11Model s w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 63) : rest.length+j < 1024 := by omega
  have ha2720 : (2720 : W).toNat = 2720 := rfl
  have hf2720 := Monpro.activeWords_fix s 2720 32 (by decide) (by norm_num) hact
  simp [hz,hzn,stage5Part11Program,stage5Part11Model,runInstructions,runInstr,List.exchange,succ_ofNat_mod,ofNat_add_mod,Nat.add_assoc,State.activeWordsAfterUInt256,literal_eq_ofNat,capacity,ha2720,hf2720]
def stage5Part12Program : List Instr := [.push 30 1766847064778384329583297500742918515827483896875618958121606201292619775,.op .AND,.op (.Dup dA0),.push 2 1216,.op .MSTORE,.op .MULMOD,.op .ADD,.push 2 2048]
def stage5Part12Model (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 : W) (rest : List W) : State :=
  let v0 : W := UInt256.land (N 1766847064778384329583297500742918515827483896875618958121606201292619775) w0
  let v1 : ByteArray := MachineState.writeBytes (s.memory) (Data.Bytes.natToBytesPadded v0.toNat 32) 1216
  let v2 : W := UInt256.mulMod v0 w1 w2
  let v3 : W := v2 + w3
  {s with pc := N 4106,memory := v1,stack := (N 2048)::v3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::w16::w17::w18::w19::rest}
theorem stage5Part12_run (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions stage5Part12Program {s with pc := N 4064,memory := s.memory,stack := w0::w1::w2::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::w16::w17::w18::w19::rest} = some (stage5Part12Model s w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 63) : rest.length+j < 1024 := by omega
  have ha1216 : (1216 : W).toNat = 1216 := rfl
  have hf1216 := Monpro.activeWords_fix s 1216 32 (by decide) (by norm_num) hact
  have ha2048 : (2048 : W).toNat = 2048 := rfl
  have hf2048 := Monpro.activeWords_fix s 2048 32 (by decide) (by norm_num) hact
  simp [hz,hzn,stage5Part12Program,stage5Part12Model,runInstructions,runInstr,List.exchange,succ_ofNat_mod,ofNat_add_mod,Nat.add_assoc,State.activeWordsAfterUInt256,literal_eq_ofNat,capacity,ha1216,hf1216,ha2048,hf2048]
def stage5Part13Program : List Instr := [.op .MULMOD]
def stage5Part13Model (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 : W) (rest : List W) : State :=
  let v0 : W := UInt256.mulMod w0 w1 w2
  {s with pc := N 4107,memory := s.memory,stack := v0::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::w16::w17::rest}
theorem stage5Part13_run (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions stage5Part13Program {s with pc := N 4106,memory := s.memory,stack := w0::w1::w2::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::w16::w17::rest} = some (stage5Part13Model s w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 63) : rest.length+j < 1024 := by omega
  simp [hz,hzn,stage5Part13Program,stage5Part13Model,runInstructions,runInstr,List.exchange,succ_ofNat_mod,ofNat_add_mod,Nat.add_assoc,State.activeWordsAfterUInt256,literal_eq_ofNat,capacity]
def stage5Program : List Instr := (stage5Part0Program++(stage5Part1Program++(stage5Part2Program++(stage5Part3Program++(stage5Part4Program++(stage5Part5Program++(stage5Part6Program++(stage5Part7Program++(stage5Part8Program++(stage5Part9Program++(stage5Part10Program++(stage5Part11Program++(stage5Part12Program++stage5Part13Program)))))))))))))
def stage5Model (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 : W) (rest : List W) : State :=
  let v0 : W := MachineState.readWord (s.memory) 768
  let v1 : W := w11 * v0
  let v2 : W := MachineState.readWord (s.memory) 64
  let v3 : W := w4 * v2
  let v4 : W := v3 + v1
  let v5 : W := MachineState.readWord (s.memory) 32
  let v6 : W := w5 * v5
  let v7 : W := v6 + v4
  let v8 : W := UInt256.mulMod w11 v0 w8
  let v9 : W := MachineState.readWord (s.memory) 64
  let v10 : W := UInt256.mulMod w4 v9 w8
  let v11 : W := v10 + v8
  let v12 : W := MachineState.readWord (s.memory) 32
  let v13 : W := UInt256.mulMod w5 v12 w8
  let v14 : W := v13 + v11
  let v15 : W := w0 + v14
  let v16 : W := w0 + v7
  let v17 : W := w9 * w6
  let v18 : W := v17 + v16
  let v19 : W := w7 * w3
  let v20 : W := v19 + v18
  let v21 : W := MachineState.readWord (s.memory) 192
  let v22 : W := v21 * w13
  let v23 : W := v22 + v20
  let v24 : W := MachineState.readWord (s.memory) 0
  let v25 : W := v24 * w1
  let v26 : W := v25 + v23
  let v27 : W := MachineState.readWord (s.memory) 224
  let v28 : W := v27 * w10
  let v29 : W := v28 + v26
  let v30 : W := UInt256.mulMod w9 w6 w8
  let v31 : W := v30 + v15
  let v32 : W := UInt256.mulMod w7 w3 w8
  let v33 : W := v32 + v31
  let v34 : W := MachineState.readWord (s.memory) 192
  let v35 : W := UInt256.mulMod v34 w13 w8
  let v36 : W := v35 + v33
  let v37 : W := MachineState.readWord (s.memory) 0
  let v38 : W := UInt256.mulMod v37 w1 w8
  let v39 : W := v38 + v36
  let v40 : W := MachineState.readWord (s.memory) 224
  let v41 : W := UInt256.mulMod v40 w10 w8
  let v42 : W := v41 + v39
  let v43 : W := MachineState.readWord (s.memory) 2720
  let v44 : W := v29 * v43
  let v45 : W := UInt256.land (N 1766847064778384329583297500742918515827483896875618958121606201292619775) v44
  let v46 : ByteArray := MachineState.writeBytes (s.memory) (Data.Bytes.natToBytesPadded v45.toNat 32) 1216
  let v47 : W := UInt256.mulMod v45 w12 w8
  let v48 : W := v47 + v42
  let v49 : W := UInt256.mulMod (N 2048) v48 w8
  {s with pc := N 4107,memory := v46,stack := v49::w1::w2::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::rest}
theorem stage5_run (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions stage5Program {s with pc := N 3958,memory := s.memory,stack := w0::w1::w2::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::rest} = some (stage5Model s w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 rest) := by
  let v0 : W := MachineState.readWord (s.memory) 768
  let v1 : W := w11 * v0
  let v2 : W := MachineState.readWord (s.memory) 64
  let v3 : W := w4 * v2
  let v4 : W := v3 + v1
  let v5 : W := MachineState.readWord (s.memory) 32
  let v6 : W := w5 * v5
  let v7 : W := v6 + v4
  let v8 : W := UInt256.mulMod w11 v0 w8
  let v9 : W := MachineState.readWord (s.memory) 64
  let v10 : W := UInt256.mulMod w4 v9 w8
  let v11 : W := v10 + v8
  let v12 : W := MachineState.readWord (s.memory) 32
  let v13 : W := UInt256.mulMod w5 v12 w8
  let v14 : W := v13 + v11
  let v15 : W := w0 + v14
  let v16 : W := w0 + v7
  let v17 : W := w9 * w6
  let v18 : W := v17 + v16
  let v19 : W := w7 * w3
  let v20 : W := v19 + v18
  let v21 : W := MachineState.readWord (s.memory) 192
  let v22 : W := v21 * w13
  let v23 : W := v22 + v20
  let v24 : W := MachineState.readWord (s.memory) 0
  let v25 : W := v24 * w1
  let v26 : W := v25 + v23
  let v27 : W := MachineState.readWord (s.memory) 224
  let v28 : W := v27 * w10
  let v29 : W := v28 + v26
  let v30 : W := UInt256.mulMod w9 w6 w8
  let v31 : W := v30 + v15
  let v32 : W := UInt256.mulMod w7 w3 w8
  let v33 : W := v32 + v31
  let v34 : W := MachineState.readWord (s.memory) 192
  let v35 : W := UInt256.mulMod v34 w13 w8
  let v36 : W := v35 + v33
  let v37 : W := MachineState.readWord (s.memory) 0
  let v38 : W := UInt256.mulMod v37 w1 w8
  let v39 : W := v38 + v36
  let v40 : W := MachineState.readWord (s.memory) 224
  let v41 : W := UInt256.mulMod v40 w10 w8
  let v42 : W := v41 + v39
  let v43 : W := MachineState.readWord (s.memory) 2720
  let v44 : W := v29 * v43
  let v45 : W := UInt256.land (N 1766847064778384329583297500742918515827483896875618958121606201292619775) v44
  let v46 : ByteArray := MachineState.writeBytes (s.memory) (Data.Bytes.natToBytesPadded v45.toNat 32) 1216
  let v47 : W := UInt256.mulMod v45 w12 w8
  let v48 : W := v47 + v42
  let v49 : W := UInt256.mulMod (N 2048) v48 w8
  have h0 : runInstructions stage5Part0Program {s with pc := N 3958,memory := s.memory,stack := w0::w1::w2::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::rest} = some {s with pc := N 3967,memory := s.memory,stack := v1::v0::w8::w11::w0::w1::w2::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::rest} := by
    simpa only [stage5Part0Model,v0,v1] using stage5Part0_run ({s with memory := s.memory}) w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 rest hcap hact
  have h1 : runInstructions stage5Part1Program {s with pc := N 3967,memory := s.memory,stack := v1::v0::w8::w11::w0::w1::w2::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::rest} = some {s with pc := N 3977,memory := s.memory,stack := w5::v5::v4::v0::w8::w11::w0::w1::w2::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::rest} := by
    simpa only [stage5Part1Model,v2,v3,v4,v5] using stage5Part1_run ({s with memory := s.memory}) v1 v0 w8 w11 w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 rest hcap hact
  have h2 : runInstructions stage5Part2Program {s with pc := N 3977,memory := s.memory,stack := w5::v5::v4::v0::w8::w11::w0::w1::w2::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::rest} = some {s with pc := N 3986,memory := s.memory,stack := w4::v9::w8::v8::v7::w0::w1::w2::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::rest} := by
    simpa only [stage5Part2Model,v6,v7,v8,v9] using stage5Part2_run ({s with memory := s.memory}) w5 v5 v4 v0 w8 w11 w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 rest hcap hact
  have h3 : runInstructions stage5Part3Program {s with pc := N 3986,memory := s.memory,stack := w4::v9::w8::v8::v7::w0::w1::w2::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::rest} = some {s with pc := N 3995,memory := s.memory,stack := v14::v7::w0::w1::w2::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::rest} := by
    simpa only [stage5Part3Model,v10,v11,v12,v13,v14] using stage5Part3_run ({s with memory := s.memory}) w4 v9 w8 v8 v7 w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 rest hcap hact
  have h4 : runInstructions stage5Part4Program {s with pc := N 3995,memory := s.memory,stack := v14::v7::w0::w1::w2::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::rest} = some {s with pc := N 4003,memory := s.memory,stack := v18::v15::w1::w2::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::rest} := by
    simpa only [stage5Part4Model,v15,v16,v17,v18] using stage5Part4_run ({s with memory := s.memory}) v14 v7 w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 rest hcap hact
  have h5 : runInstructions stage5Part5Program {s with pc := N 4003,memory := s.memory,stack := v18::v15::w1::w2::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::rest} = some {s with pc := N 4012,memory := s.memory,stack := v22::v20::v15::w1::w2::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::rest} := by
    simpa only [stage5Part5Model,v19,v20,v21,v22] using stage5Part5_run ({s with memory := s.memory}) v18 v15 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 rest hcap hact
  have h6 : runInstructions stage5Part6Program {s with pc := N 4012,memory := s.memory,stack := v22::v20::v15::w1::w2::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::rest} = some {s with pc := N 4019,memory := s.memory,stack := w10::v26::v15::w1::w2::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::rest} := by
    simpa only [stage5Part6Model,v23,v24,v25,v26] using stage5Part6_run ({s with memory := s.memory}) v22 v20 v15 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 rest hcap hact
  have h7 : runInstructions stage5Part7Program {s with pc := N 4019,memory := s.memory,stack := w10::v26::v15::w1::w2::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::rest} = some {s with pc := N 4028,memory := s.memory,stack := w9::w6::w8::v15::v29::w1::w2::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::rest} := by
    simpa only [stage5Part7Model,v27,v28,v29] using stage5Part7_run ({s with memory := s.memory}) w10 v26 v15 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 rest hcap hact
  have h8 : runInstructions stage5Part8Program {s with pc := N 4028,memory := s.memory,stack := w9::w6::w8::v15::v29::w1::w2::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::rest} = some {s with pc := N 4036,memory := s.memory,stack := w8::v33::v29::w1::w2::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::rest} := by
    simpa only [stage5Part8Model,v30,v31,v32,v33] using stage5Part8_run ({s with memory := s.memory}) w9 w6 w8 v15 v29 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 rest hcap hact
  have h9 : runInstructions stage5Part9Program {s with pc := N 4036,memory := s.memory,stack := w8::v33::v29::w1::w2::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::rest} = some {s with pc := N 4044,memory := s.memory,stack := w1::w8::v36::v29::w1::w2::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::rest} := by
    simpa only [stage5Part9Model,v34,v35,v36] using stage5Part9_run ({s with memory := s.memory}) w8 v33 v29 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 rest hcap hact
  have h10 : runInstructions stage5Part10Program {s with pc := N 4044,memory := s.memory,stack := w1::w8::v36::v29::w1::w2::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::rest} = some {s with pc := N 4053,memory := s.memory,stack := v40::w10::w8::v39::v29::w1::w2::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::rest} := by
    simpa only [stage5Part10Model,v37,v38,v39,v40] using stage5Part10_run ({s with memory := s.memory}) w1 w8 v36 v29 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 rest hcap hact
  have h11 : runInstructions stage5Part11Program {s with pc := N 4053,memory := s.memory,stack := v40::w10::w8::v39::v29::w1::w2::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::rest} = some {s with pc := N 4064,memory := s.memory,stack := v44::w12::w8::v42::w8::w1::w2::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::rest} := by
    simpa only [stage5Part11Model,v41,v42,v43,v44] using stage5Part11_run ({s with memory := s.memory}) v40 w10 w8 v39 v29 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 rest hcap hact
  have h12 : runInstructions stage5Part12Program {s with pc := N 4064,memory := s.memory,stack := v44::w12::w8::v42::w8::w1::w2::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::rest} = some {s with pc := N 4106,memory := v46,stack := (N 2048)::v48::w8::w1::w2::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::rest} := by
    simpa only [stage5Part12Model,v45,v46,v47,v48] using stage5Part12_run ({s with memory := s.memory}) v44 w12 w8 v42 w8 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 rest hcap hact
  have h13 : runInstructions stage5Part13Program {s with pc := N 4106,memory := v46,stack := (N 2048)::v48::w8::w1::w2::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::rest} = some {s with pc := N 4107,memory := v46,stack := v49::w1::w2::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::rest} := by
    simpa only [stage5Part13Model,v49] using stage5Part13_run ({s with memory := v46}) (N 2048) v48 w8 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 rest hcap hact
  exact (runInstructions_append_some _ _ _ _ _ h0 (runInstructions_append_some _ _ _ _ _ h1 (runInstructions_append_some _ _ _ _ _ h2 (runInstructions_append_some _ _ _ _ _ h3 (runInstructions_append_some _ _ _ _ _ h4 (runInstructions_append_some _ _ _ _ _ h5 (runInstructions_append_some _ _ _ _ _ h6 (runInstructions_append_some _ _ _ _ _ h7 (runInstructions_append_some _ _ _ _ _ h8 (runInstructions_append_some _ _ _ _ _ h9 (runInstructions_append_some _ _ _ _ _ h10 (runInstructions_append_some _ _ _ _ _ h11 (runInstructions_append_some _ _ _ _ _ h12 h13)))))))))))))
#print axioms stage5_run
end R9InvConsumeExec
