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
def stage10Part0Program : List Instr := [.op (.Dup dA15),.op (.Dup dA9),.push 2 1216,.op .MLOAD,.push 2 1280,.op .MLOAD,.op (.Swap sA13),.op .POP]
def stage10Part0Model (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 : W) (rest : List W) : State :=
  let v0 : W := MachineState.readWord (s.memory) 1216
  let v1 : W := MachineState.readWord (s.memory) 1280
  {s with pc := N 4951,memory := s.memory,stack := v0::w8::w15::w0::w1::w2::w3::w4::w5::w6::w7::w8::w9::v1::w11::w12::w13::w14::w15::rest}
theorem stage10Part0_run (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions stage10Part0Program {s with pc := N 4939,memory := s.memory,stack := w0::w1::w2::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::rest} = some (stage10Part0Model s w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 63) : rest.length+j < 1024 := by omega
  have ha1216 : (1216 : W).toNat = 1216 := rfl
  have hf1216 := Monpro.activeWords_fix s 1216 32 (by decide) (by norm_num) hact
  have ha1280 : (1280 : W).toNat = 1280 := rfl
  have hf1280 := Monpro.activeWords_fix s 1280 32 (by decide) (by norm_num) hact
  simp [hz,hzn,stage10Part0Program,stage10Part0Model,runInstructions,runInstr,List.exchange,succ_ofNat_mod,ofNat_add_mod,Nat.add_assoc,State.activeWordsAfterUInt256,literal_eq_ofNat,capacity,ha1216,hf1216,ha1280,hf1280]
def stage10Part1Program : List Instr := [.op (.Swap sA7),.op (.Dup dA0),.op (.Dup dA3),.op .MUL,.push 1 160,.op .MLOAD,.push 1 32,.op .MLOAD]
def stage10Part1Model (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 : W) (rest : List W) : State :=
  let v0 : W := w2 * w8
  let v1 : W := MachineState.readWord (s.memory) 160
  let v2 : W := MachineState.readWord (s.memory) 32
  {s with pc := N 4961,memory := s.memory,stack := v2::v1::v0::w8::w1::w2::w3::w4::w5::w6::w7::w0::w9::w10::w11::w12::w13::w14::w15::w16::w17::w18::rest}
theorem stage10Part1_run (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions stage10Part1Program {s with pc := N 4951,memory := s.memory,stack := w0::w1::w2::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::w16::w17::w18::rest} = some (stage10Part1Model s w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 63) : rest.length+j < 1024 := by omega
  have ha32 : (32 : W).toNat = 32 := rfl
  have hf32 := Monpro.activeWords_fix s 32 32 (by decide) (by norm_num) hact
  have ha160 : (160 : W).toNat = 160 := rfl
  have hf160 := Monpro.activeWords_fix s 160 32 (by decide) (by norm_num) hact
  simp [hz,hzn,stage10Part1Program,stage10Part1Model,runInstructions,runInstr,List.exchange,succ_ofNat_mod,ofNat_add_mod,Nat.add_assoc,State.activeWordsAfterUInt256,literal_eq_ofNat,capacity,ha32,hf32,ha160,hf160]
def stage10Part2Program : List Instr := [.op .MUL,.op .ADD,.push 1 128,.op .MLOAD,.push 1 64,.op .MLOAD,.op .MUL,.op .ADD]
def stage10Part2Model (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 w20 w21 : W) (rest : List W) : State :=
  let v0 : W := w0 * w1
  let v1 : W := v0 + w2
  let v2 : W := MachineState.readWord (s.memory) 128
  let v3 : W := MachineState.readWord (s.memory) 64
  let v4 : W := v3 * v2
  let v5 : W := v4 + v1
  {s with pc := N 4971,memory := s.memory,stack := v5::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::w16::w17::w18::w19::w20::w21::rest}
theorem stage10Part2_run (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 w20 w21 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions stage10Part2Program {s with pc := N 4961,memory := s.memory,stack := w0::w1::w2::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::w16::w17::w18::w19::w20::w21::rest} = some (stage10Part2Model s w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 w20 w21 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 63) : rest.length+j < 1024 := by omega
  have ha64 : (64 : W).toNat = 64 := rfl
  have hf64 := Monpro.activeWords_fix s 64 32 (by decide) (by norm_num) hact
  have ha128 : (128 : W).toNat = 128 := rfl
  have hf128 := Monpro.activeWords_fix s 128 32 (by decide) (by norm_num) hact
  simp [hz,hzn,stage10Part2Program,stage10Part2Model,runInstructions,runInstr,List.exchange,succ_ofNat_mod,ofNat_add_mod,Nat.add_assoc,State.activeWordsAfterUInt256,literal_eq_ofNat,capacity,ha64,hf64,ha128,hf128]
def stage10Part3Program : List Instr := [.op (.Swap sA2),.op .MULMOD,.op (.Dup dA10),.push 1 160,.op .MLOAD,.push 1 32,.op .MLOAD,.op .MULMOD]
def stage10Part3Model (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 : W) (rest : List W) : State :=
  let v0 : W := UInt256.mulMod w3 w1 w2
  let v1 : W := MachineState.readWord (s.memory) 160
  let v2 : W := MachineState.readWord (s.memory) 32
  let v3 : W := UInt256.mulMod v2 v1 w12
  {s with pc := N 4981,memory := s.memory,stack := v3::v0::w0::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::w16::w17::w18::w19::rest}
theorem stage10Part3_run (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions stage10Part3Program {s with pc := N 4971,memory := s.memory,stack := w0::w1::w2::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::w16::w17::w18::w19::rest} = some (stage10Part3Model s w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 63) : rest.length+j < 1024 := by omega
  have ha32 : (32 : W).toNat = 32 := rfl
  have hf32 := Monpro.activeWords_fix s 32 32 (by decide) (by norm_num) hact
  have ha160 : (160 : W).toNat = 160 := rfl
  have hf160 := Monpro.activeWords_fix s 160 32 (by decide) (by norm_num) hact
  simp [hz,hzn,stage10Part3Program,stage10Part3Model,runInstructions,runInstr,List.exchange,succ_ofNat_mod,ofNat_add_mod,Nat.add_assoc,State.activeWordsAfterUInt256,literal_eq_ofNat,capacity,ha32,hf32,ha160,hf160]
def stage10Part4Program : List Instr := [.op .ADD,.op (.Dup dA10),.push 1 128,.op .MLOAD,.push 1 64,.op .MLOAD,.op .MULMOD,.op .ADD]
def stage10Part4Model (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 : W) (rest : List W) : State :=
  let v0 : W := w0 + w1
  let v1 : W := MachineState.readWord (s.memory) 128
  let v2 : W := MachineState.readWord (s.memory) 64
  let v3 : W := UInt256.mulMod v2 v1 w11
  let v4 : W := v3 + v0
  {s with pc := N 4991,memory := s.memory,stack := v4::w2::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::w16::w17::w18::rest}
theorem stage10Part4_run (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions stage10Part4Program {s with pc := N 4981,memory := s.memory,stack := w0::w1::w2::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::w16::w17::w18::rest} = some (stage10Part4Model s w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 63) : rest.length+j < 1024 := by omega
  have ha64 : (64 : W).toNat = 64 := rfl
  have hf64 := Monpro.activeWords_fix s 64 32 (by decide) (by norm_num) hact
  have ha128 : (128 : W).toNat = 128 := rfl
  have hf128 := Monpro.activeWords_fix s 128 32 (by decide) (by norm_num) hact
  simp [hz,hzn,stage10Part4Program,stage10Part4Model,runInstructions,runInstr,List.exchange,succ_ofNat_mod,ofNat_add_mod,Nat.add_assoc,State.activeWordsAfterUInt256,literal_eq_ofNat,capacity,ha64,hf64,ha128,hf128]
def stage10Part5Program : List Instr := [.op (.Dup dA2),.op .ADD,.op (.Swap sA1),.op .ADD,.op (.Dup dA12),.op (.Dup dA0),.op .MUL]
def stage10Part5Model (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 : W) (rest : List W) : State :=
  let v0 : W := w2 + w0
  let v1 : W := w2 + w1
  let v2 : W := w13 * w13
  {s with pc := N 4998,memory := s.memory,stack := v2::v1::v0::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::w16::w17::rest}
theorem stage10Part5_run (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions stage10Part5Program {s with pc := N 4991,memory := s.memory,stack := w0::w1::w2::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::w16::w17::rest} = some (stage10Part5Model s w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 63) : rest.length+j < 1024 := by omega
  simp [hz,hzn,stage10Part5Program,stage10Part5Model,runInstructions,runInstr,List.exchange,succ_ofNat_mod,ofNat_add_mod,Nat.add_assoc,State.activeWordsAfterUInt256,literal_eq_ofNat,capacity]
def stage10Part6Program : List Instr := [.op .ADD,.push 1 192,.op .MLOAD,.op (.Dup dA11),.op .MUL,.op .ADD,.push 0 0,.op .MLOAD]
def stage10Part6Model (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 : W) (rest : List W) : State :=
  let v0 : W := w0 + w1
  let v1 : W := MachineState.readWord (s.memory) 192
  let v2 : W := w11 * v1
  let v3 : W := v2 + v0
  let v4 : W := MachineState.readWord (s.memory) 0
  {s with pc := N 5007,memory := s.memory,stack := v4::v3::w2::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::w16::w17::rest}
theorem stage10Part6_run (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions stage10Part6Program {s with pc := N 4998,memory := s.memory,stack := w0::w1::w2::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::w16::w17::rest} = some (stage10Part6Model s w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 63) : rest.length+j < 1024 := by omega
  have ha0 : (0 : W).toNat = 0 := rfl
  have hf0 := Monpro.activeWords_fix s 0 32 (by decide) (by norm_num) hact
  have ha192 : (192 : W).toNat = 192 := rfl
  have hf192 := Monpro.activeWords_fix s 192 32 (by decide) (by norm_num) hact
  simp [hz,hzn,stage10Part6Program,stage10Part6Model,runInstructions,runInstr,List.exchange,succ_ofNat_mod,ofNat_add_mod,Nat.add_assoc,State.activeWordsAfterUInt256,literal_eq_ofNat,capacity,ha0,hf0,ha192,hf192]
def stage10Part7Program : List Instr := [.op (.Dup dA9),.op .MUL,.op .ADD,.op (.Dup dA3),.push 1 224,.op .MLOAD,.op .MUL,.op .ADD]
def stage10Part7Model (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 : W) (rest : List W) : State :=
  let v0 : W := w9 * w0
  let v1 : W := v0 + w1
  let v2 : W := MachineState.readWord (s.memory) 224
  let v3 : W := v2 * w4
  let v4 : W := v3 + v1
  {s with pc := N 5016,memory := s.memory,stack := v4::w2::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::w16::w17::rest}
theorem stage10Part7_run (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions stage10Part7Program {s with pc := N 5007,memory := s.memory,stack := w0::w1::w2::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::w16::w17::rest} = some (stage10Part7Model s w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 63) : rest.length+j < 1024 := by omega
  have ha224 : (224 : W).toNat = 224 := rfl
  have hf224 := Monpro.activeWords_fix s 224 32 (by decide) (by norm_num) hact
  simp [hz,hzn,stage10Part7Program,stage10Part7Model,runInstructions,runInstr,List.exchange,succ_ofNat_mod,ofNat_add_mod,Nat.add_assoc,State.activeWordsAfterUInt256,literal_eq_ofNat,capacity,ha224,hf224]
def stage10Part8Program : List Instr := [.op (.Dup dA7),.op (.Dup dA7),.op .MUL,.op .ADD,.op (.Dup dA4),.op (.Dup dA6),.op .MUL,.op .ADD]
def stage10Part8Model (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 : W) (rest : List W) : State :=
  let v0 : W := w6 * w7
  let v1 : W := v0 + w0
  let v2 : W := w5 * w4
  let v3 : W := v2 + v1
  {s with pc := N 5024,memory := s.memory,stack := v3::w1::w2::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::w16::rest}
theorem stage10Part8_run (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions stage10Part8Program {s with pc := N 5016,memory := s.memory,stack := w0::w1::w2::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::w16::rest} = some (stage10Part8Model s w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 63) : rest.length+j < 1024 := by omega
  simp [hz,hzn,stage10Part8Program,stage10Part8Model,runInstructions,runInstr,List.exchange,succ_ofNat_mod,ofNat_add_mod,Nat.add_assoc,State.activeWordsAfterUInt256,literal_eq_ofNat,capacity]
def stage10Part9Program : List Instr := [.op (.Dup dA11),.op (.Dup dA15),.op .MUL,.op .ADD,.op (.Dup dA2),.op (.Dup dA14),.op .MUL,.op .ADD]
def stage10Part9Model (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 : W) (rest : List W) : State :=
  let v0 : W := w14 * w11
  let v1 : W := v0 + w0
  let v2 : W := w13 * w2
  let v3 : W := v2 + v1
  {s with pc := N 5032,memory := s.memory,stack := v3::w1::w2::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::w16::rest}
theorem stage10Part9_run (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions stage10Part9Program {s with pc := N 5024,memory := s.memory,stack := w0::w1::w2::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::w16::rest} = some (stage10Part9Model s w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 63) : rest.length+j < 1024 := by omega
  simp [hz,hzn,stage10Part9Program,stage10Part9Model,runInstructions,runInstr,List.exchange,succ_ofNat_mod,ofNat_add_mod,Nat.add_assoc,State.activeWordsAfterUInt256,literal_eq_ofNat,capacity]
def stage10Part10Program : List Instr := [.op (.Swap sA0),.op (.Dup dA9),.op (.Dup dA13),.op (.Dup dA0),.op (.Dup dA0),.op (.Dup dA0),.op .ADD]
def stage10Part10Model (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 : W) (rest : List W) : State :=
  let v0 : W := w12 + w12
  {s with pc := N 5039,memory := s.memory,stack := v0::w12::w12::w9::w1::w0::w2::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::w16::rest}
theorem stage10Part10_run (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions stage10Part10Program {s with pc := N 5032,memory := s.memory,stack := w0::w1::w2::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::w16::rest} = some (stage10Part10Model s w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 63) : rest.length+j < 1024 := by omega
  simp [hz,hzn,stage10Part10Program,stage10Part10Model,runInstructions,runInstr,List.exchange,succ_ofNat_mod,ofNat_add_mod,Nat.add_assoc,State.activeWordsAfterUInt256,literal_eq_ofNat,capacity]
def stage10Part11Program : List Instr := [.op (.Swap sA15),.op .POP,.op .MULMOD,.op .ADD,.op (.Dup dA9),.push 1 192,.op .MLOAD,.op (.Dup dA12)]
def stage10Part11Model (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 w20 : W) (rest : List W) : State :=
  let v0 : W := UInt256.mulMod w1 w2 w3
  let v1 : W := v0 + w4
  let v2 : W := MachineState.readWord (s.memory) 192
  {s with pc := N 5048,memory := s.memory,stack := w14::v2::w13::v1::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::w0::w17::w18::w19::w20::rest}
theorem stage10Part11_run (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 w20 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions stage10Part11Program {s with pc := N 5039,memory := s.memory,stack := w0::w1::w2::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::w16::w17::w18::w19::w20::rest} = some (stage10Part11Model s w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 w20 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 63) : rest.length+j < 1024 := by omega
  have ha192 : (192 : W).toNat = 192 := rfl
  have hf192 := Monpro.activeWords_fix s 192 32 (by decide) (by norm_num) hact
  simp [hz,hzn,stage10Part11Program,stage10Part11Model,runInstructions,runInstr,List.exchange,succ_ofNat_mod,ofNat_add_mod,Nat.add_assoc,State.activeWordsAfterUInt256,literal_eq_ofNat,capacity,ha192,hf192]
def stage10Part12Program : List Instr := [.op .MULMOD,.op .ADD,.op (.Dup dA9),.push 0 0,.op .MLOAD,.op (.Dup dA10),.op .MULMOD,.op .ADD]
def stage10Part12Model (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 : W) (rest : List W) : State :=
  let v0 : W := UInt256.mulMod w0 w1 w2
  let v1 : W := v0 + w3
  let v2 : W := MachineState.readWord (s.memory) 0
  let v3 : W := UInt256.mulMod w11 v2 w12
  let v4 : W := v3 + v1
  {s with pc := N 5056,memory := s.memory,stack := v4::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::w16::w17::w18::w19::rest}
theorem stage10Part12_run (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions stage10Part12Program {s with pc := N 5048,memory := s.memory,stack := w0::w1::w2::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::w16::w17::w18::w19::rest} = some (stage10Part12Model s w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 63) : rest.length+j < 1024 := by omega
  have ha0 : (0 : W).toNat = 0 := rfl
  have hf0 := Monpro.activeWords_fix s 0 32 (by decide) (by norm_num) hact
  simp [hz,hzn,stage10Part12Program,stage10Part12Model,runInstructions,runInstr,List.exchange,succ_ofNat_mod,ofNat_add_mod,Nat.add_assoc,State.activeWordsAfterUInt256,literal_eq_ofNat,capacity,ha0,hf0]
def stage10Part13Program : List Instr := [.op (.Dup dA9),.op (.Dup dA4),.push 1 224,.op .MLOAD,.op .MULMOD,.op .ADD,.op (.Dup dA9),.op (.Dup dA8)]
def stage10Part13Model (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 : W) (rest : List W) : State :=
  let v0 : W := MachineState.readWord (s.memory) 224
  let v1 : W := UInt256.mulMod v0 w3 w9
  let v2 : W := v1 + w0
  {s with pc := N 5065,memory := s.memory,stack := w7::w9::v2::w1::w2::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::w16::rest}
theorem stage10Part13_run (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions stage10Part13Program {s with pc := N 5056,memory := s.memory,stack := w0::w1::w2::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::w16::rest} = some (stage10Part13Model s w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 63) : rest.length+j < 1024 := by omega
  have ha224 : (224 : W).toNat = 224 := rfl
  have hf224 := Monpro.activeWords_fix s 224 32 (by decide) (by norm_num) hact
  simp [hz,hzn,stage10Part13Program,stage10Part13Model,runInstructions,runInstr,List.exchange,succ_ofNat_mod,ofNat_add_mod,Nat.add_assoc,State.activeWordsAfterUInt256,literal_eq_ofNat,capacity,ha224,hf224]
def stage10Part14Program : List Instr := [.op (.Dup dA8),.op .MULMOD,.op .ADD,.op (.Dup dA9),.op (.Dup dA5),.op (.Dup dA7),.op .MULMOD,.op .ADD]
def stage10Part14Model (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 : W) (rest : List W) : State :=
  let v0 : W := UInt256.mulMod w8 w0 w1
  let v1 : W := v0 + w2
  let v2 : W := UInt256.mulMod w7 w6 w11
  let v3 : W := v2 + v1
  {s with pc := N 5073,memory := s.memory,stack := v3::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::w16::w17::w18::rest}
theorem stage10Part14_run (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions stage10Part14Program {s with pc := N 5065,memory := s.memory,stack := w0::w1::w2::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::w16::w17::w18::rest} = some (stage10Part14Model s w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 63) : rest.length+j < 1024 := by omega
  simp [hz,hzn,stage10Part14Program,stage10Part14Model,runInstructions,runInstr,List.exchange,succ_ofNat_mod,ofNat_add_mod,Nat.add_assoc,State.activeWordsAfterUInt256,literal_eq_ofNat,capacity]
def stage10Part15Program : List Instr := [.op (.Dup dA9),.op (.Dup dA15),.op (.Dup dA13),.op .MULMOD,.op .ADD,.op (.Dup dA9),.op (.Dup dA3),.op (.Dup dA15)]
def stage10Part15Model (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 : W) (rest : List W) : State :=
  let v0 : W := UInt256.mulMod w11 w14 w9
  let v1 : W := v0 + w0
  {s with pc := N 5081,memory := s.memory,stack := w13::w2::w9::v1::w1::w2::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::w16::rest}
theorem stage10Part15_run (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions stage10Part15Program {s with pc := N 5073,memory := s.memory,stack := w0::w1::w2::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::w16::rest} = some (stage10Part15Model s w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 63) : rest.length+j < 1024 := by omega
  simp [hz,hzn,stage10Part15Program,stage10Part15Model,runInstructions,runInstr,List.exchange,succ_ofNat_mod,ofNat_add_mod,Nat.add_assoc,State.activeWordsAfterUInt256,literal_eq_ofNat,capacity]
def stage10Part16Program : List Instr := [.op .MULMOD,.op .ADD,.op (.Swap sA0),.push 30 1766847064778384329583297500742918515827483896875618958121606201292619775,.op .AND,.op (.Dup dA0),.push 2 800,.op .MSTORE]
def stage10Part16Model (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 : W) (rest : List W) : State :=
  let v0 : W := UInt256.mulMod w0 w1 w2
  let v1 : W := v0 + w3
  let v2 : W := UInt256.land (N 1766847064778384329583297500742918515827483896875618958121606201292619775) w4
  let v3 : ByteArray := MachineState.writeBytes (s.memory) (Data.Bytes.natToBytesPadded v2.toNat 32) 800
  {s with pc := N 5121,memory := v3,stack := v2::v1::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::w16::w17::w18::w19::rest}
theorem stage10Part16_run (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions stage10Part16Program {s with pc := N 5081,memory := s.memory,stack := w0::w1::w2::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::w16::w17::w18::w19::rest} = some (stage10Part16Model s w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 63) : rest.length+j < 1024 := by omega
  have ha800 : (800 : W).toNat = 800 := rfl
  have hf800 := Monpro.activeWords_fix s 800 32 (by decide) (by norm_num) hact
  simp [hz,hzn,stage10Part16Program,stage10Part16Model,runInstructions,runInstr,List.exchange,succ_ofNat_mod,ofNat_add_mod,Nat.add_assoc,State.activeWordsAfterUInt256,literal_eq_ofNat,capacity,ha800,hf800]
def stage10Part17Program : List Instr := [.op (.Dup dA9),.op (.Swap sA1),.op .SUB,.op (.Dup dA1),.op .ADD,.push 2 2048,.op .MULMOD]
def stage10Part17Model (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 : W) (rest : List W) : State :=
  let v0 : W := w1 - w0
  let v1 : W := w9 + v0
  let v2 : W := UInt256.mulMod (N 2048) v1 w9
  {s with pc := N 5130,memory := s.memory,stack := v2::w2::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::w16::rest}
theorem stage10Part17_run (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions stage10Part17Program {s with pc := N 5121,memory := s.memory,stack := w0::w1::w2::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::w16::rest} = some (stage10Part17Model s w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 63) : rest.length+j < 1024 := by omega
  have ha2048 : (2048 : W).toNat = 2048 := rfl
  have hf2048 := Monpro.activeWords_fix s 2048 32 (by decide) (by norm_num) hact
  simp [hz,hzn,stage10Part17Program,stage10Part17Model,runInstructions,runInstr,List.exchange,succ_ofNat_mod,ofNat_add_mod,Nat.add_assoc,State.activeWordsAfterUInt256,literal_eq_ofNat,capacity,ha2048,hf2048]
def stage10Program : List Instr := (stage10Part0Program++(stage10Part1Program++(stage10Part2Program++(stage10Part3Program++(stage10Part4Program++(stage10Part5Program++(stage10Part6Program++(stage10Part7Program++(stage10Part8Program++(stage10Part9Program++(stage10Part10Program++(stage10Part11Program++(stage10Part12Program++(stage10Part13Program++(stage10Part14Program++(stage10Part15Program++(stage10Part16Program++stage10Part17Program)))))))))))))))))
def stage10Model (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 : W) (rest : List W) : State :=
  let v0 : W := MachineState.readWord (s.memory) 1216
  let v1 : W := MachineState.readWord (s.memory) 1280
  let v2 : W := w15 * w5
  let v3 : W := MachineState.readWord (s.memory) 160
  let v4 : W := MachineState.readWord (s.memory) 32
  let v5 : W := v4 * v3
  let v6 : W := v5 + v2
  let v7 : W := MachineState.readWord (s.memory) 128
  let v8 : W := MachineState.readWord (s.memory) 64
  let v9 : W := v8 * v7
  let v10 : W := v9 + v6
  let v11 : W := UInt256.mulMod w15 w5 w8
  let v12 : W := MachineState.readWord (s.memory) 160
  let v13 : W := MachineState.readWord (s.memory) 32
  let v14 : W := UInt256.mulMod v13 v12 w8
  let v15 : W := v14 + v11
  let v16 : W := MachineState.readWord (s.memory) 128
  let v17 : W := MachineState.readWord (s.memory) 64
  let v18 : W := UInt256.mulMod v17 v16 w8
  let v19 : W := v18 + v15
  let v20 : W := w0 + v19
  let v21 : W := w0 + v10
  let v22 : W := w11 * w11
  let v23 : W := v22 + v21
  let v24 : W := MachineState.readWord (s.memory) 192
  let v25 : W := w9 * v24
  let v26 : W := v25 + v23
  let v27 : W := MachineState.readWord (s.memory) 0
  let v28 : W := w7 * v27
  let v29 : W := v28 + v26
  let v30 : W := MachineState.readWord (s.memory) 224
  let v31 : W := v30 * w2
  let v32 : W := v31 + v29
  let v33 : W := v0 * w6
  let v34 : W := v33 + v32
  let v35 : W := w4 * w3
  let v36 : W := v35 + v34
  let v37 : W := w13 * v1
  let v38 : W := v37 + v36
  let v39 : W := w12 * w1
  let v40 : W := v39 + v38
  let v41 : W := w11 + w11
  let v42 : W := UInt256.mulMod w11 w11 w8
  let v43 : W := v42 + v20
  let v44 : W := MachineState.readWord (s.memory) 192
  let v45 : W := UInt256.mulMod w9 v44 w8
  let v46 : W := v45 + v43
  let v47 : W := MachineState.readWord (s.memory) 0
  let v48 : W := UInt256.mulMod w7 v47 w8
  let v49 : W := v48 + v46
  let v50 : W := MachineState.readWord (s.memory) 224
  let v51 : W := UInt256.mulMod v50 w2 w8
  let v52 : W := v51 + v49
  let v53 : W := UInt256.mulMod v0 w6 w8
  let v54 : W := v53 + v52
  let v55 : W := UInt256.mulMod w4 w3 w8
  let v56 : W := v55 + v54
  let v57 : W := UInt256.mulMod v1 w13 w8
  let v58 : W := v57 + v56
  let v59 : W := UInt256.mulMod w12 w1 w8
  let v60 : W := v59 + v58
  let v61 : W := UInt256.land (N 1766847064778384329583297500742918515827483896875618958121606201292619775) v40
  let v62 : ByteArray := MachineState.writeBytes (s.memory) (Data.Bytes.natToBytesPadded v61.toNat 32) 800
  let v63 : W := v60 - v61
  let v64 : W := w8 + v63
  let v65 : W := UInt256.mulMod (N 2048) v64 w8
  {s with pc := N 5130,memory := v62,stack := v65::w1::w2::w3::w4::v0::w6::w7::w8::w9::v1::v41::w12::w13::w14::w15::rest}
theorem stage10_run (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions stage10Program {s with pc := N 4939,memory := s.memory,stack := w0::w1::w2::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::rest} = some (stage10Model s w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 rest) := by
  let v0 : W := MachineState.readWord (s.memory) 1216
  let v1 : W := MachineState.readWord (s.memory) 1280
  let v2 : W := w15 * w5
  let v3 : W := MachineState.readWord (s.memory) 160
  let v4 : W := MachineState.readWord (s.memory) 32
  let v5 : W := v4 * v3
  let v6 : W := v5 + v2
  let v7 : W := MachineState.readWord (s.memory) 128
  let v8 : W := MachineState.readWord (s.memory) 64
  let v9 : W := v8 * v7
  let v10 : W := v9 + v6
  let v11 : W := UInt256.mulMod w15 w5 w8
  let v12 : W := MachineState.readWord (s.memory) 160
  let v13 : W := MachineState.readWord (s.memory) 32
  let v14 : W := UInt256.mulMod v13 v12 w8
  let v15 : W := v14 + v11
  let v16 : W := MachineState.readWord (s.memory) 128
  let v17 : W := MachineState.readWord (s.memory) 64
  let v18 : W := UInt256.mulMod v17 v16 w8
  let v19 : W := v18 + v15
  let v20 : W := w0 + v19
  let v21 : W := w0 + v10
  let v22 : W := w11 * w11
  let v23 : W := v22 + v21
  let v24 : W := MachineState.readWord (s.memory) 192
  let v25 : W := w9 * v24
  let v26 : W := v25 + v23
  let v27 : W := MachineState.readWord (s.memory) 0
  let v28 : W := w7 * v27
  let v29 : W := v28 + v26
  let v30 : W := MachineState.readWord (s.memory) 224
  let v31 : W := v30 * w2
  let v32 : W := v31 + v29
  let v33 : W := v0 * w6
  let v34 : W := v33 + v32
  let v35 : W := w4 * w3
  let v36 : W := v35 + v34
  let v37 : W := w13 * v1
  let v38 : W := v37 + v36
  let v39 : W := w12 * w1
  let v40 : W := v39 + v38
  let v41 : W := w11 + w11
  let v42 : W := UInt256.mulMod w11 w11 w8
  let v43 : W := v42 + v20
  let v44 : W := MachineState.readWord (s.memory) 192
  let v45 : W := UInt256.mulMod w9 v44 w8
  let v46 : W := v45 + v43
  let v47 : W := MachineState.readWord (s.memory) 0
  let v48 : W := UInt256.mulMod w7 v47 w8
  let v49 : W := v48 + v46
  let v50 : W := MachineState.readWord (s.memory) 224
  let v51 : W := UInt256.mulMod v50 w2 w8
  let v52 : W := v51 + v49
  let v53 : W := UInt256.mulMod v0 w6 w8
  let v54 : W := v53 + v52
  let v55 : W := UInt256.mulMod w4 w3 w8
  let v56 : W := v55 + v54
  let v57 : W := UInt256.mulMod v1 w13 w8
  let v58 : W := v57 + v56
  let v59 : W := UInt256.mulMod w12 w1 w8
  let v60 : W := v59 + v58
  let v61 : W := UInt256.land (N 1766847064778384329583297500742918515827483896875618958121606201292619775) v40
  let v62 : ByteArray := MachineState.writeBytes (s.memory) (Data.Bytes.natToBytesPadded v61.toNat 32) 800
  let v63 : W := v60 - v61
  let v64 : W := w8 + v63
  let v65 : W := UInt256.mulMod (N 2048) v64 w8
  have h0 : runInstructions stage10Part0Program {s with pc := N 4939,memory := s.memory,stack := w0::w1::w2::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::rest} = some {s with pc := N 4951,memory := s.memory,stack := v0::w8::w15::w0::w1::w2::w3::w4::w5::w6::w7::w8::w9::v1::w11::w12::w13::w14::w15::rest} := by
    simpa only [stage10Part0Model,v0,v1] using stage10Part0_run ({s with memory := s.memory}) w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 rest hcap hact
  have h1 : runInstructions stage10Part1Program {s with pc := N 4951,memory := s.memory,stack := v0::w8::w15::w0::w1::w2::w3::w4::w5::w6::w7::w8::w9::v1::w11::w12::w13::w14::w15::rest} = some {s with pc := N 4961,memory := s.memory,stack := v4::v3::v2::w5::w8::w15::w0::w1::w2::w3::w4::v0::w6::w7::w8::w9::v1::w11::w12::w13::w14::w15::rest} := by
    simpa only [stage10Part1Model,v2,v3,v4] using stage10Part1_run ({s with memory := s.memory}) v0 w8 w15 w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 v1 w11 w12 w13 w14 w15 rest hcap hact
  have h2 : runInstructions stage10Part2Program {s with pc := N 4961,memory := s.memory,stack := v4::v3::v2::w5::w8::w15::w0::w1::w2::w3::w4::v0::w6::w7::w8::w9::v1::w11::w12::w13::w14::w15::rest} = some {s with pc := N 4971,memory := s.memory,stack := v10::w5::w8::w15::w0::w1::w2::w3::w4::v0::w6::w7::w8::w9::v1::w11::w12::w13::w14::w15::rest} := by
    simpa only [stage10Part2Model,v5,v6,v7,v8,v9,v10] using stage10Part2_run ({s with memory := s.memory}) v4 v3 v2 w5 w8 w15 w0 w1 w2 w3 w4 v0 w6 w7 w8 w9 v1 w11 w12 w13 w14 w15 rest hcap hact
  have h3 : runInstructions stage10Part3Program {s with pc := N 4971,memory := s.memory,stack := v10::w5::w8::w15::w0::w1::w2::w3::w4::v0::w6::w7::w8::w9::v1::w11::w12::w13::w14::w15::rest} = some {s with pc := N 4981,memory := s.memory,stack := v14::v11::v10::w0::w1::w2::w3::w4::v0::w6::w7::w8::w9::v1::w11::w12::w13::w14::w15::rest} := by
    simpa only [stage10Part3Model,v11,v12,v13,v14] using stage10Part3_run ({s with memory := s.memory}) v10 w5 w8 w15 w0 w1 w2 w3 w4 v0 w6 w7 w8 w9 v1 w11 w12 w13 w14 w15 rest hcap hact
  have h4 : runInstructions stage10Part4Program {s with pc := N 4981,memory := s.memory,stack := v14::v11::v10::w0::w1::w2::w3::w4::v0::w6::w7::w8::w9::v1::w11::w12::w13::w14::w15::rest} = some {s with pc := N 4991,memory := s.memory,stack := v19::v10::w0::w1::w2::w3::w4::v0::w6::w7::w8::w9::v1::w11::w12::w13::w14::w15::rest} := by
    simpa only [stage10Part4Model,v15,v16,v17,v18,v19] using stage10Part4_run ({s with memory := s.memory}) v14 v11 v10 w0 w1 w2 w3 w4 v0 w6 w7 w8 w9 v1 w11 w12 w13 w14 w15 rest hcap hact
  have h5 : runInstructions stage10Part5Program {s with pc := N 4991,memory := s.memory,stack := v19::v10::w0::w1::w2::w3::w4::v0::w6::w7::w8::w9::v1::w11::w12::w13::w14::w15::rest} = some {s with pc := N 4998,memory := s.memory,stack := v22::v21::v20::w1::w2::w3::w4::v0::w6::w7::w8::w9::v1::w11::w12::w13::w14::w15::rest} := by
    simpa only [stage10Part5Model,v20,v21,v22] using stage10Part5_run ({s with memory := s.memory}) v19 v10 w0 w1 w2 w3 w4 v0 w6 w7 w8 w9 v1 w11 w12 w13 w14 w15 rest hcap hact
  have h6 : runInstructions stage10Part6Program {s with pc := N 4998,memory := s.memory,stack := v22::v21::v20::w1::w2::w3::w4::v0::w6::w7::w8::w9::v1::w11::w12::w13::w14::w15::rest} = some {s with pc := N 5007,memory := s.memory,stack := v27::v26::v20::w1::w2::w3::w4::v0::w6::w7::w8::w9::v1::w11::w12::w13::w14::w15::rest} := by
    simpa only [stage10Part6Model,v23,v24,v25,v26,v27] using stage10Part6_run ({s with memory := s.memory}) v22 v21 v20 w1 w2 w3 w4 v0 w6 w7 w8 w9 v1 w11 w12 w13 w14 w15 rest hcap hact
  have h7 : runInstructions stage10Part7Program {s with pc := N 5007,memory := s.memory,stack := v27::v26::v20::w1::w2::w3::w4::v0::w6::w7::w8::w9::v1::w11::w12::w13::w14::w15::rest} = some {s with pc := N 5016,memory := s.memory,stack := v32::v20::w1::w2::w3::w4::v0::w6::w7::w8::w9::v1::w11::w12::w13::w14::w15::rest} := by
    simpa only [stage10Part7Model,v28,v29,v30,v31,v32] using stage10Part7_run ({s with memory := s.memory}) v27 v26 v20 w1 w2 w3 w4 v0 w6 w7 w8 w9 v1 w11 w12 w13 w14 w15 rest hcap hact
  have h8 : runInstructions stage10Part8Program {s with pc := N 5016,memory := s.memory,stack := v32::v20::w1::w2::w3::w4::v0::w6::w7::w8::w9::v1::w11::w12::w13::w14::w15::rest} = some {s with pc := N 5024,memory := s.memory,stack := v36::v20::w1::w2::w3::w4::v0::w6::w7::w8::w9::v1::w11::w12::w13::w14::w15::rest} := by
    simpa only [stage10Part8Model,v33,v34,v35,v36] using stage10Part8_run ({s with memory := s.memory}) v32 v20 w1 w2 w3 w4 v0 w6 w7 w8 w9 v1 w11 w12 w13 w14 w15 rest hcap hact
  have h9 : runInstructions stage10Part9Program {s with pc := N 5024,memory := s.memory,stack := v36::v20::w1::w2::w3::w4::v0::w6::w7::w8::w9::v1::w11::w12::w13::w14::w15::rest} = some {s with pc := N 5032,memory := s.memory,stack := v40::v20::w1::w2::w3::w4::v0::w6::w7::w8::w9::v1::w11::w12::w13::w14::w15::rest} := by
    simpa only [stage10Part9Model,v37,v38,v39,v40] using stage10Part9_run ({s with memory := s.memory}) v36 v20 w1 w2 w3 w4 v0 w6 w7 w8 w9 v1 w11 w12 w13 w14 w15 rest hcap hact
  have h10 : runInstructions stage10Part10Program {s with pc := N 5032,memory := s.memory,stack := v40::v20::w1::w2::w3::w4::v0::w6::w7::w8::w9::v1::w11::w12::w13::w14::w15::rest} = some {s with pc := N 5039,memory := s.memory,stack := v41::w11::w11::w8::v20::v40::w1::w2::w3::w4::v0::w6::w7::w8::w9::v1::w11::w12::w13::w14::w15::rest} := by
    simpa only [stage10Part10Model,v41] using stage10Part10_run ({s with memory := s.memory}) v40 v20 w1 w2 w3 w4 v0 w6 w7 w8 w9 v1 w11 w12 w13 w14 w15 rest hcap hact
  have h11 : runInstructions stage10Part11Program {s with pc := N 5039,memory := s.memory,stack := v41::w11::w11::w8::v20::v40::w1::w2::w3::w4::v0::w6::w7::w8::w9::v1::w11::w12::w13::w14::w15::rest} = some {s with pc := N 5048,memory := s.memory,stack := w9::v44::w8::v43::v40::w1::w2::w3::w4::v0::w6::w7::w8::w9::v1::v41::w12::w13::w14::w15::rest} := by
    simpa only [stage10Part11Model,v42,v43,v44] using stage10Part11_run ({s with memory := s.memory}) v41 w11 w11 w8 v20 v40 w1 w2 w3 w4 v0 w6 w7 w8 w9 v1 w11 w12 w13 w14 w15 rest hcap hact
  have h12 : runInstructions stage10Part12Program {s with pc := N 5048,memory := s.memory,stack := w9::v44::w8::v43::v40::w1::w2::w3::w4::v0::w6::w7::w8::w9::v1::v41::w12::w13::w14::w15::rest} = some {s with pc := N 5056,memory := s.memory,stack := v49::v40::w1::w2::w3::w4::v0::w6::w7::w8::w9::v1::v41::w12::w13::w14::w15::rest} := by
    simpa only [stage10Part12Model,v45,v46,v47,v48,v49] using stage10Part12_run ({s with memory := s.memory}) w9 v44 w8 v43 v40 w1 w2 w3 w4 v0 w6 w7 w8 w9 v1 v41 w12 w13 w14 w15 rest hcap hact
  have h13 : runInstructions stage10Part13Program {s with pc := N 5056,memory := s.memory,stack := v49::v40::w1::w2::w3::w4::v0::w6::w7::w8::w9::v1::v41::w12::w13::w14::w15::rest} = some {s with pc := N 5065,memory := s.memory,stack := w6::w8::v52::v40::w1::w2::w3::w4::v0::w6::w7::w8::w9::v1::v41::w12::w13::w14::w15::rest} := by
    simpa only [stage10Part13Model,v50,v51,v52] using stage10Part13_run ({s with memory := s.memory}) v49 v40 w1 w2 w3 w4 v0 w6 w7 w8 w9 v1 v41 w12 w13 w14 w15 rest hcap hact
  have h14 : runInstructions stage10Part14Program {s with pc := N 5065,memory := s.memory,stack := w6::w8::v52::v40::w1::w2::w3::w4::v0::w6::w7::w8::w9::v1::v41::w12::w13::w14::w15::rest} = some {s with pc := N 5073,memory := s.memory,stack := v56::v40::w1::w2::w3::w4::v0::w6::w7::w8::w9::v1::v41::w12::w13::w14::w15::rest} := by
    simpa only [stage10Part14Model,v53,v54,v55,v56] using stage10Part14_run ({s with memory := s.memory}) w6 w8 v52 v40 w1 w2 w3 w4 v0 w6 w7 w8 w9 v1 v41 w12 w13 w14 w15 rest hcap hact
  have h15 : runInstructions stage10Part15Program {s with pc := N 5073,memory := s.memory,stack := v56::v40::w1::w2::w3::w4::v0::w6::w7::w8::w9::v1::v41::w12::w13::w14::w15::rest} = some {s with pc := N 5081,memory := s.memory,stack := w12::w1::w8::v58::v40::w1::w2::w3::w4::v0::w6::w7::w8::w9::v1::v41::w12::w13::w14::w15::rest} := by
    simpa only [stage10Part15Model,v57,v58] using stage10Part15_run ({s with memory := s.memory}) v56 v40 w1 w2 w3 w4 v0 w6 w7 w8 w9 v1 v41 w12 w13 w14 w15 rest hcap hact
  have h16 : runInstructions stage10Part16Program {s with pc := N 5081,memory := s.memory,stack := w12::w1::w8::v58::v40::w1::w2::w3::w4::v0::w6::w7::w8::w9::v1::v41::w12::w13::w14::w15::rest} = some {s with pc := N 5121,memory := v62,stack := v61::v60::w1::w2::w3::w4::v0::w6::w7::w8::w9::v1::v41::w12::w13::w14::w15::rest} := by
    simpa only [stage10Part16Model,v59,v60,v61,v62] using stage10Part16_run ({s with memory := s.memory}) w12 w1 w8 v58 v40 w1 w2 w3 w4 v0 w6 w7 w8 w9 v1 v41 w12 w13 w14 w15 rest hcap hact
  have h17 : runInstructions stage10Part17Program {s with pc := N 5121,memory := v62,stack := v61::v60::w1::w2::w3::w4::v0::w6::w7::w8::w9::v1::v41::w12::w13::w14::w15::rest} = some {s with pc := N 5130,memory := v62,stack := v65::w1::w2::w3::w4::v0::w6::w7::w8::w9::v1::v41::w12::w13::w14::w15::rest} := by
    simpa only [stage10Part17Model,v63,v64,v65] using stage10Part17_run ({s with memory := v62}) v61 v60 w1 w2 w3 w4 v0 w6 w7 w8 w9 v1 v41 w12 w13 w14 w15 rest hcap hact
  exact (runInstructions_append_some _ _ _ _ _ h0 (runInstructions_append_some _ _ _ _ _ h1 (runInstructions_append_some _ _ _ _ _ h2 (runInstructions_append_some _ _ _ _ _ h3 (runInstructions_append_some _ _ _ _ _ h4 (runInstructions_append_some _ _ _ _ _ h5 (runInstructions_append_some _ _ _ _ _ h6 (runInstructions_append_some _ _ _ _ _ h7 (runInstructions_append_some _ _ _ _ _ h8 (runInstructions_append_some _ _ _ _ _ h9 (runInstructions_append_some _ _ _ _ _ h10 (runInstructions_append_some _ _ _ _ _ h11 (runInstructions_append_some _ _ _ _ _ h12 (runInstructions_append_some _ _ _ _ _ h13 (runInstructions_append_some _ _ _ _ _ h14 (runInstructions_append_some _ _ _ _ _ h15 (runInstructions_append_some _ _ _ _ _ h16 h17)))))))))))))))))
#print axioms stage10_run
end R9InvConsumeExec
