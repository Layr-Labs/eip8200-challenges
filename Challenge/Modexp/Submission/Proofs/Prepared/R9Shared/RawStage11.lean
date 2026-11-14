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
def stage11Part0Program : List Instr := [.op (.Dup dA15),.op (.Swap sA0),.push 1 128,.op .MLOAD,.op (.Dup dA13),.push 1 160,.op .MLOAD]
def stage11Part0Model (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 : W) (rest : List W) : State :=
  let v0 : W := MachineState.readWord (s.memory) 128
  let v1 : W := MachineState.readWord (s.memory) 160
  {s with pc := N 5145,memory := s.memory,stack := v1::w11::v0::w0::w15::w1::w2::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::rest}
theorem stage11Part0_run (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions stage11Part0Program {s with pc := N 5136,memory := s.memory,stack := w0::w1::w2::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::rest} = some (stage11Part0Model s w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 63) : rest.length+j < 1024 := by omega
  have ha128 : (128 : W).toNat = 128 := rfl
  have hf128 := Monpro.activeWords_fix s 128 32 (by decide) (by norm_num) hact
  have ha160 : (160 : W).toNat = 160 := rfl
  have hf160 := Monpro.activeWords_fix s 160 32 (by decide) (by norm_num) hact
  simp [hz,hzn,stage11Part0Program,stage11Part0Model,runInstructions,runInstr,List.exchange,succ_ofNat_mod,ofNat_add_mod,Nat.add_assoc,State.activeWordsAfterUInt256,literal_eq_ofNat,capacity,ha128,hf128,ha160,hf160]
def stage11Part1Program : List Instr := [.push 1 64,.op .MLOAD,.push 1 32,.op .MLOAD,.op (.Dup dA14),.op (.Dup dA7),.op (.Dup dA2),.op .MULMOD]
def stage11Part1Model (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 : W) (rest : List W) : State :=
  let v0 : W := MachineState.readWord (s.memory) 64
  let v1 : W := MachineState.readWord (s.memory) 32
  let v2 : W := UInt256.mulMod v1 w4 w12
  {s with pc := N 5155,memory := s.memory,stack := v2::v1::v0::w0::w1::w2::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::w16::w17::w18::w19::rest}
theorem stage11Part1_run (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions stage11Part1Program {s with pc := N 5145,memory := s.memory,stack := w0::w1::w2::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::w16::w17::w18::w19::rest} = some (stage11Part1Model s w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 63) : rest.length+j < 1024 := by omega
  have ha32 : (32 : W).toNat = 32 := rfl
  have hf32 := Monpro.activeWords_fix s 32 32 (by decide) (by norm_num) hact
  have ha64 : (64 : W).toNat = 64 := rfl
  have hf64 := Monpro.activeWords_fix s 64 32 (by decide) (by norm_num) hact
  simp [hz,hzn,stage11Part1Program,stage11Part1Model,runInstructions,runInstr,List.exchange,succ_ofNat_mod,ofNat_add_mod,Nat.add_assoc,State.activeWordsAfterUInt256,literal_eq_ofNat,capacity,ha32,hf32,ha64,hf64]
def stage11Part2Program : List Instr := [.op (.Dup dA15),.op (.Dup dA3),.op (.Dup dA5),.op .MULMOD,.op .ADD,.op (.Dup dA15),.op (.Dup dA5),.op (.Dup dA7)]
def stage11Part2Model (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 w20 w21 w22 : W) (rest : List W) : State :=
  let v0 : W := UInt256.mulMod w3 w2 w15
  let v1 : W := v0 + w0
  {s with pc := N 5163,memory := s.memory,stack := w5::w4::w15::v1::w1::w2::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::w16::w17::w18::w19::w20::w21::w22::rest}
theorem stage11Part2_run (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 w20 w21 w22 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions stage11Part2Program {s with pc := N 5155,memory := s.memory,stack := w0::w1::w2::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::w16::w17::w18::w19::w20::w21::w22::rest} = some (stage11Part2Model s w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 w20 w21 w22 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 63) : rest.length+j < 1024 := by omega
  simp [hz,hzn,stage11Part2Program,stage11Part2Model,runInstructions,runInstr,List.exchange,succ_ofNat_mod,ofNat_add_mod,Nat.add_assoc,State.activeWordsAfterUInt256,literal_eq_ofNat,capacity]
def stage11Part3Program : List Instr := [.op .MULMOD,.op .ADD,.op (.Dup dA6),.op .ADD,.op (.Swap sA6),.op .MUL,.op (.Swap sA1),.op .MUL]
def stage11Part3Model (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 w20 w21 w22 w23 w24 w25 : W) (rest : List W) : State :=
  let v0 : W := UInt256.mulMod w0 w1 w2
  let v1 : W := v0 + w3
  let v2 : W := w9 + v1
  let v3 : W := w10 * w4
  let v4 : W := w6 * w5
  {s with pc := N 5171,memory := s.memory,stack := v4::v3::w7::w8::w9::v2::w11::w12::w13::w14::w15::w16::w17::w18::w19::w20::w21::w22::w23::w24::w25::rest}
theorem stage11Part3_run (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 w20 w21 w22 w23 w24 w25 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions stage11Part3Program {s with pc := N 5163,memory := s.memory,stack := w0::w1::w2::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::w16::w17::w18::w19::w20::w21::w22::w23::w24::w25::rest} = some (stage11Part3Model s w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 w20 w21 w22 w23 w24 w25 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 63) : rest.length+j < 1024 := by omega
  simp [hz,hzn,stage11Part3Program,stage11Part3Model,runInstructions,runInstr,List.exchange,succ_ofNat_mod,ofNat_add_mod,Nat.add_assoc,State.activeWordsAfterUInt256,literal_eq_ofNat,capacity]
def stage11Part4Program : List Instr := [.op .ADD,.op (.Swap sA1),.op .MUL,.op .ADD,.op .ADD,.push 0 0,.op .MLOAD,.op (.Dup dA11)]
def stage11Part4Model (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 w20 : W) (rest : List W) : State :=
  let v0 : W := w0 + w1
  let v1 : W := w3 * w2
  let v2 : W := v1 + v0
  let v3 : W := v2 + w4
  let v4 : W := MachineState.readWord (s.memory) 0
  {s with pc := N 5179,memory := s.memory,stack := w14::v4::v3::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::w16::w17::w18::w19::w20::rest}
theorem stage11Part4_run (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 w20 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions stage11Part4Program {s with pc := N 5171,memory := s.memory,stack := w0::w1::w2::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::w16::w17::w18::w19::w20::rest} = some (stage11Part4Model s w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 w20 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 63) : rest.length+j < 1024 := by omega
  have ha0 : (0 : W).toNat = 0 := rfl
  have hf0 := Monpro.activeWords_fix s 0 32 (by decide) (by norm_num) hact
  simp [hz,hzn,stage11Part4Program,stage11Part4Model,runInstructions,runInstr,List.exchange,succ_ofNat_mod,ofNat_add_mod,Nat.add_assoc,State.activeWordsAfterUInt256,literal_eq_ofNat,capacity,ha0,hf0]
def stage11Part5Program : List Instr := [.op .MUL,.op .ADD,.push 1 224,.op .MLOAD,.op (.Dup dA9),.op .MUL,.op .ADD,.op (.Dup dA3)]
def stage11Part5Model (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 : W) (rest : List W) : State :=
  let v0 : W := w0 * w1
  let v1 : W := v0 + w2
  let v2 : W := MachineState.readWord (s.memory) 224
  let v3 : W := w10 * v2
  let v4 : W := v3 + v1
  {s with pc := N 5188,memory := s.memory,stack := w5::v4::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::w16::w17::w18::rest}
theorem stage11Part5_run (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions stage11Part5Program {s with pc := N 5179,memory := s.memory,stack := w0::w1::w2::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::w16::w17::w18::rest} = some (stage11Part5Model s w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 63) : rest.length+j < 1024 := by omega
  have ha224 : (224 : W).toNat = 224 := rfl
  have hf224 := Monpro.activeWords_fix s 224 32 (by decide) (by norm_num) hact
  simp [hz,hzn,stage11Part5Program,stage11Part5Model,runInstructions,runInstr,List.exchange,succ_ofNat_mod,ofNat_add_mod,Nat.add_assoc,State.activeWordsAfterUInt256,literal_eq_ofNat,capacity,ha224,hf224]
def stage11Part6Program : List Instr := [.op (.Dup dA7),.op .MUL,.op .ADD,.op (.Dup dA7),.op (.Dup dA6),.op .MUL,.op .ADD,.op (.Dup dA11)]
def stage11Part6Model (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 : W) (rest : List W) : State :=
  let v0 : W := w7 * w0
  let v1 : W := v0 + w1
  let v2 : W := w6 * w8
  let v3 : W := v2 + v1
  {s with pc := N 5196,memory := s.memory,stack := w12::v3::w2::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::w16::w17::rest}
theorem stage11Part6_run (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions stage11Part6Program {s with pc := N 5188,memory := s.memory,stack := w0::w1::w2::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::w16::w17::rest} = some (stage11Part6Model s w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 63) : rest.length+j < 1024 := by omega
  simp [hz,hzn,stage11Part6Program,stage11Part6Model,runInstructions,runInstr,List.exchange,succ_ofNat_mod,ofNat_add_mod,Nat.add_assoc,State.activeWordsAfterUInt256,literal_eq_ofNat,capacity]
def stage11Part7Program : List Instr := [.op (.Dup dA5),.op .MUL,.op .ADD,.op (.Dup dA14),.op (.Dup dA14),.op .MUL,.op .ADD,.op (.Swap sA0)]
def stage11Part7Model (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 : W) (rest : List W) : State :=
  let v0 : W := w5 * w0
  let v1 : W := v0 + w1
  let v2 : W := w14 * w15
  let v3 : W := v2 + v1
  {s with pc := N 5204,memory := s.memory,stack := w2::v3::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::w16::w17::rest}
theorem stage11Part7_run (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions stage11Part7Program {s with pc := N 5196,memory := s.memory,stack := w0::w1::w2::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::w16::w17::rest} = some (stage11Part7Model s w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 63) : rest.length+j < 1024 := by omega
  simp [hz,hzn,stage11Part7Program,stage11Part7Model,runInstructions,runInstr,List.exchange,succ_ofNat_mod,ofNat_add_mod,Nat.add_assoc,State.activeWordsAfterUInt256,literal_eq_ofNat,capacity]
def stage11Part8Program : List Instr := [.op (.Dup dA9),.push 0 0,.op .MLOAD,.op (.Dup dA12),.op .MULMOD,.op .ADD,.op (.Dup dA9)]
def stage11Part8Model (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 : W) (rest : List W) : State :=
  let v0 : W := MachineState.readWord (s.memory) 0
  let v1 : W := UInt256.mulMod w10 v0 w9
  let v2 : W := v1 + w0
  {s with pc := N 5211,memory := s.memory,stack := w9::v2::w1::w2::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::w16::rest}
theorem stage11Part8_run (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions stage11Part8Program {s with pc := N 5204,memory := s.memory,stack := w0::w1::w2::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::w16::rest} = some (stage11Part8Model s w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 63) : rest.length+j < 1024 := by omega
  have ha0 : (0 : W).toNat = 0 := rfl
  have hf0 := Monpro.activeWords_fix s 0 32 (by decide) (by norm_num) hact
  simp [hz,hzn,stage11Part8Program,stage11Part8Model,runInstructions,runInstr,List.exchange,succ_ofNat_mod,ofNat_add_mod,Nat.add_assoc,State.activeWordsAfterUInt256,literal_eq_ofNat,capacity,ha0,hf0]
def stage11Part9Program : List Instr := [.push 1 224,.op .MLOAD,.op (.Dup dA10),.op .MULMOD,.op .ADD,.op (.Dup dA9),.op (.Dup dA4),.op (.Dup dA8)]
def stage11Part9Model (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 : W) (rest : List W) : State :=
  let v0 : W := MachineState.readWord (s.memory) 224
  let v1 : W := UInt256.mulMod w9 v0 w0
  let v2 : W := v1 + w1
  {s with pc := N 5220,memory := s.memory,stack := w7::w4::w10::v2::w2::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::w16::w17::rest}
theorem stage11Part9_run (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions stage11Part9Program {s with pc := N 5211,memory := s.memory,stack := w0::w1::w2::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::w16::w17::rest} = some (stage11Part9Model s w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 63) : rest.length+j < 1024 := by omega
  have ha224 : (224 : W).toNat = 224 := rfl
  have hf224 := Monpro.activeWords_fix s 224 32 (by decide) (by norm_num) hact
  simp [hz,hzn,stage11Part9Program,stage11Part9Model,runInstructions,runInstr,List.exchange,succ_ofNat_mod,ofNat_add_mod,Nat.add_assoc,State.activeWordsAfterUInt256,literal_eq_ofNat,capacity,ha224,hf224]
def stage11Part10Program : List Instr := [.op .MULMOD,.op .ADD,.op (.Dup dA9),.op (.Dup dA8),.op (.Dup dA7),.op .MULMOD,.op .ADD,.op (.Dup dA9)]
def stage11Part10Model (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 : W) (rest : List W) : State :=
  let v0 : W := UInt256.mulMod w0 w1 w2
  let v1 : W := v0 + w3
  let v2 : W := UInt256.mulMod w8 w10 w12
  let v3 : W := v2 + v1
  {s with pc := N 5228,memory := s.memory,stack := w12::v3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::w16::w17::w18::w19::rest}
theorem stage11Part10_run (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions stage11Part10Program {s with pc := N 5220,memory := s.memory,stack := w0::w1::w2::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::w16::w17::w18::w19::rest} = some (stage11Part10Model s w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 63) : rest.length+j < 1024 := by omega
  simp [hz,hzn,stage11Part10Program,stage11Part10Model,runInstructions,runInstr,List.exchange,succ_ofNat_mod,ofNat_add_mod,Nat.add_assoc,State.activeWordsAfterUInt256,literal_eq_ofNat,capacity]
def stage11Part11Program : List Instr := [.op (.Dup dA5),.op (.Dup dA13),.op .MULMOD,.op .ADD,.op (.Dup dA9),.op (.Dup dA15),.op (.Dup dA15),.op .MULMOD]
def stage11Part11Model (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 : W) (rest : List W) : State :=
  let v0 : W := UInt256.mulMod w12 w5 w0
  let v1 : W := v0 + w1
  let v2 : W := UInt256.mulMod w14 w15 w10
  {s with pc := N 5236,memory := s.memory,stack := v2::v1::w2::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::w16::w17::rest}
theorem stage11Part11_run (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions stage11Part11Program {s with pc := N 5228,memory := s.memory,stack := w0::w1::w2::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::w16::w17::rest} = some (stage11Part11Model s w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 63) : rest.length+j < 1024 := by omega
  simp [hz,hzn,stage11Part11Program,stage11Part11Model,runInstructions,runInstr,List.exchange,succ_ofNat_mod,ofNat_add_mod,Nat.add_assoc,State.activeWordsAfterUInt256,literal_eq_ofNat,capacity]
def stage11Part12Program : List Instr := [.op .ADD,.op (.Swap sA0),.push 30 1766847064778384329583297500742918515827483896875618958121606201292619775,.op .AND,.op (.Dup dA0),.push 2 832,.op .MSTORE,.op (.Dup dA9)]
def stage11Part12Model (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 : W) (rest : List W) : State :=
  let v0 : W := w0 + w1
  let v1 : W := UInt256.land (N 1766847064778384329583297500742918515827483896875618958121606201292619775) w2
  let v2 : ByteArray := MachineState.writeBytes (s.memory) (Data.Bytes.natToBytesPadded v1.toNat 32) 832
  {s with pc := N 5276,memory := v2,stack := w10::v1::v0::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::w16::w17::rest}
theorem stage11Part12_run (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions stage11Part12Program {s with pc := N 5236,memory := s.memory,stack := w0::w1::w2::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::w16::w17::rest} = some (stage11Part12Model s w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 63) : rest.length+j < 1024 := by omega
  have ha832 : (832 : W).toNat = 832 := rfl
  have hf832 := Monpro.activeWords_fix s 832 32 (by decide) (by norm_num) hact
  simp [hz,hzn,stage11Part12Program,stage11Part12Model,runInstructions,runInstr,List.exchange,succ_ofNat_mod,ofNat_add_mod,Nat.add_assoc,State.activeWordsAfterUInt256,literal_eq_ofNat,capacity,ha832,hf832]
def stage11Part13Program : List Instr := [.op (.Swap sA1),.op .SUB,.op (.Dup dA1),.op .ADD,.push 2 2048,.op .MULMOD]
def stage11Part13Model (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 : W) (rest : List W) : State :=
  let v0 : W := w2 - w1
  let v1 : W := w0 + v0
  let v2 : W := UInt256.mulMod (N 2048) v1 w0
  {s with pc := N 5284,memory := s.memory,stack := v2::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::w16::w17::rest}
theorem stage11Part13_run (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions stage11Part13Program {s with pc := N 5276,memory := s.memory,stack := w0::w1::w2::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::w16::w17::rest} = some (stage11Part13Model s w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 63) : rest.length+j < 1024 := by omega
  have ha2048 : (2048 : W).toNat = 2048 := rfl
  have hf2048 := Monpro.activeWords_fix s 2048 32 (by decide) (by norm_num) hact
  simp [hz,hzn,stage11Part13Program,stage11Part13Model,runInstructions,runInstr,List.exchange,succ_ofNat_mod,ofNat_add_mod,Nat.add_assoc,State.activeWordsAfterUInt256,literal_eq_ofNat,capacity,ha2048,hf2048]
def stage11Program : List Instr := (stage11Part0Program++(stage11Part1Program++(stage11Part2Program++(stage11Part3Program++(stage11Part4Program++(stage11Part5Program++(stage11Part6Program++(stage11Part7Program++(stage11Part8Program++(stage11Part9Program++(stage11Part10Program++(stage11Part11Program++(stage11Part12Program++stage11Part13Program)))))))))))))
def stage11Model (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 : W) (rest : List W) : State :=
  let v0 : W := MachineState.readWord (s.memory) 128
  let v1 : W := MachineState.readWord (s.memory) 160
  let v2 : W := MachineState.readWord (s.memory) 64
  let v3 : W := MachineState.readWord (s.memory) 32
  let v4 : W := UInt256.mulMod v3 w15 w8
  let v5 : W := UInt256.mulMod v1 v2 w8
  let v6 : W := v5 + v4
  let v7 : W := UInt256.mulMod v0 w11 w8
  let v8 : W := v7 + v6
  let v9 : W := w0 + v8
  let v10 : W := w15 * v3
  let v11 : W := v1 * v2
  let v12 : W := v11 + v10
  let v13 : W := v0 * w11
  let v14 : W := v13 + v12
  let v15 : W := v14 + w0
  let v16 : W := MachineState.readWord (s.memory) 0
  let v17 : W := w9 * v16
  let v18 : W := v17 + v15
  let v19 : W := MachineState.readWord (s.memory) 224
  let v20 : W := w7 * v19
  let v21 : W := v20 + v18
  let v22 : W := w5 * w2
  let v23 : W := v22 + v21
  let v24 : W := w4 * w6
  let v25 : W := v24 + v23
  let v26 : W := w3 * w10
  let v27 : W := v26 + v25
  let v28 : W := w12 * w13
  let v29 : W := v28 + v27
  let v30 : W := MachineState.readWord (s.memory) 0
  let v31 : W := UInt256.mulMod w9 v30 w8
  let v32 : W := v31 + v9
  let v33 : W := MachineState.readWord (s.memory) 224
  let v34 : W := UInt256.mulMod w7 v33 w8
  let v35 : W := v34 + v32
  let v36 : W := UInt256.mulMod w5 w2 w8
  let v37 : W := v36 + v35
  let v38 : W := UInt256.mulMod w4 w6 w8
  let v39 : W := v38 + v37
  let v40 : W := UInt256.mulMod w10 w3 w8
  let v41 : W := v40 + v39
  let v42 : W := UInt256.mulMod w12 w13 w8
  let v43 : W := v42 + v41
  let v44 : W := UInt256.land (N 1766847064778384329583297500742918515827483896875618958121606201292619775) v29
  let v45 : ByteArray := MachineState.writeBytes (s.memory) (Data.Bytes.natToBytesPadded v44.toNat 32) 832
  let v46 : W := v43 - v44
  let v47 : W := w8 + v46
  let v48 : W := UInt256.mulMod (N 2048) v47 w8
  {s with pc := N 5284,memory := v45,stack := v48::w1::w2::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::rest}
theorem stage11_run (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions stage11Program {s with pc := N 5136,memory := s.memory,stack := w0::w1::w2::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::rest} = some (stage11Model s w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 rest) := by
  let v0 : W := MachineState.readWord (s.memory) 128
  let v1 : W := MachineState.readWord (s.memory) 160
  let v2 : W := MachineState.readWord (s.memory) 64
  let v3 : W := MachineState.readWord (s.memory) 32
  let v4 : W := UInt256.mulMod v3 w15 w8
  let v5 : W := UInt256.mulMod v1 v2 w8
  let v6 : W := v5 + v4
  let v7 : W := UInt256.mulMod v0 w11 w8
  let v8 : W := v7 + v6
  let v9 : W := w0 + v8
  let v10 : W := w15 * v3
  let v11 : W := v1 * v2
  let v12 : W := v11 + v10
  let v13 : W := v0 * w11
  let v14 : W := v13 + v12
  let v15 : W := v14 + w0
  let v16 : W := MachineState.readWord (s.memory) 0
  let v17 : W := w9 * v16
  let v18 : W := v17 + v15
  let v19 : W := MachineState.readWord (s.memory) 224
  let v20 : W := w7 * v19
  let v21 : W := v20 + v18
  let v22 : W := w5 * w2
  let v23 : W := v22 + v21
  let v24 : W := w4 * w6
  let v25 : W := v24 + v23
  let v26 : W := w3 * w10
  let v27 : W := v26 + v25
  let v28 : W := w12 * w13
  let v29 : W := v28 + v27
  let v30 : W := MachineState.readWord (s.memory) 0
  let v31 : W := UInt256.mulMod w9 v30 w8
  let v32 : W := v31 + v9
  let v33 : W := MachineState.readWord (s.memory) 224
  let v34 : W := UInt256.mulMod w7 v33 w8
  let v35 : W := v34 + v32
  let v36 : W := UInt256.mulMod w5 w2 w8
  let v37 : W := v36 + v35
  let v38 : W := UInt256.mulMod w4 w6 w8
  let v39 : W := v38 + v37
  let v40 : W := UInt256.mulMod w10 w3 w8
  let v41 : W := v40 + v39
  let v42 : W := UInt256.mulMod w12 w13 w8
  let v43 : W := v42 + v41
  let v44 : W := UInt256.land (N 1766847064778384329583297500742918515827483896875618958121606201292619775) v29
  let v45 : ByteArray := MachineState.writeBytes (s.memory) (Data.Bytes.natToBytesPadded v44.toNat 32) 832
  let v46 : W := v43 - v44
  let v47 : W := w8 + v46
  let v48 : W := UInt256.mulMod (N 2048) v47 w8
  have h0 : runInstructions stage11Part0Program {s with pc := N 5136,memory := s.memory,stack := w0::w1::w2::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::rest} = some {s with pc := N 5145,memory := s.memory,stack := v1::w11::v0::w0::w15::w1::w2::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::rest} := by
    simpa only [stage11Part0Model,v0,v1] using stage11Part0_run ({s with memory := s.memory}) w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 rest hcap hact
  have h1 : runInstructions stage11Part1Program {s with pc := N 5145,memory := s.memory,stack := v1::w11::v0::w0::w15::w1::w2::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::rest} = some {s with pc := N 5155,memory := s.memory,stack := v4::v3::v2::v1::w11::v0::w0::w15::w1::w2::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::rest} := by
    simpa only [stage11Part1Model,v2,v3,v4] using stage11Part1_run ({s with memory := s.memory}) v1 w11 v0 w0 w15 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 rest hcap hact
  have h2 : runInstructions stage11Part2Program {s with pc := N 5155,memory := s.memory,stack := v4::v3::v2::v1::w11::v0::w0::w15::w1::w2::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::rest} = some {s with pc := N 5163,memory := s.memory,stack := v0::w11::w8::v6::v3::v2::v1::w11::v0::w0::w15::w1::w2::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::rest} := by
    simpa only [stage11Part2Model,v5,v6] using stage11Part2_run ({s with memory := s.memory}) v4 v3 v2 v1 w11 v0 w0 w15 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 rest hcap hact
  have h3 : runInstructions stage11Part3Program {s with pc := N 5163,memory := s.memory,stack := v0::w11::w8::v6::v3::v2::v1::w11::v0::w0::w15::w1::w2::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::rest} = some {s with pc := N 5171,memory := s.memory,stack := v11::v10::w11::v0::w0::v9::w1::w2::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::rest} := by
    simpa only [stage11Part3Model,v7,v8,v9,v10,v11] using stage11Part3_run ({s with memory := s.memory}) v0 w11 w8 v6 v3 v2 v1 w11 v0 w0 w15 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 rest hcap hact
  have h4 : runInstructions stage11Part4Program {s with pc := N 5171,memory := s.memory,stack := v11::v10::w11::v0::w0::v9::w1::w2::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::rest} = some {s with pc := N 5179,memory := s.memory,stack := w9::v16::v15::v9::w1::w2::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::rest} := by
    simpa only [stage11Part4Model,v12,v13,v14,v15,v16] using stage11Part4_run ({s with memory := s.memory}) v11 v10 w11 v0 w0 v9 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 rest hcap hact
  have h5 : runInstructions stage11Part5Program {s with pc := N 5179,memory := s.memory,stack := w9::v16::v15::v9::w1::w2::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::rest} = some {s with pc := N 5188,memory := s.memory,stack := w2::v21::v9::w1::w2::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::rest} := by
    simpa only [stage11Part5Model,v17,v18,v19,v20,v21] using stage11Part5_run ({s with memory := s.memory}) w9 v16 v15 v9 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 rest hcap hact
  have h6 : runInstructions stage11Part6Program {s with pc := N 5188,memory := s.memory,stack := w2::v21::v9::w1::w2::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::rest} = some {s with pc := N 5196,memory := s.memory,stack := w10::v25::v9::w1::w2::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::rest} := by
    simpa only [stage11Part6Model,v22,v23,v24,v25] using stage11Part6_run ({s with memory := s.memory}) w2 v21 v9 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 rest hcap hact
  have h7 : runInstructions stage11Part7Program {s with pc := N 5196,memory := s.memory,stack := w10::v25::v9::w1::w2::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::rest} = some {s with pc := N 5204,memory := s.memory,stack := v9::v29::w1::w2::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::rest} := by
    simpa only [stage11Part7Model,v26,v27,v28,v29] using stage11Part7_run ({s with memory := s.memory}) w10 v25 v9 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 rest hcap hact
  have h8 : runInstructions stage11Part8Program {s with pc := N 5204,memory := s.memory,stack := v9::v29::w1::w2::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::rest} = some {s with pc := N 5211,memory := s.memory,stack := w8::v32::v29::w1::w2::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::rest} := by
    simpa only [stage11Part8Model,v30,v31,v32] using stage11Part8_run ({s with memory := s.memory}) v9 v29 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 rest hcap hact
  have h9 : runInstructions stage11Part9Program {s with pc := N 5211,memory := s.memory,stack := w8::v32::v29::w1::w2::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::rest} = some {s with pc := N 5220,memory := s.memory,stack := w5::w2::w8::v35::v29::w1::w2::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::rest} := by
    simpa only [stage11Part9Model,v33,v34,v35] using stage11Part9_run ({s with memory := s.memory}) w8 v32 v29 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 rest hcap hact
  have h10 : runInstructions stage11Part10Program {s with pc := N 5220,memory := s.memory,stack := w5::w2::w8::v35::v29::w1::w2::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::rest} = some {s with pc := N 5228,memory := s.memory,stack := w8::v39::v29::w1::w2::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::rest} := by
    simpa only [stage11Part10Model,v36,v37,v38,v39] using stage11Part10_run ({s with memory := s.memory}) w5 w2 w8 v35 v29 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 rest hcap hact
  have h11 : runInstructions stage11Part11Program {s with pc := N 5228,memory := s.memory,stack := w8::v39::v29::w1::w2::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::rest} = some {s with pc := N 5236,memory := s.memory,stack := v42::v41::v29::w1::w2::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::rest} := by
    simpa only [stage11Part11Model,v40,v41,v42] using stage11Part11_run ({s with memory := s.memory}) w8 v39 v29 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 rest hcap hact
  have h12 : runInstructions stage11Part12Program {s with pc := N 5236,memory := s.memory,stack := v42::v41::v29::w1::w2::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::rest} = some {s with pc := N 5276,memory := v45,stack := w8::v44::v43::w1::w2::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::rest} := by
    simpa only [stage11Part12Model,v43,v44,v45] using stage11Part12_run ({s with memory := s.memory}) v42 v41 v29 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 rest hcap hact
  have h13 : runInstructions stage11Part13Program {s with pc := N 5276,memory := v45,stack := w8::v44::v43::w1::w2::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::rest} = some {s with pc := N 5284,memory := v45,stack := v48::w1::w2::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::rest} := by
    simpa only [stage11Part13Model,v46,v47,v48] using stage11Part13_run ({s with memory := v45}) w8 v44 v43 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 rest hcap hact
  exact (runInstructions_append_some _ _ _ _ _ h0 (runInstructions_append_some _ _ _ _ _ h1 (runInstructions_append_some _ _ _ _ _ h2 (runInstructions_append_some _ _ _ _ _ h3 (runInstructions_append_some _ _ _ _ _ h4 (runInstructions_append_some _ _ _ _ _ h5 (runInstructions_append_some _ _ _ _ _ h6 (runInstructions_append_some _ _ _ _ _ h7 (runInstructions_append_some _ _ _ _ _ h8 (runInstructions_append_some _ _ _ _ _ h9 (runInstructions_append_some _ _ _ _ _ h10 (runInstructions_append_some _ _ _ _ _ h11 (runInstructions_append_some _ _ _ _ _ h12 h13)))))))))))))
#print axioms stage11_run
end R9InvConsumeExec
