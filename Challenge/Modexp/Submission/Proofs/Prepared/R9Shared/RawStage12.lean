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
def stage12Part0Program : List Instr := [.op (.Dup dA15),.op (.Swap sA0),.op (.Dup dA15),.op (.Dup dA13),.push 1 64,.op .MLOAD]
def stage12Part0Model (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 : W) (rest : List W) : State :=
  let v0 : W := MachineState.readWord (s.memory) 64
  {s with pc := N 5285,memory := s.memory,stack := v0::w11::w14::w0::w15::w1::w2::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::rest}
theorem stage12Part0_run (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions stage12Part0Program {s with pc := N 5278,memory := s.memory,stack := w0::w1::w2::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::rest} = some (stage12Part0Model s w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 63) : rest.length+j < 1024 := by omega
  have ha64 : (64 : W).toNat = 64 := rfl
  have hf64 := Monpro.activeWords_fix s 64 32 (by decide) (by norm_num) hact
  simp [hz,hzn,stage12Part0Program,stage12Part0Model,runInstructions,runInstr,List.exchange,succ_ofNat_mod,ofNat_add_mod,Nat.add_assoc,State.activeWordsAfterUInt256,literal_eq_ofNat,capacity,ha64,hf64]
def stage12Part1Program : List Instr := [.op (.Dup dA12),.op (.Dup dA5),.op (.Dup dA2),.op .MULMOD,.op (.Dup dA13),.op (.Dup dA3),.op (.Dup dA5),.op .MULMOD]
def stage12Part1Model (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 : W) (rest : List W) : State :=
  let v0 : W := UInt256.mulMod w0 w4 w12
  let v1 : W := UInt256.mulMod w2 w1 w12
  {s with pc := N 5293,memory := s.memory,stack := v1::v0::w0::w1::w2::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::w16::w17::w18::w19::rest}
theorem stage12Part1_run (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions stage12Part1Program {s with pc := N 5285,memory := s.memory,stack := w0::w1::w2::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::w16::w17::w18::w19::rest} = some (stage12Part1Model s w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 63) : rest.length+j < 1024 := by omega
  simp [hz,hzn,stage12Part1Program,stage12Part1Model,runInstructions,runInstr,List.exchange,succ_ofNat_mod,ofNat_add_mod,Nat.add_assoc,State.activeWordsAfterUInt256,literal_eq_ofNat,capacity]
def stage12Part2Program : List Instr := [.op .ADD,.op (.Dup dA4),.op .ADD,.op (.Swap sA4),.op .MUL,.op (.Swap sA1),.op .MUL,.op .ADD]
def stage12Part2Model (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 w20 w21 : W) (rest : List W) : State :=
  let v0 : W := w0 + w1
  let v1 : W := w5 + v0
  let v2 : W := w6 * w2
  let v3 : W := w4 * w3
  let v4 : W := v3 + v2
  {s with pc := N 5301,memory := s.memory,stack := v4::w5::v1::w7::w8::w9::w10::w11::w12::w13::w14::w15::w16::w17::w18::w19::w20::w21::rest}
theorem stage12Part2_run (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 w20 w21 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions stage12Part2Program {s with pc := N 5293,memory := s.memory,stack := w0::w1::w2::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::w16::w17::w18::w19::w20::w21::rest} = some (stage12Part2Model s w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 w20 w21 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 63) : rest.length+j < 1024 := by omega
  simp [hz,hzn,stage12Part2Program,stage12Part2Model,runInstructions,runInstr,List.exchange,succ_ofNat_mod,ofNat_add_mod,Nat.add_assoc,State.activeWordsAfterUInt256,literal_eq_ofNat,capacity]
def stage12Part3Program : List Instr := [.op .ADD,.push 1 128,.op .MLOAD,.op (.Dup dA0),.op .MUL,.op .ADD,.push 1 224,.op .MLOAD]
def stage12Part3Model (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 : W) (rest : List W) : State :=
  let v0 : W := w0 + w1
  let v1 : W := MachineState.readWord (s.memory) 128
  let v2 : W := v1 * v1
  let v3 : W := v2 + v0
  let v4 : W := MachineState.readWord (s.memory) 224
  {s with pc := N 5311,memory := s.memory,stack := v4::v3::w2::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::w16::w17::rest}
theorem stage12Part3_run (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions stage12Part3Program {s with pc := N 5301,memory := s.memory,stack := w0::w1::w2::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::w16::w17::rest} = some (stage12Part3Model s w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 63) : rest.length+j < 1024 := by omega
  have ha128 : (128 : W).toNat = 128 := rfl
  have hf128 := Monpro.activeWords_fix s 128 32 (by decide) (by norm_num) hact
  have ha224 : (224 : W).toNat = 224 := rfl
  have hf224 := Monpro.activeWords_fix s 224 32 (by decide) (by norm_num) hact
  simp [hz,hzn,stage12Part3Program,stage12Part3Model,runInstructions,runInstr,List.exchange,succ_ofNat_mod,ofNat_add_mod,Nat.add_assoc,State.activeWordsAfterUInt256,literal_eq_ofNat,capacity,ha128,hf128,ha224,hf224]
def stage12Part4Program : List Instr := [.op (.Dup dA11),.op .MUL,.op .ADD,.op (.Dup dA6),.op (.Dup dA9),.op .MUL,.op .ADD,.op (.Dup dA3)]
def stage12Part4Model (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 : W) (rest : List W) : State :=
  let v0 : W := w11 * w0
  let v1 : W := v0 + w1
  let v2 : W := w9 * w7
  let v3 : W := v2 + v1
  {s with pc := N 5319,memory := s.memory,stack := w4::v3::w2::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::w16::w17::rest}
theorem stage12Part4_run (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions stage12Part4Program {s with pc := N 5311,memory := s.memory,stack := w0::w1::w2::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::w16::w17::rest} = some (stage12Part4Model s w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 63) : rest.length+j < 1024 := by omega
  simp [hz,hzn,stage12Part4Program,stage12Part4Model,runInstructions,runInstr,List.exchange,succ_ofNat_mod,ofNat_add_mod,Nat.add_assoc,State.activeWordsAfterUInt256,literal_eq_ofNat,capacity]
def stage12Part5Program : List Instr := [.op (.Dup dA6),.op .MUL,.op .ADD,.op (.Dup dA11),.op (.Dup dA8),.op .MUL,.op .ADD,.op (.Dup dA4)]
def stage12Part5Model (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 : W) (rest : List W) : State :=
  let v0 : W := w6 * w0
  let v1 : W := v0 + w1
  let v2 : W := w8 * w12
  let v3 : W := v2 + v1
  {s with pc := N 5327,memory := s.memory,stack := w5::v3::w2::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::w16::w17::rest}
theorem stage12Part5_run (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions stage12Part5Program {s with pc := N 5319,memory := s.memory,stack := w0::w1::w2::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::w16::w17::rest} = some (stage12Part5Model s w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 63) : rest.length+j < 1024 := by omega
  simp [hz,hzn,stage12Part5Program,stage12Part5Model,runInstructions,runInstr,List.exchange,succ_ofNat_mod,ofNat_add_mod,Nat.add_assoc,State.activeWordsAfterUInt256,literal_eq_ofNat,capacity]
def stage12Part6Program : List Instr := [.op (.Dup dA14),.op .MUL,.op .ADD,.op (.Swap sA0),.op (.Dup dA9),.push 1 128,.op .MLOAD,.op (.Dup dA0)]
def stage12Part6Model (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 : W) (rest : List W) : State :=
  let v0 : W := w14 * w0
  let v1 : W := v0 + w1
  let v2 : W := MachineState.readWord (s.memory) 128
  {s with pc := N 5336,memory := s.memory,stack := v2::v2::w10::w2::v1::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::w16::w17::rest}
theorem stage12Part6_run (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions stage12Part6Program {s with pc := N 5327,memory := s.memory,stack := w0::w1::w2::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::w16::w17::rest} = some (stage12Part6Model s w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 63) : rest.length+j < 1024 := by omega
  have ha128 : (128 : W).toNat = 128 := rfl
  have hf128 := Monpro.activeWords_fix s 128 32 (by decide) (by norm_num) hact
  simp [hz,hzn,stage12Part6Program,stage12Part6Model,runInstructions,runInstr,List.exchange,succ_ofNat_mod,ofNat_add_mod,Nat.add_assoc,State.activeWordsAfterUInt256,literal_eq_ofNat,capacity,ha128,hf128]
def stage12Part7Program : List Instr := [.op .MULMOD,.op .ADD,.op (.Dup dA9),.push 1 224,.op .MLOAD,.op (.Dup dA12),.op .MULMOD,.op .ADD]
def stage12Part7Model (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 : W) (rest : List W) : State :=
  let v0 : W := UInt256.mulMod w0 w1 w2
  let v1 : W := v0 + w3
  let v2 : W := MachineState.readWord (s.memory) 224
  let v3 : W := UInt256.mulMod w13 v2 w12
  let v4 : W := v3 + v1
  {s with pc := N 5345,memory := s.memory,stack := v4::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::w16::w17::w18::w19::rest}
theorem stage12Part7_run (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions stage12Part7Program {s with pc := N 5336,memory := s.memory,stack := w0::w1::w2::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::w16::w17::w18::w19::rest} = some (stage12Part7Model s w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 63) : rest.length+j < 1024 := by omega
  have ha224 : (224 : W).toNat = 224 := rfl
  have hf224 := Monpro.activeWords_fix s 224 32 (by decide) (by norm_num) hact
  simp [hz,hzn,stage12Part7Program,stage12Part7Model,runInstructions,runInstr,List.exchange,succ_ofNat_mod,ofNat_add_mod,Nat.add_assoc,State.activeWordsAfterUInt256,literal_eq_ofNat,capacity,ha224,hf224]
def stage12Part8Program : List Instr := [.op (.Dup dA9),.op (.Dup dA7),.op (.Dup dA10),.op .MULMOD,.op .ADD,.op (.Dup dA9),.op (.Dup dA4),.op (.Dup dA7)]
def stage12Part8Model (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 : W) (rest : List W) : State :=
  let v0 : W := UInt256.mulMod w8 w6 w9
  let v1 : W := v0 + w0
  {s with pc := N 5353,memory := s.memory,stack := w5::w3::w9::v1::w1::w2::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::w16::rest}
theorem stage12Part8_run (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions stage12Part8Program {s with pc := N 5345,memory := s.memory,stack := w0::w1::w2::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::w16::rest} = some (stage12Part8Model s w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 63) : rest.length+j < 1024 := by omega
  simp [hz,hzn,stage12Part8Program,stage12Part8Model,runInstructions,runInstr,List.exchange,succ_ofNat_mod,ofNat_add_mod,Nat.add_assoc,State.activeWordsAfterUInt256,literal_eq_ofNat,capacity]
def stage12Part9Program : List Instr := [.op .MULMOD,.op .ADD,.op (.Dup dA9),.op (.Dup dA12),.op (.Dup dA9),.op .MULMOD,.op .ADD,.op (.Dup dA9)]
def stage12Part9Model (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 : W) (rest : List W) : State :=
  let v0 : W := UInt256.mulMod w0 w1 w2
  let v1 : W := v0 + w3
  let v2 : W := UInt256.mulMod w10 w14 w12
  let v3 : W := v2 + v1
  {s with pc := N 5361,memory := s.memory,stack := w12::v3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::w16::w17::w18::w19::rest}
theorem stage12Part9_run (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions stage12Part9Program {s with pc := N 5353,memory := s.memory,stack := w0::w1::w2::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::w16::w17::w18::w19::rest} = some (stage12Part9Model s w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 63) : rest.length+j < 1024 := by omega
  simp [hz,hzn,stage12Part9Program,stage12Part9Model,runInstructions,runInstr,List.exchange,succ_ofNat_mod,ofNat_add_mod,Nat.add_assoc,State.activeWordsAfterUInt256,literal_eq_ofNat,capacity]
def stage12Part10Program : List Instr := [.op (.Dup dA5),.op (.Dup dA15),.op .MULMOD,.op .ADD,.op (.Swap sA0),.push 30 1766847064778384329583297500742918515827483896875618958121606201292619775,.op .AND,.op (.Dup dA0)]
def stage12Part10Model (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 : W) (rest : List W) : State :=
  let v0 : W := UInt256.mulMod w14 w5 w0
  let v1 : W := v0 + w1
  let v2 : W := UInt256.land (N 1766847064778384329583297500742918515827483896875618958121606201292619775) w2
  {s with pc := N 5399,memory := s.memory,stack := v2::v2::v1::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::w16::w17::rest}
theorem stage12Part10_run (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions stage12Part10Program {s with pc := N 5361,memory := s.memory,stack := w0::w1::w2::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::w16::w17::rest} = some (stage12Part10Model s w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 63) : rest.length+j < 1024 := by omega
  simp [hz,hzn,stage12Part10Program,stage12Part10Model,runInstructions,runInstr,List.exchange,succ_ofNat_mod,ofNat_add_mod,Nat.add_assoc,State.activeWordsAfterUInt256,literal_eq_ofNat,capacity]
def stage12Part11Program : List Instr := [.push 1 32,.op .MSTORE,.op (.Dup dA9),.op (.Swap sA1),.op .SUB,.op (.Dup dA1),.op .ADD,.push 2 2048]
def stage12Part11Model (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 : W) (rest : List W) : State :=
  let v0 : ByteArray := MachineState.writeBytes (s.memory) (Data.Bytes.natToBytesPadded w0.toNat 32) 32
  let v1 : W := w2 - w1
  let v2 : W := w10 + v1
  {s with pc := N 5410,memory := v0,stack := (N 2048)::v2::w10::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::w16::w17::rest}
theorem stage12Part11_run (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions stage12Part11Program {s with pc := N 5399,memory := s.memory,stack := w0::w1::w2::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::w16::w17::rest} = some (stage12Part11Model s w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 63) : rest.length+j < 1024 := by omega
  have ha32 : (32 : W).toNat = 32 := rfl
  have hf32 := Monpro.activeWords_fix s 32 32 (by decide) (by norm_num) hact
  have ha2048 : (2048 : W).toNat = 2048 := rfl
  have hf2048 := Monpro.activeWords_fix s 2048 32 (by decide) (by norm_num) hact
  simp [hz,hzn,stage12Part11Program,stage12Part11Model,runInstructions,runInstr,List.exchange,succ_ofNat_mod,ofNat_add_mod,Nat.add_assoc,State.activeWordsAfterUInt256,literal_eq_ofNat,capacity,ha32,hf32,ha2048,hf2048]
def stage12Part12Program : List Instr := [.op .MULMOD]
def stage12Part12Model (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 : W) (rest : List W) : State :=
  let v0 : W := UInt256.mulMod w0 w1 w2
  {s with pc := N 5411,memory := s.memory,stack := v0::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::w16::w17::rest}
theorem stage12Part12_run (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions stage12Part12Program {s with pc := N 5410,memory := s.memory,stack := w0::w1::w2::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::w16::w17::rest} = some (stage12Part12Model s w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 63) : rest.length+j < 1024 := by omega
  simp [hz,hzn,stage12Part12Program,stage12Part12Model,runInstructions,runInstr,List.exchange,succ_ofNat_mod,ofNat_add_mod,Nat.add_assoc,State.activeWordsAfterUInt256,literal_eq_ofNat,capacity]
def stage12Program : List Instr := (stage12Part0Program++(stage12Part1Program++(stage12Part2Program++(stage12Part3Program++(stage12Part4Program++(stage12Part5Program++(stage12Part6Program++(stage12Part7Program++(stage12Part8Program++(stage12Part9Program++(stage12Part10Program++(stage12Part11Program++stage12Part12Program))))))))))))
def stage12Model (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 : W) (rest : List W) : State :=
  let v0 : W := MachineState.readWord (s.memory) 64
  let v1 : W := UInt256.mulMod v0 w15 w8
  let v2 : W := UInt256.mulMod w14 w11 w8
  let v3 : W := v2 + v1
  let v4 : W := w0 + v3
  let v5 : W := w15 * v0
  let v6 : W := w14 * w11
  let v7 : W := v6 + v5
  let v8 : W := v7 + w0
  let v9 : W := MachineState.readWord (s.memory) 128
  let v10 : W := v9 * v9
  let v11 : W := v10 + v8
  let v12 : W := MachineState.readWord (s.memory) 224
  let v13 : W := w9 * v12
  let v14 : W := v13 + v11
  let v15 : W := w7 * w5
  let v16 : W := v15 + v14
  let v17 : W := w4 * w2
  let v18 : W := v17 + v16
  let v19 : W := w6 * w10
  let v20 : W := v19 + v18
  let v21 : W := w12 * w3
  let v22 : W := v21 + v20
  let v23 : W := MachineState.readWord (s.memory) 128
  let v24 : W := UInt256.mulMod v23 v23 w8
  let v25 : W := v24 + v4
  let v26 : W := MachineState.readWord (s.memory) 224
  let v27 : W := UInt256.mulMod w9 v26 w8
  let v28 : W := v27 + v25
  let v29 : W := UInt256.mulMod w7 w5 w8
  let v30 : W := v29 + v28
  let v31 : W := UInt256.mulMod w4 w2 w8
  let v32 : W := v31 + v30
  let v33 : W := UInt256.mulMod w6 w10 w8
  let v34 : W := v33 + v32
  let v35 : W := UInt256.mulMod w12 w3 w8
  let v36 : W := v35 + v34
  let v37 : W := UInt256.land (N 1766847064778384329583297500742918515827483896875618958121606201292619775) v22
  let v38 : ByteArray := MachineState.writeBytes (s.memory) (Data.Bytes.natToBytesPadded v37.toNat 32) 32
  let v39 : W := v36 - v37
  let v40 : W := w8 + v39
  let v41 : W := UInt256.mulMod (N 2048) v40 w8
  {s with pc := N 5411,memory := v38,stack := v41::w1::w2::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::rest}
theorem stage12_run (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions stage12Program {s with pc := N 5278,memory := s.memory,stack := w0::w1::w2::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::rest} = some (stage12Model s w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 rest) := by
  let v0 : W := MachineState.readWord (s.memory) 64
  let v1 : W := UInt256.mulMod v0 w15 w8
  let v2 : W := UInt256.mulMod w14 w11 w8
  let v3 : W := v2 + v1
  let v4 : W := w0 + v3
  let v5 : W := w15 * v0
  let v6 : W := w14 * w11
  let v7 : W := v6 + v5
  let v8 : W := v7 + w0
  let v9 : W := MachineState.readWord (s.memory) 128
  let v10 : W := v9 * v9
  let v11 : W := v10 + v8
  let v12 : W := MachineState.readWord (s.memory) 224
  let v13 : W := w9 * v12
  let v14 : W := v13 + v11
  let v15 : W := w7 * w5
  let v16 : W := v15 + v14
  let v17 : W := w4 * w2
  let v18 : W := v17 + v16
  let v19 : W := w6 * w10
  let v20 : W := v19 + v18
  let v21 : W := w12 * w3
  let v22 : W := v21 + v20
  let v23 : W := MachineState.readWord (s.memory) 128
  let v24 : W := UInt256.mulMod v23 v23 w8
  let v25 : W := v24 + v4
  let v26 : W := MachineState.readWord (s.memory) 224
  let v27 : W := UInt256.mulMod w9 v26 w8
  let v28 : W := v27 + v25
  let v29 : W := UInt256.mulMod w7 w5 w8
  let v30 : W := v29 + v28
  let v31 : W := UInt256.mulMod w4 w2 w8
  let v32 : W := v31 + v30
  let v33 : W := UInt256.mulMod w6 w10 w8
  let v34 : W := v33 + v32
  let v35 : W := UInt256.mulMod w12 w3 w8
  let v36 : W := v35 + v34
  let v37 : W := UInt256.land (N 1766847064778384329583297500742918515827483896875618958121606201292619775) v22
  let v38 : ByteArray := MachineState.writeBytes (s.memory) (Data.Bytes.natToBytesPadded v37.toNat 32) 32
  let v39 : W := v36 - v37
  let v40 : W := w8 + v39
  let v41 : W := UInt256.mulMod (N 2048) v40 w8
  have h0 : runInstructions stage12Part0Program {s with pc := N 5278,memory := s.memory,stack := w0::w1::w2::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::rest} = some {s with pc := N 5285,memory := s.memory,stack := v0::w11::w14::w0::w15::w1::w2::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::rest} := by
    simpa only [stage12Part0Model,v0] using stage12Part0_run ({s with memory := s.memory}) w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 rest hcap hact
  have h1 : runInstructions stage12Part1Program {s with pc := N 5285,memory := s.memory,stack := v0::w11::w14::w0::w15::w1::w2::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::rest} = some {s with pc := N 5293,memory := s.memory,stack := v2::v1::v0::w11::w14::w0::w15::w1::w2::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::rest} := by
    simpa only [stage12Part1Model,v1,v2] using stage12Part1_run ({s with memory := s.memory}) v0 w11 w14 w0 w15 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 rest hcap hact
  have h2 : runInstructions stage12Part2Program {s with pc := N 5293,memory := s.memory,stack := v2::v1::v0::w11::w14::w0::w15::w1::w2::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::rest} = some {s with pc := N 5301,memory := s.memory,stack := v7::w0::v4::w1::w2::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::rest} := by
    simpa only [stage12Part2Model,v3,v4,v5,v6,v7] using stage12Part2_run ({s with memory := s.memory}) v2 v1 v0 w11 w14 w0 w15 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 rest hcap hact
  have h3 : runInstructions stage12Part3Program {s with pc := N 5301,memory := s.memory,stack := v7::w0::v4::w1::w2::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::rest} = some {s with pc := N 5311,memory := s.memory,stack := v12::v11::v4::w1::w2::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::rest} := by
    simpa only [stage12Part3Model,v8,v9,v10,v11,v12] using stage12Part3_run ({s with memory := s.memory}) v7 w0 v4 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 rest hcap hact
  have h4 : runInstructions stage12Part4Program {s with pc := N 5311,memory := s.memory,stack := v12::v11::v4::w1::w2::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::rest} = some {s with pc := N 5319,memory := s.memory,stack := w2::v16::v4::w1::w2::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::rest} := by
    simpa only [stage12Part4Model,v13,v14,v15,v16] using stage12Part4_run ({s with memory := s.memory}) v12 v11 v4 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 rest hcap hact
  have h5 : runInstructions stage12Part5Program {s with pc := N 5319,memory := s.memory,stack := w2::v16::v4::w1::w2::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::rest} = some {s with pc := N 5327,memory := s.memory,stack := w3::v20::v4::w1::w2::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::rest} := by
    simpa only [stage12Part5Model,v17,v18,v19,v20] using stage12Part5_run ({s with memory := s.memory}) w2 v16 v4 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 rest hcap hact
  have h6 : runInstructions stage12Part6Program {s with pc := N 5327,memory := s.memory,stack := w3::v20::v4::w1::w2::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::rest} = some {s with pc := N 5336,memory := s.memory,stack := v23::v23::w8::v4::v22::w1::w2::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::rest} := by
    simpa only [stage12Part6Model,v21,v22,v23] using stage12Part6_run ({s with memory := s.memory}) w3 v20 v4 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 rest hcap hact
  have h7 : runInstructions stage12Part7Program {s with pc := N 5336,memory := s.memory,stack := v23::v23::w8::v4::v22::w1::w2::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::rest} = some {s with pc := N 5345,memory := s.memory,stack := v28::v22::w1::w2::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::rest} := by
    simpa only [stage12Part7Model,v24,v25,v26,v27,v28] using stage12Part7_run ({s with memory := s.memory}) v23 v23 w8 v4 v22 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 rest hcap hact
  have h8 : runInstructions stage12Part8Program {s with pc := N 5345,memory := s.memory,stack := v28::v22::w1::w2::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::rest} = some {s with pc := N 5353,memory := s.memory,stack := w4::w2::w8::v30::v22::w1::w2::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::rest} := by
    simpa only [stage12Part8Model,v29,v30] using stage12Part8_run ({s with memory := s.memory}) v28 v22 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 rest hcap hact
  have h9 : runInstructions stage12Part9Program {s with pc := N 5353,memory := s.memory,stack := w4::w2::w8::v30::v22::w1::w2::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::rest} = some {s with pc := N 5361,memory := s.memory,stack := w8::v34::v22::w1::w2::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::rest} := by
    simpa only [stage12Part9Model,v31,v32,v33,v34] using stage12Part9_run ({s with memory := s.memory}) w4 w2 w8 v30 v22 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 rest hcap hact
  have h10 : runInstructions stage12Part10Program {s with pc := N 5361,memory := s.memory,stack := w8::v34::v22::w1::w2::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::rest} = some {s with pc := N 5399,memory := s.memory,stack := v37::v37::v36::w1::w2::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::rest} := by
    simpa only [stage12Part10Model,v35,v36,v37] using stage12Part10_run ({s with memory := s.memory}) w8 v34 v22 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 rest hcap hact
  have h11 : runInstructions stage12Part11Program {s with pc := N 5399,memory := s.memory,stack := v37::v37::v36::w1::w2::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::rest} = some {s with pc := N 5410,memory := v38,stack := (N 2048)::v40::w8::w1::w2::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::rest} := by
    simpa only [stage12Part11Model,v38,v39,v40] using stage12Part11_run ({s with memory := s.memory}) v37 v37 v36 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 rest hcap hact
  have h12 : runInstructions stage12Part12Program {s with pc := N 5410,memory := v38,stack := (N 2048)::v40::w8::w1::w2::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::rest} = some {s with pc := N 5411,memory := v38,stack := v41::w1::w2::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::rest} := by
    simpa only [stage12Part12Model,v41] using stage12Part12_run ({s with memory := v38}) (N 2048) v40 w8 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 rest hcap hact
  exact (runInstructions_append_some _ _ _ _ _ h0 (runInstructions_append_some _ _ _ _ _ h1 (runInstructions_append_some _ _ _ _ _ h2 (runInstructions_append_some _ _ _ _ _ h3 (runInstructions_append_some _ _ _ _ _ h4 (runInstructions_append_some _ _ _ _ _ h5 (runInstructions_append_some _ _ _ _ _ h6 (runInstructions_append_some _ _ _ _ _ h7 (runInstructions_append_some _ _ _ _ _ h8 (runInstructions_append_some _ _ _ _ _ h9 (runInstructions_append_some _ _ _ _ _ h10 (runInstructions_append_some _ _ _ _ _ h11 h12))))))))))))
#print axioms stage12_run
end R9InvConsumeExec
