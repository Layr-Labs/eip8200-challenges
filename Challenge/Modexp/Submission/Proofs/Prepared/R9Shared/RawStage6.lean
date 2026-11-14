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
def stage6Part0Program : List Instr :=
  [
  .push 1 128,
   .op .MLOAD,
   .op (.Dup ⟨9,by decide⟩),
   .push 2 768,
   .op .MLOAD,
   .op (.Dup ⟨0,by decide⟩),
   .op (.Dup ⟨3,by decide⟩),
   .op .MUL]
def stage6Part0Model (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 : W) (rest : List W) : State :=
  let v0 : W := MachineState.readWord (s.memory) 128
  let v1 : W := MachineState.readWord (s.memory) 768
  let v2 : W := v0 * v1
  {s with pc := N 4134,memory := s.memory,stack := v2::v1::w8::v0::w0::w1::w2::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::rest}
theorem stage6Part0_run (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions stage6Part0Program {s with pc := N 4123,memory := s.memory,stack := w0::w1::w2::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::rest} = some (stage6Part0Model s w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 63) : rest.length+j < 1024 := by omega
  have ha128 : (128 : W).toNat = 128 := rfl
  have hf128 := Monpro.activeWords_fix s 128 32 (by decide) (by norm_num) hact
  have ha768 : (768 : W).toNat = 768 := rfl
  have hf768 := Monpro.activeWords_fix s 768 32 (by decide) (by norm_num) hact
  simp [hz,hzn,stage6Part0Program,stage6Part0Model,runInstructions,runInstr,List.exchange,succ_ofNat_mod,ofNat_add_mod,Nat.add_assoc,State.activeWordsAfterUInt256,literal_eq_ofNat,capacity,ha128,hf128,ha768,hf768]
def stage6Part1Program : List Instr :=
  [
  .op (.Dup ⟨15,by decide⟩),
   .op (.Dup ⟨9,by decide⟩),
   .op .MUL,
   .op .ADD,
   .push 1 64,
   .op .MLOAD,
   .op (.Dup ⟨10,by decide⟩)]
def stage6Part1Model (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 : W) (rest : List W) : State :=
  let v0 : W := w8 * w15
  let v1 : W := v0 + w0
  let v2 : W := MachineState.readWord (s.memory) 64
  {s with pc := N 4142,memory := s.memory,stack := w9::v2::v1::w1::w2::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::w16::w17::w18::w19::rest}
theorem stage6Part1_run (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions stage6Part1Program {s with pc := N 4134,memory := s.memory,stack := w0::w1::w2::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::w16::w17::w18::w19::rest} = some (stage6Part1Model s w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 63) : rest.length+j < 1024 := by omega
  have ha64 : (64 : W).toNat = 64 := rfl
  have hf64 := Monpro.activeWords_fix s 64 32 (by decide) (by norm_num) hact
  simp [hz,hzn,stage6Part1Program,stage6Part1Model,runInstructions,runInstr,List.exchange,succ_ofNat_mod,ofNat_add_mod,Nat.add_assoc,State.activeWordsAfterUInt256,literal_eq_ofNat,capacity,ha64,hf64]
def stage6Part2Program : List Instr :=
  [
  .op .MUL,
   .op .ADD,
   .op (.Swap ⟨2,by decide⟩),
   .op .MULMOD,
   .op (.Dup ⟨10,by decide⟩),
   .op (.Dup ⟨14,by decide⟩),
   .op (.Dup ⟨8,by decide⟩)]
def stage6Part2Model (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 w20 w21 : W) (rest : List W) : State :=
  let v0 : W := w0 * w1
  let v1 : W := v0 + w2
  let v2 : W := UInt256.mulMod w5 w3 w4
  {s with pc := N 4149,memory := s.memory,stack := w10::w17::w14::v2::v1::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::w16::w17::w18::w19::w20::w21::rest}
theorem stage6Part2_run (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 w20 w21 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions stage6Part2Program {s with pc := N 4142,memory := s.memory,stack := w0::w1::w2::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::w16::w17::w18::w19::w20::w21::rest} = some (stage6Part2Model s w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 w20 w21 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 63) : rest.length+j < 1024 := by omega
  simp [hz,hzn,stage6Part2Program,stage6Part2Model,runInstructions,runInstr,List.exchange,succ_ofNat_mod,ofNat_add_mod,Nat.add_assoc,State.activeWordsAfterUInt256,literal_eq_ofNat,capacity]
def stage6Part3Program : List Instr :=
  [
  .op .MULMOD,
   .op .ADD,
   .op (.Dup ⟨10,by decide⟩),
   .push 1 64,
   .op .MLOAD,
   .op (.Dup ⟨9,by decide⟩),
   .op .MULMOD,
   .op .ADD]
def stage6Part3Model (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 w20 : W) (rest : List W) : State :=
  let v0 : W := UInt256.mulMod w0 w1 w2
  let v1 : W := v0 + w3
  let v2 : W := MachineState.readWord (s.memory) 64
  let v3 : W := UInt256.mulMod w10 v2 w13
  let v4 : W := v3 + v1
  {s with pc := N 4158,memory := s.memory,stack := v4::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::w16::w17::w18::w19::w20::rest}
theorem stage6Part3_run (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 w20 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions stage6Part3Program {s with pc := N 4149,memory := s.memory,stack := w0::w1::w2::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::w16::w17::w18::w19::w20::rest} = some (stage6Part3Model s w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 w20 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 63) : rest.length+j < 1024 := by omega
  have ha64 : (64 : W).toNat = 64 := rfl
  have hf64 := Monpro.activeWords_fix s 64 32 (by decide) (by norm_num) hact
  simp [hz,hzn,stage6Part3Program,stage6Part3Model,runInstructions,runInstr,List.exchange,succ_ofNat_mod,ofNat_add_mod,Nat.add_assoc,State.activeWordsAfterUInt256,literal_eq_ofNat,capacity,ha64,hf64]
def stage6Part4Program : List Instr :=
  [
  .op (.Dup ⟨2,by decide⟩),
   .op .ADD,
   .op (.Swap ⟨1,by decide⟩),
   .op .ADD,
   .push 1 32,
   .op .MLOAD,
   .op (.Dup ⟨0,by decide⟩),
   .op .MUL]
def stage6Part4Model (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 : W) (rest : List W) : State :=
  let v0 : W := w2 + w0
  let v1 : W := w2 + w1
  let v2 : W := MachineState.readWord (s.memory) 32
  let v3 : W := v2 * v2
  {s with pc := N 4167,memory := s.memory,stack := v3::v1::v0::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::w16::w17::rest}
theorem stage6Part4_run (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions stage6Part4Program {s with pc := N 4158,memory := s.memory,stack := w0::w1::w2::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::w16::w17::rest} = some (stage6Part4Model s w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 63) : rest.length+j < 1024 := by omega
  have ha32 : (32 : W).toNat = 32 := rfl
  have hf32 := Monpro.activeWords_fix s 32 32 (by decide) (by norm_num) hact
  simp [hz,hzn,stage6Part4Program,stage6Part4Model,runInstructions,runInstr,List.exchange,succ_ofNat_mod,ofNat_add_mod,Nat.add_assoc,State.activeWordsAfterUInt256,literal_eq_ofNat,capacity,ha32,hf32]
def stage6Part5Program : List Instr :=
  [
  .op .ADD,
   .op (.Dup ⟨3,by decide⟩),
   .op (.Dup ⟨11,by decide⟩),
   .op .MUL,
   .op .ADD,
   .op (.Dup ⟨7,by decide⟩),
   .op (.Dup ⟨9,by decide⟩),
   .op .MUL]
def stage6Part5Model (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 : W) (rest : List W) : State :=
  let v0 : W := w0 + w1
  let v1 : W := w11 * w4
  let v2 : W := v1 + v0
  let v3 : W := w9 * w8
  {s with pc := N 4175,memory := s.memory,stack := v3::v2::w2::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::w16::w17::rest}
theorem stage6Part5_run (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions stage6Part5Program {s with pc := N 4167,memory := s.memory,stack := w0::w1::w2::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::w16::w17::rest} = some (stage6Part5Model s w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 63) : rest.length+j < 1024 := by omega
  simp [hz,hzn,stage6Part5Program,stage6Part5Model,runInstructions,runInstr,List.exchange,succ_ofNat_mod,ofNat_add_mod,Nat.add_assoc,State.activeWordsAfterUInt256,literal_eq_ofNat,capacity]
def stage6Part6Program : List Instr :=
  [
  .op .ADD,
   .op (.Dup ⟨4,by decide⟩),
   .push 1 192,
   .op .MLOAD,
   .op .MUL,
   .op .ADD,
   .op (.Dup ⟨14,by decide⟩)]
def stage6Part6Model (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 : W) (rest : List W) : State :=
  let v0 : W := w0 + w1
  let v1 : W := MachineState.readWord (s.memory) 192
  let v2 : W := v1 * w5
  let v3 : W := v2 + v0
  {s with pc := N 4183,memory := s.memory,stack := w15::v3::w2::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::w16::w17::rest}
theorem stage6Part6_run (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions stage6Part6Program {s with pc := N 4175,memory := s.memory,stack := w0::w1::w2::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::w16::w17::rest} = some (stage6Part6Model s w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 63) : rest.length+j < 1024 := by omega
  have ha192 : (192 : W).toNat = 192 := rfl
  have hf192 := Monpro.activeWords_fix s 192 32 (by decide) (by norm_num) hact
  simp [hz,hzn,stage6Part6Program,stage6Part6Model,runInstructions,runInstr,List.exchange,succ_ofNat_mod,ofNat_add_mod,Nat.add_assoc,State.activeWordsAfterUInt256,literal_eq_ofNat,capacity,ha192,hf192]
def stage6Part7Program : List Instr :=
  [
  .push 0 0,
   .op .MLOAD,
   .op .MUL,
   .op .ADD,
   .op (.Dup ⟨2,by decide⟩),
   .push 1 224,
   .op .MLOAD,
   .op .MUL]
def stage6Part7Model (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 : W) (rest : List W) : State :=
  let v0 : W := MachineState.readWord (s.memory) 0
  let v1 : W := v0 * w0
  let v2 : W := v1 + w1
  let v3 : W := MachineState.readWord (s.memory) 224
  let v4 : W := v3 * w3
  {s with pc := N 4192,memory := s.memory,stack := v4::v2::w2::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::w16::w17::rest}
theorem stage6Part7_run (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions stage6Part7Program {s with pc := N 4183,memory := s.memory,stack := w0::w1::w2::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::w16::w17::rest} = some (stage6Part7Model s w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 63) : rest.length+j < 1024 := by omega
  have ha0 : (0 : W).toNat = 0 := rfl
  have hf0 := Monpro.activeWords_fix s 0 32 (by decide) (by norm_num) hact
  have ha224 : (224 : W).toNat = 224 := rfl
  have hf224 := Monpro.activeWords_fix s 224 32 (by decide) (by norm_num) hact
  simp [hz,hzn,stage6Part7Program,stage6Part7Model,runInstructions,runInstr,List.exchange,succ_ofNat_mod,ofNat_add_mod,Nat.add_assoc,State.activeWordsAfterUInt256,literal_eq_ofNat,capacity,ha0,hf0,ha224,hf224]
def stage6Part8Program : List Instr :=
  [
  .op .ADD,
   .op (.Dup ⟨11,by decide⟩),
   .push 2 1216,
   .op .MLOAD,
   .op .MUL,
   .op .ADD,
   .op (.Swap ⟨0,by decide⟩),
   .op (.Dup ⟨9,by decide⟩)]
def stage6Part8Model (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 : W) (rest : List W) : State :=
  let v0 : W := w0 + w1
  let v1 : W := MachineState.readWord (s.memory) 1216
  let v2 : W := v1 * w12
  let v3 : W := v2 + v0
  {s with pc := N 4202,memory := s.memory,stack := w10::w2::v3::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::w16::w17::rest}
theorem stage6Part8_run (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions stage6Part8Program {s with pc := N 4192,memory := s.memory,stack := w0::w1::w2::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::w16::w17::rest} = some (stage6Part8Model s w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 63) : rest.length+j < 1024 := by omega
  have ha1216 : (1216 : W).toNat = 1216 := rfl
  have hf1216 := Monpro.activeWords_fix s 1216 32 (by decide) (by norm_num) hact
  simp [hz,hzn,stage6Part8Program,stage6Part8Model,runInstructions,runInstr,List.exchange,succ_ofNat_mod,ofNat_add_mod,Nat.add_assoc,State.activeWordsAfterUInt256,literal_eq_ofNat,capacity,ha1216,hf1216]
def stage6Part9Program : List Instr :=
  [
  .push 1 32,
   .op .MLOAD,
   .op (.Dup ⟨0,by decide⟩),
   .op (.Dup ⟨0,by decide⟩),
   .op (.Dup ⟨0,by decide⟩),
   .op .ADD,
   .push 1 32,
   .op .MSTORE]
def stage6Part9Model (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 : W) (rest : List W) : State :=
  let v0 : W := MachineState.readWord (s.memory) 32
  let v1 : W := v0 + v0
  let v2 : ByteArray := MachineState.writeBytes (s.memory) (Data.Bytes.natToBytesPadded v1.toNat 32) 32
  {s with pc := N 4212,memory := v2,stack := v0::v0::w0::w1::w2::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::w16::w17::rest}
theorem stage6Part9_run (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions stage6Part9Program {s with pc := N 4202,memory := s.memory,stack := w0::w1::w2::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::w16::w17::rest} = some (stage6Part9Model s w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 63) : rest.length+j < 1024 := by omega
  have ha32 : (32 : W).toNat = 32 := rfl
  have hf32 := Monpro.activeWords_fix s 32 32 (by decide) (by norm_num) hact
  simp [hz,hzn,stage6Part9Program,stage6Part9Model,runInstructions,runInstr,List.exchange,succ_ofNat_mod,ofNat_add_mod,Nat.add_assoc,State.activeWordsAfterUInt256,literal_eq_ofNat,capacity,ha32,hf32]
def stage6Part10Program : List Instr :=
  [
  .op .MULMOD,
   .op .ADD,
   .op (.Dup ⟨9,by decide⟩),
   .op (.Dup ⟨4,by decide⟩),
   .op (.Dup ⟨12,by decide⟩),
   .op .MULMOD,
   .op .ADD,
   .op (.Dup ⟨9,by decide⟩)]
def stage6Part10Model (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 : W) (rest : List W) : State :=
  let v0 : W := UInt256.mulMod w0 w1 w2
  let v1 : W := v0 + w3
  let v2 : W := UInt256.mulMod w13 w6 w12
  let v3 : W := v2 + v1
  {s with pc := N 4220,memory := s.memory,stack := w12::v3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::w16::w17::w18::w19::rest}
theorem stage6Part10_run (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions stage6Part10Program {s with pc := N 4212,memory := s.memory,stack := w0::w1::w2::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::w16::w17::w18::w19::rest} = some (stage6Part10Model s w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 63) : rest.length+j < 1024 := by omega
  simp [hz,hzn,stage6Part10Program,stage6Part10Model,runInstructions,runInstr,List.exchange,succ_ofNat_mod,ofNat_add_mod,Nat.add_assoc,State.activeWordsAfterUInt256,literal_eq_ofNat,capacity]
def stage6Part11Program : List Instr :=
  [
  .op (.Dup ⟨8,by decide⟩),
   .op (.Dup ⟨10,by decide⟩),
   .op .MULMOD,
   .op .ADD,
   .op (.Dup ⟨9,by decide⟩),
   .op (.Dup ⟨5,by decide⟩),
   .push 1 192,
   .op .MLOAD]
def stage6Part11Model (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 : W) (rest : List W) : State :=
  let v0 : W := UInt256.mulMod w9 w8 w0
  let v1 : W := v0 + w1
  let v2 : W := MachineState.readWord (s.memory) 192
  {s with pc := N 4229,memory := s.memory,stack := v2::w5::w10::v1::w2::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::w16::w17::rest}
theorem stage6Part11_run (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions stage6Part11Program {s with pc := N 4220,memory := s.memory,stack := w0::w1::w2::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::w16::w17::rest} = some (stage6Part11Model s w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 63) : rest.length+j < 1024 := by omega
  have ha192 : (192 : W).toNat = 192 := rfl
  have hf192 := Monpro.activeWords_fix s 192 32 (by decide) (by norm_num) hact
  simp [hz,hzn,stage6Part11Program,stage6Part11Model,runInstructions,runInstr,List.exchange,succ_ofNat_mod,ofNat_add_mod,Nat.add_assoc,State.activeWordsAfterUInt256,literal_eq_ofNat,capacity,ha192,hf192]
def stage6Part12Program : List Instr :=
  [
  .op .MULMOD,
   .op .ADD,
   .op (.Dup ⟨9,by decide⟩),
   .op (.Dup ⟨15,by decide⟩),
   .push 0 0,
   .op .MLOAD,
   .op .MULMOD,
   .op .ADD]
def stage6Part12Model (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 : W) (rest : List W) : State :=
  let v0 : W := UInt256.mulMod w0 w1 w2
  let v1 : W := v0 + w3
  let v2 : W := MachineState.readWord (s.memory) 0
  let v3 : W := UInt256.mulMod v2 w17 w12
  let v4 : W := v3 + v1
  {s with pc := N 4237,memory := s.memory,stack := v4::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::w16::w17::w18::w19::rest}
theorem stage6Part12_run (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions stage6Part12Program {s with pc := N 4229,memory := s.memory,stack := w0::w1::w2::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::w16::w17::w18::w19::rest} = some (stage6Part12Model s w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 63) : rest.length+j < 1024 := by omega
  have ha0 : (0 : W).toNat = 0 := rfl
  have hf0 := Monpro.activeWords_fix s 0 32 (by decide) (by norm_num) hact
  simp [hz,hzn,stage6Part12Program,stage6Part12Model,runInstructions,runInstr,List.exchange,succ_ofNat_mod,ofNat_add_mod,Nat.add_assoc,State.activeWordsAfterUInt256,literal_eq_ofNat,capacity,ha0,hf0]
def stage6Part13Program : List Instr :=
  [
  .op (.Dup ⟨9,by decide⟩),
   .op (.Dup ⟨3,by decide⟩),
   .push 1 224,
   .op .MLOAD,
   .op .MULMOD,
   .op .ADD,
   .op (.Dup ⟨9,by decide⟩),
   .op (.Dup ⟨12,by decide⟩)]
def stage6Part13Model (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 : W) (rest : List W) : State :=
  let v0 : W := MachineState.readWord (s.memory) 224
  let v1 : W := UInt256.mulMod v0 w2 w9
  let v2 : W := v1 + w0
  {s with pc := N 4246,memory := s.memory,stack := w11::w9::v2::w1::w2::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::w16::rest}
theorem stage6Part13_run (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions stage6Part13Program {s with pc := N 4237,memory := s.memory,stack := w0::w1::w2::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::w16::rest} = some (stage6Part13Model s w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 63) : rest.length+j < 1024 := by omega
  have ha224 : (224 : W).toNat = 224 := rfl
  have hf224 := Monpro.activeWords_fix s 224 32 (by decide) (by norm_num) hact
  simp [hz,hzn,stage6Part13Program,stage6Part13Model,runInstructions,runInstr,List.exchange,succ_ofNat_mod,ofNat_add_mod,Nat.add_assoc,State.activeWordsAfterUInt256,literal_eq_ofNat,capacity,ha224,hf224]
def stage6Part14Program : List Instr :=
  [
  .push 2 1216,
   .op .MLOAD,
   .op .MULMOD,
   .op .ADD,
   .op (.Dup ⟨9,by decide⟩),
   .op (.Dup ⟨14,by decide⟩),
   .push 2 2720,
   .op .MLOAD,
   .op (.Dup ⟨2,by decide⟩)]
def stage6Part14Model (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 : W) (rest : List W) : State :=
  let v0 : W := MachineState.readWord (s.memory) 1216
  let v1 : W := UInt256.mulMod v0 w0 w1
  let v2 : W := v1 + w2
  let v3 : W := MachineState.readWord (s.memory) 2720
  {s with pc := N 4259,memory := s.memory,stack := w11::v3::w15::w11::v2::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::w16::w17::w18::rest}
theorem stage6Part14_run (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions stage6Part14Program {s with pc := N 4246,memory := s.memory,stack := w0::w1::w2::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::w16::w17::w18::rest} = some (stage6Part14Model s w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 63) : rest.length+j < 1024 := by omega
  have ha1216 : (1216 : W).toNat = 1216 := rfl
  have hf1216 := Monpro.activeWords_fix s 1216 32 (by decide) (by norm_num) hact
  have ha2720 : (2720 : W).toNat = 2720 := rfl
  have hf2720 := Monpro.activeWords_fix s 2720 32 (by decide) (by norm_num) hact
  simp [hz,hzn,stage6Part14Program,stage6Part14Model,runInstructions,runInstr,List.exchange,succ_ofNat_mod,ofNat_add_mod,Nat.add_assoc,State.activeWordsAfterUInt256,literal_eq_ofNat,capacity,ha1216,hf1216,ha2720,hf2720]
def stage6Part15Program : List Instr :=
  [
  .op (.Swap ⟨4,by decide⟩),
   .op .MUL,
   .push 30 1766847064778384329583297500742918515827483896875618958121606201292619775,
   .op .AND,
   .op (.Dup ⟨0,by decide⟩),
   .push 2 1248,
   .op .MSTORE,
   .op .MULMOD]
def stage6Part15Model (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 w20 : W) (rest : List W) : State :=
  let v0 : W := w5 * w1
  let v1 : W := UInt256.land (N 1766847064778384329583297500742918515827483896875618958121606201292619775) v0
  let v2 : ByteArray := MachineState.writeBytes (s.memory) (Data.Bytes.natToBytesPadded v1.toNat 32) 1248
  let v3 : W := UInt256.mulMod v1 w2 w3
  {s with pc := N 4299,memory := v2,stack := v3::w4::w0::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::w16::w17::w18::w19::w20::rest}
theorem stage6Part15_run (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 w20 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions stage6Part15Program {s with pc := N 4259,memory := s.memory,stack := w0::w1::w2::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::w16::w17::w18::w19::w20::rest} = some (stage6Part15Model s w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 w20 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 63) : rest.length+j < 1024 := by omega
  have ha1248 : (1248 : W).toNat = 1248 := rfl
  have hf1248 := Monpro.activeWords_fix s 1248 32 (by decide) (by norm_num) hact
  simp [hz,hzn,stage6Part15Program,stage6Part15Model,runInstructions,runInstr,List.exchange,succ_ofNat_mod,ofNat_add_mod,Nat.add_assoc,State.activeWordsAfterUInt256,literal_eq_ofNat,capacity,ha1248,hf1248]
def stage6Part16Program : List Instr :=
  [
  .op .ADD,
   .push 2 2048,
   .op .MULMOD]
def stage6Part16Model (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 : W) (rest : List W) : State :=
  let v0 : W := w0 + w1
  let v1 : W := UInt256.mulMod (N 2048) v0 w2
  {s with pc := N 4304,memory := s.memory,stack := v1::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::w16::w17::rest}
theorem stage6Part16_run (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions stage6Part16Program {s with pc := N 4299,memory := s.memory,stack := w0::w1::w2::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::w16::w17::rest} = some (stage6Part16Model s w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 63) : rest.length+j < 1024 := by omega
  simp [hz,hzn,stage6Part16Program,stage6Part16Model,runInstructions,runInstr,List.exchange,succ_ofNat_mod,ofNat_add_mod,Nat.add_assoc,State.activeWordsAfterUInt256,literal_eq_ofNat,capacity]
def stage6Program : List Instr := (stage6Part0Program++(stage6Part1Program++(stage6Part2Program++(stage6Part3Program++(stage6Part4Program++(stage6Part5Program++(stage6Part6Program++(stage6Part7Program++(stage6Part8Program++(stage6Part9Program++(stage6Part10Program++(stage6Part11Program++(stage6Part12Program++(stage6Part13Program++(stage6Part14Program++(stage6Part15Program++stage6Part16Program))))))))))))))))
def stage6Model (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 : W) (rest : List W) : State :=
  let v0 : W := MachineState.readWord (s.memory) 128
  let v1 : W := MachineState.readWord (s.memory) 768
  let v2 : W := v0 * v1
  let v3 : W := w4 * w11
  let v4 : W := v3 + v2
  let v5 : W := MachineState.readWord (s.memory) 64
  let v6 : W := w5 * v5
  let v7 : W := v6 + v4
  let v8 : W := UInt256.mulMod v0 v1 w8
  let v9 : W := UInt256.mulMod w4 w11 w8
  let v10 : W := v9 + v8
  let v11 : W := MachineState.readWord (s.memory) 64
  let v12 : W := UInt256.mulMod w5 v11 w8
  let v13 : W := v12 + v10
  let v14 : W := w0 + v13
  let v15 : W := w0 + v7
  let v16 : W := MachineState.readWord (s.memory) 32
  let v17 : W := v16 * v16
  let v18 : W := v17 + v15
  let v19 : W := w9 * w2
  let v20 : W := v19 + v18
  let v21 : W := w7 * w6
  let v22 : W := v21 + v20
  let v23 : W := MachineState.readWord (s.memory) 192
  let v24 : W := v23 * w3
  let v25 : W := v24 + v22
  let v26 : W := MachineState.readWord (s.memory) 0
  let v27 : W := v26 * w13
  let v28 : W := v27 + v25
  let v29 : W := MachineState.readWord (s.memory) 224
  let v30 : W := v29 * w1
  let v31 : W := v30 + v28
  let v32 : W := MachineState.readWord (s.memory) 1216
  let v33 : W := v32 * w10
  let v34 : W := v33 + v31
  let v35 : W := MachineState.readWord (s.memory) 32
  let v36 : W := v35 + v35
  let v37 : ByteArray := MachineState.writeBytes (s.memory) (Data.Bytes.natToBytesPadded v36.toNat 32) 32
  let v38 : W := UInt256.mulMod v35 v35 w8
  let v39 : W := v38 + v14
  let v40 : W := UInt256.mulMod w9 w2 w8
  let v41 : W := v40 + v39
  let v42 : W := UInt256.mulMod w7 w6 w8
  let v43 : W := v42 + v41
  let v44 : W := MachineState.readWord v37 192
  let v45 : W := UInt256.mulMod v44 w3 w8
  let v46 : W := v45 + v43
  let v47 : W := MachineState.readWord v37 0
  let v48 : W := UInt256.mulMod v47 w13 w8
  let v49 : W := v48 + v46
  let v50 : W := MachineState.readWord v37 224
  let v51 : W := UInt256.mulMod v50 w1 w8
  let v52 : W := v51 + v49
  let v53 : W := MachineState.readWord v37 1216
  let v54 : W := UInt256.mulMod v53 w10 w8
  let v55 : W := v54 + v52
  let v56 : W := MachineState.readWord v37 2720
  let v57 : W := v34 * v56
  let v58 : W := UInt256.land (N 1766847064778384329583297500742918515827483896875618958121606201292619775) v57
  let v59 : ByteArray := MachineState.writeBytes v37 (Data.Bytes.natToBytesPadded v58.toNat 32) 1248
  let v60 : W := UInt256.mulMod v58 w12 w8
  let v61 : W := v60 + v55
  let v62 : W := UInt256.mulMod (N 2048) v61 w8
  {s with pc := N 4304,memory := v59,stack := v62::w1::w2::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::rest}
theorem stage6_run (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions stage6Program {s with pc := N 4123,memory := s.memory,stack := w0::w1::w2::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::rest} = some (stage6Model s w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 rest) := by
  let v0 : W := MachineState.readWord (s.memory) 128
  let v1 : W := MachineState.readWord (s.memory) 768
  let v2 : W := v0 * v1
  let v3 : W := w4 * w11
  let v4 : W := v3 + v2
  let v5 : W := MachineState.readWord (s.memory) 64
  let v6 : W := w5 * v5
  let v7 : W := v6 + v4
  let v8 : W := UInt256.mulMod v0 v1 w8
  let v9 : W := UInt256.mulMod w4 w11 w8
  let v10 : W := v9 + v8
  let v11 : W := MachineState.readWord (s.memory) 64
  let v12 : W := UInt256.mulMod w5 v11 w8
  let v13 : W := v12 + v10
  let v14 : W := w0 + v13
  let v15 : W := w0 + v7
  let v16 : W := MachineState.readWord (s.memory) 32
  let v17 : W := v16 * v16
  let v18 : W := v17 + v15
  let v19 : W := w9 * w2
  let v20 : W := v19 + v18
  let v21 : W := w7 * w6
  let v22 : W := v21 + v20
  let v23 : W := MachineState.readWord (s.memory) 192
  let v24 : W := v23 * w3
  let v25 : W := v24 + v22
  let v26 : W := MachineState.readWord (s.memory) 0
  let v27 : W := v26 * w13
  let v28 : W := v27 + v25
  let v29 : W := MachineState.readWord (s.memory) 224
  let v30 : W := v29 * w1
  let v31 : W := v30 + v28
  let v32 : W := MachineState.readWord (s.memory) 1216
  let v33 : W := v32 * w10
  let v34 : W := v33 + v31
  let v35 : W := MachineState.readWord (s.memory) 32
  let v36 : W := v35 + v35
  let v37 : ByteArray := MachineState.writeBytes (s.memory) (Data.Bytes.natToBytesPadded v36.toNat 32) 32
  let v38 : W := UInt256.mulMod v35 v35 w8
  let v39 : W := v38 + v14
  let v40 : W := UInt256.mulMod w9 w2 w8
  let v41 : W := v40 + v39
  let v42 : W := UInt256.mulMod w7 w6 w8
  let v43 : W := v42 + v41
  let v44 : W := MachineState.readWord v37 192
  let v45 : W := UInt256.mulMod v44 w3 w8
  let v46 : W := v45 + v43
  let v47 : W := MachineState.readWord v37 0
  let v48 : W := UInt256.mulMod v47 w13 w8
  let v49 : W := v48 + v46
  let v50 : W := MachineState.readWord v37 224
  let v51 : W := UInt256.mulMod v50 w1 w8
  let v52 : W := v51 + v49
  let v53 : W := MachineState.readWord v37 1216
  let v54 : W := UInt256.mulMod v53 w10 w8
  let v55 : W := v54 + v52
  let v56 : W := MachineState.readWord v37 2720
  let v57 : W := v34 * v56
  let v58 : W := UInt256.land (N 1766847064778384329583297500742918515827483896875618958121606201292619775) v57
  let v59 : ByteArray := MachineState.writeBytes v37 (Data.Bytes.natToBytesPadded v58.toNat 32) 1248
  let v60 : W := UInt256.mulMod v58 w12 w8
  let v61 : W := v60 + v55
  let v62 : W := UInt256.mulMod (N 2048) v61 w8
  have h0 : runInstructions stage6Part0Program {s with pc := N 4123,memory := s.memory,stack := w0::w1::w2::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::rest} = some {s with pc := N 4134,memory := s.memory,stack := v2::v1::w8::v0::w0::w1::w2::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::rest} := by
    simpa only [stage6Part0Model,v0,v1,v2] using stage6Part0_run ({s with memory := s.memory}) w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 rest hcap hact
  have h1 : runInstructions stage6Part1Program {s with pc := N 4134,memory := s.memory,stack := v2::v1::w8::v0::w0::w1::w2::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::rest} = some {s with pc := N 4142,memory := s.memory,stack := w5::v5::v4::v1::w8::v0::w0::w1::w2::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::rest} := by
    simpa only [stage6Part1Model,v3,v4,v5] using stage6Part1_run ({s with memory := s.memory}) v2 v1 w8 v0 w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 rest hcap hact
  have h2 : runInstructions stage6Part2Program {s with pc := N 4142,memory := s.memory,stack := w5::v5::v4::v1::w8::v0::w0::w1::w2::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::rest} = some {s with pc := N 4149,memory := s.memory,stack := w4::w11::w8::v8::v7::w0::w1::w2::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::rest} := by
    simpa only [stage6Part2Model,v6,v7,v8] using stage6Part2_run ({s with memory := s.memory}) w5 v5 v4 v1 w8 v0 w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 rest hcap hact
  have h3 : runInstructions stage6Part3Program {s with pc := N 4149,memory := s.memory,stack := w4::w11::w8::v8::v7::w0::w1::w2::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::rest} = some {s with pc := N 4158,memory := s.memory,stack := v13::v7::w0::w1::w2::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::rest} := by
    simpa only [stage6Part3Model,v9,v10,v11,v12,v13] using stage6Part3_run ({s with memory := s.memory}) w4 w11 w8 v8 v7 w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 rest hcap hact
  have h4 : runInstructions stage6Part4Program {s with pc := N 4158,memory := s.memory,stack := v13::v7::w0::w1::w2::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::rest} = some {s with pc := N 4167,memory := s.memory,stack := v17::v15::v14::w1::w2::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::rest} := by
    simpa only [stage6Part4Model,v14,v15,v16,v17] using stage6Part4_run ({s with memory := s.memory}) v13 v7 w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 rest hcap hact
  have h5 : runInstructions stage6Part5Program {s with pc := N 4167,memory := s.memory,stack := v17::v15::v14::w1::w2::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::rest} = some {s with pc := N 4175,memory := s.memory,stack := v21::v20::v14::w1::w2::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::rest} := by
    simpa only [stage6Part5Model,v18,v19,v20,v21] using stage6Part5_run ({s with memory := s.memory}) v17 v15 v14 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 rest hcap hact
  have h6 : runInstructions stage6Part6Program {s with pc := N 4175,memory := s.memory,stack := v21::v20::v14::w1::w2::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::rest} = some {s with pc := N 4183,memory := s.memory,stack := w13::v25::v14::w1::w2::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::rest} := by
    simpa only [stage6Part6Model,v22,v23,v24,v25] using stage6Part6_run ({s with memory := s.memory}) v21 v20 v14 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 rest hcap hact
  have h7 : runInstructions stage6Part7Program {s with pc := N 4183,memory := s.memory,stack := w13::v25::v14::w1::w2::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::rest} = some {s with pc := N 4192,memory := s.memory,stack := v30::v28::v14::w1::w2::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::rest} := by
    simpa only [stage6Part7Model,v26,v27,v28,v29,v30] using stage6Part7_run ({s with memory := s.memory}) w13 v25 v14 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 rest hcap hact
  have h8 : runInstructions stage6Part8Program {s with pc := N 4192,memory := s.memory,stack := v30::v28::v14::w1::w2::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::rest} = some {s with pc := N 4202,memory := s.memory,stack := w8::v14::v34::w1::w2::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::rest} := by
    simpa only [stage6Part8Model,v31,v32,v33,v34] using stage6Part8_run ({s with memory := s.memory}) v30 v28 v14 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 rest hcap hact
  have h9 : runInstructions stage6Part9Program {s with pc := N 4202,memory := s.memory,stack := w8::v14::v34::w1::w2::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::rest} = some {s with pc := N 4212,memory := v37,stack := v35::v35::w8::v14::v34::w1::w2::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::rest} := by
    simpa only [stage6Part9Model,v35,v36,v37] using stage6Part9_run ({s with memory := s.memory}) w8 v14 v34 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 rest hcap hact
  have h10 : runInstructions stage6Part10Program {s with pc := N 4212,memory := v37,stack := v35::v35::w8::v14::v34::w1::w2::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::rest} = some {s with pc := N 4220,memory := v37,stack := w8::v41::v34::w1::w2::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::rest} := by
    simpa only [stage6Part10Model,v38,v39,v40,v41] using stage6Part10_run ({s with memory := v37}) v35 v35 w8 v14 v34 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 rest hcap hact
  have h11 : runInstructions stage6Part11Program {s with pc := N 4220,memory := v37,stack := w8::v41::v34::w1::w2::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::rest} = some {s with pc := N 4229,memory := v37,stack := v44::w3::w8::v43::v34::w1::w2::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::rest} := by
    simpa only [stage6Part11Model,v42,v43,v44] using stage6Part11_run ({s with memory := v37}) w8 v41 v34 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 rest hcap hact
  have h12 : runInstructions stage6Part12Program {s with pc := N 4229,memory := v37,stack := v44::w3::w8::v43::v34::w1::w2::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::rest} = some {s with pc := N 4237,memory := v37,stack := v49::v34::w1::w2::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::rest} := by
    simpa only [stage6Part12Model,v45,v46,v47,v48,v49] using stage6Part12_run ({s with memory := v37}) v44 w3 w8 v43 v34 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 rest hcap hact
  have h13 : runInstructions stage6Part13Program {s with pc := N 4237,memory := v37,stack := v49::v34::w1::w2::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::rest} = some {s with pc := N 4246,memory := v37,stack := w10::w8::v52::v34::w1::w2::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::rest} := by
    simpa only [stage6Part13Model,v50,v51,v52] using stage6Part13_run ({s with memory := v37}) v49 v34 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 rest hcap hact
  have h14 : runInstructions stage6Part14Program {s with pc := N 4246,memory := v37,stack := w10::w8::v52::v34::w1::w2::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::rest} = some {s with pc := N 4259,memory := v37,stack := w8::v56::w12::w8::v55::v34::w1::w2::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::rest} := by
    simpa only [stage6Part14Model,v53,v54,v55,v56] using stage6Part14_run ({s with memory := v37}) w10 w8 v52 v34 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 rest hcap hact
  have h15 : runInstructions stage6Part15Program {s with pc := N 4259,memory := v37,stack := w8::v56::w12::w8::v55::v34::w1::w2::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::rest} = some {s with pc := N 4299,memory := v59,stack := v60::v55::w8::w1::w2::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::rest} := by
    simpa only [stage6Part15Model,v57,v58,v59,v60] using stage6Part15_run ({s with memory := v37}) w8 v56 w12 w8 v55 v34 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 rest hcap hact
  have h16 : runInstructions stage6Part16Program {s with pc := N 4299,memory := v59,stack := v60::v55::w8::w1::w2::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::rest} = some {s with pc := N 4304,memory := v59,stack := v62::w1::w2::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::rest} := by
    simpa only [stage6Part16Model,v61,v62] using stage6Part16_run ({s with memory := v59}) v60 v55 w8 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 rest hcap hact
  exact (runInstructions_append_some _ _ _ _ _ h0 (runInstructions_append_some _ _ _ _ _ h1 (runInstructions_append_some _ _ _ _ _ h2 (runInstructions_append_some _ _ _ _ _ h3 (runInstructions_append_some _ _ _ _ _ h4 (runInstructions_append_some _ _ _ _ _ h5 (runInstructions_append_some _ _ _ _ _ h6 (runInstructions_append_some _ _ _ _ _ h7 (runInstructions_append_some _ _ _ _ _ h8 (runInstructions_append_some _ _ _ _ _ h9 (runInstructions_append_some _ _ _ _ _ h10 (runInstructions_append_some _ _ _ _ _ h11 (runInstructions_append_some _ _ _ _ _ h12 (runInstructions_append_some _ _ _ _ _ h13 (runInstructions_append_some _ _ _ _ _ h14 (runInstructions_append_some _ _ _ _ _ h15 h16))))))))))))))))
end R9InvConsumeExec
