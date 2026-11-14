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
def stage8Part0Program : List Instr :=
  [
  .op (.Dup ⟨15,by decide⟩),
   .op (.Dup ⟨9,by decide⟩),
   .push 2 768,
   .op .MLOAD,
   .op (.Dup ⟨0,by decide⟩),
   .op (.Dup ⟨3,by decide⟩),
   .op .MUL,
   .op (.Dup ⟨8,by decide⟩)]
def stage8Part0Model (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 : W) (rest : List W) : State :=
  let v0 : W := MachineState.readWord (s.memory) 768
  let v1 : W := w15 * v0
  {s with pc := N 4519,memory := s.memory,stack := w4::v1::v0::w8::w15::w0::w1::w2::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::rest}
theorem stage8Part0_run (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions stage8Part0Program {s with pc := N 4509,memory := s.memory,stack := w0::w1::w2::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::rest} = some (stage8Part0Model s w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 63) : rest.length+j < 1024 := by omega
  have ha768 : (768 : W).toNat = 768 := rfl
  have hf768 := Monpro.activeWords_fix s 768 32 (by decide) (by norm_num) hact
  simp [hz,hzn,stage8Part0Program,stage8Part0Model,runInstructions,runInstr,List.exchange,succ_ofNat_mod,ofNat_add_mod,Nat.add_assoc,State.activeWordsAfterUInt256,literal_eq_ofNat,capacity,ha768,hf768]
def stage8Part1Program : List Instr :=
  [
  .push 1 160,
   .op .MLOAD,
   .op .MUL,
   .op .ADD,
   .push 1 128,
   .op .MLOAD,
   .op (.Dup ⟨10,by decide⟩),
   .op .MUL]
def stage8Part1Model (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 w20 : W) (rest : List W) : State :=
  let v0 : W := MachineState.readWord (s.memory) 160
  let v1 : W := v0 * w0
  let v2 : W := v1 + w1
  let v3 : W := MachineState.readWord (s.memory) 128
  let v4 : W := w10 * v3
  {s with pc := N 4529,memory := s.memory,stack := v4::v2::w2::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::w16::w17::w18::w19::w20::rest}
theorem stage8Part1_run (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 w20 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions stage8Part1Program {s with pc := N 4519,memory := s.memory,stack := w0::w1::w2::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::w16::w17::w18::w19::w20::rest} = some (stage8Part1Model s w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 w20 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 63) : rest.length+j < 1024 := by omega
  have ha128 : (128 : W).toNat = 128 := rfl
  have hf128 := Monpro.activeWords_fix s 128 32 (by decide) (by norm_num) hact
  have ha160 : (160 : W).toNat = 160 := rfl
  have hf160 := Monpro.activeWords_fix s 160 32 (by decide) (by norm_num) hact
  simp [hz,hzn,stage8Part1Program,stage8Part1Model,runInstructions,runInstr,List.exchange,succ_ofNat_mod,ofNat_add_mod,Nat.add_assoc,State.activeWordsAfterUInt256,literal_eq_ofNat,capacity,ha128,hf128,ha160,hf160]
def stage8Part2Program : List Instr :=
  [
  .op .ADD,
   .op (.Dup ⟨15,by decide⟩),
   .push 1 32,
   .op .MLOAD,
   .op .MUL,
   .op .ADD,
   .op (.Swap ⟨2,by decide⟩)]
def stage8Part2Model (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 w20 : W) (rest : List W) : State :=
  let v0 : W := w0 + w1
  let v1 : W := MachineState.readWord (s.memory) 32
  let v2 : W := v1 * w16
  let v3 : W := v2 + v0
  {s with pc := N 4537,memory := s.memory,stack := w4::w2::w3::v3::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::w16::w17::w18::w19::w20::rest}
theorem stage8Part2_run (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 w20 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions stage8Part2Program {s with pc := N 4529,memory := s.memory,stack := w0::w1::w2::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::w16::w17::w18::w19::w20::rest} = some (stage8Part2Model s w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 w20 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 63) : rest.length+j < 1024 := by omega
  have ha32 : (32 : W).toNat = 32 := rfl
  have hf32 := Monpro.activeWords_fix s 32 32 (by decide) (by norm_num) hact
  simp [hz,hzn,stage8Part2Program,stage8Part2Model,runInstructions,runInstr,List.exchange,succ_ofNat_mod,ofNat_add_mod,Nat.add_assoc,State.activeWordsAfterUInt256,literal_eq_ofNat,capacity,ha32,hf32]
def stage8Part3Program : List Instr :=
  [
  .op .MULMOD,
   .op (.Dup ⟨10,by decide⟩),
   .push 1 160,
   .op .MLOAD,
   .op (.Dup ⟨8,by decide⟩),
   .op .MULMOD,
   .op .ADD,
   .op (.Dup ⟨10,by decide⟩)]
def stage8Part3Model (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 : W) (rest : List W) : State :=
  let v0 : W := UInt256.mulMod w0 w1 w2
  let v1 : W := MachineState.readWord (s.memory) 160
  let v2 : W := UInt256.mulMod w8 v1 w12
  let v3 : W := v2 + v0
  {s with pc := N 4546,memory := s.memory,stack := w12::v3::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::w16::w17::w18::w19::rest}
theorem stage8Part3_run (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions stage8Part3Program {s with pc := N 4537,memory := s.memory,stack := w0::w1::w2::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::w16::w17::w18::w19::rest} = some (stage8Part3Model s w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 63) : rest.length+j < 1024 := by omega
  have ha160 : (160 : W).toNat = 160 := rfl
  have hf160 := Monpro.activeWords_fix s 160 32 (by decide) (by norm_num) hact
  simp [hz,hzn,stage8Part3Program,stage8Part3Model,runInstructions,runInstr,List.exchange,succ_ofNat_mod,ofNat_add_mod,Nat.add_assoc,State.activeWordsAfterUInt256,literal_eq_ofNat,capacity,ha160,hf160]
def stage8Part4Program : List Instr :=
  [
  .push 1 128,
   .op .MLOAD,
   .op (.Dup ⟨9,by decide⟩),
   .op .MULMOD,
   .op .ADD,
   .op (.Dup ⟨10,by decide⟩),
   .op (.Dup ⟨14,by decide⟩)]
def stage8Part4Model (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 : W) (rest : List W) : State :=
  let v0 : W := MachineState.readWord (s.memory) 128
  let v1 : W := UInt256.mulMod w8 v0 w0
  let v2 : W := v1 + w1
  {s with pc := N 4554,memory := s.memory,stack := w14::w11::v2::w2::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::w16::w17::w18::rest}
theorem stage8Part4_run (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions stage8Part4Program {s with pc := N 4546,memory := s.memory,stack := w0::w1::w2::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::w16::w17::w18::rest} = some (stage8Part4Model s w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 63) : rest.length+j < 1024 := by omega
  have ha128 : (128 : W).toNat = 128 := rfl
  have hf128 := Monpro.activeWords_fix s 128 32 (by decide) (by norm_num) hact
  simp [hz,hzn,stage8Part4Program,stage8Part4Model,runInstructions,runInstr,List.exchange,succ_ofNat_mod,ofNat_add_mod,Nat.add_assoc,State.activeWordsAfterUInt256,literal_eq_ofNat,capacity,ha128,hf128]
def stage8Part5Program : List Instr :=
  [
  .push 1 32,
   .op .MLOAD,
   .op .MULMOD,
   .op .ADD,
   .op (.Dup ⟨2,by decide⟩),
   .op .ADD,
   .op (.Swap ⟨1,by decide⟩),
   .op .ADD]
def stage8Part5Model (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 : W) (rest : List W) : State :=
  let v0 : W := MachineState.readWord (s.memory) 32
  let v1 : W := UInt256.mulMod v0 w0 w1
  let v2 : W := v1 + w2
  let v3 : W := w4 + v2
  let v4 : W := w4 + w3
  {s with pc := N 4563,memory := s.memory,stack := v4::v3::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::w16::w17::w18::w19::rest}
theorem stage8Part5_run (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions stage8Part5Program {s with pc := N 4554,memory := s.memory,stack := w0::w1::w2::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::w16::w17::w18::w19::rest} = some (stage8Part5Model s w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 63) : rest.length+j < 1024 := by omega
  have ha32 : (32 : W).toNat = 32 := rfl
  have hf32 := Monpro.activeWords_fix s 32 32 (by decide) (by norm_num) hact
  simp [hz,hzn,stage8Part5Program,stage8Part5Model,runInstructions,runInstr,List.exchange,succ_ofNat_mod,ofNat_add_mod,Nat.add_assoc,State.activeWordsAfterUInt256,literal_eq_ofNat,capacity,ha32,hf32]
def stage8Part6Program : List Instr :=
  [
  .push 1 64,
   .op .MLOAD,
   .op (.Dup ⟨0,by decide⟩),
   .op .MUL,
   .op .ADD,
   .push 2 1600,
   .op .MLOAD,
   .op (.Swap ⟨10,by decide⟩)]
def stage8Part6Model (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 : W) (rest : List W) : State :=
  let v0 : W := MachineState.readWord (s.memory) 64
  let v1 : W := v0 * v0
  let v2 : W := v1 + w0
  let v3 : W := MachineState.readWord (s.memory) 1600
  {s with pc := N 4574,memory := s.memory,stack := w10::v2::w1::w2::w3::w4::w5::w6::w7::w8::w9::v3::w11::w12::w13::w14::w15::w16::rest}
theorem stage8Part6_run (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions stage8Part6Program {s with pc := N 4563,memory := s.memory,stack := w0::w1::w2::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::w16::rest} = some (stage8Part6Model s w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 63) : rest.length+j < 1024 := by omega
  have ha64 : (64 : W).toNat = 64 := rfl
  have hf64 := Monpro.activeWords_fix s 64 32 (by decide) (by norm_num) hact
  have ha1600 : (1600 : W).toNat = 1600 := rfl
  have hf1600 := Monpro.activeWords_fix s 1600 32 (by decide) (by norm_num) hact
  simp [hz,hzn,stage8Part6Program,stage8Part6Model,runInstructions,runInstr,List.exchange,succ_ofNat_mod,ofNat_add_mod,Nat.add_assoc,State.activeWordsAfterUInt256,literal_eq_ofNat,capacity,ha64,hf64,ha1600,hf1600]
def stage8Part7Program : List Instr :=
  [
  .op (.Dup ⟨11,by decide⟩),
   .op (.Swap ⟨2,by decide⟩),
   .op (.Dup ⟨11,by decide⟩),
   .op (.Dup ⟨2,by decide⟩),
   .op (.Dup ⟨5,by decide⟩),
   .op .MULMOD,
   .op .ADD,
   .op (.Swap ⟨2,by decide⟩)]
def stage8Part7Model (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 : W) (rest : List W) : State :=
  let v0 : W := UInt256.mulMod w11 w0 w10
  let v1 : W := v0 + w2
  {s with pc := N 4582,memory := s.memory,stack := w11::w0::w1::v1::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::w16::w17::rest}
theorem stage8Part7_run (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions stage8Part7Program {s with pc := N 4574,memory := s.memory,stack := w0::w1::w2::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::w16::w17::rest} = some (stage8Part7Model s w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 63) : rest.length+j < 1024 := by omega
  simp [hz,hzn,stage8Part7Program,stage8Part7Model,runInstructions,runInstr,List.exchange,succ_ofNat_mod,ofNat_add_mod,Nat.add_assoc,State.activeWordsAfterUInt256,literal_eq_ofNat,capacity]
def stage8Part8Program : List Instr :=
  [
  .op .MUL,
   .op .ADD,
   .push 2 1088,
   .op .MLOAD,
   .op (.Dup ⟨9,by decide⟩),
   .op .MUL,
   .op .ADD,
   .op (.Dup ⟨3,by decide⟩)]
def stage8Part8Model (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 : W) (rest : List W) : State :=
  let v0 : W := w0 * w1
  let v1 : W := v0 + w2
  let v2 : W := MachineState.readWord (s.memory) 1088
  let v3 : W := w10 * v2
  let v4 : W := v3 + v1
  {s with pc := N 4592,memory := s.memory,stack := w5::v4::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::w16::w17::w18::rest}
theorem stage8Part8_run (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions stage8Part8Program {s with pc := N 4582,memory := s.memory,stack := w0::w1::w2::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::w16::w17::w18::rest} = some (stage8Part8Model s w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 63) : rest.length+j < 1024 := by omega
  have ha1088 : (1088 : W).toNat = 1088 := rfl
  have hf1088 := Monpro.activeWords_fix s 1088 32 (by decide) (by norm_num) hact
  simp [hz,hzn,stage8Part8Program,stage8Part8Model,runInstructions,runInstr,List.exchange,succ_ofNat_mod,ofNat_add_mod,Nat.add_assoc,State.activeWordsAfterUInt256,literal_eq_ofNat,capacity,ha1088,hf1088]
def stage8Part9Program : List Instr :=
  [
  .push 1 192,
   .op .MLOAD,
   .op .MUL,
   .op .ADD,
   .op (.Dup ⟨7,by decide⟩),
   .push 0 0,
   .op .MLOAD,
   .op .MUL]
def stage8Part9Model (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 : W) (rest : List W) : State :=
  let v0 : W := MachineState.readWord (s.memory) 192
  let v1 : W := v0 * w0
  let v2 : W := v1 + w1
  let v3 : W := MachineState.readWord (s.memory) 0
  let v4 : W := v3 * w8
  {s with pc := N 4601,memory := s.memory,stack := v4::v2::w2::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::w16::w17::rest}
theorem stage8Part9_run (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions stage8Part9Program {s with pc := N 4592,memory := s.memory,stack := w0::w1::w2::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::w16::w17::rest} = some (stage8Part9Model s w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 63) : rest.length+j < 1024 := by omega
  have ha0 : (0 : W).toNat = 0 := rfl
  have hf0 := Monpro.activeWords_fix s 0 32 (by decide) (by norm_num) hact
  have ha192 : (192 : W).toNat = 192 := rfl
  have hf192 := Monpro.activeWords_fix s 192 32 (by decide) (by norm_num) hact
  simp [hz,hzn,stage8Part9Program,stage8Part9Model,runInstructions,runInstr,List.exchange,succ_ofNat_mod,ofNat_add_mod,Nat.add_assoc,State.activeWordsAfterUInt256,literal_eq_ofNat,capacity,ha0,hf0,ha192,hf192]
def stage8Part10Program : List Instr :=
  [
  .op .ADD,
   .op (.Dup ⟨4,by decide⟩),
   .push 1 224,
   .op .MLOAD,
   .op .MUL,
   .op .ADD,
   .op (.Dup ⟨14,by decide⟩)]
def stage8Part10Model (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 : W) (rest : List W) : State :=
  let v0 : W := w0 + w1
  let v1 : W := MachineState.readWord (s.memory) 224
  let v2 : W := v1 * w5
  let v3 : W := v2 + v0
  {s with pc := N 4609,memory := s.memory,stack := w15::v3::w2::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::w16::w17::rest}
theorem stage8Part10_run (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions stage8Part10Program {s with pc := N 4601,memory := s.memory,stack := w0::w1::w2::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::w16::w17::rest} = some (stage8Part10Model s w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 63) : rest.length+j < 1024 := by omega
  have ha224 : (224 : W).toNat = 224 := rfl
  have hf224 := Monpro.activeWords_fix s 224 32 (by decide) (by norm_num) hact
  simp [hz,hzn,stage8Part10Program,stage8Part10Model,runInstructions,runInstr,List.exchange,succ_ofNat_mod,ofNat_add_mod,Nat.add_assoc,State.activeWordsAfterUInt256,literal_eq_ofNat,capacity,ha224,hf224]
def stage8Part11Program : List Instr :=
  [
  .push 2 1216,
   .op .MLOAD,
   .op .MUL,
   .op .ADD,
   .op (.Dup ⟨2,by decide⟩),
   .push 2 1248,
   .op .MLOAD,
   .op .MUL]
def stage8Part11Model (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 : W) (rest : List W) : State :=
  let v0 : W := MachineState.readWord (s.memory) 1216
  let v1 : W := v0 * w0
  let v2 : W := v1 + w1
  let v3 : W := MachineState.readWord (s.memory) 1248
  let v4 : W := v3 * w3
  {s with pc := N 4621,memory := s.memory,stack := v4::v2::w2::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::w16::w17::rest}
theorem stage8Part11_run (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions stage8Part11Program {s with pc := N 4609,memory := s.memory,stack := w0::w1::w2::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::w16::w17::rest} = some (stage8Part11Model s w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 63) : rest.length+j < 1024 := by omega
  have ha1216 : (1216 : W).toNat = 1216 := rfl
  have hf1216 := Monpro.activeWords_fix s 1216 32 (by decide) (by norm_num) hact
  have ha1248 : (1248 : W).toNat = 1248 := rfl
  have hf1248 := Monpro.activeWords_fix s 1248 32 (by decide) (by norm_num) hact
  simp [hz,hzn,stage8Part11Program,stage8Part11Model,runInstructions,runInstr,List.exchange,succ_ofNat_mod,ofNat_add_mod,Nat.add_assoc,State.activeWordsAfterUInt256,literal_eq_ofNat,capacity,ha1216,hf1216,ha1248,hf1248]
def stage8Part12Program : List Instr :=
  [
  .op .ADD,
   .op (.Dup ⟨11,by decide⟩),
   .push 2 1280,
   .op .MLOAD,
   .op .MUL,
   .op .ADD,
   .op (.Swap ⟨0,by decide⟩),
   .op (.Dup ⟨9,by decide⟩)]
def stage8Part12Model (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 : W) (rest : List W) : State :=
  let v0 : W := w0 + w1
  let v1 : W := MachineState.readWord (s.memory) 1280
  let v2 : W := v1 * w12
  let v3 : W := v2 + v0
  {s with pc := N 4631,memory := s.memory,stack := w10::w2::v3::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::w16::w17::rest}
theorem stage8Part12_run (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions stage8Part12Program {s with pc := N 4621,memory := s.memory,stack := w0::w1::w2::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::w16::w17::rest} = some (stage8Part12Model s w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 63) : rest.length+j < 1024 := by omega
  have ha1280 : (1280 : W).toNat = 1280 := rfl
  have hf1280 := Monpro.activeWords_fix s 1280 32 (by decide) (by norm_num) hact
  simp [hz,hzn,stage8Part12Program,stage8Part12Model,runInstructions,runInstr,List.exchange,succ_ofNat_mod,ofNat_add_mod,Nat.add_assoc,State.activeWordsAfterUInt256,literal_eq_ofNat,capacity,ha1280,hf1280]
def stage8Part13Program : List Instr :=
  [
  .push 1 64,
   .op .MLOAD,
   .op (.Dup ⟨0,by decide⟩),
   .op (.Dup ⟨0,by decide⟩),
   .op (.Dup ⟨0,by decide⟩),
   .op .ADD,
   .push 1 64,
   .op .MSTORE]
def stage8Part13Model (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 : W) (rest : List W) : State :=
  let v0 : W := MachineState.readWord (s.memory) 64
  let v1 : W := v0 + v0
  let v2 : ByteArray := MachineState.writeBytes (s.memory) (Data.Bytes.natToBytesPadded v1.toNat 32) 64
  {s with pc := N 4641,memory := v2,stack := v0::v0::w0::w1::w2::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::w16::w17::rest}
theorem stage8Part13_run (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions stage8Part13Program {s with pc := N 4631,memory := s.memory,stack := w0::w1::w2::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::w16::w17::rest} = some (stage8Part13Model s w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 63) : rest.length+j < 1024 := by omega
  have ha64 : (64 : W).toNat = 64 := rfl
  have hf64 := Monpro.activeWords_fix s 64 32 (by decide) (by norm_num) hact
  simp [hz,hzn,stage8Part13Program,stage8Part13Model,runInstructions,runInstr,List.exchange,succ_ofNat_mod,ofNat_add_mod,Nat.add_assoc,State.activeWordsAfterUInt256,literal_eq_ofNat,capacity,ha64,hf64]
def stage8Part14Program : List Instr :=
  [
  .op .MULMOD,
   .op .ADD,
   .op (.Dup ⟨9,by decide⟩),
   .push 2 1088,
   .op .MLOAD,
   .op (.Dup ⟨10,by decide⟩),
   .op .MULMOD,
   .op .ADD]
def stage8Part14Model (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 : W) (rest : List W) : State :=
  let v0 : W := UInt256.mulMod w0 w1 w2
  let v1 : W := v0 + w3
  let v2 : W := MachineState.readWord (s.memory) 1088
  let v3 : W := UInt256.mulMod w11 v2 w12
  let v4 : W := v3 + v1
  {s with pc := N 4651,memory := s.memory,stack := v4::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::w16::w17::w18::w19::rest}
theorem stage8Part14_run (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions stage8Part14Program {s with pc := N 4641,memory := s.memory,stack := w0::w1::w2::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::w16::w17::w18::w19::rest} = some (stage8Part14Model s w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 63) : rest.length+j < 1024 := by omega
  have ha1088 : (1088 : W).toNat = 1088 := rfl
  have hf1088 := Monpro.activeWords_fix s 1088 32 (by decide) (by norm_num) hact
  simp [hz,hzn,stage8Part14Program,stage8Part14Model,runInstructions,runInstr,List.exchange,succ_ofNat_mod,ofNat_add_mod,Nat.add_assoc,State.activeWordsAfterUInt256,literal_eq_ofNat,capacity,ha1088,hf1088]
def stage8Part15Program : List Instr :=
  [
  .op (.Dup ⟨9,by decide⟩),
   .op (.Dup ⟨4,by decide⟩),
   .push 1 192,
   .op .MLOAD,
   .op .MULMOD,
   .op .ADD,
   .op (.Dup ⟨9,by decide⟩),
   .op (.Dup ⟨8,by decide⟩)]
def stage8Part15Model (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 : W) (rest : List W) : State :=
  let v0 : W := MachineState.readWord (s.memory) 192
  let v1 : W := UInt256.mulMod v0 w3 w9
  let v2 : W := v1 + w0
  {s with pc := N 4660,memory := s.memory,stack := w7::w9::v2::w1::w2::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::w16::rest}
theorem stage8Part15_run (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions stage8Part15Program {s with pc := N 4651,memory := s.memory,stack := w0::w1::w2::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::w16::rest} = some (stage8Part15Model s w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 63) : rest.length+j < 1024 := by omega
  have ha192 : (192 : W).toNat = 192 := rfl
  have hf192 := Monpro.activeWords_fix s 192 32 (by decide) (by norm_num) hact
  simp [hz,hzn,stage8Part15Program,stage8Part15Model,runInstructions,runInstr,List.exchange,succ_ofNat_mod,ofNat_add_mod,Nat.add_assoc,State.activeWordsAfterUInt256,literal_eq_ofNat,capacity,ha192,hf192]
def stage8Part16Program : List Instr :=
  [
  .push 0 0,
   .op .MLOAD,
   .op .MULMOD,
   .op .ADD,
   .op (.Dup ⟨9,by decide⟩),
   .op (.Dup ⟨5,by decide⟩),
   .push 1 224,
   .op .MLOAD]
def stage8Part16Model (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 : W) (rest : List W) : State :=
  let v0 : W := MachineState.readWord (s.memory) 0
  let v1 : W := UInt256.mulMod v0 w0 w1
  let v2 : W := v1 + w2
  let v3 : W := MachineState.readWord (s.memory) 224
  {s with pc := N 4669,memory := s.memory,stack := v3::w6::w11::v2::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::w16::w17::w18::rest}
theorem stage8Part16_run (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions stage8Part16Program {s with pc := N 4660,memory := s.memory,stack := w0::w1::w2::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::w16::w17::w18::rest} = some (stage8Part16Model s w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 63) : rest.length+j < 1024 := by omega
  have ha0 : (0 : W).toNat = 0 := rfl
  have hf0 := Monpro.activeWords_fix s 0 32 (by decide) (by norm_num) hact
  have ha224 : (224 : W).toNat = 224 := rfl
  have hf224 := Monpro.activeWords_fix s 224 32 (by decide) (by norm_num) hact
  simp [hz,hzn,stage8Part16Program,stage8Part16Model,runInstructions,runInstr,List.exchange,succ_ofNat_mod,ofNat_add_mod,Nat.add_assoc,State.activeWordsAfterUInt256,literal_eq_ofNat,capacity,ha0,hf0,ha224,hf224]
def stage8Part17Program : List Instr :=
  [
  .op .MULMOD,
   .op .ADD,
   .op (.Dup ⟨9,by decide⟩),
   .op (.Dup ⟨15,by decide⟩),
   .push 2 1216,
   .op .MLOAD,
   .op .MULMOD,
   .op .ADD]
def stage8Part17Model (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 : W) (rest : List W) : State :=
  let v0 : W := UInt256.mulMod w0 w1 w2
  let v1 : W := v0 + w3
  let v2 : W := MachineState.readWord (s.memory) 1216
  let v3 : W := UInt256.mulMod v2 w17 w12
  let v4 : W := v3 + v1
  {s with pc := N 4679,memory := s.memory,stack := v4::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::w16::w17::w18::w19::rest}
theorem stage8Part17_run (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions stage8Part17Program {s with pc := N 4669,memory := s.memory,stack := w0::w1::w2::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::w16::w17::w18::w19::rest} = some (stage8Part17Model s w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 63) : rest.length+j < 1024 := by omega
  have ha1216 : (1216 : W).toNat = 1216 := rfl
  have hf1216 := Monpro.activeWords_fix s 1216 32 (by decide) (by norm_num) hact
  simp [hz,hzn,stage8Part17Program,stage8Part17Model,runInstructions,runInstr,List.exchange,succ_ofNat_mod,ofNat_add_mod,Nat.add_assoc,State.activeWordsAfterUInt256,literal_eq_ofNat,capacity,ha1216,hf1216]
def stage8Part18Program : List Instr :=
  [
  .op (.Dup ⟨9,by decide⟩),
   .op (.Dup ⟨3,by decide⟩),
   .push 2 1248,
   .op .MLOAD,
   .op .MULMOD,
   .op .ADD,
   .op (.Dup ⟨9,by decide⟩),
   .op (.Dup ⟨12,by decide⟩)]
def stage8Part18Model (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 : W) (rest : List W) : State :=
  let v0 : W := MachineState.readWord (s.memory) 1248
  let v1 : W := UInt256.mulMod v0 w2 w9
  let v2 : W := v1 + w0
  {s with pc := N 4689,memory := s.memory,stack := w11::w9::v2::w1::w2::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::w16::rest}
theorem stage8Part18_run (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions stage8Part18Program {s with pc := N 4679,memory := s.memory,stack := w0::w1::w2::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::w16::rest} = some (stage8Part18Model s w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 63) : rest.length+j < 1024 := by omega
  have ha1248 : (1248 : W).toNat = 1248 := rfl
  have hf1248 := Monpro.activeWords_fix s 1248 32 (by decide) (by norm_num) hact
  simp [hz,hzn,stage8Part18Program,stage8Part18Model,runInstructions,runInstr,List.exchange,succ_ofNat_mod,ofNat_add_mod,Nat.add_assoc,State.activeWordsAfterUInt256,literal_eq_ofNat,capacity,ha1248,hf1248]
def stage8Part19Program : List Instr :=
  [
  .push 2 1280,
   .op .MLOAD,
   .op .MULMOD,
   .op .ADD,
   .op (.Dup ⟨9,by decide⟩),
   .push 30 1766847064778384329583297500742918515827483896875618958121606201292619775,
   .op (.Dup ⟨3,by decide⟩),
   .push 2 2720,
   .op .MLOAD]
def stage8Part19Model (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 : W) (rest : List W) : State :=
  let v0 : W := MachineState.readWord (s.memory) 1280
  let v1 : W := UInt256.mulMod v0 w0 w1
  let v2 : W := v1 + w2
  let v3 : W := MachineState.readWord (s.memory) 2720
  {s with pc := N 4732,memory := s.memory,stack := v3::w3::(N 1766847064778384329583297500742918515827483896875618958121606201292619775)::w11::v2::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::w16::w17::w18::rest}
theorem stage8Part19_run (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions stage8Part19Program {s with pc := N 4689,memory := s.memory,stack := w0::w1::w2::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::w16::w17::w18::rest} = some (stage8Part19Model s w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 63) : rest.length+j < 1024 := by omega
  have ha1280 : (1280 : W).toNat = 1280 := rfl
  have hf1280 := Monpro.activeWords_fix s 1280 32 (by decide) (by norm_num) hact
  have ha2720 : (2720 : W).toNat = 2720 := rfl
  have hf2720 := Monpro.activeWords_fix s 2720 32 (by decide) (by norm_num) hact
  simp [hz,hzn,stage8Part19Program,stage8Part19Model,runInstructions,runInstr,List.exchange,succ_ofNat_mod,ofNat_add_mod,Nat.add_assoc,State.activeWordsAfterUInt256,literal_eq_ofNat,capacity,ha1280,hf1280,ha2720,hf2720]
def stage8Part20Program : List Instr :=
  [
  .op .MUL,
   .op .AND,
   .op (.Dup ⟨0,by decide⟩),
   .op (.Swap ⟨15,by decide⟩),
   .op .MULMOD,
   .op .ADD,
   .push 2 2048]
def stage8Part20Model (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 w20 : W) (rest : List W) : State :=
  let v0 : W := w0 * w1
  let v1 : W := UInt256.land v0 w2
  let v2 : W := UInt256.mulMod w17 v1 w3
  let v3 : W := v2 + w4
  {s with pc := N 4741,memory := s.memory,stack := (N 2048)::v3::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::w16::v1::w18::w19::w20::rest}
theorem stage8Part20_run (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 w20 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions stage8Part20Program {s with pc := N 4732,memory := s.memory,stack := w0::w1::w2::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::w16::w17::w18::w19::w20::rest} = some (stage8Part20Model s w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 w20 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 63) : rest.length+j < 1024 := by omega
  simp [hz,hzn,stage8Part20Program,stage8Part20Model,runInstructions,runInstr,List.exchange,succ_ofNat_mod,ofNat_add_mod,Nat.add_assoc,State.activeWordsAfterUInt256,literal_eq_ofNat,capacity]
def stage8Part21Program : List Instr :=
  [
  .op (.Dup ⟨10,by decide⟩),
   .op (.Swap ⟨2,by decide⟩),
   .op .POP,
   .op .MULMOD]
def stage8Part21Model (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 : W) (rest : List W) : State :=
  let v0 : W := UInt256.mulMod w0 w1 w10
  {s with pc := N 4745,memory := s.memory,stack := v0::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::w16::w17::rest}
theorem stage8Part21_run (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions stage8Part21Program {s with pc := N 4741,memory := s.memory,stack := w0::w1::w2::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::w16::w17::rest} = some (stage8Part21Model s w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 63) : rest.length+j < 1024 := by omega
  simp [hz,hzn,stage8Part21Program,stage8Part21Model,runInstructions,runInstr,List.exchange,succ_ofNat_mod,ofNat_add_mod,Nat.add_assoc,State.activeWordsAfterUInt256,literal_eq_ofNat,capacity]
def stage8Program : List Instr := (stage8Part0Program++(stage8Part1Program++(stage8Part2Program++(stage8Part3Program++(stage8Part4Program++(stage8Part5Program++(stage8Part6Program++(stage8Part7Program++(stage8Part8Program++(stage8Part9Program++(stage8Part10Program++(stage8Part11Program++(stage8Part12Program++(stage8Part13Program++(stage8Part14Program++(stage8Part15Program++(stage8Part16Program++(stage8Part17Program++(stage8Part18Program++(stage8Part19Program++(stage8Part20Program++stage8Part21Program)))))))))))))))))))))
def stage8Model (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 : W) (rest : List W) : State :=
  let v0 : W := MachineState.readWord (s.memory) 768
  let v1 : W := w15 * v0
  let v2 : W := MachineState.readWord (s.memory) 160
  let v3 : W := v2 * w4
  let v4 : W := v3 + v1
  let v5 : W := MachineState.readWord (s.memory) 128
  let v6 : W := w5 * v5
  let v7 : W := v6 + v4
  let v8 : W := MachineState.readWord (s.memory) 32
  let v9 : W := v8 * w11
  let v10 : W := v9 + v7
  let v11 : W := UInt256.mulMod w15 v0 w8
  let v12 : W := MachineState.readWord (s.memory) 160
  let v13 : W := UInt256.mulMod w4 v12 w8
  let v14 : W := v13 + v11
  let v15 : W := MachineState.readWord (s.memory) 128
  let v16 : W := UInt256.mulMod w5 v15 w8
  let v17 : W := v16 + v14
  let v18 : W := MachineState.readWord (s.memory) 32
  let v19 : W := UInt256.mulMod v18 w11 w8
  let v20 : W := v19 + v17
  let v21 : W := w0 + v20
  let v22 : W := w0 + v10
  let v23 : W := MachineState.readWord (s.memory) 64
  let v24 : W := v23 * v23
  let v25 : W := v24 + v22
  let v26 : W := MachineState.readWord (s.memory) 1600
  let v27 : W := UInt256.mulMod v26 w9 w8
  let v28 : W := v27 + v21
  let v29 : W := v26 * w9
  let v30 : W := v29 + v25
  let v31 : W := MachineState.readWord (s.memory) 1088
  let v32 : W := w7 * v31
  let v33 : W := v32 + v30
  let v34 : W := MachineState.readWord (s.memory) 192
  let v35 : W := v34 * w2
  let v36 : W := v35 + v33
  let v37 : W := MachineState.readWord (s.memory) 0
  let v38 : W := v37 * w6
  let v39 : W := v38 + v36
  let v40 : W := MachineState.readWord (s.memory) 224
  let v41 : W := v40 * w3
  let v42 : W := v41 + v39
  let v43 : W := MachineState.readWord (s.memory) 1216
  let v44 : W := v43 * w13
  let v45 : W := v44 + v42
  let v46 : W := MachineState.readWord (s.memory) 1248
  let v47 : W := v46 * w1
  let v48 : W := v47 + v45
  let v49 : W := MachineState.readWord (s.memory) 1280
  let v50 : W := v49 * w10
  let v51 : W := v50 + v48
  let v52 : W := MachineState.readWord (s.memory) 64
  let v53 : W := v52 + v52
  let v54 : ByteArray := MachineState.writeBytes (s.memory) (Data.Bytes.natToBytesPadded v53.toNat 32) 64
  let v55 : W := UInt256.mulMod v52 v52 w8
  let v56 : W := v55 + v28
  let v57 : W := MachineState.readWord v54 1088
  let v58 : W := UInt256.mulMod w7 v57 w8
  let v59 : W := v58 + v56
  let v60 : W := MachineState.readWord v54 192
  let v61 : W := UInt256.mulMod v60 w2 w8
  let v62 : W := v61 + v59
  let v63 : W := MachineState.readWord v54 0
  let v64 : W := UInt256.mulMod v63 w6 w8
  let v65 : W := v64 + v62
  let v66 : W := MachineState.readWord v54 224
  let v67 : W := UInt256.mulMod v66 w3 w8
  let v68 : W := v67 + v65
  let v69 : W := MachineState.readWord v54 1216
  let v70 : W := UInt256.mulMod v69 w13 w8
  let v71 : W := v70 + v68
  let v72 : W := MachineState.readWord v54 1248
  let v73 : W := UInt256.mulMod v72 w1 w8
  let v74 : W := v73 + v71
  let v75 : W := MachineState.readWord v54 1280
  let v76 : W := UInt256.mulMod v75 w10 w8
  let v77 : W := v76 + v74
  let v78 : W := MachineState.readWord v54 2720
  let v79 : W := v78 * v51
  let v80 : W := UInt256.land v79 (N 1766847064778384329583297500742918515827483896875618958121606201292619775)
  let v81 : W := UInt256.mulMod w12 v80 w8
  let v82 : W := v81 + v77
  let v83 : W := UInt256.mulMod (N 2048) v82 w8
  {s with pc := N 4745,memory := v54,stack := v83::w1::w2::w3::w4::w5::w6::w7::w8::v26::w10::w11::v80::w13::w14::w15::rest}
theorem stage8_run (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions stage8Program {s with pc := N 4509,memory := s.memory,stack := w0::w1::w2::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::rest} = some (stage8Model s w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 rest) := by
  let v0 : W := MachineState.readWord (s.memory) 768
  let v1 : W := w15 * v0
  let v2 : W := MachineState.readWord (s.memory) 160
  let v3 : W := v2 * w4
  let v4 : W := v3 + v1
  let v5 : W := MachineState.readWord (s.memory) 128
  let v6 : W := w5 * v5
  let v7 : W := v6 + v4
  let v8 : W := MachineState.readWord (s.memory) 32
  let v9 : W := v8 * w11
  let v10 : W := v9 + v7
  let v11 : W := UInt256.mulMod w15 v0 w8
  let v12 : W := MachineState.readWord (s.memory) 160
  let v13 : W := UInt256.mulMod w4 v12 w8
  let v14 : W := v13 + v11
  let v15 : W := MachineState.readWord (s.memory) 128
  let v16 : W := UInt256.mulMod w5 v15 w8
  let v17 : W := v16 + v14
  let v18 : W := MachineState.readWord (s.memory) 32
  let v19 : W := UInt256.mulMod v18 w11 w8
  let v20 : W := v19 + v17
  let v21 : W := w0 + v20
  let v22 : W := w0 + v10
  let v23 : W := MachineState.readWord (s.memory) 64
  let v24 : W := v23 * v23
  let v25 : W := v24 + v22
  let v26 : W := MachineState.readWord (s.memory) 1600
  let v27 : W := UInt256.mulMod v26 w9 w8
  let v28 : W := v27 + v21
  let v29 : W := v26 * w9
  let v30 : W := v29 + v25
  let v31 : W := MachineState.readWord (s.memory) 1088
  let v32 : W := w7 * v31
  let v33 : W := v32 + v30
  let v34 : W := MachineState.readWord (s.memory) 192
  let v35 : W := v34 * w2
  let v36 : W := v35 + v33
  let v37 : W := MachineState.readWord (s.memory) 0
  let v38 : W := v37 * w6
  let v39 : W := v38 + v36
  let v40 : W := MachineState.readWord (s.memory) 224
  let v41 : W := v40 * w3
  let v42 : W := v41 + v39
  let v43 : W := MachineState.readWord (s.memory) 1216
  let v44 : W := v43 * w13
  let v45 : W := v44 + v42
  let v46 : W := MachineState.readWord (s.memory) 1248
  let v47 : W := v46 * w1
  let v48 : W := v47 + v45
  let v49 : W := MachineState.readWord (s.memory) 1280
  let v50 : W := v49 * w10
  let v51 : W := v50 + v48
  let v52 : W := MachineState.readWord (s.memory) 64
  let v53 : W := v52 + v52
  let v54 : ByteArray := MachineState.writeBytes (s.memory) (Data.Bytes.natToBytesPadded v53.toNat 32) 64
  let v55 : W := UInt256.mulMod v52 v52 w8
  let v56 : W := v55 + v28
  let v57 : W := MachineState.readWord v54 1088
  let v58 : W := UInt256.mulMod w7 v57 w8
  let v59 : W := v58 + v56
  let v60 : W := MachineState.readWord v54 192
  let v61 : W := UInt256.mulMod v60 w2 w8
  let v62 : W := v61 + v59
  let v63 : W := MachineState.readWord v54 0
  let v64 : W := UInt256.mulMod v63 w6 w8
  let v65 : W := v64 + v62
  let v66 : W := MachineState.readWord v54 224
  let v67 : W := UInt256.mulMod v66 w3 w8
  let v68 : W := v67 + v65
  let v69 : W := MachineState.readWord v54 1216
  let v70 : W := UInt256.mulMod v69 w13 w8
  let v71 : W := v70 + v68
  let v72 : W := MachineState.readWord v54 1248
  let v73 : W := UInt256.mulMod v72 w1 w8
  let v74 : W := v73 + v71
  let v75 : W := MachineState.readWord v54 1280
  let v76 : W := UInt256.mulMod v75 w10 w8
  let v77 : W := v76 + v74
  let v78 : W := MachineState.readWord v54 2720
  let v79 : W := v78 * v51
  let v80 : W := UInt256.land v79 (N 1766847064778384329583297500742918515827483896875618958121606201292619775)
  let v81 : W := UInt256.mulMod w12 v80 w8
  let v82 : W := v81 + v77
  let v83 : W := UInt256.mulMod (N 2048) v82 w8
  have h0 : runInstructions stage8Part0Program {s with pc := N 4509,memory := s.memory,stack := w0::w1::w2::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::rest} = some {s with pc := N 4519,memory := s.memory,stack := w4::v1::v0::w8::w15::w0::w1::w2::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::rest} := by
    simpa only [stage8Part0Model,v0,v1] using stage8Part0_run ({s with memory := s.memory}) w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 rest hcap hact
  have h1 : runInstructions stage8Part1Program {s with pc := N 4519,memory := s.memory,stack := w4::v1::v0::w8::w15::w0::w1::w2::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::rest} = some {s with pc := N 4529,memory := s.memory,stack := v6::v4::v0::w8::w15::w0::w1::w2::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::rest} := by
    simpa only [stage8Part1Model,v2,v3,v4,v5,v6] using stage8Part1_run ({s with memory := s.memory}) w4 v1 v0 w8 w15 w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 rest hcap hact
  have h2 : runInstructions stage8Part2Program {s with pc := N 4529,memory := s.memory,stack := v6::v4::v0::w8::w15::w0::w1::w2::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::rest} = some {s with pc := N 4537,memory := s.memory,stack := w15::v0::w8::v10::w0::w1::w2::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::rest} := by
    simpa only [stage8Part2Model,v7,v8,v9,v10] using stage8Part2_run ({s with memory := s.memory}) v6 v4 v0 w8 w15 w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 rest hcap hact
  have h3 : runInstructions stage8Part3Program {s with pc := N 4537,memory := s.memory,stack := w15::v0::w8::v10::w0::w1::w2::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::rest} = some {s with pc := N 4546,memory := s.memory,stack := w8::v14::v10::w0::w1::w2::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::rest} := by
    simpa only [stage8Part3Model,v11,v12,v13,v14] using stage8Part3_run ({s with memory := s.memory}) w15 v0 w8 v10 w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 rest hcap hact
  have h4 : runInstructions stage8Part4Program {s with pc := N 4546,memory := s.memory,stack := w8::v14::v10::w0::w1::w2::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::rest} = some {s with pc := N 4554,memory := s.memory,stack := w11::w8::v17::v10::w0::w1::w2::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::rest} := by
    simpa only [stage8Part4Model,v15,v16,v17] using stage8Part4_run ({s with memory := s.memory}) w8 v14 v10 w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 rest hcap hact
  have h5 : runInstructions stage8Part5Program {s with pc := N 4554,memory := s.memory,stack := w11::w8::v17::v10::w0::w1::w2::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::rest} = some {s with pc := N 4563,memory := s.memory,stack := v22::v21::w1::w2::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::rest} := by
    simpa only [stage8Part5Model,v18,v19,v20,v21,v22] using stage8Part5_run ({s with memory := s.memory}) w11 w8 v17 v10 w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 rest hcap hact
  have h6 : runInstructions stage8Part6Program {s with pc := N 4563,memory := s.memory,stack := v22::v21::w1::w2::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::rest} = some {s with pc := N 4574,memory := s.memory,stack := w9::v25::v21::w1::w2::w3::w4::w5::w6::w7::w8::v26::w10::w11::w12::w13::w14::w15::rest} := by
    simpa only [stage8Part6Model,v23,v24,v25,v26] using stage8Part6_run ({s with memory := s.memory}) v22 v21 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 rest hcap hact
  have h7 : runInstructions stage8Part7Program {s with pc := N 4574,memory := s.memory,stack := w9::v25::v21::w1::w2::w3::w4::w5::w6::w7::w8::v26::w10::w11::w12::w13::w14::w15::rest} = some {s with pc := N 4582,memory := s.memory,stack := v26::w9::v25::v28::w1::w2::w3::w4::w5::w6::w7::w8::v26::w10::w11::w12::w13::w14::w15::rest} := by
    simpa only [stage8Part7Model,v27,v28] using stage8Part7_run ({s with memory := s.memory}) w9 v25 v21 w1 w2 w3 w4 w5 w6 w7 w8 v26 w10 w11 w12 w13 w14 w15 rest hcap hact
  have h8 : runInstructions stage8Part8Program {s with pc := N 4582,memory := s.memory,stack := v26::w9::v25::v28::w1::w2::w3::w4::w5::w6::w7::w8::v26::w10::w11::w12::w13::w14::w15::rest} = some {s with pc := N 4592,memory := s.memory,stack := w2::v33::v28::w1::w2::w3::w4::w5::w6::w7::w8::v26::w10::w11::w12::w13::w14::w15::rest} := by
    simpa only [stage8Part8Model,v29,v30,v31,v32,v33] using stage8Part8_run ({s with memory := s.memory}) v26 w9 v25 v28 w1 w2 w3 w4 w5 w6 w7 w8 v26 w10 w11 w12 w13 w14 w15 rest hcap hact
  have h9 : runInstructions stage8Part9Program {s with pc := N 4592,memory := s.memory,stack := w2::v33::v28::w1::w2::w3::w4::w5::w6::w7::w8::v26::w10::w11::w12::w13::w14::w15::rest} = some {s with pc := N 4601,memory := s.memory,stack := v38::v36::v28::w1::w2::w3::w4::w5::w6::w7::w8::v26::w10::w11::w12::w13::w14::w15::rest} := by
    simpa only [stage8Part9Model,v34,v35,v36,v37,v38] using stage8Part9_run ({s with memory := s.memory}) w2 v33 v28 w1 w2 w3 w4 w5 w6 w7 w8 v26 w10 w11 w12 w13 w14 w15 rest hcap hact
  have h10 : runInstructions stage8Part10Program {s with pc := N 4601,memory := s.memory,stack := v38::v36::v28::w1::w2::w3::w4::w5::w6::w7::w8::v26::w10::w11::w12::w13::w14::w15::rest} = some {s with pc := N 4609,memory := s.memory,stack := w13::v42::v28::w1::w2::w3::w4::w5::w6::w7::w8::v26::w10::w11::w12::w13::w14::w15::rest} := by
    simpa only [stage8Part10Model,v39,v40,v41,v42] using stage8Part10_run ({s with memory := s.memory}) v38 v36 v28 w1 w2 w3 w4 w5 w6 w7 w8 v26 w10 w11 w12 w13 w14 w15 rest hcap hact
  have h11 : runInstructions stage8Part11Program {s with pc := N 4609,memory := s.memory,stack := w13::v42::v28::w1::w2::w3::w4::w5::w6::w7::w8::v26::w10::w11::w12::w13::w14::w15::rest} = some {s with pc := N 4621,memory := s.memory,stack := v47::v45::v28::w1::w2::w3::w4::w5::w6::w7::w8::v26::w10::w11::w12::w13::w14::w15::rest} := by
    simpa only [stage8Part11Model,v43,v44,v45,v46,v47] using stage8Part11_run ({s with memory := s.memory}) w13 v42 v28 w1 w2 w3 w4 w5 w6 w7 w8 v26 w10 w11 w12 w13 w14 w15 rest hcap hact
  have h12 : runInstructions stage8Part12Program {s with pc := N 4621,memory := s.memory,stack := v47::v45::v28::w1::w2::w3::w4::w5::w6::w7::w8::v26::w10::w11::w12::w13::w14::w15::rest} = some {s with pc := N 4631,memory := s.memory,stack := w8::v28::v51::w1::w2::w3::w4::w5::w6::w7::w8::v26::w10::w11::w12::w13::w14::w15::rest} := by
    simpa only [stage8Part12Model,v48,v49,v50,v51] using stage8Part12_run ({s with memory := s.memory}) v47 v45 v28 w1 w2 w3 w4 w5 w6 w7 w8 v26 w10 w11 w12 w13 w14 w15 rest hcap hact
  have h13 : runInstructions stage8Part13Program {s with pc := N 4631,memory := s.memory,stack := w8::v28::v51::w1::w2::w3::w4::w5::w6::w7::w8::v26::w10::w11::w12::w13::w14::w15::rest} = some {s with pc := N 4641,memory := v54,stack := v52::v52::w8::v28::v51::w1::w2::w3::w4::w5::w6::w7::w8::v26::w10::w11::w12::w13::w14::w15::rest} := by
    simpa only [stage8Part13Model,v52,v53,v54] using stage8Part13_run ({s with memory := s.memory}) w8 v28 v51 w1 w2 w3 w4 w5 w6 w7 w8 v26 w10 w11 w12 w13 w14 w15 rest hcap hact
  have h14 : runInstructions stage8Part14Program {s with pc := N 4641,memory := v54,stack := v52::v52::w8::v28::v51::w1::w2::w3::w4::w5::w6::w7::w8::v26::w10::w11::w12::w13::w14::w15::rest} = some {s with pc := N 4651,memory := v54,stack := v59::v51::w1::w2::w3::w4::w5::w6::w7::w8::v26::w10::w11::w12::w13::w14::w15::rest} := by
    simpa only [stage8Part14Model,v55,v56,v57,v58,v59] using stage8Part14_run ({s with memory := v54}) v52 v52 w8 v28 v51 w1 w2 w3 w4 w5 w6 w7 w8 v26 w10 w11 w12 w13 w14 w15 rest hcap hact
  have h15 : runInstructions stage8Part15Program {s with pc := N 4651,memory := v54,stack := v59::v51::w1::w2::w3::w4::w5::w6::w7::w8::v26::w10::w11::w12::w13::w14::w15::rest} = some {s with pc := N 4660,memory := v54,stack := w6::w8::v62::v51::w1::w2::w3::w4::w5::w6::w7::w8::v26::w10::w11::w12::w13::w14::w15::rest} := by
    simpa only [stage8Part15Model,v60,v61,v62] using stage8Part15_run ({s with memory := v54}) v59 v51 w1 w2 w3 w4 w5 w6 w7 w8 v26 w10 w11 w12 w13 w14 w15 rest hcap hact
  have h16 : runInstructions stage8Part16Program {s with pc := N 4660,memory := v54,stack := w6::w8::v62::v51::w1::w2::w3::w4::w5::w6::w7::w8::v26::w10::w11::w12::w13::w14::w15::rest} = some {s with pc := N 4669,memory := v54,stack := v66::w3::w8::v65::v51::w1::w2::w3::w4::w5::w6::w7::w8::v26::w10::w11::w12::w13::w14::w15::rest} := by
    simpa only [stage8Part16Model,v63,v64,v65,v66] using stage8Part16_run ({s with memory := v54}) w6 w8 v62 v51 w1 w2 w3 w4 w5 w6 w7 w8 v26 w10 w11 w12 w13 w14 w15 rest hcap hact
  have h17 : runInstructions stage8Part17Program {s with pc := N 4669,memory := v54,stack := v66::w3::w8::v65::v51::w1::w2::w3::w4::w5::w6::w7::w8::v26::w10::w11::w12::w13::w14::w15::rest} = some {s with pc := N 4679,memory := v54,stack := v71::v51::w1::w2::w3::w4::w5::w6::w7::w8::v26::w10::w11::w12::w13::w14::w15::rest} := by
    simpa only [stage8Part17Model,v67,v68,v69,v70,v71] using stage8Part17_run ({s with memory := v54}) v66 w3 w8 v65 v51 w1 w2 w3 w4 w5 w6 w7 w8 v26 w10 w11 w12 w13 w14 w15 rest hcap hact
  have h18 : runInstructions stage8Part18Program {s with pc := N 4679,memory := v54,stack := v71::v51::w1::w2::w3::w4::w5::w6::w7::w8::v26::w10::w11::w12::w13::w14::w15::rest} = some {s with pc := N 4689,memory := v54,stack := w10::w8::v74::v51::w1::w2::w3::w4::w5::w6::w7::w8::v26::w10::w11::w12::w13::w14::w15::rest} := by
    simpa only [stage8Part18Model,v72,v73,v74] using stage8Part18_run ({s with memory := v54}) v71 v51 w1 w2 w3 w4 w5 w6 w7 w8 v26 w10 w11 w12 w13 w14 w15 rest hcap hact
  have h19 : runInstructions stage8Part19Program {s with pc := N 4689,memory := v54,stack := w10::w8::v74::v51::w1::w2::w3::w4::w5::w6::w7::w8::v26::w10::w11::w12::w13::w14::w15::rest} = some {s with pc := N 4732,memory := v54,stack := v78::v51::(N 1766847064778384329583297500742918515827483896875618958121606201292619775)::w8::v77::v51::w1::w2::w3::w4::w5::w6::w7::w8::v26::w10::w11::w12::w13::w14::w15::rest} := by
    simpa only [stage8Part19Model,v75,v76,v77,v78] using stage8Part19_run ({s with memory := v54}) w10 w8 v74 v51 w1 w2 w3 w4 w5 w6 w7 w8 v26 w10 w11 w12 w13 w14 w15 rest hcap hact
  have h20 : runInstructions stage8Part20Program {s with pc := N 4732,memory := v54,stack := v78::v51::(N 1766847064778384329583297500742918515827483896875618958121606201292619775)::w8::v77::v51::w1::w2::w3::w4::w5::w6::w7::w8::v26::w10::w11::w12::w13::w14::w15::rest} = some {s with pc := N 4741,memory := v54,stack := (N 2048)::v82::v51::w1::w2::w3::w4::w5::w6::w7::w8::v26::w10::w11::v80::w13::w14::w15::rest} := by
    simpa only [stage8Part20Model,v79,v80,v81,v82] using stage8Part20_run ({s with memory := v54}) v78 v51 (N 1766847064778384329583297500742918515827483896875618958121606201292619775) w8 v77 v51 w1 w2 w3 w4 w5 w6 w7 w8 v26 w10 w11 w12 w13 w14 w15 rest hcap hact
  have h21 : runInstructions stage8Part21Program {s with pc := N 4741,memory := v54,stack := (N 2048)::v82::v51::w1::w2::w3::w4::w5::w6::w7::w8::v26::w10::w11::v80::w13::w14::w15::rest} = some {s with pc := N 4745,memory := v54,stack := v83::w1::w2::w3::w4::w5::w6::w7::w8::v26::w10::w11::v80::w13::w14::w15::rest} := by
    simpa only [stage8Part21Model,v83] using stage8Part21_run ({s with memory := v54}) (N 2048) v82 v51 w1 w2 w3 w4 w5 w6 w7 w8 v26 w10 w11 v80 w13 w14 w15 rest hcap hact
  exact (runInstructions_append_some _ _ _ _ _ h0 (runInstructions_append_some _ _ _ _ _ h1 (runInstructions_append_some _ _ _ _ _ h2 (runInstructions_append_some _ _ _ _ _ h3 (runInstructions_append_some _ _ _ _ _ h4 (runInstructions_append_some _ _ _ _ _ h5 (runInstructions_append_some _ _ _ _ _ h6 (runInstructions_append_some _ _ _ _ _ h7 (runInstructions_append_some _ _ _ _ _ h8 (runInstructions_append_some _ _ _ _ _ h9 (runInstructions_append_some _ _ _ _ _ h10 (runInstructions_append_some _ _ _ _ _ h11 (runInstructions_append_some _ _ _ _ _ h12 (runInstructions_append_some _ _ _ _ _ h13 (runInstructions_append_some _ _ _ _ _ h14 (runInstructions_append_some _ _ _ _ _ h15 (runInstructions_append_some _ _ _ _ _ h16 (runInstructions_append_some _ _ _ _ _ h17 (runInstructions_append_some _ _ _ _ _ h18 (runInstructions_append_some _ _ _ _ _ h19 (runInstructions_append_some _ _ _ _ _ h20 h21)))))))))))))))))))))
end R9InvConsumeExec
