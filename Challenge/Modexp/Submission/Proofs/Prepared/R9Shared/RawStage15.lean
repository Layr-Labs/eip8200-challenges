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
def stage15Part0Program : List Instr :=
  [
  .push 2 800,
   .op .MLOAD,
   .op (.Swap ⟨4,by decide⟩),
   .op .POP,
   .op (.Dup ⟨15,by decide⟩),
   .push 1 160,
   .op .MLOAD,
   .op (.Dup ⟨0,by decide⟩)]
def stage15Part0Model (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 : W) (rest : List W) : State :=
  let v0 : W := MachineState.readWord (s.memory) 800
  let v1 : W := MachineState.readWord (s.memory) 160
  {s with pc := N 5476,memory := s.memory,stack := v1::v1::w15::w0::w1::w2::w3::v0::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::rest}
theorem stage15Part0_run (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions stage15Part0Program {s with pc := N 5465,memory := s.memory,stack := w0::w1::w2::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::rest} = some (stage15Part0Model s w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 63) : rest.length+j < 1024 := by omega
  have ha160 : (160 : W).toNat = 160 := rfl
  have hf160 := Monpro.activeWords_fix s 160 32 (by decide) (by norm_num) hact
  have ha800 : (800 : W).toNat = 800 := rfl
  have hf800 := Monpro.activeWords_fix s 800 32 (by decide) (by norm_num) hact
  simp [hz,hzn,stage15Part0Program,stage15Part0Model,runInstructions,runInstr,List.exchange,succ_ofNat_mod,ofNat_add_mod,Nat.add_assoc,State.activeWordsAfterUInt256,literal_eq_ofNat,capacity,ha160,hf160,ha800,hf800]
def stage15Part1Program : List Instr :=
  [
  .op .ADD,
   .op (.Dup ⟨10,by decide⟩),
   .op (.Dup ⟨1,by decide⟩),
   .op (.Dup ⟨3,by decide⟩),
   .op .MULMOD,
   .op (.Swap ⟨1,by decide⟩),
   .op .MUL,
   .op (.Dup ⟨2,by decide⟩)]
def stage15Part1Model (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 : W) (rest : List W) : State :=
  let v0 : W := w0 + w1
  let v1 : W := UInt256.mulMod w2 v0 w11
  let v2 : W := w2 * v0
  {s with pc := N 5484,memory := s.memory,stack := w3::v2::v1::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::w16::w17::w18::rest}
theorem stage15Part1_run (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions stage15Part1Program {s with pc := N 5476,memory := s.memory,stack := w0::w1::w2::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::w16::w17::w18::rest} = some (stage15Part1Model s w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 63) : rest.length+j < 1024 := by omega
  simp [hz,hzn,stage15Part1Program,stage15Part1Model,runInstructions,runInstr,List.exchange,succ_ofNat_mod,ofNat_add_mod,Nat.add_assoc,State.activeWordsAfterUInt256,literal_eq_ofNat,capacity]
def stage15Part2Program : List Instr :=
  [
  .op .ADD,
   .op (.Dup ⟨11,by decide⟩),
   .op (.Dup ⟨13,by decide⟩),
   .op .MUL,
   .op .ADD,
   .op (.Dup ⟨9,by decide⟩),
   .op (.Dup ⟨15,by decide⟩),
   .op .MUL]
def stage15Part2Model (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 : W) (rest : List W) : State :=
  let v0 : W := w0 + w1
  let v1 : W := w13 * w12
  let v2 : W := v1 + v0
  let v3 : W := w15 * w10
  {s with pc := N 5492,memory := s.memory,stack := v3::v2::w2::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::w16::w17::w18::rest}
theorem stage15Part2_run (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions stage15Part2Program {s with pc := N 5484,memory := s.memory,stack := w0::w1::w2::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::w16::w17::w18::rest} = some (stage15Part2Model s w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 63) : rest.length+j < 1024 := by omega
  simp [hz,hzn,stage15Part2Program,stage15Part2Model,runInstructions,runInstr,List.exchange,succ_ofNat_mod,ofNat_add_mod,Nat.add_assoc,State.activeWordsAfterUInt256,literal_eq_ofNat,capacity]
def stage15Part3Program : List Instr :=
  [
  .op .ADD,
   .op (.Swap ⟨1,by decide⟩),
   .op .ADD,
   .op (.Dup ⟨9,by decide⟩),
   .op (.Dup ⟨11,by decide⟩),
   .op (.Dup ⟨13,by decide⟩),
   .op .MULMOD,
   .op .ADD]
def stage15Part3Model (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 : W) (rest : List W) : State :=
  let v0 : W := w0 + w1
  let v1 : W := w3 + w2
  let v2 : W := UInt256.mulMod w13 w12 w11
  let v3 : W := v2 + v1
  {s with pc := N 5500,memory := s.memory,stack := v3::v0::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::w16::w17::w18::rest}
theorem stage15Part3_run (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions stage15Part3Program {s with pc := N 5492,memory := s.memory,stack := w0::w1::w2::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::w16::w17::w18::rest} = some (stage15Part3Model s w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 63) : rest.length+j < 1024 := by omega
  simp [hz,hzn,stage15Part3Program,stage15Part3Model,runInstructions,runInstr,List.exchange,succ_ofNat_mod,ofNat_add_mod,Nat.add_assoc,State.activeWordsAfterUInt256,literal_eq_ofNat,capacity]
def stage15Part4Program : List Instr :=
  [
  .op (.Dup ⟨9,by decide⟩),
   .op (.Dup ⟨14,by decide⟩),
   .op (.Dup ⟨10,by decide⟩),
   .op .MULMOD,
   .op .ADD,
   .op (.Swap ⟨0,by decide⟩),
   .op (.Dup ⟨15,by decide⟩),
   .op .AND]
def stage15Part4Model (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 : W) (rest : List W) : State :=
  let v0 : W := UInt256.mulMod w8 w13 w9
  let v1 : W := v0 + w0
  let v2 : W := UInt256.land w15 w1
  {s with pc := N 5508,memory := s.memory,stack := v2::v1::w2::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::w16::rest}
theorem stage15Part4_run (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions stage15Part4Program {s with pc := N 5500,memory := s.memory,stack := w0::w1::w2::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::w16::rest} = some (stage15Part4Model s w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 63) : rest.length+j < 1024 := by omega
  simp [hz,hzn,stage15Part4Program,stage15Part4Model,runInstructions,runInstr,List.exchange,succ_ofNat_mod,ofNat_add_mod,Nat.add_assoc,State.activeWordsAfterUInt256,literal_eq_ofNat,capacity]
def stage15Part5Program : List Instr :=
  [
  .op (.Dup ⟨0,by decide⟩),
   .push 1 128,
   .op .MSTORE,
   .op (.Dup ⟨9,by decide⟩),
   .op (.Swap ⟨1,by decide⟩),
   .op .SUB,
   .op (.Dup ⟨1,by decide⟩),
   .op .ADD]
def stage15Part5Model (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 : W) (rest : List W) : State :=
  let v0 : ByteArray := MachineState.writeBytes (s.memory) (Data.Bytes.natToBytesPadded w0.toNat 32) 128
  let v1 : W := w1 - w0
  let v2 : W := w9 + v1
  {s with pc := N 5517,memory := v0,stack := v2::w9::w2::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::w16::rest}
theorem stage15Part5_run (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions stage15Part5Program {s with pc := N 5508,memory := s.memory,stack := w0::w1::w2::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::w16::rest} = some (stage15Part5Model s w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 63) : rest.length+j < 1024 := by omega
  have ha128 : (128 : W).toNat = 128 := rfl
  have hf128 := Monpro.activeWords_fix s 128 32 (by decide) (by norm_num) hact
  simp [hz,hzn,stage15Part5Program,stage15Part5Model,runInstructions,runInstr,List.exchange,succ_ofNat_mod,ofNat_add_mod,Nat.add_assoc,State.activeWordsAfterUInt256,literal_eq_ofNat,capacity,ha128,hf128]
def stage15Part6Program : List Instr :=
  [
  .push 2 2048,
   .op .MULMOD]
def stage15Part6Model (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 : W) (rest : List W) : State :=
  let v0 : W := UInt256.mulMod (N 2048) w0 w1
  {s with pc := N 5521,memory := s.memory,stack := v0::w2::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::w16::rest}
theorem stage15Part6_run (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions stage15Part6Program {s with pc := N 5517,memory := s.memory,stack := w0::w1::w2::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::w16::rest} = some (stage15Part6Model s w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 63) : rest.length+j < 1024 := by omega
  simp [hz,hzn,stage15Part6Program,stage15Part6Model,runInstructions,runInstr,List.exchange,succ_ofNat_mod,ofNat_add_mod,Nat.add_assoc,State.activeWordsAfterUInt256,literal_eq_ofNat,capacity]
def stage15Program : List Instr := (stage15Part0Program++(stage15Part1Program++(stage15Part2Program++(stage15Part3Program++(stage15Part4Program++(stage15Part5Program++stage15Part6Program))))))
def stage15Model (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 : W) (rest : List W) : State :=
  let v0 : W := MachineState.readWord (s.memory) 800
  let v1 : W := MachineState.readWord (s.memory) 160
  let v2 : W := v1 + v1
  let v3 : W := UInt256.mulMod w15 v2 w8
  let v4 : W := w15 * v2
  let v5 : W := w0 + v4
  let v6 : W := w10 * w9
  let v7 : W := v6 + v5
  let v8 : W := w12 * w7
  let v9 : W := v8 + v7
  let v10 : W := w0 + v3
  let v11 : W := UInt256.mulMod w10 w9 w8
  let v12 : W := v11 + v10
  let v13 : W := UInt256.mulMod w7 w12 w8
  let v14 : W := v13 + v12
  let v15 : W := UInt256.land w14 v9
  let v16 : ByteArray := MachineState.writeBytes (s.memory) (Data.Bytes.natToBytesPadded v15.toNat 32) 128
  let v17 : W := v14 - v15
  let v18 : W := w8 + v17
  let v19 : W := UInt256.mulMod (N 2048) v18 w8
  {s with pc := N 5521,memory := v16,stack := v19::w1::w2::w3::v0::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::rest}
theorem stage15_run (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions stage15Program {s with pc := N 5465,memory := s.memory,stack := w0::w1::w2::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::rest} = some (stage15Model s w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 rest) := by
  let v0 : W := MachineState.readWord (s.memory) 800
  let v1 : W := MachineState.readWord (s.memory) 160
  let v2 : W := v1 + v1
  let v3 : W := UInt256.mulMod w15 v2 w8
  let v4 : W := w15 * v2
  let v5 : W := w0 + v4
  let v6 : W := w10 * w9
  let v7 : W := v6 + v5
  let v8 : W := w12 * w7
  let v9 : W := v8 + v7
  let v10 : W := w0 + v3
  let v11 : W := UInt256.mulMod w10 w9 w8
  let v12 : W := v11 + v10
  let v13 : W := UInt256.mulMod w7 w12 w8
  let v14 : W := v13 + v12
  let v15 : W := UInt256.land w14 v9
  let v16 : ByteArray := MachineState.writeBytes (s.memory) (Data.Bytes.natToBytesPadded v15.toNat 32) 128
  let v17 : W := v14 - v15
  let v18 : W := w8 + v17
  let v19 : W := UInt256.mulMod (N 2048) v18 w8
  have h0 : runInstructions stage15Part0Program {s with pc := N 5465,memory := s.memory,stack := w0::w1::w2::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::rest} = some {s with pc := N 5476,memory := s.memory,stack := v1::v1::w15::w0::w1::w2::w3::v0::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::rest} := by
    simpa only [stage15Part0Model,v0,v1] using stage15Part0_run ({s with memory := s.memory}) w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 rest hcap hact
  have h1 : runInstructions stage15Part1Program {s with pc := N 5476,memory := s.memory,stack := v1::v1::w15::w0::w1::w2::w3::v0::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::rest} = some {s with pc := N 5484,memory := s.memory,stack := w0::v4::v3::w0::w1::w2::w3::v0::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::rest} := by
    simpa only [stage15Part1Model,v2,v3,v4] using stage15Part1_run ({s with memory := s.memory}) v1 v1 w15 w0 w1 w2 w3 v0 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 rest hcap hact
  have h2 : runInstructions stage15Part2Program {s with pc := N 5484,memory := s.memory,stack := w0::v4::v3::w0::w1::w2::w3::v0::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::rest} = some {s with pc := N 5492,memory := s.memory,stack := v8::v7::v3::w0::w1::w2::w3::v0::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::rest} := by
    simpa only [stage15Part2Model,v5,v6,v7,v8] using stage15Part2_run ({s with memory := s.memory}) w0 v4 v3 w0 w1 w2 w3 v0 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 rest hcap hact
  have h3 : runInstructions stage15Part3Program {s with pc := N 5492,memory := s.memory,stack := v8::v7::v3::w0::w1::w2::w3::v0::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::rest} = some {s with pc := N 5500,memory := s.memory,stack := v12::v9::w1::w2::w3::v0::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::rest} := by
    simpa only [stage15Part3Model,v9,v10,v11,v12] using stage15Part3_run ({s with memory := s.memory}) v8 v7 v3 w0 w1 w2 w3 v0 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 rest hcap hact
  have h4 : runInstructions stage15Part4Program {s with pc := N 5500,memory := s.memory,stack := v12::v9::w1::w2::w3::v0::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::rest} = some {s with pc := N 5508,memory := s.memory,stack := v15::v14::w1::w2::w3::v0::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::rest} := by
    simpa only [stage15Part4Model,v13,v14,v15] using stage15Part4_run ({s with memory := s.memory}) v12 v9 w1 w2 w3 v0 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 rest hcap hact
  have h5 : runInstructions stage15Part5Program {s with pc := N 5508,memory := s.memory,stack := v15::v14::w1::w2::w3::v0::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::rest} = some {s with pc := N 5517,memory := v16,stack := v18::w8::w1::w2::w3::v0::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::rest} := by
    simpa only [stage15Part5Model,v16,v17,v18] using stage15Part5_run ({s with memory := s.memory}) v15 v14 w1 w2 w3 v0 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 rest hcap hact
  have h6 : runInstructions stage15Part6Program {s with pc := N 5517,memory := v16,stack := v18::w8::w1::w2::w3::v0::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::rest} = some {s with pc := N 5521,memory := v16,stack := v19::w1::w2::w3::v0::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::rest} := by
    simpa only [stage15Part6Model,v19] using stage15Part6_run ({s with memory := v16}) v18 w8 w1 w2 w3 v0 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 rest hcap hact
  exact (runInstructions_append_some _ _ _ _ _ h0 (runInstructions_append_some _ _ _ _ _ h1 (runInstructions_append_some _ _ _ _ _ h2 (runInstructions_append_some _ _ _ _ _ h3 (runInstructions_append_some _ _ _ _ _ h4 (runInstructions_append_some _ _ _ _ _ h5 h6))))))
end R9InvConsumeExec
