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
def stage1Part0Program : List Instr :=
  [
  .push 2 768,
   .op .MLOAD,
   .op (.Dup ⟨0,by decide⟩),
   .op .ADD,
   .op (.Dup ⟨0,by decide⟩),
   .push 2 768,
   .op .MSTORE,
   .op (.Dup ⟨9,by decide⟩)]
def stage1Part0Model (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 : W) (rest : List W) : State :=
  let v0 : W := MachineState.readWord (s.memory) 768
  let v1 : W := v0 + v0
  let v2 : ByteArray := MachineState.writeBytes (s.memory) (Data.Bytes.natToBytesPadded v1.toNat 32) 768
  {s with pc := N 3565,memory := v2,stack := w8::v1::w0::w1::w2::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::rest}
theorem stage1Part0_run (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions stage1Part0Program {s with pc := N 3553,memory := s.memory,stack := w0::w1::w2::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::rest} = some (stage1Part0Model s w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 63) : rest.length+j < 1024 := by omega
  have ha768 : (768 : W).toNat = 768 := rfl
  have hf768 := Monpro.activeWords_fix s 768 32 (by decide) (by norm_num) hact
  simp [hz,hzn,stage1Part0Program,stage1Part0Model,runInstructions,runInstr,List.exchange,succ_ofNat_mod,ofNat_add_mod,Nat.add_assoc,State.activeWordsAfterUInt256,literal_eq_ofNat,capacity,ha768,hf768]
def stage1Part1Program : List Instr :=
  [
  .op (.Dup ⟨1,by decide⟩),
   .op (.Dup ⟨7,by decide⟩),
   .op .MULMOD,
   .op (.Swap ⟨0,by decide⟩),
   .op (.Dup ⟨6,by decide⟩),
   .op .MUL,
   .op (.Dup ⟨2,by decide⟩),
   .op .ADD]
def stage1Part1Model (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 : W) (rest : List W) : State :=
  let v0 : W := UInt256.mulMod w6 w1 w0
  let v1 : W := w6 * w1
  let v2 : W := w2 + v1
  {s with pc := N 3573,memory := s.memory,stack := v2::v0::w2::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::w16::w17::rest}
theorem stage1Part1_run (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions stage1Part1Program {s with pc := N 3565,memory := s.memory,stack := w0::w1::w2::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::w16::w17::rest} = some (stage1Part1Model s w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 63) : rest.length+j < 1024 := by omega
  simp [hz,hzn,stage1Part1Program,stage1Part1Model,runInstructions,runInstr,List.exchange,succ_ofNat_mod,ofNat_add_mod,Nat.add_assoc,State.activeWordsAfterUInt256,literal_eq_ofNat,capacity]
def stage1Part2Program : List Instr :=
  [
  .op (.Dup ⟨11,by decide⟩),
   .op (.Dup ⟨13,by decide⟩),
   .op .MUL,
   .op .ADD,
   .op (.Swap ⟨1,by decide⟩),
   .op .ADD,
   .op (.Dup ⟨9,by decide⟩),
   .op (.Dup ⟨12,by decide⟩)]
def stage1Part2Model (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 : W) (rest : List W) : State :=
  let v0 : W := w12 * w11
  let v1 : W := v0 + w0
  let v2 : W := w2 + w1
  {s with pc := N 3581,memory := s.memory,stack := w12::w10::v2::v1::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::w16::w17::rest}
theorem stage1Part2_run (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions stage1Part2Program {s with pc := N 3573,memory := s.memory,stack := w0::w1::w2::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::w16::w17::rest} = some (stage1Part2Model s w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 63) : rest.length+j < 1024 := by omega
  simp [hz,hzn,stage1Part2Program,stage1Part2Model,runInstructions,runInstr,List.exchange,succ_ofNat_mod,ofNat_add_mod,Nat.add_assoc,State.activeWordsAfterUInt256,literal_eq_ofNat,capacity]
def stage1Part3Program : List Instr :=
  [
  .op (.Dup ⟨12,by decide⟩),
   .op .MULMOD,
   .op .ADD,
   .op (.Dup ⟨9,by decide⟩),
   .op (.Dup ⟨14,by decide⟩),
   .push 2 2720,
   .op .MLOAD,
   .op (.Dup ⟨2,by decide⟩),
   .op (.Swap ⟨4,by decide⟩)]
def stage1Part3Model (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 : W) (rest : List W) : State :=
  let v0 : W := UInt256.mulMod w12 w0 w1
  let v1 : W := v0 + w2
  let v2 : W := MachineState.readWord (s.memory) 2720
  {s with pc := N 3592,memory := s.memory,stack := w3::v2::w15::w11::v1::w11::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::w16::w17::w18::rest}
theorem stage1Part3_run (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions stage1Part3Program {s with pc := N 3581,memory := s.memory,stack := w0::w1::w2::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::w16::w17::w18::rest} = some (stage1Part3Model s w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 63) : rest.length+j < 1024 := by omega
  have ha2720 : (2720 : W).toNat = 2720 := rfl
  have hf2720 := Monpro.activeWords_fix s 2720 32 (by decide) (by norm_num) hact
  simp [hz,hzn,stage1Part3Program,stage1Part3Model,runInstructions,runInstr,List.exchange,succ_ofNat_mod,ofNat_add_mod,Nat.add_assoc,State.activeWordsAfterUInt256,literal_eq_ofNat,capacity,ha2720,hf2720]
def stage1Part4Program : List Instr :=
  [
  .op .MUL,
   .push 30 1766847064778384329583297500742918515827483896875618958121606201292619775,
   .op .AND,
   .op (.Dup ⟨0,by decide⟩),
   .op (.Swap ⟨11,by decide⟩),
   .op .POP,
   .op .MULMOD,
   .op .ADD]
def stage1Part4Model (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 w20 : W) (rest : List W) : State :=
  let v0 : W := w0 * w1
  let v1 : W := UInt256.land (N 1766847064778384329583297500742918515827483896875618958121606201292619775) v0
  let v2 : W := UInt256.mulMod v1 w2 w3
  let v3 : W := v2 + w4
  {s with pc := N 3630,memory := s.memory,stack := v3::w5::w6::w7::w8::w9::w10::w11::v1::w13::w14::w15::w16::w17::w18::w19::w20::rest}
theorem stage1Part4_run (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 w20 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions stage1Part4Program {s with pc := N 3592,memory := s.memory,stack := w0::w1::w2::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::w16::w17::w18::w19::w20::rest} = some (stage1Part4Model s w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 w20 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 63) : rest.length+j < 1024 := by omega
  simp [hz,hzn,stage1Part4Program,stage1Part4Model,runInstructions,runInstr,List.exchange,succ_ofNat_mod,ofNat_add_mod,Nat.add_assoc,State.activeWordsAfterUInt256,literal_eq_ofNat,capacity]
def stage1Part5Program : List Instr :=
  [
  .push 2 2048,
   .op .MULMOD]
def stage1Part5Model (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 : W) (rest : List W) : State :=
  let v0 : W := UInt256.mulMod (N 2048) w0 w1
  {s with pc := N 3634,memory := s.memory,stack := v0::w2::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::w16::rest}
theorem stage1Part5_run (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions stage1Part5Program {s with pc := N 3630,memory := s.memory,stack := w0::w1::w2::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::w16::rest} = some (stage1Part5Model s w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 63) : rest.length+j < 1024 := by omega
  simp [hz,hzn,stage1Part5Program,stage1Part5Model,runInstructions,runInstr,List.exchange,succ_ofNat_mod,ofNat_add_mod,Nat.add_assoc,State.activeWordsAfterUInt256,literal_eq_ofNat,capacity]
def stage1Program : List Instr := (stage1Part0Program++(stage1Part1Program++(stage1Part2Program++(stage1Part3Program++(stage1Part4Program++stage1Part5Program)))))
def stage1Model (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 : W) (rest : List W) : State :=
  let v0 : W := MachineState.readWord (s.memory) 768
  let v1 : W := v0 + v0
  let v2 : ByteArray := MachineState.writeBytes (s.memory) (Data.Bytes.natToBytesPadded v1.toNat 32) 768
  let v3 : W := UInt256.mulMod w4 v1 w8
  let v4 : W := w4 * v1
  let v5 : W := w0 + v4
  let v6 : W := w10 * w9
  let v7 : W := v6 + v5
  let v8 : W := w0 + v3
  let v9 : W := UInt256.mulMod w9 w10 w8
  let v10 : W := v9 + v8
  let v11 : W := MachineState.readWord v2 2720
  let v12 : W := v7 * v11
  let v13 : W := UInt256.land (N 1766847064778384329583297500742918515827483896875618958121606201292619775) v12
  let v14 : W := UInt256.mulMod v13 w12 w8
  let v15 : W := v14 + v10
  let v16 : W := UInt256.mulMod (N 2048) v15 w8
  {s with pc := N 3634,memory := v2,stack := v16::w1::w2::w3::w4::w5::w6::v13::w8::w9::w10::w11::w12::w13::w14::w15::rest}
theorem stage1_run (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions stage1Program {s with pc := N 3553,memory := s.memory,stack := w0::w1::w2::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::rest} = some (stage1Model s w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 rest) := by
  let v0 : W := MachineState.readWord (s.memory) 768
  let v1 : W := v0 + v0
  let v2 : ByteArray := MachineState.writeBytes (s.memory) (Data.Bytes.natToBytesPadded v1.toNat 32) 768
  let v3 : W := UInt256.mulMod w4 v1 w8
  let v4 : W := w4 * v1
  let v5 : W := w0 + v4
  let v6 : W := w10 * w9
  let v7 : W := v6 + v5
  let v8 : W := w0 + v3
  let v9 : W := UInt256.mulMod w9 w10 w8
  let v10 : W := v9 + v8
  let v11 : W := MachineState.readWord v2 2720
  let v12 : W := v7 * v11
  let v13 : W := UInt256.land (N 1766847064778384329583297500742918515827483896875618958121606201292619775) v12
  let v14 : W := UInt256.mulMod v13 w12 w8
  let v15 : W := v14 + v10
  let v16 : W := UInt256.mulMod (N 2048) v15 w8
  have h0 : runInstructions stage1Part0Program {s with pc := N 3553,memory := s.memory,stack := w0::w1::w2::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::rest} = some {s with pc := N 3565,memory := v2,stack := w8::v1::w0::w1::w2::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::rest} := by
    simpa only [stage1Part0Model,v0,v1,v2] using stage1Part0_run ({s with memory := s.memory}) w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 rest hcap hact
  have h1 : runInstructions stage1Part1Program {s with pc := N 3565,memory := v2,stack := w8::v1::w0::w1::w2::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::rest} = some {s with pc := N 3573,memory := v2,stack := v5::v3::w0::w1::w2::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::rest} := by
    simpa only [stage1Part1Model,v3,v4,v5] using stage1Part1_run ({s with memory := v2}) w8 v1 w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 rest hcap hact
  have h2 : runInstructions stage1Part2Program {s with pc := N 3573,memory := v2,stack := v5::v3::w0::w1::w2::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::rest} = some {s with pc := N 3581,memory := v2,stack := w10::w8::v8::v7::w1::w2::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::rest} := by
    simpa only [stage1Part2Model,v6,v7,v8] using stage1Part2_run ({s with memory := v2}) v5 v3 w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 rest hcap hact
  have h3 : runInstructions stage1Part3Program {s with pc := N 3581,memory := v2,stack := w10::w8::v8::v7::w1::w2::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::rest} = some {s with pc := N 3592,memory := v2,stack := v7::v11::w12::w8::v10::w8::w1::w2::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::rest} := by
    simpa only [stage1Part3Model,v9,v10,v11] using stage1Part3_run ({s with memory := v2}) w10 w8 v8 v7 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 rest hcap hact
  have h4 : runInstructions stage1Part4Program {s with pc := N 3592,memory := v2,stack := v7::v11::w12::w8::v10::w8::w1::w2::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::rest} = some {s with pc := N 3630,memory := v2,stack := v15::w8::w1::w2::w3::w4::w5::w6::v13::w8::w9::w10::w11::w12::w13::w14::w15::rest} := by
    simpa only [stage1Part4Model,v12,v13,v14,v15] using stage1Part4_run ({s with memory := v2}) v7 v11 w12 w8 v10 w8 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 rest hcap hact
  have h5 : runInstructions stage1Part5Program {s with pc := N 3630,memory := v2,stack := v15::w8::w1::w2::w3::w4::w5::w6::v13::w8::w9::w10::w11::w12::w13::w14::w15::rest} = some {s with pc := N 3634,memory := v2,stack := v16::w1::w2::w3::w4::w5::w6::v13::w8::w9::w10::w11::w12::w13::w14::w15::rest} := by
    simpa only [stage1Part5Model,v16] using stage1Part5_run ({s with memory := v2}) v15 w8 w1 w2 w3 w4 w5 w6 v13 w8 w9 w10 w11 w12 w13 w14 w15 rest hcap hact
  exact (runInstructions_append_some _ _ _ _ _ h0 (runInstructions_append_some _ _ _ _ _ h1 (runInstructions_append_some _ _ _ _ _ h2 (runInstructions_append_some _ _ _ _ _ h3 (runInstructions_append_some _ _ _ _ _ h4 h5)))))
end R9InvConsumeExec
