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
def stage16Part0Program : List Instr :=
  [
  .op (.Swap ⟨9,by decide⟩),
   .op .POP,
   .op (.Dup ⟨7,by decide⟩),
   .op (.Dup ⟨15,by decide⟩),
   .op (.Dup ⟨0,by decide⟩),
   .op .MULMOD,
   .op (.Dup ⟨8,by decide⟩),
   .op (.Dup ⟨10,by decide⟩)]
def stage16Part0Model (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 : W) (rest : List W) : State :=
  let v0 : W := UInt256.mulMod w15 w15 w8
  {s with pc := N 5529,memory := s.memory,stack := w9::w8::v0::w1::w2::w3::w4::w5::w6::w7::w8::w9::w0::w11::w12::w13::w14::w15::rest}
theorem stage16Part0_run (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions stage16Part0Program {s with pc := N 5521,memory := s.memory,stack := w0::w1::w2::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::rest} = some (stage16Part0Model s w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 63) : rest.length+j < 1024 := by omega
  simp [hz,hzn,stage16Part0Program,stage16Part0Model,runInstructions,runInstr,List.exchange,succ_ofNat_mod,ofNat_add_mod,Nat.add_assoc,State.activeWordsAfterUInt256,literal_eq_ofNat,capacity]
def stage16Part1Program : List Instr :=
  [
  .op (.Dup ⟨14,by decide⟩),
   .op .MULMOD,
   .op (.Dup ⟨11,by decide⟩),
   .op .ADD,
   .op .ADD,
   .op (.Dup ⟨15,by decide⟩),
   .op (.Dup ⟨0,by decide⟩),
   .op .MUL]
def stage16Part1Model (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 : W) (rest : List W) : State :=
  let v0 : W := UInt256.mulMod w14 w0 w1
  let v1 : W := w12 + v0
  let v2 : W := v1 + w2
  let v3 : W := w17 * w17
  {s with pc := N 5537,memory := s.memory,stack := v3::v2::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::w16::w17::rest}
theorem stage16Part1_run (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions stage16Part1Program {s with pc := N 5529,memory := s.memory,stack := w0::w1::w2::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::w16::w17::rest} = some (stage16Part1Model s w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 63) : rest.length+j < 1024 := by omega
  simp [hz,hzn,stage16Part1Program,stage16Part1Model,runInstructions,runInstr,List.exchange,succ_ofNat_mod,ofNat_add_mod,Nat.add_assoc,State.activeWordsAfterUInt256,literal_eq_ofNat,capacity]
def stage16Part2Program : List Instr :=
  [
  .op (.Dup ⟨10,by decide⟩),
   .op (.Dup ⟨14,by decide⟩),
   .op .MUL,
   .push 2 1376,
   .op .MLOAD,
   .op (.Swap ⟨12,by decide⟩),
   .op .ADD,
   .op .ADD]
def stage16Part2Model (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 : W) (rest : List W) : State :=
  let v0 : W := w13 * w10
  let v1 : W := MachineState.readWord (s.memory) 1376
  let v2 : W := w11 + v0
  let v3 : W := v2 + w0
  {s with pc := N 5547,memory := s.memory,stack := v3::w1::w2::w3::w4::w5::w6::w7::w8::w9::w10::v1::w12::w13::w14::w15::w16::rest}
theorem stage16Part2_run (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions stage16Part2Program {s with pc := N 5537,memory := s.memory,stack := w0::w1::w2::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::w16::rest} = some (stage16Part2Model s w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 63) : rest.length+j < 1024 := by omega
  have ha1376 : (1376 : W).toNat = 1376 := rfl
  have hf1376 := Monpro.activeWords_fix s 1376 32 (by decide) (by norm_num) hact
  simp [hz,hzn,stage16Part2Program,stage16Part2Model,runInstructions,runInstr,List.exchange,succ_ofNat_mod,ofNat_add_mod,Nat.add_assoc,State.activeWordsAfterUInt256,literal_eq_ofNat,capacity,ha1376,hf1376]
def stage16Part3Program : List Instr :=
  [
  .op (.Dup ⟨15,by decide⟩),
   .op .AND,
   .op (.Dup ⟨0,by decide⟩),
   .push 1 160,
   .op .MSTORE,
   .op (.Dup ⟨9,by decide⟩),
   .op (.Swap ⟨1,by decide⟩),
   .op .SUB]
def stage16Part3Model (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 : W) (rest : List W) : State :=
  let v0 : W := UInt256.land w15 w0
  let v1 : ByteArray := MachineState.writeBytes (s.memory) (Data.Bytes.natToBytesPadded v0.toNat 32) 160
  let v2 : W := w1 - v0
  {s with pc := N 5556,memory := v1,stack := v2::w9::w2::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::w16::rest}
theorem stage16Part3_run (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions stage16Part3Program {s with pc := N 5547,memory := s.memory,stack := w0::w1::w2::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::w16::rest} = some (stage16Part3Model s w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 63) : rest.length+j < 1024 := by omega
  have ha160 : (160 : W).toNat = 160 := rfl
  have hf160 := Monpro.activeWords_fix s 160 32 (by decide) (by norm_num) hact
  simp [hz,hzn,stage16Part3Program,stage16Part3Model,runInstructions,runInstr,List.exchange,succ_ofNat_mod,ofNat_add_mod,Nat.add_assoc,State.activeWordsAfterUInt256,literal_eq_ofNat,capacity,ha160,hf160]
def stage16Part4Program : List Instr :=
  [
  .op (.Dup ⟨1,by decide⟩),
   .op .ADD,
   .push 2 2048,
   .op .MULMOD]
def stage16Part4Model (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 : W) (rest : List W) : State :=
  let v0 : W := w1 + w0
  let v1 : W := UInt256.mulMod (N 2048) v0 w1
  {s with pc := N 5562,memory := s.memory,stack := v1::w2::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::w16::rest}
theorem stage16Part4_run (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions stage16Part4Program {s with pc := N 5556,memory := s.memory,stack := w0::w1::w2::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::w16::rest} = some (stage16Part4Model s w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 63) : rest.length+j < 1024 := by omega
  simp [hz,hzn,stage16Part4Program,stage16Part4Model,runInstructions,runInstr,List.exchange,succ_ofNat_mod,ofNat_add_mod,Nat.add_assoc,State.activeWordsAfterUInt256,literal_eq_ofNat,capacity]
def stage16Program : List Instr := (stage16Part0Program++(stage16Part1Program++(stage16Part2Program++(stage16Part3Program++stage16Part4Program))))
def stage16Model (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 : W) (rest : List W) : State :=
  let v0 : W := UInt256.mulMod w15 w15 w8
  let v1 : W := UInt256.mulMod w12 w9 w8
  let v2 : W := w0 + v1
  let v3 : W := v2 + v0
  let v4 : W := w15 * w15
  let v5 : W := w12 * w9
  let v6 : W := MachineState.readWord (s.memory) 1376
  let v7 : W := w0 + v5
  let v8 : W := v7 + v4
  let v9 : W := UInt256.land w14 v8
  let v10 : ByteArray := MachineState.writeBytes (s.memory) (Data.Bytes.natToBytesPadded v9.toNat 32) 160
  let v11 : W := v3 - v9
  let v12 : W := w8 + v11
  let v13 : W := UInt256.mulMod (N 2048) v12 w8
  {s with pc := N 5562,memory := v10,stack := v13::w1::w2::w3::w4::w5::w6::w7::w8::w9::v6::w11::w12::w13::w14::w15::rest}
theorem stage16_run (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions stage16Program {s with pc := N 5521,memory := s.memory,stack := w0::w1::w2::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::rest} = some (stage16Model s w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 rest) := by
  let v0 : W := UInt256.mulMod w15 w15 w8
  let v1 : W := UInt256.mulMod w12 w9 w8
  let v2 : W := w0 + v1
  let v3 : W := v2 + v0
  let v4 : W := w15 * w15
  let v5 : W := w12 * w9
  let v6 : W := MachineState.readWord (s.memory) 1376
  let v7 : W := w0 + v5
  let v8 : W := v7 + v4
  let v9 : W := UInt256.land w14 v8
  let v10 : ByteArray := MachineState.writeBytes (s.memory) (Data.Bytes.natToBytesPadded v9.toNat 32) 160
  let v11 : W := v3 - v9
  let v12 : W := w8 + v11
  let v13 : W := UInt256.mulMod (N 2048) v12 w8
  have h0 : runInstructions stage16Part0Program {s with pc := N 5521,memory := s.memory,stack := w0::w1::w2::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::rest} = some {s with pc := N 5529,memory := s.memory,stack := w9::w8::v0::w1::w2::w3::w4::w5::w6::w7::w8::w9::w0::w11::w12::w13::w14::w15::rest} := by
    simpa only [stage16Part0Model,v0] using stage16Part0_run ({s with memory := s.memory}) w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 rest hcap hact
  have h1 : runInstructions stage16Part1Program {s with pc := N 5529,memory := s.memory,stack := w9::w8::v0::w1::w2::w3::w4::w5::w6::w7::w8::w9::w0::w11::w12::w13::w14::w15::rest} = some {s with pc := N 5537,memory := s.memory,stack := v4::v3::w1::w2::w3::w4::w5::w6::w7::w8::w9::w0::w11::w12::w13::w14::w15::rest} := by
    simpa only [stage16Part1Model,v1,v2,v3,v4] using stage16Part1_run ({s with memory := s.memory}) w9 w8 v0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w0 w11 w12 w13 w14 w15 rest hcap hact
  have h2 : runInstructions stage16Part2Program {s with pc := N 5537,memory := s.memory,stack := v4::v3::w1::w2::w3::w4::w5::w6::w7::w8::w9::w0::w11::w12::w13::w14::w15::rest} = some {s with pc := N 5547,memory := s.memory,stack := v8::v3::w1::w2::w3::w4::w5::w6::w7::w8::w9::v6::w11::w12::w13::w14::w15::rest} := by
    simpa only [stage16Part2Model,v5,v6,v7,v8] using stage16Part2_run ({s with memory := s.memory}) v4 v3 w1 w2 w3 w4 w5 w6 w7 w8 w9 w0 w11 w12 w13 w14 w15 rest hcap hact
  have h3 : runInstructions stage16Part3Program {s with pc := N 5547,memory := s.memory,stack := v8::v3::w1::w2::w3::w4::w5::w6::w7::w8::w9::v6::w11::w12::w13::w14::w15::rest} = some {s with pc := N 5556,memory := v10,stack := v11::w8::w1::w2::w3::w4::w5::w6::w7::w8::w9::v6::w11::w12::w13::w14::w15::rest} := by
    simpa only [stage16Part3Model,v9,v10,v11] using stage16Part3_run ({s with memory := s.memory}) v8 v3 w1 w2 w3 w4 w5 w6 w7 w8 w9 v6 w11 w12 w13 w14 w15 rest hcap hact
  have h4 : runInstructions stage16Part4Program {s with pc := N 5556,memory := v10,stack := v11::w8::w1::w2::w3::w4::w5::w6::w7::w8::w9::v6::w11::w12::w13::w14::w15::rest} = some {s with pc := N 5562,memory := v10,stack := v13::w1::w2::w3::w4::w5::w6::w7::w8::w9::v6::w11::w12::w13::w14::w15::rest} := by
    simpa only [stage16Part4Model,v12,v13] using stage16Part4_run ({s with memory := v10}) v11 w8 w1 w2 w3 w4 w5 w6 w7 w8 w9 v6 w11 w12 w13 w14 w15 rest hcap hact
  exact (runInstructions_append_some _ _ _ _ _ h0 (runInstructions_append_some _ _ _ _ _ h1 (runInstructions_append_some _ _ _ _ _ h2 (runInstructions_append_some _ _ _ _ _ h3 h4))))
end R9InvConsumeExec
