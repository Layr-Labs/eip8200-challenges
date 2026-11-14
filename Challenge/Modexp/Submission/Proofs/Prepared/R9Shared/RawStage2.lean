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
def stage2Part0Program : List Instr := [.push 2 768,.op .MLOAD,.op (.Dup dA2),.op (.Dup dA11),.op .MUL,.op (.Dup dA6),.op (.Dup dA0),.op .MUL]
def stage2Part0Model (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 : W) (rest : List W) : State :=
  let v0 : W := MachineState.readWord (s.memory) 768
  let v1 : W := w9 * w1
  let v2 : W := w4 * w4
  {s with pc := N 3639,memory := s.memory,stack := v2::v1::v0::w0::w1::w2::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::rest}
theorem stage2Part0_run (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions stage2Part0Program {s with pc := N 3629,memory := s.memory,stack := w0::w1::w2::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::rest} = some (stage2Part0Model s w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 63) : rest.length+j < 1024 := by omega
  have ha768 : (768 : W).toNat = 768 := rfl
  have hf768 := Monpro.activeWords_fix s 768 32 (by decide) (by norm_num) hact
  simp [hz,hzn,stage2Part0Program,stage2Part0Model,runInstructions,runInstr,List.exchange,succ_ofNat_mod,ofNat_add_mod,Nat.add_assoc,State.activeWordsAfterUInt256,literal_eq_ofNat,capacity,ha768,hf768]
def stage2Part1Program : List Instr := [.op (.Dup dA11),.op (.Dup dA3),.op (.Dup dA10),.op .MULMOD,.op (.Swap sA2),.op (.Dup dA9),.op .MUL,.op (.Dup dA4)]
def stage2Part1Model (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 : W) (rest : List W) : State :=
  let v0 : W := UInt256.mulMod w8 w2 w11
  let v1 : W := w8 * w2
  {s with pc := N 3647,memory := s.memory,stack := w3::v1::w0::w1::v0::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::w16::w17::w18::rest}
theorem stage2Part1_run (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions stage2Part1Program {s with pc := N 3639,memory := s.memory,stack := w0::w1::w2::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::w16::w17::w18::rest} = some (stage2Part1Model s w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 63) : rest.length+j < 1024 := by omega
  simp [hz,hzn,stage2Part1Program,stage2Part1Model,runInstructions,runInstr,List.exchange,succ_ofNat_mod,ofNat_add_mod,Nat.add_assoc,State.activeWordsAfterUInt256,literal_eq_ofNat,capacity]
def stage2Part2Program : List Instr := [.op .ADD,.op .ADD,.op .ADD,.op (.Dup dA9),.op (.Dup dA13),.op .MUL,.op .ADD,.op (.Swap sA1)]
def stage2Part2Model (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 w20 : W) (rest : List W) : State :=
  let v0 : W := w0 + w1
  let v1 : W := v0 + w2
  let v2 : W := v1 + w3
  let v3 : W := w15 * w12
  let v4 : W := v3 + v2
  {s with pc := N 3655,memory := s.memory,stack := w5::w4::v4::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::w16::w17::w18::w19::w20::rest}
theorem stage2Part2_run (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 w20 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions stage2Part2Program {s with pc := N 3647,memory := s.memory,stack := w0::w1::w2::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::w16::w17::w18::w19::w20::rest} = some (stage2Part2Model s w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 w20 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 63) : rest.length+j < 1024 := by omega
  simp [hz,hzn,stage2Part2Program,stage2Part2Model,runInstructions,runInstr,List.exchange,succ_ofNat_mod,ofNat_add_mod,Nat.add_assoc,State.activeWordsAfterUInt256,literal_eq_ofNat,capacity]
def stage2Part3Program : List Instr := [.op .ADD,.op (.Dup dA9),.op (.Dup dA6),.op (.Dup dA0),.op (.Dup dA0),.op .ADD,.op (.Swap sA7),.op .MULMOD]
def stage2Part3Model (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 : W) (rest : List W) : State :=
  let v0 : W := w0 + w1
  let v1 : W := w6 + w6
  let v2 : W := UInt256.mulMod w6 w6 w10
  {s with pc := N 3663,memory := s.memory,stack := v2::v0::w2::w3::w4::w5::v1::w7::w8::w9::w10::w11::w12::w13::w14::w15::w16::w17::rest}
theorem stage2Part3_run (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions stage2Part3Program {s with pc := N 3655,memory := s.memory,stack := w0::w1::w2::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::w16::w17::rest} = some (stage2Part3Model s w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 63) : rest.length+j < 1024 := by omega
  simp [hz,hzn,stage2Part3Program,stage2Part3Model,runInstructions,runInstr,List.exchange,succ_ofNat_mod,ofNat_add_mod,Nat.add_assoc,State.activeWordsAfterUInt256,literal_eq_ofNat,capacity]
def stage2Part4Program : List Instr := [.op .ADD,.op (.Dup dA9),.op (.Dup dA3),.op (.Dup dA12),.op .MULMOD,.op .ADD,.op (.Dup dA9),.op (.Dup dA12)]
def stage2Part4Model (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 : W) (rest : List W) : State :=
  let v0 : W := w0 + w1
  let v1 : W := UInt256.mulMod w11 w3 w10
  let v2 : W := v1 + v0
  {s with pc := N 3671,memory := s.memory,stack := w12::w10::v2::w2::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::w16::w17::rest}
theorem stage2Part4_run (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions stage2Part4Program {s with pc := N 3663,memory := s.memory,stack := w0::w1::w2::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::w16::w17::rest} = some (stage2Part4Model s w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 63) : rest.length+j < 1024 := by omega
  simp [hz,hzn,stage2Part4Program,stage2Part4Model,runInstructions,runInstr,List.exchange,succ_ofNat_mod,ofNat_add_mod,Nat.add_assoc,State.activeWordsAfterUInt256,literal_eq_ofNat,capacity]
def stage2Part5Program : List Instr := [.op (.Dup dA10),.op .MULMOD,.op .ADD,.op (.Dup dA9),.op (.Dup dA14),.push 2 2720,.op .MLOAD,.op (.Dup dA2),.op (.Swap sA4)]
def stage2Part5Model (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 : W) (rest : List W) : State :=
  let v0 : W := UInt256.mulMod w10 w0 w1
  let v1 : W := v0 + w2
  let v2 : W := MachineState.readWord (s.memory) 2720
  {s with pc := N 3682,memory := s.memory,stack := w3::v2::w15::w11::v1::w11::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::w16::w17::w18::rest}
theorem stage2Part5_run (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions stage2Part5Program {s with pc := N 3671,memory := s.memory,stack := w0::w1::w2::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::w16::w17::w18::rest} = some (stage2Part5Model s w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 63) : rest.length+j < 1024 := by omega
  have ha2720 : (2720 : W).toNat = 2720 := rfl
  have hf2720 := Monpro.activeWords_fix s 2720 32 (by decide) (by norm_num) hact
  simp [hz,hzn,stage2Part5Program,stage2Part5Model,runInstructions,runInstr,List.exchange,succ_ofNat_mod,ofNat_add_mod,Nat.add_assoc,State.activeWordsAfterUInt256,literal_eq_ofNat,capacity,ha2720,hf2720]
def stage2Part6Program : List Instr := [.op .MUL,.push 30 1766847064778384329583297500742918515827483896875618958121606201292619775,.op .AND,.op (.Dup dA0),.push 1 192,.op .MSTORE,.op .MULMOD,.op .ADD]
def stage2Part6Model (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 w20 : W) (rest : List W) : State :=
  let v0 : W := w0 * w1
  let v1 : W := UInt256.land (N 1766847064778384329583297500742918515827483896875618958121606201292619775) v0
  let v2 : ByteArray := MachineState.writeBytes (s.memory) (Data.Bytes.natToBytesPadded v1.toNat 32) 192
  let v3 : W := UInt256.mulMod v1 w2 w3
  let v4 : W := v3 + w4
  {s with pc := N 3721,memory := v2,stack := v4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::w16::w17::w18::w19::w20::rest}
theorem stage2Part6_run (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 w20 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions stage2Part6Program {s with pc := N 3682,memory := s.memory,stack := w0::w1::w2::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::w16::w17::w18::w19::w20::rest} = some (stage2Part6Model s w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 w20 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 63) : rest.length+j < 1024 := by omega
  have ha192 : (192 : W).toNat = 192 := rfl
  have hf192 := Monpro.activeWords_fix s 192 32 (by decide) (by norm_num) hact
  simp [hz,hzn,stage2Part6Program,stage2Part6Model,runInstructions,runInstr,List.exchange,succ_ofNat_mod,ofNat_add_mod,Nat.add_assoc,State.activeWordsAfterUInt256,literal_eq_ofNat,capacity,ha192,hf192]
def stage2Part7Program : List Instr := [.push 2 2048,.op .MULMOD]
def stage2Part7Model (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 : W) (rest : List W) : State :=
  let v0 : W := UInt256.mulMod (N 2048) w0 w1
  {s with pc := N 3725,memory := s.memory,stack := v0::w2::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::w16::rest}
theorem stage2Part7_run (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions stage2Part7Program {s with pc := N 3721,memory := s.memory,stack := w0::w1::w2::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::w16::rest} = some (stage2Part7Model s w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 63) : rest.length+j < 1024 := by omega
  have ha2048 : (2048 : W).toNat = 2048 := rfl
  have hf2048 := Monpro.activeWords_fix s 2048 32 (by decide) (by norm_num) hact
  simp [hz,hzn,stage2Part7Program,stage2Part7Model,runInstructions,runInstr,List.exchange,succ_ofNat_mod,ofNat_add_mod,Nat.add_assoc,State.activeWordsAfterUInt256,literal_eq_ofNat,capacity,ha2048,hf2048]
def stage2Program : List Instr := (stage2Part0Program++(stage2Part1Program++(stage2Part2Program++(stage2Part3Program++(stage2Part4Program++(stage2Part5Program++(stage2Part6Program++stage2Part7Program)))))))
def stage2Model (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 : W) (rest : List W) : State :=
  let v0 : W := MachineState.readWord (s.memory) 768
  let v1 : W := w9 * w1
  let v2 : W := w4 * w4
  let v3 : W := UInt256.mulMod w5 v0 w8
  let v4 : W := w5 * v0
  let v5 : W := w0 + v4
  let v6 : W := v5 + v2
  let v7 : W := v6 + v1
  let v8 : W := w10 * w7
  let v9 : W := v8 + v7
  let v10 : W := w0 + v3
  let v11 : W := w4 + w4
  let v12 : W := UInt256.mulMod w4 w4 w8
  let v13 : W := v12 + v10
  let v14 : W := UInt256.mulMod w9 w1 w8
  let v15 : W := v14 + v13
  let v16 : W := UInt256.mulMod w7 w10 w8
  let v17 : W := v16 + v15
  let v18 : W := MachineState.readWord (s.memory) 2720
  let v19 : W := v9 * v18
  let v20 : W := UInt256.land (N 1766847064778384329583297500742918515827483896875618958121606201292619775) v19
  let v21 : ByteArray := MachineState.writeBytes (s.memory) (Data.Bytes.natToBytesPadded v20.toNat 32) 192
  let v22 : W := UInt256.mulMod v20 w12 w8
  let v23 : W := v22 + v17
  let v24 : W := UInt256.mulMod (N 2048) v23 w8
  {s with pc := N 3725,memory := v21,stack := v24::w1::w2::w3::v11::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::rest}
theorem stage2_run (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions stage2Program {s with pc := N 3629,memory := s.memory,stack := w0::w1::w2::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::rest} = some (stage2Model s w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 rest) := by
  let v0 : W := MachineState.readWord (s.memory) 768
  let v1 : W := w9 * w1
  let v2 : W := w4 * w4
  let v3 : W := UInt256.mulMod w5 v0 w8
  let v4 : W := w5 * v0
  let v5 : W := w0 + v4
  let v6 : W := v5 + v2
  let v7 : W := v6 + v1
  let v8 : W := w10 * w7
  let v9 : W := v8 + v7
  let v10 : W := w0 + v3
  let v11 : W := w4 + w4
  let v12 : W := UInt256.mulMod w4 w4 w8
  let v13 : W := v12 + v10
  let v14 : W := UInt256.mulMod w9 w1 w8
  let v15 : W := v14 + v13
  let v16 : W := UInt256.mulMod w7 w10 w8
  let v17 : W := v16 + v15
  let v18 : W := MachineState.readWord (s.memory) 2720
  let v19 : W := v9 * v18
  let v20 : W := UInt256.land (N 1766847064778384329583297500742918515827483896875618958121606201292619775) v19
  let v21 : ByteArray := MachineState.writeBytes (s.memory) (Data.Bytes.natToBytesPadded v20.toNat 32) 192
  let v22 : W := UInt256.mulMod v20 w12 w8
  let v23 : W := v22 + v17
  let v24 : W := UInt256.mulMod (N 2048) v23 w8
  have h0 : runInstructions stage2Part0Program {s with pc := N 3629,memory := s.memory,stack := w0::w1::w2::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::rest} = some {s with pc := N 3639,memory := s.memory,stack := v2::v1::v0::w0::w1::w2::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::rest} := by
    simpa only [stage2Part0Model,v0,v1,v2] using stage2Part0_run ({s with memory := s.memory}) w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 rest hcap hact
  have h1 : runInstructions stage2Part1Program {s with pc := N 3639,memory := s.memory,stack := v2::v1::v0::w0::w1::w2::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::rest} = some {s with pc := N 3647,memory := s.memory,stack := w0::v4::v2::v1::v3::w0::w1::w2::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::rest} := by
    simpa only [stage2Part1Model,v3,v4] using stage2Part1_run ({s with memory := s.memory}) v2 v1 v0 w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 rest hcap hact
  have h2 : runInstructions stage2Part2Program {s with pc := N 3647,memory := s.memory,stack := w0::v4::v2::v1::v3::w0::w1::w2::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::rest} = some {s with pc := N 3655,memory := s.memory,stack := w0::v3::v9::w1::w2::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::rest} := by
    simpa only [stage2Part2Model,v5,v6,v7,v8,v9] using stage2Part2_run ({s with memory := s.memory}) w0 v4 v2 v1 v3 w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 rest hcap hact
  have h3 : runInstructions stage2Part3Program {s with pc := N 3655,memory := s.memory,stack := w0::v3::v9::w1::w2::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::rest} = some {s with pc := N 3663,memory := s.memory,stack := v12::v10::v9::w1::w2::w3::v11::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::rest} := by
    simpa only [stage2Part3Model,v10,v11,v12] using stage2Part3_run ({s with memory := s.memory}) w0 v3 v9 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 rest hcap hact
  have h4 : runInstructions stage2Part4Program {s with pc := N 3663,memory := s.memory,stack := v12::v10::v9::w1::w2::w3::v11::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::rest} = some {s with pc := N 3671,memory := s.memory,stack := w10::w8::v15::v9::w1::w2::w3::v11::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::rest} := by
    simpa only [stage2Part4Model,v13,v14,v15] using stage2Part4_run ({s with memory := s.memory}) v12 v10 v9 w1 w2 w3 v11 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 rest hcap hact
  have h5 : runInstructions stage2Part5Program {s with pc := N 3671,memory := s.memory,stack := w10::w8::v15::v9::w1::w2::w3::v11::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::rest} = some {s with pc := N 3682,memory := s.memory,stack := v9::v18::w12::w8::v17::w8::w1::w2::w3::v11::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::rest} := by
    simpa only [stage2Part5Model,v16,v17,v18] using stage2Part5_run ({s with memory := s.memory}) w10 w8 v15 v9 w1 w2 w3 v11 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 rest hcap hact
  have h6 : runInstructions stage2Part6Program {s with pc := N 3682,memory := s.memory,stack := v9::v18::w12::w8::v17::w8::w1::w2::w3::v11::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::rest} = some {s with pc := N 3721,memory := v21,stack := v23::w8::w1::w2::w3::v11::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::rest} := by
    simpa only [stage2Part6Model,v19,v20,v21,v22,v23] using stage2Part6_run ({s with memory := s.memory}) v9 v18 w12 w8 v17 w8 w1 w2 w3 v11 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 rest hcap hact
  have h7 : runInstructions stage2Part7Program {s with pc := N 3721,memory := v21,stack := v23::w8::w1::w2::w3::v11::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::rest} = some {s with pc := N 3725,memory := v21,stack := v24::w1::w2::w3::v11::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::rest} := by
    simpa only [stage2Part7Model,v24] using stage2Part7_run ({s with memory := v21}) v23 w8 w1 w2 w3 v11 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 rest hcap hact
  exact (runInstructions_append_some _ _ _ _ _ h0 (runInstructions_append_some _ _ _ _ _ h1 (runInstructions_append_some _ _ _ _ _ h2 (runInstructions_append_some _ _ _ _ _ h3 (runInstructions_append_some _ _ _ _ _ h4 (runInstructions_append_some _ _ _ _ _ h5 (runInstructions_append_some _ _ _ _ _ h6 h7)))))))
#print axioms stage2_run
end R9InvConsumeExec
