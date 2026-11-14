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
def stage13Part0Program : List Instr := [.op (.Dup dA15),.op (.Swap sA0),.op (.Dup dA15),.push 1 128,.op .MLOAD,.op (.Dup dA0),.op .ADD]
def stage13Part0Model (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 : W) (rest : List W) : State :=
  let v0 : W := MachineState.readWord (s.memory) 128
  let v1 : W := v0 + v0
  {s with pc := N 5419,memory := s.memory,stack := v1::w14::w0::w15::w1::w2::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::rest}
theorem stage13Part0_run (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions stage13Part0Program {s with pc := N 5411,memory := s.memory,stack := w0::w1::w2::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::rest} = some (stage13Part0Model s w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 63) : rest.length+j < 1024 := by omega
  have ha128 : (128 : W).toNat = 128 := rfl
  have hf128 := Monpro.activeWords_fix s 128 32 (by decide) (by norm_num) hact
  simp [hz,hzn,stage13Part0Program,stage13Part0Model,runInstructions,runInstr,List.exchange,succ_ofNat_mod,ofNat_add_mod,Nat.add_assoc,State.activeWordsAfterUInt256,literal_eq_ofNat,capacity,ha128,hf128]
def stage13Part1Program : List Instr := [.op (.Dup dA14),.op (.Dup dA12),.op (.Dup dA5),.op (.Dup dA2),.op .MULMOD,.op (.Dup dA13),.op (.Dup dA3)]
def stage13Part1Model (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 : W) (rest : List W) : State :=
  let v0 : W := UInt256.mulMod w14 w3 w11
  {s with pc := N 5426,memory := s.memory,stack := w0::w11::v0::w14::w0::w1::w2::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::w16::w17::w18::rest}
theorem stage13Part1_run (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions stage13Part1Program {s with pc := N 5419,memory := s.memory,stack := w0::w1::w2::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::w16::w17::w18::rest} = some (stage13Part1Model s w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 63) : rest.length+j < 1024 := by omega
  simp [hz,hzn,stage13Part1Program,stage13Part1Model,runInstructions,runInstr,List.exchange,succ_ofNat_mod,ofNat_add_mod,Nat.add_assoc,State.activeWordsAfterUInt256,literal_eq_ofNat,capacity]
def stage13Part2Program : List Instr := [.op (.Dup dA5),.op .MULMOD,.op .ADD,.op (.Dup dA4),.op .ADD,.op (.Swap sA4),.op .MUL,.op (.Swap sA1)]
def stage13Part2Model (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 w20 w21 w22 : W) (rest : List W) : State :=
  let v0 : W := UInt256.mulMod w5 w0 w1
  let v1 : W := v0 + w2
  let v2 : W := w6 + v1
  let v3 : W := w7 * w3
  {s with pc := N 5434,memory := s.memory,stack := w5::w4::v3::w6::v2::w8::w9::w10::w11::w12::w13::w14::w15::w16::w17::w18::w19::w20::w21::w22::rest}
theorem stage13Part2_run (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 w20 w21 w22 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions stage13Part2Program {s with pc := N 5426,memory := s.memory,stack := w0::w1::w2::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::w16::w17::w18::w19::w20::w21::w22::rest} = some (stage13Part2Model s w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 w20 w21 w22 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 63) : rest.length+j < 1024 := by omega
  simp [hz,hzn,stage13Part2Program,stage13Part2Model,runInstructions,runInstr,List.exchange,succ_ofNat_mod,ofNat_add_mod,Nat.add_assoc,State.activeWordsAfterUInt256,literal_eq_ofNat,capacity]
def stage13Part3Program : List Instr := [.op .MUL,.op .ADD,.op .ADD,.op (.Dup dA6),.op (.Dup dA11),.op .MUL,.op .ADD,.op (.Dup dA5)]
def stage13Part3Model (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 : W) (rest : List W) : State :=
  let v0 : W := w0 * w1
  let v1 : W := v0 + w2
  let v2 : W := v1 + w3
  let v3 : W := w13 * w9
  let v4 : W := v3 + v2
  {s with pc := N 5442,memory := s.memory,stack := w8::v4::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::w16::w17::w18::w19::rest}
theorem stage13Part3_run (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions stage13Part3Program {s with pc := N 5434,memory := s.memory,stack := w0::w1::w2::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::w16::w17::w18::w19::rest} = some (stage13Part3Model s w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 63) : rest.length+j < 1024 := by omega
  simp [hz,hzn,stage13Part3Program,stage13Part3Model,runInstructions,runInstr,List.exchange,succ_ofNat_mod,ofNat_add_mod,Nat.add_assoc,State.activeWordsAfterUInt256,literal_eq_ofNat,capacity]
def stage13Part4Program : List Instr := [.op (.Dup dA9),.op .MUL,.op .ADD,.op (.Dup dA11),.op (.Dup dA4),.op .MUL,.op .ADD,.op (.Dup dA7)]
def stage13Part4Model (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 : W) (rest : List W) : State :=
  let v0 : W := w9 * w0
  let v1 : W := v0 + w1
  let v2 : W := w4 * w12
  let v3 : W := v2 + v1
  {s with pc := N 5450,memory := s.memory,stack := w8::v3::w2::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::w16::w17::rest}
theorem stage13Part4_run (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions stage13Part4Program {s with pc := N 5442,memory := s.memory,stack := w0::w1::w2::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::w16::w17::rest} = some (stage13Part4Model s w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 63) : rest.length+j < 1024 := by omega
  simp [hz,hzn,stage13Part4Program,stage13Part4Model,runInstructions,runInstr,List.exchange,succ_ofNat_mod,ofNat_add_mod,Nat.add_assoc,State.activeWordsAfterUInt256,literal_eq_ofNat,capacity]
def stage13Part5Program : List Instr := [.op (.Dup dA14),.op .MUL,.op .ADD,.op (.Swap sA0),.op (.Dup dA9),.op (.Dup dA7),.op (.Dup dA12),.op .MULMOD]
def stage13Part5Model (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 : W) (rest : List W) : State :=
  let v0 : W := w14 * w0
  let v1 : W := v0 + w1
  let v2 : W := UInt256.mulMod w11 w7 w10
  {s with pc := N 5458,memory := s.memory,stack := v2::w2::v1::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::w16::w17::rest}
theorem stage13Part5_run (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions stage13Part5Program {s with pc := N 5450,memory := s.memory,stack := w0::w1::w2::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::w16::w17::rest} = some (stage13Part5Model s w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 63) : rest.length+j < 1024 := by omega
  simp [hz,hzn,stage13Part5Program,stage13Part5Model,runInstructions,runInstr,List.exchange,succ_ofNat_mod,ofNat_add_mod,Nat.add_assoc,State.activeWordsAfterUInt256,literal_eq_ofNat,capacity]
def stage13Part6Program : List Instr := [.op .ADD,.op (.Dup dA9),.op (.Dup dA6),.op (.Dup dA10),.op .MULMOD,.op .ADD,.op (.Dup dA9),.op (.Dup dA4)]
def stage13Part6Model (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 : W) (rest : List W) : State :=
  let v0 : W := w0 + w1
  let v1 : W := UInt256.mulMod w9 w6 w10
  let v2 : W := v1 + v0
  {s with pc := N 5466,memory := s.memory,stack := w4::w10::v2::w2::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::w16::w17::rest}
theorem stage13Part6_run (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions stage13Part6Program {s with pc := N 5458,memory := s.memory,stack := w0::w1::w2::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::w16::w17::rest} = some (stage13Part6Model s w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 63) : rest.length+j < 1024 := by omega
  simp [hz,hzn,stage13Part6Program,stage13Part6Model,runInstructions,runInstr,List.exchange,succ_ofNat_mod,ofNat_add_mod,Nat.add_assoc,State.activeWordsAfterUInt256,literal_eq_ofNat,capacity]
def stage13Part7Program : List Instr := [.op (.Dup dA13),.op .MULMOD,.op .ADD,.op (.Dup dA9),.op (.Dup dA8),.op (.Dup dA15),.op .MULMOD,.op .ADD]
def stage13Part7Model (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 : W) (rest : List W) : State :=
  let v0 : W := UInt256.mulMod w13 w0 w1
  let v1 : W := v0 + w2
  let v2 : W := UInt256.mulMod w15 w9 w11
  let v3 : W := v2 + v1
  {s with pc := N 5474,memory := s.memory,stack := v3::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::w16::w17::w18::rest}
theorem stage13Part7_run (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions stage13Part7Program {s with pc := N 5466,memory := s.memory,stack := w0::w1::w2::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::w16::w17::w18::rest} = some (stage13Part7Model s w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 63) : rest.length+j < 1024 := by omega
  simp [hz,hzn,stage13Part7Program,stage13Part7Model,runInstructions,runInstr,List.exchange,succ_ofNat_mod,ofNat_add_mod,Nat.add_assoc,State.activeWordsAfterUInt256,literal_eq_ofNat,capacity]
def stage13Part8Program : List Instr := [.op (.Swap sA0),.push 30 1766847064778384329583297500742918515827483896875618958121606201292619775,.op .AND,.op (.Dup dA0),.push 1 64,.op .MSTORE,.op (.Dup dA9),.op (.Swap sA1)]
def stage13Part8Model (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 : W) (rest : List W) : State :=
  let v0 : W := UInt256.land (N 1766847064778384329583297500742918515827483896875618958121606201292619775) w1
  let v1 : ByteArray := MachineState.writeBytes (s.memory) (Data.Bytes.natToBytesPadded v0.toNat 32) 64
  {s with pc := N 5513,memory := v1,stack := w0::v0::w9::w2::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::w16::rest}
theorem stage13Part8_run (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions stage13Part8Program {s with pc := N 5474,memory := s.memory,stack := w0::w1::w2::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::w16::rest} = some (stage13Part8Model s w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 63) : rest.length+j < 1024 := by omega
  have ha64 : (64 : W).toNat = 64 := rfl
  have hf64 := Monpro.activeWords_fix s 64 32 (by decide) (by norm_num) hact
  simp [hz,hzn,stage13Part8Program,stage13Part8Model,runInstructions,runInstr,List.exchange,succ_ofNat_mod,ofNat_add_mod,Nat.add_assoc,State.activeWordsAfterUInt256,literal_eq_ofNat,capacity,ha64,hf64]
def stage13Part9Program : List Instr := [.op .SUB,.op (.Dup dA1),.op .ADD,.push 2 2048,.op .MULMOD]
def stage13Part9Model (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 : W) (rest : List W) : State :=
  let v0 : W := w0 - w1
  let v1 : W := w2 + v0
  let v2 : W := UInt256.mulMod (N 2048) v1 w2
  {s with pc := N 5520,memory := s.memory,stack := v2::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::w16::w17::rest}
theorem stage13Part9_run (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions stage13Part9Program {s with pc := N 5513,memory := s.memory,stack := w0::w1::w2::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::w16::w17::rest} = some (stage13Part9Model s w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 63) : rest.length+j < 1024 := by omega
  have ha2048 : (2048 : W).toNat = 2048 := rfl
  have hf2048 := Monpro.activeWords_fix s 2048 32 (by decide) (by norm_num) hact
  simp [hz,hzn,stage13Part9Program,stage13Part9Model,runInstructions,runInstr,List.exchange,succ_ofNat_mod,ofNat_add_mod,Nat.add_assoc,State.activeWordsAfterUInt256,literal_eq_ofNat,capacity,ha2048,hf2048]
def stage13Program : List Instr := (stage13Part0Program++(stage13Part1Program++(stage13Part2Program++(stage13Part3Program++(stage13Part4Program++(stage13Part5Program++(stage13Part6Program++(stage13Part7Program++(stage13Part8Program++stage13Part9Program)))))))))
def stage13Model (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 : W) (rest : List W) : State :=
  let v0 : W := MachineState.readWord (s.memory) 128
  let v1 : W := v0 + v0
  let v2 : W := UInt256.mulMod w11 w15 w8
  let v3 : W := UInt256.mulMod w14 v1 w8
  let v4 : W := v3 + v2
  let v5 : W := w0 + v4
  let v6 : W := w15 * w11
  let v7 : W := w14 * v1
  let v8 : W := v7 + v6
  let v9 : W := v8 + w0
  let v10 : W := w9 * w5
  let v11 : W := v10 + v9
  let v12 : W := w7 * w4
  let v13 : W := v12 + v11
  let v14 : W := w2 * w10
  let v15 : W := v14 + v13
  let v16 : W := w12 * w6
  let v17 : W := v16 + v15
  let v18 : W := UInt256.mulMod w9 w5 w8
  let v19 : W := v18 + v5
  let v20 : W := UInt256.mulMod w7 w4 w8
  let v21 : W := v20 + v19
  let v22 : W := UInt256.mulMod w10 w2 w8
  let v23 : W := v22 + v21
  let v24 : W := UInt256.mulMod w12 w6 w8
  let v25 : W := v24 + v23
  let v26 : W := UInt256.land (N 1766847064778384329583297500742918515827483896875618958121606201292619775) v17
  let v27 : ByteArray := MachineState.writeBytes (s.memory) (Data.Bytes.natToBytesPadded v26.toNat 32) 64
  let v28 : W := v25 - v26
  let v29 : W := w8 + v28
  let v30 : W := UInt256.mulMod (N 2048) v29 w8
  {s with pc := N 5520,memory := v27,stack := v30::w1::w2::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::rest}
theorem stage13_run (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions stage13Program {s with pc := N 5411,memory := s.memory,stack := w0::w1::w2::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::rest} = some (stage13Model s w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 rest) := by
  let v0 : W := MachineState.readWord (s.memory) 128
  let v1 : W := v0 + v0
  let v2 : W := UInt256.mulMod w11 w15 w8
  let v3 : W := UInt256.mulMod w14 v1 w8
  let v4 : W := v3 + v2
  let v5 : W := w0 + v4
  let v6 : W := w15 * w11
  let v7 : W := w14 * v1
  let v8 : W := v7 + v6
  let v9 : W := v8 + w0
  let v10 : W := w9 * w5
  let v11 : W := v10 + v9
  let v12 : W := w7 * w4
  let v13 : W := v12 + v11
  let v14 : W := w2 * w10
  let v15 : W := v14 + v13
  let v16 : W := w12 * w6
  let v17 : W := v16 + v15
  let v18 : W := UInt256.mulMod w9 w5 w8
  let v19 : W := v18 + v5
  let v20 : W := UInt256.mulMod w7 w4 w8
  let v21 : W := v20 + v19
  let v22 : W := UInt256.mulMod w10 w2 w8
  let v23 : W := v22 + v21
  let v24 : W := UInt256.mulMod w12 w6 w8
  let v25 : W := v24 + v23
  let v26 : W := UInt256.land (N 1766847064778384329583297500742918515827483896875618958121606201292619775) v17
  let v27 : ByteArray := MachineState.writeBytes (s.memory) (Data.Bytes.natToBytesPadded v26.toNat 32) 64
  let v28 : W := v25 - v26
  let v29 : W := w8 + v28
  let v30 : W := UInt256.mulMod (N 2048) v29 w8
  have h0 : runInstructions stage13Part0Program {s with pc := N 5411,memory := s.memory,stack := w0::w1::w2::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::rest} = some {s with pc := N 5419,memory := s.memory,stack := v1::w14::w0::w15::w1::w2::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::rest} := by
    simpa only [stage13Part0Model,v0,v1] using stage13Part0_run ({s with memory := s.memory}) w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 rest hcap hact
  have h1 : runInstructions stage13Part1Program {s with pc := N 5419,memory := s.memory,stack := v1::w14::w0::w15::w1::w2::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::rest} = some {s with pc := N 5426,memory := s.memory,stack := v1::w8::v2::w11::v1::w14::w0::w15::w1::w2::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::rest} := by
    simpa only [stage13Part1Model,v2] using stage13Part1_run ({s with memory := s.memory}) v1 w14 w0 w15 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 rest hcap hact
  have h2 : runInstructions stage13Part2Program {s with pc := N 5426,memory := s.memory,stack := v1::w8::v2::w11::v1::w14::w0::w15::w1::w2::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::rest} = some {s with pc := N 5434,memory := s.memory,stack := w14::v1::v6::w0::v5::w1::w2::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::rest} := by
    simpa only [stage13Part2Model,v3,v4,v5,v6] using stage13Part2_run ({s with memory := s.memory}) v1 w8 v2 w11 v1 w14 w0 w15 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 rest hcap hact
  have h3 : runInstructions stage13Part3Program {s with pc := N 5434,memory := s.memory,stack := w14::v1::v6::w0::v5::w1::w2::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::rest} = some {s with pc := N 5442,memory := s.memory,stack := w4::v11::v5::w1::w2::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::rest} := by
    simpa only [stage13Part3Model,v7,v8,v9,v10,v11] using stage13Part3_run ({s with memory := s.memory}) w14 v1 v6 w0 v5 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 rest hcap hact
  have h4 : runInstructions stage13Part4Program {s with pc := N 5442,memory := s.memory,stack := w4::v11::v5::w1::w2::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::rest} = some {s with pc := N 5450,memory := s.memory,stack := w6::v15::v5::w1::w2::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::rest} := by
    simpa only [stage13Part4Model,v12,v13,v14,v15] using stage13Part4_run ({s with memory := s.memory}) w4 v11 v5 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 rest hcap hact
  have h5 : runInstructions stage13Part5Program {s with pc := N 5450,memory := s.memory,stack := w6::v15::v5::w1::w2::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::rest} = some {s with pc := N 5458,memory := s.memory,stack := v18::v5::v17::w1::w2::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::rest} := by
    simpa only [stage13Part5Model,v16,v17,v18] using stage13Part5_run ({s with memory := s.memory}) w6 v15 v5 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 rest hcap hact
  have h6 : runInstructions stage13Part6Program {s with pc := N 5458,memory := s.memory,stack := v18::v5::v17::w1::w2::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::rest} = some {s with pc := N 5466,memory := s.memory,stack := w2::w8::v21::v17::w1::w2::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::rest} := by
    simpa only [stage13Part6Model,v19,v20,v21] using stage13Part6_run ({s with memory := s.memory}) v18 v5 v17 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 rest hcap hact
  have h7 : runInstructions stage13Part7Program {s with pc := N 5466,memory := s.memory,stack := w2::w8::v21::v17::w1::w2::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::rest} = some {s with pc := N 5474,memory := s.memory,stack := v25::v17::w1::w2::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::rest} := by
    simpa only [stage13Part7Model,v22,v23,v24,v25] using stage13Part7_run ({s with memory := s.memory}) w2 w8 v21 v17 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 rest hcap hact
  have h8 : runInstructions stage13Part8Program {s with pc := N 5474,memory := s.memory,stack := v25::v17::w1::w2::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::rest} = some {s with pc := N 5513,memory := v27,stack := v25::v26::w8::w1::w2::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::rest} := by
    simpa only [stage13Part8Model,v26,v27] using stage13Part8_run ({s with memory := s.memory}) v25 v17 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 rest hcap hact
  have h9 : runInstructions stage13Part9Program {s with pc := N 5513,memory := v27,stack := v25::v26::w8::w1::w2::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::rest} = some {s with pc := N 5520,memory := v27,stack := v30::w1::w2::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::rest} := by
    simpa only [stage13Part9Model,v28,v29,v30] using stage13Part9_run ({s with memory := v27}) v25 v26 w8 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 rest hcap hact
  exact (runInstructions_append_some _ _ _ _ _ h0 (runInstructions_append_some _ _ _ _ _ h1 (runInstructions_append_some _ _ _ _ _ h2 (runInstructions_append_some _ _ _ _ _ h3 (runInstructions_append_some _ _ _ _ _ h4 (runInstructions_append_some _ _ _ _ _ h5 (runInstructions_append_some _ _ _ _ _ h6 (runInstructions_append_some _ _ _ _ _ h7 (runInstructions_append_some _ _ _ _ _ h8 h9)))))))))
#print axioms stage13_run
end R9InvConsumeExec
