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
def stage14Part0Program : List Instr := [.push 2 832,.op .MLOAD,.op (.Swap sA5),.op .POP,.op (.Dup dA15),.op (.Dup dA9),.push 1 128,.op .MLOAD]
def stage14Part0Model (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 : W) (rest : List W) : State :=
  let v0 : W := MachineState.readWord (s.memory) 832
  let v1 : W := MachineState.readWord (s.memory) 128
  {s with pc := N 5529,memory := s.memory,stack := v1::w8::w15::w0::w1::w2::w3::w4::v0::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::rest}
theorem stage14Part0_run (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions stage14Part0Program {s with pc := N 5518,memory := s.memory,stack := w0::w1::w2::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::rest} = some (stage14Part0Model s w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 63) : rest.length+j < 1024 := by omega
  have ha128 : (128 : W).toNat = 128 := rfl
  have hf128 := Monpro.activeWords_fix s 128 32 (by decide) (by norm_num) hact
  have ha832 : (832 : W).toNat = 832 := rfl
  have hf832 := Monpro.activeWords_fix s 832 32 (by decide) (by norm_num) hact
  simp [hz,hzn,stage14Part0Program,stage14Part0Model,runInstructions,runInstr,List.exchange,succ_ofNat_mod,ofNat_add_mod,Nat.add_assoc,State.activeWordsAfterUInt256,literal_eq_ofNat,capacity,ha128,hf128,ha832,hf832]
def stage14Part1Program : List Instr := [.op (.Dup dA0),.op .ADD,.op (.Dup dA0),.op (.Dup dA3),.op .MUL,.op (.Swap sA2),.op .MULMOD,.op (.Dup dA2)]
def stage14Part1Model (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 : W) (rest : List W) : State :=
  let v0 : W := w0 + w0
  let v1 : W := w2 * v0
  let v2 : W := UInt256.mulMod w2 v0 w1
  {s with pc := N 5537,memory := s.memory,stack := w3::v2::v1::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::w16::w17::w18::rest}
theorem stage14Part1_run (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions stage14Part1Program {s with pc := N 5529,memory := s.memory,stack := w0::w1::w2::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::w16::w17::w18::rest} = some (stage14Part1Model s w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 63) : rest.length+j < 1024 := by omega
  simp [hz,hzn,stage14Part1Program,stage14Part1Model,runInstructions,runInstr,List.exchange,succ_ofNat_mod,ofNat_add_mod,Nat.add_assoc,State.activeWordsAfterUInt256,literal_eq_ofNat,capacity]
def stage14Part2Program : List Instr := [.op .ADD,.op (.Swap sA1),.op .ADD,.op (.Dup dA15),.op (.Dup dA0),.op .MUL,.op .ADD]
def stage14Part2Model (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 : W) (rest : List W) : State :=
  let v0 : W := w0 + w1
  let v1 : W := w3 + w2
  let v2 : W := w17 * w17
  let v3 : W := v2 + v1
  {s with pc := N 5544,memory := s.memory,stack := v3::v0::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::w16::w17::w18::rest}
theorem stage14Part2_run (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions stage14Part2Program {s with pc := N 5537,memory := s.memory,stack := w0::w1::w2::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::w16::w17::w18::rest} = some (stage14Part2Model s w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 63) : rest.length+j < 1024 := by omega
  simp [hz,hzn,stage14Part2Program,stage14Part2Model,runInstructions,runInstr,List.exchange,succ_ofNat_mod,ofNat_add_mod,Nat.add_assoc,State.activeWordsAfterUInt256,literal_eq_ofNat,capacity]
def stage14Part3Program : List Instr := [.op (.Dup dA5),.op (.Dup dA11),.op .MUL,.op .ADD,.op (.Dup dA11),.op (.Dup dA9),.op .MUL,.op .ADD]
def stage14Part3Model (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 : W) (rest : List W) : State :=
  let v0 : W := w10 * w5
  let v1 : W := v0 + w0
  let v2 : W := w8 * w11
  let v3 : W := v2 + v1
  {s with pc := N 5552,memory := s.memory,stack := v3::w1::w2::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::w16::rest}
theorem stage14Part3_run (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions stage14Part3Program {s with pc := N 5544,memory := s.memory,stack := w0::w1::w2::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::w16::rest} = some (stage14Part3Model s w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 63) : rest.length+j < 1024 := by omega
  simp [hz,hzn,stage14Part3Program,stage14Part3Model,runInstructions,runInstr,List.exchange,succ_ofNat_mod,ofNat_add_mod,Nat.add_assoc,State.activeWordsAfterUInt256,literal_eq_ofNat,capacity]
def stage14Part4Program : List Instr := [.op (.Dup dA3),.op (.Dup dA14),.op .MUL,.op .ADD,.op (.Swap sA0),.op (.Dup dA9),.push 1 160,.op .MLOAD]
def stage14Part4Model (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 : W) (rest : List W) : State :=
  let v0 : W := w13 * w3
  let v1 : W := v0 + w0
  let v2 : W := MachineState.readWord (s.memory) 160
  {s with pc := N 5561,memory := s.memory,stack := v2::w9::w1::v1::w2::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::w16::rest}
theorem stage14Part4_run (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions stage14Part4Program {s with pc := N 5552,memory := s.memory,stack := w0::w1::w2::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::w16::rest} = some (stage14Part4Model s w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 63) : rest.length+j < 1024 := by omega
  have ha160 : (160 : W).toNat = 160 := rfl
  have hf160 := Monpro.activeWords_fix s 160 32 (by decide) (by norm_num) hact
  simp [hz,hzn,stage14Part4Program,stage14Part4Model,runInstructions,runInstr,List.exchange,succ_ofNat_mod,ofNat_add_mod,Nat.add_assoc,State.activeWordsAfterUInt256,literal_eq_ofNat,capacity,ha160,hf160]
def stage14Part5Program : List Instr := [.op (.Dup dA0),.op .MULMOD,.op .ADD,.op (.Dup dA9),.op (.Dup dA6),.op (.Dup dA12),.op .MULMOD,.op .ADD]
def stage14Part5Model (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 : W) (rest : List W) : State :=
  let v0 : W := UInt256.mulMod w0 w0 w1
  let v1 : W := v0 + w2
  let v2 : W := UInt256.mulMod w12 w7 w11
  let v3 : W := v2 + v1
  {s with pc := N 5569,memory := s.memory,stack := v3::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::w16::w17::w18::rest}
theorem stage14Part5_run (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions stage14Part5Program {s with pc := N 5561,memory := s.memory,stack := w0::w1::w2::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::w16::w17::w18::rest} = some (stage14Part5Model s w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 63) : rest.length+j < 1024 := by omega
  simp [hz,hzn,stage14Part5Program,stage14Part5Model,runInstructions,runInstr,List.exchange,succ_ofNat_mod,ofNat_add_mod,Nat.add_assoc,State.activeWordsAfterUInt256,literal_eq_ofNat,capacity]
def stage14Part6Program : List Instr := [.op (.Dup dA9),.op (.Dup dA12),.op (.Dup dA10),.op .MULMOD,.op .ADD,.op (.Dup dA9),.op (.Dup dA14),.op (.Dup dA5)]
def stage14Part6Model (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 : W) (rest : List W) : State :=
  let v0 : W := UInt256.mulMod w8 w11 w9
  let v1 : W := v0 + w0
  {s with pc := N 5577,memory := s.memory,stack := w3::w13::w9::v1::w1::w2::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::w16::rest}
theorem stage14Part6_run (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions stage14Part6Program {s with pc := N 5569,memory := s.memory,stack := w0::w1::w2::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::w16::rest} = some (stage14Part6Model s w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 63) : rest.length+j < 1024 := by omega
  simp [hz,hzn,stage14Part6Program,stage14Part6Model,runInstructions,runInstr,List.exchange,succ_ofNat_mod,ofNat_add_mod,Nat.add_assoc,State.activeWordsAfterUInt256,literal_eq_ofNat,capacity]
def stage14Part7Program : List Instr := [.op .MULMOD,.op .ADD,.op (.Swap sA0),.push 30 1766847064778384329583297500742918515827483896875618958121606201292619775,.op .AND,.op (.Dup dA0),.op (.Swap sA12),.op .POP]
def stage14Part7Model (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 : W) (rest : List W) : State :=
  let v0 : W := UInt256.mulMod w0 w1 w2
  let v1 : W := v0 + w3
  let v2 : W := UInt256.land (N 1766847064778384329583297500742918515827483896875618958121606201292619775) w4
  {s with pc := N 5615,memory := s.memory,stack := v2::v1::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::v2::w16::w17::w18::w19::rest}
theorem stage14Part7_run (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions stage14Part7Program {s with pc := N 5577,memory := s.memory,stack := w0::w1::w2::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::w16::w17::w18::w19::rest} = some (stage14Part7Model s w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 63) : rest.length+j < 1024 := by omega
  simp [hz,hzn,stage14Part7Program,stage14Part7Model,runInstructions,runInstr,List.exchange,succ_ofNat_mod,ofNat_add_mod,Nat.add_assoc,State.activeWordsAfterUInt256,literal_eq_ofNat,capacity]
def stage14Part8Program : List Instr := [.op (.Dup dA9),.op (.Swap sA1),.op .SUB,.op (.Dup dA1),.op .ADD,.push 2 2048,.op .MULMOD]
def stage14Part8Model (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 : W) (rest : List W) : State :=
  let v0 : W := w1 - w0
  let v1 : W := w9 + v0
  let v2 : W := UInt256.mulMod (N 2048) v1 w9
  {s with pc := N 5624,memory := s.memory,stack := v2::w2::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::w16::rest}
theorem stage14Part8_run (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions stage14Part8Program {s with pc := N 5615,memory := s.memory,stack := w0::w1::w2::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::w16::rest} = some (stage14Part8Model s w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 63) : rest.length+j < 1024 := by omega
  have ha2048 : (2048 : W).toNat = 2048 := rfl
  have hf2048 := Monpro.activeWords_fix s 2048 32 (by decide) (by norm_num) hact
  simp [hz,hzn,stage14Part8Program,stage14Part8Model,runInstructions,runInstr,List.exchange,succ_ofNat_mod,ofNat_add_mod,Nat.add_assoc,State.activeWordsAfterUInt256,literal_eq_ofNat,capacity,ha2048,hf2048]
def stage14Program : List Instr := (stage14Part0Program++(stage14Part1Program++(stage14Part2Program++(stage14Part3Program++(stage14Part4Program++(stage14Part5Program++(stage14Part6Program++(stage14Part7Program++stage14Part8Program))))))))
def stage14Model (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 : W) (rest : List W) : State :=
  let v0 : W := MachineState.readWord (s.memory) 832
  let v1 : W := MachineState.readWord (s.memory) 128
  let v2 : W := v1 + v1
  let v3 : W := w15 * v2
  let v4 : W := UInt256.mulMod w15 v2 w8
  let v5 : W := w0 + v4
  let v6 : W := w0 + v3
  let v7 : W := w14 * w14
  let v8 : W := v7 + v6
  let v9 : W := w9 * w4
  let v10 : W := v9 + v8
  let v11 : W := w7 * w10
  let v12 : W := v11 + v10
  let v13 : W := w12 * w2
  let v14 : W := v13 + v12
  let v15 : W := MachineState.readWord (s.memory) 160
  let v16 : W := UInt256.mulMod v15 v15 w8
  let v17 : W := v16 + v5
  let v18 : W := UInt256.mulMod w9 w4 w8
  let v19 : W := v18 + v17
  let v20 : W := UInt256.mulMod w7 w10 w8
  let v21 : W := v20 + v19
  let v22 : W := UInt256.mulMod w2 w12 w8
  let v23 : W := v22 + v21
  let v24 : W := UInt256.land (N 1766847064778384329583297500742918515827483896875618958121606201292619775) v14
  let v25 : W := v23 - v24
  let v26 : W := w8 + v25
  let v27 : W := UInt256.mulMod (N 2048) v26 w8
  {s with pc := N 5624,memory := s.memory,stack := v27::w1::w2::w3::w4::v0::w6::w7::w8::w9::w10::v24::w12::w13::w14::w15::rest}
theorem stage14_run (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions stage14Program {s with pc := N 5518,memory := s.memory,stack := w0::w1::w2::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::rest} = some (stage14Model s w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 rest) := by
  let v0 : W := MachineState.readWord (s.memory) 832
  let v1 : W := MachineState.readWord (s.memory) 128
  let v2 : W := v1 + v1
  let v3 : W := w15 * v2
  let v4 : W := UInt256.mulMod w15 v2 w8
  let v5 : W := w0 + v4
  let v6 : W := w0 + v3
  let v7 : W := w14 * w14
  let v8 : W := v7 + v6
  let v9 : W := w9 * w4
  let v10 : W := v9 + v8
  let v11 : W := w7 * w10
  let v12 : W := v11 + v10
  let v13 : W := w12 * w2
  let v14 : W := v13 + v12
  let v15 : W := MachineState.readWord (s.memory) 160
  let v16 : W := UInt256.mulMod v15 v15 w8
  let v17 : W := v16 + v5
  let v18 : W := UInt256.mulMod w9 w4 w8
  let v19 : W := v18 + v17
  let v20 : W := UInt256.mulMod w7 w10 w8
  let v21 : W := v20 + v19
  let v22 : W := UInt256.mulMod w2 w12 w8
  let v23 : W := v22 + v21
  let v24 : W := UInt256.land (N 1766847064778384329583297500742918515827483896875618958121606201292619775) v14
  let v25 : W := v23 - v24
  let v26 : W := w8 + v25
  let v27 : W := UInt256.mulMod (N 2048) v26 w8
  have h0 : runInstructions stage14Part0Program {s with pc := N 5518,memory := s.memory,stack := w0::w1::w2::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::rest} = some {s with pc := N 5529,memory := s.memory,stack := v1::w8::w15::w0::w1::w2::w3::w4::v0::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::rest} := by
    simpa only [stage14Part0Model,v0,v1] using stage14Part0_run ({s with memory := s.memory}) w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 rest hcap hact
  have h1 : runInstructions stage14Part1Program {s with pc := N 5529,memory := s.memory,stack := v1::w8::w15::w0::w1::w2::w3::w4::v0::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::rest} = some {s with pc := N 5537,memory := s.memory,stack := w0::v4::v3::w0::w1::w2::w3::w4::v0::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::rest} := by
    simpa only [stage14Part1Model,v2,v3,v4] using stage14Part1_run ({s with memory := s.memory}) v1 w8 w15 w0 w1 w2 w3 w4 v0 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 rest hcap hact
  have h2 : runInstructions stage14Part2Program {s with pc := N 5537,memory := s.memory,stack := w0::v4::v3::w0::w1::w2::w3::w4::v0::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::rest} = some {s with pc := N 5544,memory := s.memory,stack := v8::v5::w1::w2::w3::w4::v0::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::rest} := by
    simpa only [stage14Part2Model,v5,v6,v7,v8] using stage14Part2_run ({s with memory := s.memory}) w0 v4 v3 w0 w1 w2 w3 w4 v0 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 rest hcap hact
  have h3 : runInstructions stage14Part3Program {s with pc := N 5544,memory := s.memory,stack := v8::v5::w1::w2::w3::w4::v0::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::rest} = some {s with pc := N 5552,memory := s.memory,stack := v12::v5::w1::w2::w3::w4::v0::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::rest} := by
    simpa only [stage14Part3Model,v9,v10,v11,v12] using stage14Part3_run ({s with memory := s.memory}) v8 v5 w1 w2 w3 w4 v0 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 rest hcap hact
  have h4 : runInstructions stage14Part4Program {s with pc := N 5552,memory := s.memory,stack := v12::v5::w1::w2::w3::w4::v0::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::rest} = some {s with pc := N 5561,memory := s.memory,stack := v15::w8::v5::v14::w1::w2::w3::w4::v0::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::rest} := by
    simpa only [stage14Part4Model,v13,v14,v15] using stage14Part4_run ({s with memory := s.memory}) v12 v5 w1 w2 w3 w4 v0 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 rest hcap hact
  have h5 : runInstructions stage14Part5Program {s with pc := N 5561,memory := s.memory,stack := v15::w8::v5::v14::w1::w2::w3::w4::v0::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::rest} = some {s with pc := N 5569,memory := s.memory,stack := v19::v14::w1::w2::w3::w4::v0::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::rest} := by
    simpa only [stage14Part5Model,v16,v17,v18,v19] using stage14Part5_run ({s with memory := s.memory}) v15 w8 v5 v14 w1 w2 w3 w4 v0 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 rest hcap hact
  have h6 : runInstructions stage14Part6Program {s with pc := N 5569,memory := s.memory,stack := v19::v14::w1::w2::w3::w4::v0::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::rest} = some {s with pc := N 5577,memory := s.memory,stack := w2::w12::w8::v21::v14::w1::w2::w3::w4::v0::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::rest} := by
    simpa only [stage14Part6Model,v20,v21] using stage14Part6_run ({s with memory := s.memory}) v19 v14 w1 w2 w3 w4 v0 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 rest hcap hact
  have h7 : runInstructions stage14Part7Program {s with pc := N 5577,memory := s.memory,stack := w2::w12::w8::v21::v14::w1::w2::w3::w4::v0::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::rest} = some {s with pc := N 5615,memory := s.memory,stack := v24::v23::w1::w2::w3::w4::v0::w6::w7::w8::w9::w10::v24::w12::w13::w14::w15::rest} := by
    simpa only [stage14Part7Model,v22,v23,v24] using stage14Part7_run ({s with memory := s.memory}) w2 w12 w8 v21 v14 w1 w2 w3 w4 v0 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 rest hcap hact
  have h8 : runInstructions stage14Part8Program {s with pc := N 5615,memory := s.memory,stack := v24::v23::w1::w2::w3::w4::v0::w6::w7::w8::w9::w10::v24::w12::w13::w14::w15::rest} = some {s with pc := N 5624,memory := s.memory,stack := v27::w1::w2::w3::w4::v0::w6::w7::w8::w9::w10::v24::w12::w13::w14::w15::rest} := by
    simpa only [stage14Part8Model,v25,v26,v27] using stage14Part8_run ({s with memory := s.memory}) v24 v23 w1 w2 w3 w4 v0 w6 w7 w8 w9 w10 v24 w12 w13 w14 w15 rest hcap hact
  exact (runInstructions_append_some _ _ _ _ _ h0 (runInstructions_append_some _ _ _ _ _ h1 (runInstructions_append_some _ _ _ _ _ h2 (runInstructions_append_some _ _ _ _ _ h3 (runInstructions_append_some _ _ _ _ _ h4 (runInstructions_append_some _ _ _ _ _ h5 (runInstructions_append_some _ _ _ _ _ h6 (runInstructions_append_some _ _ _ _ _ h7 h8))))))))
#print axioms stage14_run
end R9InvConsumeExec
