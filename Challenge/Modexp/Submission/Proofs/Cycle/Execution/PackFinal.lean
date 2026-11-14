import Challenge.Modexp.Submission.Proofs.Prepared.StackArgs
import Challenge.Modexp.Submission.Proofs.Fast.Monpro
import Challenge.Modexp.Submission.Proofs.Bytecode.WindowNibbleDefs
open CycleSubmission.SharedStackArgs
open EvmSemantics EvmSemantics.EVM YulEvmCompiler
open Challenge.EvmProof.Word Challenge.EvmProof.Stepper
open Challenge.Modexp.Submission.Proofs.Bytecode.WindowNibbleKernel
open Challenge.Modexp.Submission.Proofs.Fast
set_option maxRecDepth 40000
set_option maxHeartbeats 8000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
local notation "W" => UInt256
local notation "N" => UInt256.ofNat
namespace CycleSubmission.Execution
def packOverlapPart0Program : List Instr := [.op .JUMPDEST,.push 1 160,.op .MLOAD,.push 1 128,.op .MLOAD,.push 1 96,.op .MLOAD,.push 2 768,.op .MLOAD,.push 1 240,.op .MSTORE]
def packOverlapPart0Model (s : State) (f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 : W) (rest : List W) : State :=
  let v0 : W := MachineState.readWord (s.memory) 160
  let v1 : W := MachineState.readWord (s.memory) 128
  let v2 : W := MachineState.readWord (s.memory) 96
  let v3 : W := MachineState.readWord (s.memory) 768
  let v4 : ByteArray := MachineState.writeBytes (s.memory) (Data.Bytes.natToBytesPadded v3.toNat 32) 240
  {s with pc := N 8546,memory := v4,stack := v2::v1::v0::f0::f1::f2::f3::f4::f5::f6::f7::f8::f9::f10::f11::f12::f13::rest}
theorem packOverlapPart0_run (s : State) (f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 : W) (rest : List W) (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
 runInstructions packOverlapPart0Program {s with pc := N 8529,memory := s.memory,stack := f0::f1::f2::f3::f4::f5::f6::f7::f8::f9::f10::f11::f12::f13::rest} = some (packOverlapPart0Model s f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 rest) := by
 have hz : ({val := 0} : W) = N 0 := rfl
 have hzn : ({val := 0} : W).toNat = 0 := rfl
 have capacity (j : Nat) (hj : j ≤ 63) : rest.length+j < 1024 := by omega
 have ha96 : (96 : W).toNat = 96 := rfl
 have hf96 := Monpro.activeWords_fix s 96 32 (by decide) (by norm_num) hact
 have ha128 : (128 : W).toNat = 128 := rfl
 have hf128 := Monpro.activeWords_fix s 128 32 (by decide) (by norm_num) hact
 have ha160 : (160 : W).toNat = 160 := rfl
 have hf160 := Monpro.activeWords_fix s 160 32 (by decide) (by norm_num) hact
 have ha240 : (240 : W).toNat = 240 := rfl
 have hf240 := Monpro.activeWords_fix s 240 32 (by decide) (by norm_num) hact
 have ha768 : (768 : W).toNat = 768 := rfl
 have hf768 := Monpro.activeWords_fix s 768 32 (by decide) (by norm_num) hact
 simp [packOverlapPart0Program,packOverlapPart0Model,hz,hzn,runInstructions,runInstr,List.exchange,succ_ofNat_mod,ofNat_add_mod,Nat.add_assoc,State.activeWordsAfterUInt256,literal_eq_ofNat,capacity,ha96,hf96,ha128,hf128,ha160,hf160,ha240,hf240,ha768,hf768]
def packOverlapPart1Program : List Instr := [.op (.Dup dA6),.push 1 210,.op .MSTORE]
def packOverlapPart1Model (s : State) (f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 f16 : W) (rest : List W) : State :=
  let v0 : ByteArray := MachineState.writeBytes (s.memory) (Data.Bytes.natToBytesPadded f6.toNat 32) 210
  {s with pc := N 8550,memory := v0,stack := f0::f1::f2::f3::f4::f5::f6::f7::f8::f9::f10::f11::f12::f13::f14::f15::f16::rest}
theorem packOverlapPart1_run (s : State) (f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 f16 : W) (rest : List W) (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
 runInstructions packOverlapPart1Program {s with pc := N 8546,memory := s.memory,stack := f0::f1::f2::f3::f4::f5::f6::f7::f8::f9::f10::f11::f12::f13::f14::f15::f16::rest} = some (packOverlapPart1Model s f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 f16 rest) := by
 have hz : ({val := 0} : W) = N 0 := rfl
 have hzn : ({val := 0} : W).toNat = 0 := rfl
 have capacity (j : Nat) (hj : j ≤ 63) : rest.length+j < 1024 := by omega
 have ha210 : (210 : W).toNat = 210 := rfl
 have hf210 := Monpro.activeWords_fix s 210 32 (by decide) (by norm_num) hact
 simp [packOverlapPart1Program,packOverlapPart1Model,hz,hzn,runInstructions,runInstr,List.exchange,succ_ofNat_mod,ofNat_add_mod,Nat.add_assoc,State.activeWordsAfterUInt256,literal_eq_ofNat,capacity,ha210,hf210]
def packOverlapPart2Program : List Instr := [.op (.Dup dA7),.push 1 180,.op .MSTORE]
def packOverlapPart2Model (s : State) (f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 f16 : W) (rest : List W) : State :=
  let v0 : ByteArray := MachineState.writeBytes (s.memory) (Data.Bytes.natToBytesPadded f7.toNat 32) 180
  {s with pc := N 8554,memory := v0,stack := f0::f1::f2::f3::f4::f5::f6::f7::f8::f9::f10::f11::f12::f13::f14::f15::f16::rest}
theorem packOverlapPart2_run (s : State) (f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 f16 : W) (rest : List W) (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
 runInstructions packOverlapPart2Program {s with pc := N 8550,memory := s.memory,stack := f0::f1::f2::f3::f4::f5::f6::f7::f8::f9::f10::f11::f12::f13::f14::f15::f16::rest} = some (packOverlapPart2Model s f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 f16 rest) := by
 have hz : ({val := 0} : W) = N 0 := rfl
 have hzn : ({val := 0} : W).toNat = 0 := rfl
 have capacity (j : Nat) (hj : j ≤ 63) : rest.length+j < 1024 := by omega
 have ha180 : (180 : W).toNat = 180 := rfl
 have hf180 := Monpro.activeWords_fix s 180 32 (by decide) (by norm_num) hact
 simp [packOverlapPart2Program,packOverlapPart2Model,hz,hzn,runInstructions,runInstr,List.exchange,succ_ofNat_mod,ofNat_add_mod,Nat.add_assoc,State.activeWordsAfterUInt256,literal_eq_ofNat,capacity,ha180,hf180]
def packOverlapPart3Program : List Instr := [.push 1 32,.op .MLOAD,.push 1 150,.op .MSTORE]
def packOverlapPart3Model (s : State) (f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 f16 : W) (rest : List W) : State :=
  let v0 : W := MachineState.readWord (s.memory) 32
  let v1 : ByteArray := MachineState.writeBytes (s.memory) (Data.Bytes.natToBytesPadded v0.toNat 32) 150
  {s with pc := N 8560,memory := v1,stack := f0::f1::f2::f3::f4::f5::f6::f7::f8::f9::f10::f11::f12::f13::f14::f15::f16::rest}
theorem packOverlapPart3_run (s : State) (f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 f16 : W) (rest : List W) (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
 runInstructions packOverlapPart3Program {s with pc := N 8554,memory := s.memory,stack := f0::f1::f2::f3::f4::f5::f6::f7::f8::f9::f10::f11::f12::f13::f14::f15::f16::rest} = some (packOverlapPart3Model s f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 f16 rest) := by
 have hz : ({val := 0} : W) = N 0 := rfl
 have hzn : ({val := 0} : W).toNat = 0 := rfl
 have capacity (j : Nat) (hj : j ≤ 63) : rest.length+j < 1024 := by omega
 have ha32 : (32 : W).toNat = 32 := rfl
 have hf32 := Monpro.activeWords_fix s 32 32 (by decide) (by norm_num) hact
 have ha150 : (150 : W).toNat = 150 := rfl
 have hf150 := Monpro.activeWords_fix s 150 32 (by decide) (by norm_num) hact
 simp [packOverlapPart3Program,packOverlapPart3Model,hz,hzn,runInstructions,runInstr,List.exchange,succ_ofNat_mod,ofNat_add_mod,Nat.add_assoc,State.activeWordsAfterUInt256,literal_eq_ofNat,capacity,ha32,hf32,ha150,hf150]
def packOverlapPart4Program : List Instr := [.push 1 64,.op .MLOAD,.push 1 120,.op .MSTORE]
def packOverlapPart4Model (s : State) (f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 f16 : W) (rest : List W) : State :=
  let v0 : W := MachineState.readWord (s.memory) 64
  let v1 : ByteArray := MachineState.writeBytes (s.memory) (Data.Bytes.natToBytesPadded v0.toNat 32) 120
  {s with pc := N 8566,memory := v1,stack := f0::f1::f2::f3::f4::f5::f6::f7::f8::f9::f10::f11::f12::f13::f14::f15::f16::rest}
theorem packOverlapPart4_run (s : State) (f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 f16 : W) (rest : List W) (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
 runInstructions packOverlapPart4Program {s with pc := N 8560,memory := s.memory,stack := f0::f1::f2::f3::f4::f5::f6::f7::f8::f9::f10::f11::f12::f13::f14::f15::f16::rest} = some (packOverlapPart4Model s f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 f16 rest) := by
 have hz : ({val := 0} : W) = N 0 := rfl
 have hzn : ({val := 0} : W).toNat = 0 := rfl
 have capacity (j : Nat) (hj : j ≤ 63) : rest.length+j < 1024 := by omega
 have ha64 : (64 : W).toNat = 64 := rfl
 have hf64 := Monpro.activeWords_fix s 64 32 (by decide) (by norm_num) hact
 have ha120 : (120 : W).toNat = 120 := rfl
 have hf120 := Monpro.activeWords_fix s 120 32 (by decide) (by norm_num) hact
 simp [packOverlapPart4Program,packOverlapPart4Model,hz,hzn,runInstructions,runInstr,List.exchange,succ_ofNat_mod,ofNat_add_mod,Nat.add_assoc,State.activeWordsAfterUInt256,literal_eq_ofNat,capacity,ha64,hf64,ha120,hf120]
def packOverlapPart5Program : List Instr := [.push 1 90,.op .MSTORE]
def packOverlapPart5Model (s : State) (f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 f16 : W) (rest : List W) : State :=
  let v0 : ByteArray := MachineState.writeBytes (s.memory) (Data.Bytes.natToBytesPadded f0.toNat 32) 90
  {s with pc := N 8569,memory := v0,stack := f1::f2::f3::f4::f5::f6::f7::f8::f9::f10::f11::f12::f13::f14::f15::f16::rest}
theorem packOverlapPart5_run (s : State) (f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 f16 : W) (rest : List W) (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
 runInstructions packOverlapPart5Program {s with pc := N 8566,memory := s.memory,stack := f0::f1::f2::f3::f4::f5::f6::f7::f8::f9::f10::f11::f12::f13::f14::f15::f16::rest} = some (packOverlapPart5Model s f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 f16 rest) := by
 have hz : ({val := 0} : W) = N 0 := rfl
 have hzn : ({val := 0} : W).toNat = 0 := rfl
 have capacity (j : Nat) (hj : j ≤ 63) : rest.length+j < 1024 := by omega
 have ha90 : (90 : W).toNat = 90 := rfl
 have hf90 := Monpro.activeWords_fix s 90 32 (by decide) (by norm_num) hact
 simp [packOverlapPart5Program,packOverlapPart5Model,hz,hzn,runInstructions,runInstr,List.exchange,succ_ofNat_mod,ofNat_add_mod,Nat.add_assoc,State.activeWordsAfterUInt256,literal_eq_ofNat,capacity,ha90,hf90]
def packOverlapPart6Program : List Instr := [.push 1 60,.op .MSTORE]
def packOverlapPart6Model (s : State) (f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 : W) (rest : List W) : State :=
  let v0 : ByteArray := MachineState.writeBytes (s.memory) (Data.Bytes.natToBytesPadded f0.toNat 32) 60
  {s with pc := N 8572,memory := v0,stack := f1::f2::f3::f4::f5::f6::f7::f8::f9::f10::f11::f12::f13::f14::f15::rest}
theorem packOverlapPart6_run (s : State) (f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 : W) (rest : List W) (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
 runInstructions packOverlapPart6Program {s with pc := N 8569,memory := s.memory,stack := f0::f1::f2::f3::f4::f5::f6::f7::f8::f9::f10::f11::f12::f13::f14::f15::rest} = some (packOverlapPart6Model s f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 rest) := by
 have hz : ({val := 0} : W) = N 0 := rfl
 have hzn : ({val := 0} : W).toNat = 0 := rfl
 have capacity (j : Nat) (hj : j ≤ 63) : rest.length+j < 1024 := by omega
 have ha60 : (60 : W).toNat = 60 := rfl
 have hf60 := Monpro.activeWords_fix s 60 32 (by decide) (by norm_num) hact
 simp [packOverlapPart6Program,packOverlapPart6Model,hz,hzn,runInstructions,runInstr,List.exchange,succ_ofNat_mod,ofNat_add_mod,Nat.add_assoc,State.activeWordsAfterUInt256,literal_eq_ofNat,capacity,ha60,hf60]
def packOverlapPart7Program : List Instr := [.push 1 30,.op .MSTORE]
def packOverlapPart7Model (s : State) (f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 : W) (rest : List W) : State :=
  let v0 : ByteArray := MachineState.writeBytes (s.memory) (Data.Bytes.natToBytesPadded f0.toNat 32) 30
  {s with pc := N 8575,memory := v0,stack := f1::f2::f3::f4::f5::f6::f7::f8::f9::f10::f11::f12::f13::f14::rest}
theorem packOverlapPart7_run (s : State) (f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 : W) (rest : List W) (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
 runInstructions packOverlapPart7Program {s with pc := N 8572,memory := s.memory,stack := f0::f1::f2::f3::f4::f5::f6::f7::f8::f9::f10::f11::f12::f13::f14::rest} = some (packOverlapPart7Model s f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 rest) := by
 have hz : ({val := 0} : W) = N 0 := rfl
 have hzn : ({val := 0} : W).toNat = 0 := rfl
 have capacity (j : Nat) (hj : j ≤ 63) : rest.length+j < 1024 := by omega
 have ha30 : (30 : W).toNat = 30 := rfl
 have hf30 := Monpro.activeWords_fix s 30 32 (by decide) (by norm_num) hact
 simp [packOverlapPart7Program,packOverlapPart7Model,hz,hzn,runInstructions,runInstr,List.exchange,succ_ofNat_mod,ofNat_add_mod,Nat.add_assoc,State.activeWordsAfterUInt256,literal_eq_ofNat,capacity,ha30,hf30]
def packOverlapPart8Program : List Instr := [.op (.Dup dA13),.push 0 0,.op .MSTORE]
def packOverlapPart8Model (s : State) (f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 : W) (rest : List W) : State :=
  let v0 : ByteArray := MachineState.writeBytes (s.memory) (Data.Bytes.natToBytesPadded f13.toNat 32) 0
  {s with pc := N 8578,memory := v0,stack := f0::f1::f2::f3::f4::f5::f6::f7::f8::f9::f10::f11::f12::f13::rest}
theorem packOverlapPart8_run (s : State) (f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 : W) (rest : List W) (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
 runInstructions packOverlapPart8Program {s with pc := N 8575,memory := s.memory,stack := f0::f1::f2::f3::f4::f5::f6::f7::f8::f9::f10::f11::f12::f13::rest} = some (packOverlapPart8Model s f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 rest) := by
 have hz : ({val := 0} : W) = N 0 := rfl
 have hzn : ({val := 0} : W).toNat = 0 := rfl
 have capacity (j : Nat) (hj : j ≤ 63) : rest.length+j < 1024 := by omega
 have ha0 : (0 : W).toNat = 0 := rfl
 have hf0 := Monpro.activeWords_fix s 0 32 (by decide) (by norm_num) hact
 simp [packOverlapPart8Program,packOverlapPart8Model,hz,hzn,runInstructions,runInstr,List.exchange,succ_ofNat_mod,ofNat_add_mod,Nat.add_assoc,State.activeWordsAfterUInt256,literal_eq_ofNat,capacity,ha0,hf0]
def packFinalProgram : List Instr := (packOverlapPart0Program++(packOverlapPart1Program++(packOverlapPart2Program++(packOverlapPart3Program++(packOverlapPart4Program++(packOverlapPart5Program++(packOverlapPart6Program++(packOverlapPart7Program++packOverlapPart8Program))))))))
def packFinalModel (s : State) (f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 : W) (rest : List W) : State :=
  let v0 : W := MachineState.readWord (s.memory) 160
  let v1 : W := MachineState.readWord (s.memory) 128
  let v2 : W := MachineState.readWord (s.memory) 96
  let v3 : W := MachineState.readWord (s.memory) 768
  let v4 : ByteArray := MachineState.writeBytes (s.memory) (Data.Bytes.natToBytesPadded v3.toNat 32) 240
  let v5 : ByteArray := MachineState.writeBytes v4 (Data.Bytes.natToBytesPadded f3.toNat 32) 210
  let v6 : ByteArray := MachineState.writeBytes v5 (Data.Bytes.natToBytesPadded f4.toNat 32) 180
  let v7 : W := MachineState.readWord v6 32
  let v8 : ByteArray := MachineState.writeBytes v6 (Data.Bytes.natToBytesPadded v7.toNat 32) 150
  let v9 : W := MachineState.readWord v8 64
  let v10 : ByteArray := MachineState.writeBytes v8 (Data.Bytes.natToBytesPadded v9.toNat 32) 120
  let v11 : ByteArray := MachineState.writeBytes v10 (Data.Bytes.natToBytesPadded v2.toNat 32) 90
  let v12 : ByteArray := MachineState.writeBytes v11 (Data.Bytes.natToBytesPadded v1.toNat 32) 60
  let v13 : ByteArray := MachineState.writeBytes v12 (Data.Bytes.natToBytesPadded v0.toNat 32) 30
  let v14 : ByteArray := MachineState.writeBytes v13 (Data.Bytes.natToBytesPadded f13.toNat 32) 0
  {s with pc := N 8578,memory := v14,stack := f0::f1::f2::f3::f4::f5::f6::f7::f8::f9::f10::f11::f12::f13::rest}
theorem packFinal_run (s : State) (f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 : W) (rest : List W) (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
 runInstructions packFinalProgram {s with pc := N 8529,memory := s.memory,stack := f0::f1::f2::f3::f4::f5::f6::f7::f8::f9::f10::f11::f12::f13::rest} = some (packFinalModel s f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 rest) := by
  let v0 : W := MachineState.readWord (s.memory) 160
  let v1 : W := MachineState.readWord (s.memory) 128
  let v2 : W := MachineState.readWord (s.memory) 96
  let v3 : W := MachineState.readWord (s.memory) 768
  let v4 : ByteArray := MachineState.writeBytes (s.memory) (Data.Bytes.natToBytesPadded v3.toNat 32) 240
  let v5 : ByteArray := MachineState.writeBytes v4 (Data.Bytes.natToBytesPadded f3.toNat 32) 210
  let v6 : ByteArray := MachineState.writeBytes v5 (Data.Bytes.natToBytesPadded f4.toNat 32) 180
  let v7 : W := MachineState.readWord v6 32
  let v8 : ByteArray := MachineState.writeBytes v6 (Data.Bytes.natToBytesPadded v7.toNat 32) 150
  let v9 : W := MachineState.readWord v8 64
  let v10 : ByteArray := MachineState.writeBytes v8 (Data.Bytes.natToBytesPadded v9.toNat 32) 120
  let v11 : ByteArray := MachineState.writeBytes v10 (Data.Bytes.natToBytesPadded v2.toNat 32) 90
  let v12 : ByteArray := MachineState.writeBytes v11 (Data.Bytes.natToBytesPadded v1.toNat 32) 60
  let v13 : ByteArray := MachineState.writeBytes v12 (Data.Bytes.natToBytesPadded v0.toNat 32) 30
  let v14 : ByteArray := MachineState.writeBytes v13 (Data.Bytes.natToBytesPadded f13.toNat 32) 0
  have h0 : runInstructions packOverlapPart0Program {s with pc := N 8529,memory := s.memory,stack := f0::f1::f2::f3::f4::f5::f6::f7::f8::f9::f10::f11::f12::f13::rest} = some {s with pc := N 8546,memory := v4,stack := v2::v1::v0::f0::f1::f2::f3::f4::f5::f6::f7::f8::f9::f10::f11::f12::f13::rest} := by
    simpa only [packOverlapPart0Model,v0,v1,v2,v3,v4] using packOverlapPart0_run ({s with memory := s.memory}) f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 rest hcap hact
  have h1 : runInstructions packOverlapPart1Program {s with pc := N 8546,memory := v4,stack := v2::v1::v0::f0::f1::f2::f3::f4::f5::f6::f7::f8::f9::f10::f11::f12::f13::rest} = some {s with pc := N 8550,memory := v5,stack := v2::v1::v0::f0::f1::f2::f3::f4::f5::f6::f7::f8::f9::f10::f11::f12::f13::rest} := by
    simpa only [packOverlapPart1Model,v5] using packOverlapPart1_run ({s with memory := v4}) v2 v1 v0 f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 rest hcap hact
  have h2 : runInstructions packOverlapPart2Program {s with pc := N 8550,memory := v5,stack := v2::v1::v0::f0::f1::f2::f3::f4::f5::f6::f7::f8::f9::f10::f11::f12::f13::rest} = some {s with pc := N 8554,memory := v6,stack := v2::v1::v0::f0::f1::f2::f3::f4::f5::f6::f7::f8::f9::f10::f11::f12::f13::rest} := by
    simpa only [packOverlapPart2Model,v6] using packOverlapPart2_run ({s with memory := v5}) v2 v1 v0 f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 rest hcap hact
  have h3 : runInstructions packOverlapPart3Program {s with pc := N 8554,memory := v6,stack := v2::v1::v0::f0::f1::f2::f3::f4::f5::f6::f7::f8::f9::f10::f11::f12::f13::rest} = some {s with pc := N 8560,memory := v8,stack := v2::v1::v0::f0::f1::f2::f3::f4::f5::f6::f7::f8::f9::f10::f11::f12::f13::rest} := by
    simpa only [packOverlapPart3Model,v7,v8] using packOverlapPart3_run ({s with memory := v6}) v2 v1 v0 f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 rest hcap hact
  have h4 : runInstructions packOverlapPart4Program {s with pc := N 8560,memory := v8,stack := v2::v1::v0::f0::f1::f2::f3::f4::f5::f6::f7::f8::f9::f10::f11::f12::f13::rest} = some {s with pc := N 8566,memory := v10,stack := v2::v1::v0::f0::f1::f2::f3::f4::f5::f6::f7::f8::f9::f10::f11::f12::f13::rest} := by
    simpa only [packOverlapPart4Model,v9,v10] using packOverlapPart4_run ({s with memory := v8}) v2 v1 v0 f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 rest hcap hact
  have h5 : runInstructions packOverlapPart5Program {s with pc := N 8566,memory := v10,stack := v2::v1::v0::f0::f1::f2::f3::f4::f5::f6::f7::f8::f9::f10::f11::f12::f13::rest} = some {s with pc := N 8569,memory := v11,stack := v1::v0::f0::f1::f2::f3::f4::f5::f6::f7::f8::f9::f10::f11::f12::f13::rest} := by
    simpa only [packOverlapPart5Model,v11] using packOverlapPart5_run ({s with memory := v10}) v2 v1 v0 f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 rest hcap hact
  have h6 : runInstructions packOverlapPart6Program {s with pc := N 8569,memory := v11,stack := v1::v0::f0::f1::f2::f3::f4::f5::f6::f7::f8::f9::f10::f11::f12::f13::rest} = some {s with pc := N 8572,memory := v12,stack := v0::f0::f1::f2::f3::f4::f5::f6::f7::f8::f9::f10::f11::f12::f13::rest} := by
    simpa only [packOverlapPart6Model,v12] using packOverlapPart6_run ({s with memory := v11}) v1 v0 f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 rest hcap hact
  have h7 : runInstructions packOverlapPart7Program {s with pc := N 8572,memory := v12,stack := v0::f0::f1::f2::f3::f4::f5::f6::f7::f8::f9::f10::f11::f12::f13::rest} = some {s with pc := N 8575,memory := v13,stack := f0::f1::f2::f3::f4::f5::f6::f7::f8::f9::f10::f11::f12::f13::rest} := by
    simpa only [packOverlapPart7Model,v13] using packOverlapPart7_run ({s with memory := v12}) v0 f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 rest hcap hact
  have h8 : runInstructions packOverlapPart8Program {s with pc := N 8575,memory := v13,stack := f0::f1::f2::f3::f4::f5::f6::f7::f8::f9::f10::f11::f12::f13::rest} = some {s with pc := N 8578,memory := v14,stack := f0::f1::f2::f3::f4::f5::f6::f7::f8::f9::f10::f11::f12::f13::rest} := by
    simpa only [packOverlapPart8Model,v14] using packOverlapPart8_run ({s with memory := v13}) f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 rest hcap hact
  exact (runInstructions_append_some _ _ _ _ _ h0 (runInstructions_append_some _ _ _ _ _ h1 (runInstructions_append_some _ _ _ _ _ h2 (runInstructions_append_some _ _ _ _ _ h3 (runInstructions_append_some _ _ _ _ _ h4 (runInstructions_append_some _ _ _ _ _ h5 (runInstructions_append_some _ _ _ _ _ h6 (runInstructions_append_some _ _ _ _ _ h7 h8))))))))
#print axioms packFinal_run
end CycleSubmission.Execution
