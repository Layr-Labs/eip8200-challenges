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
def packOverlapPart0Program : List Instr := [.op .JUMPDEST,.push 2 768,.op .MLOAD,.push 2 2336,.op .MSTORE]
def packOverlapPart0Model (s : State) (f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 : W) (rest : List W) : State :=
  let v0 : W := MachineState.readWord (s.memory) 768
  let v1 : ByteArray := MachineState.writeBytes (s.memory) (Data.Bytes.natToBytesPadded v0.toNat 32) 2336
  {s with pc := N 8510,memory := v1,stack := f0::f1::f2::f3::f4::f5::f6::f7::f8::f9::f10::f11::f12::f13::rest}
theorem packOverlapPart0_run (s : State) (f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 : W) (rest : List W) (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
 runInstructions packOverlapPart0Program {s with pc := N 8501,memory := s.memory,stack := f0::f1::f2::f3::f4::f5::f6::f7::f8::f9::f10::f11::f12::f13::rest} = some (packOverlapPart0Model s f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 rest) := by
 have hz : ({val := 0} : W) = N 0 := rfl
 have hzn : ({val := 0} : W).toNat = 0 := rfl
 have capacity (j : Nat) (hj : j ≤ 63) : rest.length+j < 1024 := by omega
 have ha768 : (768 : W).toNat = 768 := rfl
 have hf768 := Monpro.activeWords_fix s 768 32 (by decide) (by norm_num) hact
 have ha2336 : (2336 : W).toNat = 2336 := rfl
 have hf2336 := Monpro.activeWords_fix s 2336 32 (by decide) (by norm_num) hact
 simp [packOverlapPart0Program,packOverlapPart0Model,hz,hzn,runInstructions,runInstr,List.exchange,succ_ofNat_mod,ofNat_add_mod,Nat.add_assoc,State.activeWordsAfterUInt256,literal_eq_ofNat,capacity,ha768,hf768,ha2336,hf2336]
def packOverlapPart1Program : List Instr := [.op (.Dup dA3),.push 2 2306,.op .MSTORE]
def packOverlapPart1Model (s : State) (f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 : W) (rest : List W) : State :=
  let v0 : ByteArray := MachineState.writeBytes (s.memory) (Data.Bytes.natToBytesPadded f3.toNat 32) 2306
  {s with pc := N 8515,memory := v0,stack := f0::f1::f2::f3::f4::f5::f6::f7::f8::f9::f10::f11::f12::f13::rest}
theorem packOverlapPart1_run (s : State) (f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 : W) (rest : List W) (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
 runInstructions packOverlapPart1Program {s with pc := N 8510,memory := s.memory,stack := f0::f1::f2::f3::f4::f5::f6::f7::f8::f9::f10::f11::f12::f13::rest} = some (packOverlapPart1Model s f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 rest) := by
 have hz : ({val := 0} : W) = N 0 := rfl
 have hzn : ({val := 0} : W).toNat = 0 := rfl
 have capacity (j : Nat) (hj : j ≤ 63) : rest.length+j < 1024 := by omega
 have ha2306 : (2306 : W).toNat = 2306 := rfl
 have hf2306 := Monpro.activeWords_fix s 2306 32 (by decide) (by norm_num) hact
 simp [packOverlapPart1Program,packOverlapPart1Model,hz,hzn,runInstructions,runInstr,List.exchange,succ_ofNat_mod,ofNat_add_mod,Nat.add_assoc,State.activeWordsAfterUInt256,literal_eq_ofNat,capacity,ha2306,hf2306]
def packOverlapPart2Program : List Instr := [.op (.Dup dA4),.push 2 2276,.op .MSTORE]
def packOverlapPart2Model (s : State) (f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 : W) (rest : List W) : State :=
  let v0 : ByteArray := MachineState.writeBytes (s.memory) (Data.Bytes.natToBytesPadded f4.toNat 32) 2276
  {s with pc := N 8520,memory := v0,stack := f0::f1::f2::f3::f4::f5::f6::f7::f8::f9::f10::f11::f12::f13::rest}
theorem packOverlapPart2_run (s : State) (f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 : W) (rest : List W) (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
 runInstructions packOverlapPart2Program {s with pc := N 8515,memory := s.memory,stack := f0::f1::f2::f3::f4::f5::f6::f7::f8::f9::f10::f11::f12::f13::rest} = some (packOverlapPart2Model s f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 rest) := by
 have hz : ({val := 0} : W) = N 0 := rfl
 have hzn : ({val := 0} : W).toNat = 0 := rfl
 have capacity (j : Nat) (hj : j ≤ 63) : rest.length+j < 1024 := by omega
 have ha2276 : (2276 : W).toNat = 2276 := rfl
 have hf2276 := Monpro.activeWords_fix s 2276 32 (by decide) (by norm_num) hact
 simp [packOverlapPart2Program,packOverlapPart2Model,hz,hzn,runInstructions,runInstr,List.exchange,succ_ofNat_mod,ofNat_add_mod,Nat.add_assoc,State.activeWordsAfterUInt256,literal_eq_ofNat,capacity,ha2276,hf2276]
def packOverlapPart3Program : List Instr := [.push 1 32,.op .MLOAD,.push 2 2246,.op .MSTORE]
def packOverlapPart3Model (s : State) (f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 : W) (rest : List W) : State :=
  let v0 : W := MachineState.readWord (s.memory) 32
  let v1 : ByteArray := MachineState.writeBytes (s.memory) (Data.Bytes.natToBytesPadded v0.toNat 32) 2246
  {s with pc := N 8527,memory := v1,stack := f0::f1::f2::f3::f4::f5::f6::f7::f8::f9::f10::f11::f12::f13::rest}
theorem packOverlapPart3_run (s : State) (f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 : W) (rest : List W) (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
 runInstructions packOverlapPart3Program {s with pc := N 8520,memory := s.memory,stack := f0::f1::f2::f3::f4::f5::f6::f7::f8::f9::f10::f11::f12::f13::rest} = some (packOverlapPart3Model s f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 rest) := by
 have hz : ({val := 0} : W) = N 0 := rfl
 have hzn : ({val := 0} : W).toNat = 0 := rfl
 have capacity (j : Nat) (hj : j ≤ 63) : rest.length+j < 1024 := by omega
 have ha32 : (32 : W).toNat = 32 := rfl
 have hf32 := Monpro.activeWords_fix s 32 32 (by decide) (by norm_num) hact
 have ha2246 : (2246 : W).toNat = 2246 := rfl
 have hf2246 := Monpro.activeWords_fix s 2246 32 (by decide) (by norm_num) hact
 simp [packOverlapPart3Program,packOverlapPart3Model,hz,hzn,runInstructions,runInstr,List.exchange,succ_ofNat_mod,ofNat_add_mod,Nat.add_assoc,State.activeWordsAfterUInt256,literal_eq_ofNat,capacity,ha32,hf32,ha2246,hf2246]
def packOverlapPart4Program : List Instr := [.push 1 64,.op .MLOAD,.push 2 2216,.op .MSTORE]
def packOverlapPart4Model (s : State) (f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 : W) (rest : List W) : State :=
  let v0 : W := MachineState.readWord (s.memory) 64
  let v1 : ByteArray := MachineState.writeBytes (s.memory) (Data.Bytes.natToBytesPadded v0.toNat 32) 2216
  {s with pc := N 8534,memory := v1,stack := f0::f1::f2::f3::f4::f5::f6::f7::f8::f9::f10::f11::f12::f13::rest}
theorem packOverlapPart4_run (s : State) (f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 : W) (rest : List W) (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
 runInstructions packOverlapPart4Program {s with pc := N 8527,memory := s.memory,stack := f0::f1::f2::f3::f4::f5::f6::f7::f8::f9::f10::f11::f12::f13::rest} = some (packOverlapPart4Model s f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 rest) := by
 have hz : ({val := 0} : W) = N 0 := rfl
 have hzn : ({val := 0} : W).toNat = 0 := rfl
 have capacity (j : Nat) (hj : j ≤ 63) : rest.length+j < 1024 := by omega
 have ha64 : (64 : W).toNat = 64 := rfl
 have hf64 := Monpro.activeWords_fix s 64 32 (by decide) (by norm_num) hact
 have ha2216 : (2216 : W).toNat = 2216 := rfl
 have hf2216 := Monpro.activeWords_fix s 2216 32 (by decide) (by norm_num) hact
 simp [packOverlapPart4Program,packOverlapPart4Model,hz,hzn,runInstructions,runInstr,List.exchange,succ_ofNat_mod,ofNat_add_mod,Nat.add_assoc,State.activeWordsAfterUInt256,literal_eq_ofNat,capacity,ha64,hf64,ha2216,hf2216]
def packOverlapPart5Program : List Instr := [.push 1 96,.op .MLOAD,.push 2 2186,.op .MSTORE]
def packOverlapPart5Model (s : State) (f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 : W) (rest : List W) : State :=
  let v0 : W := MachineState.readWord (s.memory) 96
  let v1 : ByteArray := MachineState.writeBytes (s.memory) (Data.Bytes.natToBytesPadded v0.toNat 32) 2186
  {s with pc := N 8541,memory := v1,stack := f0::f1::f2::f3::f4::f5::f6::f7::f8::f9::f10::f11::f12::f13::rest}
theorem packOverlapPart5_run (s : State) (f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 : W) (rest : List W) (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
 runInstructions packOverlapPart5Program {s with pc := N 8534,memory := s.memory,stack := f0::f1::f2::f3::f4::f5::f6::f7::f8::f9::f10::f11::f12::f13::rest} = some (packOverlapPart5Model s f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 rest) := by
 have hz : ({val := 0} : W) = N 0 := rfl
 have hzn : ({val := 0} : W).toNat = 0 := rfl
 have capacity (j : Nat) (hj : j ≤ 63) : rest.length+j < 1024 := by omega
 have ha96 : (96 : W).toNat = 96 := rfl
 have hf96 := Monpro.activeWords_fix s 96 32 (by decide) (by norm_num) hact
 have ha2186 : (2186 : W).toNat = 2186 := rfl
 have hf2186 := Monpro.activeWords_fix s 2186 32 (by decide) (by norm_num) hact
 simp [packOverlapPart5Program,packOverlapPart5Model,hz,hzn,runInstructions,runInstr,List.exchange,succ_ofNat_mod,ofNat_add_mod,Nat.add_assoc,State.activeWordsAfterUInt256,literal_eq_ofNat,capacity,ha96,hf96,ha2186,hf2186]
def packOverlapPart6Program : List Instr := [.push 1 128,.op .MLOAD,.push 2 2156,.op .MSTORE]
def packOverlapPart6Model (s : State) (f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 : W) (rest : List W) : State :=
  let v0 : W := MachineState.readWord (s.memory) 128
  let v1 : ByteArray := MachineState.writeBytes (s.memory) (Data.Bytes.natToBytesPadded v0.toNat 32) 2156
  {s with pc := N 8548,memory := v1,stack := f0::f1::f2::f3::f4::f5::f6::f7::f8::f9::f10::f11::f12::f13::rest}
theorem packOverlapPart6_run (s : State) (f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 : W) (rest : List W) (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
 runInstructions packOverlapPart6Program {s with pc := N 8541,memory := s.memory,stack := f0::f1::f2::f3::f4::f5::f6::f7::f8::f9::f10::f11::f12::f13::rest} = some (packOverlapPart6Model s f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 rest) := by
 have hz : ({val := 0} : W) = N 0 := rfl
 have hzn : ({val := 0} : W).toNat = 0 := rfl
 have capacity (j : Nat) (hj : j ≤ 63) : rest.length+j < 1024 := by omega
 have ha128 : (128 : W).toNat = 128 := rfl
 have hf128 := Monpro.activeWords_fix s 128 32 (by decide) (by norm_num) hact
 have ha2156 : (2156 : W).toNat = 2156 := rfl
 have hf2156 := Monpro.activeWords_fix s 2156 32 (by decide) (by norm_num) hact
 simp [packOverlapPart6Program,packOverlapPart6Model,hz,hzn,runInstructions,runInstr,List.exchange,succ_ofNat_mod,ofNat_add_mod,Nat.add_assoc,State.activeWordsAfterUInt256,literal_eq_ofNat,capacity,ha128,hf128,ha2156,hf2156]
def packOverlapPart7Program : List Instr := [.push 1 160,.op .MLOAD,.push 2 2126,.op .MSTORE]
def packOverlapPart7Model (s : State) (f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 : W) (rest : List W) : State :=
  let v0 : W := MachineState.readWord (s.memory) 160
  let v1 : ByteArray := MachineState.writeBytes (s.memory) (Data.Bytes.natToBytesPadded v0.toNat 32) 2126
  {s with pc := N 8555,memory := v1,stack := f0::f1::f2::f3::f4::f5::f6::f7::f8::f9::f10::f11::f12::f13::rest}
theorem packOverlapPart7_run (s : State) (f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 : W) (rest : List W) (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
 runInstructions packOverlapPart7Program {s with pc := N 8548,memory := s.memory,stack := f0::f1::f2::f3::f4::f5::f6::f7::f8::f9::f10::f11::f12::f13::rest} = some (packOverlapPart7Model s f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 rest) := by
 have hz : ({val := 0} : W) = N 0 := rfl
 have hzn : ({val := 0} : W).toNat = 0 := rfl
 have capacity (j : Nat) (hj : j ≤ 63) : rest.length+j < 1024 := by omega
 have ha160 : (160 : W).toNat = 160 := rfl
 have hf160 := Monpro.activeWords_fix s 160 32 (by decide) (by norm_num) hact
 have ha2126 : (2126 : W).toNat = 2126 := rfl
 have hf2126 := Monpro.activeWords_fix s 2126 32 (by decide) (by norm_num) hact
 simp [packOverlapPart7Program,packOverlapPart7Model,hz,hzn,runInstructions,runInstr,List.exchange,succ_ofNat_mod,ofNat_add_mod,Nat.add_assoc,State.activeWordsAfterUInt256,literal_eq_ofNat,capacity,ha160,hf160,ha2126,hf2126]
def packOverlapPart8Program : List Instr := [.op (.Dup dA13),.push 2 2096,.op .MSTORE]
def packOverlapPart8Model (s : State) (f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 : W) (rest : List W) : State :=
  let v0 : ByteArray := MachineState.writeBytes (s.memory) (Data.Bytes.natToBytesPadded f13.toNat 32) 2096
  {s with pc := N 8560,memory := v0,stack := f0::f1::f2::f3::f4::f5::f6::f7::f8::f9::f10::f11::f12::f13::rest}
theorem packOverlapPart8_run (s : State) (f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 : W) (rest : List W) (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
 runInstructions packOverlapPart8Program {s with pc := N 8555,memory := s.memory,stack := f0::f1::f2::f3::f4::f5::f6::f7::f8::f9::f10::f11::f12::f13::rest} = some (packOverlapPart8Model s f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 rest) := by
 have hz : ({val := 0} : W) = N 0 := rfl
 have hzn : ({val := 0} : W).toNat = 0 := rfl
 have capacity (j : Nat) (hj : j ≤ 63) : rest.length+j < 1024 := by omega
 have ha2096 : (2096 : W).toNat = 2096 := rfl
 have hf2096 := Monpro.activeWords_fix s 2096 32 (by decide) (by norm_num) hact
 simp [packOverlapPart8Program,packOverlapPart8Model,hz,hzn,runInstructions,runInstr,List.exchange,succ_ofNat_mod,ofNat_add_mod,Nat.add_assoc,State.activeWordsAfterUInt256,literal_eq_ofNat,capacity,ha2096,hf2096]
def packFinalProgram : List Instr := (packOverlapPart0Program++(packOverlapPart1Program++(packOverlapPart2Program++(packOverlapPart3Program++(packOverlapPart4Program++(packOverlapPart5Program++(packOverlapPart6Program++(packOverlapPart7Program++packOverlapPart8Program))))))))
def packFinalModel (s : State) (f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 : W) (rest : List W) : State :=
  let v0 : W := MachineState.readWord (s.memory) 768
  let v1 : ByteArray := MachineState.writeBytes (s.memory) (Data.Bytes.natToBytesPadded v0.toNat 32) 2336
  let v2 : ByteArray := MachineState.writeBytes v1 (Data.Bytes.natToBytesPadded f3.toNat 32) 2306
  let v3 : ByteArray := MachineState.writeBytes v2 (Data.Bytes.natToBytesPadded f4.toNat 32) 2276
  let v4 : W := MachineState.readWord v3 32
  let v5 : ByteArray := MachineState.writeBytes v3 (Data.Bytes.natToBytesPadded v4.toNat 32) 2246
  let v6 : W := MachineState.readWord v5 64
  let v7 : ByteArray := MachineState.writeBytes v5 (Data.Bytes.natToBytesPadded v6.toNat 32) 2216
  let v8 : W := MachineState.readWord v7 96
  let v9 : ByteArray := MachineState.writeBytes v7 (Data.Bytes.natToBytesPadded v8.toNat 32) 2186
  let v10 : W := MachineState.readWord v9 128
  let v11 : ByteArray := MachineState.writeBytes v9 (Data.Bytes.natToBytesPadded v10.toNat 32) 2156
  let v12 : W := MachineState.readWord v11 160
  let v13 : ByteArray := MachineState.writeBytes v11 (Data.Bytes.natToBytesPadded v12.toNat 32) 2126
  let v14 : ByteArray := MachineState.writeBytes v13 (Data.Bytes.natToBytesPadded f13.toNat 32) 2096
  {s with pc := N 8560,memory := v14,stack := f0::f1::f2::f3::f4::f5::f6::f7::f8::f9::f10::f11::f12::f13::rest}
theorem packFinal_run (s : State) (f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 : W) (rest : List W) (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
 runInstructions packFinalProgram {s with pc := N 8501,memory := s.memory,stack := f0::f1::f2::f3::f4::f5::f6::f7::f8::f9::f10::f11::f12::f13::rest} = some (packFinalModel s f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 rest) := by
  let v0 : W := MachineState.readWord (s.memory) 768
  let v1 : ByteArray := MachineState.writeBytes (s.memory) (Data.Bytes.natToBytesPadded v0.toNat 32) 2336
  let v2 : ByteArray := MachineState.writeBytes v1 (Data.Bytes.natToBytesPadded f3.toNat 32) 2306
  let v3 : ByteArray := MachineState.writeBytes v2 (Data.Bytes.natToBytesPadded f4.toNat 32) 2276
  let v4 : W := MachineState.readWord v3 32
  let v5 : ByteArray := MachineState.writeBytes v3 (Data.Bytes.natToBytesPadded v4.toNat 32) 2246
  let v6 : W := MachineState.readWord v5 64
  let v7 : ByteArray := MachineState.writeBytes v5 (Data.Bytes.natToBytesPadded v6.toNat 32) 2216
  let v8 : W := MachineState.readWord v7 96
  let v9 : ByteArray := MachineState.writeBytes v7 (Data.Bytes.natToBytesPadded v8.toNat 32) 2186
  let v10 : W := MachineState.readWord v9 128
  let v11 : ByteArray := MachineState.writeBytes v9 (Data.Bytes.natToBytesPadded v10.toNat 32) 2156
  let v12 : W := MachineState.readWord v11 160
  let v13 : ByteArray := MachineState.writeBytes v11 (Data.Bytes.natToBytesPadded v12.toNat 32) 2126
  let v14 : ByteArray := MachineState.writeBytes v13 (Data.Bytes.natToBytesPadded f13.toNat 32) 2096
  have h0 : runInstructions packOverlapPart0Program {s with pc := N 8501,memory := s.memory,stack := f0::f1::f2::f3::f4::f5::f6::f7::f8::f9::f10::f11::f12::f13::rest} = some {s with pc := N 8510,memory := v1,stack := f0::f1::f2::f3::f4::f5::f6::f7::f8::f9::f10::f11::f12::f13::rest} := by
    simpa only [packOverlapPart0Model,v0,v1] using packOverlapPart0_run ({s with memory := s.memory}) f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 rest hcap hact
  have h1 : runInstructions packOverlapPart1Program {s with pc := N 8510,memory := v1,stack := f0::f1::f2::f3::f4::f5::f6::f7::f8::f9::f10::f11::f12::f13::rest} = some {s with pc := N 8515,memory := v2,stack := f0::f1::f2::f3::f4::f5::f6::f7::f8::f9::f10::f11::f12::f13::rest} := by
    simpa only [packOverlapPart1Model,v2] using packOverlapPart1_run ({s with memory := v1}) f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 rest hcap hact
  have h2 : runInstructions packOverlapPart2Program {s with pc := N 8515,memory := v2,stack := f0::f1::f2::f3::f4::f5::f6::f7::f8::f9::f10::f11::f12::f13::rest} = some {s with pc := N 8520,memory := v3,stack := f0::f1::f2::f3::f4::f5::f6::f7::f8::f9::f10::f11::f12::f13::rest} := by
    simpa only [packOverlapPart2Model,v3] using packOverlapPart2_run ({s with memory := v2}) f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 rest hcap hact
  have h3 : runInstructions packOverlapPart3Program {s with pc := N 8520,memory := v3,stack := f0::f1::f2::f3::f4::f5::f6::f7::f8::f9::f10::f11::f12::f13::rest} = some {s with pc := N 8527,memory := v5,stack := f0::f1::f2::f3::f4::f5::f6::f7::f8::f9::f10::f11::f12::f13::rest} := by
    simpa only [packOverlapPart3Model,v4,v5] using packOverlapPart3_run ({s with memory := v3}) f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 rest hcap hact
  have h4 : runInstructions packOverlapPart4Program {s with pc := N 8527,memory := v5,stack := f0::f1::f2::f3::f4::f5::f6::f7::f8::f9::f10::f11::f12::f13::rest} = some {s with pc := N 8534,memory := v7,stack := f0::f1::f2::f3::f4::f5::f6::f7::f8::f9::f10::f11::f12::f13::rest} := by
    simpa only [packOverlapPart4Model,v6,v7] using packOverlapPart4_run ({s with memory := v5}) f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 rest hcap hact
  have h5 : runInstructions packOverlapPart5Program {s with pc := N 8534,memory := v7,stack := f0::f1::f2::f3::f4::f5::f6::f7::f8::f9::f10::f11::f12::f13::rest} = some {s with pc := N 8541,memory := v9,stack := f0::f1::f2::f3::f4::f5::f6::f7::f8::f9::f10::f11::f12::f13::rest} := by
    simpa only [packOverlapPart5Model,v8,v9] using packOverlapPart5_run ({s with memory := v7}) f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 rest hcap hact
  have h6 : runInstructions packOverlapPart6Program {s with pc := N 8541,memory := v9,stack := f0::f1::f2::f3::f4::f5::f6::f7::f8::f9::f10::f11::f12::f13::rest} = some {s with pc := N 8548,memory := v11,stack := f0::f1::f2::f3::f4::f5::f6::f7::f8::f9::f10::f11::f12::f13::rest} := by
    simpa only [packOverlapPart6Model,v10,v11] using packOverlapPart6_run ({s with memory := v9}) f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 rest hcap hact
  have h7 : runInstructions packOverlapPart7Program {s with pc := N 8548,memory := v11,stack := f0::f1::f2::f3::f4::f5::f6::f7::f8::f9::f10::f11::f12::f13::rest} = some {s with pc := N 8555,memory := v13,stack := f0::f1::f2::f3::f4::f5::f6::f7::f8::f9::f10::f11::f12::f13::rest} := by
    simpa only [packOverlapPart7Model,v12,v13] using packOverlapPart7_run ({s with memory := v11}) f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 rest hcap hact
  have h8 : runInstructions packOverlapPart8Program {s with pc := N 8555,memory := v13,stack := f0::f1::f2::f3::f4::f5::f6::f7::f8::f9::f10::f11::f12::f13::rest} = some {s with pc := N 8560,memory := v14,stack := f0::f1::f2::f3::f4::f5::f6::f7::f8::f9::f10::f11::f12::f13::rest} := by
    simpa only [packOverlapPart8Model,v14] using packOverlapPart8_run ({s with memory := v13}) f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 rest hcap hact
  exact (runInstructions_append_some _ _ _ _ _ h0 (runInstructions_append_some _ _ _ _ _ h1 (runInstructions_append_some _ _ _ _ _ h2 (runInstructions_append_some _ _ _ _ _ h3 (runInstructions_append_some _ _ _ _ _ h4 (runInstructions_append_some _ _ _ _ _ h5 (runInstructions_append_some _ _ _ _ _ h6 (runInstructions_append_some _ _ _ _ _ h7 h8))))))))
#print axioms packFinal_run
end CycleSubmission.Execution
