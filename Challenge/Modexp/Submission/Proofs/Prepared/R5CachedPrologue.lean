import Challenge.Modexp.Submission.Proofs.Prepared.StackArgs
import Challenge.Modexp.Submission.Proofs.Fast.Monpro
import Challenge.Modexp.Submission.Proofs.Bytecode.WindowNibbleDefs
import Challenge.Modexp.Submission.Proofs.R5.ConstantFold
import Challenge.Modexp.Submission.Proofs.R5.PrologueMeaning
open CycleSubmission.SharedStackArgs
open EvmSemantics EvmSemantics.EVM YulEvmCompiler
open Challenge.EvmProof.Word Challenge.EvmProof.Stepper
open Challenge.Modexp.Submission.Proofs.Bytecode.WindowNibbleKernel
open Challenge.Modexp.Submission.Proofs.Fast
set_option maxRecDepth 40000
set_option maxHeartbeats 16000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
local notation "W" => UInt256
local notation "N" => UInt256.ofNat
namespace R5CachePrefixOld
def part0Program : List Instr := [.op .JUMPDEST,.op (.Dup dA14),.op (.Dup dA12),.push 1 16,.op .SHL,.op (.Dup dA0),.push 1 192,.op .MSTORE]
def part0Model (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 : W) (rest : List W) : State :=
  let v0 : W := UInt256.shiftLeft w11 (N 16)
  let v1 : ByteArray := MachineState.writeBytes (s.memory) (Data.Bytes.natToBytesPadded v0.toNat 32) 192
  {s with pc := N 8466,memory := v1,stack := v0::w14::w0::w1::w2::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::rest}
theorem part0_run (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions part0Program {s with pc := N 8456,memory := s.memory,stack := w0::w1::w2::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::rest} = some (part0Model s w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 63) : rest.length+j < 1024 := by omega
  have ha192 : (192 : W).toNat = 192 := rfl
  have hf192 := Monpro.activeWords_fix s 192 32 (by decide) (by norm_num) hact
  simp [hz,hzn,part0Program,part0Model,runInstructions,runInstr,List.exchange,succ_ofNat_mod,ofNat_add_mod,Nat.add_assoc,State.activeWordsAfterUInt256,literal_eq_ofNat,capacity,ha192,hf192]
def part1Program : List Instr := [.push 0 0,.op .NOT,.push 1 5,.op .SHR,.op (.Dup dA0),.push 1 11,.op .SHR,.push 1 224,.op .MSTORE]
def part1Model (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 : W) (rest : List W) : State :=
  let v0 : W := UInt256.lnot (N 0)
  let v1 : W := UInt256.shiftRight v0 (N 5)
  let v2 : W := UInt256.shiftRight v1 (N 11)
  let v3 : ByteArray := MachineState.writeBytes (s.memory) (Data.Bytes.natToBytesPadded v2.toNat 32) 224
  {s with pc := N 8478,memory := v3,stack := v1::w0::w1::w2::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::w16::w17::rest}
theorem part1_run (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions part1Program {s with pc := N 8466,memory := s.memory,stack := w0::w1::w2::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::w16::w17::rest} = some (part1Model s w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 63) : rest.length+j < 1024 := by omega
  have ha224 : (224 : W).toNat = 224 := rfl
  have hf224 := Monpro.activeWords_fix s 224 32 (by decide) (by norm_num) hact
  simp [hz,hzn,part1Program,part1Model,runInstructions,runInstr,List.exchange,succ_ofNat_mod,ofNat_add_mod,Nat.add_assoc,State.activeWordsAfterUInt256,literal_eq_ofNat,capacity,ha224,hf224]
def part2Program : List Instr := [.push 0 0,.op .MLOAD,.push 1 192,.op .SHR,.push 1 224,.op .MLOAD,.op (.Dup dA0),.push 1 36,.op .MLOAD]
def part2Model (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 : W) (rest : List W) : State :=
  let v0 : W := MachineState.readWord (s.memory) 0
  let v1 : W := UInt256.shiftRight v0 (N 192)
  let v2 : W := MachineState.readWord (s.memory) 224
  let v3 : W := MachineState.readWord (s.memory) 36
  {s with pc := N 8490,memory := s.memory,stack := v3::v2::v2::v1::w0::w1::w2::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::w16::w17::w18::rest}
theorem part2_run (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions part2Program {s with pc := N 8478,memory := s.memory,stack := w0::w1::w2::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::w16::w17::w18::rest} = some (part2Model s w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 63) : rest.length+j < 1024 := by omega
  have ha0 : (0 : W).toNat = 0 := rfl
  have hf0 := Monpro.activeWords_fix s 0 32 (by decide) (by norm_num) hact
  have ha36 : (36 : W).toNat = 36 := rfl
  have hf36 := Monpro.activeWords_fix s 36 32 (by decide) (by norm_num) hact
  have ha224 : (224 : W).toNat = 224 := rfl
  have hf224 := Monpro.activeWords_fix s 224 32 (by decide) (by norm_num) hact
  simp [hz,hzn,part2Program,part2Model,runInstructions,runInstr,List.exchange,succ_ofNat_mod,ofNat_add_mod,Nat.add_assoc,State.activeWordsAfterUInt256,literal_eq_ofNat,capacity,ha0,hf0,ha36,hf36,ha224,hf224]
def part3Program : List Instr := [.op (.Dup dA2),.op .AND,.push 1 66,.op .MLOAD,.op (.Dup dA3),.op .AND,.push 1 96,.op .MLOAD]
def part3Model (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 w20 w21 w22 : W) (rest : List W) : State :=
  let v0 : W := UInt256.land w2 w0
  let v1 : W := MachineState.readWord (s.memory) 66
  let v2 : W := UInt256.land w2 v1
  let v3 : W := MachineState.readWord (s.memory) 96
  {s with pc := N 8500,memory := s.memory,stack := v3::v2::v0::w1::w2::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::w16::w17::w18::w19::w20::w21::w22::rest}
theorem part3_run (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 w20 w21 w22 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions part3Program {s with pc := N 8490,memory := s.memory,stack := w0::w1::w2::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::w16::w17::w18::w19::w20::w21::w22::rest} = some (part3Model s w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 w20 w21 w22 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 63) : rest.length+j < 1024 := by omega
  have ha66 : (66 : W).toNat = 66 := rfl
  have hf66 := Monpro.activeWords_fix s 66 32 (by decide) (by norm_num) hact
  have ha96 : (96 : W).toNat = 96 := rfl
  have hf96 := Monpro.activeWords_fix s 96 32 (by decide) (by norm_num) hact
  simp [hz,hzn,part3Program,part3Model,runInstructions,runInstr,List.exchange,succ_ofNat_mod,ofNat_add_mod,Nat.add_assoc,State.activeWordsAfterUInt256,literal_eq_ofNat,capacity,ha66,hf66,ha96,hf96]
def part4Program : List Instr := [.push 1 6,.op .MLOAD,.op (.Dup dA5),.op .AND,.op (.Swap sA4),.op .AND,.push 1 160,.op .MSTORE]
def part4Model (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 w20 w21 w22 w23 w24 : W) (rest : List W) : State :=
  let v0 : W := MachineState.readWord (s.memory) 6
  let v1 : W := UInt256.land w4 v0
  let v2 : W := UInt256.land w4 w0
  let v3 : ByteArray := MachineState.writeBytes (s.memory) (Data.Bytes.natToBytesPadded v2.toNat 32) 160
  {s with pc := N 8510,memory := v3,stack := w1::w2::w3::v1::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::w16::w17::w18::w19::w20::w21::w22::w23::w24::rest}
theorem part4_run (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 w20 w21 w22 w23 w24 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions part4Program {s with pc := N 8500,memory := s.memory,stack := w0::w1::w2::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::w16::w17::w18::w19::w20::w21::w22::w23::w24::rest} = some (part4Model s w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 w20 w21 w22 w23 w24 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 63) : rest.length+j < 1024 := by omega
  have ha6 : (6 : W).toNat = 6 := rfl
  have hf6 := Monpro.activeWords_fix s 6 32 (by decide) (by norm_num) hact
  have ha160 : (160 : W).toNat = 160 := rfl
  have hf160 := Monpro.activeWords_fix s 160 32 (by decide) (by norm_num) hact
  simp [hz,hzn,part4Program,part4Model,runInstructions,runInstr,List.exchange,succ_ofNat_mod,ofNat_add_mod,Nat.add_assoc,State.activeWordsAfterUInt256,literal_eq_ofNat,capacity,ha6,hf6,ha160,hf160]
def part5Program : List Instr := [.push 2 352,.op .MLOAD,.op (.Dup dA3),.op .AND,.push 0 0,.op .MSTORE,.push 2 322,.op .MLOAD]
def part5Model (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 w20 w21 w22 w23 : W) (rest : List W) : State :=
  let v0 : W := MachineState.readWord (s.memory) 352
  let v1 : W := UInt256.land w2 v0
  let v2 : ByteArray := MachineState.writeBytes (s.memory) (Data.Bytes.natToBytesPadded v1.toNat 32) 0
  let v3 : W := MachineState.readWord v2 322
  {s with pc := N 8522,memory := v2,stack := v3::w0::w1::w2::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::w16::w17::w18::w19::w20::w21::w22::w23::rest}
theorem part5_run (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 w20 w21 w22 w23 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions part5Program {s with pc := N 8510,memory := s.memory,stack := w0::w1::w2::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::w16::w17::w18::w19::w20::w21::w22::w23::rest} = some (part5Model s w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 w20 w21 w22 w23 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 63) : rest.length+j < 1024 := by omega
  have ha0 : (0 : W).toNat = 0 := rfl
  have hf0 := Monpro.activeWords_fix s 0 32 (by decide) (by norm_num) hact
  have ha322 : (322 : W).toNat = 322 := rfl
  have hf322 := Monpro.activeWords_fix s 322 32 (by decide) (by norm_num) hact
  have ha352 : (352 : W).toNat = 352 := rfl
  have hf352 := Monpro.activeWords_fix s 352 32 (by decide) (by norm_num) hact
  simp [hz,hzn,part5Program,part5Model,runInstructions,runInstr,List.exchange,succ_ofNat_mod,ofNat_add_mod,Nat.add_assoc,State.activeWordsAfterUInt256,literal_eq_ofNat,capacity,ha0,hf0,ha322,hf322,ha352,hf352]
def part6Program : List Instr := [.op (.Dup dA3),.op .AND,.push 1 32,.op .MSTORE,.push 2 292,.op .MLOAD,.op (.Dup dA3),.op .AND]
def part6Model (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 w20 w21 w22 w23 w24 : W) (rest : List W) : State :=
  let v0 : W := UInt256.land w3 w0
  let v1 : ByteArray := MachineState.writeBytes (s.memory) (Data.Bytes.natToBytesPadded v0.toNat 32) 32
  let v2 : W := MachineState.readWord v1 292
  let v3 : W := UInt256.land w3 v2
  {s with pc := N 8533,memory := v1,stack := v3::w1::w2::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::w16::w17::w18::w19::w20::w21::w22::w23::w24::rest}
theorem part6_run (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 w20 w21 w22 w23 w24 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions part6Program {s with pc := N 8522,memory := s.memory,stack := w0::w1::w2::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::w16::w17::w18::w19::w20::w21::w22::w23::w24::rest} = some (part6Model s w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 w20 w21 w22 w23 w24 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 63) : rest.length+j < 1024 := by omega
  have ha32 : (32 : W).toNat = 32 := rfl
  have hf32 := Monpro.activeWords_fix s 32 32 (by decide) (by norm_num) hact
  have ha292 : (292 : W).toNat = 292 := rfl
  have hf292 := Monpro.activeWords_fix s 292 32 (by decide) (by norm_num) hact
  simp [hz,hzn,part6Program,part6Model,runInstructions,runInstr,List.exchange,succ_ofNat_mod,ofNat_add_mod,Nat.add_assoc,State.activeWordsAfterUInt256,literal_eq_ofNat,capacity,ha32,hf32,ha292,hf292]
def part7Program : List Instr := [.push 1 64,.op .MSTORE,.op (.Swap sA0),.op (.Swap sA1),.push 2 262,.op .MLOAD,.op .AND,.push 1 96,.op .MSTORE]
def part7Model (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 w20 w21 w22 w23 w24 : W) (rest : List W) : State :=
  let v0 : ByteArray := MachineState.writeBytes (s.memory) (Data.Bytes.natToBytesPadded w0.toNat 32) 64
  let v1 : W := MachineState.readWord v0 262
  let v2 : W := UInt256.land v1 w3
  let v3 : ByteArray := MachineState.writeBytes v0 (Data.Bytes.natToBytesPadded v2.toNat 32) 96
  {s with pc := N 8546,memory := v3,stack := w1::w2::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::w16::w17::w18::w19::w20::w21::w22::w23::w24::rest}
theorem part7_run (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 w20 w21 w22 w23 w24 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions part7Program {s with pc := N 8533,memory := s.memory,stack := w0::w1::w2::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::w16::w17::w18::w19::w20::w21::w22::w23::w24::rest} = some (part7Model s w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 w20 w21 w22 w23 w24 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 63) : rest.length+j < 1024 := by omega
  have ha64 : (64 : W).toNat = 64 := rfl
  have hf64 := Monpro.activeWords_fix s 64 32 (by decide) (by norm_num) hact
  have ha96 : (96 : W).toNat = 96 := rfl
  have hf96 := Monpro.activeWords_fix s 96 32 (by decide) (by norm_num) hact
  have ha262 : (262 : W).toNat = 262 := rfl
  have hf262 := Monpro.activeWords_fix s 262 32 (by decide) (by norm_num) hact
  simp [hz,hzn,part7Program,part7Model,runInstructions,runInstr,List.exchange,succ_ofNat_mod,ofNat_add_mod,Nat.add_assoc,State.activeWordsAfterUInt256,literal_eq_ofNat,capacity,ha64,hf64,ha96,hf96,ha262,hf262]
def part8Program : List Instr := [.push 2 256,.op .MLOAD,.push 1 192,.op .SHR,.push 1 128,.op .MSTORE,.push 2 2112,.op .MLOAD]
def part8Model (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 w20 w21 w22 : W) (rest : List W) : State :=
  let v0 : W := MachineState.readWord (s.memory) 256
  let v1 : W := UInt256.shiftRight v0 (N 192)
  let v2 : ByteArray := MachineState.writeBytes (s.memory) (Data.Bytes.natToBytesPadded v1.toNat 32) 128
  let v3 : W := MachineState.readWord v2 2112
  {s with pc := N 8560,memory := v2,stack := v3::w0::w1::w2::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::w16::w17::w18::w19::w20::w21::w22::rest}
theorem part8_run (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 w20 w21 w22 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions part8Program {s with pc := N 8546,memory := s.memory,stack := w0::w1::w2::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::w16::w17::w18::w19::w20::w21::w22::rest} = some (part8Model s w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 w20 w21 w22 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 63) : rest.length+j < 1024 := by omega
  have ha128 : (128 : W).toNat = 128 := rfl
  have hf128 := Monpro.activeWords_fix s 128 32 (by decide) (by norm_num) hact
  have ha256 : (256 : W).toNat = 256 := rfl
  have hf256 := Monpro.activeWords_fix s 256 32 (by decide) (by norm_num) hact
  have ha2112 : (2112 : W).toNat = 2112 := rfl
  have hf2112 := Monpro.activeWords_fix s 2112 32 (by decide) (by norm_num) hact
  simp [hz,hzn,part8Program,part8Model,runInstructions,runInstr,List.exchange,succ_ofNat_mod,ofNat_add_mod,Nat.add_assoc,State.activeWordsAfterUInt256,literal_eq_ofNat,capacity,ha128,hf128,ha256,hf256,ha2112,hf2112]
def part9Program : List Instr := [.push 1 16,.op .SHR,.op (.Dup dA0),.push 1 200,.op .SHR,.push 5 1099511627775,.op .EQ]
def part9Model (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 w20 w21 w22 w23 : W) (rest : List W) : State :=
  let v0 : W := UInt256.shiftRight w0 (N 16)
  let v1 : W := UInt256.shiftRight v0 (N 200)
  let v2 : W := UInt256.eq (N 1099511627775) v1
  {s with pc := N 8574,memory := s.memory,stack := v2::v0::w1::w2::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::w16::w17::w18::w19::w20::w21::w22::w23::rest}
theorem part9_run (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 w20 w21 w22 w23 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions part9Program {s with pc := N 8560,memory := s.memory,stack := w0::w1::w2::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::w16::w17::w18::w19::w20::w21::w22::w23::rest} = some (part9Model s w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 w20 w21 w22 w23 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 63) : rest.length+j < 1024 := by omega
  simp [hz,hzn,part9Program,part9Model,runInstructions,runInstr,List.exchange,succ_ofNat_mod,ofNat_add_mod,Nat.add_assoc,State.activeWordsAfterUInt256,literal_eq_ofNat,capacity]
def program : List Instr := (part0Program++(part1Program++(part2Program++(part3Program++(part4Program++(part5Program++(part6Program++(part7Program++(part8Program++part9Program)))))))))
def model (s : State) (f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 : W) (rest : List W) : State :=
  let v0 : W := UInt256.shiftLeft f11 (N 16)
  let v1 : ByteArray := MachineState.writeBytes (s.memory) (Data.Bytes.natToBytesPadded v0.toNat 32) 192
  let v2 : W := UInt256.lnot (N 0)
  let v3 : W := UInt256.shiftRight v2 (N 5)
  let v4 : W := UInt256.shiftRight v3 (N 11)
  let v5 : ByteArray := MachineState.writeBytes v1 (Data.Bytes.natToBytesPadded v4.toNat 32) 224
  let v6 : W := MachineState.readWord v5 0
  let v7 : W := UInt256.shiftRight v6 (N 192)
  let v8 : W := MachineState.readWord v5 224
  let v9 : W := MachineState.readWord v5 36
  let v10 : W := UInt256.land v8 v9
  let v11 : W := MachineState.readWord v5 66
  let v12 : W := UInt256.land v8 v11
  let v13 : W := MachineState.readWord v5 96
  let v14 : W := MachineState.readWord v5 6
  let v15 : W := UInt256.land v8 v14
  let v16 : W := UInt256.land v8 v13
  let v17 : ByteArray := MachineState.writeBytes v5 (Data.Bytes.natToBytesPadded v16.toNat 32) 160
  let v18 : W := MachineState.readWord v17 352
  let v19 : W := UInt256.land v8 v18
  let v20 : ByteArray := MachineState.writeBytes v17 (Data.Bytes.natToBytesPadded v19.toNat 32) 0
  let v21 : W := MachineState.readWord v20 322
  let v22 : W := UInt256.land v8 v21
  let v23 : ByteArray := MachineState.writeBytes v20 (Data.Bytes.natToBytesPadded v22.toNat 32) 32
  let v24 : W := MachineState.readWord v23 292
  let v25 : W := UInt256.land v8 v24
  let v26 : ByteArray := MachineState.writeBytes v23 (Data.Bytes.natToBytesPadded v25.toNat 32) 64
  let v27 : W := MachineState.readWord v26 262
  let v28 : W := UInt256.land v27 v8
  let v29 : ByteArray := MachineState.writeBytes v26 (Data.Bytes.natToBytesPadded v28.toNat 32) 96
  let v30 : W := MachineState.readWord v29 256
  let v31 : W := UInt256.shiftRight v30 (N 192)
  let v32 : ByteArray := MachineState.writeBytes v29 (Data.Bytes.natToBytesPadded v31.toNat 32) 128
  let v33 : W := MachineState.readWord v32 2112
  let v34 : W := UInt256.shiftRight v33 (N 16)
  let v35 : W := UInt256.shiftRight v34 (N 200)
  let v36 : W := UInt256.eq (N 1099511627775) v35
  {s with pc := N 8574,memory := v32,stack := v36::v34::v12::v10::v15::v7::v3::v0::f14::f0::f1::f2::f3::f4::f5::f6::f7::f8::f9::f10::f11::f12::f13::f14::f15::rest}
theorem run (s : State) (f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions program {s with pc := N 8456,memory := s.memory,stack := f0::f1::f2::f3::f4::f5::f6::f7::f8::f9::f10::f11::f12::f13::f14::f15::rest} = some (model s f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 rest) := by
  let v0 : W := UInt256.shiftLeft f11 (N 16)
  let v1 : ByteArray := MachineState.writeBytes (s.memory) (Data.Bytes.natToBytesPadded v0.toNat 32) 192
  let v2 : W := UInt256.lnot (N 0)
  let v3 : W := UInt256.shiftRight v2 (N 5)
  let v4 : W := UInt256.shiftRight v3 (N 11)
  let v5 : ByteArray := MachineState.writeBytes v1 (Data.Bytes.natToBytesPadded v4.toNat 32) 224
  let v6 : W := MachineState.readWord v5 0
  let v7 : W := UInt256.shiftRight v6 (N 192)
  let v8 : W := MachineState.readWord v5 224
  let v9 : W := MachineState.readWord v5 36
  let v10 : W := UInt256.land v8 v9
  let v11 : W := MachineState.readWord v5 66
  let v12 : W := UInt256.land v8 v11
  let v13 : W := MachineState.readWord v5 96
  let v14 : W := MachineState.readWord v5 6
  let v15 : W := UInt256.land v8 v14
  let v16 : W := UInt256.land v8 v13
  let v17 : ByteArray := MachineState.writeBytes v5 (Data.Bytes.natToBytesPadded v16.toNat 32) 160
  let v18 : W := MachineState.readWord v17 352
  let v19 : W := UInt256.land v8 v18
  let v20 : ByteArray := MachineState.writeBytes v17 (Data.Bytes.natToBytesPadded v19.toNat 32) 0
  let v21 : W := MachineState.readWord v20 322
  let v22 : W := UInt256.land v8 v21
  let v23 : ByteArray := MachineState.writeBytes v20 (Data.Bytes.natToBytesPadded v22.toNat 32) 32
  let v24 : W := MachineState.readWord v23 292
  let v25 : W := UInt256.land v8 v24
  let v26 : ByteArray := MachineState.writeBytes v23 (Data.Bytes.natToBytesPadded v25.toNat 32) 64
  let v27 : W := MachineState.readWord v26 262
  let v28 : W := UInt256.land v27 v8
  let v29 : ByteArray := MachineState.writeBytes v26 (Data.Bytes.natToBytesPadded v28.toNat 32) 96
  let v30 : W := MachineState.readWord v29 256
  let v31 : W := UInt256.shiftRight v30 (N 192)
  let v32 : ByteArray := MachineState.writeBytes v29 (Data.Bytes.natToBytesPadded v31.toNat 32) 128
  let v33 : W := MachineState.readWord v32 2112
  let v34 : W := UInt256.shiftRight v33 (N 16)
  let v35 : W := UInt256.shiftRight v34 (N 200)
  let v36 : W := UInt256.eq (N 1099511627775) v35
  have h0 : runInstructions part0Program {s with pc := N 8456,memory := s.memory,stack := f0::f1::f2::f3::f4::f5::f6::f7::f8::f9::f10::f11::f12::f13::f14::f15::rest} = some {s with pc := N 8466,memory := v1,stack := v0::f14::f0::f1::f2::f3::f4::f5::f6::f7::f8::f9::f10::f11::f12::f13::f14::f15::rest} := by
    simpa only [part0Model,v0,v1] using part0_run ({s with memory := s.memory}) f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 rest hcap hact
  have h1 : runInstructions part1Program {s with pc := N 8466,memory := v1,stack := v0::f14::f0::f1::f2::f3::f4::f5::f6::f7::f8::f9::f10::f11::f12::f13::f14::f15::rest} = some {s with pc := N 8478,memory := v5,stack := v3::v0::f14::f0::f1::f2::f3::f4::f5::f6::f7::f8::f9::f10::f11::f12::f13::f14::f15::rest} := by
    simpa only [part1Model,v2,v3,v4,v5] using part1_run ({s with memory := v1}) v0 f14 f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 rest hcap hact
  have h2 : runInstructions part2Program {s with pc := N 8478,memory := v5,stack := v3::v0::f14::f0::f1::f2::f3::f4::f5::f6::f7::f8::f9::f10::f11::f12::f13::f14::f15::rest} = some {s with pc := N 8490,memory := v5,stack := v9::v8::v8::v7::v3::v0::f14::f0::f1::f2::f3::f4::f5::f6::f7::f8::f9::f10::f11::f12::f13::f14::f15::rest} := by
    simpa only [part2Model,v6,v7,v8,v9] using part2_run ({s with memory := v5}) v3 v0 f14 f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 rest hcap hact
  have h3 : runInstructions part3Program {s with pc := N 8490,memory := v5,stack := v9::v8::v8::v7::v3::v0::f14::f0::f1::f2::f3::f4::f5::f6::f7::f8::f9::f10::f11::f12::f13::f14::f15::rest} = some {s with pc := N 8500,memory := v5,stack := v13::v12::v10::v8::v8::v7::v3::v0::f14::f0::f1::f2::f3::f4::f5::f6::f7::f8::f9::f10::f11::f12::f13::f14::f15::rest} := by
    simpa only [part3Model,v10,v11,v12,v13] using part3_run ({s with memory := v5}) v9 v8 v8 v7 v3 v0 f14 f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 rest hcap hact
  have h4 : runInstructions part4Program {s with pc := N 8500,memory := v5,stack := v13::v12::v10::v8::v8::v7::v3::v0::f14::f0::f1::f2::f3::f4::f5::f6::f7::f8::f9::f10::f11::f12::f13::f14::f15::rest} = some {s with pc := N 8510,memory := v17,stack := v12::v10::v8::v15::v7::v3::v0::f14::f0::f1::f2::f3::f4::f5::f6::f7::f8::f9::f10::f11::f12::f13::f14::f15::rest} := by
    simpa only [part4Model,v14,v15,v16,v17] using part4_run ({s with memory := v5}) v13 v12 v10 v8 v8 v7 v3 v0 f14 f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 rest hcap hact
  have h5 : runInstructions part5Program {s with pc := N 8510,memory := v17,stack := v12::v10::v8::v15::v7::v3::v0::f14::f0::f1::f2::f3::f4::f5::f6::f7::f8::f9::f10::f11::f12::f13::f14::f15::rest} = some {s with pc := N 8522,memory := v20,stack := v21::v12::v10::v8::v15::v7::v3::v0::f14::f0::f1::f2::f3::f4::f5::f6::f7::f8::f9::f10::f11::f12::f13::f14::f15::rest} := by
    simpa only [part5Model,v18,v19,v20,v21] using part5_run ({s with memory := v17}) v12 v10 v8 v15 v7 v3 v0 f14 f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 rest hcap hact
  have h6 : runInstructions part6Program {s with pc := N 8522,memory := v20,stack := v21::v12::v10::v8::v15::v7::v3::v0::f14::f0::f1::f2::f3::f4::f5::f6::f7::f8::f9::f10::f11::f12::f13::f14::f15::rest} = some {s with pc := N 8533,memory := v23,stack := v25::v12::v10::v8::v15::v7::v3::v0::f14::f0::f1::f2::f3::f4::f5::f6::f7::f8::f9::f10::f11::f12::f13::f14::f15::rest} := by
    simpa only [part6Model,v22,v23,v24,v25] using part6_run ({s with memory := v20}) v21 v12 v10 v8 v15 v7 v3 v0 f14 f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 rest hcap hact
  have h7 : runInstructions part7Program {s with pc := N 8533,memory := v23,stack := v25::v12::v10::v8::v15::v7::v3::v0::f14::f0::f1::f2::f3::f4::f5::f6::f7::f8::f9::f10::f11::f12::f13::f14::f15::rest} = some {s with pc := N 8546,memory := v29,stack := v12::v10::v15::v7::v3::v0::f14::f0::f1::f2::f3::f4::f5::f6::f7::f8::f9::f10::f11::f12::f13::f14::f15::rest} := by
    simpa only [part7Model,v26,v27,v28,v29] using part7_run ({s with memory := v23}) v25 v12 v10 v8 v15 v7 v3 v0 f14 f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 rest hcap hact
  have h8 : runInstructions part8Program {s with pc := N 8546,memory := v29,stack := v12::v10::v15::v7::v3::v0::f14::f0::f1::f2::f3::f4::f5::f6::f7::f8::f9::f10::f11::f12::f13::f14::f15::rest} = some {s with pc := N 8560,memory := v32,stack := v33::v12::v10::v15::v7::v3::v0::f14::f0::f1::f2::f3::f4::f5::f6::f7::f8::f9::f10::f11::f12::f13::f14::f15::rest} := by
    simpa only [part8Model,v30,v31,v32,v33] using part8_run ({s with memory := v29}) v12 v10 v15 v7 v3 v0 f14 f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 rest hcap hact
  have h9 : runInstructions part9Program {s with pc := N 8560,memory := v32,stack := v33::v12::v10::v15::v7::v3::v0::f14::f0::f1::f2::f3::f4::f5::f6::f7::f8::f9::f10::f11::f12::f13::f14::f15::rest} = some {s with pc := N 8574,memory := v32,stack := v36::v34::v12::v10::v15::v7::v3::v0::f14::f0::f1::f2::f3::f4::f5::f6::f7::f8::f9::f10::f11::f12::f13::f14::f15::rest} := by
    simpa only [part9Model,v34,v35,v36] using part9_run ({s with memory := v32}) v33 v12 v10 v15 v7 v3 v0 f14 f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 rest hcap hact
  exact (runInstructions_append_some _ _ _ _ _ h0 (runInstructions_append_some _ _ _ _ _ h1 (runInstructions_append_some _ _ _ _ _ h2 (runInstructions_append_some _ _ _ _ _ h3 (runInstructions_append_some _ _ _ _ _ h4 (runInstructions_append_some _ _ _ _ _ h5 (runInstructions_append_some _ _ _ _ _ h6 (runInstructions_append_some _ _ _ _ _ h7 (runInstructions_append_some _ _ _ _ _ h8 h9)))))))))
end R5CachePrefixOld
namespace R5CachePrefixNew
def part0Program : List Instr := [
  .op .JUMPDEST,
   .op (.Dup dA14),
   .push 1 96,
   .op .MLOAD,
   .push 0 0,
   .op .NOT,
   .push 1 16,
   .op .SHR,
   .op .AND,
   .op (.Dup dA13),
   .push 1 16]
def part0Model (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 : W) (rest : List W) : State :=
  let v0 : W := MachineState.readWord (s.memory) 96
  let v1 : W := UInt256.land (N 1766847064778384329583297500742918515827483896875618958121606201292619775) v0
  {s with pc := N 8665,memory := s.memory,stack := (N 16)::w11::v1::w14::w0::w1::w2::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::rest}
theorem part0_run (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions part0Program {s with pc := N 8651,memory := s.memory,stack := w0::w1::w2::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::rest} = some (part0Model s w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 63) : rest.length+j < 1024 := by omega
  have ha96 : (96 : W).toNat = 96 := rfl
  have hf96 := Monpro.activeWords_fix s 96 32 (by decide) (by norm_num) hact
  have hmask : UInt256.shiftRight (UInt256.lnot (N 0)) (N 16) = N 1766847064778384329583297500742918515827483896875618958121606201292619775 := by decide
  simp [hmask,hz,hzn,part0Program,part0Model,runInstructions,runInstr,List.exchange,succ_ofNat_mod,ofNat_add_mod,Nat.add_assoc,State.activeWordsAfterUInt256,literal_eq_ofNat,capacity,ha96,hf96]
def part1Program : List Instr := [.op .SHL,.op (.Dup dA0),.push 1 192,.op .MSTORE,.push 0 0,.op .NOT,.push 1 5,.op .SHR]
def part1Model (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 : W) (rest : List W) : State :=
  let v0 : W := UInt256.shiftLeft w1 w0
  let v1 : ByteArray := MachineState.writeBytes (s.memory) (Data.Bytes.natToBytesPadded v0.toNat 32) 192
  let v2 : W := UInt256.lnot (N 0)
  let v3 : W := UInt256.shiftRight v2 (N 5)
  {s with pc := N 8675,memory := v1,stack := v3::v0::w2::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::w16::w17::w18::w19::rest}
theorem part1_run (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions part1Program {s with pc := N 8665,memory := s.memory,stack := w0::w1::w2::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::w16::w17::w18::w19::rest} = some (part1Model s w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 63) : rest.length+j < 1024 := by omega
  have ha192 : (192 : W).toNat = 192 := rfl
  have hf192 := Monpro.activeWords_fix s 192 32 (by decide) (by norm_num) hact
  simp [hz,hzn,part1Program,part1Model,runInstructions,runInstr,List.exchange,succ_ofNat_mod,ofNat_add_mod,Nat.add_assoc,State.activeWordsAfterUInt256,literal_eq_ofNat,capacity,ha192,hf192]
def part2Program : List Instr := [.op (.Dup dA0),.push 1 11,.op .SHR,.push 1 224,.op .MSTORE,.push 0 0,.op .MLOAD,.push 1 192]
def part2Model (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 : W) (rest : List W) : State :=
  let v0 : W := UInt256.shiftRight w0 (N 11)
  let v1 : ByteArray := MachineState.writeBytes (s.memory) (Data.Bytes.natToBytesPadded v0.toNat 32) 224
  let v2 : W := MachineState.readWord v1 0
  {s with pc := N 8686,memory := v1,stack := (N 192)::v2::w0::w1::w2::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::w16::w17::w18::w19::rest}
theorem part2_run (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions part2Program {s with pc := N 8675,memory := s.memory,stack := w0::w1::w2::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::w16::w17::w18::w19::rest} = some (part2Model s w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 63) : rest.length+j < 1024 := by omega
  have ha0 : (0 : W).toNat = 0 := rfl
  have hf0 := Monpro.activeWords_fix s 0 32 (by decide) (by norm_num) hact
  have ha224 : (224 : W).toNat = 224 := rfl
  have hf224 := Monpro.activeWords_fix s 224 32 (by decide) (by norm_num) hact
  simp [hz,hzn,part2Program,part2Model,runInstructions,runInstr,List.exchange,succ_ofNat_mod,ofNat_add_mod,Nat.add_assoc,State.activeWordsAfterUInt256,literal_eq_ofNat,capacity,ha0,hf0,ha224,hf224]
def part3Program : List Instr := [.op .SHR,.push 1 224,.op .MLOAD,.op (.Dup dA0),.push 1 36,.op .MLOAD,.op (.Dup dA2),.op .AND]
def part3Model (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 w20 w21 : W) (rest : List W) : State :=
  let v0 : W := UInt256.shiftRight w1 w0
  let v1 : W := MachineState.readWord (s.memory) 224
  let v2 : W := MachineState.readWord (s.memory) 36
  let v3 : W := UInt256.land v1 v2
  {s with pc := N 8696,memory := s.memory,stack := v3::v1::v1::v0::w2::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::w16::w17::w18::w19::w20::w21::rest}
theorem part3_run (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 w20 w21 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions part3Program {s with pc := N 8686,memory := s.memory,stack := w0::w1::w2::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::w16::w17::w18::w19::w20::w21::rest} = some (part3Model s w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 w20 w21 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 63) : rest.length+j < 1024 := by omega
  have ha36 : (36 : W).toNat = 36 := rfl
  have hf36 := Monpro.activeWords_fix s 36 32 (by decide) (by norm_num) hact
  have ha224 : (224 : W).toNat = 224 := rfl
  have hf224 := Monpro.activeWords_fix s 224 32 (by decide) (by norm_num) hact
  simp [hz,hzn,part3Program,part3Model,runInstructions,runInstr,List.exchange,succ_ofNat_mod,ofNat_add_mod,Nat.add_assoc,State.activeWordsAfterUInt256,literal_eq_ofNat,capacity,ha36,hf36,ha224,hf224]
def part4Program : List Instr := [.push 1 66,.op .MLOAD,.op (.Dup dA3),.op .AND,.push 1 96,.op .MLOAD,.push 1 6,.op .MLOAD]
def part4Model (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 w20 w21 w22 w23 : W) (rest : List W) : State :=
  let v0 : W := MachineState.readWord (s.memory) 66
  let v1 : W := UInt256.land w2 v0
  let v2 : W := MachineState.readWord (s.memory) 96
  let v3 : W := MachineState.readWord (s.memory) 6
  {s with pc := N 8707,memory := s.memory,stack := v3::v2::v1::w0::w1::w2::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::w16::w17::w18::w19::w20::w21::w22::w23::rest}
theorem part4_run (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 w20 w21 w22 w23 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions part4Program {s with pc := N 8696,memory := s.memory,stack := w0::w1::w2::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::w16::w17::w18::w19::w20::w21::w22::w23::rest} = some (part4Model s w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 w20 w21 w22 w23 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 63) : rest.length+j < 1024 := by omega
  have ha6 : (6 : W).toNat = 6 := rfl
  have hf6 := Monpro.activeWords_fix s 6 32 (by decide) (by norm_num) hact
  have ha66 : (66 : W).toNat = 66 := rfl
  have hf66 := Monpro.activeWords_fix s 66 32 (by decide) (by norm_num) hact
  have ha96 : (96 : W).toNat = 96 := rfl
  have hf96 := Monpro.activeWords_fix s 96 32 (by decide) (by norm_num) hact
  simp [hz,hzn,part4Program,part4Model,runInstructions,runInstr,List.exchange,succ_ofNat_mod,ofNat_add_mod,Nat.add_assoc,State.activeWordsAfterUInt256,literal_eq_ofNat,capacity,ha6,hf6,ha66,hf66,ha96,hf96]
def part5Program : List Instr := [.op (.Dup dA5),.op .AND,.op (.Swap sA4),.op .AND,.push 1 160,.op .MSTORE,.push 2 352,.op .MLOAD]
def part5Model (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 w20 w21 w22 w23 w24 w25 w26 : W) (rest : List W) : State :=
  let v0 : W := UInt256.land w5 w0
  let v1 : W := UInt256.land w5 w1
  let v2 : ByteArray := MachineState.writeBytes (s.memory) (Data.Bytes.natToBytesPadded v1.toNat 32) 160
  let v3 : W := MachineState.readWord v2 352
  {s with pc := N 8718,memory := v2,stack := v3::w2::w3::w4::v0::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::w16::w17::w18::w19::w20::w21::w22::w23::w24::w25::w26::rest}
theorem part5_run (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 w20 w21 w22 w23 w24 w25 w26 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions part5Program {s with pc := N 8707,memory := s.memory,stack := w0::w1::w2::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::w16::w17::w18::w19::w20::w21::w22::w23::w24::w25::w26::rest} = some (part5Model s w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 w20 w21 w22 w23 w24 w25 w26 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 63) : rest.length+j < 1024 := by omega
  have ha160 : (160 : W).toNat = 160 := rfl
  have hf160 := Monpro.activeWords_fix s 160 32 (by decide) (by norm_num) hact
  have ha352 : (352 : W).toNat = 352 := rfl
  have hf352 := Monpro.activeWords_fix s 352 32 (by decide) (by norm_num) hact
  simp [hz,hzn,part5Program,part5Model,runInstructions,runInstr,List.exchange,succ_ofNat_mod,ofNat_add_mod,Nat.add_assoc,State.activeWordsAfterUInt256,literal_eq_ofNat,capacity,ha160,hf160,ha352,hf352]
def part6Program : List Instr := [.op (.Dup dA3),.op .AND,.push 0 0,.op .MSTORE,.push 2 322,.op .MLOAD,.op (.Dup dA3),.op .AND]
def part6Model (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 w20 w21 w22 w23 w24 w25 : W) (rest : List W) : State :=
  let v0 : W := UInt256.land w3 w0
  let v1 : ByteArray := MachineState.writeBytes (s.memory) (Data.Bytes.natToBytesPadded v0.toNat 32) 0
  let v2 : W := MachineState.readWord v1 322
  let v3 : W := UInt256.land w3 v2
  {s with pc := N 8728,memory := v1,stack := v3::w1::w2::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::w16::w17::w18::w19::w20::w21::w22::w23::w24::w25::rest}
theorem part6_run (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 w20 w21 w22 w23 w24 w25 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions part6Program {s with pc := N 8718,memory := s.memory,stack := w0::w1::w2::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::w16::w17::w18::w19::w20::w21::w22::w23::w24::w25::rest} = some (part6Model s w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 w20 w21 w22 w23 w24 w25 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 63) : rest.length+j < 1024 := by omega
  have ha0 : (0 : W).toNat = 0 := rfl
  have hf0 := Monpro.activeWords_fix s 0 32 (by decide) (by norm_num) hact
  have ha322 : (322 : W).toNat = 322 := rfl
  have hf322 := Monpro.activeWords_fix s 322 32 (by decide) (by norm_num) hact
  simp [hz,hzn,part6Program,part6Model,runInstructions,runInstr,List.exchange,succ_ofNat_mod,ofNat_add_mod,Nat.add_assoc,State.activeWordsAfterUInt256,literal_eq_ofNat,capacity,ha0,hf0,ha322,hf322]
def part7Program : List Instr := [.push 1 32,.op .MSTORE,.push 2 292,.op .MLOAD,.op (.Dup dA3),.op .AND,.push 1 64,.op .MSTORE]
def part7Model (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 w20 w21 w22 w23 w24 w25 : W) (rest : List W) : State :=
  let v0 : ByteArray := MachineState.writeBytes (s.memory) (Data.Bytes.natToBytesPadded w0.toNat 32) 32
  let v1 : W := MachineState.readWord v0 292
  let v2 : W := UInt256.land w3 v1
  let v3 : ByteArray := MachineState.writeBytes v0 (Data.Bytes.natToBytesPadded v2.toNat 32) 64
  {s with pc := N 8740,memory := v3,stack := w1::w2::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::w16::w17::w18::w19::w20::w21::w22::w23::w24::w25::rest}
theorem part7_run (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 w20 w21 w22 w23 w24 w25 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions part7Program {s with pc := N 8728,memory := s.memory,stack := w0::w1::w2::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::w16::w17::w18::w19::w20::w21::w22::w23::w24::w25::rest} = some (part7Model s w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 w20 w21 w22 w23 w24 w25 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 63) : rest.length+j < 1024 := by omega
  have ha32 : (32 : W).toNat = 32 := rfl
  have hf32 := Monpro.activeWords_fix s 32 32 (by decide) (by norm_num) hact
  have ha64 : (64 : W).toNat = 64 := rfl
  have hf64 := Monpro.activeWords_fix s 64 32 (by decide) (by norm_num) hact
  have ha292 : (292 : W).toNat = 292 := rfl
  have hf292 := Monpro.activeWords_fix s 292 32 (by decide) (by norm_num) hact
  simp [hz,hzn,part7Program,part7Model,runInstructions,runInstr,List.exchange,succ_ofNat_mod,ofNat_add_mod,Nat.add_assoc,State.activeWordsAfterUInt256,literal_eq_ofNat,capacity,ha32,hf32,ha64,hf64,ha292,hf292]
def part8Program : List Instr := [.op (.Swap sA0),.op (.Swap sA1),.push 2 262,.op .MLOAD,.op .AND,.push 1 96,.op .MSTORE,.push 2 256,.op .MLOAD]
def part8Model (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 w20 w21 w22 w23 w24 : W) (rest : List W) : State :=
  let v0 : W := MachineState.readWord (s.memory) 262
  let v1 : W := UInt256.land v0 w2
  let v2 : ByteArray := MachineState.writeBytes (s.memory) (Data.Bytes.natToBytesPadded v1.toNat 32) 96
  let v3 : W := MachineState.readWord v2 256
  {s with pc := N 8754,memory := v2,stack := v3::w0::w1::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::w16::w17::w18::w19::w20::w21::w22::w23::w24::rest}
theorem part8_run (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 w20 w21 w22 w23 w24 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions part8Program {s with pc := N 8740,memory := s.memory,stack := w0::w1::w2::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::w16::w17::w18::w19::w20::w21::w22::w23::w24::rest} = some (part8Model s w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 w20 w21 w22 w23 w24 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 63) : rest.length+j < 1024 := by omega
  have ha96 : (96 : W).toNat = 96 := rfl
  have hf96 := Monpro.activeWords_fix s 96 32 (by decide) (by norm_num) hact
  have ha256 : (256 : W).toNat = 256 := rfl
  have hf256 := Monpro.activeWords_fix s 256 32 (by decide) (by norm_num) hact
  have ha262 : (262 : W).toNat = 262 := rfl
  have hf262 := Monpro.activeWords_fix s 262 32 (by decide) (by norm_num) hact
  simp [hz,hzn,part8Program,part8Model,runInstructions,runInstr,List.exchange,succ_ofNat_mod,ofNat_add_mod,Nat.add_assoc,State.activeWordsAfterUInt256,literal_eq_ofNat,capacity,ha96,hf96,ha256,hf256,ha262,hf262]
def part9Program : List Instr := [.push 1 192,.op .SHR,.push 1 128,.op .MSTORE,.push 2 2112,.op .MLOAD,.push 1 16,.op .SHR]
def part9Model (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 w20 w21 w22 w23 w24 : W) (rest : List W) : State :=
  let v0 : W := UInt256.shiftRight w0 (N 192)
  let v1 : ByteArray := MachineState.writeBytes (s.memory) (Data.Bytes.natToBytesPadded v0.toNat 32) 128
  let v2 : W := MachineState.readWord v1 2112
  let v3 : W := UInt256.shiftRight v2 (N 16)
  {s with pc := N 8767,memory := v1,stack := v3::w1::w2::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::w16::w17::w18::w19::w20::w21::w22::w23::w24::rest}
theorem part9_run (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 w20 w21 w22 w23 w24 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions part9Program {s with pc := N 8754,memory := s.memory,stack := w0::w1::w2::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::w16::w17::w18::w19::w20::w21::w22::w23::w24::rest} = some (part9Model s w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 w20 w21 w22 w23 w24 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 63) : rest.length+j < 1024 := by omega
  have ha128 : (128 : W).toNat = 128 := rfl
  have hf128 := Monpro.activeWords_fix s 128 32 (by decide) (by norm_num) hact
  have ha2112 : (2112 : W).toNat = 2112 := rfl
  have hf2112 := Monpro.activeWords_fix s 2112 32 (by decide) (by norm_num) hact
  simp [hz,hzn,part9Program,part9Model,runInstructions,runInstr,List.exchange,succ_ofNat_mod,ofNat_add_mod,Nat.add_assoc,State.activeWordsAfterUInt256,literal_eq_ofNat,capacity,ha128,hf128,ha2112,hf2112]
def part10Program : List Instr := [.op (.Dup dA0),.push 1 200,.op .SHR,.push 5 1099511627775,.op .EQ]
def part10Model (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 w20 w21 w22 w23 w24 : W) (rest : List W) : State :=
  let v0 : W := UInt256.shiftRight w0 (N 200)
  let v1 : W := UInt256.eq (N 1099511627775) v0
  {s with pc := N 8778,memory := s.memory,stack := v1::w0::w1::w2::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::w16::w17::w18::w19::w20::w21::w22::w23::w24::rest}
theorem part10_run (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 w20 w21 w22 w23 w24 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions part10Program {s with pc := N 8767,memory := s.memory,stack := w0::w1::w2::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::w16::w17::w18::w19::w20::w21::w22::w23::w24::rest} = some (part10Model s w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 w20 w21 w22 w23 w24 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 63) : rest.length+j < 1024 := by omega
  simp [hz,hzn,part10Program,part10Model,runInstructions,runInstr,List.exchange,succ_ofNat_mod,ofNat_add_mod,Nat.add_assoc,State.activeWordsAfterUInt256,literal_eq_ofNat,capacity]
def program : List Instr := (part0Program++(part1Program++(part2Program++(part3Program++(part4Program++(part5Program++(part6Program++(part7Program++(part8Program++(part9Program++part10Program))))))))))
def model (s : State) (f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 : W) (rest : List W) : State :=
  let v0 : W := MachineState.readWord (s.memory) 96
  let v1 : W := UInt256.land (N 1766847064778384329583297500742918515827483896875618958121606201292619775) v0
  let v2 : W := UInt256.shiftLeft f11 (N 16)
  let v3 : ByteArray := MachineState.writeBytes (s.memory) (Data.Bytes.natToBytesPadded v2.toNat 32) 192
  let v4 : W := UInt256.lnot (N 0)
  let v5 : W := UInt256.shiftRight v4 (N 5)
  let v6 : W := UInt256.shiftRight v5 (N 11)
  let v7 : ByteArray := MachineState.writeBytes v3 (Data.Bytes.natToBytesPadded v6.toNat 32) 224
  let v8 : W := MachineState.readWord v7 0
  let v9 : W := UInt256.shiftRight v8 (N 192)
  let v10 : W := MachineState.readWord v7 224
  let v11 : W := MachineState.readWord v7 36
  let v12 : W := UInt256.land v10 v11
  let v13 : W := MachineState.readWord v7 66
  let v14 : W := UInt256.land v10 v13
  let v15 : W := MachineState.readWord v7 96
  let v16 : W := MachineState.readWord v7 6
  let v17 : W := UInt256.land v10 v16
  let v18 : W := UInt256.land v10 v15
  let v19 : ByteArray := MachineState.writeBytes v7 (Data.Bytes.natToBytesPadded v18.toNat 32) 160
  let v20 : W := MachineState.readWord v19 352
  let v21 : W := UInt256.land v10 v20
  let v22 : ByteArray := MachineState.writeBytes v19 (Data.Bytes.natToBytesPadded v21.toNat 32) 0
  let v23 : W := MachineState.readWord v22 322
  let v24 : W := UInt256.land v10 v23
  let v25 : ByteArray := MachineState.writeBytes v22 (Data.Bytes.natToBytesPadded v24.toNat 32) 32
  let v26 : W := MachineState.readWord v25 292
  let v27 : W := UInt256.land v10 v26
  let v28 : ByteArray := MachineState.writeBytes v25 (Data.Bytes.natToBytesPadded v27.toNat 32) 64
  let v29 : W := MachineState.readWord v28 262
  let v30 : W := UInt256.land v29 v10
  let v31 : ByteArray := MachineState.writeBytes v28 (Data.Bytes.natToBytesPadded v30.toNat 32) 96
  let v32 : W := MachineState.readWord v31 256
  let v33 : W := UInt256.shiftRight v32 (N 192)
  let v34 : ByteArray := MachineState.writeBytes v31 (Data.Bytes.natToBytesPadded v33.toNat 32) 128
  let v35 : W := MachineState.readWord v34 2112
  let v36 : W := UInt256.shiftRight v35 (N 16)
  let v37 : W := UInt256.shiftRight v36 (N 200)
  let v38 : W := UInt256.eq (N 1099511627775) v37
  {s with pc := N 8778,memory := v34,stack := v38::v36::v14::v12::v17::v9::v5::v2::v1::f14::f0::f1::f2::f3::f4::f5::f6::f7::f8::f9::f10::f11::f12::f13::f14::f15::rest}
theorem run (s : State) (f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions program {s with pc := N 8651,memory := s.memory,stack := f0::f1::f2::f3::f4::f5::f6::f7::f8::f9::f10::f11::f12::f13::f14::f15::rest} = some (model s f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 rest) := by
  let v0 : W := MachineState.readWord (s.memory) 96
  let v1 : W := UInt256.land (N 1766847064778384329583297500742918515827483896875618958121606201292619775) v0
  let v2 : W := UInt256.shiftLeft f11 (N 16)
  let v3 : ByteArray := MachineState.writeBytes (s.memory) (Data.Bytes.natToBytesPadded v2.toNat 32) 192
  let v4 : W := UInt256.lnot (N 0)
  let v5 : W := UInt256.shiftRight v4 (N 5)
  let v6 : W := UInt256.shiftRight v5 (N 11)
  let v7 : ByteArray := MachineState.writeBytes v3 (Data.Bytes.natToBytesPadded v6.toNat 32) 224
  let v8 : W := MachineState.readWord v7 0
  let v9 : W := UInt256.shiftRight v8 (N 192)
  let v10 : W := MachineState.readWord v7 224
  let v11 : W := MachineState.readWord v7 36
  let v12 : W := UInt256.land v10 v11
  let v13 : W := MachineState.readWord v7 66
  let v14 : W := UInt256.land v10 v13
  let v15 : W := MachineState.readWord v7 96
  let v16 : W := MachineState.readWord v7 6
  let v17 : W := UInt256.land v10 v16
  let v18 : W := UInt256.land v10 v15
  let v19 : ByteArray := MachineState.writeBytes v7 (Data.Bytes.natToBytesPadded v18.toNat 32) 160
  let v20 : W := MachineState.readWord v19 352
  let v21 : W := UInt256.land v10 v20
  let v22 : ByteArray := MachineState.writeBytes v19 (Data.Bytes.natToBytesPadded v21.toNat 32) 0
  let v23 : W := MachineState.readWord v22 322
  let v24 : W := UInt256.land v10 v23
  let v25 : ByteArray := MachineState.writeBytes v22 (Data.Bytes.natToBytesPadded v24.toNat 32) 32
  let v26 : W := MachineState.readWord v25 292
  let v27 : W := UInt256.land v10 v26
  let v28 : ByteArray := MachineState.writeBytes v25 (Data.Bytes.natToBytesPadded v27.toNat 32) 64
  let v29 : W := MachineState.readWord v28 262
  let v30 : W := UInt256.land v29 v10
  let v31 : ByteArray := MachineState.writeBytes v28 (Data.Bytes.natToBytesPadded v30.toNat 32) 96
  let v32 : W := MachineState.readWord v31 256
  let v33 : W := UInt256.shiftRight v32 (N 192)
  let v34 : ByteArray := MachineState.writeBytes v31 (Data.Bytes.natToBytesPadded v33.toNat 32) 128
  let v35 : W := MachineState.readWord v34 2112
  let v36 : W := UInt256.shiftRight v35 (N 16)
  let v37 : W := UInt256.shiftRight v36 (N 200)
  let v38 : W := UInt256.eq (N 1099511627775) v37
  have h0 : runInstructions part0Program {s with pc := N 8651,memory := s.memory,stack := f0::f1::f2::f3::f4::f5::f6::f7::f8::f9::f10::f11::f12::f13::f14::f15::rest} = some {s with pc := N 8665,memory := s.memory,stack := (N 16)::f11::v1::f14::f0::f1::f2::f3::f4::f5::f6::f7::f8::f9::f10::f11::f12::f13::f14::f15::rest} := by
    simpa only [part0Model,v0,v1] using part0_run ({s with memory := s.memory}) f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 rest hcap hact
  have h1 : runInstructions part1Program {s with pc := N 8665,memory := s.memory,stack := (N 16)::f11::v1::f14::f0::f1::f2::f3::f4::f5::f6::f7::f8::f9::f10::f11::f12::f13::f14::f15::rest} = some {s with pc := N 8675,memory := v3,stack := v5::v2::v1::f14::f0::f1::f2::f3::f4::f5::f6::f7::f8::f9::f10::f11::f12::f13::f14::f15::rest} := by
    simpa only [part1Model,v2,v3,v4,v5] using part1_run ({s with memory := s.memory}) (N 16) f11 v1 f14 f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 rest hcap hact
  have h2 : runInstructions part2Program {s with pc := N 8675,memory := v3,stack := v5::v2::v1::f14::f0::f1::f2::f3::f4::f5::f6::f7::f8::f9::f10::f11::f12::f13::f14::f15::rest} = some {s with pc := N 8686,memory := v7,stack := (N 192)::v8::v5::v2::v1::f14::f0::f1::f2::f3::f4::f5::f6::f7::f8::f9::f10::f11::f12::f13::f14::f15::rest} := by
    simpa only [part2Model,v6,v7,v8] using part2_run ({s with memory := v3}) v5 v2 v1 f14 f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 rest hcap hact
  have h3 : runInstructions part3Program {s with pc := N 8686,memory := v7,stack := (N 192)::v8::v5::v2::v1::f14::f0::f1::f2::f3::f4::f5::f6::f7::f8::f9::f10::f11::f12::f13::f14::f15::rest} = some {s with pc := N 8696,memory := v7,stack := v12::v10::v10::v9::v5::v2::v1::f14::f0::f1::f2::f3::f4::f5::f6::f7::f8::f9::f10::f11::f12::f13::f14::f15::rest} := by
    simpa only [part3Model,v9,v10,v11,v12] using part3_run ({s with memory := v7}) (N 192) v8 v5 v2 v1 f14 f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 rest hcap hact
  have h4 : runInstructions part4Program {s with pc := N 8696,memory := v7,stack := v12::v10::v10::v9::v5::v2::v1::f14::f0::f1::f2::f3::f4::f5::f6::f7::f8::f9::f10::f11::f12::f13::f14::f15::rest} = some {s with pc := N 8707,memory := v7,stack := v16::v15::v14::v12::v10::v10::v9::v5::v2::v1::f14::f0::f1::f2::f3::f4::f5::f6::f7::f8::f9::f10::f11::f12::f13::f14::f15::rest} := by
    simpa only [part4Model,v13,v14,v15,v16] using part4_run ({s with memory := v7}) v12 v10 v10 v9 v5 v2 v1 f14 f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 rest hcap hact
  have h5 : runInstructions part5Program {s with pc := N 8707,memory := v7,stack := v16::v15::v14::v12::v10::v10::v9::v5::v2::v1::f14::f0::f1::f2::f3::f4::f5::f6::f7::f8::f9::f10::f11::f12::f13::f14::f15::rest} = some {s with pc := N 8718,memory := v19,stack := v20::v14::v12::v10::v17::v9::v5::v2::v1::f14::f0::f1::f2::f3::f4::f5::f6::f7::f8::f9::f10::f11::f12::f13::f14::f15::rest} := by
    simpa only [part5Model,v17,v18,v19,v20] using part5_run ({s with memory := v7}) v16 v15 v14 v12 v10 v10 v9 v5 v2 v1 f14 f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 rest hcap hact
  have h6 : runInstructions part6Program {s with pc := N 8718,memory := v19,stack := v20::v14::v12::v10::v17::v9::v5::v2::v1::f14::f0::f1::f2::f3::f4::f5::f6::f7::f8::f9::f10::f11::f12::f13::f14::f15::rest} = some {s with pc := N 8728,memory := v22,stack := v24::v14::v12::v10::v17::v9::v5::v2::v1::f14::f0::f1::f2::f3::f4::f5::f6::f7::f8::f9::f10::f11::f12::f13::f14::f15::rest} := by
    simpa only [part6Model,v21,v22,v23,v24] using part6_run ({s with memory := v19}) v20 v14 v12 v10 v17 v9 v5 v2 v1 f14 f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 rest hcap hact
  have h7 : runInstructions part7Program {s with pc := N 8728,memory := v22,stack := v24::v14::v12::v10::v17::v9::v5::v2::v1::f14::f0::f1::f2::f3::f4::f5::f6::f7::f8::f9::f10::f11::f12::f13::f14::f15::rest} = some {s with pc := N 8740,memory := v28,stack := v14::v12::v10::v17::v9::v5::v2::v1::f14::f0::f1::f2::f3::f4::f5::f6::f7::f8::f9::f10::f11::f12::f13::f14::f15::rest} := by
    simpa only [part7Model,v25,v26,v27,v28] using part7_run ({s with memory := v22}) v24 v14 v12 v10 v17 v9 v5 v2 v1 f14 f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 rest hcap hact
  have h8 : runInstructions part8Program {s with pc := N 8740,memory := v28,stack := v14::v12::v10::v17::v9::v5::v2::v1::f14::f0::f1::f2::f3::f4::f5::f6::f7::f8::f9::f10::f11::f12::f13::f14::f15::rest} = some {s with pc := N 8754,memory := v31,stack := v32::v14::v12::v17::v9::v5::v2::v1::f14::f0::f1::f2::f3::f4::f5::f6::f7::f8::f9::f10::f11::f12::f13::f14::f15::rest} := by
    simpa only [part8Model,v29,v30,v31,v32] using part8_run ({s with memory := v28}) v14 v12 v10 v17 v9 v5 v2 v1 f14 f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 rest hcap hact
  have h9 : runInstructions part9Program {s with pc := N 8754,memory := v31,stack := v32::v14::v12::v17::v9::v5::v2::v1::f14::f0::f1::f2::f3::f4::f5::f6::f7::f8::f9::f10::f11::f12::f13::f14::f15::rest} = some {s with pc := N 8767,memory := v34,stack := v36::v14::v12::v17::v9::v5::v2::v1::f14::f0::f1::f2::f3::f4::f5::f6::f7::f8::f9::f10::f11::f12::f13::f14::f15::rest} := by
    simpa only [part9Model,v33,v34,v35,v36] using part9_run ({s with memory := v31}) v32 v14 v12 v17 v9 v5 v2 v1 f14 f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 rest hcap hact
  have h10 : runInstructions part10Program {s with pc := N 8767,memory := v34,stack := v36::v14::v12::v17::v9::v5::v2::v1::f14::f0::f1::f2::f3::f4::f5::f6::f7::f8::f9::f10::f11::f12::f13::f14::f15::rest} = some {s with pc := N 8778,memory := v34,stack := v38::v36::v14::v12::v17::v9::v5::v2::v1::f14::f0::f1::f2::f3::f4::f5::f6::f7::f8::f9::f10::f11::f12::f13::f14::f15::rest} := by
    simpa only [part10Model,v37,v38] using part10_run ({s with memory := v34}) v36 v14 v12 v17 v9 v5 v2 v1 f14 f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 rest hcap hact
  exact (runInstructions_append_some _ _ _ _ _ h0 (runInstructions_append_some _ _ _ _ _ h1 (runInstructions_append_some _ _ _ _ _ h2 (runInstructions_append_some _ _ _ _ _ h3 (runInstructions_append_some _ _ _ _ _ h4 (runInstructions_append_some _ _ _ _ _ h5 (runInstructions_append_some _ _ _ _ _ h6 (runInstructions_append_some _ _ _ _ _ h7 (runInstructions_append_some _ _ _ _ _ h8 (runInstructions_append_some _ _ _ _ _ h9 h10))))))))))
end R5CachePrefixNew
namespace R5CachePrefixBridge
open CycleSubmission.R5.ExecPrologue CycleSubmission.R5.PrologueRun
abbrev cached (s : State) : UInt256 := UInt256.land (UInt256.ofNat (2^240-1)) (MachineState.readWord s.memory 96)
def inject (st : State) (word : UInt256) : State :=
  {st with pc := UInt256.ofNat 8778,stack := st.stack.take 8++word::st.stack.drop 8}
theorem embedding (s : State) (f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 : UInt256) (rest : List UInt256) :
 R5CachePrefixNew.model s f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 rest = inject (R5CachePrefixOld.model s f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 rest) (cached s) := by
 simp [R5CachePrefixNew.model,R5CachePrefixOld.model,inject,cached]
theorem old_model (s : State) (f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 : UInt256) (rest : List UInt256) (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
 R5CachePrefixOld.model s f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 rest =
   {s with pc := UInt256.ofNat 8574,memory := proSegM7 s.memory f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15,stack := proSegV8_0 s.memory f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15::proSegV8_1 s.memory f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15::proSegV2_0 s.memory f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15::proSegV2_1 s.memory f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15::proSegV2_2 s.memory f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15::proSegV2_3 s.memory f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15::proSegV2_4 s.memory f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15::proSegV0_0 s.memory f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15::f14::f0::f1::f2::f3::f4::f5::f6::f7::f8::f9::f10::f11::f12::f13::f14::f15::rest} := by
 have hprog : R5CachePrefixOld.program = ConstantFold5349.foldedPrologueProgram := by rfl
 have hraw := R5CachePrefixOld.run s f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 rest hcap hact
 rw [hprog] at hraw
 exact Option.some.inj (hraw.symm.trans (ConstantFold5349.folded_proSeg_run s f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 rest hcap hact))
theorem cache_matches_memory (s : State) (f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 : UInt256) (rest : List UInt256) :
 MachineState.readWord (proSegM7 s.memory f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15) 160 = cached s := by
 simpa only [cached,CycleSubmission.R5.Digits.M] using CycleSubmission.R5.PrologueMeaning.m7_n0 s.memory f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15
def result (s : State) (f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 : UInt256) (rest : List UInt256) : State := inject (R5CachePrefixOld.model s f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 rest) (MachineState.readWord (R5CachePrefixOld.model s f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 rest).memory 160)
theorem run (s : State) (f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 : UInt256) (rest : List UInt256) (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
 runInstructions R5CachePrefixNew.program {s with pc := UInt256.ofNat 8651,stack := f0::f1::f2::f3::f4::f5::f6::f7::f8::f9::f10::f11::f12::f13::f14::f15::rest} = some (result s f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 rest) := by
 have h := R5CachePrefixNew.run s f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 rest hcap hact
 rw [embedding] at h
 have hm : MachineState.readWord (R5CachePrefixOld.model s f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 rest).memory 160 = cached s := by
  rw [old_model s f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 rest hcap hact]
  exact cache_matches_memory s f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 rest
 simpa only [result,hm] using h
theorem result_eq (s : State) (f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 : UInt256) (rest : List UInt256) (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
 result s f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 rest = {s with pc := UInt256.ofNat 8778,memory := proSegM7 s.memory f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15,stack := proSegV8_0 s.memory f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15::proSegV8_1 s.memory f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15::proSegV2_0 s.memory f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15::proSegV2_1 s.memory f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15::proSegV2_2 s.memory f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15::proSegV2_3 s.memory f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15::proSegV2_4 s.memory f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15::proSegV0_0 s.memory f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15::(MachineState.readWord (proSegM7 s.memory f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15) 160)::f14::f0::f1::f2::f3::f4::f5::f6::f7::f8::f9::f10::f11::f12::f13::f14::f15::rest} := by
 simpa only [result,old_model s f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 rest hcap hact,inject,List.take_succ_cons,List.drop_succ_cons,List.take_zero,List.drop_zero,List.cons_append,List.nil_append]
#print axioms run
end R5CachePrefixBridge
