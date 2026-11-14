import Challenge.Modexp.Submission.Proofs.Prepared.R9Shared.RawPrelude
open CycleSubmission.SharedStackArgs
set_option maxRecDepth 40000
set_option maxHeartbeats 8000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
namespace CycleSubmission.Execution
open EvmSemantics EvmSemantics.EVM YulEvmCompiler
open Challenge.EvmProof.Word Challenge.EvmProof.Stepper
open CycleSubmission.Prepared.Arithmetic
open Challenge.Modexp.Submission.Proofs.Bytecode.WindowNibbleKernel
open Challenge.Modexp.Submission.Proofs.Fast
local notation "W" => UInt256
local notation "N" => UInt256.ofNat
def entrypart0Program : List Instr := [.op .JUMPDEST,.op (.Dup dA14),.op (.Dup dA6),.push 1 16,.op .SHR,.push 2 2368,.op .MLOAD]
def entrypart0Model (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 : W) (rest : List W) : State :=
  let v0 : W := UInt256.shiftRight w5 (N 16)
  let v1 : W := MachineState.readWord (s.memory) 2368
  {s with pc := N 3330,memory := s.memory,stack := v1::v0::w14::w0::w1::w2::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::rest}
theorem entrypart0_run (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions entrypart0Program {s with pc := N 3320,memory := s.memory,stack := w0::w1::w2::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::rest} = some (entrypart0Model s w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 63) : rest.length+j < 1024 := by omega
  have ha16 : (16 : W).toNat = 16 := rfl
  have hf16 := Monpro.activeWords_fix s 16 32 (by decide) (by norm_num) hact
  have ha2368 : (2368 : W).toNat = 2368 := rfl
  have hf2368 := Monpro.activeWords_fix s 2368 32 (by decide) (by norm_num) hact
  simp [hz,hzn,entrypart0Program,entrypart0Model,runInstructions,runInstr,List.exchange,succ_ofNat_mod,ofNat_add_mod,Nat.add_assoc,State.activeWordsAfterUInt256,literal_eq_ofNat,capacity,ha16,hf16,ha2368,hf2368]
def entrypart1Program : List Instr := [.push 1 16,.op .SHR,.push 1 134,.op .MLOAD,.op (.Dup dA2),.op .AND,.push 1 224,.op .MLOAD]
def entrypart1Model (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 : W) (rest : List W) : State :=
  let v0 : W := UInt256.shiftRight w0 (N 16)
  let v1 : W := MachineState.readWord (s.memory) 134
  let v2 : W := UInt256.land w1 v1
  let v3 : W := MachineState.readWord (s.memory) 224
  {s with pc := N 3341,memory := s.memory,stack := v3::v2::v0::w1::w2::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::w16::w17::w18::rest}
theorem entrypart1_run (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions entrypart1Program {s with pc := N 3330,memory := s.memory,stack := w0::w1::w2::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::w16::w17::w18::rest} = some (entrypart1Model s w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 63) : rest.length+j < 1024 := by omega
  have ha16 : (16 : W).toNat = 16 := rfl
  have hf16 := Monpro.activeWords_fix s 16 32 (by decide) (by norm_num) hact
  have ha134 : (134 : W).toNat = 134 := rfl
  have hf134 := Monpro.activeWords_fix s 134 32 (by decide) (by norm_num) hact
  have ha224 : (224 : W).toNat = 224 := rfl
  have hf224 := Monpro.activeWords_fix s 224 32 (by decide) (by norm_num) hact
  simp [hz,hzn,entrypart1Program,entrypart1Model,runInstructions,runInstr,List.exchange,succ_ofNat_mod,ofNat_add_mod,Nat.add_assoc,State.activeWordsAfterUInt256,literal_eq_ofNat,capacity,ha16,hf16,ha134,hf134,ha224,hf224]
def entrypart2Program : List Instr := [.op (.Dup dA3),.op .AND,.op (.Dup dA0),.push 2 1344,.op .MSTORE,.op (.Swap sA0),.op (.Swap sA1),.op (.Swap sA2)]
def entrypart2Model (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 w20 : W) (rest : List W) : State :=
  let v0 : W := UInt256.land w3 w0
  let v1 : ByteArray := MachineState.writeBytes (s.memory) (Data.Bytes.natToBytesPadded v0.toNat 32) 1344
  {s with pc := N 3351,memory := v1,stack := w3::v0::w1::w2::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::w16::w17::w18::w19::w20::rest}
theorem entrypart2_run (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 w20 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions entrypart2Program {s with pc := N 3341,memory := s.memory,stack := w0::w1::w2::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::w16::w17::w18::w19::w20::rest} = some (entrypart2Model s w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 w20 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 63) : rest.length+j < 1024 := by omega
  have ha1344 : (1344 : W).toNat = 1344 := rfl
  have hf1344 := Monpro.activeWords_fix s 1344 32 (by decide) (by norm_num) hact
  simp [hz,hzn,entrypart2Program,entrypart2Model,runInstructions,runInstr,List.exchange,succ_ofNat_mod,ofNat_add_mod,Nat.add_assoc,State.activeWordsAfterUInt256,literal_eq_ofNat,capacity,ha1344,hf1344]
def entrypart3Program : List Instr := [.push 1 194,.op .MLOAD,.op (.Dup dA1),.op .AND,.op (.Dup dA0),.push 2 1376,.op .MSTORE,.push 0 0,.op .MLOAD]
def entrypart3Model (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 w20 : W) (rest : List W) : State :=
  let v0 : W := MachineState.readWord (s.memory) 194
  let v1 : W := UInt256.land w0 v0
  let v2 : ByteArray := MachineState.writeBytes (s.memory) (Data.Bytes.natToBytesPadded v1.toNat 32) 1376
  let v3 : W := MachineState.readWord v2 0
  {s with pc := N 3363,memory := v2,stack := v3::v1::w0::w1::w2::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::w16::w17::w18::w19::w20::rest}
theorem entrypart3_run (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 w20 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions entrypart3Program {s with pc := N 3351,memory := s.memory,stack := w0::w1::w2::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::w16::w17::w18::w19::w20::rest} = some (entrypart3Model s w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 w20 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 63) : rest.length+j < 1024 := by omega
  have ha0 : (0 : W).toNat = 0 := rfl
  have hf0 := Monpro.activeWords_fix s 0 32 (by decide) (by norm_num) hact
  have ha194 : (194 : W).toNat = 194 := rfl
  have hf194 := Monpro.activeWords_fix s 194 32 (by decide) (by norm_num) hact
  have ha1376 : (1376 : W).toNat = 1376 := rfl
  have hf1376 := Monpro.activeWords_fix s 1376 32 (by decide) (by norm_num) hact
  simp [hz,hzn,entrypart3Program,entrypart3Model,runInstructions,runInstr,List.exchange,succ_ofNat_mod,ofNat_add_mod,Nat.add_assoc,State.activeWordsAfterUInt256,literal_eq_ofNat,capacity,ha0,hf0,ha194,hf194,ha1376,hf1376]
def entrypart4Program : List Instr := [.push 1 128,.op .SHR,.op (.Dup dA0),.push 2 1600,.op .MSTORE,.push 0 0,.op .NOT,.push 1 5,.op .SHR,.push 1 14,.op .MLOAD]
def entrypart4Model (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 w20 w21 w22 : W) (rest : List W) : State :=
  let v0 : W := UInt256.shiftRight w0 (N 128)
  let v1 : ByteArray := MachineState.writeBytes (s.memory) (Data.Bytes.natToBytesPadded v0.toNat 32) 1600
  let v2 : W := UInt256.lnot (N 0)
  let v3 : W := UInt256.shiftRight v2 (N 5)
  let v4 : W := MachineState.readWord v1 14
  {s with pc := N 3379,memory := v1,stack := v4::v3::v0::w1::w2::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::w16::w17::w18::w19::w20::w21::w22::rest}
theorem entrypart4_run (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 w20 w21 w22 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions entrypart4Program {s with pc := N 3363,memory := s.memory,stack := w0::w1::w2::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::w16::w17::w18::w19::w20::w21::w22::rest} = some (entrypart4Model s w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 w20 w21 w22 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 63) : rest.length+j < 1024 := by omega
  have ha5 : (5 : W).toNat = 5 := rfl
  have hf5 := Monpro.activeWords_fix s 5 32 (by decide) (by norm_num) hact
  have ha14 : (14 : W).toNat = 14 := rfl
  have hf14 := Monpro.activeWords_fix s 14 32 (by decide) (by norm_num) hact
  have ha128 : (128 : W).toNat = 128 := rfl
  have hf128 := Monpro.activeWords_fix s 128 32 (by decide) (by norm_num) hact
  have ha1600 : (1600 : W).toNat = 1600 := rfl
  have hf1600 := Monpro.activeWords_fix s 1600 32 (by decide) (by norm_num) hact
  simp [hz,hzn,entrypart4Program,entrypart4Model,runInstructions,runInstr,List.exchange,succ_ofNat_mod,ofNat_add_mod,Nat.add_assoc,State.activeWordsAfterUInt256,literal_eq_ofNat,capacity,ha5,hf5,ha14,hf14,ha128,hf128,ha1600,hf1600]
def entrypart5Program : List Instr := [.op (.Dup dA4),.op .AND,.op (.Dup dA0),.push 2 1568,.op .MSTORE,.push 1 74,.op .MLOAD,.op (.Dup dA5)]
def entrypart5Model (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 w20 w21 w22 w23 w24 : W) (rest : List W) : State :=
  let v0 : W := UInt256.land w4 w0
  let v1 : ByteArray := MachineState.writeBytes (s.memory) (Data.Bytes.natToBytesPadded v0.toNat 32) 1568
  let v2 : W := MachineState.readWord v1 74
  {s with pc := N 3390,memory := v1,stack := w4::v2::v0::w1::w2::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::w16::w17::w18::w19::w20::w21::w22::w23::w24::rest}
theorem entrypart5_run (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 w20 w21 w22 w23 w24 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions entrypart5Program {s with pc := N 3379,memory := s.memory,stack := w0::w1::w2::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::w16::w17::w18::w19::w20::w21::w22::w23::w24::rest} = some (entrypart5Model s w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 w20 w21 w22 w23 w24 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 63) : rest.length+j < 1024 := by omega
  have ha74 : (74 : W).toNat = 74 := rfl
  have hf74 := Monpro.activeWords_fix s 74 32 (by decide) (by norm_num) hact
  have ha1568 : (1568 : W).toNat = 1568 := rfl
  have hf1568 := Monpro.activeWords_fix s 1568 32 (by decide) (by norm_num) hact
  simp [hz,hzn,entrypart5Program,entrypart5Model,runInstructions,runInstr,List.exchange,succ_ofNat_mod,ofNat_add_mod,Nat.add_assoc,State.activeWordsAfterUInt256,literal_eq_ofNat,capacity,ha74,hf74,ha1568,hf1568]
def entrypart6Program : List Instr := [.op .AND,.push 2 2546,.op .MLOAD,.op (.Dup dA6),.op .AND,.push 2 2576,.op .MLOAD,.op (.Dup dA7)]
def entrypart6Model (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 w20 w21 w22 w23 w24 w25 w26 : W) (rest : List W) : State :=
  let v0 : W := UInt256.land w0 w1
  let v1 : W := MachineState.readWord (s.memory) 2546
  let v2 : W := UInt256.land w6 v1
  let v3 : W := MachineState.readWord (s.memory) 2576
  {s with pc := N 3402,memory := s.memory,stack := w6::v3::v2::v0::w2::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::w16::w17::w18::w19::w20::w21::w22::w23::w24::w25::w26::rest}
theorem entrypart6_run (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 w20 w21 w22 w23 w24 w25 w26 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions entrypart6Program {s with pc := N 3390,memory := s.memory,stack := w0::w1::w2::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::w16::w17::w18::w19::w20::w21::w22::w23::w24::w25::w26::rest} = some (entrypart6Model s w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 w20 w21 w22 w23 w24 w25 w26 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 63) : rest.length+j < 1024 := by omega
  have ha2546 : (2546 : W).toNat = 2546 := rfl
  have hf2546 := Monpro.activeWords_fix s 2546 32 (by decide) (by norm_num) hact
  have ha2576 : (2576 : W).toNat = 2576 := rfl
  have hf2576 := Monpro.activeWords_fix s 2576 32 (by decide) (by norm_num) hact
  simp [hz,hzn,entrypart6Program,entrypart6Model,runInstructions,runInstr,List.exchange,succ_ofNat_mod,ofNat_add_mod,Nat.add_assoc,State.activeWordsAfterUInt256,literal_eq_ofNat,capacity,ha2546,hf2546,ha2576,hf2576]
def entrypart7Program : List Instr := [.op .AND,.push 1 104,.op .MLOAD,.op (.Dup dA8),.op .AND,.push 1 44,.op .MLOAD,.op (.Dup dA9)]
def entrypart7Model (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 w20 w21 w22 w23 w24 w25 w26 w27 w28 : W) (rest : List W) : State :=
  let v0 : W := UInt256.land w0 w1
  let v1 : W := MachineState.readWord (s.memory) 104
  let v2 : W := UInt256.land w8 v1
  let v3 : W := MachineState.readWord (s.memory) 44
  {s with pc := N 3412,memory := s.memory,stack := w8::v3::v2::v0::w2::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::w16::w17::w18::w19::w20::w21::w22::w23::w24::w25::w26::w27::w28::rest}
theorem entrypart7_run (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 w20 w21 w22 w23 w24 w25 w26 w27 w28 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions entrypart7Program {s with pc := N 3402,memory := s.memory,stack := w0::w1::w2::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::w16::w17::w18::w19::w20::w21::w22::w23::w24::w25::w26::w27::w28::rest} = some (entrypart7Model s w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 w20 w21 w22 w23 w24 w25 w26 w27 w28 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 63) : rest.length+j < 1024 := by omega
  have ha44 : (44 : W).toNat = 44 := rfl
  have hf44 := Monpro.activeWords_fix s 44 32 (by decide) (by norm_num) hact
  have ha104 : (104 : W).toNat = 104 := rfl
  have hf104 := Monpro.activeWords_fix s 104 32 (by decide) (by norm_num) hact
  simp [hz,hzn,entrypart7Program,entrypart7Model,runInstructions,runInstr,List.exchange,succ_ofNat_mod,ofNat_add_mod,Nat.add_assoc,State.activeWordsAfterUInt256,literal_eq_ofNat,capacity,ha44,hf44,ha104,hf104]
def entrypart8Program : List Instr := [.op .AND,.push 1 164,.op .MLOAD,.op (.Dup dA10),.op .AND,.push 2 2592,.op .MLOAD,.push 1 112]
def entrypart8Model (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 w20 w21 w22 w23 w24 w25 w26 w27 w28 w29 w30 : W) (rest : List W) : State :=
  let v0 : W := UInt256.land w0 w1
  let v1 : W := MachineState.readWord (s.memory) 164
  let v2 : W := UInt256.land w10 v1
  let v3 : W := MachineState.readWord (s.memory) 2592
  {s with pc := N 3424,memory := s.memory,stack := (N 112)::v3::v2::v0::w2::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::w16::w17::w18::w19::w20::w21::w22::w23::w24::w25::w26::w27::w28::w29::w30::rest}
theorem entrypart8_run (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 w20 w21 w22 w23 w24 w25 w26 w27 w28 w29 w30 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions entrypart8Program {s with pc := N 3412,memory := s.memory,stack := w0::w1::w2::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::w16::w17::w18::w19::w20::w21::w22::w23::w24::w25::w26::w27::w28::w29::w30::rest} = some (entrypart8Model s w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 w20 w21 w22 w23 w24 w25 w26 w27 w28 w29 w30 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 63) : rest.length+j < 1024 := by omega
  have ha112 : (112 : W).toNat = 112 := rfl
  have hf112 := Monpro.activeWords_fix s 112 32 (by decide) (by norm_num) hact
  have ha164 : (164 : W).toNat = 164 := rfl
  have hf164 := Monpro.activeWords_fix s 164 32 (by decide) (by norm_num) hact
  have ha2592 : (2592 : W).toNat = 2592 := rfl
  have hf2592 := Monpro.activeWords_fix s 2592 32 (by decide) (by norm_num) hact
  simp [hz,hzn,entrypart8Program,entrypart8Model,runInstructions,runInstr,List.exchange,succ_ofNat_mod,ofNat_add_mod,Nat.add_assoc,State.activeWordsAfterUInt256,literal_eq_ofNat,capacity,ha112,hf112,ha164,hf164,ha2592,hf2592]
def entrypart9Program : List Instr := [.op .SHL,.op (.Dup dA11),.op .AND,.push 2 768,.op .MSTORE,.push 2 2516,.op .MLOAD,.op (.Dup dA11)]
def entrypart9Model (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 w20 w21 w22 w23 w24 w25 w26 w27 w28 w29 w30 w31 w32 : W) (rest : List W) : State :=
  let v0 : W := UInt256.shiftLeft w1 w0
  let v1 : W := UInt256.land w12 v0
  let v2 : ByteArray := MachineState.writeBytes (s.memory) (Data.Bytes.natToBytesPadded v1.toNat 32) 768
  let v3 : W := MachineState.readWord v2 2516
  {s with pc := N 3436,memory := v2,stack := w12::v3::w2::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::w16::w17::w18::w19::w20::w21::w22::w23::w24::w25::w26::w27::w28::w29::w30::w31::w32::rest}
theorem entrypart9_run (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 w20 w21 w22 w23 w24 w25 w26 w27 w28 w29 w30 w31 w32 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions entrypart9Program {s with pc := N 3424,memory := s.memory,stack := w0::w1::w2::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::w16::w17::w18::w19::w20::w21::w22::w23::w24::w25::w26::w27::w28::w29::w30::w31::w32::rest} = some (entrypart9Model s w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 w20 w21 w22 w23 w24 w25 w26 w27 w28 w29 w30 w31 w32 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 63) : rest.length+j < 1024 := by omega
  have ha768 : (768 : W).toNat = 768 := rfl
  have hf768 := Monpro.activeWords_fix s 768 32 (by decide) (by norm_num) hact
  have ha2516 : (2516 : W).toNat = 2516 := rfl
  have hf2516 := Monpro.activeWords_fix s 2516 32 (by decide) (by norm_num) hact
  simp [hz,hzn,entrypart9Program,entrypart9Model,runInstructions,runInstr,List.exchange,succ_ofNat_mod,ofNat_add_mod,Nat.add_assoc,State.activeWordsAfterUInt256,literal_eq_ofNat,capacity,ha768,hf768,ha2516,hf2516]
def entrypart10Program : List Instr := [.op .AND,.push 1 32,.op .MSTORE,.push 2 2486,.op .MLOAD,.op (.Dup dA11),.op .AND,.push 1 64,.op .MSTORE]
def entrypart10Model (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 w20 w21 w22 w23 w24 w25 w26 w27 w28 w29 w30 w31 w32 : W) (rest : List W) : State :=
  let v0 : W := UInt256.land w0 w1
  let v1 : ByteArray := MachineState.writeBytes (s.memory) (Data.Bytes.natToBytesPadded v0.toNat 32) 32
  let v2 : W := MachineState.readWord v1 2486
  let v3 : W := UInt256.land w12 v2
  let v4 : ByteArray := MachineState.writeBytes v1 (Data.Bytes.natToBytesPadded v3.toNat 32) 64
  {s with pc := N 3449,memory := v4,stack := w2::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::w16::w17::w18::w19::w20::w21::w22::w23::w24::w25::w26::w27::w28::w29::w30::w31::w32::rest}
theorem entrypart10_run (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 w20 w21 w22 w23 w24 w25 w26 w27 w28 w29 w30 w31 w32 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions entrypart10Program {s with pc := N 3436,memory := s.memory,stack := w0::w1::w2::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::w16::w17::w18::w19::w20::w21::w22::w23::w24::w25::w26::w27::w28::w29::w30::w31::w32::rest} = some (entrypart10Model s w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 w20 w21 w22 w23 w24 w25 w26 w27 w28 w29 w30 w31 w32 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 63) : rest.length+j < 1024 := by omega
  have ha32 : (32 : W).toNat = 32 := rfl
  have hf32 := Monpro.activeWords_fix s 32 32 (by decide) (by norm_num) hact
  have ha64 : (64 : W).toNat = 64 := rfl
  have hf64 := Monpro.activeWords_fix s 64 32 (by decide) (by norm_num) hact
  have ha2486 : (2486 : W).toNat = 2486 := rfl
  have hf2486 := Monpro.activeWords_fix s 2486 32 (by decide) (by norm_num) hact
  simp [hz,hzn,entrypart10Program,entrypart10Model,runInstructions,runInstr,List.exchange,succ_ofNat_mod,ofNat_add_mod,Nat.add_assoc,State.activeWordsAfterUInt256,literal_eq_ofNat,capacity,ha32,hf32,ha64,hf64,ha2486,hf2486]
def entrypart11Program : List Instr := [.push 2 2456,.op .MLOAD,.op (.Dup dA11),.op .AND,.op (.Swap sA15),.op .POP,.push 2 2426,.op .MLOAD]
def entrypart11Model (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 w20 w21 w22 w23 w24 w25 w26 w27 w28 w29 w30 : W) (rest : List W) : State :=
  let v0 : W := MachineState.readWord (s.memory) 2456
  let v1 : W := UInt256.land w10 v0
  let v2 : W := MachineState.readWord (s.memory) 2426
  {s with pc := N 3461,memory := s.memory,stack := v2::w0::w1::w2::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::v1::w16::w17::w18::w19::w20::w21::w22::w23::w24::w25::w26::w27::w28::w29::w30::rest}
theorem entrypart11_run (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 w20 w21 w22 w23 w24 w25 w26 w27 w28 w29 w30 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions entrypart11Program {s with pc := N 3449,memory := s.memory,stack := w0::w1::w2::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::w16::w17::w18::w19::w20::w21::w22::w23::w24::w25::w26::w27::w28::w29::w30::rest} = some (entrypart11Model s w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 w20 w21 w22 w23 w24 w25 w26 w27 w28 w29 w30 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 63) : rest.length+j < 1024 := by omega
  have ha2426 : (2426 : W).toNat = 2426 := rfl
  have hf2426 := Monpro.activeWords_fix s 2426 32 (by decide) (by norm_num) hact
  have ha2456 : (2456 : W).toNat = 2456 := rfl
  have hf2456 := Monpro.activeWords_fix s 2456 32 (by decide) (by norm_num) hact
  simp [hz,hzn,entrypart11Program,entrypart11Model,runInstructions,runInstr,List.exchange,succ_ofNat_mod,ofNat_add_mod,Nat.add_assoc,State.activeWordsAfterUInt256,literal_eq_ofNat,capacity,ha2426,hf2426,ha2456,hf2456]
def entrypart12Program : List Instr := [.op (.Dup dA11),.op .AND,.push 1 128,.op .MSTORE,.op (.Swap sA9),.push 2 2396,.op .MLOAD,.op .AND,.op (.Swap sA12),.op (.Swap sA13),.push 0 0,.op .SUB,.op (.Swap sA14),.op (.Swap sA9)]
def entrypart12Model (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 w20 w21 w22 w23 w24 w25 w26 w27 w28 w29 w30 w31 : W) (rest : List W) : State :=
  let v0 : W := UInt256.land w11 w0
  let v1 : ByteArray := MachineState.writeBytes (s.memory) (Data.Bytes.natToBytesPadded v0.toNat 32) 128
  let v2 : W := MachineState.readWord v1 2396
  let v3 : W := UInt256.land v2 w11
  let v4 : W := (N 0) - w15
  {s with pc := N 3478,memory := v1,stack := w1::w2::w3::w4::w5::w6::w7::w8::w9::w10::w16::w12::w13::v3::w14::v4::w17::w18::w19::w20::w21::w22::w23::w24::w25::w26::w27::w28::w29::w30::w31::rest}
theorem entrypart12_run (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 w20 w21 w22 w23 w24 w25 w26 w27 w28 w29 w30 w31 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions entrypart12Program {s with pc := N 3461,memory := s.memory,stack := w0::w1::w2::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::w16::w17::w18::w19::w20::w21::w22::w23::w24::w25::w26::w27::w28::w29::w30::w31::rest} = some (entrypart12Model s w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 w20 w21 w22 w23 w24 w25 w26 w27 w28 w29 w30 w31 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 63) : rest.length+j < 1024 := by omega
  have ha128 : (128 : W).toNat = 128 := rfl
  have hf128 := Monpro.activeWords_fix s 128 32 (by decide) (by norm_num) hact
  have ha2396 : (2396 : W).toNat = 2396 := rfl
  have hf2396 := Monpro.activeWords_fix s 2396 32 (by decide) (by norm_num) hact
  simp [hz,hzn,entrypart12Program,entrypart12Model,runInstructions,runInstr,List.exchange,succ_ofNat_mod,ofNat_add_mod,Nat.add_assoc,State.activeWordsAfterUInt256,literal_eq_ofNat,capacity,ha128,hf128,ha2396,hf2396]
def entrypart13Program : List Instr := []
def entrypart13Model (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 w20 w21 w22 w23 w24 w25 w26 w27 w28 w29 w30 : W) (rest : List W) : State :=
  {s with pc := N 3478,memory := s.memory,stack := w0::w1::w2::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::w16::w17::w18::w19::w20::w21::w22::w23::w24::w25::w26::w27::w28::w29::w30::rest}
theorem entrypart13_run (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 w20 w21 w22 w23 w24 w25 w26 w27 w28 w29 w30 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions entrypart13Program {s with pc := N 3478,memory := s.memory,stack := w0::w1::w2::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::w16::w17::w18::w19::w20::w21::w22::w23::w24::w25::w26::w27::w28::w29::w30::rest} = some (entrypart13Model s w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 w20 w21 w22 w23 w24 w25 w26 w27 w28 w29 w30 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 63) : rest.length+j < 1024 := by omega
  simp [hz,hzn,entrypart13Program,entrypart13Model,runInstructions,runInstr,List.exchange,succ_ofNat_mod,ofNat_add_mod,Nat.add_assoc,State.activeWordsAfterUInt256,literal_eq_ofNat,capacity]
def entryProgram : List Instr := (entrypart0Program++(entrypart1Program++(entrypart2Program++(entrypart3Program++(entrypart4Program++(entrypart5Program++(entrypart6Program++(entrypart7Program++(entrypart8Program++(entrypart9Program++(entrypart10Program++(entrypart11Program++(entrypart12Program++entrypart13Program)))))))))))))
def entryModel (s : State) (pbi hd w3 ent m32 allones m128 m64 m0 tl m96 inv tn aprev counter ret : W) (rest : List W) : State :=
  let v0 : W := UInt256.shiftRight (allones) (N 16)
  let v1 : W := MachineState.readWord (s.memory) 2368
  let v2 : W := UInt256.shiftRight v1 (N 16)
  let v3 : W := MachineState.readWord (s.memory) 134
  let v4 : W := UInt256.land v0 v3
  let v5 : W := MachineState.readWord (s.memory) 224
  let v6 : W := UInt256.land v0 v5
  let v7 : ByteArray := MachineState.writeBytes (s.memory) (Data.Bytes.natToBytesPadded v6.toNat 32) 1344
  let v8 : W := MachineState.readWord v7 194
  let v9 : W := UInt256.land v0 v8
  let v10 : ByteArray := MachineState.writeBytes v7 (Data.Bytes.natToBytesPadded v9.toNat 32) 1376
  let v11 : W := MachineState.readWord v10 0
  let v12 : W := UInt256.shiftRight v11 (N 128)
  let v13 : ByteArray := MachineState.writeBytes v10 (Data.Bytes.natToBytesPadded v12.toNat 32) 1600
  let v14 : W := UInt256.lnot (N 0)
  let v15 : W := UInt256.shiftRight v14 (N 5)
  let v16 : W := MachineState.readWord v13 14
  let v17 : W := UInt256.land v0 v16
  let v18 : ByteArray := MachineState.writeBytes v13 (Data.Bytes.natToBytesPadded v17.toNat 32) 1568
  let v19 : W := MachineState.readWord v18 74
  let v20 : W := UInt256.land v0 v19
  let v21 : W := MachineState.readWord v18 2546
  let v22 : W := UInt256.land v0 v21
  let v23 : W := MachineState.readWord v18 2576
  let v24 : W := UInt256.land v0 v23
  let v25 : W := MachineState.readWord v18 104
  let v26 : W := UInt256.land v0 v25
  let v27 : W := MachineState.readWord v18 44
  let v28 : W := UInt256.land v0 v27
  let v29 : W := MachineState.readWord v18 164
  let v30 : W := UInt256.land v0 v29
  let v31 : W := MachineState.readWord v18 2592
  let v32 : W := UInt256.shiftLeft v31 (N 112)
  let v33 : W := UInt256.land v0 v32
  let v34 : ByteArray := MachineState.writeBytes v18 (Data.Bytes.natToBytesPadded v33.toNat 32) 768
  let v35 : W := MachineState.readWord v34 2516
  let v36 : W := UInt256.land v0 v35
  let v37 : ByteArray := MachineState.writeBytes v34 (Data.Bytes.natToBytesPadded v36.toNat 32) 32
  let v38 : W := MachineState.readWord v37 2486
  let v39 : W := UInt256.land v0 v38
  let v40 : ByteArray := MachineState.writeBytes v37 (Data.Bytes.natToBytesPadded v39.toNat 32) 64
  let v41 : W := MachineState.readWord v40 2456
  let v42 : W := UInt256.land v0 v41
  let v43 : W := MachineState.readWord v40 2426
  let v44 : W := UInt256.land v0 v43
  let v45 : ByteArray := MachineState.writeBytes v40 (Data.Bytes.natToBytesPadded v44.toNat 32) 128
  let v46 : W := MachineState.readWord v45 2396
  let v47 : W := UInt256.land v46 v0
  let v48 : W := (N 0) - (counter)
  {s with pc := N 3478,memory := v45,stack := v30::v28::v26::v24::v22::v20::v17::v15::v12::v9::v42::v6::v4::v47::v2::v48::(hd)::w3::(ent)::(m32)::(allones)::(m128)::(m64)::(m0)::(tl)::(m96)::(inv)::(tn)::(aprev)::(counter)::(ret)::rest}
theorem entry_run (s : State) (pbi hd w3 ent m32 allones m128 m64 m0 tl m96 inv tn aprev counter ret : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions entryProgram {s with pc := N 3320,memory := s.memory,stack := (pbi)::(hd)::w3::(ent)::(m32)::(allones)::(m128)::(m64)::(m0)::(tl)::(m96)::(inv)::(tn)::(aprev)::(counter)::(ret)::rest} = some (entryModel s pbi hd w3 ent m32 allones m128 m64 m0 tl m96 inv tn aprev counter ret rest) := by
  let v0 : W := UInt256.shiftRight (allones) (N 16)
  let v1 : W := MachineState.readWord (s.memory) 2368
  let v2 : W := UInt256.shiftRight v1 (N 16)
  let v3 : W := MachineState.readWord (s.memory) 134
  let v4 : W := UInt256.land v0 v3
  let v5 : W := MachineState.readWord (s.memory) 224
  let v6 : W := UInt256.land v0 v5
  let v7 : ByteArray := MachineState.writeBytes (s.memory) (Data.Bytes.natToBytesPadded v6.toNat 32) 1344
  let v8 : W := MachineState.readWord v7 194
  let v9 : W := UInt256.land v0 v8
  let v10 : ByteArray := MachineState.writeBytes v7 (Data.Bytes.natToBytesPadded v9.toNat 32) 1376
  let v11 : W := MachineState.readWord v10 0
  let v12 : W := UInt256.shiftRight v11 (N 128)
  let v13 : ByteArray := MachineState.writeBytes v10 (Data.Bytes.natToBytesPadded v12.toNat 32) 1600
  let v14 : W := UInt256.lnot (N 0)
  let v15 : W := UInt256.shiftRight v14 (N 5)
  let v16 : W := MachineState.readWord v13 14
  let v17 : W := UInt256.land v0 v16
  let v18 : ByteArray := MachineState.writeBytes v13 (Data.Bytes.natToBytesPadded v17.toNat 32) 1568
  let v19 : W := MachineState.readWord v18 74
  let v20 : W := UInt256.land v0 v19
  let v21 : W := MachineState.readWord v18 2546
  let v22 : W := UInt256.land v0 v21
  let v23 : W := MachineState.readWord v18 2576
  let v24 : W := UInt256.land v0 v23
  let v25 : W := MachineState.readWord v18 104
  let v26 : W := UInt256.land v0 v25
  let v27 : W := MachineState.readWord v18 44
  let v28 : W := UInt256.land v0 v27
  let v29 : W := MachineState.readWord v18 164
  let v30 : W := UInt256.land v0 v29
  let v31 : W := MachineState.readWord v18 2592
  let v32 : W := UInt256.shiftLeft v31 (N 112)
  let v33 : W := UInt256.land v0 v32
  let v34 : ByteArray := MachineState.writeBytes v18 (Data.Bytes.natToBytesPadded v33.toNat 32) 768
  let v35 : W := MachineState.readWord v34 2516
  let v36 : W := UInt256.land v0 v35
  let v37 : ByteArray := MachineState.writeBytes v34 (Data.Bytes.natToBytesPadded v36.toNat 32) 32
  let v38 : W := MachineState.readWord v37 2486
  let v39 : W := UInt256.land v0 v38
  let v40 : ByteArray := MachineState.writeBytes v37 (Data.Bytes.natToBytesPadded v39.toNat 32) 64
  let v41 : W := MachineState.readWord v40 2456
  let v42 : W := UInt256.land v0 v41
  let v43 : W := MachineState.readWord v40 2426
  let v44 : W := UInt256.land v0 v43
  let v45 : ByteArray := MachineState.writeBytes v40 (Data.Bytes.natToBytesPadded v44.toNat 32) 128
  let v46 : W := MachineState.readWord v45 2396
  let v47 : W := UInt256.land v46 v0
  let v48 : W := (N 0) - (counter)
  have h0 : runInstructions entrypart0Program {s with pc := N 3320,memory := s.memory,stack := (pbi)::(hd)::w3::(ent)::(m32)::(allones)::(m128)::(m64)::(m0)::(tl)::(m96)::(inv)::(tn)::(aprev)::(counter)::(ret)::rest} = some {s with pc := N 3330,memory := s.memory,stack := v1::v0::(counter)::(pbi)::(hd)::w3::(ent)::(m32)::(allones)::(m128)::(m64)::(m0)::(tl)::(m96)::(inv)::(tn)::(aprev)::(counter)::(ret)::rest} := by
    simpa only [entrypart0Model,v0,v1] using entrypart0_run ({s with memory := s.memory}) (pbi) (hd) w3 (ent) (m32) (allones) (m128) (m64) (m0) (tl) (m96) (inv) (tn) (aprev) (counter) (ret) rest hcap hact
  have h1 : runInstructions entrypart1Program {s with pc := N 3330,memory := s.memory,stack := v1::v0::(counter)::(pbi)::(hd)::w3::(ent)::(m32)::(allones)::(m128)::(m64)::(m0)::(tl)::(m96)::(inv)::(tn)::(aprev)::(counter)::(ret)::rest} = some {s with pc := N 3341,memory := s.memory,stack := v5::v4::v2::v0::(counter)::(pbi)::(hd)::w3::(ent)::(m32)::(allones)::(m128)::(m64)::(m0)::(tl)::(m96)::(inv)::(tn)::(aprev)::(counter)::(ret)::rest} := by
    simpa only [entrypart1Model,v2,v3,v4,v5] using entrypart1_run ({s with memory := s.memory}) v1 v0 (counter) (pbi) (hd) w3 (ent) (m32) (allones) (m128) (m64) (m0) (tl) (m96) (inv) (tn) (aprev) (counter) (ret) rest hcap hact
  have h2 : runInstructions entrypart2Program {s with pc := N 3341,memory := s.memory,stack := v5::v4::v2::v0::(counter)::(pbi)::(hd)::w3::(ent)::(m32)::(allones)::(m128)::(m64)::(m0)::(tl)::(m96)::(inv)::(tn)::(aprev)::(counter)::(ret)::rest} = some {s with pc := N 3351,memory := v7,stack := v0::v6::v4::v2::(counter)::(pbi)::(hd)::w3::(ent)::(m32)::(allones)::(m128)::(m64)::(m0)::(tl)::(m96)::(inv)::(tn)::(aprev)::(counter)::(ret)::rest} := by
    simpa only [entrypart2Model,v6,v7] using entrypart2_run ({s with memory := s.memory}) v5 v4 v2 v0 (counter) (pbi) (hd) w3 (ent) (m32) (allones) (m128) (m64) (m0) (tl) (m96) (inv) (tn) (aprev) (counter) (ret) rest hcap hact
  have h3 : runInstructions entrypart3Program {s with pc := N 3351,memory := v7,stack := v0::v6::v4::v2::(counter)::(pbi)::(hd)::w3::(ent)::(m32)::(allones)::(m128)::(m64)::(m0)::(tl)::(m96)::(inv)::(tn)::(aprev)::(counter)::(ret)::rest} = some {s with pc := N 3363,memory := v10,stack := v11::v9::v0::v6::v4::v2::(counter)::(pbi)::(hd)::w3::(ent)::(m32)::(allones)::(m128)::(m64)::(m0)::(tl)::(m96)::(inv)::(tn)::(aprev)::(counter)::(ret)::rest} := by
    simpa only [entrypart3Model,v8,v9,v10,v11] using entrypart3_run ({s with memory := v7}) v0 v6 v4 v2 (counter) (pbi) (hd) w3 (ent) (m32) (allones) (m128) (m64) (m0) (tl) (m96) (inv) (tn) (aprev) (counter) (ret) rest hcap hact
  have h4 : runInstructions entrypart4Program {s with pc := N 3363,memory := v10,stack := v11::v9::v0::v6::v4::v2::(counter)::(pbi)::(hd)::w3::(ent)::(m32)::(allones)::(m128)::(m64)::(m0)::(tl)::(m96)::(inv)::(tn)::(aprev)::(counter)::(ret)::rest} = some {s with pc := N 3379,memory := v13,stack := v16::v15::v12::v9::v0::v6::v4::v2::(counter)::(pbi)::(hd)::w3::(ent)::(m32)::(allones)::(m128)::(m64)::(m0)::(tl)::(m96)::(inv)::(tn)::(aprev)::(counter)::(ret)::rest} := by
    simpa only [entrypart4Model,v12,v13,v14,v15,v16] using entrypart4_run ({s with memory := v10}) v11 v9 v0 v6 v4 v2 (counter) (pbi) (hd) w3 (ent) (m32) (allones) (m128) (m64) (m0) (tl) (m96) (inv) (tn) (aprev) (counter) (ret) rest hcap hact
  have h5 : runInstructions entrypart5Program {s with pc := N 3379,memory := v13,stack := v16::v15::v12::v9::v0::v6::v4::v2::(counter)::(pbi)::(hd)::w3::(ent)::(m32)::(allones)::(m128)::(m64)::(m0)::(tl)::(m96)::(inv)::(tn)::(aprev)::(counter)::(ret)::rest} = some {s with pc := N 3390,memory := v18,stack := v0::v19::v17::v15::v12::v9::v0::v6::v4::v2::(counter)::(pbi)::(hd)::w3::(ent)::(m32)::(allones)::(m128)::(m64)::(m0)::(tl)::(m96)::(inv)::(tn)::(aprev)::(counter)::(ret)::rest} := by
    simpa only [entrypart5Model,v17,v18,v19] using entrypart5_run ({s with memory := v13}) v16 v15 v12 v9 v0 v6 v4 v2 (counter) (pbi) (hd) w3 (ent) (m32) (allones) (m128) (m64) (m0) (tl) (m96) (inv) (tn) (aprev) (counter) (ret) rest hcap hact
  have h6 : runInstructions entrypart6Program {s with pc := N 3390,memory := v18,stack := v0::v19::v17::v15::v12::v9::v0::v6::v4::v2::(counter)::(pbi)::(hd)::w3::(ent)::(m32)::(allones)::(m128)::(m64)::(m0)::(tl)::(m96)::(inv)::(tn)::(aprev)::(counter)::(ret)::rest} = some {s with pc := N 3402,memory := v18,stack := v0::v23::v22::v20::v17::v15::v12::v9::v0::v6::v4::v2::(counter)::(pbi)::(hd)::w3::(ent)::(m32)::(allones)::(m128)::(m64)::(m0)::(tl)::(m96)::(inv)::(tn)::(aprev)::(counter)::(ret)::rest} := by
    simpa only [entrypart6Model,v20,v21,v22,v23] using entrypart6_run ({s with memory := v18}) v0 v19 v17 v15 v12 v9 v0 v6 v4 v2 (counter) (pbi) (hd) w3 (ent) (m32) (allones) (m128) (m64) (m0) (tl) (m96) (inv) (tn) (aprev) (counter) (ret) rest hcap hact
  have h7 : runInstructions entrypart7Program {s with pc := N 3402,memory := v18,stack := v0::v23::v22::v20::v17::v15::v12::v9::v0::v6::v4::v2::(counter)::(pbi)::(hd)::w3::(ent)::(m32)::(allones)::(m128)::(m64)::(m0)::(tl)::(m96)::(inv)::(tn)::(aprev)::(counter)::(ret)::rest} = some {s with pc := N 3412,memory := v18,stack := v0::v27::v26::v24::v22::v20::v17::v15::v12::v9::v0::v6::v4::v2::(counter)::(pbi)::(hd)::w3::(ent)::(m32)::(allones)::(m128)::(m64)::(m0)::(tl)::(m96)::(inv)::(tn)::(aprev)::(counter)::(ret)::rest} := by
    simpa only [entrypart7Model,v24,v25,v26,v27] using entrypart7_run ({s with memory := v18}) v0 v23 v22 v20 v17 v15 v12 v9 v0 v6 v4 v2 (counter) (pbi) (hd) w3 (ent) (m32) (allones) (m128) (m64) (m0) (tl) (m96) (inv) (tn) (aprev) (counter) (ret) rest hcap hact
  have h8 : runInstructions entrypart8Program {s with pc := N 3412,memory := v18,stack := v0::v27::v26::v24::v22::v20::v17::v15::v12::v9::v0::v6::v4::v2::(counter)::(pbi)::(hd)::w3::(ent)::(m32)::(allones)::(m128)::(m64)::(m0)::(tl)::(m96)::(inv)::(tn)::(aprev)::(counter)::(ret)::rest} = some {s with pc := N 3424,memory := v18,stack := (N 112)::v31::v30::v28::v26::v24::v22::v20::v17::v15::v12::v9::v0::v6::v4::v2::(counter)::(pbi)::(hd)::w3::(ent)::(m32)::(allones)::(m128)::(m64)::(m0)::(tl)::(m96)::(inv)::(tn)::(aprev)::(counter)::(ret)::rest} := by
    simpa only [entrypart8Model,v28,v29,v30,v31] using entrypart8_run ({s with memory := v18}) v0 v27 v26 v24 v22 v20 v17 v15 v12 v9 v0 v6 v4 v2 (counter) (pbi) (hd) w3 (ent) (m32) (allones) (m128) (m64) (m0) (tl) (m96) (inv) (tn) (aprev) (counter) (ret) rest hcap hact
  have h9 : runInstructions entrypart9Program {s with pc := N 3424,memory := v18,stack := (N 112)::v31::v30::v28::v26::v24::v22::v20::v17::v15::v12::v9::v0::v6::v4::v2::(counter)::(pbi)::(hd)::w3::(ent)::(m32)::(allones)::(m128)::(m64)::(m0)::(tl)::(m96)::(inv)::(tn)::(aprev)::(counter)::(ret)::rest} = some {s with pc := N 3436,memory := v34,stack := v0::v35::v30::v28::v26::v24::v22::v20::v17::v15::v12::v9::v0::v6::v4::v2::(counter)::(pbi)::(hd)::w3::(ent)::(m32)::(allones)::(m128)::(m64)::(m0)::(tl)::(m96)::(inv)::(tn)::(aprev)::(counter)::(ret)::rest} := by
    simpa only [entrypart9Model,v32,v33,v34,v35] using entrypart9_run ({s with memory := v18}) (N 112) v31 v30 v28 v26 v24 v22 v20 v17 v15 v12 v9 v0 v6 v4 v2 (counter) (pbi) (hd) w3 (ent) (m32) (allones) (m128) (m64) (m0) (tl) (m96) (inv) (tn) (aprev) (counter) (ret) rest hcap hact
  have h10 : runInstructions entrypart10Program {s with pc := N 3436,memory := v34,stack := v0::v35::v30::v28::v26::v24::v22::v20::v17::v15::v12::v9::v0::v6::v4::v2::(counter)::(pbi)::(hd)::w3::(ent)::(m32)::(allones)::(m128)::(m64)::(m0)::(tl)::(m96)::(inv)::(tn)::(aprev)::(counter)::(ret)::rest} = some {s with pc := N 3449,memory := v40,stack := v30::v28::v26::v24::v22::v20::v17::v15::v12::v9::v0::v6::v4::v2::(counter)::(pbi)::(hd)::w3::(ent)::(m32)::(allones)::(m128)::(m64)::(m0)::(tl)::(m96)::(inv)::(tn)::(aprev)::(counter)::(ret)::rest} := by
    simpa only [entrypart10Model,v36,v37,v38,v39,v40] using entrypart10_run ({s with memory := v34}) v0 v35 v30 v28 v26 v24 v22 v20 v17 v15 v12 v9 v0 v6 v4 v2 (counter) (pbi) (hd) w3 (ent) (m32) (allones) (m128) (m64) (m0) (tl) (m96) (inv) (tn) (aprev) (counter) (ret) rest hcap hact
  have h11 : runInstructions entrypart11Program {s with pc := N 3449,memory := v40,stack := v30::v28::v26::v24::v22::v20::v17::v15::v12::v9::v0::v6::v4::v2::(counter)::(pbi)::(hd)::w3::(ent)::(m32)::(allones)::(m128)::(m64)::(m0)::(tl)::(m96)::(inv)::(tn)::(aprev)::(counter)::(ret)::rest} = some {s with pc := N 3461,memory := v40,stack := v43::v30::v28::v26::v24::v22::v20::v17::v15::v12::v9::v0::v6::v4::v2::(counter)::v42::(hd)::w3::(ent)::(m32)::(allones)::(m128)::(m64)::(m0)::(tl)::(m96)::(inv)::(tn)::(aprev)::(counter)::(ret)::rest} := by
    simpa only [entrypart11Model,v41,v42,v43] using entrypart11_run ({s with memory := v40}) v30 v28 v26 v24 v22 v20 v17 v15 v12 v9 v0 v6 v4 v2 (counter) (pbi) (hd) w3 (ent) (m32) (allones) (m128) (m64) (m0) (tl) (m96) (inv) (tn) (aprev) (counter) (ret) rest hcap hact
  have h12 : runInstructions entrypart12Program {s with pc := N 3461,memory := v40,stack := v43::v30::v28::v26::v24::v22::v20::v17::v15::v12::v9::v0::v6::v4::v2::(counter)::v42::(hd)::w3::(ent)::(m32)::(allones)::(m128)::(m64)::(m0)::(tl)::(m96)::(inv)::(tn)::(aprev)::(counter)::(ret)::rest} = some {s with pc := N 3478,memory := v45,stack := v30::v28::v26::v24::v22::v20::v17::v15::v12::v9::v42::v6::v4::v47::v2::v48::(hd)::w3::(ent)::(m32)::(allones)::(m128)::(m64)::(m0)::(tl)::(m96)::(inv)::(tn)::(aprev)::(counter)::(ret)::rest} := by
    simpa only [entrypart12Model,v44,v45,v46,v47,v48] using entrypart12_run ({s with memory := v40}) v43 v30 v28 v26 v24 v22 v20 v17 v15 v12 v9 v0 v6 v4 v2 (counter) v42 (hd) w3 (ent) (m32) (allones) (m128) (m64) (m0) (tl) (m96) (inv) (tn) (aprev) (counter) (ret) rest hcap hact
  have h13 : runInstructions entrypart13Program {s with pc := N 3478,memory := v45,stack := v30::v28::v26::v24::v22::v20::v17::v15::v12::v9::v42::v6::v4::v47::v2::v48::(hd)::w3::(ent)::(m32)::(allones)::(m128)::(m64)::(m0)::(tl)::(m96)::(inv)::(tn)::(aprev)::(counter)::(ret)::rest} = some {s with pc := N 3478,memory := v45,stack := v30::v28::v26::v24::v22::v20::v17::v15::v12::v9::v42::v6::v4::v47::v2::v48::(hd)::w3::(ent)::(m32)::(allones)::(m128)::(m64)::(m0)::(tl)::(m96)::(inv)::(tn)::(aprev)::(counter)::(ret)::rest} := by
    simpa only [entrypart13Model] using entrypart13_run ({s with memory := v45}) v30 v28 v26 v24 v22 v20 v17 v15 v12 v9 v42 v6 v4 v47 v2 v48 (hd) w3 (ent) (m32) (allones) (m128) (m64) (m0) (tl) (m96) (inv) (tn) (aprev) (counter) (ret) rest hcap hact
  exact (runInstructions_append_some _ _ _ _ _ h0 (runInstructions_append_some _ _ _ _ _ h1 (runInstructions_append_some _ _ _ _ _ h2 (runInstructions_append_some _ _ _ _ _ h3 (runInstructions_append_some _ _ _ _ _ h4 (runInstructions_append_some _ _ _ _ _ h5 (runInstructions_append_some _ _ _ _ _ h6 (runInstructions_append_some _ _ _ _ _ h7 (runInstructions_append_some _ _ _ _ _ h8 (runInstructions_append_some _ _ _ _ _ h9 (runInstructions_append_some _ _ _ _ _ h10 (runInstructions_append_some _ _ _ _ _ h11 (runInstructions_append_some _ _ _ _ _ h12 h13)))))))))))))
#print axioms entry_run
end CycleSubmission.Execution
