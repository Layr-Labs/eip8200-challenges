import Challenge.Modexp.Submission.Proofs.Prepared.StackArgs
import Challenge.Modexp.Submission.Proofs.Prepared.Arithmetic
import Challenge.Modexp.Submission.Proofs.Fast.Monpro
import Challenge.Modexp.Submission.Proofs.Bytecode.WindowNibbleDefs
open CycleSubmission.SharedStackArgs
set_option warningAsError true
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option maxRecDepth 40000
set_option maxHeartbeats 8000000
namespace CycleSubmission.Execution
open EvmSemantics EvmSemantics.EVM YulEvmCompiler
open Challenge.Modexp.Submission.Proofs.Bytecode.WindowNibbleKernel
open Challenge.Modexp.Submission.Proofs.Fast
open Challenge.EvmProof.Word Challenge.EvmProof.Stepper
local notation "W" => UInt256
local notation "N" => UInt256.ofNat
open CycleSubmission.Prepared.Arithmetic
def pr8Newpart0Program : List Instr :=
  [
  .op (.Dup dA3),
   .push 2 1216,
   .op .MLOAD,
   .op .MULMOD,
   .op .ADD,
   .op (.Dup dA9),
   .op (.Dup dA12),
   .push 2 1248,
   .op .MLOAD]
def pr8Newpart0Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 : W) (rest : List W) : State :=
  let v0 : W := MachineState.readWord s.memory 1216
  let v1 : W := UInt256.mulMod v0 x3 x0
  let v2 : W := v1 + x1
  let v3 : W := MachineState.readWord s.memory 1248
  {s with pc := N 6957,memory := s.memory,stack := v3::x12::x10::v2::x2::x3::x4::x5::x6::x7::x8::x9::x10::x11::x12::x13::x14::x15::x16::rest}
theorem pr8Newpart0_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions pr8Newpart0Program {s with pc := N 6944,stack := x0::x1::x2::x3::x4::x5::x6::x7::x8::x9::x10::x11::x12::x13::x14::x15::x16::rest} =
      some (pr8Newpart0Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 19) : rest.length + j < 1024 := by omega
  have ha1216 : (1216 : W).toNat = 1216 := rfl
  have hf1216 := Monpro.activeWords_fix s 1216 32 (by decide) (by norm_num) hact
  have ha1248 : (1248 : W).toNat = 1248 := rfl
  have hf1248 := Monpro.activeWords_fix s 1248 32 (by decide) (by norm_num) hact
  simp [hz,hzn,pr8Newpart0Program,pr8Newpart0Model,runInstructions,runInstr,List.exchange,succ_ofNat_mod,ofNat_add_mod,Nat.add_assoc,State.activeWordsAfterUInt256,literal_eq_ofNat,capacity,ha1216,hf1216,ha1248,hf1248]
def pr8Newpart1Program : List Instr :=
  [
  .op .MULMOD,
   .op .ADD,
   .op (.Dup dA9),
   .op (.Dup dA14),
   .push 2 2720,
   .op .MLOAD,
   .op (.Dup dA2),
   .op (.Swap sA4)]
def pr8Newpart1Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 : W) (rest : List W) : State :=
  let v0 : W := UInt256.mulMod x0 x1 x2
  let v1 : W := v0 + x3
  let v2 : W := MachineState.readWord s.memory 2720
  {s with pc := N 6967,memory := s.memory,stack := x4::v2::x16::x12::v1::x12::x5::x6::x7::x8::x9::x10::x11::x12::x13::x14::x15::x16::x17::x18::rest}
theorem pr8Newpart1_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions pr8Newpart1Program {s with pc := N 6957,stack := x0::x1::x2::x3::x4::x5::x6::x7::x8::x9::x10::x11::x12::x13::x14::x15::x16::x17::x18::rest} =
      some (pr8Newpart1Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 20) : rest.length + j < 1024 := by omega
  have ha2720 : (2720 : W).toNat = 2720 := rfl
  have hf2720 := Monpro.activeWords_fix s 2720 32 (by decide) (by norm_num) hact
  simp [hz,hzn,pr8Newpart1Program,pr8Newpart1Model,runInstructions,runInstr,List.exchange,succ_ofNat_mod,ofNat_add_mod,Nat.add_assoc,State.activeWordsAfterUInt256,literal_eq_ofNat,capacity,ha2720,hf2720]
def pr8Newpart2Program : List Instr :=
  [
  .op .MUL,
   .op (.Dup dA15),
   .op .AND,
   .op (.Dup dA0),
   .push 2 1280,
   .op .MSTORE,
   .op .MULMOD,
   .op .ADD]
def pr8Newpart2Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 : W) (rest : List W) : State :=
  let v0 : W := x0 * x1
  let v1 : W := UInt256.land x16 v0
  let v2 : ByteArray := MachineState.writeBytes s.memory (Data.Bytes.natToBytesPadded v1.toNat 32) 1280
  let v3 : W := UInt256.mulMod v1 x2 x3
  let v4 : W := v3 + x4
  {s with pc := N 6977,memory := v2,stack := v4::x5::x6::x7::x8::x9::x10::x11::x12::x13::x14::x15::x16::x17::x18::x19::rest}
theorem pr8Newpart2_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions pr8Newpart2Program {s with pc := N 6967,stack := x0::x1::x2::x3::x4::x5::x6::x7::x8::x9::x10::x11::x12::x13::x14::x15::x16::x17::x18::x19::rest} =
      some (pr8Newpart2Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 21) : rest.length + j < 1024 := by omega
  have ha1280 : (1280 : W).toNat = 1280 := rfl
  have hf1280 := Monpro.activeWords_fix s 1280 32 (by decide) (by norm_num) hact
  simp [hz,hzn,pr8Newpart2Program,pr8Newpart2Model,runInstructions,runInstr,List.exchange,succ_ofNat_mod,ofNat_add_mod,Nat.add_assoc,State.activeWordsAfterUInt256,literal_eq_ofNat,capacity,ha1280,hf1280]
def pr8Newpart3Program : List Instr :=
  [
  .push 2 2048,
   .op .MULMOD,
   .push 2 2016,
   .op .MLOAD,
   .push 2 768,
   .op .MLOAD,
   .push 2 2048,
   .op .MLOAD]
def pr8Newpart3Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 : W) (rest : List W) : State :=
  let v0 : W := UInt256.mulMod (N 2048) x0 x1
  let v1 : W := MachineState.readWord s.memory 2016
  let v2 : W := MachineState.readWord s.memory 768
  let v3 : W := MachineState.readWord s.memory 2048
  {s with pc := N 6993,memory := s.memory,stack := v3::v2::v1::v0::x2::x3::x4::x5::x6::x7::x8::x9::x10::x11::x12::x13::x14::x15::rest}
theorem pr8Newpart3_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions pr8Newpart3Program {s with pc := N 6977,stack := x0::x1::x2::x3::x4::x5::x6::x7::x8::x9::x10::x11::x12::x13::x14::x15::rest} =
      some (pr8Newpart3Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 18) : rest.length + j < 1024 := by omega
  have ha768 : (768 : W).toNat = 768 := rfl
  have hf768 := Monpro.activeWords_fix s 768 32 (by decide) (by norm_num) hact
  have ha2016 : (2016 : W).toNat = 2016 := rfl
  have hf2016 := Monpro.activeWords_fix s 2016 32 (by decide) (by norm_num) hact
  have ha2048 : (2048 : W).toNat = 2048 := rfl
  have hf2048 := Monpro.activeWords_fix s 2048 32 (by decide) (by norm_num) hact
  simp [hz,hzn,pr8Newpart3Program,pr8Newpart3Model,runInstructions,runInstr,List.exchange,succ_ofNat_mod,ofNat_add_mod,Nat.add_assoc,State.activeWordsAfterUInt256,literal_eq_ofNat,capacity,ha768,hf768,ha2016,hf2016,ha2048,hf2048]
def pr8Newpart4Program : List Instr :=
  [
  .op (.Dup dA11),
   .op (.Dup dA1),
   .op (.Dup dA3),
   .op .MULMOD,
   .op (.Swap sA1),
   .op .MUL,
   .op (.Dup dA3),
   .op .ADD]
def pr8Newpart4Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 : W) (rest : List W) : State :=
  let v0 : W := UInt256.mulMod x1 x0 x11
  let v1 : W := x1 * x0
  let v2 : W := x3 + v1
  {s with pc := N 7001,memory := s.memory,stack := v2::v0::x2::x3::x4::x5::x6::x7::x8::x9::x10::x11::x12::x13::x14::x15::x16::x17::rest}
theorem pr8Newpart4_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions pr8Newpart4Program {s with pc := N 6993,stack := x0::x1::x2::x3::x4::x5::x6::x7::x8::x9::x10::x11::x12::x13::x14::x15::x16::x17::rest} =
      some (pr8Newpart4Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 21) : rest.length + j < 1024 := by omega
  simp [hz,hzn,pr8Newpart4Program,pr8Newpart4Model,runInstructions,runInstr,List.exchange,succ_ofNat_mod,ofNat_add_mod,Nat.add_assoc,State.activeWordsAfterUInt256,literal_eq_ofNat,capacity]
def pr8Newpart5Program : List Instr :=
  [
  .op (.Dup dA11),
   .op (.Dup dA3),
   .op (.Dup dA9),
   .op .MULMOD,
   .op (.Swap sA2),
   .op (.Dup dA8),
   .op .MUL,
   .op .ADD]
def pr8Newpart5Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 : W) (rest : List W) : State :=
  let v0 : W := UInt256.mulMod x7 x2 x11
  let v1 : W := x7 * x2
  let v2 : W := v1 + x0
  {s with pc := N 7009,memory := s.memory,stack := v2::x1::v0::x3::x4::x5::x6::x7::x8::x9::x10::x11::x12::x13::x14::x15::x16::x17::rest}
theorem pr8Newpart5_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions pr8Newpart5Program {s with pc := N 7001,stack := x0::x1::x2::x3::x4::x5::x6::x7::x8::x9::x10::x11::x12::x13::x14::x15::x16::x17::rest} =
      some (pr8Newpart5Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 21) : rest.length + j < 1024 := by omega
  simp [hz,hzn,pr8Newpart5Program,pr8Newpart5Model,runInstructions,runInstr,List.exchange,succ_ofNat_mod,ofNat_add_mod,Nat.add_assoc,State.activeWordsAfterUInt256,literal_eq_ofNat,capacity]
def pr8Newpart6Program : List Instr :=
  [
  .op (.Swap sA2),
   .op .ADD,
   .op .ADD,
   .op (.Swap sA1),
   .op (.Swap sA14),
   .op (.Swap sA1),
   .op (.Dup dA9),
   .op (.Dup dA7)]
def pr8Newpart6Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 : W) (rest : List W) : State :=
  let v0 : W := x3 + x1
  let v1 : W := v0 + x2
  {s with pc := N 7017,memory := s.memory,stack := x8::x11::v1::x0::x17::x5::x6::x7::x8::x9::x10::x11::x12::x13::x14::x15::x16::x4::rest}
theorem pr8Newpart6_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions pr8Newpart6Program {s with pc := N 7009,stack := x0::x1::x2::x3::x4::x5::x6::x7::x8::x9::x10::x11::x12::x13::x14::x15::x16::x17::rest} =
      some (pr8Newpart6Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 18) : rest.length + j < 1024 := by omega
  simp [hz,hzn,pr8Newpart6Program,pr8Newpart6Model,runInstructions,runInstr,List.exchange,succ_ofNat_mod,ofNat_add_mod,Nat.add_assoc,State.activeWordsAfterUInt256,literal_eq_ofNat,capacity]
def pr8Newpart7Program : List Instr :=
  [
  .push 2 1984,
   .op .MLOAD,
   .op (.Swap sA3),
   .op (.Dup dA1),
   .op (.Dup dA5),
   .op .MUL,
   .op .ADD,
   .op (.Swap sA3)]
def pr8Newpart7Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 : W) (rest : List W) : State :=
  let v0 : W := MachineState.readWord s.memory 1984
  let v1 : W := v0 * x0
  let v2 : W := v1 + x3
  {s with pc := N 7027,memory := s.memory,stack := v0::x0::x1::x2::v2::x4::x5::x6::x7::x8::x9::x10::x11::x12::x13::x14::x15::x16::x17::rest}
theorem pr8Newpart7_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions pr8Newpart7Program {s with pc := N 7017,stack := x0::x1::x2::x3::x4::x5::x6::x7::x8::x9::x10::x11::x12::x13::x14::x15::x16::x17::rest} =
      some (pr8Newpart7Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 21) : rest.length + j < 1024 := by omega
  have ha1984 : (1984 : W).toNat = 1984 := rfl
  have hf1984 := Monpro.activeWords_fix s 1984 32 (by decide) (by norm_num) hact
  simp [hz,hzn,pr8Newpart7Program,pr8Newpart7Model,runInstructions,runInstr,List.exchange,succ_ofNat_mod,ofNat_add_mod,Nat.add_assoc,State.activeWordsAfterUInt256,literal_eq_ofNat,capacity,ha1984,hf1984]
def pr8Newpart8Program : List Instr :=
  [
  .op .MULMOD,
   .op .ADD,
   .op (.Dup dA9),
   .push 1 32,
   .op .MLOAD,
   .push 2 1952,
   .op .MLOAD,
   .op (.Swap sA3)]
def pr8Newpart8Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 : W) (rest : List W) : State :=
  let v0 : W := UInt256.mulMod x0 x1 x2
  let v1 : W := v0 + x3
  let v2 : W := MachineState.readWord s.memory 32
  let v3 : W := MachineState.readWord s.memory 1952
  {s with pc := N 7038,memory := s.memory,stack := x4::v2::x12::v1::v3::x5::x6::x7::x8::x9::x10::x11::x12::x13::x14::x15::x16::x17::x18::rest}
theorem pr8Newpart8_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions pr8Newpart8Program {s with pc := N 7027,stack := x0::x1::x2::x3::x4::x5::x6::x7::x8::x9::x10::x11::x12::x13::x14::x15::x16::x17::x18::rest} =
      some (pr8Newpart8Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 19) : rest.length + j < 1024 := by omega
  have ha32 : (32 : W).toNat = 32 := rfl
  have hf32 := Monpro.activeWords_fix s 32 32 (by decide) (by norm_num) hact
  have ha1952 : (1952 : W).toNat = 1952 := rfl
  have hf1952 := Monpro.activeWords_fix s 1952 32 (by decide) (by norm_num) hact
  simp [hz,hzn,pr8Newpart8Program,pr8Newpart8Model,runInstructions,runInstr,List.exchange,succ_ofNat_mod,ofNat_add_mod,Nat.add_assoc,State.activeWordsAfterUInt256,literal_eq_ofNat,capacity,ha32,hf32,ha1952,hf1952]
def pr8Newpart9Program : List Instr :=
  [
  .op (.Dup dA1),
   .op (.Dup dA5),
   .op .MUL,
   .op .ADD,
   .op (.Swap sA3),
   .op .MULMOD,
   .op .ADD,
   .op (.Dup dA9)]
def pr8Newpart9Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 : W) (rest : List W) : State :=
  let v0 : W := x4 * x1
  let v1 : W := v0 + x0
  let v2 : W := UInt256.mulMod x4 x1 x2
  let v3 : W := v2 + x3
  {s with pc := N 7046,memory := s.memory,stack := x12::v3::v1::x5::x6::x7::x8::x9::x10::x11::x12::x13::x14::x15::x16::x17::x18::rest}
theorem pr8Newpart9_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions pr8Newpart9Program {s with pc := N 7038,stack := x0::x1::x2::x3::x4::x5::x6::x7::x8::x9::x10::x11::x12::x13::x14::x15::x16::x17::x18::rest} =
      some (pr8Newpart9Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 21) : rest.length + j < 1024 := by omega
  simp [hz,hzn,pr8Newpart9Program,pr8Newpart9Model,runInstructions,runInstr,List.exchange,succ_ofNat_mod,ofNat_add_mod,Nat.add_assoc,State.activeWordsAfterUInt256,literal_eq_ofNat,capacity]
def pr8Newpart10Program : List Instr :=
  [
  .push 1 64,
   .op .MLOAD,
   .push 2 1920,
   .op .MLOAD,
   .op (.Swap sA3),
   .op (.Dup dA1),
   .op (.Dup dA5),
   .op .MUL]
def pr8Newpart10Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 : W) (rest : List W) : State :=
  let v0 : W := MachineState.readWord s.memory 64
  let v1 : W := MachineState.readWord s.memory 1920
  let v2 : W := v1 * v0
  {s with pc := N 7057,memory := s.memory,stack := v2::x2::v0::x0::x1::v1::x3::x4::x5::x6::x7::x8::x9::x10::x11::x12::x13::x14::x15::x16::rest}
theorem pr8Newpart10_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions pr8Newpart10Program {s with pc := N 7046,stack := x0::x1::x2::x3::x4::x5::x6::x7::x8::x9::x10::x11::x12::x13::x14::x15::x16::rest} =
      some (pr8Newpart10Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 21) : rest.length + j < 1024 := by omega
  have ha64 : (64 : W).toNat = 64 := rfl
  have hf64 := Monpro.activeWords_fix s 64 32 (by decide) (by norm_num) hact
  have ha1920 : (1920 : W).toNat = 1920 := rfl
  have hf1920 := Monpro.activeWords_fix s 1920 32 (by decide) (by norm_num) hact
  simp [hz,hzn,pr8Newpart10Program,pr8Newpart10Model,runInstructions,runInstr,List.exchange,succ_ofNat_mod,ofNat_add_mod,Nat.add_assoc,State.activeWordsAfterUInt256,literal_eq_ofNat,capacity,ha64,hf64,ha1920,hf1920]
def pr8Newpart11Program : List Instr :=
  [
  .op .ADD,
   .op (.Swap sA3),
   .op .MULMOD,
   .op .ADD,
   .op (.Dup dA9),
   .push 1 96,
   .op .MLOAD,
   .push 2 1888,
   .op .MLOAD]
def pr8Newpart11Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 : W) (rest : List W) : State :=
  let v0 : W := x0 + x1
  let v1 : W := UInt256.mulMod x5 x2 x3
  let v2 : W := v1 + x4
  let v3 : W := MachineState.readWord s.memory 96
  let v4 : W := MachineState.readWord s.memory 1888
  {s with pc := N 7069,memory := s.memory,stack := v4::v3::x13::v2::v0::x6::x7::x8::x9::x10::x11::x12::x13::x14::x15::x16::x17::x18::x19::rest}
theorem pr8Newpart11_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions pr8Newpart11Program {s with pc := N 7057,stack := x0::x1::x2::x3::x4::x5::x6::x7::x8::x9::x10::x11::x12::x13::x14::x15::x16::x17::x18::x19::rest} =
      some (pr8Newpart11Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 20) : rest.length + j < 1024 := by omega
  have ha96 : (96 : W).toNat = 96 := rfl
  have hf96 := Monpro.activeWords_fix s 96 32 (by decide) (by norm_num) hact
  have ha1888 : (1888 : W).toNat = 1888 := rfl
  have hf1888 := Monpro.activeWords_fix s 1888 32 (by decide) (by norm_num) hact
  simp [hz,hzn,pr8Newpart11Program,pr8Newpart11Model,runInstructions,runInstr,List.exchange,succ_ofNat_mod,ofNat_add_mod,Nat.add_assoc,State.activeWordsAfterUInt256,literal_eq_ofNat,capacity,ha96,hf96,ha1888,hf1888]
def pr8Newpart12Program : List Instr :=
  [
  .op (.Swap sA3),
   .op (.Dup dA1)]
def pr8Newpart12Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 : W) (rest : List W) : State :=
  {s with pc := N 7071,memory := s.memory,stack := x1::x4::x1::x2::x3::x0::x5::x6::x7::x8::x9::x10::x11::x12::x13::x14::x15::x16::x17::x18::rest}
theorem pr8Newpart12_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions pr8Newpart12Program {s with pc := N 7069,stack := x0::x1::x2::x3::x4::x5::x6::x7::x8::x9::x10::x11::x12::x13::x14::x15::x16::x17::x18::rest} =
      some (pr8Newpart12Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 20) : rest.length + j < 1024 := by omega
  simp [hz,hzn,pr8Newpart12Program,pr8Newpart12Model,runInstructions,runInstr,List.exchange,succ_ofNat_mod,ofNat_add_mod,Nat.add_assoc,State.activeWordsAfterUInt256,literal_eq_ofNat,capacity]
def pr8NewProgram : List Instr :=
  [
  .op (.Dup dA3),
   .push 2 1216,
   .op .MLOAD,
   .op .MULMOD,
   .op .ADD,
   .op (.Dup dA9),
   .op (.Dup dA12),
   .push 2 1248,
   .op .MLOAD,
   .op .MULMOD,
   .op .ADD,
   .op (.Dup dA9),
   .op (.Dup dA14),
   .push 2 2720,
   .op .MLOAD,
   .op (.Dup dA2),
   .op (.Swap sA4),
   .op .MUL,
   .op (.Dup dA15),
   .op .AND,
   .op (.Dup dA0),
   .push 2 1280,
   .op .MSTORE,
   .op .MULMOD,
   .op .ADD,
   .push 2 2048,
   .op .MULMOD,
   .push 2 2016,
   .op .MLOAD,
   .push 2 768,
   .op .MLOAD,
   .push 2 2048,
   .op .MLOAD,
   .op (.Dup dA11),
   .op (.Dup dA1),
   .op (.Dup dA3),
   .op .MULMOD,
   .op (.Swap sA1),
   .op .MUL,
   .op (.Dup dA3),
   .op .ADD,
   .op (.Dup dA11),
   .op (.Dup dA3),
   .op (.Dup dA9),
   .op .MULMOD,
   .op (.Swap sA2),
   .op (.Dup dA8),
   .op .MUL,
   .op .ADD,
   .op (.Swap sA2),
   .op .ADD,
   .op .ADD,
   .op (.Swap sA1),
   .op (.Swap sA14),
   .op (.Swap sA1),
   .op (.Dup dA9),
   .op (.Dup dA7),
   .push 2 1984,
   .op .MLOAD,
   .op (.Swap sA3),
   .op (.Dup dA1),
   .op (.Dup dA5),
   .op .MUL,
   .op .ADD,
   .op (.Swap sA3),
   .op .MULMOD,
   .op .ADD,
   .op (.Dup dA9),
   .push 1 32,
   .op .MLOAD,
   .push 2 1952,
   .op .MLOAD,
   .op (.Swap sA3),
   .op (.Dup dA1),
   .op (.Dup dA5),
   .op .MUL,
   .op .ADD,
   .op (.Swap sA3),
   .op .MULMOD,
   .op .ADD,
   .op (.Dup dA9),
   .push 1 64,
   .op .MLOAD,
   .push 2 1920,
   .op .MLOAD,
   .op (.Swap sA3),
   .op (.Dup dA1),
   .op (.Dup dA5),
   .op .MUL,
   .op .ADD,
   .op (.Swap sA3),
   .op .MULMOD,
   .op .ADD,
   .op (.Dup dA9),
   .push 1 96,
   .op .MLOAD,
   .push 2 1888,
   .op .MLOAD,
   .op (.Swap sA3),
   .op (.Dup dA1)]
def pr8NewModel (s : State) (carry w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 : W) (rest : List W) : State :=
  let v0 : W := MachineState.readWord s.memory 1216
  let v1 : W := UInt256.mulMod v0 w2 carry
  let v2 : W := v1 + w0
  let v3 : W := MachineState.readWord s.memory 1248
  let v4 : W := UInt256.mulMod v3 w11 w9
  let v5 : W := v4 + v2
  let v6 : W := MachineState.readWord s.memory 2720
  let v7 : W := w1 * v6
  let v8 : W := UInt256.land w12 v7
  let v9 : ByteArray := MachineState.writeBytes s.memory (Data.Bytes.natToBytesPadded v8.toNat 32) 1280
  let v10 : W := UInt256.mulMod v8 w13 w9
  let v11 : W := v10 + v5
  let v12 : W := UInt256.mulMod (N 2048) v11 w9
  let v13 : W := MachineState.readWord v9 2016
  let v14 : W := MachineState.readWord v9 768
  let v15 : W := MachineState.readWord v9 2048
  let v16 : W := UInt256.mulMod v14 v15 w9
  let v17 : W := v14 * v15
  let v18 : W := v12 + v17
  let v19 : W := UInt256.mulMod w5 v13 w9
  let v20 : W := w5 * v13
  let v21 : W := v20 + v18
  let v22 : W := v12 + v16
  let v23 : W := v22 + v19
  let v24 : W := MachineState.readWord v9 1984
  let v25 : W := v24 * w6
  let v26 : W := v25 + v21
  let v27 : W := UInt256.mulMod v24 w6 w9
  let v28 : W := v27 + v23
  let v29 : W := MachineState.readWord v9 32
  let v30 : W := MachineState.readWord v9 1952
  let v31 : W := v30 * v29
  let v32 : W := v31 + v26
  let v33 : W := UInt256.mulMod v30 v29 w9
  let v34 : W := v33 + v28
  let v35 : W := MachineState.readWord v9 64
  let v36 : W := MachineState.readWord v9 1920
  let v37 : W := v36 * v35
  let v38 : W := v37 + v32
  let v39 : W := UInt256.mulMod v36 v35 w9
  let v40 : W := v39 + v34
  let v41 : W := MachineState.readWord v9 96
  let v42 : W := MachineState.readWord v9 1888
  {s with pc := N 7071,memory := v9,stack := v41::v38::v41::w9::v40::v42::w15::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w2::rest}
theorem pr8New_run (s : State) (carry w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions pr8NewProgram {s with pc := N 6944,stack := carry::w0::w1::w2::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::rest} =
      some (pr8NewModel s carry w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 rest) := by
  let v0 : W := MachineState.readWord s.memory 1216
  let v1 : W := UInt256.mulMod v0 w2 carry
  let v2 : W := v1 + w0
  let v3 : W := MachineState.readWord s.memory 1248
  let v4 : W := UInt256.mulMod v3 w11 w9
  let v5 : W := v4 + v2
  let v6 : W := MachineState.readWord s.memory 2720
  let v7 : W := w1 * v6
  let v8 : W := UInt256.land w12 v7
  let v9 : ByteArray := MachineState.writeBytes s.memory (Data.Bytes.natToBytesPadded v8.toNat 32) 1280
  let v10 : W := UInt256.mulMod v8 w13 w9
  let v11 : W := v10 + v5
  let v12 : W := UInt256.mulMod (N 2048) v11 w9
  let v13 : W := MachineState.readWord v9 2016
  let v14 : W := MachineState.readWord v9 768
  let v15 : W := MachineState.readWord v9 2048
  let v16 : W := UInt256.mulMod v14 v15 w9
  let v17 : W := v14 * v15
  let v18 : W := v12 + v17
  let v19 : W := UInt256.mulMod w5 v13 w9
  let v20 : W := w5 * v13
  let v21 : W := v20 + v18
  let v22 : W := v12 + v16
  let v23 : W := v22 + v19
  let v24 : W := MachineState.readWord v9 1984
  let v25 : W := v24 * w6
  let v26 : W := v25 + v21
  let v27 : W := UInt256.mulMod v24 w6 w9
  let v28 : W := v27 + v23
  let v29 : W := MachineState.readWord v9 32
  let v30 : W := MachineState.readWord v9 1952
  let v31 : W := v30 * v29
  let v32 : W := v31 + v26
  let v33 : W := UInt256.mulMod v30 v29 w9
  let v34 : W := v33 + v28
  let v35 : W := MachineState.readWord v9 64
  let v36 : W := MachineState.readWord v9 1920
  let v37 : W := v36 * v35
  let v38 : W := v37 + v32
  let v39 : W := UInt256.mulMod v36 v35 w9
  let v40 : W := v39 + v34
  let v41 : W := MachineState.readWord v9 96
  let v42 : W := MachineState.readWord v9 1888
  have h0 : runInstructions pr8Newpart0Program {s with pc := N 6944,memory := s.memory,stack := carry::w0::w1::w2::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::rest} = some {s with pc := N 6957,memory := s.memory,stack := v3::w11::w9::v2::w1::w2::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::rest} := by
    simpa only [pr8Newpart0Model,v0,v1,v2,v3] using pr8Newpart0_run (s) (carry) w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 rest hcap hact
  have h1 : runInstructions pr8Newpart1Program {s with pc := N 6957,memory := s.memory,stack := v3::w11::w9::v2::w1::w2::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::rest} = some {s with pc := N 6967,memory := s.memory,stack := w1::v6::w13::w9::v5::w9::w2::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::rest} := by
    simpa only [pr8Newpart1Model,v4,v5,v6] using pr8Newpart1_run (s) v3 w11 w9 v2 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 rest hcap hact
  have h2 : runInstructions pr8Newpart2Program {s with pc := N 6967,memory := s.memory,stack := w1::v6::w13::w9::v5::w9::w2::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::rest} = some {s with pc := N 6977,memory := v9,stack := v11::w9::w2::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::rest} := by
    simpa only [pr8Newpart2Model,v7,v8,v9,v10,v11] using pr8Newpart2_run (s) w1 v6 w13 w9 v5 w9 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 rest hcap hact
  have h3 : runInstructions pr8Newpart3Program {s with pc := N 6977,memory := v9,stack := v11::w9::w2::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::rest} = some {s with pc := N 6993,memory := v9,stack := v15::v14::v13::v12::w2::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::rest} := by
    simpa only [pr8Newpart3Model,v12,v13,v14,v15] using pr8Newpart3_run ({s with memory := v9}) v11 w9 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 rest hcap hact
  have h4 : runInstructions pr8Newpart4Program {s with pc := N 6993,memory := v9,stack := v15::v14::v13::v12::w2::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::rest} = some {s with pc := N 7001,memory := v9,stack := v18::v16::v13::v12::w2::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::rest} := by
    simpa only [pr8Newpart4Model,v16,v17,v18] using pr8Newpart4_run ({s with memory := v9}) v15 v14 v13 v12 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 rest hcap hact
  have h5 : runInstructions pr8Newpart5Program {s with pc := N 7001,memory := v9,stack := v18::v16::v13::v12::w2::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::rest} = some {s with pc := N 7009,memory := v9,stack := v21::v16::v19::v12::w2::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::rest} := by
    simpa only [pr8Newpart5Model,v19,v20,v21] using pr8Newpart5_run ({s with memory := v9}) v18 v16 v13 v12 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 rest hcap hact
  have h6 : runInstructions pr8Newpart6Program {s with pc := N 7009,memory := v9,stack := v21::v16::v19::v12::w2::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::rest} = some {s with pc := N 7017,memory := v9,stack := w6::w9::v23::v21::w15::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w2::rest} := by
    simpa only [pr8Newpart6Model,v22,v23] using pr8Newpart6_run ({s with memory := v9}) v21 v16 v19 v12 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 rest hcap hact
  have h7 : runInstructions pr8Newpart7Program {s with pc := N 7017,memory := v9,stack := w6::w9::v23::v21::w15::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w2::rest} = some {s with pc := N 7027,memory := v9,stack := v24::w6::w9::v23::v26::w15::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w2::rest} := by
    simpa only [pr8Newpart7Model,v24,v25,v26] using pr8Newpart7_run ({s with memory := v9}) w6 w9 v23 v21 w15 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w2 rest hcap hact
  have h8 : runInstructions pr8Newpart8Program {s with pc := N 7027,memory := v9,stack := v24::w6::w9::v23::v26::w15::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w2::rest} = some {s with pc := N 7038,memory := v9,stack := v26::v29::w9::v28::v30::w15::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w2::rest} := by
    simpa only [pr8Newpart8Model,v27,v28,v29,v30] using pr8Newpart8_run ({s with memory := v9}) v24 w6 w9 v23 v26 w15 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w2 rest hcap hact
  have h9 : runInstructions pr8Newpart9Program {s with pc := N 7038,memory := v9,stack := v26::v29::w9::v28::v30::w15::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w2::rest} = some {s with pc := N 7046,memory := v9,stack := w9::v34::v32::w15::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w2::rest} := by
    simpa only [pr8Newpart9Model,v31,v32,v33,v34] using pr8Newpart9_run ({s with memory := v9}) v26 v29 w9 v28 v30 w15 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w2 rest hcap hact
  have h10 : runInstructions pr8Newpart10Program {s with pc := N 7046,memory := v9,stack := w9::v34::v32::w15::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w2::rest} = some {s with pc := N 7057,memory := v9,stack := v37::v32::v35::w9::v34::v36::w15::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w2::rest} := by
    simpa only [pr8Newpart10Model,v35,v36,v37] using pr8Newpart10_run ({s with memory := v9}) w9 v34 v32 w15 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w2 rest hcap hact
  have h11 : runInstructions pr8Newpart11Program {s with pc := N 7057,memory := v9,stack := v37::v32::v35::w9::v34::v36::w15::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w2::rest} = some {s with pc := N 7069,memory := v9,stack := v42::v41::w9::v40::v38::w15::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w2::rest} := by
    simpa only [pr8Newpart11Model,v38,v39,v40,v41,v42] using pr8Newpart11_run ({s with memory := v9}) v37 v32 v35 w9 v34 v36 w15 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w2 rest hcap hact
  have h12 : runInstructions pr8Newpart12Program {s with pc := N 7069,memory := v9,stack := v42::v41::w9::v40::v38::w15::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w2::rest} = some {s with pc := N 7071,memory := v9,stack := v41::v38::v41::w9::v40::v42::w15::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w2::rest} := by
    simpa only [pr8Newpart12Model] using pr8Newpart12_run ({s with memory := v9}) v42 v41 w9 v40 v38 w15 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w2 rest hcap hact
  exact (runInstructions_append_some _ _ _ _ _ h0 (runInstructions_append_some _ _ _ _ _ h1 (runInstructions_append_some _ _ _ _ _ h2 (runInstructions_append_some _ _ _ _ _ h3 (runInstructions_append_some _ _ _ _ _ h4 (runInstructions_append_some _ _ _ _ _ h5 (runInstructions_append_some _ _ _ _ _ h6 (runInstructions_append_some _ _ _ _ _ h7 (runInstructions_append_some _ _ _ _ _ h8 (runInstructions_append_some _ _ _ _ _ h9 (runInstructions_append_some _ _ _ _ _ h10 (runInstructions_append_some _ _ _ _ _ h11 h12))))))))))))
#print axioms pr8New_run
def productColumn8Model (s : State) (carry w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 : W) (rest : List W) : State :=
  let v0 : W := MachineState.readWord s.memory 1216
  let v1 : W := UInt256.mulMod v0 w2 carry
  let v2 : W := v1 + w0
  let v3 : W := MachineState.readWord s.memory 1248
  let v4 : W := UInt256.mulMod v3 w11 w9
  let v5 : W := v4 + v2
  let v6 : W := MachineState.readWord s.memory 2720
  let v7 : W := w1 * v6
  let v8 : W := UInt256.land w12 v7
  let v9 : ByteArray := MachineState.writeBytes s.memory (Data.Bytes.natToBytesPadded v8.toNat 32) 1280
  let v10 : W := UInt256.mulMod v8 w13 w9
  let v11 : W := v10 + v5
  let v12 : W := UInt256.mulMod (N 2048) v11 w9
  let v13 : W := MachineState.readWord v9 768
  let v14 : W := MachineState.readWord v9 2048
  let v15 : W := v14 * v13
  let v16 : W := v15 + v12
  let v17 : W := UInt256.mulMod v14 v13 w9
  let v18 : W := v17 + v12
  let v19 : W := MachineState.readWord v9 2016
  let v20 : W := v19 * w5
  let v21 : W := v20 + v16
  let v22 : W := UInt256.mulMod v19 w5 w9
  let v23 : W := v22 + v18
  let v24 : W := MachineState.readWord v9 1984
  let v25 : W := v24 * w6
  let v26 : W := v25 + v21
  let v27 : W := UInt256.mulMod v24 w6 w9
  let v28 : W := v27 + v23
  let v29 : W := MachineState.readWord v9 32
  let v30 : W := MachineState.readWord v9 1952
  let v31 : W := v30 * v29
  let v32 : W := v31 + v26
  let v33 : W := UInt256.mulMod v30 v29 w9
  let v34 : W := v33 + v28
  let v35 : W := MachineState.readWord v9 64
  let v36 : W := MachineState.readWord v9 1920
  let v37 : W := v36 * v35
  let v38 : W := v37 + v32
  let v39 : W := UInt256.mulMod v36 v35 w9
  let v40 : W := v39 + v34
  let v41 : W := MachineState.readWord v9 96
  let v42 : W := MachineState.readWord v9 1888
  {s with pc := N 7071,memory := v9,stack := v41::v38::v41::w9::v40::v42::w15::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w2::rest}
def productColumn8Program : List Instr := pr8NewProgram
private theorem aux_shared0 (w9 : W) (z0 z1 : W) :
    (UInt256.mulMod z0 z1 w9) = (UInt256.mulMod z1 z0 w9) := by
  simp (disch := decide) only [addC,addA,addL,mulC,mmC,amC,andC,orC,xorC,eqC,read_disjoint,Challenge.EvmProof.Memory.readWord_writeWord]
private theorem aux_shared1 (z0 z1 : W) :
    (z0 * z1) = (z1 * z0) := by
  simp (disch := decide) only [addC,addA,addL,mulC,mmC,amC,andC,orC,xorC,eqC,read_disjoint,Challenge.EvmProof.Memory.readWord_writeWord]
private theorem aux_shared2 (z0 z1 : W) :
    (z0 + z1) = (z1 + z0) := by
  simp (disch := decide) only [addC,addA,addL,mulC,mmC,amC,andC,orC,xorC,eqC,read_disjoint,Challenge.EvmProof.Memory.readWord_writeWord]
private theorem aux_shared3 (w5 w9 : W) (z0 : W) :
    (UInt256.mulMod w5 z0 w9) = (UInt256.mulMod z0 w5 w9) := by
  simp (disch := decide) only [addC,addA,addL,mulC,mmC,amC,andC,orC,xorC,eqC,read_disjoint,Challenge.EvmProof.Memory.readWord_writeWord]
private theorem aux_shared4 (w5 : W) (z0 : W) :
    (w5 * z0) = (z0 * w5) := by
  simp (disch := decide) only [addC,addA,addL,mulC,mmC,amC,andC,orC,xorC,eqC,read_disjoint,Challenge.EvmProof.Memory.readWord_writeWord]
private theorem prepared_model_eq (s : State) (carry w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 : W) (rest : List W) :
    productColumn8Model s carry w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 rest = pr8NewModel s carry w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 rest := by
  let o0 : W := MachineState.readWord s.memory 1216
  let o1 : W := UInt256.mulMod o0 w2 carry
  let o2 : W := o1 + w0
  let o3 : W := MachineState.readWord s.memory 1248
  let o4 : W := UInt256.mulMod o3 w11 w9
  let o5 : W := o4 + o2
  let o6 : W := MachineState.readWord s.memory 2720
  let o7 : W := w1 * o6
  let o8 : W := UInt256.land w12 o7
  let o9 : ByteArray := MachineState.writeBytes s.memory (Data.Bytes.natToBytesPadded o8.toNat 32) 1280
  let o10 : W := UInt256.mulMod o8 w13 w9
  let o11 : W := o10 + o5
  let o12 : W := UInt256.mulMod (N 2048) o11 w9
  let o13 : W := MachineState.readWord o9 768
  let o14 : W := MachineState.readWord o9 2048
  let o15 : W := o14 * o13
  let o16 : W := o15 + o12
  let o17 : W := UInt256.mulMod o14 o13 w9
  let o18 : W := o17 + o12
  let o19 : W := MachineState.readWord o9 2016
  let o20 : W := o19 * w5
  let o21 : W := o20 + o16
  let o22 : W := UInt256.mulMod o19 w5 w9
  let o23 : W := o22 + o18
  let o24 : W := MachineState.readWord o9 1984
  let o25 : W := o24 * w6
  let o26 : W := o25 + o21
  let o27 : W := UInt256.mulMod o24 w6 w9
  let o28 : W := o27 + o23
  let o29 : W := MachineState.readWord o9 32
  let o30 : W := MachineState.readWord o9 1952
  let o31 : W := o30 * o29
  let o32 : W := o31 + o26
  let o33 : W := UInt256.mulMod o30 o29 w9
  let o34 : W := o33 + o28
  let o35 : W := MachineState.readWord o9 64
  let o36 : W := MachineState.readWord o9 1920
  let o37 : W := o36 * o35
  let o38 : W := o37 + o32
  let o39 : W := UInt256.mulMod o36 o35 w9
  let o40 : W := o39 + o34
  let o41 : W := MachineState.readWord o9 96
  let o42 : W := MachineState.readWord o9 1888
  let n0 : W := MachineState.readWord s.memory 1216
  let n1 : W := UInt256.mulMod n0 w2 carry
  let n2 : W := n1 + w0
  let n3 : W := MachineState.readWord s.memory 1248
  let n4 : W := UInt256.mulMod n3 w11 w9
  let n5 : W := n4 + n2
  let n6 : W := MachineState.readWord s.memory 2720
  let n7 : W := w1 * n6
  let n8 : W := UInt256.land w12 n7
  let n9 : ByteArray := MachineState.writeBytes s.memory (Data.Bytes.natToBytesPadded n8.toNat 32) 1280
  let n10 : W := UInt256.mulMod n8 w13 w9
  let n11 : W := n10 + n5
  let n12 : W := UInt256.mulMod (N 2048) n11 w9
  let n13 : W := MachineState.readWord n9 2016
  let n14 : W := MachineState.readWord n9 768
  let n15 : W := MachineState.readWord n9 2048
  let n16 : W := UInt256.mulMod n14 n15 w9
  let n17 : W := n14 * n15
  let n18 : W := n12 + n17
  let n19 : W := UInt256.mulMod w5 n13 w9
  let n20 : W := w5 * n13
  let n21 : W := n20 + n18
  let n22 : W := n12 + n16
  let n23 : W := n22 + n19
  let n24 : W := MachineState.readWord n9 1984
  let n25 : W := n24 * w6
  let n26 : W := n25 + n21
  let n27 : W := UInt256.mulMod n24 w6 w9
  let n28 : W := n27 + n23
  let n29 : W := MachineState.readWord n9 32
  let n30 : W := MachineState.readWord n9 1952
  let n31 : W := n30 * n29
  let n32 : W := n31 + n26
  let n33 : W := UInt256.mulMod n30 n29 w9
  let n34 : W := n33 + n28
  let n35 : W := MachineState.readWord n9 64
  let n36 : W := MachineState.readWord n9 1920
  let n37 : W := n36 * n35
  let n38 : W := n37 + n32
  let n39 : W := UInt256.mulMod n36 n35 w9
  let n40 : W := n39 + n34
  let n41 : W := MachineState.readWord n9 96
  let n42 : W := MachineState.readWord n9 1888
  have eq_n0 : n0 = o0 := by
    simp only [n0,o0]
  have eq_n1 : n1 = o1 := by
    simp only [n1,o1,eq_n0]
  have eq_n2 : n2 = o2 := by
    simp only [n2,o2,eq_n1]
  have eq_n3 : n3 = o3 := by
    simp only [n3,o3]
  have eq_n4 : n4 = o4 := by
    simp only [n4,o4,eq_n3]
  have eq_n5 : n5 = o5 := by
    simp only [n5,o5,eq_n4,eq_n2]
  have eq_n6 : n6 = o6 := by
    simp only [n6,o6]
  have eq_n7 : n7 = o7 := by
    simp only [n7,o7,eq_n6]
  have eq_n8 : n8 = o8 := by
    simp only [n8,o8,eq_n7]
  have eq_n9 : n9 = o9 := by
    simp only [n9,o9,eq_n8]
  have eq_n10 : n10 = o10 := by
    simp only [n10,o10,eq_n8]
  have eq_n11 : n11 = o11 := by
    simp only [n11,o11,eq_n10,eq_n5]
  have eq_n12 : n12 = o12 := by
    simp only [n12,o12,eq_n11]
  have eq_n13 : n13 = o19 := by
    simp only [n13,o19,eq_n9]
  have eq_n14 : n14 = o13 := by
    simp only [n14,o13,eq_n9]
  have eq_n15 : n15 = o14 := by
    simp only [n15,o14,eq_n9]
  have eq_n16 : n16 = o17 := by
    simpa only [n16,o17,eq_n14,eq_n15] using
      (aux_shared0 w9 o13 o14)
  have eq_n17 : n17 = o15 := by
    simpa only [n17,o15,eq_n14,eq_n15] using
      (aux_shared1  o13 o14)
  have eq_n18 : n18 = o16 := by
    simpa only [n18,o16,eq_n12,eq_n17] using
      (aux_shared2  o12 o15)
  have eq_n19 : n19 = o22 := by
    simpa only [n19,o22,eq_n13] using
      (aux_shared3 w5 w9 o19)
  have eq_n20 : n20 = o20 := by
    simpa only [n20,o20,eq_n13] using
      (aux_shared4 w5 o19)
  have eq_n21 : n21 = o21 := by
    simp only [n21,o21,eq_n20,eq_n18]
  have eq_n22 : n22 = o18 := by
    simpa only [n22,o18,eq_n12,eq_n16] using
      (aux_shared2  o12 o17)
  have eq_n23 : n23 = o23 := by
    simpa only [n23,o23,eq_n22,eq_n19] using
      (aux_shared2  o18 o22)
  have eq_n24 : n24 = o24 := by
    simp only [n24,o24,eq_n9]
  have eq_n25 : n25 = o25 := by
    simp only [n25,o25,eq_n24]
  have eq_n26 : n26 = o26 := by
    simp only [n26,o26,eq_n25,eq_n21]
  have eq_n27 : n27 = o27 := by
    simp only [n27,o27,eq_n24]
  have eq_n28 : n28 = o28 := by
    simp only [n28,o28,eq_n27,eq_n23]
  have eq_n29 : n29 = o29 := by
    simp only [n29,o29,eq_n9]
  have eq_n30 : n30 = o30 := by
    simp only [n30,o30,eq_n9]
  have eq_n31 : n31 = o31 := by
    simp only [n31,o31,eq_n30,eq_n29]
  have eq_n32 : n32 = o32 := by
    simp only [n32,o32,eq_n31,eq_n26]
  have eq_n33 : n33 = o33 := by
    simp only [n33,o33,eq_n30,eq_n29]
  have eq_n34 : n34 = o34 := by
    simp only [n34,o34,eq_n33,eq_n28]
  have eq_n35 : n35 = o35 := by
    simp only [n35,o35,eq_n9]
  have eq_n36 : n36 = o36 := by
    simp only [n36,o36,eq_n9]
  have eq_n37 : n37 = o37 := by
    simp only [n37,o37,eq_n36,eq_n35]
  have eq_n38 : n38 = o38 := by
    simp only [n38,o38,eq_n37,eq_n32]
  have eq_n39 : n39 = o39 := by
    simp only [n39,o39,eq_n36,eq_n35]
  have eq_n40 : n40 = o40 := by
    simp only [n40,o40,eq_n39,eq_n34]
  have eq_n41 : n41 = o41 := by
    simp only [n41,o41,eq_n9]
  have eq_n42 : n42 = o42 := by
    simp only [n42,o42,eq_n9]
  change {s with pc := N 7071,memory := o9,stack := o41::o38::o41::w9::o40::o42::w15::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w2::rest} =
    {s with pc := N 7071,memory := n9,stack := n41::n38::n41::w9::n40::n42::w15::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w2::rest}
  simp only [eq_n0,eq_n1,eq_n2,eq_n3,eq_n4,eq_n5,eq_n6,eq_n7,eq_n8,eq_n9,eq_n10,eq_n11,eq_n12,eq_n13,eq_n14,eq_n15,eq_n16,eq_n17,eq_n18,eq_n19,eq_n20,eq_n21,eq_n22,eq_n23,eq_n24,eq_n25,eq_n26,eq_n27,eq_n28,eq_n29,eq_n30,eq_n31,eq_n32,eq_n33,eq_n34,eq_n35,eq_n36,eq_n37,eq_n38,eq_n39,eq_n40,eq_n41,eq_n42]
theorem productColumn8_run (s : State) (carry w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions productColumn8Program {s with pc := N 6944,stack := carry::w0::w1::w2::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::rest} =
      some (productColumn8Model s carry w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 rest) := by
  exact (pr8New_run s carry w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 rest hcap hact).trans
    (congrArg some (prepared_model_eq s carry w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 rest).symm)
#print axioms productColumn8_run
end CycleSubmission.Execution
