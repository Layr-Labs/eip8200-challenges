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
def pr14Newpart0Program : List Instr :=
  [
  .op (.Swap sA0),
   .op (.Dup dA12),
   .op .AND,
   .op (.Dup dA0),
   .op (.Swap sA1),
   .op .SUB,
   .op (.Dup dA9),
   .op .ADD]
def pr14Newpart0Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 : W) (rest : List W) : State :=
  let v0 : W := UInt256.land x12 x1
  let v1 : W := x0 - v0
  let v2 : W := x9 + v1
  {s with pc := N 7703,memory := s.memory,stack := v2::v0::x2::x3::x4::x5::x6::x7::x8::x9::x10::x11::x12::x13::x14::x15::rest}
theorem pr14Newpart0_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions pr14Newpart0Program {s with pc := N 7695,stack := x0::x1::x2::x3::x4::x5::x6::x7::x8::x9::x10::x11::x12::x13::x14::x15::rest} =
      some (pr14Newpart0Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 17) : rest.length + j < 1024 := by omega
  simp [hz,hzn,pr14Newpart0Program,pr14Newpart0Model,runInstructions,runInstr,List.exchange,succ_ofNat_mod,ofNat_add_mod,Nat.add_assoc,State.activeWordsAfterUInt256,literal_eq_ofNat,capacity]
def pr14Newpart1Program : List Instr :=
  [
  .push 2 2048,
   .op (.Dup dA10),
   .op (.Swap sA1),
   .op .MULMOD,
   .op (.Dup dA9),
   .push 1 32,
   .op .MLOAD,
   .op (.Dup dA2)]
def pr14Newpart1Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 : W) (rest : List W) : State :=
  let v0 : W := UInt256.mulMod x0 (N 2048) x9
  let v1 : W := MachineState.readWord s.memory 32
  {s with pc := N 7714,memory := s.memory,stack := v0::v1::x9::v0::x1::x2::x3::x4::x5::x6::x7::x8::x9::x10::x11::x12::x13::x14::x15::rest}
theorem pr14Newpart1_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions pr14Newpart1Program {s with pc := N 7703,stack := x0::x1::x2::x3::x4::x5::x6::x7::x8::x9::x10::x11::x12::x13::x14::x15::rest} =
      some (pr14Newpart1Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 19) : rest.length + j < 1024 := by omega
  have ha32 : (32 : W).toNat = 32 := rfl
  have hf32 := Monpro.activeWords_fix s 32 32 (by decide) (by norm_num) hact
  simp [hz,hzn,pr14Newpart1Program,pr14Newpart1Model,runInstructions,runInstr,List.exchange,succ_ofNat_mod,ofNat_add_mod,Nat.add_assoc,State.activeWordsAfterUInt256,literal_eq_ofNat,capacity,ha32,hf32]
def pr14Newpart2Program : List Instr :=
  [
  .push 2 2048,
   .op .MLOAD,
   .op (.Swap sA4),
   .push 2 800,
   .op .MSTORE,
   .op (.Dup dA1),
   .op (.Dup dA5),
   .op .MUL]
def pr14Newpart2Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 : W) (rest : List W) : State :=
  let v0 : W := MachineState.readWord s.memory 2048
  let v1 : ByteArray := MachineState.writeBytes s.memory (Data.Bytes.natToBytesPadded x4.toNat 32) 800
  let v2 : W := v0 * x1
  {s with pc := N 7726,memory := v1,stack := v2::x0::x1::x2::x3::v0::x5::x6::x7::x8::x9::x10::x11::x12::x13::x14::x15::x16::x17::x18::rest}
theorem pr14Newpart2_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions pr14Newpart2Program {s with pc := N 7714,stack := x0::x1::x2::x3::x4::x5::x6::x7::x8::x9::x10::x11::x12::x13::x14::x15::x16::x17::x18::rest} =
      some (pr14Newpart2Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 21) : rest.length + j < 1024 := by omega
  have ha800 : (800 : W).toNat = 800 := rfl
  have hf800 := Monpro.activeWords_fix s 800 32 (by decide) (by norm_num) hact
  have ha2048 : (2048 : W).toNat = 2048 := rfl
  have hf2048 := Monpro.activeWords_fix s 2048 32 (by decide) (by norm_num) hact
  simp [hz,hzn,pr14Newpart2Program,pr14Newpart2Model,runInstructions,runInstr,List.exchange,succ_ofNat_mod,ofNat_add_mod,Nat.add_assoc,State.activeWordsAfterUInt256,literal_eq_ofNat,capacity,ha800,hf800,ha2048,hf2048]
def pr14Newpart3Program : List Instr :=
  [
  .op .ADD,
   .op (.Swap sA3),
   .op .MULMOD,
   .op .ADD,
   .op (.Dup dA9),
   .push 1 64,
   .op .MLOAD,
   .push 2 2016,
   .op .MLOAD]
def pr14Newpart3Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 : W) (rest : List W) : State :=
  let v0 : W := x0 + x1
  let v1 : W := UInt256.mulMod x5 x2 x3
  let v2 : W := v1 + x4
  let v3 : W := MachineState.readWord s.memory 64
  let v4 : W := MachineState.readWord s.memory 2016
  {s with pc := N 7738,memory := s.memory,stack := v4::v3::x13::v2::v0::x6::x7::x8::x9::x10::x11::x12::x13::x14::x15::x16::x17::x18::x19::rest}
theorem pr14Newpart3_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions pr14Newpart3Program {s with pc := N 7726,stack := x0::x1::x2::x3::x4::x5::x6::x7::x8::x9::x10::x11::x12::x13::x14::x15::x16::x17::x18::x19::rest} =
      some (pr14Newpart3Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 20) : rest.length + j < 1024 := by omega
  have ha64 : (64 : W).toNat = 64 := rfl
  have hf64 := Monpro.activeWords_fix s 64 32 (by decide) (by norm_num) hact
  have ha2016 : (2016 : W).toNat = 2016 := rfl
  have hf2016 := Monpro.activeWords_fix s 2016 32 (by decide) (by norm_num) hact
  simp [hz,hzn,pr14Newpart3Program,pr14Newpart3Model,runInstructions,runInstr,List.exchange,succ_ofNat_mod,ofNat_add_mod,Nat.add_assoc,State.activeWordsAfterUInt256,literal_eq_ofNat,capacity,ha64,hf64,ha2016,hf2016]
def pr14Newpart4Program : List Instr :=
  [
  .op (.Swap sA3),
   .op (.Dup dA1),
   .op (.Dup dA5),
   .op .MUL,
   .op .ADD,
   .op (.Swap sA3),
   .op .MULMOD,
   .op .ADD]
def pr14Newpart4Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 : W) (rest : List W) : State :=
  let v0 : W := x0 * x1
  let v1 : W := v0 + x4
  let v2 : W := UInt256.mulMod x0 x1 x2
  let v3 : W := v2 + x3
  {s with pc := N 7746,memory := s.memory,stack := v3::v1::x5::x6::x7::x8::x9::x10::x11::x12::x13::x14::x15::x16::x17::x18::rest}
theorem pr14Newpart4_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions pr14Newpart4Program {s with pc := N 7738,stack := x0::x1::x2::x3::x4::x5::x6::x7::x8::x9::x10::x11::x12::x13::x14::x15::x16::x17::x18::rest} =
      some (pr14Newpart4Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 21) : rest.length + j < 1024 := by omega
  simp [hz,hzn,pr14Newpart4Program,pr14Newpart4Model,runInstructions,runInstr,List.exchange,succ_ofNat_mod,ofNat_add_mod,Nat.add_assoc,State.activeWordsAfterUInt256,literal_eq_ofNat,capacity]
def pr14Newpart5Program : List Instr :=
  [
  .op (.Dup dA9),
   .push 1 96,
   .op .MLOAD,
   .push 2 1984,
   .op .MLOAD,
   .op (.Swap sA3),
   .op (.Dup dA1),
   .op (.Dup dA5)]
def pr14Newpart5Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 : W) (rest : List W) : State :=
  let v0 : W := MachineState.readWord s.memory 96
  let v1 : W := MachineState.readWord s.memory 1984
  {s with pc := N 7757,memory := s.memory,stack := v1::v0::x1::v0::x9::x0::v1::x2::x3::x4::x5::x6::x7::x8::x9::x10::x11::x12::x13::x14::x15::rest}
theorem pr14Newpart5_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions pr14Newpart5Program {s with pc := N 7746,stack := x0::x1::x2::x3::x4::x5::x6::x7::x8::x9::x10::x11::x12::x13::x14::x15::rest} =
      some (pr14Newpart5Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 21) : rest.length + j < 1024 := by omega
  have ha96 : (96 : W).toNat = 96 := rfl
  have hf96 := Monpro.activeWords_fix s 96 32 (by decide) (by norm_num) hact
  have ha1984 : (1984 : W).toNat = 1984 := rfl
  have hf1984 := Monpro.activeWords_fix s 1984 32 (by decide) (by norm_num) hact
  simp [hz,hzn,pr14Newpart5Program,pr14Newpart5Model,runInstructions,runInstr,List.exchange,succ_ofNat_mod,ofNat_add_mod,Nat.add_assoc,State.activeWordsAfterUInt256,literal_eq_ofNat,capacity,ha96,hf96,ha1984,hf1984]
def pr14Newpart6Program : List Instr :=
  [
  .op .MUL,
   .op .ADD,
   .op (.Swap sA3),
   .op .MULMOD,
   .op .ADD,
   .op (.Dup dA9),
   .push 1 128,
   .op .MLOAD]
def pr14Newpart6Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 : W) (rest : List W) : State :=
  let v0 : W := x0 * x1
  let v1 : W := v0 + x2
  let v2 : W := UInt256.mulMod x6 x3 x4
  let v3 : W := v2 + x5
  let v4 : W := MachineState.readWord s.memory 128
  {s with pc := N 7766,memory := s.memory,stack := v4::x14::v3::v1::x7::x8::x9::x10::x11::x12::x13::x14::x15::x16::x17::x18::x19::x20::rest}
theorem pr14Newpart6_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions pr14Newpart6Program {s with pc := N 7757,stack := x0::x1::x2::x3::x4::x5::x6::x7::x8::x9::x10::x11::x12::x13::x14::x15::x16::x17::x18::x19::x20::rest} =
      some (pr14Newpart6Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 21) : rest.length + j < 1024 := by omega
  have ha128 : (128 : W).toNat = 128 := rfl
  have hf128 := Monpro.activeWords_fix s 128 32 (by decide) (by norm_num) hact
  simp [hz,hzn,pr14Newpart6Program,pr14Newpart6Model,runInstructions,runInstr,List.exchange,succ_ofNat_mod,ofNat_add_mod,Nat.add_assoc,State.activeWordsAfterUInt256,literal_eq_ofNat,capacity,ha128,hf128]
def pr14Newpart7Program : List Instr :=
  [
  .push 2 1952,
   .op .MLOAD,
   .op (.Swap sA3),
   .op (.Dup dA1),
   .op (.Dup dA5),
   .op .MUL,
   .op .ADD,
   .op (.Swap sA3)]
def pr14Newpart7Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 : W) (rest : List W) : State :=
  let v0 : W := MachineState.readWord s.memory 1952
  let v1 : W := v0 * x0
  let v2 : W := v1 + x3
  {s with pc := N 7776,memory := s.memory,stack := v0::x0::x1::x2::v2::x4::x5::x6::x7::x8::x9::x10::x11::x12::x13::x14::x15::x16::x17::rest}
theorem pr14Newpart7_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions pr14Newpart7Program {s with pc := N 7766,stack := x0::x1::x2::x3::x4::x5::x6::x7::x8::x9::x10::x11::x12::x13::x14::x15::x16::x17::rest} =
      some (pr14Newpart7Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 21) : rest.length + j < 1024 := by omega
  have ha1952 : (1952 : W).toNat = 1952 := rfl
  have hf1952 := Monpro.activeWords_fix s 1952 32 (by decide) (by norm_num) hact
  simp [hz,hzn,pr14Newpart7Program,pr14Newpart7Model,runInstructions,runInstr,List.exchange,succ_ofNat_mod,ofNat_add_mod,Nat.add_assoc,State.activeWordsAfterUInt256,literal_eq_ofNat,capacity,ha1952,hf1952]
def pr14Newpart8Program : List Instr :=
  [
  .op .MULMOD,
   .op .ADD,
   .push 1 160,
   .op .MLOAD,
   .push 2 1920,
   .op .MLOAD,
   .op (.Dup dA11),
   .op (.Dup dA1)]
def pr14Newpart8Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 : W) (rest : List W) : State :=
  let v0 : W := UInt256.mulMod x0 x1 x2
  let v1 : W := v0 + x3
  let v2 : W := MachineState.readWord s.memory 160
  let v3 : W := MachineState.readWord s.memory 1920
  {s with pc := N 7787,memory := s.memory,stack := v3::x12::v3::v2::v1::x4::x5::x6::x7::x8::x9::x10::x11::x12::x13::x14::x15::x16::x17::x18::rest}
theorem pr14Newpart8_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions pr14Newpart8Program {s with pc := N 7776,stack := x0::x1::x2::x3::x4::x5::x6::x7::x8::x9::x10::x11::x12::x13::x14::x15::x16::x17::x18::rest} =
      some (pr14Newpart8Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 20) : rest.length + j < 1024 := by omega
  have ha160 : (160 : W).toNat = 160 := rfl
  have hf160 := Monpro.activeWords_fix s 160 32 (by decide) (by norm_num) hact
  have ha1920 : (1920 : W).toNat = 1920 := rfl
  have hf1920 := Monpro.activeWords_fix s 1920 32 (by decide) (by norm_num) hact
  simp [hz,hzn,pr14Newpart8Program,pr14Newpart8Model,runInstructions,runInstr,List.exchange,succ_ofNat_mod,ofNat_add_mod,Nat.add_assoc,State.activeWordsAfterUInt256,literal_eq_ofNat,capacity,ha160,hf160,ha1920,hf1920]
def pr14Newpart9Program : List Instr :=
  [
  .op (.Dup dA3),
   .op .MULMOD,
   .op (.Swap sA1),
   .op .MUL,
   .push 2 1888,
   .op .MLOAD,
   .op (.Swap sA3),
   .op .ADD]
def pr14Newpart9Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 : W) (rest : List W) : State :=
  let v0 : W := UInt256.mulMod x3 x0 x1
  let v1 : W := x3 * x2
  let v2 : W := MachineState.readWord s.memory 1888
  let v3 : W := x5 + v1
  {s with pc := N 7797,memory := s.memory,stack := v3::v0::x4::v2::x6::x7::x8::x9::x10::x11::x12::x13::x14::x15::x16::x17::x18::x19::rest}
theorem pr14Newpart9_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions pr14Newpart9Program {s with pc := N 7787,stack := x0::x1::x2::x3::x4::x5::x6::x7::x8::x9::x10::x11::x12::x13::x14::x15::x16::x17::x18::x19::rest} =
      some (pr14Newpart9Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 21) : rest.length + j < 1024 := by omega
  have ha1888 : (1888 : W).toNat = 1888 := rfl
  have hf1888 := Monpro.activeWords_fix s 1888 32 (by decide) (by norm_num) hact
  simp [hz,hzn,pr14Newpart9Program,pr14Newpart9Model,runInstructions,runInstr,List.exchange,succ_ofNat_mod,ofNat_add_mod,Nat.add_assoc,State.activeWordsAfterUInt256,literal_eq_ofNat,capacity,ha1888,hf1888]
def pr14Newpart10Program : List Instr :=
  [
  .op (.Swap sA1),
   .op .ADD,
   .op (.Dup dA10),
   .op (.Dup dA3),
   .op (.Dup dA5),
   .op .MULMOD,
   .op .ADD,
   .op (.Swap sA1)]
def pr14Newpart10Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 : W) (rest : List W) : State :=
  let v0 : W := x2 + x1
  let v1 : W := UInt256.mulMod x4 x3 x11
  let v2 : W := v1 + v0
  {s with pc := N 7805,memory := s.memory,stack := x3::x0::v2::x4::x5::x6::x7::x8::x9::x10::x11::x12::x13::x14::x15::x16::x17::rest}
theorem pr14Newpart10_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions pr14Newpart10Program {s with pc := N 7797,stack := x0::x1::x2::x3::x4::x5::x6::x7::x8::x9::x10::x11::x12::x13::x14::x15::x16::x17::rest} =
      some (pr14Newpart10Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 20) : rest.length + j < 1024 := by omega
  simp [hz,hzn,pr14Newpart10Program,pr14Newpart10Model,runInstructions,runInstr,List.exchange,succ_ofNat_mod,ofNat_add_mod,Nat.add_assoc,State.activeWordsAfterUInt256,literal_eq_ofNat,capacity]
def pr14Newpart11Program : List Instr :=
  [
  .op (.Dup dA3),
   .op .MUL,
   .op .ADD,
   .push 0 0,
   .op .MLOAD,
   .op (.Dup dA11),
   .op .MUL,
   .op .ADD]
def pr14Newpart11Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 : W) (rest : List W) : State :=
  let v0 : W := x3 * x0
  let v1 : W := v0 + x1
  let v2 : W := MachineState.readWord s.memory 0
  let v3 : W := x11 * v2
  let v4 : W := v3 + v1
  {s with pc := N 7813,memory := s.memory,stack := v4::x2::x3::x4::x5::x6::x7::x8::x9::x10::x11::x12::x13::x14::x15::x16::rest}
theorem pr14Newpart11_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions pr14Newpart11Program {s with pc := N 7805,stack := x0::x1::x2::x3::x4::x5::x6::x7::x8::x9::x10::x11::x12::x13::x14::x15::x16::rest} =
      some (pr14Newpart11Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 18) : rest.length + j < 1024 := by omega
  have ha0 : (0 : W).toNat = 0 := rfl
  have hf0 := Monpro.activeWords_fix s 0 32 (by decide) (by norm_num) hact
  simp [hz,hzn,pr14Newpart11Program,pr14Newpart11Model,runInstructions,runInstr,List.exchange,succ_ofNat_mod,ofNat_add_mod,Nat.add_assoc,State.activeWordsAfterUInt256,literal_eq_ofNat,capacity,ha0,hf0]
def pr14Newpart12Program : List Instr :=
  [
  .push 1 224,
   .op .MLOAD,
   .op (.Dup dA9),
   .op .MUL,
   .op .ADD,
   .op (.Dup dA6),
   .op (.Dup dA4),
   .op .MUL]
def pr14Newpart12Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 : W) (rest : List W) : State :=
  let v0 : W := MachineState.readWord s.memory 224
  let v1 : W := x8 * v0
  let v2 : W := v1 + x0
  let v3 : W := x3 * x6
  {s with pc := N 7822,memory := s.memory,stack := v3::v2::x1::x2::x3::x4::x5::x6::x7::x8::x9::x10::x11::x12::x13::x14::x15::rest}
theorem pr14Newpart12_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions pr14Newpart12Program {s with pc := N 7813,stack := x0::x1::x2::x3::x4::x5::x6::x7::x8::x9::x10::x11::x12::x13::x14::x15::rest} =
      some (pr14Newpart12Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 18) : rest.length + j < 1024 := by omega
  have ha224 : (224 : W).toNat = 224 := rfl
  have hf224 := Monpro.activeWords_fix s 224 32 (by decide) (by norm_num) hact
  simp [hz,hzn,pr14Newpart12Program,pr14Newpart12Model,runInstructions,runInstr,List.exchange,succ_ofNat_mod,ofNat_add_mod,Nat.add_assoc,State.activeWordsAfterUInt256,literal_eq_ofNat,capacity,ha224,hf224]
def pr14Newpart13Program : List Instr :=
  [
  .op .ADD,
   .op (.Dup dA5),
   .op (.Dup dA8),
   .op .MUL,
   .op .ADD,
   .op (.Dup dA11)]
def pr14Newpart13Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 : W) (rest : List W) : State :=
  let v0 : W := x0 + x1
  let v1 : W := x8 * x6
  let v2 : W := v1 + v0
  {s with pc := N 7828,memory := s.memory,stack := x12::v2::x2::x3::x4::x5::x6::x7::x8::x9::x10::x11::x12::x13::x14::x15::x16::rest}
theorem pr14Newpart13_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions pr14Newpart13Program {s with pc := N 7822,stack := x0::x1::x2::x3::x4::x5::x6::x7::x8::x9::x10::x11::x12::x13::x14::x15::x16::rest} =
      some (pr14Newpart13Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 18) : rest.length + j < 1024 := by omega
  simp [hz,hzn,pr14Newpart13Program,pr14Newpart13Model,runInstructions,runInstr,List.exchange,succ_ofNat_mod,ofNat_add_mod,Nat.add_assoc,State.activeWordsAfterUInt256,literal_eq_ofNat,capacity]
def pr14NewProgram : List Instr :=
  [
  .op (.Swap sA0),
   .op (.Dup dA12),
   .op .AND,
   .op (.Dup dA0),
   .op (.Swap sA1),
   .op .SUB,
   .op (.Dup dA9),
   .op .ADD,
   .push 2 2048,
   .op (.Dup dA10),
   .op (.Swap sA1),
   .op .MULMOD,
   .op (.Dup dA9),
   .push 1 32,
   .op .MLOAD,
   .op (.Dup dA2),
   .push 2 2048,
   .op .MLOAD,
   .op (.Swap sA4),
   .push 2 800,
   .op .MSTORE,
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
   .push 2 2016,
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
   .push 1 128,
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
   .push 1 160,
   .op .MLOAD,
   .push 2 1920,
   .op .MLOAD,
   .op (.Dup dA11),
   .op (.Dup dA1),
   .op (.Dup dA3),
   .op .MULMOD,
   .op (.Swap sA1),
   .op .MUL,
   .push 2 1888,
   .op .MLOAD,
   .op (.Swap sA3),
   .op .ADD,
   .op (.Swap sA1),
   .op .ADD,
   .op (.Dup dA10),
   .op (.Dup dA3),
   .op (.Dup dA5),
   .op .MULMOD,
   .op .ADD,
   .op (.Swap sA1),
   .op (.Dup dA3),
   .op .MUL,
   .op .ADD,
   .push 0 0,
   .op .MLOAD,
   .op (.Dup dA11),
   .op .MUL,
   .op .ADD,
   .push 1 224,
   .op .MLOAD,
   .op (.Dup dA9),
   .op .MUL,
   .op .ADD,
   .op (.Dup dA6),
   .op (.Dup dA4),
   .op .MUL,
   .op .ADD,
   .op (.Dup dA5),
   .op (.Dup dA8),
   .op .MUL,
   .op .ADD,
   .op (.Dup dA11)]
def pr14NewModel (s : State) (carry w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 : W) (rest : List W) : State :=
  let v0 : W := UInt256.land w11 w0
  let v1 : W := carry - v0
  let v2 : W := w8 + v1
  let v3 : W := UInt256.mulMod v2 (N 2048) w8
  let v4 : W := MachineState.readWord s.memory 32
  let v5 : W := MachineState.readWord s.memory 2048
  let v6 : ByteArray := MachineState.writeBytes s.memory (Data.Bytes.natToBytesPadded v0.toNat 32) 800
  let v7 : W := v5 * v4
  let v8 : W := v7 + v3
  let v9 : W := UInt256.mulMod v5 v4 w8
  let v10 : W := v9 + v3
  let v11 : W := MachineState.readWord v6 64
  let v12 : W := MachineState.readWord v6 2016
  let v13 : W := v12 * v11
  let v14 : W := v13 + v8
  let v15 : W := UInt256.mulMod v12 v11 w8
  let v16 : W := v15 + v10
  let v17 : W := MachineState.readWord v6 96
  let v18 : W := MachineState.readWord v6 1984
  let v19 : W := v18 * v17
  let v20 : W := v19 + v14
  let v21 : W := UInt256.mulMod v18 v17 w8
  let v22 : W := v21 + v16
  let v23 : W := MachineState.readWord v6 128
  let v24 : W := MachineState.readWord v6 1952
  let v25 : W := v24 * v23
  let v26 : W := v25 + v20
  let v27 : W := UInt256.mulMod v24 v23 w8
  let v28 : W := v27 + v22
  let v29 : W := MachineState.readWord v6 160
  let v30 : W := MachineState.readWord v6 1920
  let v31 : W := UInt256.mulMod v29 v30 w8
  let v32 : W := v29 * v30
  let v33 : W := MachineState.readWord v6 1888
  let v34 : W := v26 + v32
  let v35 : W := v28 + v31
  let v36 : W := UInt256.mulMod w1 v33 w8
  let v37 : W := v36 + v35
  let v38 : W := w1 * v33
  let v39 : W := v38 + v34
  let v40 : W := MachineState.readWord v6 0
  let v41 : W := w9 * v40
  let v42 : W := v41 + v39
  let v43 : W := MachineState.readWord v6 224
  let v44 : W := w7 * v43
  let v45 : W := v44 + v42
  let v46 : W := w2 * w5
  let v47 : W := v46 + v45
  let v48 : W := w6 * w4
  let v49 : W := v48 + v47
  {s with pc := N 7828,memory := v6,stack := w10::v49::v37::w1::w2::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::rest}
theorem pr14New_run (s : State) (carry w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions pr14NewProgram {s with pc := N 7695,stack := carry::w0::w1::w2::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::rest} =
      some (pr14NewModel s carry w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 rest) := by
  let v0 : W := UInt256.land w11 w0
  let v1 : W := carry - v0
  let v2 : W := w8 + v1
  let v3 : W := UInt256.mulMod v2 (N 2048) w8
  let v4 : W := MachineState.readWord s.memory 32
  let v5 : W := MachineState.readWord s.memory 2048
  let v6 : ByteArray := MachineState.writeBytes s.memory (Data.Bytes.natToBytesPadded v0.toNat 32) 800
  let v7 : W := v5 * v4
  let v8 : W := v7 + v3
  let v9 : W := UInt256.mulMod v5 v4 w8
  let v10 : W := v9 + v3
  let v11 : W := MachineState.readWord v6 64
  let v12 : W := MachineState.readWord v6 2016
  let v13 : W := v12 * v11
  let v14 : W := v13 + v8
  let v15 : W := UInt256.mulMod v12 v11 w8
  let v16 : W := v15 + v10
  let v17 : W := MachineState.readWord v6 96
  let v18 : W := MachineState.readWord v6 1984
  let v19 : W := v18 * v17
  let v20 : W := v19 + v14
  let v21 : W := UInt256.mulMod v18 v17 w8
  let v22 : W := v21 + v16
  let v23 : W := MachineState.readWord v6 128
  let v24 : W := MachineState.readWord v6 1952
  let v25 : W := v24 * v23
  let v26 : W := v25 + v20
  let v27 : W := UInt256.mulMod v24 v23 w8
  let v28 : W := v27 + v22
  let v29 : W := MachineState.readWord v6 160
  let v30 : W := MachineState.readWord v6 1920
  let v31 : W := UInt256.mulMod v29 v30 w8
  let v32 : W := v29 * v30
  let v33 : W := MachineState.readWord v6 1888
  let v34 : W := v26 + v32
  let v35 : W := v28 + v31
  let v36 : W := UInt256.mulMod w1 v33 w8
  let v37 : W := v36 + v35
  let v38 : W := w1 * v33
  let v39 : W := v38 + v34
  let v40 : W := MachineState.readWord v6 0
  let v41 : W := w9 * v40
  let v42 : W := v41 + v39
  let v43 : W := MachineState.readWord v6 224
  let v44 : W := w7 * v43
  let v45 : W := v44 + v42
  let v46 : W := w2 * w5
  let v47 : W := v46 + v45
  let v48 : W := w6 * w4
  let v49 : W := v48 + v47
  have h0 : runInstructions pr14Newpart0Program {s with pc := N 7695,memory := s.memory,stack := carry::w0::w1::w2::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::rest} = some {s with pc := N 7703,memory := s.memory,stack := v2::v0::w1::w2::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::rest} := by
    simpa only [pr14Newpart0Model,v0,v1,v2] using pr14Newpart0_run (s) (carry) w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 rest hcap hact
  have h1 : runInstructions pr14Newpart1Program {s with pc := N 7703,memory := s.memory,stack := v2::v0::w1::w2::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::rest} = some {s with pc := N 7714,memory := s.memory,stack := v3::v4::w8::v3::v0::w1::w2::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::rest} := by
    simpa only [pr14Newpart1Model,v3,v4] using pr14Newpart1_run (s) v2 v0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 rest hcap hact
  have h2 : runInstructions pr14Newpart2Program {s with pc := N 7714,memory := s.memory,stack := v3::v4::w8::v3::v0::w1::w2::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::rest} = some {s with pc := N 7726,memory := v6,stack := v7::v3::v4::w8::v3::v5::w1::w2::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::rest} := by
    simpa only [pr14Newpart2Model,v5,v6,v7] using pr14Newpart2_run (s) v3 v4 w8 v3 v0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 rest hcap hact
  have h3 : runInstructions pr14Newpart3Program {s with pc := N 7726,memory := v6,stack := v7::v3::v4::w8::v3::v5::w1::w2::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::rest} = some {s with pc := N 7738,memory := v6,stack := v12::v11::w8::v10::v8::w1::w2::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::rest} := by
    simpa only [pr14Newpart3Model,v8,v9,v10,v11,v12] using pr14Newpart3_run ({s with memory := v6}) v7 v3 v4 w8 v3 v5 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 rest hcap hact
  have h4 : runInstructions pr14Newpart4Program {s with pc := N 7738,memory := v6,stack := v12::v11::w8::v10::v8::w1::w2::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::rest} = some {s with pc := N 7746,memory := v6,stack := v16::v14::w1::w2::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::rest} := by
    simpa only [pr14Newpart4Model,v13,v14,v15,v16] using pr14Newpart4_run ({s with memory := v6}) v12 v11 w8 v10 v8 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 rest hcap hact
  have h5 : runInstructions pr14Newpart5Program {s with pc := N 7746,memory := v6,stack := v16::v14::w1::w2::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::rest} = some {s with pc := N 7757,memory := v6,stack := v18::v17::v14::v17::w8::v16::v18::w1::w2::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::rest} := by
    simpa only [pr14Newpart5Model,v17,v18] using pr14Newpart5_run ({s with memory := v6}) v16 v14 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 rest hcap hact
  have h6 : runInstructions pr14Newpart6Program {s with pc := N 7757,memory := v6,stack := v18::v17::v14::v17::w8::v16::v18::w1::w2::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::rest} = some {s with pc := N 7766,memory := v6,stack := v23::w8::v22::v20::w1::w2::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::rest} := by
    simpa only [pr14Newpart6Model,v19,v20,v21,v22,v23] using pr14Newpart6_run ({s with memory := v6}) v18 v17 v14 v17 w8 v16 v18 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 rest hcap hact
  have h7 : runInstructions pr14Newpart7Program {s with pc := N 7766,memory := v6,stack := v23::w8::v22::v20::w1::w2::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::rest} = some {s with pc := N 7776,memory := v6,stack := v24::v23::w8::v22::v26::w1::w2::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::rest} := by
    simpa only [pr14Newpart7Model,v24,v25,v26] using pr14Newpart7_run ({s with memory := v6}) v23 w8 v22 v20 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 rest hcap hact
  have h8 : runInstructions pr14Newpart8Program {s with pc := N 7776,memory := v6,stack := v24::v23::w8::v22::v26::w1::w2::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::rest} = some {s with pc := N 7787,memory := v6,stack := v30::w8::v30::v29::v28::v26::w1::w2::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::rest} := by
    simpa only [pr14Newpart8Model,v27,v28,v29,v30] using pr14Newpart8_run ({s with memory := v6}) v24 v23 w8 v22 v26 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 rest hcap hact
  have h9 : runInstructions pr14Newpart9Program {s with pc := N 7787,memory := v6,stack := v30::w8::v30::v29::v28::v26::w1::w2::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::rest} = some {s with pc := N 7797,memory := v6,stack := v34::v31::v28::v33::w1::w2::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::rest} := by
    simpa only [pr14Newpart9Model,v31,v32,v33,v34] using pr14Newpart9_run ({s with memory := v6}) v30 w8 v30 v29 v28 v26 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 rest hcap hact
  have h10 : runInstructions pr14Newpart10Program {s with pc := N 7797,memory := v6,stack := v34::v31::v28::v33::w1::w2::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::rest} = some {s with pc := N 7805,memory := v6,stack := v33::v34::v37::w1::w2::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::rest} := by
    simpa only [pr14Newpart10Model,v35,v36,v37] using pr14Newpart10_run ({s with memory := v6}) v34 v31 v28 v33 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 rest hcap hact
  have h11 : runInstructions pr14Newpart11Program {s with pc := N 7805,memory := v6,stack := v33::v34::v37::w1::w2::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::rest} = some {s with pc := N 7813,memory := v6,stack := v42::v37::w1::w2::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::rest} := by
    simpa only [pr14Newpart11Model,v38,v39,v40,v41,v42] using pr14Newpart11_run ({s with memory := v6}) v33 v34 v37 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 rest hcap hact
  have h12 : runInstructions pr14Newpart12Program {s with pc := N 7813,memory := v6,stack := v42::v37::w1::w2::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::rest} = some {s with pc := N 7822,memory := v6,stack := v46::v45::v37::w1::w2::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::rest} := by
    simpa only [pr14Newpart12Model,v43,v44,v45,v46] using pr14Newpart12_run ({s with memory := v6}) v42 v37 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 rest hcap hact
  have h13 : runInstructions pr14Newpart13Program {s with pc := N 7822,memory := v6,stack := v46::v45::v37::w1::w2::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::rest} = some {s with pc := N 7828,memory := v6,stack := w10::v49::v37::w1::w2::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::rest} := by
    simpa only [pr14Newpart13Model,v47,v48,v49] using pr14Newpart13_run ({s with memory := v6}) v46 v45 v37 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 rest hcap hact
  exact (runInstructions_append_some _ _ _ _ _ h0 (runInstructions_append_some _ _ _ _ _ h1 (runInstructions_append_some _ _ _ _ _ h2 (runInstructions_append_some _ _ _ _ _ h3 (runInstructions_append_some _ _ _ _ _ h4 (runInstructions_append_some _ _ _ _ _ h5 (runInstructions_append_some _ _ _ _ _ h6 (runInstructions_append_some _ _ _ _ _ h7 (runInstructions_append_some _ _ _ _ _ h8 (runInstructions_append_some _ _ _ _ _ h9 (runInstructions_append_some _ _ _ _ _ h10 (runInstructions_append_some _ _ _ _ _ h11 (runInstructions_append_some _ _ _ _ _ h12 h13)))))))))))))
#print axioms pr14New_run
def productColumn14Model (s : State) (carry w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 : W) (rest : List W) : State :=
  let v0 : W := UInt256.land w11 w0
  let v1 : W := carry - v0
  let v2 : W := w8 + v1
  let v3 : W := UInt256.mulMod v2 (N 2048) w8
  let v4 : W := MachineState.readWord s.memory 32
  let v5 : W := MachineState.readWord s.memory 2048
  let v6 : ByteArray := MachineState.writeBytes s.memory (Data.Bytes.natToBytesPadded v0.toNat 32) 800
  let v7 : W := v5 * v4
  let v8 : W := v7 + v3
  let v9 : W := UInt256.mulMod v5 v4 w8
  let v10 : W := v9 + v3
  let v11 : W := MachineState.readWord v6 64
  let v12 : W := MachineState.readWord v6 2016
  let v13 : W := v12 * v11
  let v14 : W := v13 + v8
  let v15 : W := UInt256.mulMod v12 v11 w8
  let v16 : W := v15 + v10
  let v17 : W := MachineState.readWord v6 96
  let v18 : W := MachineState.readWord v6 1984
  let v19 : W := v18 * v17
  let v20 : W := v19 + v14
  let v21 : W := UInt256.mulMod v18 v17 w8
  let v22 : W := v21 + v16
  let v23 : W := MachineState.readWord v6 128
  let v24 : W := MachineState.readWord v6 1952
  let v25 : W := v24 * v23
  let v26 : W := v25 + v20
  let v27 : W := UInt256.mulMod v24 v23 w8
  let v28 : W := v27 + v22
  let v29 : W := MachineState.readWord v6 160
  let v30 : W := MachineState.readWord v6 1920
  let v31 : W := v30 * v29
  let v32 : W := v31 + v26
  let v33 : W := UInt256.mulMod v30 v29 w8
  let v34 : W := v33 + v28
  let v35 : W := MachineState.readWord v6 1888
  let v36 : W := v35 * w1
  let v37 : W := v36 + v32
  let v38 : W := UInt256.mulMod v35 w1 w8
  let v39 : W := v38 + v34
  let v40 : W := MachineState.readWord v6 0
  let v41 : W := w9 * v40
  let v42 : W := v41 + v37
  let v43 : W := MachineState.readWord v6 224
  let v44 : W := w7 * v43
  let v45 : W := v44 + v42
  let v46 : W := w2 * w5
  let v47 : W := v46 + v45
  let v48 : W := w6 * w4
  let v49 : W := v48 + v47
  {s with pc := N 7828,memory := v6,stack := w10::v49::v39::w1::w2::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::rest}
def productColumn14Program : List Instr := pr14NewProgram
private theorem aux_shared0 (w8 : W) (z0 z1 : W) :
    (UInt256.mulMod z0 z1 w8) = (UInt256.mulMod z1 z0 w8) := by
  simp (disch := decide) only [addC,addA,addL,mulC,mmC,amC,andC,orC,xorC,eqC,read_disjoint,Challenge.EvmProof.Memory.readWord_writeWord]
private theorem aux_shared1 (z0 z1 : W) :
    (z0 * z1) = (z1 * z0) := by
  simp (disch := decide) only [addC,addA,addL,mulC,mmC,amC,andC,orC,xorC,eqC,read_disjoint,Challenge.EvmProof.Memory.readWord_writeWord]
private theorem aux_shared2 (z0 z1 : W) :
    (z0 + z1) = (z1 + z0) := by
  simp (disch := decide) only [addC,addA,addL,mulC,mmC,amC,andC,orC,xorC,eqC,read_disjoint,Challenge.EvmProof.Memory.readWord_writeWord]
private theorem aux_shared3 (w1 w8 : W) (z0 : W) :
    (UInt256.mulMod w1 z0 w8) = (UInt256.mulMod z0 w1 w8) := by
  simp (disch := decide) only [addC,addA,addL,mulC,mmC,amC,andC,orC,xorC,eqC,read_disjoint,Challenge.EvmProof.Memory.readWord_writeWord]
private theorem aux_shared4 (w1 : W) (z0 : W) :
    (w1 * z0) = (z0 * w1) := by
  simp (disch := decide) only [addC,addA,addL,mulC,mmC,amC,andC,orC,xorC,eqC,read_disjoint,Challenge.EvmProof.Memory.readWord_writeWord]
private theorem prepared_model_eq (s : State) (carry w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 : W) (rest : List W) :
    productColumn14Model s carry w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 rest = pr14NewModel s carry w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 rest := by
  let o0 : W := UInt256.land w11 w0
  let o1 : W := carry - o0
  let o2 : W := w8 + o1
  let o3 : W := UInt256.mulMod o2 (N 2048) w8
  let o4 : W := MachineState.readWord s.memory 32
  let o5 : W := MachineState.readWord s.memory 2048
  let o6 : ByteArray := MachineState.writeBytes s.memory (Data.Bytes.natToBytesPadded o0.toNat 32) 800
  let o7 : W := o5 * o4
  let o8 : W := o7 + o3
  let o9 : W := UInt256.mulMod o5 o4 w8
  let o10 : W := o9 + o3
  let o11 : W := MachineState.readWord o6 64
  let o12 : W := MachineState.readWord o6 2016
  let o13 : W := o12 * o11
  let o14 : W := o13 + o8
  let o15 : W := UInt256.mulMod o12 o11 w8
  let o16 : W := o15 + o10
  let o17 : W := MachineState.readWord o6 96
  let o18 : W := MachineState.readWord o6 1984
  let o19 : W := o18 * o17
  let o20 : W := o19 + o14
  let o21 : W := UInt256.mulMod o18 o17 w8
  let o22 : W := o21 + o16
  let o23 : W := MachineState.readWord o6 128
  let o24 : W := MachineState.readWord o6 1952
  let o25 : W := o24 * o23
  let o26 : W := o25 + o20
  let o27 : W := UInt256.mulMod o24 o23 w8
  let o28 : W := o27 + o22
  let o29 : W := MachineState.readWord o6 160
  let o30 : W := MachineState.readWord o6 1920
  let o31 : W := o30 * o29
  let o32 : W := o31 + o26
  let o33 : W := UInt256.mulMod o30 o29 w8
  let o34 : W := o33 + o28
  let o35 : W := MachineState.readWord o6 1888
  let o36 : W := o35 * w1
  let o37 : W := o36 + o32
  let o38 : W := UInt256.mulMod o35 w1 w8
  let o39 : W := o38 + o34
  let o40 : W := MachineState.readWord o6 0
  let o41 : W := w9 * o40
  let o42 : W := o41 + o37
  let o43 : W := MachineState.readWord o6 224
  let o44 : W := w7 * o43
  let o45 : W := o44 + o42
  let o46 : W := w2 * w5
  let o47 : W := o46 + o45
  let o48 : W := w6 * w4
  let o49 : W := o48 + o47
  let n0 : W := UInt256.land w11 w0
  let n1 : W := carry - n0
  let n2 : W := w8 + n1
  let n3 : W := UInt256.mulMod n2 (N 2048) w8
  let n4 : W := MachineState.readWord s.memory 32
  let n5 : W := MachineState.readWord s.memory 2048
  let n6 : ByteArray := MachineState.writeBytes s.memory (Data.Bytes.natToBytesPadded n0.toNat 32) 800
  let n7 : W := n5 * n4
  let n8 : W := n7 + n3
  let n9 : W := UInt256.mulMod n5 n4 w8
  let n10 : W := n9 + n3
  let n11 : W := MachineState.readWord n6 64
  let n12 : W := MachineState.readWord n6 2016
  let n13 : W := n12 * n11
  let n14 : W := n13 + n8
  let n15 : W := UInt256.mulMod n12 n11 w8
  let n16 : W := n15 + n10
  let n17 : W := MachineState.readWord n6 96
  let n18 : W := MachineState.readWord n6 1984
  let n19 : W := n18 * n17
  let n20 : W := n19 + n14
  let n21 : W := UInt256.mulMod n18 n17 w8
  let n22 : W := n21 + n16
  let n23 : W := MachineState.readWord n6 128
  let n24 : W := MachineState.readWord n6 1952
  let n25 : W := n24 * n23
  let n26 : W := n25 + n20
  let n27 : W := UInt256.mulMod n24 n23 w8
  let n28 : W := n27 + n22
  let n29 : W := MachineState.readWord n6 160
  let n30 : W := MachineState.readWord n6 1920
  let n31 : W := UInt256.mulMod n29 n30 w8
  let n32 : W := n29 * n30
  let n33 : W := MachineState.readWord n6 1888
  let n34 : W := n26 + n32
  let n35 : W := n28 + n31
  let n36 : W := UInt256.mulMod w1 n33 w8
  let n37 : W := n36 + n35
  let n38 : W := w1 * n33
  let n39 : W := n38 + n34
  let n40 : W := MachineState.readWord n6 0
  let n41 : W := w9 * n40
  let n42 : W := n41 + n39
  let n43 : W := MachineState.readWord n6 224
  let n44 : W := w7 * n43
  let n45 : W := n44 + n42
  let n46 : W := w2 * w5
  let n47 : W := n46 + n45
  let n48 : W := w6 * w4
  let n49 : W := n48 + n47
  have eq_n0 : n0 = o0 := by
    simp only [n0,o0]
  have eq_n1 : n1 = o1 := by
    simp only [n1,o1,eq_n0]
  have eq_n2 : n2 = o2 := by
    simp only [n2,o2,eq_n1]
  have eq_n3 : n3 = o3 := by
    simp only [n3,o3,eq_n2]
  have eq_n4 : n4 = o4 := by
    simp only [n4,o4]
  have eq_n5 : n5 = o5 := by
    simp only [n5,o5]
  have eq_n6 : n6 = o6 := by
    simp only [n6,o6,eq_n0]
  have eq_n7 : n7 = o7 := by
    simp only [n7,o7,eq_n5,eq_n4]
  have eq_n8 : n8 = o8 := by
    simp only [n8,o8,eq_n7,eq_n3]
  have eq_n9 : n9 = o9 := by
    simp only [n9,o9,eq_n5,eq_n4]
  have eq_n10 : n10 = o10 := by
    simp only [n10,o10,eq_n9,eq_n3]
  have eq_n11 : n11 = o11 := by
    simp only [n11,o11,eq_n6]
  have eq_n12 : n12 = o12 := by
    simp only [n12,o12,eq_n6]
  have eq_n13 : n13 = o13 := by
    simp only [n13,o13,eq_n12,eq_n11]
  have eq_n14 : n14 = o14 := by
    simp only [n14,o14,eq_n13,eq_n8]
  have eq_n15 : n15 = o15 := by
    simp only [n15,o15,eq_n12,eq_n11]
  have eq_n16 : n16 = o16 := by
    simp only [n16,o16,eq_n15,eq_n10]
  have eq_n17 : n17 = o17 := by
    simp only [n17,o17,eq_n6]
  have eq_n18 : n18 = o18 := by
    simp only [n18,o18,eq_n6]
  have eq_n19 : n19 = o19 := by
    simp only [n19,o19,eq_n18,eq_n17]
  have eq_n20 : n20 = o20 := by
    simp only [n20,o20,eq_n19,eq_n14]
  have eq_n21 : n21 = o21 := by
    simp only [n21,o21,eq_n18,eq_n17]
  have eq_n22 : n22 = o22 := by
    simp only [n22,o22,eq_n21,eq_n16]
  have eq_n23 : n23 = o23 := by
    simp only [n23,o23,eq_n6]
  have eq_n24 : n24 = o24 := by
    simp only [n24,o24,eq_n6]
  have eq_n25 : n25 = o25 := by
    simp only [n25,o25,eq_n24,eq_n23]
  have eq_n26 : n26 = o26 := by
    simp only [n26,o26,eq_n25,eq_n20]
  have eq_n27 : n27 = o27 := by
    simp only [n27,o27,eq_n24,eq_n23]
  have eq_n28 : n28 = o28 := by
    simp only [n28,o28,eq_n27,eq_n22]
  have eq_n29 : n29 = o29 := by
    simp only [n29,o29,eq_n6]
  have eq_n30 : n30 = o30 := by
    simp only [n30,o30,eq_n6]
  have eq_n31 : n31 = o33 := by
    simpa only [n31,o33,eq_n29,eq_n30] using
      (aux_shared0 w8 o29 o30)
  have eq_n32 : n32 = o31 := by
    simpa only [n32,o31,eq_n29,eq_n30] using
      (aux_shared1  o29 o30)
  have eq_n33 : n33 = o35 := by
    simp only [n33,o35,eq_n6]
  have eq_n34 : n34 = o32 := by
    simpa only [n34,o32,eq_n26,eq_n32] using
      (aux_shared2  o26 o31)
  have eq_n35 : n35 = o34 := by
    simpa only [n35,o34,eq_n28,eq_n31] using
      (aux_shared2  o28 o33)
  have eq_n36 : n36 = o38 := by
    simpa only [n36,o38,eq_n33] using
      (aux_shared3 w1 w8 o35)
  have eq_n37 : n37 = o39 := by
    simp only [n37,o39,eq_n36,eq_n35]
  have eq_n38 : n38 = o36 := by
    simpa only [n38,o36,eq_n33] using
      (aux_shared4 w1 o35)
  have eq_n39 : n39 = o37 := by
    simp only [n39,o37,eq_n38,eq_n34]
  have eq_n40 : n40 = o40 := by
    simp only [n40,o40,eq_n6]
  have eq_n41 : n41 = o41 := by
    simp only [n41,o41,eq_n40]
  have eq_n42 : n42 = o42 := by
    simp only [n42,o42,eq_n41,eq_n39]
  have eq_n43 : n43 = o43 := by
    simp only [n43,o43,eq_n6]
  have eq_n44 : n44 = o44 := by
    simp only [n44,o44,eq_n43]
  have eq_n45 : n45 = o45 := by
    simp only [n45,o45,eq_n44,eq_n42]
  have eq_n46 : n46 = o46 := by
    simp only [n46,o46]
  have eq_n47 : n47 = o47 := by
    simp only [n47,o47,eq_n46,eq_n45]
  have eq_n48 : n48 = o48 := by
    simp only [n48,o48]
  have eq_n49 : n49 = o49 := by
    simp only [n49,o49,eq_n48,eq_n47]
  change {s with pc := N 7828,memory := o6,stack := w10::o49::o39::w1::w2::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::rest} =
    {s with pc := N 7828,memory := n6,stack := w10::n49::n37::w1::w2::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::rest}
  simp only [eq_n0,eq_n1,eq_n2,eq_n3,eq_n4,eq_n5,eq_n6,eq_n7,eq_n8,eq_n9,eq_n10,eq_n11,eq_n12,eq_n13,eq_n14,eq_n15,eq_n16,eq_n17,eq_n18,eq_n19,eq_n20,eq_n21,eq_n22,eq_n23,eq_n24,eq_n25,eq_n26,eq_n27,eq_n28,eq_n29,eq_n30,eq_n31,eq_n32,eq_n33,eq_n34,eq_n35,eq_n36,eq_n37,eq_n38,eq_n39,eq_n40,eq_n41,eq_n42,eq_n43,eq_n44,eq_n45,eq_n46,eq_n47,eq_n48,eq_n49]
theorem productColumn14_run (s : State) (carry w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions productColumn14Program {s with pc := N 7695,stack := carry::w0::w1::w2::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::rest} =
      some (productColumn14Model s carry w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 rest) := by
  exact (pr14New_run s carry w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 rest hcap hact).trans
    (congrArg some (prepared_model_eq s carry w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 rest).symm)
#print axioms productColumn14_run
end CycleSubmission.Execution
