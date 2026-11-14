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
def pr2Newpart0Program : List Instr :=
  [
  .op .MUL,
   .op .ADD,
   .op (.Swap sA0),
   .op (.Dup dA9),
   .op (.Dup dA15),
   .op (.Dup dA12),
   .op .MULMOD,
   .op .ADD]
def pr2Newpart0Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 : W) (rest : List W) : State :=
  let v0 : W := x0 * x1
  let v1 : W := v0 + x2
  let v2 : W := UInt256.mulMod x12 x16 x11
  let v3 : W := v2 + x3
  {s with pc := N 6193,memory := s.memory,stack := v3::v1::x4::x5::x6::x7::x8::x9::x10::x11::x12::x13::x14::x15::x16::x17::rest}
theorem pr2Newpart0_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions pr2Newpart0Program {s with pc := N 6185,stack := x0::x1::x2::x3::x4::x5::x6::x7::x8::x9::x10::x11::x12::x13::x14::x15::x16::x17::rest} =
      some (pr2Newpart0Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 19) : rest.length + j < 1024 := by omega
  simp [hz,hzn,pr2Newpart0Program,pr2Newpart0Model,runInstructions,runInstr,List.exchange,succ_ofNat_mod,ofNat_add_mod,Nat.add_assoc,State.activeWordsAfterUInt256,literal_eq_ofNat,capacity]
def pr2Newpart1Program : List Instr :=
  [
  .op (.Dup dA9),
   .op (.Dup dA3),
   .op (.Dup dA10),
   .op .MULMOD,
   .op .ADD,
   .op (.Dup dA9),
   .op (.Dup dA12),
   .push 1 192,
   .op .MLOAD]
def pr2Newpart1Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 : W) (rest : List W) : State :=
  let v0 : W := UInt256.mulMod x8 x2 x9
  let v1 : W := v0 + x0
  let v2 : W := MachineState.readWord s.memory 192
  {s with pc := N 6203,memory := s.memory,stack := v2::x11::x9::v1::x1::x2::x3::x4::x5::x6::x7::x8::x9::x10::x11::x12::x13::x14::x15::rest}
theorem pr2Newpart1_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions pr2Newpart1Program {s with pc := N 6193,stack := x0::x1::x2::x3::x4::x5::x6::x7::x8::x9::x10::x11::x12::x13::x14::x15::rest} =
      some (pr2Newpart1Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 19) : rest.length + j < 1024 := by omega
  have ha192 : (192 : W).toNat = 192 := rfl
  have hf192 := Monpro.activeWords_fix s 192 32 (by decide) (by norm_num) hact
  simp [hz,hzn,pr2Newpart1Program,pr2Newpart1Model,runInstructions,runInstr,List.exchange,succ_ofNat_mod,ofNat_add_mod,Nat.add_assoc,State.activeWordsAfterUInt256,literal_eq_ofNat,capacity,ha192,hf192]
def pr2Newpart2Program : List Instr :=
  [
  .op .MULMOD,
   .op .ADD,
   .op (.Dup dA9),
   .op (.Dup dA14),
   .push 2 2720,
   .op .MLOAD,
   .op (.Dup dA2),
   .op (.Swap sA4)]
def pr2Newpart2Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 : W) (rest : List W) : State :=
  let v0 : W := UInt256.mulMod x0 x1 x2
  let v1 : W := v0 + x3
  let v2 : W := MachineState.readWord s.memory 2720
  {s with pc := N 6213,memory := s.memory,stack := x4::v2::x16::x12::v1::x12::x5::x6::x7::x8::x9::x10::x11::x12::x13::x14::x15::x16::x17::x18::rest}
theorem pr2Newpart2_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions pr2Newpart2Program {s with pc := N 6203,stack := x0::x1::x2::x3::x4::x5::x6::x7::x8::x9::x10::x11::x12::x13::x14::x15::x16::x17::x18::rest} =
      some (pr2Newpart2Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 20) : rest.length + j < 1024 := by omega
  have ha2720 : (2720 : W).toNat = 2720 := rfl
  have hf2720 := Monpro.activeWords_fix s 2720 32 (by decide) (by norm_num) hact
  simp [hz,hzn,pr2Newpart2Program,pr2Newpart2Model,runInstructions,runInstr,List.exchange,succ_ofNat_mod,ofNat_add_mod,Nat.add_assoc,State.activeWordsAfterUInt256,literal_eq_ofNat,capacity,ha2720,hf2720]
def pr2Newpart3Program : List Instr :=
  [
  .op .MUL,
   .op (.Dup dA15),
   .op .AND,
   .op (.Dup dA0),
   .push 0 0,
   .op .MSTORE,
   .op .MULMOD,
   .op .ADD]
def pr2Newpart3Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 : W) (rest : List W) : State :=
  let v0 : W := x0 * x1
  let v1 : W := UInt256.land x16 v0
  let v2 : ByteArray := MachineState.writeBytes s.memory (Data.Bytes.natToBytesPadded v1.toNat 32) 0
  let v3 : W := UInt256.mulMod v1 x2 x3
  let v4 : W := v3 + x4
  {s with pc := N 6221,memory := v2,stack := v4::x5::x6::x7::x8::x9::x10::x11::x12::x13::x14::x15::x16::x17::x18::x19::rest}
theorem pr2Newpart3_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions pr2Newpart3Program {s with pc := N 6213,stack := x0::x1::x2::x3::x4::x5::x6::x7::x8::x9::x10::x11::x12::x13::x14::x15::x16::x17::x18::x19::rest} =
      some (pr2Newpart3Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 21) : rest.length + j < 1024 := by omega
  have ha0 : (0 : W).toNat = 0 := rfl
  have hf0 := Monpro.activeWords_fix s 0 32 (by decide) (by norm_num) hact
  simp [hz,hzn,pr2Newpart3Program,pr2Newpart3Model,runInstructions,runInstr,List.exchange,succ_ofNat_mod,ofNat_add_mod,Nat.add_assoc,State.activeWordsAfterUInt256,literal_eq_ofNat,capacity,ha0,hf0]
def pr2Newpart4Program : List Instr :=
  [
  .push 2 2048,
   .op .MULMOD,
   .push 2 1888,
   .op .MLOAD,
   .push 2 768,
   .op .MLOAD,
   .push 2 1920,
   .op .MLOAD]
def pr2Newpart4Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 : W) (rest : List W) : State :=
  let v0 : W := UInt256.mulMod (N 2048) x0 x1
  let v1 : W := MachineState.readWord s.memory 1888
  let v2 : W := MachineState.readWord s.memory 768
  let v3 : W := MachineState.readWord s.memory 1920
  {s with pc := N 6237,memory := s.memory,stack := v3::v2::v1::v0::x2::x3::x4::x5::x6::x7::x8::x9::x10::x11::x12::x13::x14::x15::rest}
theorem pr2Newpart4_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions pr2Newpart4Program {s with pc := N 6221,stack := x0::x1::x2::x3::x4::x5::x6::x7::x8::x9::x10::x11::x12::x13::x14::x15::rest} =
      some (pr2Newpart4Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 18) : rest.length + j < 1024 := by omega
  have ha768 : (768 : W).toNat = 768 := rfl
  have hf768 := Monpro.activeWords_fix s 768 32 (by decide) (by norm_num) hact
  have ha1888 : (1888 : W).toNat = 1888 := rfl
  have hf1888 := Monpro.activeWords_fix s 1888 32 (by decide) (by norm_num) hact
  have ha1920 : (1920 : W).toNat = 1920 := rfl
  have hf1920 := Monpro.activeWords_fix s 1920 32 (by decide) (by norm_num) hact
  simp [hz,hzn,pr2Newpart4Program,pr2Newpart4Model,runInstructions,runInstr,List.exchange,succ_ofNat_mod,ofNat_add_mod,Nat.add_assoc,State.activeWordsAfterUInt256,literal_eq_ofNat,capacity,ha768,hf768,ha1888,hf1888,ha1920,hf1920]
def pr2Newpart5Program : List Instr :=
  [
  .op (.Dup dA11),
   .op (.Dup dA1),
   .op (.Dup dA3),
   .op .MULMOD,
   .op (.Swap sA1),
   .op .MUL,
   .op (.Dup dA3),
   .op .ADD]
def pr2Newpart5Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 : W) (rest : List W) : State :=
  let v0 : W := UInt256.mulMod x1 x0 x11
  let v1 : W := x1 * x0
  let v2 : W := x3 + v1
  {s with pc := N 6245,memory := s.memory,stack := v2::v0::x2::x3::x4::x5::x6::x7::x8::x9::x10::x11::x12::x13::x14::x15::x16::x17::rest}
theorem pr2Newpart5_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions pr2Newpart5Program {s with pc := N 6237,stack := x0::x1::x2::x3::x4::x5::x6::x7::x8::x9::x10::x11::x12::x13::x14::x15::x16::x17::rest} =
      some (pr2Newpart5Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 21) : rest.length + j < 1024 := by omega
  simp [hz,hzn,pr2Newpart5Program,pr2Newpart5Model,runInstructions,runInstr,List.exchange,succ_ofNat_mod,ofNat_add_mod,Nat.add_assoc,State.activeWordsAfterUInt256,literal_eq_ofNat,capacity]
def pr2Newpart6Program : List Instr :=
  [
  .op (.Dup dA11),
   .op (.Dup dA3),
   .op (.Dup dA9),
   .op .MULMOD,
   .op (.Swap sA2),
   .op (.Dup dA8),
   .op .MUL,
   .op .ADD]
def pr2Newpart6Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 : W) (rest : List W) : State :=
  let v0 : W := UInt256.mulMod x7 x2 x11
  let v1 : W := x7 * x2
  let v2 : W := v1 + x0
  {s with pc := N 6253,memory := s.memory,stack := v2::x1::v0::x3::x4::x5::x6::x7::x8::x9::x10::x11::x12::x13::x14::x15::x16::x17::rest}
theorem pr2Newpart6_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions pr2Newpart6Program {s with pc := N 6245,stack := x0::x1::x2::x3::x4::x5::x6::x7::x8::x9::x10::x11::x12::x13::x14::x15::x16::x17::rest} =
      some (pr2Newpart6Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 21) : rest.length + j < 1024 := by omega
  simp [hz,hzn,pr2Newpart6Program,pr2Newpart6Model,runInstructions,runInstr,List.exchange,succ_ofNat_mod,ofNat_add_mod,Nat.add_assoc,State.activeWordsAfterUInt256,literal_eq_ofNat,capacity]
def pr2Newpart7Program : List Instr :=
  [
  .op (.Swap sA2),
   .op .ADD,
   .op .ADD,
   .op (.Dup dA9),
   .op (.Dup dA7),
   .push 2 1856,
   .op .MLOAD,
   .op (.Swap sA3)]
def pr2Newpart7Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 : W) (rest : List W) : State :=
  let v0 : W := x3 + x1
  let v1 : W := v0 + x2
  let v2 : W := MachineState.readWord s.memory 1856
  {s with pc := N 6263,memory := s.memory,stack := x0::x8::x11::v1::v2::x4::x5::x6::x7::x8::x9::x10::x11::x12::x13::x14::x15::x16::x17::rest}
theorem pr2Newpart7_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions pr2Newpart7Program {s with pc := N 6253,stack := x0::x1::x2::x3::x4::x5::x6::x7::x8::x9::x10::x11::x12::x13::x14::x15::x16::x17::rest} =
      some (pr2Newpart7Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 19) : rest.length + j < 1024 := by omega
  have ha1856 : (1856 : W).toNat = 1856 := rfl
  have hf1856 := Monpro.activeWords_fix s 1856 32 (by decide) (by norm_num) hact
  simp [hz,hzn,pr2Newpart7Program,pr2Newpart7Model,runInstructions,runInstr,List.exchange,succ_ofNat_mod,ofNat_add_mod,Nat.add_assoc,State.activeWordsAfterUInt256,literal_eq_ofNat,capacity,ha1856,hf1856]
def pr2Newpart8Program : List Instr :=
  [
  .op (.Dup dA1),
   .op (.Dup dA5),
   .op .MUL,
   .op .ADD,
   .op (.Swap sA3),
   .op .MULMOD,
   .op .ADD,
   .push 1 64,
   .op .MLOAD]
def pr2Newpart8Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 : W) (rest : List W) : State :=
  let v0 : W := x4 * x1
  let v1 : W := v0 + x0
  let v2 : W := UInt256.mulMod x4 x1 x2
  let v3 : W := v2 + x3
  let v4 : W := MachineState.readWord s.memory 64
  {s with pc := N 6273,memory := s.memory,stack := v4::v3::v1::x5::x6::x7::x8::x9::x10::x11::x12::x13::x14::x15::x16::x17::x18::rest}
theorem pr2Newpart8_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions pr2Newpart8Program {s with pc := N 6263,stack := x0::x1::x2::x3::x4::x5::x6::x7::x8::x9::x10::x11::x12::x13::x14::x15::x16::x17::x18::rest} =
      some (pr2Newpart8Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 21) : rest.length + j < 1024 := by omega
  have ha64 : (64 : W).toNat = 64 := rfl
  have hf64 := Monpro.activeWords_fix s 64 32 (by decide) (by norm_num) hact
  simp [hz,hzn,pr2Newpart8Program,pr2Newpart8Model,runInstructions,runInstr,List.exchange,succ_ofNat_mod,ofNat_add_mod,Nat.add_assoc,State.activeWordsAfterUInt256,literal_eq_ofNat,capacity,ha64,hf64]
def pr2Newpart9Program : List Instr :=
  [
  .push 1 32,
   .op .MLOAD,
   .push 2 1824,
   .op .MLOAD,
   .op (.Dup dA12),
   .op (.Dup dA1),
   .op (.Dup dA3),
   .op .MULMOD]
def pr2Newpart9Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 : W) (rest : List W) : State :=
  let v0 : W := MachineState.readWord s.memory 32
  let v1 : W := MachineState.readWord s.memory 1824
  let v2 : W := UInt256.mulMod v0 v1 x10
  {s with pc := N 6284,memory := s.memory,stack := v2::v1::v0::x0::x1::x2::x3::x4::x5::x6::x7::x8::x9::x10::x11::x12::x13::x14::x15::x16::rest}
theorem pr2Newpart9_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions pr2Newpart9Program {s with pc := N 6273,stack := x0::x1::x2::x3::x4::x5::x6::x7::x8::x9::x10::x11::x12::x13::x14::x15::x16::rest} =
      some (pr2Newpart9Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 22) : rest.length + j < 1024 := by omega
  have ha32 : (32 : W).toNat = 32 := rfl
  have hf32 := Monpro.activeWords_fix s 32 32 (by decide) (by norm_num) hact
  have ha1824 : (1824 : W).toNat = 1824 := rfl
  have hf1824 := Monpro.activeWords_fix s 1824 32 (by decide) (by norm_num) hact
  simp [hz,hzn,pr2Newpart9Program,pr2Newpart9Model,runInstructions,runInstr,List.exchange,succ_ofNat_mod,ofNat_add_mod,Nat.add_assoc,State.activeWordsAfterUInt256,literal_eq_ofNat,capacity,ha32,hf32,ha1824,hf1824]
def pr2Newpart10Program : List Instr :=
  [
  .op (.Swap sA1),
   .op .MUL,
   .push 2 1792,
   .op .MLOAD,
   .op (.Swap sA4),
   .op .ADD,
   .op (.Swap sA2),
   .op .ADD]
def pr2Newpart10Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 : W) (rest : List W) : State :=
  let v0 : W := x2 * x1
  let v1 : W := MachineState.readWord s.memory 1792
  let v2 : W := x5 + v0
  let v3 : W := x4 + x0
  {s with pc := N 6294,memory := s.memory,stack := v3::x3::v2::v1::x6::x7::x8::x9::x10::x11::x12::x13::x14::x15::x16::x17::x18::x19::rest}
theorem pr2Newpart10_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions pr2Newpart10Program {s with pc := N 6284,stack := x0::x1::x2::x3::x4::x5::x6::x7::x8::x9::x10::x11::x12::x13::x14::x15::x16::x17::x18::x19::rest} =
      some (pr2Newpart10Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 20) : rest.length + j < 1024 := by omega
  have ha1792 : (1792 : W).toNat = 1792 := rfl
  have hf1792 := Monpro.activeWords_fix s 1792 32 (by decide) (by norm_num) hact
  simp [hz,hzn,pr2Newpart10Program,pr2Newpart10Model,runInstructions,runInstr,List.exchange,succ_ofNat_mod,ofNat_add_mod,Nat.add_assoc,State.activeWordsAfterUInt256,literal_eq_ofNat,capacity,ha1792,hf1792]
def pr2Newpart11Program : List Instr :=
  [
  .op (.Dup dA11),
   .op (.Dup dA2),
   .op (.Dup dA5),
   .op .MULMOD,
   .op .ADD,
   .op (.Swap sA2),
   .op .MUL,
   .op .ADD]
def pr2Newpart11Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 : W) (rest : List W) : State :=
  let v0 : W := UInt256.mulMod x3 x1 x11
  let v1 : W := v0 + x0
  let v2 : W := x3 * x1
  let v3 : W := v2 + x2
  {s with pc := N 6302,memory := s.memory,stack := v3::v1::x4::x5::x6::x7::x8::x9::x10::x11::x12::x13::x14::x15::x16::x17::rest}
theorem pr2Newpart11_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions pr2Newpart11Program {s with pc := N 6294,stack := x0::x1::x2::x3::x4::x5::x6::x7::x8::x9::x10::x11::x12::x13::x14::x15::x16::x17::rest} =
      some (pr2Newpart11Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 21) : rest.length + j < 1024 := by omega
  simp [hz,hzn,pr2Newpart11Program,pr2Newpart11Model,runInstructions,runInstr,List.exchange,succ_ofNat_mod,ofNat_add_mod,Nat.add_assoc,State.activeWordsAfterUInt256,literal_eq_ofNat,capacity]
def pr2Newpart12Program : List Instr :=
  [
  .op (.Dup dA4),
   .op (.Dup dA11),
   .op .MUL,
   .op .ADD,
   .op (.Dup dA14),
   .op (.Dup dA9),
   .op .MUL,
   .op .ADD]
def pr2Newpart12Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 : W) (rest : List W) : State :=
  let v0 : W := x10 * x4
  let v1 : W := v0 + x0
  let v2 : W := x8 * x14
  let v3 : W := v2 + v1
  {s with pc := N 6310,memory := s.memory,stack := v3::x1::x2::x3::x4::x5::x6::x7::x8::x9::x10::x11::x12::x13::x14::x15::rest}
theorem pr2Newpart12_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions pr2Newpart12Program {s with pc := N 6302,stack := x0::x1::x2::x3::x4::x5::x6::x7::x8::x9::x10::x11::x12::x13::x14::x15::rest} =
      some (pr2Newpart12Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 18) : rest.length + j < 1024 := by omega
  simp [hz,hzn,pr2Newpart12Program,pr2Newpart12Model,runInstructions,runInstr,List.exchange,succ_ofNat_mod,ofNat_add_mod,Nat.add_assoc,State.activeWordsAfterUInt256,literal_eq_ofNat,capacity]
def pr2Newpart13Program : List Instr :=
  [
  .op (.Dup dA2)]
def pr2Newpart13Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 : W) (rest : List W) : State :=
  {s with pc := N 6311,memory := s.memory,stack := x2::x0::x1::x2::x3::x4::x5::x6::x7::x8::x9::x10::x11::x12::x13::x14::x15::rest}
theorem pr2Newpart13_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions pr2Newpart13Program {s with pc := N 6310,stack := x0::x1::x2::x3::x4::x5::x6::x7::x8::x9::x10::x11::x12::x13::x14::x15::rest} =
      some (pr2Newpart13Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 17) : rest.length + j < 1024 := by omega
  simp [hz,hzn,pr2Newpart13Program,pr2Newpart13Model,runInstructions,runInstr,List.exchange,succ_ofNat_mod,ofNat_add_mod,Nat.add_assoc,State.activeWordsAfterUInt256,literal_eq_ofNat,capacity]
def pr2NewProgram : List Instr :=
  [
  .op .MUL,
   .op .ADD,
   .op (.Swap sA0),
   .op (.Dup dA9),
   .op (.Dup dA15),
   .op (.Dup dA12),
   .op .MULMOD,
   .op .ADD,
   .op (.Dup dA9),
   .op (.Dup dA3),
   .op (.Dup dA10),
   .op .MULMOD,
   .op .ADD,
   .op (.Dup dA9),
   .op (.Dup dA12),
   .push 1 192,
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
   .push 0 0,
   .op .MSTORE,
   .op .MULMOD,
   .op .ADD,
   .push 2 2048,
   .op .MULMOD,
   .push 2 1888,
   .op .MLOAD,
   .push 2 768,
   .op .MLOAD,
   .push 2 1920,
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
   .op (.Dup dA9),
   .op (.Dup dA7),
   .push 2 1856,
   .op .MLOAD,
   .op (.Swap sA3),
   .op (.Dup dA1),
   .op (.Dup dA5),
   .op .MUL,
   .op .ADD,
   .op (.Swap sA3),
   .op .MULMOD,
   .op .ADD,
   .push 1 64,
   .op .MLOAD,
   .push 1 32,
   .op .MLOAD,
   .push 2 1824,
   .op .MLOAD,
   .op (.Dup dA12),
   .op (.Dup dA1),
   .op (.Dup dA3),
   .op .MULMOD,
   .op (.Swap sA1),
   .op .MUL,
   .push 2 1792,
   .op .MLOAD,
   .op (.Swap sA4),
   .op .ADD,
   .op (.Swap sA2),
   .op .ADD,
   .op (.Dup dA11),
   .op (.Dup dA2),
   .op (.Dup dA5),
   .op .MULMOD,
   .op .ADD,
   .op (.Swap sA2),
   .op .MUL,
   .op .ADD,
   .op (.Dup dA4),
   .op (.Dup dA11),
   .op .MUL,
   .op .ADD,
   .op (.Dup dA14),
   .op (.Dup dA9),
   .op .MUL,
   .op .ADD,
   .op (.Dup dA2)]
def pr2NewModel (s : State) (carry w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 : W) (rest : List W) : State :=
  let v0 : W := carry * w0
  let v1 : W := v0 + w1
  let v2 : W := UInt256.mulMod w11 w15 w10
  let v3 : W := v2 + w2
  let v4 : W := UInt256.mulMod w9 w3 w10
  let v5 : W := v4 + v3
  let v6 : W := MachineState.readWord s.memory 192
  let v7 : W := UInt256.mulMod v6 w12 w10
  let v8 : W := v7 + v5
  let v9 : W := MachineState.readWord s.memory 2720
  let v10 : W := v1 * v9
  let v11 : W := UInt256.land w13 v10
  let v12 : ByteArray := MachineState.writeBytes s.memory (Data.Bytes.natToBytesPadded v11.toNat 32) 0
  let v13 : W := UInt256.mulMod v11 w14 w10
  let v14 : W := v13 + v8
  let v15 : W := UInt256.mulMod (N 2048) v14 w10
  let v16 : W := MachineState.readWord v12 1888
  let v17 : W := MachineState.readWord v12 768
  let v18 : W := MachineState.readWord v12 1920
  let v19 : W := UInt256.mulMod v17 v18 w10
  let v20 : W := v17 * v18
  let v21 : W := v15 + v20
  let v22 : W := UInt256.mulMod w6 v16 w10
  let v23 : W := w6 * v16
  let v24 : W := v23 + v21
  let v25 : W := v15 + v19
  let v26 : W := v25 + v22
  let v27 : W := MachineState.readWord v12 1856
  let v28 : W := v27 * w7
  let v29 : W := v28 + v24
  let v30 : W := UInt256.mulMod v27 w7 w10
  let v31 : W := v30 + v26
  let v32 : W := MachineState.readWord v12 64
  let v33 : W := MachineState.readWord v12 32
  let v34 : W := MachineState.readWord v12 1824
  let v35 : W := UInt256.mulMod v33 v34 w10
  let v36 : W := v33 * v34
  let v37 : W := MachineState.readWord v12 1792
  let v38 : W := v29 + v36
  let v39 : W := v31 + v35
  let v40 : W := UInt256.mulMod v37 v32 w10
  let v41 : W := v40 + v39
  let v42 : W := v37 * v32
  let v43 : W := v42 + v38
  let v44 : W := w11 * w5
  let v45 : W := v44 + v43
  let v46 : W := w9 * w15
  let v47 : W := v46 + v45
  {s with pc := N 6311,memory := v12,stack := w3::v47::v41::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::w16::rest}
theorem pr2New_run (s : State) (carry w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions pr2NewProgram {s with pc := N 6185,stack := carry::w0::w1::w2::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::w16::rest} =
      some (pr2NewModel s carry w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 rest) := by
  let v0 : W := carry * w0
  let v1 : W := v0 + w1
  let v2 : W := UInt256.mulMod w11 w15 w10
  let v3 : W := v2 + w2
  let v4 : W := UInt256.mulMod w9 w3 w10
  let v5 : W := v4 + v3
  let v6 : W := MachineState.readWord s.memory 192
  let v7 : W := UInt256.mulMod v6 w12 w10
  let v8 : W := v7 + v5
  let v9 : W := MachineState.readWord s.memory 2720
  let v10 : W := v1 * v9
  let v11 : W := UInt256.land w13 v10
  let v12 : ByteArray := MachineState.writeBytes s.memory (Data.Bytes.natToBytesPadded v11.toNat 32) 0
  let v13 : W := UInt256.mulMod v11 w14 w10
  let v14 : W := v13 + v8
  let v15 : W := UInt256.mulMod (N 2048) v14 w10
  let v16 : W := MachineState.readWord v12 1888
  let v17 : W := MachineState.readWord v12 768
  let v18 : W := MachineState.readWord v12 1920
  let v19 : W := UInt256.mulMod v17 v18 w10
  let v20 : W := v17 * v18
  let v21 : W := v15 + v20
  let v22 : W := UInt256.mulMod w6 v16 w10
  let v23 : W := w6 * v16
  let v24 : W := v23 + v21
  let v25 : W := v15 + v19
  let v26 : W := v25 + v22
  let v27 : W := MachineState.readWord v12 1856
  let v28 : W := v27 * w7
  let v29 : W := v28 + v24
  let v30 : W := UInt256.mulMod v27 w7 w10
  let v31 : W := v30 + v26
  let v32 : W := MachineState.readWord v12 64
  let v33 : W := MachineState.readWord v12 32
  let v34 : W := MachineState.readWord v12 1824
  let v35 : W := UInt256.mulMod v33 v34 w10
  let v36 : W := v33 * v34
  let v37 : W := MachineState.readWord v12 1792
  let v38 : W := v29 + v36
  let v39 : W := v31 + v35
  let v40 : W := UInt256.mulMod v37 v32 w10
  let v41 : W := v40 + v39
  let v42 : W := v37 * v32
  let v43 : W := v42 + v38
  let v44 : W := w11 * w5
  let v45 : W := v44 + v43
  let v46 : W := w9 * w15
  let v47 : W := v46 + v45
  have h0 : runInstructions pr2Newpart0Program {s with pc := N 6185,memory := s.memory,stack := carry::w0::w1::w2::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::w16::rest} = some {s with pc := N 6193,memory := s.memory,stack := v3::v1::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::w16::rest} := by
    simpa only [pr2Newpart0Model,v0,v1,v2,v3] using pr2Newpart0_run (s) (carry) w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 rest hcap hact
  have h1 : runInstructions pr2Newpart1Program {s with pc := N 6193,memory := s.memory,stack := v3::v1::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::w16::rest} = some {s with pc := N 6203,memory := s.memory,stack := v6::w12::w10::v5::v1::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::w16::rest} := by
    simpa only [pr2Newpart1Model,v4,v5,v6] using pr2Newpart1_run (s) v3 v1 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 rest hcap hact
  have h2 : runInstructions pr2Newpart2Program {s with pc := N 6203,memory := s.memory,stack := v6::w12::w10::v5::v1::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::w16::rest} = some {s with pc := N 6213,memory := s.memory,stack := v1::v9::w14::w10::v8::w10::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::w16::rest} := by
    simpa only [pr2Newpart2Model,v7,v8,v9] using pr2Newpart2_run (s) v6 w12 w10 v5 v1 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 rest hcap hact
  have h3 : runInstructions pr2Newpart3Program {s with pc := N 6213,memory := s.memory,stack := v1::v9::w14::w10::v8::w10::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::w16::rest} = some {s with pc := N 6221,memory := v12,stack := v14::w10::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::w16::rest} := by
    simpa only [pr2Newpart3Model,v10,v11,v12,v13,v14] using pr2Newpart3_run (s) v1 v9 w14 w10 v8 w10 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 rest hcap hact
  have h4 : runInstructions pr2Newpart4Program {s with pc := N 6221,memory := v12,stack := v14::w10::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::w16::rest} = some {s with pc := N 6237,memory := v12,stack := v18::v17::v16::v15::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::w16::rest} := by
    simpa only [pr2Newpart4Model,v15,v16,v17,v18] using pr2Newpart4_run ({s with memory := v12}) v14 w10 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 rest hcap hact
  have h5 : runInstructions pr2Newpart5Program {s with pc := N 6237,memory := v12,stack := v18::v17::v16::v15::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::w16::rest} = some {s with pc := N 6245,memory := v12,stack := v21::v19::v16::v15::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::w16::rest} := by
    simpa only [pr2Newpart5Model,v19,v20,v21] using pr2Newpart5_run ({s with memory := v12}) v18 v17 v16 v15 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 rest hcap hact
  have h6 : runInstructions pr2Newpart6Program {s with pc := N 6245,memory := v12,stack := v21::v19::v16::v15::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::w16::rest} = some {s with pc := N 6253,memory := v12,stack := v24::v19::v22::v15::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::w16::rest} := by
    simpa only [pr2Newpart6Model,v22,v23,v24] using pr2Newpart6_run ({s with memory := v12}) v21 v19 v16 v15 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 rest hcap hact
  have h7 : runInstructions pr2Newpart7Program {s with pc := N 6253,memory := v12,stack := v24::v19::v22::v15::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::w16::rest} = some {s with pc := N 6263,memory := v12,stack := v24::w7::w10::v26::v27::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::w16::rest} := by
    simpa only [pr2Newpart7Model,v25,v26,v27] using pr2Newpart7_run ({s with memory := v12}) v24 v19 v22 v15 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 rest hcap hact
  have h8 : runInstructions pr2Newpart8Program {s with pc := N 6263,memory := v12,stack := v24::w7::w10::v26::v27::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::w16::rest} = some {s with pc := N 6273,memory := v12,stack := v32::v31::v29::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::w16::rest} := by
    simpa only [pr2Newpart8Model,v28,v29,v30,v31,v32] using pr2Newpart8_run ({s with memory := v12}) v24 w7 w10 v26 v27 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 rest hcap hact
  have h9 : runInstructions pr2Newpart9Program {s with pc := N 6273,memory := v12,stack := v32::v31::v29::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::w16::rest} = some {s with pc := N 6284,memory := v12,stack := v35::v34::v33::v32::v31::v29::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::w16::rest} := by
    simpa only [pr2Newpart9Model,v33,v34,v35] using pr2Newpart9_run ({s with memory := v12}) v32 v31 v29 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 rest hcap hact
  have h10 : runInstructions pr2Newpart10Program {s with pc := N 6284,memory := v12,stack := v35::v34::v33::v32::v31::v29::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::w16::rest} = some {s with pc := N 6294,memory := v12,stack := v39::v32::v38::v37::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::w16::rest} := by
    simpa only [pr2Newpart10Model,v36,v37,v38,v39] using pr2Newpart10_run ({s with memory := v12}) v35 v34 v33 v32 v31 v29 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 rest hcap hact
  have h11 : runInstructions pr2Newpart11Program {s with pc := N 6294,memory := v12,stack := v39::v32::v38::v37::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::w16::rest} = some {s with pc := N 6302,memory := v12,stack := v43::v41::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::w16::rest} := by
    simpa only [pr2Newpart11Model,v40,v41,v42,v43] using pr2Newpart11_run ({s with memory := v12}) v39 v32 v38 v37 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 rest hcap hact
  have h12 : runInstructions pr2Newpart12Program {s with pc := N 6302,memory := v12,stack := v43::v41::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::w16::rest} = some {s with pc := N 6310,memory := v12,stack := v47::v41::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::w16::rest} := by
    simpa only [pr2Newpart12Model,v44,v45,v46,v47] using pr2Newpart12_run ({s with memory := v12}) v43 v41 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 rest hcap hact
  have h13 : runInstructions pr2Newpart13Program {s with pc := N 6310,memory := v12,stack := v47::v41::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::w16::rest} = some {s with pc := N 6311,memory := v12,stack := w3::v47::v41::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::w16::rest} := by
    simpa only [pr2Newpart13Model] using pr2Newpart13_run ({s with memory := v12}) v47 v41 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 rest hcap hact
  exact (runInstructions_append_some _ _ _ _ _ h0 (runInstructions_append_some _ _ _ _ _ h1 (runInstructions_append_some _ _ _ _ _ h2 (runInstructions_append_some _ _ _ _ _ h3 (runInstructions_append_some _ _ _ _ _ h4 (runInstructions_append_some _ _ _ _ _ h5 (runInstructions_append_some _ _ _ _ _ h6 (runInstructions_append_some _ _ _ _ _ h7 (runInstructions_append_some _ _ _ _ _ h8 (runInstructions_append_some _ _ _ _ _ h9 (runInstructions_append_some _ _ _ _ _ h10 (runInstructions_append_some _ _ _ _ _ h11 (runInstructions_append_some _ _ _ _ _ h12 h13)))))))))))))
#print axioms pr2New_run
def productColumn2Model (s : State) (carry w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 : W) (rest : List W) : State :=
  let v0 : W := carry * w0
  let v1 : W := v0 + w1
  let v2 : W := UInt256.mulMod w11 w15 w10
  let v3 : W := v2 + w2
  let v4 : W := UInt256.mulMod w9 w3 w10
  let v5 : W := v4 + v3
  let v6 : W := MachineState.readWord s.memory 192
  let v7 : W := UInt256.mulMod v6 w12 w10
  let v8 : W := v7 + v5
  let v9 : W := MachineState.readWord s.memory 2720
  let v10 : W := v1 * v9
  let v11 : W := UInt256.land w13 v10
  let v12 : ByteArray := MachineState.writeBytes s.memory (Data.Bytes.natToBytesPadded v11.toNat 32) 0
  let v13 : W := UInt256.mulMod v11 w14 w10
  let v14 : W := v13 + v8
  let v15 : W := UInt256.mulMod (N 2048) v14 w10
  let v16 : W := MachineState.readWord v12 768
  let v17 : W := MachineState.readWord v12 1920
  let v18 : W := v17 * v16
  let v19 : W := v18 + v15
  let v20 : W := UInt256.mulMod v17 v16 w10
  let v21 : W := v20 + v15
  let v22 : W := MachineState.readWord v12 1888
  let v23 : W := v22 * w6
  let v24 : W := v23 + v19
  let v25 : W := UInt256.mulMod v22 w6 w10
  let v26 : W := v25 + v21
  let v27 : W := MachineState.readWord v12 1856
  let v28 : W := v27 * w7
  let v29 : W := v28 + v24
  let v30 : W := UInt256.mulMod v27 w7 w10
  let v31 : W := v30 + v26
  let v32 : W := MachineState.readWord v12 32
  let v33 : W := MachineState.readWord v12 1824
  let v34 : W := v33 * v32
  let v35 : W := v34 + v29
  let v36 : W := UInt256.mulMod v33 v32 w10
  let v37 : W := v36 + v31
  let v38 : W := MachineState.readWord v12 64
  let v39 : W := MachineState.readWord v12 1792
  let v40 : W := v39 * v38
  let v41 : W := v40 + v35
  let v42 : W := UInt256.mulMod v39 v38 w10
  let v43 : W := v42 + v37
  let v44 : W := w11 * w5
  let v45 : W := v44 + v41
  let v46 : W := w9 * w15
  let v47 : W := v46 + v45
  {s with pc := N 6311,memory := v12,stack := w3::v47::v43::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::w16::rest}
def productColumn2Program : List Instr := pr2NewProgram
private theorem aux_shared0 (w10 : W) (z0 z1 : W) :
    (UInt256.mulMod z0 z1 w10) = (UInt256.mulMod z1 z0 w10) := by
  simp (disch := decide) only [addC,addA,addL,mulC,mmC,amC,andC,orC,xorC,eqC,read_disjoint,Challenge.EvmProof.Memory.readWord_writeWord]
private theorem aux_shared1 (z0 z1 : W) :
    (z0 * z1) = (z1 * z0) := by
  simp (disch := decide) only [addC,addA,addL,mulC,mmC,amC,andC,orC,xorC,eqC,read_disjoint,Challenge.EvmProof.Memory.readWord_writeWord]
private theorem aux_shared2 (z0 z1 : W) :
    (z0 + z1) = (z1 + z0) := by
  simp (disch := decide) only [addC,addA,addL,mulC,mmC,amC,andC,orC,xorC,eqC,read_disjoint,Challenge.EvmProof.Memory.readWord_writeWord]
private theorem aux_shared3 (w6 w10 : W) (z0 : W) :
    (UInt256.mulMod w6 z0 w10) = (UInt256.mulMod z0 w6 w10) := by
  simp (disch := decide) only [addC,addA,addL,mulC,mmC,amC,andC,orC,xorC,eqC,read_disjoint,Challenge.EvmProof.Memory.readWord_writeWord]
private theorem aux_shared4 (w6 : W) (z0 : W) :
    (w6 * z0) = (z0 * w6) := by
  simp (disch := decide) only [addC,addA,addL,mulC,mmC,amC,andC,orC,xorC,eqC,read_disjoint,Challenge.EvmProof.Memory.readWord_writeWord]
private theorem prepared_model_eq (s : State) (carry w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 : W) (rest : List W) :
    productColumn2Model s carry w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 rest = pr2NewModel s carry w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 rest := by
  let o0 : W := carry * w0
  let o1 : W := o0 + w1
  let o2 : W := UInt256.mulMod w11 w15 w10
  let o3 : W := o2 + w2
  let o4 : W := UInt256.mulMod w9 w3 w10
  let o5 : W := o4 + o3
  let o6 : W := MachineState.readWord s.memory 192
  let o7 : W := UInt256.mulMod o6 w12 w10
  let o8 : W := o7 + o5
  let o9 : W := MachineState.readWord s.memory 2720
  let o10 : W := o1 * o9
  let o11 : W := UInt256.land w13 o10
  let o12 : ByteArray := MachineState.writeBytes s.memory (Data.Bytes.natToBytesPadded o11.toNat 32) 0
  let o13 : W := UInt256.mulMod o11 w14 w10
  let o14 : W := o13 + o8
  let o15 : W := UInt256.mulMod (N 2048) o14 w10
  let o16 : W := MachineState.readWord o12 768
  let o17 : W := MachineState.readWord o12 1920
  let o18 : W := o17 * o16
  let o19 : W := o18 + o15
  let o20 : W := UInt256.mulMod o17 o16 w10
  let o21 : W := o20 + o15
  let o22 : W := MachineState.readWord o12 1888
  let o23 : W := o22 * w6
  let o24 : W := o23 + o19
  let o25 : W := UInt256.mulMod o22 w6 w10
  let o26 : W := o25 + o21
  let o27 : W := MachineState.readWord o12 1856
  let o28 : W := o27 * w7
  let o29 : W := o28 + o24
  let o30 : W := UInt256.mulMod o27 w7 w10
  let o31 : W := o30 + o26
  let o32 : W := MachineState.readWord o12 32
  let o33 : W := MachineState.readWord o12 1824
  let o34 : W := o33 * o32
  let o35 : W := o34 + o29
  let o36 : W := UInt256.mulMod o33 o32 w10
  let o37 : W := o36 + o31
  let o38 : W := MachineState.readWord o12 64
  let o39 : W := MachineState.readWord o12 1792
  let o40 : W := o39 * o38
  let o41 : W := o40 + o35
  let o42 : W := UInt256.mulMod o39 o38 w10
  let o43 : W := o42 + o37
  let o44 : W := w11 * w5
  let o45 : W := o44 + o41
  let o46 : W := w9 * w15
  let o47 : W := o46 + o45
  let n0 : W := carry * w0
  let n1 : W := n0 + w1
  let n2 : W := UInt256.mulMod w11 w15 w10
  let n3 : W := n2 + w2
  let n4 : W := UInt256.mulMod w9 w3 w10
  let n5 : W := n4 + n3
  let n6 : W := MachineState.readWord s.memory 192
  let n7 : W := UInt256.mulMod n6 w12 w10
  let n8 : W := n7 + n5
  let n9 : W := MachineState.readWord s.memory 2720
  let n10 : W := n1 * n9
  let n11 : W := UInt256.land w13 n10
  let n12 : ByteArray := MachineState.writeBytes s.memory (Data.Bytes.natToBytesPadded n11.toNat 32) 0
  let n13 : W := UInt256.mulMod n11 w14 w10
  let n14 : W := n13 + n8
  let n15 : W := UInt256.mulMod (N 2048) n14 w10
  let n16 : W := MachineState.readWord n12 1888
  let n17 : W := MachineState.readWord n12 768
  let n18 : W := MachineState.readWord n12 1920
  let n19 : W := UInt256.mulMod n17 n18 w10
  let n20 : W := n17 * n18
  let n21 : W := n15 + n20
  let n22 : W := UInt256.mulMod w6 n16 w10
  let n23 : W := w6 * n16
  let n24 : W := n23 + n21
  let n25 : W := n15 + n19
  let n26 : W := n25 + n22
  let n27 : W := MachineState.readWord n12 1856
  let n28 : W := n27 * w7
  let n29 : W := n28 + n24
  let n30 : W := UInt256.mulMod n27 w7 w10
  let n31 : W := n30 + n26
  let n32 : W := MachineState.readWord n12 64
  let n33 : W := MachineState.readWord n12 32
  let n34 : W := MachineState.readWord n12 1824
  let n35 : W := UInt256.mulMod n33 n34 w10
  let n36 : W := n33 * n34
  let n37 : W := MachineState.readWord n12 1792
  let n38 : W := n29 + n36
  let n39 : W := n31 + n35
  let n40 : W := UInt256.mulMod n37 n32 w10
  let n41 : W := n40 + n39
  let n42 : W := n37 * n32
  let n43 : W := n42 + n38
  let n44 : W := w11 * w5
  let n45 : W := n44 + n43
  let n46 : W := w9 * w15
  let n47 : W := n46 + n45
  have eq_n0 : n0 = o0 := by
    simp only [n0,o0]
  have eq_n1 : n1 = o1 := by
    simp only [n1,o1,eq_n0]
  have eq_n2 : n2 = o2 := by
    simp only [n2,o2]
  have eq_n3 : n3 = o3 := by
    simp only [n3,o3,eq_n2]
  have eq_n4 : n4 = o4 := by
    simp only [n4,o4]
  have eq_n5 : n5 = o5 := by
    simp only [n5,o5,eq_n4,eq_n3]
  have eq_n6 : n6 = o6 := by
    simp only [n6,o6]
  have eq_n7 : n7 = o7 := by
    simp only [n7,o7,eq_n6]
  have eq_n8 : n8 = o8 := by
    simp only [n8,o8,eq_n7,eq_n5]
  have eq_n9 : n9 = o9 := by
    simp only [n9,o9]
  have eq_n10 : n10 = o10 := by
    simp only [n10,o10,eq_n1,eq_n9]
  have eq_n11 : n11 = o11 := by
    simp only [n11,o11,eq_n10]
  have eq_n12 : n12 = o12 := by
    simp only [n12,o12,eq_n11]
  have eq_n13 : n13 = o13 := by
    simp only [n13,o13,eq_n11]
  have eq_n14 : n14 = o14 := by
    simp only [n14,o14,eq_n13,eq_n8]
  have eq_n15 : n15 = o15 := by
    simp only [n15,o15,eq_n14]
  have eq_n16 : n16 = o22 := by
    simp only [n16,o22,eq_n12]
  have eq_n17 : n17 = o16 := by
    simp only [n17,o16,eq_n12]
  have eq_n18 : n18 = o17 := by
    simp only [n18,o17,eq_n12]
  have eq_n19 : n19 = o20 := by
    simpa only [n19,o20,eq_n17,eq_n18] using
      (aux_shared0 w10 o16 o17)
  have eq_n20 : n20 = o18 := by
    simpa only [n20,o18,eq_n17,eq_n18] using
      (aux_shared1  o16 o17)
  have eq_n21 : n21 = o19 := by
    simpa only [n21,o19,eq_n15,eq_n20] using
      (aux_shared2  o15 o18)
  have eq_n22 : n22 = o25 := by
    simpa only [n22,o25,eq_n16] using
      (aux_shared3 w6 w10 o22)
  have eq_n23 : n23 = o23 := by
    simpa only [n23,o23,eq_n16] using
      (aux_shared4 w6 o22)
  have eq_n24 : n24 = o24 := by
    simp only [n24,o24,eq_n23,eq_n21]
  have eq_n25 : n25 = o21 := by
    simpa only [n25,o21,eq_n15,eq_n19] using
      (aux_shared2  o15 o20)
  have eq_n26 : n26 = o26 := by
    simpa only [n26,o26,eq_n25,eq_n22] using
      (aux_shared2  o21 o25)
  have eq_n27 : n27 = o27 := by
    simp only [n27,o27,eq_n12]
  have eq_n28 : n28 = o28 := by
    simp only [n28,o28,eq_n27]
  have eq_n29 : n29 = o29 := by
    simp only [n29,o29,eq_n28,eq_n24]
  have eq_n30 : n30 = o30 := by
    simp only [n30,o30,eq_n27]
  have eq_n31 : n31 = o31 := by
    simp only [n31,o31,eq_n30,eq_n26]
  have eq_n32 : n32 = o38 := by
    simp only [n32,o38,eq_n12]
  have eq_n33 : n33 = o32 := by
    simp only [n33,o32,eq_n12]
  have eq_n34 : n34 = o33 := by
    simp only [n34,o33,eq_n12]
  have eq_n35 : n35 = o36 := by
    simpa only [n35,o36,eq_n33,eq_n34] using
      (aux_shared0 w10 o32 o33)
  have eq_n36 : n36 = o34 := by
    simpa only [n36,o34,eq_n33,eq_n34] using
      (aux_shared1  o32 o33)
  have eq_n37 : n37 = o39 := by
    simp only [n37,o39,eq_n12]
  have eq_n38 : n38 = o35 := by
    simpa only [n38,o35,eq_n29,eq_n36] using
      (aux_shared2  o29 o34)
  have eq_n39 : n39 = o37 := by
    simpa only [n39,o37,eq_n31,eq_n35] using
      (aux_shared2  o31 o36)
  have eq_n40 : n40 = o42 := by
    simp only [n40,o42,eq_n37,eq_n32]
  have eq_n41 : n41 = o43 := by
    simp only [n41,o43,eq_n40,eq_n39]
  have eq_n42 : n42 = o40 := by
    simp only [n42,o40,eq_n37,eq_n32]
  have eq_n43 : n43 = o41 := by
    simp only [n43,o41,eq_n42,eq_n38]
  have eq_n44 : n44 = o44 := by
    simp only [n44,o44]
  have eq_n45 : n45 = o45 := by
    simp only [n45,o45,eq_n44,eq_n43]
  have eq_n46 : n46 = o46 := by
    simp only [n46,o46]
  have eq_n47 : n47 = o47 := by
    simp only [n47,o47,eq_n46,eq_n45]
  change {s with pc := N 6311,memory := o12,stack := w3::o47::o43::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::w16::rest} =
    {s with pc := N 6311,memory := n12,stack := w3::n47::n41::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::w16::rest}
  simp only [eq_n0,eq_n1,eq_n2,eq_n3,eq_n4,eq_n5,eq_n6,eq_n7,eq_n8,eq_n9,eq_n10,eq_n11,eq_n12,eq_n13,eq_n14,eq_n15,eq_n16,eq_n17,eq_n18,eq_n19,eq_n20,eq_n21,eq_n22,eq_n23,eq_n24,eq_n25,eq_n26,eq_n27,eq_n28,eq_n29,eq_n30,eq_n31,eq_n32,eq_n33,eq_n34,eq_n35,eq_n36,eq_n37,eq_n38,eq_n39,eq_n40,eq_n41,eq_n42,eq_n43,eq_n44,eq_n45,eq_n46,eq_n47]
theorem productColumn2_run (s : State) (carry w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions productColumn2Program {s with pc := N 6185,stack := carry::w0::w1::w2::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::w16::rest} =
      some (productColumn2Model s carry w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 rest) := by
  exact (pr2New_run s carry w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 rest hcap hact).trans
    (congrArg some (prepared_model_eq s carry w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 rest).symm)
#print axioms productColumn2_run
end CycleSubmission.Execution
