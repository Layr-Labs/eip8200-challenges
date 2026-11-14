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
def pr13Newpart0Program : List Instr :=
  [
  .push 2 1920,
   .op .MLOAD,
   .op (.Swap sA3),
   .op (.Dup dA1),
   .op (.Dup dA5),
   .op .MUL,
   .op .ADD,
   .op (.Swap sA3)]
def pr13Newpart0Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 : W) (rest : List W) : State :=
  let v0 : W := MachineState.readWord s.memory 1920
  let v1 : W := v0 * x0
  let v2 : W := v1 + x3
  {s with pc := N 7588,memory := s.memory,stack := v0::x0::x1::x2::v2::x4::x5::x6::x7::x8::x9::x10::x11::x12::x13::x14::x15::x16::x17::rest}
theorem pr13Newpart0_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions pr13Newpart0Program {s with pc := N 7578,stack := x0::x1::x2::x3::x4::x5::x6::x7::x8::x9::x10::x11::x12::x13::x14::x15::x16::x17::rest} =
      some (pr13Newpart0Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 21) : rest.length + j < 1024 := by omega
  have ha1920 : (1920 : W).toNat = 1920 := rfl
  have hf1920 := Monpro.activeWords_fix s 1920 32 (by decide) (by norm_num) hact
  simp [hz,hzn,pr13Newpart0Program,pr13Newpart0Model,runInstructions,runInstr,List.exchange,succ_ofNat_mod,ofNat_add_mod,Nat.add_assoc,State.activeWordsAfterUInt256,literal_eq_ofNat,capacity,ha1920,hf1920]
def pr13Newpart1Program : List Instr :=
  [
  .op .MULMOD,
   .op .ADD,
   .push 1 160,
   .op .MLOAD,
   .push 2 1888,
   .op .MLOAD,
   .op (.Dup dA11),
   .op (.Dup dA1)]
def pr13Newpart1Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 : W) (rest : List W) : State :=
  let v0 : W := UInt256.mulMod x0 x1 x2
  let v1 : W := v0 + x3
  let v2 : W := MachineState.readWord s.memory 160
  let v3 : W := MachineState.readWord s.memory 1888
  {s with pc := N 7599,memory := s.memory,stack := v3::x12::v3::v2::v1::x4::x5::x6::x7::x8::x9::x10::x11::x12::x13::x14::x15::x16::x17::x18::rest}
theorem pr13Newpart1_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions pr13Newpart1Program {s with pc := N 7588,stack := x0::x1::x2::x3::x4::x5::x6::x7::x8::x9::x10::x11::x12::x13::x14::x15::x16::x17::x18::rest} =
      some (pr13Newpart1Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 20) : rest.length + j < 1024 := by omega
  have ha160 : (160 : W).toNat = 160 := rfl
  have hf160 := Monpro.activeWords_fix s 160 32 (by decide) (by norm_num) hact
  have ha1888 : (1888 : W).toNat = 1888 := rfl
  have hf1888 := Monpro.activeWords_fix s 1888 32 (by decide) (by norm_num) hact
  simp [hz,hzn,pr13Newpart1Program,pr13Newpart1Model,runInstructions,runInstr,List.exchange,succ_ofNat_mod,ofNat_add_mod,Nat.add_assoc,State.activeWordsAfterUInt256,literal_eq_ofNat,capacity,ha160,hf160,ha1888,hf1888]
def pr13Newpart2Program : List Instr :=
  [
  .op (.Dup dA3),
   .op .MULMOD,
   .op (.Swap sA1),
   .op .MUL,
   .push 2 1856,
   .op .MLOAD,
   .op (.Swap sA3),
   .op .ADD]
def pr13Newpart2Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 : W) (rest : List W) : State :=
  let v0 : W := UInt256.mulMod x3 x0 x1
  let v1 : W := x3 * x2
  let v2 : W := MachineState.readWord s.memory 1856
  let v3 : W := x5 + v1
  {s with pc := N 7609,memory := s.memory,stack := v3::v0::x4::v2::x6::x7::x8::x9::x10::x11::x12::x13::x14::x15::x16::x17::x18::x19::rest}
theorem pr13Newpart2_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions pr13Newpart2Program {s with pc := N 7599,stack := x0::x1::x2::x3::x4::x5::x6::x7::x8::x9::x10::x11::x12::x13::x14::x15::x16::x17::x18::x19::rest} =
      some (pr13Newpart2Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 21) : rest.length + j < 1024 := by omega
  have ha1856 : (1856 : W).toNat = 1856 := rfl
  have hf1856 := Monpro.activeWords_fix s 1856 32 (by decide) (by norm_num) hact
  simp [hz,hzn,pr13Newpart2Program,pr13Newpart2Model,runInstructions,runInstr,List.exchange,succ_ofNat_mod,ofNat_add_mod,Nat.add_assoc,State.activeWordsAfterUInt256,literal_eq_ofNat,capacity,ha1856,hf1856]
def pr13Newpart3Program : List Instr :=
  [
  .op (.Swap sA1),
   .op .ADD,
   .op (.Dup dA10),
   .op (.Dup dA3),
   .op (.Dup dA5),
   .op .MULMOD,
   .op .ADD,
   .op (.Swap sA1)]
def pr13Newpart3Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 : W) (rest : List W) : State :=
  let v0 : W := x2 + x1
  let v1 : W := UInt256.mulMod x4 x3 x11
  let v2 : W := v1 + v0
  {s with pc := N 7617,memory := s.memory,stack := x3::x0::v2::x4::x5::x6::x7::x8::x9::x10::x11::x12::x13::x14::x15::x16::x17::rest}
theorem pr13Newpart3_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions pr13Newpart3Program {s with pc := N 7609,stack := x0::x1::x2::x3::x4::x5::x6::x7::x8::x9::x10::x11::x12::x13::x14::x15::x16::x17::rest} =
      some (pr13Newpart3Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 20) : rest.length + j < 1024 := by omega
  simp [hz,hzn,pr13Newpart3Program,pr13Newpart3Model,runInstructions,runInstr,List.exchange,succ_ofNat_mod,ofNat_add_mod,Nat.add_assoc,State.activeWordsAfterUInt256,literal_eq_ofNat,capacity]
def pr13Newpart4Program : List Instr :=
  [
  .op (.Dup dA3),
   .op .MUL,
   .op .ADD,
   .push 1 192,
   .op .MLOAD,
   .op (.Dup dA11),
   .op .MUL,
   .op .ADD]
def pr13Newpart4Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 : W) (rest : List W) : State :=
  let v0 : W := x3 * x0
  let v1 : W := v0 + x1
  let v2 : W := MachineState.readWord s.memory 192
  let v3 : W := x11 * v2
  let v4 : W := v3 + v1
  {s with pc := N 7626,memory := s.memory,stack := v4::x2::x3::x4::x5::x6::x7::x8::x9::x10::x11::x12::x13::x14::x15::x16::rest}
theorem pr13Newpart4_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions pr13Newpart4Program {s with pc := N 7617,stack := x0::x1::x2::x3::x4::x5::x6::x7::x8::x9::x10::x11::x12::x13::x14::x15::x16::rest} =
      some (pr13Newpart4Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 18) : rest.length + j < 1024 := by omega
  have ha192 : (192 : W).toNat = 192 := rfl
  have hf192 := Monpro.activeWords_fix s 192 32 (by decide) (by norm_num) hact
  simp [hz,hzn,pr13Newpart4Program,pr13Newpart4Model,runInstructions,runInstr,List.exchange,succ_ofNat_mod,ofNat_add_mod,Nat.add_assoc,State.activeWordsAfterUInt256,literal_eq_ofNat,capacity,ha192,hf192]
def pr13Newpart5Program : List Instr :=
  [
  .push 0 0,
   .op .MLOAD,
   .op (.Dup dA9),
   .op .MUL,
   .op .ADD,
   .push 1 224,
   .op .MLOAD,
   .op (.Dup dA4)]
def pr13Newpart5Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 : W) (rest : List W) : State :=
  let v0 : W := MachineState.readWord s.memory 0
  let v1 : W := x8 * v0
  let v2 : W := v1 + x0
  let v3 : W := MachineState.readWord s.memory 224
  {s with pc := N 7635,memory := s.memory,stack := x3::v3::v2::x1::x2::x3::x4::x5::x6::x7::x8::x9::x10::x11::x12::x13::x14::x15::rest}
theorem pr13Newpart5_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions pr13Newpart5Program {s with pc := N 7626,stack := x0::x1::x2::x3::x4::x5::x6::x7::x8::x9::x10::x11::x12::x13::x14::x15::rest} =
      some (pr13Newpart5Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 18) : rest.length + j < 1024 := by omega
  have ha0 : (0 : W).toNat = 0 := rfl
  have hf0 := Monpro.activeWords_fix s 0 32 (by decide) (by norm_num) hact
  have ha224 : (224 : W).toNat = 224 := rfl
  have hf224 := Monpro.activeWords_fix s 224 32 (by decide) (by norm_num) hact
  simp [hz,hzn,pr13Newpart5Program,pr13Newpart5Model,runInstructions,runInstr,List.exchange,succ_ofNat_mod,ofNat_add_mod,Nat.add_assoc,State.activeWordsAfterUInt256,literal_eq_ofNat,capacity,ha0,hf0,ha224,hf224]
def pr13Newpart6Program : List Instr :=
  [
  .op .MUL,
   .op .ADD,
   .op (.Dup dA6),
   .op (.Dup dA8),
   .op .MUL,
   .op .ADD,
   .op (.Dup dA5),
   .op (.Dup dA5)]
def pr13Newpart6Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 : W) (rest : List W) : State :=
  let v0 : W := x0 * x1
  let v1 : W := v0 + x2
  let v2 : W := x9 * x8
  let v3 : W := v2 + v1
  {s with pc := N 7643,memory := s.memory,stack := x6::x7::v3::x3::x4::x5::x6::x7::x8::x9::x10::x11::x12::x13::x14::x15::x16::x17::rest}
theorem pr13Newpart6_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions pr13Newpart6Program {s with pc := N 7635,stack := x0::x1::x2::x3::x4::x5::x6::x7::x8::x9::x10::x11::x12::x13::x14::x15::x16::x17::rest} =
      some (pr13Newpart6Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 18) : rest.length + j < 1024 := by omega
  simp [hz,hzn,pr13Newpart6Program,pr13Newpart6Model,runInstructions,runInstr,List.exchange,succ_ofNat_mod,ofNat_add_mod,Nat.add_assoc,State.activeWordsAfterUInt256,literal_eq_ofNat,capacity]
def pr13Newpart7Program : List Instr :=
  [
  .op .MUL,
   .op .ADD,
   .op (.Dup dA11),
   .op (.Dup dA15),
   .op .MUL,
   .op .ADD,
   .op (.Dup dA15),
   .op (.Dup dA14)]
def pr13Newpart7Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 : W) (rest : List W) : State :=
  let v0 : W := x0 * x1
  let v1 : W := v0 + x2
  let v2 : W := x16 * x13
  let v3 : W := v2 + v1
  {s with pc := N 7651,memory := s.memory,stack := x15::x17::v3::x3::x4::x5::x6::x7::x8::x9::x10::x11::x12::x13::x14::x15::x16::x17::rest}
theorem pr13Newpart7_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions pr13Newpart7Program {s with pc := N 7643,stack := x0::x1::x2::x3::x4::x5::x6::x7::x8::x9::x10::x11::x12::x13::x14::x15::x16::x17::rest} =
      some (pr13Newpart7Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 18) : rest.length + j < 1024 := by omega
  simp [hz,hzn,pr13Newpart7Program,pr13Newpart7Model,runInstructions,runInstr,List.exchange,succ_ofNat_mod,ofNat_add_mod,Nat.add_assoc,State.activeWordsAfterUInt256,literal_eq_ofNat,capacity]
def pr13Newpart8Program : List Instr :=
  [
  .op .MUL,
   .op .ADD,
   .op (.Swap sA0),
   .op (.Dup dA9),
   .push 1 192,
   .op .MLOAD,
   .op (.Dup dA12),
   .op .MULMOD]
def pr13Newpart8Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 : W) (rest : List W) : State :=
  let v0 : W := x0 * x1
  let v1 : W := v0 + x2
  let v2 : W := MachineState.readWord s.memory 192
  let v3 : W := UInt256.mulMod x12 v2 x11
  {s with pc := N 7660,memory := s.memory,stack := v3::x3::v1::x4::x5::x6::x7::x8::x9::x10::x11::x12::x13::x14::x15::x16::x17::rest}
theorem pr13Newpart8_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions pr13Newpart8Program {s with pc := N 7651,stack := x0::x1::x2::x3::x4::x5::x6::x7::x8::x9::x10::x11::x12::x13::x14::x15::x16::x17::rest} =
      some (pr13Newpart8Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 19) : rest.length + j < 1024 := by omega
  have ha192 : (192 : W).toNat = 192 := rfl
  have hf192 := Monpro.activeWords_fix s 192 32 (by decide) (by norm_num) hact
  simp [hz,hzn,pr13Newpart8Program,pr13Newpart8Model,runInstructions,runInstr,List.exchange,succ_ofNat_mod,ofNat_add_mod,Nat.add_assoc,State.activeWordsAfterUInt256,literal_eq_ofNat,capacity,ha192,hf192]
def pr13Newpart9Program : List Instr :=
  [
  .op .ADD,
   .op (.Dup dA9),
   .push 0 0,
   .op .MLOAD,
   .op (.Dup dA10),
   .op .MULMOD,
   .op .ADD,
   .op (.Dup dA9)]
def pr13Newpart9Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 : W) (rest : List W) : State :=
  let v0 : W := x0 + x1
  let v1 : W := MachineState.readWord s.memory 0
  let v2 : W := UInt256.mulMod x9 v1 x10
  let v3 : W := v2 + v0
  {s with pc := N 7668,memory := s.memory,stack := x10::v3::x2::x3::x4::x5::x6::x7::x8::x9::x10::x11::x12::x13::x14::x15::x16::rest}
theorem pr13Newpart9_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions pr13Newpart9Program {s with pc := N 7660,stack := x0::x1::x2::x3::x4::x5::x6::x7::x8::x9::x10::x11::x12::x13::x14::x15::x16::rest} =
      some (pr13Newpart9Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 19) : rest.length + j < 1024 := by omega
  have ha0 : (0 : W).toNat = 0 := rfl
  have hf0 := Monpro.activeWords_fix s 0 32 (by decide) (by norm_num) hact
  simp [hz,hzn,pr13Newpart9Program,pr13Newpart9Model,runInstructions,runInstr,List.exchange,succ_ofNat_mod,ofNat_add_mod,Nat.add_assoc,State.activeWordsAfterUInt256,literal_eq_ofNat,capacity,ha0,hf0]
def pr13Newpart10Program : List Instr :=
  [
  .push 1 224,
   .op .MLOAD,
   .op (.Dup dA5),
   .op .MULMOD,
   .op .ADD,
   .op (.Dup dA9),
   .op (.Dup dA7),
   .op (.Dup dA9)]
def pr13Newpart10Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 : W) (rest : List W) : State :=
  let v0 : W := MachineState.readWord s.memory 224
  let v1 : W := UInt256.mulMod x4 v0 x0
  let v2 : W := v1 + x1
  {s with pc := N 7677,memory := s.memory,stack := x8::x7::x10::v2::x2::x3::x4::x5::x6::x7::x8::x9::x10::x11::x12::x13::x14::x15::x16::rest}
theorem pr13Newpart10_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions pr13Newpart10Program {s with pc := N 7668,stack := x0::x1::x2::x3::x4::x5::x6::x7::x8::x9::x10::x11::x12::x13::x14::x15::x16::rest} =
      some (pr13Newpart10Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 19) : rest.length + j < 1024 := by omega
  have ha224 : (224 : W).toNat = 224 := rfl
  have hf224 := Monpro.activeWords_fix s 224 32 (by decide) (by norm_num) hact
  simp [hz,hzn,pr13Newpart10Program,pr13Newpart10Model,runInstructions,runInstr,List.exchange,succ_ofNat_mod,ofNat_add_mod,Nat.add_assoc,State.activeWordsAfterUInt256,literal_eq_ofNat,capacity,ha224,hf224]
def pr13Newpart11Program : List Instr :=
  [
  .op .MULMOD,
   .op .ADD,
   .op (.Dup dA9),
   .op (.Dup dA6),
   .op (.Dup dA6),
   .op .MULMOD,
   .op .ADD,
   .op (.Dup dA9)]
def pr13Newpart11Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 : W) (rest : List W) : State :=
  let v0 : W := UInt256.mulMod x0 x1 x2
  let v1 : W := v0 + x3
  let v2 : W := UInt256.mulMod x7 x8 x12
  let v3 : W := v2 + v1
  {s with pc := N 7685,memory := s.memory,stack := x12::v3::x4::x5::x6::x7::x8::x9::x10::x11::x12::x13::x14::x15::x16::x17::x18::rest}
theorem pr13Newpart11_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions pr13Newpart11Program {s with pc := N 7677,stack := x0::x1::x2::x3::x4::x5::x6::x7::x8::x9::x10::x11::x12::x13::x14::x15::x16::x17::x18::rest} =
      some (pr13Newpart11Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 19) : rest.length + j < 1024 := by omega
  simp [hz,hzn,pr13Newpart11Program,pr13Newpart11Model,runInstructions,runInstr,List.exchange,succ_ofNat_mod,ofNat_add_mod,Nat.add_assoc,State.activeWordsAfterUInt256,literal_eq_ofNat,capacity]
def pr13Newpart12Program : List Instr :=
  [
  .op (.Dup dA15),
   .op (.Dup dA13),
   .op .MULMOD,
   .op .ADD,
   .op (.Dup dA15),
   .op (.Dup dA10),
   .op (.Swap sA0),
   .op (.Dup dA15)]
def pr13Newpart12Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 : W) (rest : List W) : State :=
  let v0 : W := UInt256.mulMod x12 x15 x0
  let v1 : W := v0 + x1
  {s with pc := N 7693,memory := s.memory,stack := x14::x16::x10::v1::x2::x3::x4::x5::x6::x7::x8::x9::x10::x11::x12::x13::x14::x15::x16::rest}
theorem pr13Newpart12_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions pr13Newpart12Program {s with pc := N 7685,stack := x0::x1::x2::x3::x4::x5::x6::x7::x8::x9::x10::x11::x12::x13::x14::x15::x16::rest} =
      some (pr13Newpart12Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 19) : rest.length + j < 1024 := by omega
  simp [hz,hzn,pr13Newpart12Program,pr13Newpart12Model,runInstructions,runInstr,List.exchange,succ_ofNat_mod,ofNat_add_mod,Nat.add_assoc,State.activeWordsAfterUInt256,literal_eq_ofNat,capacity]
def pr13Newpart13Program : List Instr :=
  [
  .op .MULMOD,
   .op .ADD]
def pr13Newpart13Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 : W) (rest : List W) : State :=
  let v0 : W := UInt256.mulMod x0 x1 x2
  let v1 : W := v0 + x3
  {s with pc := N 7695,memory := s.memory,stack := v1::x4::x5::x6::x7::x8::x9::x10::x11::x12::x13::x14::x15::x16::x17::x18::rest}
theorem pr13Newpart13_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions pr13Newpart13Program {s with pc := N 7693,stack := x0::x1::x2::x3::x4::x5::x6::x7::x8::x9::x10::x11::x12::x13::x14::x15::x16::x17::x18::rest} =
      some (pr13Newpart13Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 19) : rest.length + j < 1024 := by omega
  simp [hz,hzn,pr13Newpart13Program,pr13Newpart13Model,runInstructions,runInstr,List.exchange,succ_ofNat_mod,ofNat_add_mod,Nat.add_assoc,State.activeWordsAfterUInt256,literal_eq_ofNat,capacity]
def pr13NewProgram : List Instr :=
  [
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
   .push 1 160,
   .op .MLOAD,
   .push 2 1888,
   .op .MLOAD,
   .op (.Dup dA11),
   .op (.Dup dA1),
   .op (.Dup dA3),
   .op .MULMOD,
   .op (.Swap sA1),
   .op .MUL,
   .push 2 1856,
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
   .push 1 192,
   .op .MLOAD,
   .op (.Dup dA11),
   .op .MUL,
   .op .ADD,
   .push 0 0,
   .op .MLOAD,
   .op (.Dup dA9),
   .op .MUL,
   .op .ADD,
   .push 1 224,
   .op .MLOAD,
   .op (.Dup dA4),
   .op .MUL,
   .op .ADD,
   .op (.Dup dA6),
   .op (.Dup dA8),
   .op .MUL,
   .op .ADD,
   .op (.Dup dA5),
   .op (.Dup dA5),
   .op .MUL,
   .op .ADD,
   .op (.Dup dA11),
   .op (.Dup dA15),
   .op .MUL,
   .op .ADD,
   .op (.Dup dA15),
   .op (.Dup dA14),
   .op .MUL,
   .op .ADD,
   .op (.Swap sA0),
   .op (.Dup dA9),
   .push 1 192,
   .op .MLOAD,
   .op (.Dup dA12),
   .op .MULMOD,
   .op .ADD,
   .op (.Dup dA9),
   .push 0 0,
   .op .MLOAD,
   .op (.Dup dA10),
   .op .MULMOD,
   .op .ADD,
   .op (.Dup dA9),
   .push 1 224,
   .op .MLOAD,
   .op (.Dup dA5),
   .op .MULMOD,
   .op .ADD,
   .op (.Dup dA9),
   .op (.Dup dA7),
   .op (.Dup dA9),
   .op .MULMOD,
   .op .ADD,
   .op (.Dup dA9),
   .op (.Dup dA6),
   .op (.Dup dA6),
   .op .MULMOD,
   .op .ADD,
   .op (.Dup dA9),
   .op (.Dup dA15),
   .op (.Dup dA13),
   .op .MULMOD,
   .op .ADD,
   .op (.Dup dA15),
   .op (.Dup dA10),
   .op (.Swap sA0),
   .op (.Dup dA15),
   .op .MULMOD,
   .op .ADD]
def pr13NewModel (s : State) (carry w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 : W) (rest : List W) : State :=
  let v0 : W := MachineState.readWord s.memory 1920
  let v1 : W := v0 * carry
  let v2 : W := v1 + w2
  let v3 : W := UInt256.mulMod v0 carry w0
  let v4 : W := v3 + w1
  let v5 : W := MachineState.readWord s.memory 160
  let v6 : W := MachineState.readWord s.memory 1888
  let v7 : W := UInt256.mulMod v5 v6 w10
  let v8 : W := v5 * v6
  let v9 : W := MachineState.readWord s.memory 1856
  let v10 : W := v2 + v8
  let v11 : W := v4 + v7
  let v12 : W := UInt256.mulMod w3 v9 w10
  let v13 : W := v12 + v11
  let v14 : W := w3 * v9
  let v15 : W := v14 + v10
  let v16 : W := MachineState.readWord s.memory 192
  let v17 : W := w11 * v16
  let v18 : W := v17 + v15
  let v19 : W := MachineState.readWord s.memory 0
  let v20 : W := w9 * v19
  let v21 : W := v20 + v18
  let v22 : W := MachineState.readWord s.memory 224
  let v23 : W := w4 * v22
  let v24 : W := v23 + v21
  let v25 : W := w8 * w7
  let v26 : W := v25 + v24
  let v27 : W := w5 * w6
  let v28 : W := v27 + v26
  let v29 : W := w15 * w12
  let v30 : W := v29 + v28
  let v31 : W := w14 * w16
  let v32 : W := v31 + v30
  let v33 : W := MachineState.readWord s.memory 192
  let v34 : W := UInt256.mulMod w11 v33 w10
  let v35 : W := v34 + v13
  let v36 : W := MachineState.readWord s.memory 0
  let v37 : W := UInt256.mulMod w9 v36 w10
  let v38 : W := v37 + v35
  let v39 : W := MachineState.readWord s.memory 224
  let v40 : W := UInt256.mulMod w4 v39 w10
  let v41 : W := v40 + v38
  let v42 : W := UInt256.mulMod w8 w7 w10
  let v43 : W := v42 + v41
  let v44 : W := UInt256.mulMod w5 w6 w10
  let v45 : W := v44 + v43
  let v46 : W := UInt256.mulMod w12 w15 w10
  let v47 : W := v46 + v45
  let v48 : W := UInt256.mulMod w14 w16 w10
  let v49 : W := v48 + v47
  {s with pc := N 7695,memory := s.memory,stack := v49::v32::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::w16::rest}
theorem pr13New_run (s : State) (carry w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions pr13NewProgram {s with pc := N 7578,stack := carry::w0::w1::w2::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::w16::rest} =
      some (pr13NewModel s carry w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 rest) := by
  let v0 : W := MachineState.readWord s.memory 1920
  let v1 : W := v0 * carry
  let v2 : W := v1 + w2
  let v3 : W := UInt256.mulMod v0 carry w0
  let v4 : W := v3 + w1
  let v5 : W := MachineState.readWord s.memory 160
  let v6 : W := MachineState.readWord s.memory 1888
  let v7 : W := UInt256.mulMod v5 v6 w10
  let v8 : W := v5 * v6
  let v9 : W := MachineState.readWord s.memory 1856
  let v10 : W := v2 + v8
  let v11 : W := v4 + v7
  let v12 : W := UInt256.mulMod w3 v9 w10
  let v13 : W := v12 + v11
  let v14 : W := w3 * v9
  let v15 : W := v14 + v10
  let v16 : W := MachineState.readWord s.memory 192
  let v17 : W := w11 * v16
  let v18 : W := v17 + v15
  let v19 : W := MachineState.readWord s.memory 0
  let v20 : W := w9 * v19
  let v21 : W := v20 + v18
  let v22 : W := MachineState.readWord s.memory 224
  let v23 : W := w4 * v22
  let v24 : W := v23 + v21
  let v25 : W := w8 * w7
  let v26 : W := v25 + v24
  let v27 : W := w5 * w6
  let v28 : W := v27 + v26
  let v29 : W := w15 * w12
  let v30 : W := v29 + v28
  let v31 : W := w14 * w16
  let v32 : W := v31 + v30
  let v33 : W := MachineState.readWord s.memory 192
  let v34 : W := UInt256.mulMod w11 v33 w10
  let v35 : W := v34 + v13
  let v36 : W := MachineState.readWord s.memory 0
  let v37 : W := UInt256.mulMod w9 v36 w10
  let v38 : W := v37 + v35
  let v39 : W := MachineState.readWord s.memory 224
  let v40 : W := UInt256.mulMod w4 v39 w10
  let v41 : W := v40 + v38
  let v42 : W := UInt256.mulMod w8 w7 w10
  let v43 : W := v42 + v41
  let v44 : W := UInt256.mulMod w5 w6 w10
  let v45 : W := v44 + v43
  let v46 : W := UInt256.mulMod w12 w15 w10
  let v47 : W := v46 + v45
  let v48 : W := UInt256.mulMod w14 w16 w10
  let v49 : W := v48 + v47
  have h0 : runInstructions pr13Newpart0Program {s with pc := N 7578,memory := s.memory,stack := carry::w0::w1::w2::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::w16::rest} = some {s with pc := N 7588,memory := s.memory,stack := v0::carry::w0::w1::v2::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::w16::rest} := by
    simpa only [pr13Newpart0Model,v0,v1,v2] using pr13Newpart0_run (s) (carry) w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 rest hcap hact
  have h1 : runInstructions pr13Newpart1Program {s with pc := N 7588,memory := s.memory,stack := v0::carry::w0::w1::v2::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::w16::rest} = some {s with pc := N 7599,memory := s.memory,stack := v6::w10::v6::v5::v4::v2::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::w16::rest} := by
    simpa only [pr13Newpart1Model,v3,v4,v5,v6] using pr13Newpart1_run (s) v0 (carry) w0 w1 v2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 rest hcap hact
  have h2 : runInstructions pr13Newpart2Program {s with pc := N 7599,memory := s.memory,stack := v6::w10::v6::v5::v4::v2::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::w16::rest} = some {s with pc := N 7609,memory := s.memory,stack := v10::v7::v4::v9::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::w16::rest} := by
    simpa only [pr13Newpart2Model,v7,v8,v9,v10] using pr13Newpart2_run (s) v6 w10 v6 v5 v4 v2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 rest hcap hact
  have h3 : runInstructions pr13Newpart3Program {s with pc := N 7609,memory := s.memory,stack := v10::v7::v4::v9::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::w16::rest} = some {s with pc := N 7617,memory := s.memory,stack := v9::v10::v13::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::w16::rest} := by
    simpa only [pr13Newpart3Model,v11,v12,v13] using pr13Newpart3_run (s) v10 v7 v4 v9 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 rest hcap hact
  have h4 : runInstructions pr13Newpart4Program {s with pc := N 7617,memory := s.memory,stack := v9::v10::v13::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::w16::rest} = some {s with pc := N 7626,memory := s.memory,stack := v18::v13::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::w16::rest} := by
    simpa only [pr13Newpart4Model,v14,v15,v16,v17,v18] using pr13Newpart4_run (s) v9 v10 v13 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 rest hcap hact
  have h5 : runInstructions pr13Newpart5Program {s with pc := N 7626,memory := s.memory,stack := v18::v13::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::w16::rest} = some {s with pc := N 7635,memory := s.memory,stack := w4::v22::v21::v13::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::w16::rest} := by
    simpa only [pr13Newpart5Model,v19,v20,v21,v22] using pr13Newpart5_run (s) v18 v13 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 rest hcap hact
  have h6 : runInstructions pr13Newpart6Program {s with pc := N 7635,memory := s.memory,stack := w4::v22::v21::v13::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::w16::rest} = some {s with pc := N 7643,memory := s.memory,stack := w5::w6::v26::v13::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::w16::rest} := by
    simpa only [pr13Newpart6Model,v23,v24,v25,v26] using pr13Newpart6_run (s) w4 v22 v21 v13 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 rest hcap hact
  have h7 : runInstructions pr13Newpart7Program {s with pc := N 7643,memory := s.memory,stack := w5::w6::v26::v13::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::w16::rest} = some {s with pc := N 7651,memory := s.memory,stack := w14::w16::v30::v13::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::w16::rest} := by
    simpa only [pr13Newpart7Model,v27,v28,v29,v30] using pr13Newpart7_run (s) w5 w6 v26 v13 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 rest hcap hact
  have h8 : runInstructions pr13Newpart8Program {s with pc := N 7651,memory := s.memory,stack := w14::w16::v30::v13::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::w16::rest} = some {s with pc := N 7660,memory := s.memory,stack := v34::v13::v32::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::w16::rest} := by
    simpa only [pr13Newpart8Model,v31,v32,v33,v34] using pr13Newpart8_run (s) w14 w16 v30 v13 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 rest hcap hact
  have h9 : runInstructions pr13Newpart9Program {s with pc := N 7660,memory := s.memory,stack := v34::v13::v32::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::w16::rest} = some {s with pc := N 7668,memory := s.memory,stack := w10::v38::v32::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::w16::rest} := by
    simpa only [pr13Newpart9Model,v35,v36,v37,v38] using pr13Newpart9_run (s) v34 v13 v32 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 rest hcap hact
  have h10 : runInstructions pr13Newpart10Program {s with pc := N 7668,memory := s.memory,stack := w10::v38::v32::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::w16::rest} = some {s with pc := N 7677,memory := s.memory,stack := w8::w7::w10::v41::v32::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::w16::rest} := by
    simpa only [pr13Newpart10Model,v39,v40,v41] using pr13Newpart10_run (s) w10 v38 v32 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 rest hcap hact
  have h11 : runInstructions pr13Newpart11Program {s with pc := N 7677,memory := s.memory,stack := w8::w7::w10::v41::v32::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::w16::rest} = some {s with pc := N 7685,memory := s.memory,stack := w10::v45::v32::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::w16::rest} := by
    simpa only [pr13Newpart11Model,v42,v43,v44,v45] using pr13Newpart11_run (s) w8 w7 w10 v41 v32 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 rest hcap hact
  have h12 : runInstructions pr13Newpart12Program {s with pc := N 7685,memory := s.memory,stack := w10::v45::v32::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::w16::rest} = some {s with pc := N 7693,memory := s.memory,stack := w14::w16::w10::v47::v32::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::w16::rest} := by
    simpa only [pr13Newpart12Model,v46,v47] using pr13Newpart12_run (s) w10 v45 v32 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 rest hcap hact
  have h13 : runInstructions pr13Newpart13Program {s with pc := N 7693,memory := s.memory,stack := w14::w16::w10::v47::v32::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::w16::rest} = some {s with pc := N 7695,memory := s.memory,stack := v49::v32::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::w16::rest} := by
    simpa only [pr13Newpart13Model,v48,v49] using pr13Newpart13_run (s) w14 w16 w10 v47 v32 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 rest hcap hact
  exact (runInstructions_append_some _ _ _ _ _ h0 (runInstructions_append_some _ _ _ _ _ h1 (runInstructions_append_some _ _ _ _ _ h2 (runInstructions_append_some _ _ _ _ _ h3 (runInstructions_append_some _ _ _ _ _ h4 (runInstructions_append_some _ _ _ _ _ h5 (runInstructions_append_some _ _ _ _ _ h6 (runInstructions_append_some _ _ _ _ _ h7 (runInstructions_append_some _ _ _ _ _ h8 (runInstructions_append_some _ _ _ _ _ h9 (runInstructions_append_some _ _ _ _ _ h10 (runInstructions_append_some _ _ _ _ _ h11 (runInstructions_append_some _ _ _ _ _ h12 h13)))))))))))))
#print axioms pr13New_run
def productColumn13Model (s : State) (carry w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 : W) (rest : List W) : State :=
  let v0 : W := MachineState.readWord s.memory 1920
  let v1 : W := v0 * carry
  let v2 : W := v1 + w2
  let v3 : W := UInt256.mulMod v0 carry w0
  let v4 : W := v3 + w1
  let v5 : W := MachineState.readWord s.memory 160
  let v6 : W := MachineState.readWord s.memory 1888
  let v7 : W := v6 * v5
  let v8 : W := v7 + v2
  let v9 : W := UInt256.mulMod v6 v5 w10
  let v10 : W := v9 + v4
  let v11 : W := MachineState.readWord s.memory 1856
  let v12 : W := v11 * w3
  let v13 : W := v12 + v8
  let v14 : W := UInt256.mulMod v11 w3 w10
  let v15 : W := v14 + v10
  let v16 : W := MachineState.readWord s.memory 192
  let v17 : W := w11 * v16
  let v18 : W := v17 + v13
  let v19 : W := MachineState.readWord s.memory 0
  let v20 : W := w9 * v19
  let v21 : W := v20 + v18
  let v22 : W := MachineState.readWord s.memory 224
  let v23 : W := w4 * v22
  let v24 : W := v23 + v21
  let v25 : W := w8 * w7
  let v26 : W := v25 + v24
  let v27 : W := w5 * w6
  let v28 : W := v27 + v26
  let v29 : W := w15 * w12
  let v30 : W := v29 + v28
  let v31 : W := w14 * w16
  let v32 : W := v31 + v30
  let v33 : W := MachineState.readWord s.memory 192
  let v34 : W := UInt256.mulMod w11 v33 w10
  let v35 : W := v34 + v15
  let v36 : W := MachineState.readWord s.memory 0
  let v37 : W := UInt256.mulMod w9 v36 w10
  let v38 : W := v37 + v35
  let v39 : W := MachineState.readWord s.memory 224
  let v40 : W := UInt256.mulMod w4 v39 w10
  let v41 : W := v40 + v38
  let v42 : W := UInt256.mulMod w8 w7 w10
  let v43 : W := v42 + v41
  let v44 : W := UInt256.mulMod w5 w6 w10
  let v45 : W := v44 + v43
  let v46 : W := UInt256.mulMod w12 w15 w10
  let v47 : W := v46 + v45
  let v48 : W := UInt256.mulMod w14 w16 w10
  let v49 : W := v48 + v47
  {s with pc := N 7695,memory := s.memory,stack := v49::v32::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::w16::rest}
def productColumn13Program : List Instr := pr13NewProgram
private theorem aux_shared0 (w10 : W) (z0 z1 : W) :
    (UInt256.mulMod z0 z1 w10) = (UInt256.mulMod z1 z0 w10) := by
  simp (disch := decide) only [addC,addA,addL,mulC,mmC,amC,andC,orC,xorC,eqC,read_disjoint,Challenge.EvmProof.Memory.readWord_writeWord]
private theorem aux_shared1 (z0 z1 : W) :
    (z0 * z1) = (z1 * z0) := by
  simp (disch := decide) only [addC,addA,addL,mulC,mmC,amC,andC,orC,xorC,eqC,read_disjoint,Challenge.EvmProof.Memory.readWord_writeWord]
private theorem aux_shared2 (z0 z1 : W) :
    (z0 + z1) = (z1 + z0) := by
  simp (disch := decide) only [addC,addA,addL,mulC,mmC,amC,andC,orC,xorC,eqC,read_disjoint,Challenge.EvmProof.Memory.readWord_writeWord]
private theorem aux_shared3 (w3 w10 : W) (z0 : W) :
    (UInt256.mulMod w3 z0 w10) = (UInt256.mulMod z0 w3 w10) := by
  simp (disch := decide) only [addC,addA,addL,mulC,mmC,amC,andC,orC,xorC,eqC,read_disjoint,Challenge.EvmProof.Memory.readWord_writeWord]
private theorem aux_shared4 (w3 : W) (z0 : W) :
    (w3 * z0) = (z0 * w3) := by
  simp (disch := decide) only [addC,addA,addL,mulC,mmC,amC,andC,orC,xorC,eqC,read_disjoint,Challenge.EvmProof.Memory.readWord_writeWord]
private theorem prepared_model_eq (s : State) (carry w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 : W) (rest : List W) :
    productColumn13Model s carry w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 rest = pr13NewModel s carry w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 rest := by
  let o0 : W := MachineState.readWord s.memory 1920
  let o1 : W := o0 * carry
  let o2 : W := o1 + w2
  let o3 : W := UInt256.mulMod o0 carry w0
  let o4 : W := o3 + w1
  let o5 : W := MachineState.readWord s.memory 160
  let o6 : W := MachineState.readWord s.memory 1888
  let o7 : W := o6 * o5
  let o8 : W := o7 + o2
  let o9 : W := UInt256.mulMod o6 o5 w10
  let o10 : W := o9 + o4
  let o11 : W := MachineState.readWord s.memory 1856
  let o12 : W := o11 * w3
  let o13 : W := o12 + o8
  let o14 : W := UInt256.mulMod o11 w3 w10
  let o15 : W := o14 + o10
  let o16 : W := MachineState.readWord s.memory 192
  let o17 : W := w11 * o16
  let o18 : W := o17 + o13
  let o19 : W := MachineState.readWord s.memory 0
  let o20 : W := w9 * o19
  let o21 : W := o20 + o18
  let o22 : W := MachineState.readWord s.memory 224
  let o23 : W := w4 * o22
  let o24 : W := o23 + o21
  let o25 : W := w8 * w7
  let o26 : W := o25 + o24
  let o27 : W := w5 * w6
  let o28 : W := o27 + o26
  let o29 : W := w15 * w12
  let o30 : W := o29 + o28
  let o31 : W := w14 * w16
  let o32 : W := o31 + o30
  let o33 : W := MachineState.readWord s.memory 192
  let o34 : W := UInt256.mulMod w11 o33 w10
  let o35 : W := o34 + o15
  let o36 : W := MachineState.readWord s.memory 0
  let o37 : W := UInt256.mulMod w9 o36 w10
  let o38 : W := o37 + o35
  let o39 : W := MachineState.readWord s.memory 224
  let o40 : W := UInt256.mulMod w4 o39 w10
  let o41 : W := o40 + o38
  let o42 : W := UInt256.mulMod w8 w7 w10
  let o43 : W := o42 + o41
  let o44 : W := UInt256.mulMod w5 w6 w10
  let o45 : W := o44 + o43
  let o46 : W := UInt256.mulMod w12 w15 w10
  let o47 : W := o46 + o45
  let o48 : W := UInt256.mulMod w14 w16 w10
  let o49 : W := o48 + o47
  let n0 : W := MachineState.readWord s.memory 1920
  let n1 : W := n0 * carry
  let n2 : W := n1 + w2
  let n3 : W := UInt256.mulMod n0 carry w0
  let n4 : W := n3 + w1
  let n5 : W := MachineState.readWord s.memory 160
  let n6 : W := MachineState.readWord s.memory 1888
  let n7 : W := UInt256.mulMod n5 n6 w10
  let n8 : W := n5 * n6
  let n9 : W := MachineState.readWord s.memory 1856
  let n10 : W := n2 + n8
  let n11 : W := n4 + n7
  let n12 : W := UInt256.mulMod w3 n9 w10
  let n13 : W := n12 + n11
  let n14 : W := w3 * n9
  let n15 : W := n14 + n10
  let n16 : W := MachineState.readWord s.memory 192
  let n17 : W := w11 * n16
  let n18 : W := n17 + n15
  let n19 : W := MachineState.readWord s.memory 0
  let n20 : W := w9 * n19
  let n21 : W := n20 + n18
  let n22 : W := MachineState.readWord s.memory 224
  let n23 : W := w4 * n22
  let n24 : W := n23 + n21
  let n25 : W := w8 * w7
  let n26 : W := n25 + n24
  let n27 : W := w5 * w6
  let n28 : W := n27 + n26
  let n29 : W := w15 * w12
  let n30 : W := n29 + n28
  let n31 : W := w14 * w16
  let n32 : W := n31 + n30
  let n33 : W := MachineState.readWord s.memory 192
  let n34 : W := UInt256.mulMod w11 n33 w10
  let n35 : W := n34 + n13
  let n36 : W := MachineState.readWord s.memory 0
  let n37 : W := UInt256.mulMod w9 n36 w10
  let n38 : W := n37 + n35
  let n39 : W := MachineState.readWord s.memory 224
  let n40 : W := UInt256.mulMod w4 n39 w10
  let n41 : W := n40 + n38
  let n42 : W := UInt256.mulMod w8 w7 w10
  let n43 : W := n42 + n41
  let n44 : W := UInt256.mulMod w5 w6 w10
  let n45 : W := n44 + n43
  let n46 : W := UInt256.mulMod w12 w15 w10
  let n47 : W := n46 + n45
  let n48 : W := UInt256.mulMod w14 w16 w10
  let n49 : W := n48 + n47
  have eq_o33 : o33 = o16 := by
    simp only [o33,o16]
  have eq_o36 : o36 = o19 := by
    simp only [o36,o19]
  have eq_o39 : o39 = o22 := by
    simp only [o39,o22]
  have eq_n0 : n0 = o0 := by
    simp only [n0,o0]
  have eq_n1 : n1 = o1 := by
    simp only [n1,o1,eq_n0]
  have eq_n2 : n2 = o2 := by
    simp only [n2,o2,eq_n1]
  have eq_n3 : n3 = o3 := by
    simp only [n3,o3,eq_n0]
  have eq_n4 : n4 = o4 := by
    simp only [n4,o4,eq_n3]
  have eq_n5 : n5 = o5 := by
    simp only [n5,o5]
  have eq_n6 : n6 = o6 := by
    simp only [n6,o6]
  have eq_n7 : n7 = o9 := by
    simpa only [n7,o9,eq_n5,eq_n6] using
      (aux_shared0 w10 o5 o6)
  have eq_n8 : n8 = o7 := by
    simpa only [n8,o7,eq_n5,eq_n6] using
      (aux_shared1  o5 o6)
  have eq_n9 : n9 = o11 := by
    simp only [n9,o11]
  have eq_n10 : n10 = o8 := by
    simpa only [n10,o8,eq_n2,eq_n8] using
      (aux_shared2  o2 o7)
  have eq_n11 : n11 = o10 := by
    simpa only [n11,o10,eq_n4,eq_n7] using
      (aux_shared2  o4 o9)
  have eq_n12 : n12 = o14 := by
    simpa only [n12,o14,eq_n9] using
      (aux_shared3 w3 w10 o11)
  have eq_n13 : n13 = o15 := by
    simp only [n13,o15,eq_n12,eq_n11]
  have eq_n14 : n14 = o12 := by
    simpa only [n14,o12,eq_n9] using
      (aux_shared4 w3 o11)
  have eq_n15 : n15 = o13 := by
    simp only [n15,o13,eq_n14,eq_n10]
  have eq_n16 : n16 = o16 := by
    simp only [n16,o16]
  have eq_n17 : n17 = o17 := by
    simp only [n17,o17,eq_n16]
  have eq_n18 : n18 = o18 := by
    simp only [n18,o18,eq_n17,eq_n15]
  have eq_n19 : n19 = o19 := by
    simp only [n19,o19]
  have eq_n20 : n20 = o20 := by
    simp only [n20,o20,eq_n19]
  have eq_n21 : n21 = o21 := by
    simp only [n21,o21,eq_n20,eq_n18]
  have eq_n22 : n22 = o22 := by
    simp only [n22,o22]
  have eq_n23 : n23 = o23 := by
    simp only [n23,o23,eq_n22]
  have eq_n24 : n24 = o24 := by
    simp only [n24,o24,eq_n23,eq_n21]
  have eq_n25 : n25 = o25 := by
    simp only [n25,o25]
  have eq_n26 : n26 = o26 := by
    simp only [n26,o26,eq_n25,eq_n24]
  have eq_n27 : n27 = o27 := by
    simp only [n27,o27]
  have eq_n28 : n28 = o28 := by
    simp only [n28,o28,eq_n27,eq_n26]
  have eq_n29 : n29 = o29 := by
    simp only [n29,o29]
  have eq_n30 : n30 = o30 := by
    simp only [n30,o30,eq_n29,eq_n28]
  have eq_n31 : n31 = o31 := by
    simp only [n31,o31]
  have eq_n32 : n32 = o32 := by
    simp only [n32,o32,eq_n31,eq_n30]
  have eq_n33 : n33 = o16 := by
    simp only [n33,o16]
  have eq_n34 : n34 = o34 := by
    simp only [n34,o34,eq_n33,eq_o33]
  have eq_n35 : n35 = o35 := by
    simp only [n35,o35,eq_n34,eq_n13]
  have eq_n36 : n36 = o19 := by
    simp only [n36,o19]
  have eq_n37 : n37 = o37 := by
    simp only [n37,o37,eq_n36,eq_o36]
  have eq_n38 : n38 = o38 := by
    simp only [n38,o38,eq_n37,eq_n35]
  have eq_n39 : n39 = o22 := by
    simp only [n39,o22]
  have eq_n40 : n40 = o40 := by
    simp only [n40,o40,eq_n39,eq_o39]
  have eq_n41 : n41 = o41 := by
    simp only [n41,o41,eq_n40,eq_n38]
  have eq_n42 : n42 = o42 := by
    simp only [n42,o42]
  have eq_n43 : n43 = o43 := by
    simp only [n43,o43,eq_n42,eq_n41]
  have eq_n44 : n44 = o44 := by
    simp only [n44,o44]
  have eq_n45 : n45 = o45 := by
    simp only [n45,o45,eq_n44,eq_n43]
  have eq_n46 : n46 = o46 := by
    simp only [n46,o46]
  have eq_n47 : n47 = o47 := by
    simp only [n47,o47,eq_n46,eq_n45]
  have eq_n48 : n48 = o48 := by
    simp only [n48,o48]
  have eq_n49 : n49 = o49 := by
    simp only [n49,o49,eq_n48,eq_n47]
  change {s with pc := N 7695,memory := s.memory,stack := o49::o32::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::w16::rest} =
    {s with pc := N 7695,memory := s.memory,stack := n49::n32::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::w16::rest}
  simp only [eq_o33,eq_o36,eq_o39,eq_n0,eq_n1,eq_n2,eq_n3,eq_n4,eq_n5,eq_n6,eq_n7,eq_n8,eq_n9,eq_n10,eq_n11,eq_n12,eq_n13,eq_n14,eq_n15,eq_n16,eq_n17,eq_n18,eq_n19,eq_n20,eq_n21,eq_n22,eq_n23,eq_n24,eq_n25,eq_n26,eq_n27,eq_n28,eq_n29,eq_n30,eq_n31,eq_n32,eq_n33,eq_n34,eq_n35,eq_n36,eq_n37,eq_n38,eq_n39,eq_n40,eq_n41,eq_n42,eq_n43,eq_n44,eq_n45,eq_n46,eq_n47,eq_n48,eq_n49]
theorem productColumn13_run (s : State) (carry w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions productColumn13Program {s with pc := N 7578,stack := carry::w0::w1::w2::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::w16::rest} =
      some (productColumn13Model s carry w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 rest) := by
  exact (pr13New_run s carry w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 rest hcap hact).trans
    (congrArg some (prepared_model_eq s carry w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 rest).symm)
#print axioms productColumn13_run
end CycleSubmission.Execution
