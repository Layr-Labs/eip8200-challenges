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
def pr11Newpart0Program : List Instr :=
  [
  .op (.Swap sA3),
   .op (.Dup dA1),
   .op (.Dup dA5),
   .op .MUL,
   .op .ADD,
   .op (.Swap sA3),
   .op .MULMOD,
   .op .ADD]
def pr11Newpart0Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 : W) (rest : List W) : State :=
  let v0 : W := x0 * x1
  let v1 : W := v0 + x4
  let v2 : W := UInt256.mulMod x0 x1 x2
  let v3 : W := v2 + x3
  {s with pc := N 7335,memory := s.memory,stack := v3::v1::x5::x6::x7::x8::x9::x10::x11::x12::x13::x14::x15::x16::x17::x18::rest}
theorem pr11Newpart0_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions pr11Newpart0Program {s with pc := N 7327,stack := x0::x1::x2::x3::x4::x5::x6::x7::x8::x9::x10::x11::x12::x13::x14::x15::x16::x17::x18::rest} =
      some (pr11Newpart0Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 21) : rest.length + j < 1024 := by omega
  simp [hz,hzn,pr11Newpart0Program,pr11Newpart0Model,runInstructions,runInstr,List.exchange,succ_ofNat_mod,ofNat_add_mod,Nat.add_assoc,State.activeWordsAfterUInt256,literal_eq_ofNat,capacity]
def pr11Newpart1Program : List Instr :=
  [
  .op (.Dup dA9),
   .push 1 128,
   .op .MLOAD,
   .push 2 1888,
   .op .MLOAD,
   .op (.Swap sA3),
   .op (.Dup dA1),
   .op (.Dup dA5)]
def pr11Newpart1Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 : W) (rest : List W) : State :=
  let v0 : W := MachineState.readWord s.memory 128
  let v1 : W := MachineState.readWord s.memory 1888
  {s with pc := N 7346,memory := s.memory,stack := v1::v0::x1::v0::x9::x0::v1::x2::x3::x4::x5::x6::x7::x8::x9::x10::x11::x12::x13::x14::x15::rest}
theorem pr11Newpart1_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions pr11Newpart1Program {s with pc := N 7335,stack := x0::x1::x2::x3::x4::x5::x6::x7::x8::x9::x10::x11::x12::x13::x14::x15::rest} =
      some (pr11Newpart1Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 21) : rest.length + j < 1024 := by omega
  have ha128 : (128 : W).toNat = 128 := rfl
  have hf128 := Monpro.activeWords_fix s 128 32 (by decide) (by norm_num) hact
  have ha1888 : (1888 : W).toNat = 1888 := rfl
  have hf1888 := Monpro.activeWords_fix s 1888 32 (by decide) (by norm_num) hact
  simp [hz,hzn,pr11Newpart1Program,pr11Newpart1Model,runInstructions,runInstr,List.exchange,succ_ofNat_mod,ofNat_add_mod,Nat.add_assoc,State.activeWordsAfterUInt256,literal_eq_ofNat,capacity,ha128,hf128,ha1888,hf1888]
def pr11Newpart2Program : List Instr :=
  [
  .op .MUL,
   .op .ADD,
   .op (.Swap sA3),
   .op .MULMOD,
   .op .ADD,
   .push 1 160,
   .op .MLOAD,
   .push 2 1856,
   .op .MLOAD]
def pr11Newpart2Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 : W) (rest : List W) : State :=
  let v0 : W := x0 * x1
  let v1 : W := v0 + x2
  let v2 : W := UInt256.mulMod x6 x3 x4
  let v3 : W := v2 + x5
  let v4 : W := MachineState.readWord s.memory 160
  let v5 : W := MachineState.readWord s.memory 1856
  {s with pc := N 7358,memory := s.memory,stack := v5::v4::v3::v1::x7::x8::x9::x10::x11::x12::x13::x14::x15::x16::x17::x18::x19::x20::rest}
theorem pr11Newpart2_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions pr11Newpart2Program {s with pc := N 7346,stack := x0::x1::x2::x3::x4::x5::x6::x7::x8::x9::x10::x11::x12::x13::x14::x15::x16::x17::x18::x19::x20::rest} =
      some (pr11Newpart2Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 21) : rest.length + j < 1024 := by omega
  have ha160 : (160 : W).toNat = 160 := rfl
  have hf160 := Monpro.activeWords_fix s 160 32 (by decide) (by norm_num) hact
  have ha1856 : (1856 : W).toNat = 1856 := rfl
  have hf1856 := Monpro.activeWords_fix s 1856 32 (by decide) (by norm_num) hact
  simp [hz,hzn,pr11Newpart2Program,pr11Newpart2Model,runInstructions,runInstr,List.exchange,succ_ofNat_mod,ofNat_add_mod,Nat.add_assoc,State.activeWordsAfterUInt256,literal_eq_ofNat,capacity,ha160,hf160,ha1856,hf1856]
def pr11Newpart3Program : List Instr :=
  [
  .op (.Dup dA11),
   .op (.Dup dA1),
   .op (.Dup dA3),
   .op .MULMOD,
   .op (.Swap sA1),
   .op .MUL,
   .push 2 1824,
   .op .MLOAD]
def pr11Newpart3Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 : W) (rest : List W) : State :=
  let v0 : W := UInt256.mulMod x1 x0 x11
  let v1 : W := x1 * x0
  let v2 : W := MachineState.readWord s.memory 1824
  {s with pc := N 7368,memory := s.memory,stack := v2::v1::v0::x2::x3::x4::x5::x6::x7::x8::x9::x10::x11::x12::x13::x14::x15::x16::x17::rest}
theorem pr11Newpart3_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions pr11Newpart3Program {s with pc := N 7358,stack := x0::x1::x2::x3::x4::x5::x6::x7::x8::x9::x10::x11::x12::x13::x14::x15::x16::x17::rest} =
      some (pr11Newpart3Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 21) : rest.length + j < 1024 := by omega
  have ha1824 : (1824 : W).toNat = 1824 := rfl
  have hf1824 := Monpro.activeWords_fix s 1824 32 (by decide) (by norm_num) hact
  simp [hz,hzn,pr11Newpart3Program,pr11Newpart3Model,runInstructions,runInstr,List.exchange,succ_ofNat_mod,ofNat_add_mod,Nat.add_assoc,State.activeWordsAfterUInt256,literal_eq_ofNat,capacity,ha1824,hf1824]
def pr11Newpart4Program : List Instr :=
  [
  .op (.Swap sA3),
   .op .ADD,
   .op (.Swap sA1),
   .op .ADD,
   .op (.Dup dA10),
   .op (.Dup dA3),
   .op (.Dup dA5),
   .op .MULMOD]
def pr11Newpart4Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 : W) (rest : List W) : State :=
  let v0 : W := x4 + x1
  let v1 : W := x3 + x2
  let v2 : W := UInt256.mulMod x5 x0 x12
  {s with pc := N 7376,memory := s.memory,stack := v2::v1::v0::x0::x5::x6::x7::x8::x9::x10::x11::x12::x13::x14::x15::x16::x17::x18::rest}
theorem pr11Newpart4_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions pr11Newpart4Program {s with pc := N 7368,stack := x0::x1::x2::x3::x4::x5::x6::x7::x8::x9::x10::x11::x12::x13::x14::x15::x16::x17::x18::rest} =
      some (pr11Newpart4Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 20) : rest.length + j < 1024 := by omega
  simp [hz,hzn,pr11Newpart4Program,pr11Newpart4Model,runInstructions,runInstr,List.exchange,succ_ofNat_mod,ofNat_add_mod,Nat.add_assoc,State.activeWordsAfterUInt256,literal_eq_ofNat,capacity]
def pr11Newpart5Program : List Instr :=
  [
  .op .ADD,
   .op (.Swap sA1),
   .op (.Dup dA3),
   .op .MUL,
   .op .ADD,
   .push 2 1088,
   .op .MLOAD,
   .op (.Dup dA11)]
def pr11Newpart5Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 : W) (rest : List W) : State :=
  let v0 : W := x0 + x1
  let v1 : W := x4 * x3
  let v2 : W := v1 + x2
  let v3 : W := MachineState.readWord s.memory 1088
  {s with pc := N 7386,memory := s.memory,stack := x12::v3::v2::v0::x4::x5::x6::x7::x8::x9::x10::x11::x12::x13::x14::x15::x16::x17::rest}
theorem pr11Newpart5_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions pr11Newpart5Program {s with pc := N 7376,stack := x0::x1::x2::x3::x4::x5::x6::x7::x8::x9::x10::x11::x12::x13::x14::x15::x16::x17::rest} =
      some (pr11Newpart5Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 18) : rest.length + j < 1024 := by omega
  have ha1088 : (1088 : W).toNat = 1088 := rfl
  have hf1088 := Monpro.activeWords_fix s 1088 32 (by decide) (by norm_num) hact
  simp [hz,hzn,pr11Newpart5Program,pr11Newpart5Model,runInstructions,runInstr,List.exchange,succ_ofNat_mod,ofNat_add_mod,Nat.add_assoc,State.activeWordsAfterUInt256,literal_eq_ofNat,capacity,ha1088,hf1088]
def pr11Newpart6Program : List Instr :=
  [
  .op .MUL,
   .op .ADD,
   .push 1 192,
   .op .MLOAD,
   .op (.Dup dA9),
   .op .MUL,
   .op .ADD,
   .push 0 0,
   .op .MLOAD]
def pr11Newpart6Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 : W) (rest : List W) : State :=
  let v0 : W := x0 * x1
  let v1 : W := v0 + x2
  let v2 : W := MachineState.readWord s.memory 192
  let v3 : W := x10 * v2
  let v4 : W := v3 + v1
  let v5 : W := MachineState.readWord s.memory 0
  {s with pc := N 7396,memory := s.memory,stack := v5::v4::x3::x4::x5::x6::x7::x8::x9::x10::x11::x12::x13::x14::x15::x16::x17::rest}
theorem pr11Newpart6_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions pr11Newpart6Program {s with pc := N 7386,stack := x0::x1::x2::x3::x4::x5::x6::x7::x8::x9::x10::x11::x12::x13::x14::x15::x16::x17::rest} =
      some (pr11Newpart6Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 18) : rest.length + j < 1024 := by omega
  have ha0 : (0 : W).toNat = 0 := rfl
  have hf0 := Monpro.activeWords_fix s 0 32 (by decide) (by norm_num) hact
  have ha192 : (192 : W).toNat = 192 := rfl
  have hf192 := Monpro.activeWords_fix s 192 32 (by decide) (by norm_num) hact
  simp [hz,hzn,pr11Newpart6Program,pr11Newpart6Model,runInstructions,runInstr,List.exchange,succ_ofNat_mod,ofNat_add_mod,Nat.add_assoc,State.activeWordsAfterUInt256,literal_eq_ofNat,capacity,ha0,hf0,ha192,hf192]
def pr11Newpart7Program : List Instr :=
  [
  .op (.Dup dA4),
   .op .MUL,
   .op .ADD,
   .push 1 224,
   .op .MLOAD,
   .op (.Dup dA8),
   .op .MUL,
   .op .ADD]
def pr11Newpart7Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 : W) (rest : List W) : State :=
  let v0 : W := x4 * x0
  let v1 : W := v0 + x1
  let v2 : W := MachineState.readWord s.memory 224
  let v3 : W := x8 * v2
  let v4 : W := v3 + v1
  {s with pc := N 7405,memory := s.memory,stack := v4::x2::x3::x4::x5::x6::x7::x8::x9::x10::x11::x12::x13::x14::x15::x16::rest}
theorem pr11Newpart7_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions pr11Newpart7Program {s with pc := N 7396,stack := x0::x1::x2::x3::x4::x5::x6::x7::x8::x9::x10::x11::x12::x13::x14::x15::x16::rest} =
      some (pr11Newpart7Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 18) : rest.length + j < 1024 := by omega
  have ha224 : (224 : W).toNat = 224 := rfl
  have hf224 := Monpro.activeWords_fix s 224 32 (by decide) (by norm_num) hact
  simp [hz,hzn,pr11Newpart7Program,pr11Newpart7Model,runInstructions,runInstr,List.exchange,succ_ofNat_mod,ofNat_add_mod,Nat.add_assoc,State.activeWordsAfterUInt256,literal_eq_ofNat,capacity,ha224,hf224]
def pr11Newpart8Program : List Instr :=
  [
  .push 2 1216,
   .op .MLOAD,
   .op (.Dup dA5),
   .op .MUL,
   .op .ADD,
   .op (.Dup dA5),
   .op (.Dup dA15),
   .op .MUL]
def pr11Newpart8Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 : W) (rest : List W) : State :=
  let v0 : W := MachineState.readWord s.memory 1216
  let v1 : W := x4 * v0
  let v2 : W := v1 + x0
  let v3 : W := x14 * x5
  {s with pc := N 7415,memory := s.memory,stack := v3::v2::x1::x2::x3::x4::x5::x6::x7::x8::x9::x10::x11::x12::x13::x14::x15::rest}
theorem pr11Newpart8_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions pr11Newpart8Program {s with pc := N 7405,stack := x0::x1::x2::x3::x4::x5::x6::x7::x8::x9::x10::x11::x12::x13::x14::x15::rest} =
      some (pr11Newpart8Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 18) : rest.length + j < 1024 := by omega
  have ha1216 : (1216 : W).toNat = 1216 := rfl
  have hf1216 := Monpro.activeWords_fix s 1216 32 (by decide) (by norm_num) hact
  simp [hz,hzn,pr11Newpart8Program,pr11Newpart8Model,runInstructions,runInstr,List.exchange,succ_ofNat_mod,ofNat_add_mod,Nat.add_assoc,State.activeWordsAfterUInt256,literal_eq_ofNat,capacity,ha1216,hf1216]
def pr11Newpart9Program : List Instr :=
  [
  .op .ADD,
   .op (.Dup dA15),
   .push 2 1280,
   .op .MLOAD,
   .op .MUL,
   .op .ADD,
   .op (.Dup dA13),
   .op (.Dup dA12)]
def pr11Newpart9Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 : W) (rest : List W) : State :=
  let v0 : W := x0 + x1
  let v1 : W := MachineState.readWord s.memory 1280
  let v2 : W := v1 * x16
  let v3 : W := v2 + v0
  {s with pc := N 7425,memory := s.memory,stack := x12::x14::v3::x2::x3::x4::x5::x6::x7::x8::x9::x10::x11::x12::x13::x14::x15::x16::rest}
theorem pr11Newpart9_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions pr11Newpart9Program {s with pc := N 7415,stack := x0::x1::x2::x3::x4::x5::x6::x7::x8::x9::x10::x11::x12::x13::x14::x15::x16::rest} =
      some (pr11Newpart9Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 18) : rest.length + j < 1024 := by omega
  have ha1280 : (1280 : W).toNat = 1280 := rfl
  have hf1280 := Monpro.activeWords_fix s 1280 32 (by decide) (by norm_num) hact
  simp [hz,hzn,pr11Newpart9Program,pr11Newpart9Model,runInstructions,runInstr,List.exchange,succ_ofNat_mod,ofNat_add_mod,Nat.add_assoc,State.activeWordsAfterUInt256,literal_eq_ofNat,capacity,ha1280,hf1280]
def pr11Newpart10Program : List Instr :=
  [
  .op .MUL,
   .op .ADD,
   .op (.Swap sA0),
   .op (.Dup dA9),
   .push 2 1088,
   .op .MLOAD,
   .op (.Dup dA12),
   .op .MULMOD]
def pr11Newpart10Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 : W) (rest : List W) : State :=
  let v0 : W := x0 * x1
  let v1 : W := v0 + x2
  let v2 : W := MachineState.readWord s.memory 1088
  let v3 : W := UInt256.mulMod x12 v2 x11
  {s with pc := N 7435,memory := s.memory,stack := v3::x3::v1::x4::x5::x6::x7::x8::x9::x10::x11::x12::x13::x14::x15::x16::x17::rest}
theorem pr11Newpart10_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions pr11Newpart10Program {s with pc := N 7425,stack := x0::x1::x2::x3::x4::x5::x6::x7::x8::x9::x10::x11::x12::x13::x14::x15::x16::x17::rest} =
      some (pr11Newpart10Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 19) : rest.length + j < 1024 := by omega
  have ha1088 : (1088 : W).toNat = 1088 := rfl
  have hf1088 := Monpro.activeWords_fix s 1088 32 (by decide) (by norm_num) hact
  simp [hz,hzn,pr11Newpart10Program,pr11Newpart10Model,runInstructions,runInstr,List.exchange,succ_ofNat_mod,ofNat_add_mod,Nat.add_assoc,State.activeWordsAfterUInt256,literal_eq_ofNat,capacity,ha1088,hf1088]
def pr11Newpart11Program : List Instr :=
  [
  .op .ADD,
   .op (.Dup dA9),
   .push 1 192,
   .op .MLOAD,
   .op (.Dup dA10),
   .op .MULMOD,
   .op .ADD,
   .op (.Dup dA9)]
def pr11Newpart11Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 : W) (rest : List W) : State :=
  let v0 : W := x0 + x1
  let v1 : W := MachineState.readWord s.memory 192
  let v2 : W := UInt256.mulMod x9 v1 x10
  let v3 : W := v2 + v0
  {s with pc := N 7444,memory := s.memory,stack := x10::v3::x2::x3::x4::x5::x6::x7::x8::x9::x10::x11::x12::x13::x14::x15::x16::rest}
theorem pr11Newpart11_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions pr11Newpart11Program {s with pc := N 7435,stack := x0::x1::x2::x3::x4::x5::x6::x7::x8::x9::x10::x11::x12::x13::x14::x15::x16::rest} =
      some (pr11Newpart11Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 19) : rest.length + j < 1024 := by omega
  have ha192 : (192 : W).toNat = 192 := rfl
  have hf192 := Monpro.activeWords_fix s 192 32 (by decide) (by norm_num) hact
  simp [hz,hzn,pr11Newpart11Program,pr11Newpart11Model,runInstructions,runInstr,List.exchange,succ_ofNat_mod,ofNat_add_mod,Nat.add_assoc,State.activeWordsAfterUInt256,literal_eq_ofNat,capacity,ha192,hf192]
def pr11Newpart12Program : List Instr :=
  [
  .push 0 0,
   .op .MLOAD,
   .op (.Dup dA5),
   .op .MULMOD,
   .op .ADD,
   .op (.Dup dA9),
   .push 1 224,
   .op .MLOAD]
def pr11Newpart12Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 : W) (rest : List W) : State :=
  let v0 : W := MachineState.readWord s.memory 0
  let v1 : W := UInt256.mulMod x4 v0 x0
  let v2 : W := v1 + x1
  let v3 : W := MachineState.readWord s.memory 224
  {s with pc := N 7453,memory := s.memory,stack := v3::x10::v2::x2::x3::x4::x5::x6::x7::x8::x9::x10::x11::x12::x13::x14::x15::x16::rest}
theorem pr11Newpart12_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions pr11Newpart12Program {s with pc := N 7444,stack := x0::x1::x2::x3::x4::x5::x6::x7::x8::x9::x10::x11::x12::x13::x14::x15::x16::rest} =
      some (pr11Newpart12Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 19) : rest.length + j < 1024 := by omega
  have ha0 : (0 : W).toNat = 0 := rfl
  have hf0 := Monpro.activeWords_fix s 0 32 (by decide) (by norm_num) hact
  have ha224 : (224 : W).toNat = 224 := rfl
  have hf224 := Monpro.activeWords_fix s 224 32 (by decide) (by norm_num) hact
  simp [hz,hzn,pr11Newpart12Program,pr11Newpart12Model,runInstructions,runInstr,List.exchange,succ_ofNat_mod,ofNat_add_mod,Nat.add_assoc,State.activeWordsAfterUInt256,literal_eq_ofNat,capacity,ha0,hf0,ha224,hf224]
def pr11Newpart13Program : List Instr :=
  [
  .op (.Dup dA9)]
def pr11Newpart13Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 : W) (rest : List W) : State :=
  {s with pc := N 7454,memory := s.memory,stack := x9::x0::x1::x2::x3::x4::x5::x6::x7::x8::x9::x10::x11::x12::x13::x14::x15::x16::x17::rest}
theorem pr11Newpart13_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions pr11Newpart13Program {s with pc := N 7453,stack := x0::x1::x2::x3::x4::x5::x6::x7::x8::x9::x10::x11::x12::x13::x14::x15::x16::x17::rest} =
      some (pr11Newpart13Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 19) : rest.length + j < 1024 := by omega
  simp [hz,hzn,pr11Newpart13Program,pr11Newpart13Model,runInstructions,runInstr,List.exchange,succ_ofNat_mod,ofNat_add_mod,Nat.add_assoc,State.activeWordsAfterUInt256,literal_eq_ofNat,capacity]
def pr11NewProgram : List Instr :=
  [
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
   .push 2 1888,
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
   .push 2 1856,
   .op .MLOAD,
   .op (.Dup dA11),
   .op (.Dup dA1),
   .op (.Dup dA3),
   .op .MULMOD,
   .op (.Swap sA1),
   .op .MUL,
   .push 2 1824,
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
   .push 2 1088,
   .op .MLOAD,
   .op (.Dup dA11),
   .op .MUL,
   .op .ADD,
   .push 1 192,
   .op .MLOAD,
   .op (.Dup dA9),
   .op .MUL,
   .op .ADD,
   .push 0 0,
   .op .MLOAD,
   .op (.Dup dA4),
   .op .MUL,
   .op .ADD,
   .push 1 224,
   .op .MLOAD,
   .op (.Dup dA8),
   .op .MUL,
   .op .ADD,
   .push 2 1216,
   .op .MLOAD,
   .op (.Dup dA5),
   .op .MUL,
   .op .ADD,
   .op (.Dup dA5),
   .op (.Dup dA15),
   .op .MUL,
   .op .ADD,
   .op (.Dup dA15),
   .push 2 1280,
   .op .MLOAD,
   .op .MUL,
   .op .ADD,
   .op (.Dup dA13),
   .op (.Dup dA12),
   .op .MUL,
   .op .ADD,
   .op (.Swap sA0),
   .op (.Dup dA9),
   .push 2 1088,
   .op .MLOAD,
   .op (.Dup dA12),
   .op .MULMOD,
   .op .ADD,
   .op (.Dup dA9),
   .push 1 192,
   .op .MLOAD,
   .op (.Dup dA10),
   .op .MULMOD,
   .op .ADD,
   .op (.Dup dA9),
   .push 0 0,
   .op .MLOAD,
   .op (.Dup dA5),
   .op .MULMOD,
   .op .ADD,
   .op (.Dup dA9),
   .push 1 224,
   .op .MLOAD,
   .op (.Dup dA9)]
def pr11NewModel (s : State) (carry w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 : W) (rest : List W) : State :=
  let v0 : W := carry * w0
  let v1 : W := v0 + w3
  let v2 : W := UInt256.mulMod carry w0 w1
  let v3 : W := v2 + w2
  let v4 : W := MachineState.readWord s.memory 128
  let v5 : W := MachineState.readWord s.memory 1888
  let v6 : W := v5 * v4
  let v7 : W := v6 + v1
  let v8 : W := UInt256.mulMod v5 v4 w11
  let v9 : W := v8 + v3
  let v10 : W := MachineState.readWord s.memory 160
  let v11 : W := MachineState.readWord s.memory 1856
  let v12 : W := UInt256.mulMod v10 v11 w11
  let v13 : W := v10 * v11
  let v14 : W := MachineState.readWord s.memory 1824
  let v15 : W := v7 + v13
  let v16 : W := v9 + v12
  let v17 : W := UInt256.mulMod w4 v14 w11
  let v18 : W := v17 + v16
  let v19 : W := w4 * v14
  let v20 : W := v19 + v15
  let v21 : W := MachineState.readWord s.memory 1088
  let v22 : W := w12 * v21
  let v23 : W := v22 + v20
  let v24 : W := MachineState.readWord s.memory 192
  let v25 : W := w10 * v24
  let v26 : W := v25 + v23
  let v27 : W := MachineState.readWord s.memory 0
  let v28 : W := w5 * v27
  let v29 : W := v28 + v26
  let v30 : W := MachineState.readWord s.memory 224
  let v31 : W := w9 * v30
  let v32 : W := v31 + v29
  let v33 : W := MachineState.readWord s.memory 1216
  let v34 : W := w6 * v33
  let v35 : W := v34 + v32
  let v36 : W := w16 * w7
  let v37 : W := v36 + v35
  let v38 : W := MachineState.readWord s.memory 1280
  let v39 : W := v38 * w17
  let v40 : W := v39 + v37
  let v41 : W := w13 * w15
  let v42 : W := v41 + v40
  let v43 : W := MachineState.readWord s.memory 1088
  let v44 : W := UInt256.mulMod w12 v43 w11
  let v45 : W := v44 + v18
  let v46 : W := MachineState.readWord s.memory 192
  let v47 : W := UInt256.mulMod w10 v46 w11
  let v48 : W := v47 + v45
  let v49 : W := MachineState.readWord s.memory 0
  let v50 : W := UInt256.mulMod w5 v49 w11
  let v51 : W := v50 + v48
  let v52 : W := MachineState.readWord s.memory 224
  {s with pc := N 7454,memory := s.memory,stack := w9::v52::w11::v51::v42::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::w16::w17::rest}
theorem pr11New_run (s : State) (carry w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions pr11NewProgram {s with pc := N 7327,stack := carry::w0::w1::w2::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::w16::w17::rest} =
      some (pr11NewModel s carry w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 rest) := by
  let v0 : W := carry * w0
  let v1 : W := v0 + w3
  let v2 : W := UInt256.mulMod carry w0 w1
  let v3 : W := v2 + w2
  let v4 : W := MachineState.readWord s.memory 128
  let v5 : W := MachineState.readWord s.memory 1888
  let v6 : W := v5 * v4
  let v7 : W := v6 + v1
  let v8 : W := UInt256.mulMod v5 v4 w11
  let v9 : W := v8 + v3
  let v10 : W := MachineState.readWord s.memory 160
  let v11 : W := MachineState.readWord s.memory 1856
  let v12 : W := UInt256.mulMod v10 v11 w11
  let v13 : W := v10 * v11
  let v14 : W := MachineState.readWord s.memory 1824
  let v15 : W := v7 + v13
  let v16 : W := v9 + v12
  let v17 : W := UInt256.mulMod w4 v14 w11
  let v18 : W := v17 + v16
  let v19 : W := w4 * v14
  let v20 : W := v19 + v15
  let v21 : W := MachineState.readWord s.memory 1088
  let v22 : W := w12 * v21
  let v23 : W := v22 + v20
  let v24 : W := MachineState.readWord s.memory 192
  let v25 : W := w10 * v24
  let v26 : W := v25 + v23
  let v27 : W := MachineState.readWord s.memory 0
  let v28 : W := w5 * v27
  let v29 : W := v28 + v26
  let v30 : W := MachineState.readWord s.memory 224
  let v31 : W := w9 * v30
  let v32 : W := v31 + v29
  let v33 : W := MachineState.readWord s.memory 1216
  let v34 : W := w6 * v33
  let v35 : W := v34 + v32
  let v36 : W := w16 * w7
  let v37 : W := v36 + v35
  let v38 : W := MachineState.readWord s.memory 1280
  let v39 : W := v38 * w17
  let v40 : W := v39 + v37
  let v41 : W := w13 * w15
  let v42 : W := v41 + v40
  let v43 : W := MachineState.readWord s.memory 1088
  let v44 : W := UInt256.mulMod w12 v43 w11
  let v45 : W := v44 + v18
  let v46 : W := MachineState.readWord s.memory 192
  let v47 : W := UInt256.mulMod w10 v46 w11
  let v48 : W := v47 + v45
  let v49 : W := MachineState.readWord s.memory 0
  let v50 : W := UInt256.mulMod w5 v49 w11
  let v51 : W := v50 + v48
  let v52 : W := MachineState.readWord s.memory 224
  have h0 : runInstructions pr11Newpart0Program {s with pc := N 7327,memory := s.memory,stack := carry::w0::w1::w2::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::w16::w17::rest} = some {s with pc := N 7335,memory := s.memory,stack := v3::v1::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::w16::w17::rest} := by
    simpa only [pr11Newpart0Model,v0,v1,v2,v3] using pr11Newpart0_run (s) (carry) w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 rest hcap hact
  have h1 : runInstructions pr11Newpart1Program {s with pc := N 7335,memory := s.memory,stack := v3::v1::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::w16::w17::rest} = some {s with pc := N 7346,memory := s.memory,stack := v5::v4::v1::v4::w11::v3::v5::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::w16::w17::rest} := by
    simpa only [pr11Newpart1Model,v4,v5] using pr11Newpart1_run (s) v3 v1 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 rest hcap hact
  have h2 : runInstructions pr11Newpart2Program {s with pc := N 7346,memory := s.memory,stack := v5::v4::v1::v4::w11::v3::v5::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::w16::w17::rest} = some {s with pc := N 7358,memory := s.memory,stack := v11::v10::v9::v7::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::w16::w17::rest} := by
    simpa only [pr11Newpart2Model,v6,v7,v8,v9,v10,v11] using pr11Newpart2_run (s) v5 v4 v1 v4 w11 v3 v5 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 rest hcap hact
  have h3 : runInstructions pr11Newpart3Program {s with pc := N 7358,memory := s.memory,stack := v11::v10::v9::v7::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::w16::w17::rest} = some {s with pc := N 7368,memory := s.memory,stack := v14::v13::v12::v9::v7::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::w16::w17::rest} := by
    simpa only [pr11Newpart3Model,v12,v13,v14] using pr11Newpart3_run (s) v11 v10 v9 v7 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 rest hcap hact
  have h4 : runInstructions pr11Newpart4Program {s with pc := N 7368,memory := s.memory,stack := v14::v13::v12::v9::v7::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::w16::w17::rest} = some {s with pc := N 7376,memory := s.memory,stack := v17::v16::v15::v14::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::w16::w17::rest} := by
    simpa only [pr11Newpart4Model,v15,v16,v17] using pr11Newpart4_run (s) v14 v13 v12 v9 v7 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 rest hcap hact
  have h5 : runInstructions pr11Newpart5Program {s with pc := N 7376,memory := s.memory,stack := v17::v16::v15::v14::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::w16::w17::rest} = some {s with pc := N 7386,memory := s.memory,stack := w12::v21::v20::v18::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::w16::w17::rest} := by
    simpa only [pr11Newpart5Model,v18,v19,v20,v21] using pr11Newpart5_run (s) v17 v16 v15 v14 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 rest hcap hact
  have h6 : runInstructions pr11Newpart6Program {s with pc := N 7386,memory := s.memory,stack := w12::v21::v20::v18::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::w16::w17::rest} = some {s with pc := N 7396,memory := s.memory,stack := v27::v26::v18::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::w16::w17::rest} := by
    simpa only [pr11Newpart6Model,v22,v23,v24,v25,v26,v27] using pr11Newpart6_run (s) w12 v21 v20 v18 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 rest hcap hact
  have h7 : runInstructions pr11Newpart7Program {s with pc := N 7396,memory := s.memory,stack := v27::v26::v18::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::w16::w17::rest} = some {s with pc := N 7405,memory := s.memory,stack := v32::v18::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::w16::w17::rest} := by
    simpa only [pr11Newpart7Model,v28,v29,v30,v31,v32] using pr11Newpart7_run (s) v27 v26 v18 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 rest hcap hact
  have h8 : runInstructions pr11Newpart8Program {s with pc := N 7405,memory := s.memory,stack := v32::v18::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::w16::w17::rest} = some {s with pc := N 7415,memory := s.memory,stack := v36::v35::v18::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::w16::w17::rest} := by
    simpa only [pr11Newpart8Model,v33,v34,v35,v36] using pr11Newpart8_run (s) v32 v18 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 rest hcap hact
  have h9 : runInstructions pr11Newpart9Program {s with pc := N 7415,memory := s.memory,stack := v36::v35::v18::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::w16::w17::rest} = some {s with pc := N 7425,memory := s.memory,stack := w13::w15::v40::v18::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::w16::w17::rest} := by
    simpa only [pr11Newpart9Model,v37,v38,v39,v40] using pr11Newpart9_run (s) v36 v35 v18 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 rest hcap hact
  have h10 : runInstructions pr11Newpart10Program {s with pc := N 7425,memory := s.memory,stack := w13::w15::v40::v18::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::w16::w17::rest} = some {s with pc := N 7435,memory := s.memory,stack := v44::v18::v42::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::w16::w17::rest} := by
    simpa only [pr11Newpart10Model,v41,v42,v43,v44] using pr11Newpart10_run (s) w13 w15 v40 v18 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 rest hcap hact
  have h11 : runInstructions pr11Newpart11Program {s with pc := N 7435,memory := s.memory,stack := v44::v18::v42::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::w16::w17::rest} = some {s with pc := N 7444,memory := s.memory,stack := w11::v48::v42::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::w16::w17::rest} := by
    simpa only [pr11Newpart11Model,v45,v46,v47,v48] using pr11Newpart11_run (s) v44 v18 v42 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 rest hcap hact
  have h12 : runInstructions pr11Newpart12Program {s with pc := N 7444,memory := s.memory,stack := w11::v48::v42::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::w16::w17::rest} = some {s with pc := N 7453,memory := s.memory,stack := v52::w11::v51::v42::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::w16::w17::rest} := by
    simpa only [pr11Newpart12Model,v49,v50,v51,v52] using pr11Newpart12_run (s) w11 v48 v42 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 rest hcap hact
  have h13 : runInstructions pr11Newpart13Program {s with pc := N 7453,memory := s.memory,stack := v52::w11::v51::v42::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::w16::w17::rest} = some {s with pc := N 7454,memory := s.memory,stack := w9::v52::w11::v51::v42::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::w16::w17::rest} := by
    simpa only [pr11Newpart13Model] using pr11Newpart13_run (s) v52 w11 v51 v42 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 rest hcap hact
  exact (runInstructions_append_some _ _ _ _ _ h0 (runInstructions_append_some _ _ _ _ _ h1 (runInstructions_append_some _ _ _ _ _ h2 (runInstructions_append_some _ _ _ _ _ h3 (runInstructions_append_some _ _ _ _ _ h4 (runInstructions_append_some _ _ _ _ _ h5 (runInstructions_append_some _ _ _ _ _ h6 (runInstructions_append_some _ _ _ _ _ h7 (runInstructions_append_some _ _ _ _ _ h8 (runInstructions_append_some _ _ _ _ _ h9 (runInstructions_append_some _ _ _ _ _ h10 (runInstructions_append_some _ _ _ _ _ h11 (runInstructions_append_some _ _ _ _ _ h12 h13)))))))))))))
#print axioms pr11New_run
def productColumn11Model (s : State) (carry w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 : W) (rest : List W) : State :=
  let v0 : W := carry * w0
  let v1 : W := v0 + w3
  let v2 : W := UInt256.mulMod carry w0 w1
  let v3 : W := v2 + w2
  let v4 : W := MachineState.readWord s.memory 128
  let v5 : W := MachineState.readWord s.memory 1888
  let v6 : W := v5 * v4
  let v7 : W := v6 + v1
  let v8 : W := UInt256.mulMod v5 v4 w11
  let v9 : W := v8 + v3
  let v10 : W := MachineState.readWord s.memory 160
  let v11 : W := MachineState.readWord s.memory 1856
  let v12 : W := v11 * v10
  let v13 : W := v12 + v7
  let v14 : W := UInt256.mulMod v11 v10 w11
  let v15 : W := v14 + v9
  let v16 : W := MachineState.readWord s.memory 1824
  let v17 : W := v16 * w4
  let v18 : W := v17 + v13
  let v19 : W := UInt256.mulMod v16 w4 w11
  let v20 : W := v19 + v15
  let v21 : W := MachineState.readWord s.memory 1088
  let v22 : W := w12 * v21
  let v23 : W := v22 + v18
  let v24 : W := MachineState.readWord s.memory 192
  let v25 : W := w10 * v24
  let v26 : W := v25 + v23
  let v27 : W := MachineState.readWord s.memory 0
  let v28 : W := w5 * v27
  let v29 : W := v28 + v26
  let v30 : W := MachineState.readWord s.memory 224
  let v31 : W := w9 * v30
  let v32 : W := v31 + v29
  let v33 : W := MachineState.readWord s.memory 1216
  let v34 : W := w6 * v33
  let v35 : W := v34 + v32
  let v36 : W := w16 * w7
  let v37 : W := v36 + v35
  let v38 : W := MachineState.readWord s.memory 1280
  let v39 : W := v38 * w17
  let v40 : W := v39 + v37
  let v41 : W := w13 * w15
  let v42 : W := v41 + v40
  let v43 : W := MachineState.readWord s.memory 1088
  let v44 : W := UInt256.mulMod w12 v43 w11
  let v45 : W := v44 + v20
  let v46 : W := MachineState.readWord s.memory 192
  let v47 : W := UInt256.mulMod w10 v46 w11
  let v48 : W := v47 + v45
  let v49 : W := MachineState.readWord s.memory 0
  let v50 : W := UInt256.mulMod w5 v49 w11
  let v51 : W := v50 + v48
  let v52 : W := MachineState.readWord s.memory 224
  {s with pc := N 7454,memory := s.memory,stack := w9::v52::w11::v51::v42::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::w16::w17::rest}
def productColumn11Program : List Instr := pr11NewProgram
private theorem aux_shared0 (w11 : W) (z0 z1 : W) :
    (UInt256.mulMod z0 z1 w11) = (UInt256.mulMod z1 z0 w11) := by
  simp (disch := decide) only [addC,addA,addL,mulC,mmC,amC,andC,orC,xorC,eqC,read_disjoint,Challenge.EvmProof.Memory.readWord_writeWord]
private theorem aux_shared1 (z0 z1 : W) :
    (z0 * z1) = (z1 * z0) := by
  simp (disch := decide) only [addC,addA,addL,mulC,mmC,amC,andC,orC,xorC,eqC,read_disjoint,Challenge.EvmProof.Memory.readWord_writeWord]
private theorem aux_shared2 (z0 z1 : W) :
    (z0 + z1) = (z1 + z0) := by
  simp (disch := decide) only [addC,addA,addL,mulC,mmC,amC,andC,orC,xorC,eqC,read_disjoint,Challenge.EvmProof.Memory.readWord_writeWord]
private theorem aux_shared3 (w4 w11 : W) (z0 : W) :
    (UInt256.mulMod w4 z0 w11) = (UInt256.mulMod z0 w4 w11) := by
  simp (disch := decide) only [addC,addA,addL,mulC,mmC,amC,andC,orC,xorC,eqC,read_disjoint,Challenge.EvmProof.Memory.readWord_writeWord]
private theorem aux_shared4 (w4 : W) (z0 : W) :
    (w4 * z0) = (z0 * w4) := by
  simp (disch := decide) only [addC,addA,addL,mulC,mmC,amC,andC,orC,xorC,eqC,read_disjoint,Challenge.EvmProof.Memory.readWord_writeWord]
private theorem prepared_model_eq (s : State) (carry w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 : W) (rest : List W) :
    productColumn11Model s carry w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 rest = pr11NewModel s carry w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 rest := by
  let o0 : W := carry * w0
  let o1 : W := o0 + w3
  let o2 : W := UInt256.mulMod carry w0 w1
  let o3 : W := o2 + w2
  let o4 : W := MachineState.readWord s.memory 128
  let o5 : W := MachineState.readWord s.memory 1888
  let o6 : W := o5 * o4
  let o7 : W := o6 + o1
  let o8 : W := UInt256.mulMod o5 o4 w11
  let o9 : W := o8 + o3
  let o10 : W := MachineState.readWord s.memory 160
  let o11 : W := MachineState.readWord s.memory 1856
  let o12 : W := o11 * o10
  let o13 : W := o12 + o7
  let o14 : W := UInt256.mulMod o11 o10 w11
  let o15 : W := o14 + o9
  let o16 : W := MachineState.readWord s.memory 1824
  let o17 : W := o16 * w4
  let o18 : W := o17 + o13
  let o19 : W := UInt256.mulMod o16 w4 w11
  let o20 : W := o19 + o15
  let o21 : W := MachineState.readWord s.memory 1088
  let o22 : W := w12 * o21
  let o23 : W := o22 + o18
  let o24 : W := MachineState.readWord s.memory 192
  let o25 : W := w10 * o24
  let o26 : W := o25 + o23
  let o27 : W := MachineState.readWord s.memory 0
  let o28 : W := w5 * o27
  let o29 : W := o28 + o26
  let o30 : W := MachineState.readWord s.memory 224
  let o31 : W := w9 * o30
  let o32 : W := o31 + o29
  let o33 : W := MachineState.readWord s.memory 1216
  let o34 : W := w6 * o33
  let o35 : W := o34 + o32
  let o36 : W := w16 * w7
  let o37 : W := o36 + o35
  let o38 : W := MachineState.readWord s.memory 1280
  let o39 : W := o38 * w17
  let o40 : W := o39 + o37
  let o41 : W := w13 * w15
  let o42 : W := o41 + o40
  let o43 : W := MachineState.readWord s.memory 1088
  let o44 : W := UInt256.mulMod w12 o43 w11
  let o45 : W := o44 + o20
  let o46 : W := MachineState.readWord s.memory 192
  let o47 : W := UInt256.mulMod w10 o46 w11
  let o48 : W := o47 + o45
  let o49 : W := MachineState.readWord s.memory 0
  let o50 : W := UInt256.mulMod w5 o49 w11
  let o51 : W := o50 + o48
  let o52 : W := MachineState.readWord s.memory 224
  let n0 : W := carry * w0
  let n1 : W := n0 + w3
  let n2 : W := UInt256.mulMod carry w0 w1
  let n3 : W := n2 + w2
  let n4 : W := MachineState.readWord s.memory 128
  let n5 : W := MachineState.readWord s.memory 1888
  let n6 : W := n5 * n4
  let n7 : W := n6 + n1
  let n8 : W := UInt256.mulMod n5 n4 w11
  let n9 : W := n8 + n3
  let n10 : W := MachineState.readWord s.memory 160
  let n11 : W := MachineState.readWord s.memory 1856
  let n12 : W := UInt256.mulMod n10 n11 w11
  let n13 : W := n10 * n11
  let n14 : W := MachineState.readWord s.memory 1824
  let n15 : W := n7 + n13
  let n16 : W := n9 + n12
  let n17 : W := UInt256.mulMod w4 n14 w11
  let n18 : W := n17 + n16
  let n19 : W := w4 * n14
  let n20 : W := n19 + n15
  let n21 : W := MachineState.readWord s.memory 1088
  let n22 : W := w12 * n21
  let n23 : W := n22 + n20
  let n24 : W := MachineState.readWord s.memory 192
  let n25 : W := w10 * n24
  let n26 : W := n25 + n23
  let n27 : W := MachineState.readWord s.memory 0
  let n28 : W := w5 * n27
  let n29 : W := n28 + n26
  let n30 : W := MachineState.readWord s.memory 224
  let n31 : W := w9 * n30
  let n32 : W := n31 + n29
  let n33 : W := MachineState.readWord s.memory 1216
  let n34 : W := w6 * n33
  let n35 : W := n34 + n32
  let n36 : W := w16 * w7
  let n37 : W := n36 + n35
  let n38 : W := MachineState.readWord s.memory 1280
  let n39 : W := n38 * w17
  let n40 : W := n39 + n37
  let n41 : W := w13 * w15
  let n42 : W := n41 + n40
  let n43 : W := MachineState.readWord s.memory 1088
  let n44 : W := UInt256.mulMod w12 n43 w11
  let n45 : W := n44 + n18
  let n46 : W := MachineState.readWord s.memory 192
  let n47 : W := UInt256.mulMod w10 n46 w11
  let n48 : W := n47 + n45
  let n49 : W := MachineState.readWord s.memory 0
  let n50 : W := UInt256.mulMod w5 n49 w11
  let n51 : W := n50 + n48
  let n52 : W := MachineState.readWord s.memory 224
  have eq_o43 : o43 = o21 := by
    simp only [o43,o21]
  have eq_o46 : o46 = o24 := by
    simp only [o46,o24]
  have eq_o49 : o49 = o27 := by
    simp only [o49,o27]
  have eq_o52 : o52 = o30 := by
    simp only [o52,o30]
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
    simp only [n5,o5]
  have eq_n6 : n6 = o6 := by
    simp only [n6,o6,eq_n5,eq_n4]
  have eq_n7 : n7 = o7 := by
    simp only [n7,o7,eq_n6,eq_n1]
  have eq_n8 : n8 = o8 := by
    simp only [n8,o8,eq_n5,eq_n4]
  have eq_n9 : n9 = o9 := by
    simp only [n9,o9,eq_n8,eq_n3]
  have eq_n10 : n10 = o10 := by
    simp only [n10,o10]
  have eq_n11 : n11 = o11 := by
    simp only [n11,o11]
  have eq_n12 : n12 = o14 := by
    simpa only [n12,o14,eq_n10,eq_n11] using
      (aux_shared0 w11 o10 o11)
  have eq_n13 : n13 = o12 := by
    simpa only [n13,o12,eq_n10,eq_n11] using
      (aux_shared1  o10 o11)
  have eq_n14 : n14 = o16 := by
    simp only [n14,o16]
  have eq_n15 : n15 = o13 := by
    simpa only [n15,o13,eq_n7,eq_n13] using
      (aux_shared2  o7 o12)
  have eq_n16 : n16 = o15 := by
    simpa only [n16,o15,eq_n9,eq_n12] using
      (aux_shared2  o9 o14)
  have eq_n17 : n17 = o19 := by
    simpa only [n17,o19,eq_n14] using
      (aux_shared3 w4 w11 o16)
  have eq_n18 : n18 = o20 := by
    simp only [n18,o20,eq_n17,eq_n16]
  have eq_n19 : n19 = o17 := by
    simpa only [n19,o17,eq_n14] using
      (aux_shared4 w4 o16)
  have eq_n20 : n20 = o18 := by
    simp only [n20,o18,eq_n19,eq_n15]
  have eq_n21 : n21 = o21 := by
    simp only [n21,o21]
  have eq_n22 : n22 = o22 := by
    simp only [n22,o22,eq_n21]
  have eq_n23 : n23 = o23 := by
    simp only [n23,o23,eq_n22,eq_n20]
  have eq_n24 : n24 = o24 := by
    simp only [n24,o24]
  have eq_n25 : n25 = o25 := by
    simp only [n25,o25,eq_n24]
  have eq_n26 : n26 = o26 := by
    simp only [n26,o26,eq_n25,eq_n23]
  have eq_n27 : n27 = o27 := by
    simp only [n27,o27]
  have eq_n28 : n28 = o28 := by
    simp only [n28,o28,eq_n27]
  have eq_n29 : n29 = o29 := by
    simp only [n29,o29,eq_n28,eq_n26]
  have eq_n30 : n30 = o30 := by
    simp only [n30,o30]
  have eq_n31 : n31 = o31 := by
    simp only [n31,o31,eq_n30]
  have eq_n32 : n32 = o32 := by
    simp only [n32,o32,eq_n31,eq_n29]
  have eq_n33 : n33 = o33 := by
    simp only [n33,o33]
  have eq_n34 : n34 = o34 := by
    simp only [n34,o34,eq_n33]
  have eq_n35 : n35 = o35 := by
    simp only [n35,o35,eq_n34,eq_n32]
  have eq_n36 : n36 = o36 := by
    simp only [n36,o36]
  have eq_n37 : n37 = o37 := by
    simp only [n37,o37,eq_n36,eq_n35]
  have eq_n38 : n38 = o38 := by
    simp only [n38,o38]
  have eq_n39 : n39 = o39 := by
    simp only [n39,o39,eq_n38]
  have eq_n40 : n40 = o40 := by
    simp only [n40,o40,eq_n39,eq_n37]
  have eq_n41 : n41 = o41 := by
    simp only [n41,o41]
  have eq_n42 : n42 = o42 := by
    simp only [n42,o42,eq_n41,eq_n40]
  have eq_n43 : n43 = o21 := by
    simp only [n43,o21]
  have eq_n44 : n44 = o44 := by
    simp only [n44,o44,eq_n43,eq_o43]
  have eq_n45 : n45 = o45 := by
    simp only [n45,o45,eq_n44,eq_n18]
  have eq_n46 : n46 = o24 := by
    simp only [n46,o24]
  have eq_n47 : n47 = o47 := by
    simp only [n47,o47,eq_n46,eq_o46]
  have eq_n48 : n48 = o48 := by
    simp only [n48,o48,eq_n47,eq_n45]
  have eq_n49 : n49 = o27 := by
    simp only [n49,o27]
  have eq_n50 : n50 = o50 := by
    simp only [n50,o50,eq_n49,eq_o49]
  have eq_n51 : n51 = o51 := by
    simp only [n51,o51,eq_n50,eq_n48]
  have eq_n52 : n52 = o30 := by
    simp only [n52,o30]
  change {s with pc := N 7454,memory := s.memory,stack := w9::o52::w11::o51::o42::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::w16::w17::rest} =
    {s with pc := N 7454,memory := s.memory,stack := w9::n52::w11::n51::n42::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::w16::w17::rest}
  simp only [eq_o43,eq_o46,eq_o49,eq_o52,eq_n0,eq_n1,eq_n2,eq_n3,eq_n4,eq_n5,eq_n6,eq_n7,eq_n8,eq_n9,eq_n10,eq_n11,eq_n12,eq_n13,eq_n14,eq_n15,eq_n16,eq_n17,eq_n18,eq_n19,eq_n20,eq_n21,eq_n22,eq_n23,eq_n24,eq_n25,eq_n26,eq_n27,eq_n28,eq_n29,eq_n30,eq_n31,eq_n32,eq_n33,eq_n34,eq_n35,eq_n36,eq_n37,eq_n38,eq_n39,eq_n40,eq_n41,eq_n42,eq_n43,eq_n44,eq_n45,eq_n46,eq_n47,eq_n48,eq_n49,eq_n50,eq_n51,eq_n52]
theorem productColumn11_run (s : State) (carry w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions productColumn11Program {s with pc := N 7327,stack := carry::w0::w1::w2::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::w16::w17::rest} =
      some (productColumn11Model s carry w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 rest) := by
  exact (pr11New_run s carry w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 rest hcap hact).trans
    (congrArg some (prepared_model_eq s carry w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 rest).symm)
#print axioms productColumn11_run
end CycleSubmission.Execution
