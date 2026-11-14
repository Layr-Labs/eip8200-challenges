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
def pr10Newpart0Program : List Instr :=
  [
  .op .ADD,
   .op (.Dup dA9),
   .push 0 0,
   .op .MLOAD,
   .op (.Dup dA9),
   .op .MULMOD,
   .op .ADD,
   .op (.Dup dA9)]
def pr10Newpart0Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 : W) (rest : List W) : State :=
  let v0 : W := x0 + x1
  let v1 : W := MachineState.readWord s.memory 0
  let v2 : W := UInt256.mulMod x8 v1 x10
  let v3 : W := v2 + v0
  {s with pc := N 7208,memory := s.memory,stack := x10::v3::x2::x3::x4::x5::x6::x7::x8::x9::x10::x11::x12::x13::x14::x15::x16::rest}
theorem pr10Newpart0_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions pr10Newpart0Program {s with pc := N 7200,stack := x0::x1::x2::x3::x4::x5::x6::x7::x8::x9::x10::x11::x12::x13::x14::x15::x16::rest} =
      some (pr10Newpart0Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 19) : rest.length + j < 1024 := by omega
  have ha0 : (0 : W).toNat = 0 := rfl
  have hf0 := Monpro.activeWords_fix s 0 32 (by decide) (by norm_num) hact
  simp [hz,hzn,pr10Newpart0Program,pr10Newpart0Model,runInstructions,runInstr,List.exchange,succ_ofNat_mod,ofNat_add_mod,Nat.add_assoc,State.activeWordsAfterUInt256,literal_eq_ofNat,capacity,ha0,hf0]
def pr10Newpart1Program : List Instr :=
  [
  .push 1 224,
   .op .MLOAD,
   .op (.Dup dA6),
   .op .MULMOD,
   .op .ADD,
   .op (.Dup dA9),
   .op (.Dup dA15),
   .push 2 1216,
   .op .MLOAD]
def pr10Newpart1Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 : W) (rest : List W) : State :=
  let v0 : W := MachineState.readWord s.memory 224
  let v1 : W := UInt256.mulMod x5 v0 x0
  let v2 : W := v1 + x1
  let v3 : W := MachineState.readWord s.memory 1216
  {s with pc := N 7220,memory := s.memory,stack := v3::x15::x10::v2::x2::x3::x4::x5::x6::x7::x8::x9::x10::x11::x12::x13::x14::x15::x16::rest}
theorem pr10Newpart1_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions pr10Newpart1Program {s with pc := N 7208,stack := x0::x1::x2::x3::x4::x5::x6::x7::x8::x9::x10::x11::x12::x13::x14::x15::x16::rest} =
      some (pr10Newpart1Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 19) : rest.length + j < 1024 := by omega
  have ha224 : (224 : W).toNat = 224 := rfl
  have hf224 := Monpro.activeWords_fix s 224 32 (by decide) (by norm_num) hact
  have ha1216 : (1216 : W).toNat = 1216 := rfl
  have hf1216 := Monpro.activeWords_fix s 1216 32 (by decide) (by norm_num) hact
  simp [hz,hzn,pr10Newpart1Program,pr10Newpart1Model,runInstructions,runInstr,List.exchange,succ_ofNat_mod,ofNat_add_mod,Nat.add_assoc,State.activeWordsAfterUInt256,literal_eq_ofNat,capacity,ha224,hf224,ha1216,hf1216]
def pr10Newpart2Program : List Instr :=
  [
  .op .MULMOD,
   .op .ADD,
   .op (.Dup dA15),
   .op (.Dup dA10),
   .op (.Swap sA0),
   .push 2 1248,
   .op .MLOAD,
   .op .MULMOD]
def pr10Newpart2Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 : W) (rest : List W) : State :=
  let v0 : W := UInt256.mulMod x0 x1 x2
  let v1 : W := v0 + x3
  let v2 : W := MachineState.readWord s.memory 1248
  let v3 : W := UInt256.mulMod v2 x18 x12
  {s with pc := N 7230,memory := s.memory,stack := v3::v1::x4::x5::x6::x7::x8::x9::x10::x11::x12::x13::x14::x15::x16::x17::x18::rest}
theorem pr10Newpart2_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions pr10Newpart2Program {s with pc := N 7220,stack := x0::x1::x2::x3::x4::x5::x6::x7::x8::x9::x10::x11::x12::x13::x14::x15::x16::x17::x18::rest} =
      some (pr10Newpart2Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 19) : rest.length + j < 1024 := by omega
  have ha1248 : (1248 : W).toNat = 1248 := rfl
  have hf1248 := Monpro.activeWords_fix s 1248 32 (by decide) (by norm_num) hact
  simp [hz,hzn,pr10Newpart2Program,pr10Newpart2Model,runInstructions,runInstr,List.exchange,succ_ofNat_mod,ofNat_add_mod,Nat.add_assoc,State.activeWordsAfterUInt256,literal_eq_ofNat,capacity,ha1248,hf1248]
def pr10Newpart3Program : List Instr :=
  [
  .op .ADD,
   .op (.Dup dA9),
   .push 2 1280,
   .op .MLOAD,
   .op (.Dup dA13),
   .op .MULMOD,
   .op .ADD,
   .op (.Dup dA9)]
def pr10Newpart3Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 : W) (rest : List W) : State :=
  let v0 : W := x0 + x1
  let v1 : W := MachineState.readWord s.memory 1280
  let v2 : W := UInt256.mulMod x12 v1 x10
  let v3 : W := v2 + v0
  {s with pc := N 7240,memory := s.memory,stack := x10::v3::x2::x3::x4::x5::x6::x7::x8::x9::x10::x11::x12::x13::x14::x15::x16::rest}
theorem pr10Newpart3_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions pr10Newpart3Program {s with pc := N 7230,stack := x0::x1::x2::x3::x4::x5::x6::x7::x8::x9::x10::x11::x12::x13::x14::x15::x16::rest} =
      some (pr10Newpart3Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 19) : rest.length + j < 1024 := by omega
  have ha1280 : (1280 : W).toNat = 1280 := rfl
  have hf1280 := Monpro.activeWords_fix s 1280 32 (by decide) (by norm_num) hact
  simp [hz,hzn,pr10Newpart3Program,pr10Newpart3Model,runInstructions,runInstr,List.exchange,succ_ofNat_mod,ofNat_add_mod,Nat.add_assoc,State.activeWordsAfterUInt256,literal_eq_ofNat,capacity,ha1280,hf1280]
def pr10Newpart4Program : List Instr :=
  [
  .op (.Dup dA13),
   .push 2 2720,
   .op .MLOAD,
   .op (.Dup dA2),
   .op (.Swap sA4),
   .op .MUL,
   .op .AND,
   .op (.Swap sA14)]
def pr10Newpart4Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 : W) (rest : List W) : State :=
  let v0 : W := MachineState.readWord s.memory 2720
  let v1 : W := x2 * v0
  let v2 : W := UInt256.land v1 x13
  {s with pc := N 7250,memory := s.memory,stack := x14::x0::x1::x0::x3::x4::x5::x6::x7::x8::x9::x10::x11::x12::x13::v2::x15::x16::rest}
theorem pr10Newpart4_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions pr10Newpart4Program {s with pc := N 7240,stack := x0::x1::x2::x3::x4::x5::x6::x7::x8::x9::x10::x11::x12::x13::x14::x15::x16::rest} =
      some (pr10Newpart4Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 20) : rest.length + j < 1024 := by omega
  have ha2720 : (2720 : W).toNat = 2720 := rfl
  have hf2720 := Monpro.activeWords_fix s 2720 32 (by decide) (by norm_num) hact
  simp [hz,hzn,pr10Newpart4Program,pr10Newpart4Model,runInstructions,runInstr,List.exchange,succ_ofNat_mod,ofNat_add_mod,Nat.add_assoc,State.activeWordsAfterUInt256,literal_eq_ofNat,capacity,ha2720,hf2720]
def pr10Newpart5Program : List Instr :=
  [
  .op (.Dup dA15),
   .op .MULMOD,
   .op .ADD,
   .push 2 2048,
   .op .MULMOD,
   .push 2 2048,
   .op .MLOAD,
   .op (.Dup dA9)]
def pr10Newpart5Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 : W) (rest : List W) : State :=
  let v0 : W := UInt256.mulMod x15 x0 x1
  let v1 : W := v0 + x2
  let v2 : W := UInt256.mulMod (N 2048) v1 x3
  let v3 : W := MachineState.readWord s.memory 2048
  {s with pc := N 7262,memory := s.memory,stack := x11::v3::v2::x4::x5::x6::x7::x8::x9::x10::x11::x12::x13::x14::x15::x16::x17::rest}
theorem pr10Newpart5_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions pr10Newpart5Program {s with pc := N 7250,stack := x0::x1::x2::x3::x4::x5::x6::x7::x8::x9::x10::x11::x12::x13::x14::x15::x16::x17::rest} =
      some (pr10Newpart5Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 19) : rest.length + j < 1024 := by omega
  have ha2048 : (2048 : W).toNat = 2048 := rfl
  have hf2048 := Monpro.activeWords_fix s 2048 32 (by decide) (by norm_num) hact
  simp [hz,hzn,pr10Newpart5Program,pr10Newpart5Model,runInstructions,runInstr,List.exchange,succ_ofNat_mod,ofNat_add_mod,Nat.add_assoc,State.activeWordsAfterUInt256,literal_eq_ofNat,capacity,ha2048,hf2048]
def pr10Newpart6Program : List Instr :=
  [
  .op (.Dup dA1),
   .op (.Dup dA7),
   .op .MULMOD,
   .op (.Dup dA2),
   .op .ADD,
   .op (.Swap sA5),
   .op .MUL,
   .op .ADD]
def pr10Newpart6Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 : W) (rest : List W) : State :=
  let v0 : W := UInt256.mulMod x6 x1 x0
  let v1 : W := x2 + v0
  let v2 : W := x6 * x1
  let v3 : W := v2 + x2
  {s with pc := N 7270,memory := s.memory,stack := v3::x3::x4::x5::v1::x7::x8::x9::x10::x11::x12::x13::x14::x15::x16::rest}
theorem pr10Newpart6_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions pr10Newpart6Program {s with pc := N 7262,stack := x0::x1::x2::x3::x4::x5::x6::x7::x8::x9::x10::x11::x12::x13::x14::x15::x16::rest} =
      some (pr10Newpart6Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 19) : rest.length + j < 1024 := by omega
  simp [hz,hzn,pr10Newpart6Program,pr10Newpart6Model,runInstructions,runInstr,List.exchange,succ_ofNat_mod,ofNat_add_mod,Nat.add_assoc,State.activeWordsAfterUInt256,literal_eq_ofNat,capacity]
def pr10Newpart7Program : List Instr :=
  [
  .push 2 1248,
   .op .MLOAD,
   .op (.Swap sA4),
   .op (.Dup dA9),
   .op (.Dup dA7),
   .push 2 2016,
   .op .MLOAD,
   .op (.Swap sA3)]
def pr10Newpart7Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 : W) (rest : List W) : State :=
  let v0 : W := MachineState.readWord s.memory 1248
  let v1 : W := MachineState.readWord s.memory 2016
  {s with pc := N 7282,memory := s.memory,stack := x0::x5::x8::x4::v1::x1::x2::x3::v0::x5::x6::x7::x8::x9::x10::x11::x12::x13::x14::rest}
theorem pr10Newpart7_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions pr10Newpart7Program {s with pc := N 7270,stack := x0::x1::x2::x3::x4::x5::x6::x7::x8::x9::x10::x11::x12::x13::x14::rest} =
      some (pr10Newpart7Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 19) : rest.length + j < 1024 := by omega
  have ha1248 : (1248 : W).toNat = 1248 := rfl
  have hf1248 := Monpro.activeWords_fix s 1248 32 (by decide) (by norm_num) hact
  have ha2016 : (2016 : W).toNat = 2016 := rfl
  have hf2016 := Monpro.activeWords_fix s 2016 32 (by decide) (by norm_num) hact
  simp [hz,hzn,pr10Newpart7Program,pr10Newpart7Model,runInstructions,runInstr,List.exchange,succ_ofNat_mod,ofNat_add_mod,Nat.add_assoc,State.activeWordsAfterUInt256,literal_eq_ofNat,capacity,ha1248,hf1248,ha2016,hf2016]
def pr10Newpart8Program : List Instr :=
  [
  .op (.Dup dA1),
   .op (.Dup dA5),
   .op .MUL,
   .op .ADD,
   .op (.Swap sA3),
   .op .MULMOD,
   .op .ADD,
   .op (.Dup dA9)]
def pr10Newpart8Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 : W) (rest : List W) : State :=
  let v0 : W := x4 * x1
  let v1 : W := v0 + x0
  let v2 : W := UInt256.mulMod x4 x1 x2
  let v3 : W := v2 + x3
  {s with pc := N 7290,memory := s.memory,stack := x12::v3::v1::x5::x6::x7::x8::x9::x10::x11::x12::x13::x14::x15::x16::x17::x18::rest}
theorem pr10Newpart8_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions pr10Newpart8Program {s with pc := N 7282,stack := x0::x1::x2::x3::x4::x5::x6::x7::x8::x9::x10::x11::x12::x13::x14::x15::x16::x17::x18::rest} =
      some (pr10Newpart8Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 21) : rest.length + j < 1024 := by omega
  simp [hz,hzn,pr10Newpart8Program,pr10Newpart8Model,runInstructions,runInstr,List.exchange,succ_ofNat_mod,ofNat_add_mod,Nat.add_assoc,State.activeWordsAfterUInt256,literal_eq_ofNat,capacity]
def pr10Newpart9Program : List Instr :=
  [
  .push 1 32,
   .op .MLOAD,
   .push 2 1984,
   .op .MLOAD,
   .op (.Swap sA3),
   .op (.Dup dA1),
   .op (.Dup dA5),
   .op .MUL]
def pr10Newpart9Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 : W) (rest : List W) : State :=
  let v0 : W := MachineState.readWord s.memory 32
  let v1 : W := MachineState.readWord s.memory 1984
  let v2 : W := v1 * v0
  {s with pc := N 7301,memory := s.memory,stack := v2::x2::v0::x0::x1::v1::x3::x4::x5::x6::x7::x8::x9::x10::x11::x12::x13::x14::x15::x16::rest}
theorem pr10Newpart9_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions pr10Newpart9Program {s with pc := N 7290,stack := x0::x1::x2::x3::x4::x5::x6::x7::x8::x9::x10::x11::x12::x13::x14::x15::x16::rest} =
      some (pr10Newpart9Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 21) : rest.length + j < 1024 := by omega
  have ha32 : (32 : W).toNat = 32 := rfl
  have hf32 := Monpro.activeWords_fix s 32 32 (by decide) (by norm_num) hact
  have ha1984 : (1984 : W).toNat = 1984 := rfl
  have hf1984 := Monpro.activeWords_fix s 1984 32 (by decide) (by norm_num) hact
  simp [hz,hzn,pr10Newpart9Program,pr10Newpart9Model,runInstructions,runInstr,List.exchange,succ_ofNat_mod,ofNat_add_mod,Nat.add_assoc,State.activeWordsAfterUInt256,literal_eq_ofNat,capacity,ha32,hf32,ha1984,hf1984]
def pr10Newpart10Program : List Instr :=
  [
  .op .ADD,
   .op (.Swap sA3),
   .op .MULMOD,
   .op .ADD,
   .op (.Dup dA9),
   .push 1 64,
   .op .MLOAD,
   .push 2 1952,
   .op .MLOAD]
def pr10Newpart10Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 : W) (rest : List W) : State :=
  let v0 : W := x0 + x1
  let v1 : W := UInt256.mulMod x5 x2 x3
  let v2 : W := v1 + x4
  let v3 : W := MachineState.readWord s.memory 64
  let v4 : W := MachineState.readWord s.memory 1952
  {s with pc := N 7313,memory := s.memory,stack := v4::v3::x13::v2::v0::x6::x7::x8::x9::x10::x11::x12::x13::x14::x15::x16::x17::x18::x19::rest}
theorem pr10Newpart10_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions pr10Newpart10Program {s with pc := N 7301,stack := x0::x1::x2::x3::x4::x5::x6::x7::x8::x9::x10::x11::x12::x13::x14::x15::x16::x17::x18::x19::rest} =
      some (pr10Newpart10Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 20) : rest.length + j < 1024 := by omega
  have ha64 : (64 : W).toNat = 64 := rfl
  have hf64 := Monpro.activeWords_fix s 64 32 (by decide) (by norm_num) hact
  have ha1952 : (1952 : W).toNat = 1952 := rfl
  have hf1952 := Monpro.activeWords_fix s 1952 32 (by decide) (by norm_num) hact
  simp [hz,hzn,pr10Newpart10Program,pr10Newpart10Model,runInstructions,runInstr,List.exchange,succ_ofNat_mod,ofNat_add_mod,Nat.add_assoc,State.activeWordsAfterUInt256,literal_eq_ofNat,capacity,ha64,hf64,ha1952,hf1952]
def pr10Newpart11Program : List Instr :=
  [
  .op (.Swap sA3),
   .op (.Dup dA1),
   .op (.Dup dA5),
   .op .MUL,
   .op .ADD,
   .op (.Swap sA3),
   .op .MULMOD,
   .op .ADD]
def pr10Newpart11Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 : W) (rest : List W) : State :=
  let v0 : W := x0 * x1
  let v1 : W := v0 + x4
  let v2 : W := UInt256.mulMod x0 x1 x2
  let v3 : W := v2 + x3
  {s with pc := N 7321,memory := s.memory,stack := v3::v1::x5::x6::x7::x8::x9::x10::x11::x12::x13::x14::x15::x16::x17::x18::rest}
theorem pr10Newpart11_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions pr10Newpart11Program {s with pc := N 7313,stack := x0::x1::x2::x3::x4::x5::x6::x7::x8::x9::x10::x11::x12::x13::x14::x15::x16::x17::x18::rest} =
      some (pr10Newpart11Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 21) : rest.length + j < 1024 := by omega
  simp [hz,hzn,pr10Newpart11Program,pr10Newpart11Model,runInstructions,runInstr,List.exchange,succ_ofNat_mod,ofNat_add_mod,Nat.add_assoc,State.activeWordsAfterUInt256,literal_eq_ofNat,capacity]
def pr10Newpart12Program : List Instr :=
  [
  .op (.Dup dA9),
   .push 1 96,
   .op .MLOAD,
   .push 2 1920,
   .op .MLOAD]
def pr10Newpart12Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 : W) (rest : List W) : State :=
  let v0 : W := MachineState.readWord s.memory 96
  let v1 : W := MachineState.readWord s.memory 1920
  {s with pc := N 7329,memory := s.memory,stack := v1::v0::x9::x0::x1::x2::x3::x4::x5::x6::x7::x8::x9::x10::x11::x12::x13::x14::x15::rest}
theorem pr10Newpart12_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions pr10Newpart12Program {s with pc := N 7321,stack := x0::x1::x2::x3::x4::x5::x6::x7::x8::x9::x10::x11::x12::x13::x14::x15::rest} =
      some (pr10Newpart12Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 19) : rest.length + j < 1024 := by omega
  have ha96 : (96 : W).toNat = 96 := rfl
  have hf96 := Monpro.activeWords_fix s 96 32 (by decide) (by norm_num) hact
  have ha1920 : (1920 : W).toNat = 1920 := rfl
  have hf1920 := Monpro.activeWords_fix s 1920 32 (by decide) (by norm_num) hact
  simp [hz,hzn,pr10Newpart12Program,pr10Newpart12Model,runInstructions,runInstr,List.exchange,succ_ofNat_mod,ofNat_add_mod,Nat.add_assoc,State.activeWordsAfterUInt256,literal_eq_ofNat,capacity,ha96,hf96,ha1920,hf1920]
def pr10NewProgram : List Instr :=
  [
  .op .ADD,
   .op (.Dup dA9),
   .push 0 0,
   .op .MLOAD,
   .op (.Dup dA9),
   .op .MULMOD,
   .op .ADD,
   .op (.Dup dA9),
   .push 1 224,
   .op .MLOAD,
   .op (.Dup dA6),
   .op .MULMOD,
   .op .ADD,
   .op (.Dup dA9),
   .op (.Dup dA15),
   .push 2 1216,
   .op .MLOAD,
   .op .MULMOD,
   .op .ADD,
   .op (.Dup dA15),
   .op (.Dup dA10),
   .op (.Swap sA0),
   .push 2 1248,
   .op .MLOAD,
   .op .MULMOD,
   .op .ADD,
   .op (.Dup dA9),
   .push 2 1280,
   .op .MLOAD,
   .op (.Dup dA13),
   .op .MULMOD,
   .op .ADD,
   .op (.Dup dA9),
   .op (.Dup dA13),
   .push 2 2720,
   .op .MLOAD,
   .op (.Dup dA2),
   .op (.Swap sA4),
   .op .MUL,
   .op .AND,
   .op (.Swap sA14),
   .op (.Dup dA15),
   .op .MULMOD,
   .op .ADD,
   .push 2 2048,
   .op .MULMOD,
   .push 2 2048,
   .op .MLOAD,
   .op (.Dup dA9),
   .op (.Dup dA1),
   .op (.Dup dA7),
   .op .MULMOD,
   .op (.Dup dA2),
   .op .ADD,
   .op (.Swap sA5),
   .op .MUL,
   .op .ADD,
   .push 2 1248,
   .op .MLOAD,
   .op (.Swap sA4),
   .op (.Dup dA9),
   .op (.Dup dA7),
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
   .push 1 32,
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
   .push 1 64,
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
   .push 1 96,
   .op .MLOAD,
   .push 2 1920,
   .op .MLOAD]
def pr10NewModel (s : State) (carry w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 : W) (rest : List W) : State :=
  let v0 : W := carry + w0
  let v1 : W := MachineState.readWord s.memory 0
  let v2 : W := UInt256.mulMod w7 v1 w9
  let v3 : W := v2 + v0
  let v4 : W := MachineState.readWord s.memory 224
  let v5 : W := UInt256.mulMod w4 v4 w9
  let v6 : W := v5 + v3
  let v7 : W := MachineState.readWord s.memory 1216
  let v8 : W := UInt256.mulMod v7 w14 w9
  let v9 : W := v8 + v6
  let v10 : W := MachineState.readWord s.memory 1248
  let v11 : W := UInt256.mulMod v10 w15 w9
  let v12 : W := v11 + v9
  let v13 : W := MachineState.readWord s.memory 1280
  let v14 : W := UInt256.mulMod w11 v13 w9
  let v15 : W := v14 + v12
  let v16 : W := MachineState.readWord s.memory 2720
  let v17 : W := w1 * v16
  let v18 : W := UInt256.land v17 w12
  let v19 : W := UInt256.mulMod v18 w13 w9
  let v20 : W := v19 + v15
  let v21 : W := UInt256.mulMod (N 2048) v20 w9
  let v22 : W := MachineState.readWord s.memory 2048
  let v23 : W := UInt256.mulMod w5 v22 w9
  let v24 : W := v21 + v23
  let v25 : W := w5 * v22
  let v26 : W := v25 + v21
  let v27 : W := MachineState.readWord s.memory 1248
  let v28 : W := MachineState.readWord s.memory 2016
  let v29 : W := v28 * w6
  let v30 : W := v29 + v26
  let v31 : W := UInt256.mulMod v28 w6 w9
  let v32 : W := v31 + v24
  let v33 : W := MachineState.readWord s.memory 32
  let v34 : W := MachineState.readWord s.memory 1984
  let v35 : W := v34 * v33
  let v36 : W := v35 + v30
  let v37 : W := UInt256.mulMod v34 v33 w9
  let v38 : W := v37 + v32
  let v39 : W := MachineState.readWord s.memory 64
  let v40 : W := MachineState.readWord s.memory 1952
  let v41 : W := v40 * v39
  let v42 : W := v41 + v36
  let v43 : W := UInt256.mulMod v40 v39 w9
  let v44 : W := v43 + v38
  let v45 : W := MachineState.readWord s.memory 96
  let v46 : W := MachineState.readWord s.memory 1920
  {s with pc := N 7329,memory := s.memory,stack := v46::v45::w9::v44::v42::w2::w3::w4::v27::w6::w7::w8::w9::w10::w11::w12::v18::w14::w15::rest}
theorem pr10New_run (s : State) (carry w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions pr10NewProgram {s with pc := N 7200,stack := carry::w0::w1::w2::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::rest} =
      some (pr10NewModel s carry w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 rest) := by
  let v0 : W := carry + w0
  let v1 : W := MachineState.readWord s.memory 0
  let v2 : W := UInt256.mulMod w7 v1 w9
  let v3 : W := v2 + v0
  let v4 : W := MachineState.readWord s.memory 224
  let v5 : W := UInt256.mulMod w4 v4 w9
  let v6 : W := v5 + v3
  let v7 : W := MachineState.readWord s.memory 1216
  let v8 : W := UInt256.mulMod v7 w14 w9
  let v9 : W := v8 + v6
  let v10 : W := MachineState.readWord s.memory 1248
  let v11 : W := UInt256.mulMod v10 w15 w9
  let v12 : W := v11 + v9
  let v13 : W := MachineState.readWord s.memory 1280
  let v14 : W := UInt256.mulMod w11 v13 w9
  let v15 : W := v14 + v12
  let v16 : W := MachineState.readWord s.memory 2720
  let v17 : W := w1 * v16
  let v18 : W := UInt256.land v17 w12
  let v19 : W := UInt256.mulMod v18 w13 w9
  let v20 : W := v19 + v15
  let v21 : W := UInt256.mulMod (N 2048) v20 w9
  let v22 : W := MachineState.readWord s.memory 2048
  let v23 : W := UInt256.mulMod w5 v22 w9
  let v24 : W := v21 + v23
  let v25 : W := w5 * v22
  let v26 : W := v25 + v21
  let v27 : W := MachineState.readWord s.memory 1248
  let v28 : W := MachineState.readWord s.memory 2016
  let v29 : W := v28 * w6
  let v30 : W := v29 + v26
  let v31 : W := UInt256.mulMod v28 w6 w9
  let v32 : W := v31 + v24
  let v33 : W := MachineState.readWord s.memory 32
  let v34 : W := MachineState.readWord s.memory 1984
  let v35 : W := v34 * v33
  let v36 : W := v35 + v30
  let v37 : W := UInt256.mulMod v34 v33 w9
  let v38 : W := v37 + v32
  let v39 : W := MachineState.readWord s.memory 64
  let v40 : W := MachineState.readWord s.memory 1952
  let v41 : W := v40 * v39
  let v42 : W := v41 + v36
  let v43 : W := UInt256.mulMod v40 v39 w9
  let v44 : W := v43 + v38
  let v45 : W := MachineState.readWord s.memory 96
  let v46 : W := MachineState.readWord s.memory 1920
  have h0 : runInstructions pr10Newpart0Program {s with pc := N 7200,memory := s.memory,stack := carry::w0::w1::w2::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::rest} = some {s with pc := N 7208,memory := s.memory,stack := w9::v3::w1::w2::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::rest} := by
    simpa only [pr10Newpart0Model,v0,v1,v2,v3] using pr10Newpart0_run (s) (carry) w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 rest hcap hact
  have h1 : runInstructions pr10Newpart1Program {s with pc := N 7208,memory := s.memory,stack := w9::v3::w1::w2::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::rest} = some {s with pc := N 7220,memory := s.memory,stack := v7::w14::w9::v6::w1::w2::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::rest} := by
    simpa only [pr10Newpart1Model,v4,v5,v6,v7] using pr10Newpart1_run (s) w9 v3 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 rest hcap hact
  have h2 : runInstructions pr10Newpart2Program {s with pc := N 7220,memory := s.memory,stack := v7::w14::w9::v6::w1::w2::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::rest} = some {s with pc := N 7230,memory := s.memory,stack := v11::v9::w1::w2::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::rest} := by
    simpa only [pr10Newpart2Model,v8,v9,v10,v11] using pr10Newpart2_run (s) v7 w14 w9 v6 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 rest hcap hact
  have h3 : runInstructions pr10Newpart3Program {s with pc := N 7230,memory := s.memory,stack := v11::v9::w1::w2::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::rest} = some {s with pc := N 7240,memory := s.memory,stack := w9::v15::w1::w2::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::rest} := by
    simpa only [pr10Newpart3Model,v12,v13,v14,v15] using pr10Newpart3_run (s) v11 v9 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 rest hcap hact
  have h4 : runInstructions pr10Newpart4Program {s with pc := N 7240,memory := s.memory,stack := w9::v15::w1::w2::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::rest} = some {s with pc := N 7250,memory := s.memory,stack := w13::w9::v15::w9::w2::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::v18::w14::w15::rest} := by
    simpa only [pr10Newpart4Model,v16,v17,v18] using pr10Newpart4_run (s) w9 v15 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 rest hcap hact
  have h5 : runInstructions pr10Newpart5Program {s with pc := N 7250,memory := s.memory,stack := w13::w9::v15::w9::w2::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::v18::w14::w15::rest} = some {s with pc := N 7262,memory := s.memory,stack := w9::v22::v21::w2::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::v18::w14::w15::rest} := by
    simpa only [pr10Newpart5Model,v19,v20,v21,v22] using pr10Newpart5_run (s) w13 w9 v15 w9 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 v18 w14 w15 rest hcap hact
  have h6 : runInstructions pr10Newpart6Program {s with pc := N 7262,memory := s.memory,stack := w9::v22::v21::w2::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::v18::w14::w15::rest} = some {s with pc := N 7270,memory := s.memory,stack := v26::w2::w3::w4::v24::w6::w7::w8::w9::w10::w11::w12::v18::w14::w15::rest} := by
    simpa only [pr10Newpart6Model,v23,v24,v25,v26] using pr10Newpart6_run (s) w9 v22 v21 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 v18 w14 w15 rest hcap hact
  have h7 : runInstructions pr10Newpart7Program {s with pc := N 7270,memory := s.memory,stack := v26::w2::w3::w4::v24::w6::w7::w8::w9::w10::w11::w12::v18::w14::w15::rest} = some {s with pc := N 7282,memory := s.memory,stack := v26::w6::w9::v24::v28::w2::w3::w4::v27::w6::w7::w8::w9::w10::w11::w12::v18::w14::w15::rest} := by
    simpa only [pr10Newpart7Model,v27,v28] using pr10Newpart7_run (s) v26 w2 w3 w4 v24 w6 w7 w8 w9 w10 w11 w12 v18 w14 w15 rest hcap hact
  have h8 : runInstructions pr10Newpart8Program {s with pc := N 7282,memory := s.memory,stack := v26::w6::w9::v24::v28::w2::w3::w4::v27::w6::w7::w8::w9::w10::w11::w12::v18::w14::w15::rest} = some {s with pc := N 7290,memory := s.memory,stack := w9::v32::v30::w2::w3::w4::v27::w6::w7::w8::w9::w10::w11::w12::v18::w14::w15::rest} := by
    simpa only [pr10Newpart8Model,v29,v30,v31,v32] using pr10Newpart8_run (s) v26 w6 w9 v24 v28 w2 w3 w4 v27 w6 w7 w8 w9 w10 w11 w12 v18 w14 w15 rest hcap hact
  have h9 : runInstructions pr10Newpart9Program {s with pc := N 7290,memory := s.memory,stack := w9::v32::v30::w2::w3::w4::v27::w6::w7::w8::w9::w10::w11::w12::v18::w14::w15::rest} = some {s with pc := N 7301,memory := s.memory,stack := v35::v30::v33::w9::v32::v34::w2::w3::w4::v27::w6::w7::w8::w9::w10::w11::w12::v18::w14::w15::rest} := by
    simpa only [pr10Newpart9Model,v33,v34,v35] using pr10Newpart9_run (s) w9 v32 v30 w2 w3 w4 v27 w6 w7 w8 w9 w10 w11 w12 v18 w14 w15 rest hcap hact
  have h10 : runInstructions pr10Newpart10Program {s with pc := N 7301,memory := s.memory,stack := v35::v30::v33::w9::v32::v34::w2::w3::w4::v27::w6::w7::w8::w9::w10::w11::w12::v18::w14::w15::rest} = some {s with pc := N 7313,memory := s.memory,stack := v40::v39::w9::v38::v36::w2::w3::w4::v27::w6::w7::w8::w9::w10::w11::w12::v18::w14::w15::rest} := by
    simpa only [pr10Newpart10Model,v36,v37,v38,v39,v40] using pr10Newpart10_run (s) v35 v30 v33 w9 v32 v34 w2 w3 w4 v27 w6 w7 w8 w9 w10 w11 w12 v18 w14 w15 rest hcap hact
  have h11 : runInstructions pr10Newpart11Program {s with pc := N 7313,memory := s.memory,stack := v40::v39::w9::v38::v36::w2::w3::w4::v27::w6::w7::w8::w9::w10::w11::w12::v18::w14::w15::rest} = some {s with pc := N 7321,memory := s.memory,stack := v44::v42::w2::w3::w4::v27::w6::w7::w8::w9::w10::w11::w12::v18::w14::w15::rest} := by
    simpa only [pr10Newpart11Model,v41,v42,v43,v44] using pr10Newpart11_run (s) v40 v39 w9 v38 v36 w2 w3 w4 v27 w6 w7 w8 w9 w10 w11 w12 v18 w14 w15 rest hcap hact
  have h12 : runInstructions pr10Newpart12Program {s with pc := N 7321,memory := s.memory,stack := v44::v42::w2::w3::w4::v27::w6::w7::w8::w9::w10::w11::w12::v18::w14::w15::rest} = some {s with pc := N 7329,memory := s.memory,stack := v46::v45::w9::v44::v42::w2::w3::w4::v27::w6::w7::w8::w9::w10::w11::w12::v18::w14::w15::rest} := by
    simpa only [pr10Newpart12Model,v45,v46] using pr10Newpart12_run (s) v44 v42 w2 w3 w4 v27 w6 w7 w8 w9 w10 w11 w12 v18 w14 w15 rest hcap hact
  exact (runInstructions_append_some _ _ _ _ _ h0 (runInstructions_append_some _ _ _ _ _ h1 (runInstructions_append_some _ _ _ _ _ h2 (runInstructions_append_some _ _ _ _ _ h3 (runInstructions_append_some _ _ _ _ _ h4 (runInstructions_append_some _ _ _ _ _ h5 (runInstructions_append_some _ _ _ _ _ h6 (runInstructions_append_some _ _ _ _ _ h7 (runInstructions_append_some _ _ _ _ _ h8 (runInstructions_append_some _ _ _ _ _ h9 (runInstructions_append_some _ _ _ _ _ h10 (runInstructions_append_some _ _ _ _ _ h11 h12))))))))))))
#print axioms pr10New_run
def productColumn10Model (s : State) (carry w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 : W) (rest : List W) : State :=
  let v0 : W := carry + w0
  let v1 : W := MachineState.readWord s.memory 0
  let v2 : W := UInt256.mulMod w7 v1 w9
  let v3 : W := v2 + v0
  let v4 : W := MachineState.readWord s.memory 224
  let v5 : W := UInt256.mulMod w4 v4 w9
  let v6 : W := v5 + v3
  let v7 : W := MachineState.readWord s.memory 1216
  let v8 : W := UInt256.mulMod v7 w14 w9
  let v9 : W := v8 + v6
  let v10 : W := MachineState.readWord s.memory 1248
  let v11 : W := UInt256.mulMod v10 w15 w9
  let v12 : W := v11 + v9
  let v13 : W := MachineState.readWord s.memory 1280
  let v14 : W := UInt256.mulMod w11 v13 w9
  let v15 : W := v14 + v12
  let v16 : W := MachineState.readWord s.memory 2720
  let v17 : W := w1 * v16
  let v18 : W := UInt256.land v17 w12
  let v19 : W := UInt256.mulMod w13 v18 w9
  let v20 : W := v19 + v15
  let v21 : W := UInt256.mulMod (N 2048) v20 w9
  let v22 : W := MachineState.readWord s.memory 1248
  let v23 : W := MachineState.readWord s.memory 2048
  let v24 : W := v23 * w5
  let v25 : W := v24 + v21
  let v26 : W := UInt256.mulMod v23 w5 w9
  let v27 : W := v26 + v21
  let v28 : W := MachineState.readWord s.memory 2016
  let v29 : W := v28 * w6
  let v30 : W := v29 + v25
  let v31 : W := UInt256.mulMod v28 w6 w9
  let v32 : W := v31 + v27
  let v33 : W := MachineState.readWord s.memory 32
  let v34 : W := MachineState.readWord s.memory 1984
  let v35 : W := v34 * v33
  let v36 : W := v35 + v30
  let v37 : W := UInt256.mulMod v34 v33 w9
  let v38 : W := v37 + v32
  let v39 : W := MachineState.readWord s.memory 64
  let v40 : W := MachineState.readWord s.memory 1952
  let v41 : W := v40 * v39
  let v42 : W := v41 + v36
  let v43 : W := UInt256.mulMod v40 v39 w9
  let v44 : W := v43 + v38
  let v45 : W := MachineState.readWord s.memory 96
  let v46 : W := MachineState.readWord s.memory 1920
  {s with pc := N 7329,memory := s.memory,stack := v46::v45::w9::v44::v42::w2::w3::w4::v22::w6::w7::w8::w9::w10::w11::w12::v18::w14::w15::rest}
def productColumn10Program : List Instr := pr10NewProgram
private theorem aux_shared0 (w9 w13 : W) (z0 : W) :
    (UInt256.mulMod z0 w13 w9) = (UInt256.mulMod w13 z0 w9) := by
  simp (disch := decide) only [addC,addA,addL,mulC,mmC,amC,andC,orC,xorC,eqC,read_disjoint,Challenge.EvmProof.Memory.readWord_writeWord]
private theorem aux_shared1 (w5 w9 : W) (z0 : W) :
    (UInt256.mulMod w5 z0 w9) = (UInt256.mulMod z0 w5 w9) := by
  simp (disch := decide) only [addC,addA,addL,mulC,mmC,amC,andC,orC,xorC,eqC,read_disjoint,Challenge.EvmProof.Memory.readWord_writeWord]
private theorem aux_shared2 (z0 z1 : W) :
    (z0 + z1) = (z1 + z0) := by
  simp (disch := decide) only [addC,addA,addL,mulC,mmC,amC,andC,orC,xorC,eqC,read_disjoint,Challenge.EvmProof.Memory.readWord_writeWord]
private theorem aux_shared3 (w5 : W) (z0 : W) :
    (w5 * z0) = (z0 * w5) := by
  simp (disch := decide) only [addC,addA,addL,mulC,mmC,amC,andC,orC,xorC,eqC,read_disjoint,Challenge.EvmProof.Memory.readWord_writeWord]
private theorem prepared_model_eq (s : State) (carry w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 : W) (rest : List W) :
    productColumn10Model s carry w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 rest = pr10NewModel s carry w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 rest := by
  let o0 : W := carry + w0
  let o1 : W := MachineState.readWord s.memory 0
  let o2 : W := UInt256.mulMod w7 o1 w9
  let o3 : W := o2 + o0
  let o4 : W := MachineState.readWord s.memory 224
  let o5 : W := UInt256.mulMod w4 o4 w9
  let o6 : W := o5 + o3
  let o7 : W := MachineState.readWord s.memory 1216
  let o8 : W := UInt256.mulMod o7 w14 w9
  let o9 : W := o8 + o6
  let o10 : W := MachineState.readWord s.memory 1248
  let o11 : W := UInt256.mulMod o10 w15 w9
  let o12 : W := o11 + o9
  let o13 : W := MachineState.readWord s.memory 1280
  let o14 : W := UInt256.mulMod w11 o13 w9
  let o15 : W := o14 + o12
  let o16 : W := MachineState.readWord s.memory 2720
  let o17 : W := w1 * o16
  let o18 : W := UInt256.land o17 w12
  let o19 : W := UInt256.mulMod w13 o18 w9
  let o20 : W := o19 + o15
  let o21 : W := UInt256.mulMod (N 2048) o20 w9
  let o22 : W := MachineState.readWord s.memory 1248
  let o23 : W := MachineState.readWord s.memory 2048
  let o24 : W := o23 * w5
  let o25 : W := o24 + o21
  let o26 : W := UInt256.mulMod o23 w5 w9
  let o27 : W := o26 + o21
  let o28 : W := MachineState.readWord s.memory 2016
  let o29 : W := o28 * w6
  let o30 : W := o29 + o25
  let o31 : W := UInt256.mulMod o28 w6 w9
  let o32 : W := o31 + o27
  let o33 : W := MachineState.readWord s.memory 32
  let o34 : W := MachineState.readWord s.memory 1984
  let o35 : W := o34 * o33
  let o36 : W := o35 + o30
  let o37 : W := UInt256.mulMod o34 o33 w9
  let o38 : W := o37 + o32
  let o39 : W := MachineState.readWord s.memory 64
  let o40 : W := MachineState.readWord s.memory 1952
  let o41 : W := o40 * o39
  let o42 : W := o41 + o36
  let o43 : W := UInt256.mulMod o40 o39 w9
  let o44 : W := o43 + o38
  let o45 : W := MachineState.readWord s.memory 96
  let o46 : W := MachineState.readWord s.memory 1920
  let n0 : W := carry + w0
  let n1 : W := MachineState.readWord s.memory 0
  let n2 : W := UInt256.mulMod w7 n1 w9
  let n3 : W := n2 + n0
  let n4 : W := MachineState.readWord s.memory 224
  let n5 : W := UInt256.mulMod w4 n4 w9
  let n6 : W := n5 + n3
  let n7 : W := MachineState.readWord s.memory 1216
  let n8 : W := UInt256.mulMod n7 w14 w9
  let n9 : W := n8 + n6
  let n10 : W := MachineState.readWord s.memory 1248
  let n11 : W := UInt256.mulMod n10 w15 w9
  let n12 : W := n11 + n9
  let n13 : W := MachineState.readWord s.memory 1280
  let n14 : W := UInt256.mulMod w11 n13 w9
  let n15 : W := n14 + n12
  let n16 : W := MachineState.readWord s.memory 2720
  let n17 : W := w1 * n16
  let n18 : W := UInt256.land n17 w12
  let n19 : W := UInt256.mulMod n18 w13 w9
  let n20 : W := n19 + n15
  let n21 : W := UInt256.mulMod (N 2048) n20 w9
  let n22 : W := MachineState.readWord s.memory 2048
  let n23 : W := UInt256.mulMod w5 n22 w9
  let n24 : W := n21 + n23
  let n25 : W := w5 * n22
  let n26 : W := n25 + n21
  let n27 : W := MachineState.readWord s.memory 1248
  let n28 : W := MachineState.readWord s.memory 2016
  let n29 : W := n28 * w6
  let n30 : W := n29 + n26
  let n31 : W := UInt256.mulMod n28 w6 w9
  let n32 : W := n31 + n24
  let n33 : W := MachineState.readWord s.memory 32
  let n34 : W := MachineState.readWord s.memory 1984
  let n35 : W := n34 * n33
  let n36 : W := n35 + n30
  let n37 : W := UInt256.mulMod n34 n33 w9
  let n38 : W := n37 + n32
  let n39 : W := MachineState.readWord s.memory 64
  let n40 : W := MachineState.readWord s.memory 1952
  let n41 : W := n40 * n39
  let n42 : W := n41 + n36
  let n43 : W := UInt256.mulMod n40 n39 w9
  let n44 : W := n43 + n38
  let n45 : W := MachineState.readWord s.memory 96
  let n46 : W := MachineState.readWord s.memory 1920
  have eq_o22 : o22 = o10 := by
    simp only [o22,o10]
  have eq_n0 : n0 = o0 := by
    simp only [n0,o0]
  have eq_n1 : n1 = o1 := by
    simp only [n1,o1]
  have eq_n2 : n2 = o2 := by
    simp only [n2,o2,eq_n1]
  have eq_n3 : n3 = o3 := by
    simp only [n3,o3,eq_n2,eq_n0]
  have eq_n4 : n4 = o4 := by
    simp only [n4,o4]
  have eq_n5 : n5 = o5 := by
    simp only [n5,o5,eq_n4]
  have eq_n6 : n6 = o6 := by
    simp only [n6,o6,eq_n5,eq_n3]
  have eq_n7 : n7 = o7 := by
    simp only [n7,o7]
  have eq_n8 : n8 = o8 := by
    simp only [n8,o8,eq_n7]
  have eq_n9 : n9 = o9 := by
    simp only [n9,o9,eq_n8,eq_n6]
  have eq_n10 : n10 = o10 := by
    simp only [n10,o10]
  have eq_n11 : n11 = o11 := by
    simp only [n11,o11,eq_n10]
  have eq_n12 : n12 = o12 := by
    simp only [n12,o12,eq_n11,eq_n9]
  have eq_n13 : n13 = o13 := by
    simp only [n13,o13]
  have eq_n14 : n14 = o14 := by
    simp only [n14,o14,eq_n13]
  have eq_n15 : n15 = o15 := by
    simp only [n15,o15,eq_n14,eq_n12]
  have eq_n16 : n16 = o16 := by
    simp only [n16,o16]
  have eq_n17 : n17 = o17 := by
    simp only [n17,o17,eq_n16]
  have eq_n18 : n18 = o18 := by
    simp only [n18,o18,eq_n17]
  have eq_n19 : n19 = o19 := by
    simpa only [n19,o19,eq_n18] using
      (aux_shared0 w9 w13 o18)
  have eq_n20 : n20 = o20 := by
    simp only [n20,o20,eq_n19,eq_n15]
  have eq_n21 : n21 = o21 := by
    simp only [n21,o21,eq_n20]
  have eq_n22 : n22 = o23 := by
    simp only [n22,o23]
  have eq_n23 : n23 = o26 := by
    simpa only [n23,o26,eq_n22] using
      (aux_shared1 w5 w9 o23)
  have eq_n24 : n24 = o27 := by
    simpa only [n24,o27,eq_n21,eq_n23] using
      (aux_shared2  o21 o26)
  have eq_n25 : n25 = o24 := by
    simpa only [n25,o24,eq_n22] using
      (aux_shared3 w5 o23)
  have eq_n26 : n26 = o25 := by
    simp only [n26,o25,eq_n25,eq_n21]
  have eq_n27 : n27 = o10 := by
    simp only [n27,o10]
  have eq_n28 : n28 = o28 := by
    simp only [n28,o28]
  have eq_n29 : n29 = o29 := by
    simp only [n29,o29,eq_n28]
  have eq_n30 : n30 = o30 := by
    simp only [n30,o30,eq_n29,eq_n26]
  have eq_n31 : n31 = o31 := by
    simp only [n31,o31,eq_n28]
  have eq_n32 : n32 = o32 := by
    simp only [n32,o32,eq_n31,eq_n24]
  have eq_n33 : n33 = o33 := by
    simp only [n33,o33]
  have eq_n34 : n34 = o34 := by
    simp only [n34,o34]
  have eq_n35 : n35 = o35 := by
    simp only [n35,o35,eq_n34,eq_n33]
  have eq_n36 : n36 = o36 := by
    simp only [n36,o36,eq_n35,eq_n30]
  have eq_n37 : n37 = o37 := by
    simp only [n37,o37,eq_n34,eq_n33]
  have eq_n38 : n38 = o38 := by
    simp only [n38,o38,eq_n37,eq_n32]
  have eq_n39 : n39 = o39 := by
    simp only [n39,o39]
  have eq_n40 : n40 = o40 := by
    simp only [n40,o40]
  have eq_n41 : n41 = o41 := by
    simp only [n41,o41,eq_n40,eq_n39]
  have eq_n42 : n42 = o42 := by
    simp only [n42,o42,eq_n41,eq_n36]
  have eq_n43 : n43 = o43 := by
    simp only [n43,o43,eq_n40,eq_n39]
  have eq_n44 : n44 = o44 := by
    simp only [n44,o44,eq_n43,eq_n38]
  have eq_n45 : n45 = o45 := by
    simp only [n45,o45]
  have eq_n46 : n46 = o46 := by
    simp only [n46,o46]
  change {s with pc := N 7329,memory := s.memory,stack := o46::o45::w9::o44::o42::w2::w3::w4::o22::w6::w7::w8::w9::w10::w11::w12::o18::w14::w15::rest} =
    {s with pc := N 7329,memory := s.memory,stack := n46::n45::w9::n44::n42::w2::w3::w4::n27::w6::w7::w8::w9::w10::w11::w12::n18::w14::w15::rest}
  simp only [eq_o22,eq_n0,eq_n1,eq_n2,eq_n3,eq_n4,eq_n5,eq_n6,eq_n7,eq_n8,eq_n9,eq_n10,eq_n11,eq_n12,eq_n13,eq_n14,eq_n15,eq_n16,eq_n17,eq_n18,eq_n19,eq_n20,eq_n21,eq_n22,eq_n23,eq_n24,eq_n25,eq_n26,eq_n27,eq_n28,eq_n29,eq_n30,eq_n31,eq_n32,eq_n33,eq_n34,eq_n35,eq_n36,eq_n37,eq_n38,eq_n39,eq_n40,eq_n41,eq_n42,eq_n43,eq_n44,eq_n45,eq_n46]
theorem productColumn10_run (s : State) (carry w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions productColumn10Program {s with pc := N 7200,stack := carry::w0::w1::w2::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::rest} =
      some (productColumn10Model s carry w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 rest) := by
  exact (pr10New_run s carry w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 rest hcap hact).trans
    (congrArg some (prepared_model_eq s carry w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 rest).symm)
#print axioms productColumn10_run
end CycleSubmission.Execution
