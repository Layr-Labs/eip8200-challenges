import Challenge.Modexp.Submission.Proofs.Prepared.StackArgs
import Challenge.Modexp.Submission.Proofs.Cycle.Execution.Product18
import Challenge.Modexp.Submission.Proofs.Cycle.Execution.Product19
import Challenge.Modexp.Submission.Proofs.Prepared.Arithmetic
import Challenge.Modexp.Submission.Proofs.Fast.Monpro
import Challenge.Modexp.Submission.Proofs.Bytecode.WindowNibbleDefs
open CycleSubmission.SharedStackArgs
set_option warningAsError true
set_option linter.unnecessarySimpa false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option maxRecDepth 40000
set_option maxHeartbeats 8000000
namespace CycleSubmission.Prepared.ProductGroup10052
open EvmSemantics EvmSemantics.EVM YulEvmCompiler
open Challenge.Modexp.Submission.Proofs.Bytecode.WindowNibbleKernel
open Challenge.Modexp.Submission.Proofs.Fast
open CycleSubmission.Prepared.Arithmetic CycleSubmission.Execution
open Challenge.EvmProof.Word Challenge.EvmProof.Stepper
local notation "W" => UInt256
local notation "N" => UInt256.ofNat
def oldModel (s : State) (carry w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 : W) (rest : List W) : State :=
  let v0 : W := carry * w0
  let v1 : W := v0 + w1
  let v2 : W := UInt256.mulMod w5 w2 w3
  let v3 : W := v2 + w4
  let v4 : W := w14 * w9
  let v5 : W := v4 + v1
  let v6 : W := w12 * w15
  let v7 : W := v6 + v5
  let v8 : W := w7 * w17
  let v9 : W := v8 + v7
  let v10 : W := UInt256.mulMod w14 w9 w13
  let v11 : W := v10 + v3
  let v12 : W := UInt256.mulMod w12 w15 w13
  let v13 : W := v12 + v11
  let v14 : W := UInt256.mulMod w7 w17 w13
  let v15 : W := v14 + v13
  let v16 : W := UInt256.land w16 v9
  let v17 : ByteArray := MachineState.writeBytes s.memory (Data.Bytes.natToBytesPadded v16.toNat 32) 96
  let v18 : W := v15 - v16
  let v19 : W := w13 + v18
  let v20 : W := UInt256.mulMod v19 (N 2048) w13
  let v21 : W := MachineState.readWord v17 2048
  let v22 : W := MachineState.readWord v17 160
  let v23 : W := MachineState.readWord v17 800
  let v24 : W := v21 * v22
  let v25 : W := v24 + v20
  let v26 : W := UInt256.mulMod v21 v22 w13
  let v27 : W := v26 + v20
  let v28 : W := MachineState.readWord v17 2016
  let v29 : W := v28 * w6
  let v30 : W := v29 + v25
  let v31 : W := UInt256.mulMod v28 w6 w13
  let v32 : W := v31 + v27
  let v33 : W := w14 * w15
  let v34 : W := v33 + v30
  let v35 : W := w12 * w17
  let v36 : W := v35 + v34
  let v37 : W := UInt256.mulMod w14 w15 w13
  let v38 : W := v37 + v32
  let v39 : W := UInt256.mulMod w12 w17 w13
  let v40 : W := v39 + v38
  let v41 : W := UInt256.land w16 v36
  let v42 : ByteArray := MachineState.writeBytes v17 (Data.Bytes.natToBytesPadded v41.toNat 32) 128
  let v43 : W := v40 - v41
  let v44 : W := w13 + v43
  let v45 : W := UInt256.mulMod v44 (N 2048) w13
  let v46 : W := MachineState.readWord v42 2048
  let v47 : W := UInt256.mulMod v46 w6 w13
  let v48 : W := v47 + v45
  let v49 : W := v46 * w6
  let v50 : W := v49 + v45
  let v51 : W := w14 * w17
  let v52 : W := v51 + v50
  let v53 : W := UInt256.mulMod w14 w17 w13
  let v54 : W := v53 + v48
  let v55 : W := UInt256.land w16 v52
  let v56 : W := v54 - v55
  let v57 : W := w13 + v56
  let v58 : W := UInt256.mulMod v57 (N 2048) w13
  let v59 : ByteArray := MachineState.writeBytes v42 (Data.Bytes.natToBytesPadded v55.toNat 32) 160
  {s with pc := N 8138,memory := v59,stack := w19::w7::w8::v23::w10::w11::w12::w13::w14::w15::w16::w17::w18::v58::rest}
def newpart0Program : List Instr :=
  [
  .op .MUL,
   .op .ADD,
   .op (.Swap sA3),
   .op .MULMOD,
   .op .ADD,
   .op (.Swap sA0),
   .op (.Dup dA5),
   .op (.Dup dA11)]
def newpart0Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 : W) (rest : List W) : State :=
  let v0 : W := x0 * x1
  let v1 : W := v0 + x2
  let v2 : W := UInt256.mulMod x6 x3 x4
  let v3 : W := v2 + x5
  {s with pc := N 7984,memory := s.memory,stack := x15::x10::v1::v3::x7::x8::x9::x10::x11::x12::x13::x14::x15::x16::x17::x18::x19::x20::rest}
theorem newpart0_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions newpart0Program {s with pc := N 7976,stack := x0::x1::x2::x3::x4::x5::x6::x7::x8::x9::x10::x11::x12::x13::x14::x15::x16::x17::x18::x19::x20::rest} =
      some (newpart0Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 21) : rest.length + j < 1024 := by omega
  simp [hz,hzn,newpart0Program,newpart0Model,runInstructions,runInstr,List.exchange,succ_ofNat_mod,ofNat_add_mod,Nat.add_assoc,State.activeWordsAfterUInt256,literal_eq_ofNat,capacity]
def newpart1Program : List Instr :=
  [
  .op .MUL,
   .op .ADD,
   .op (.Dup dA11),
   .op (.Dup dA9),
   .op .MUL,
   .op .ADD,
   .op (.Dup dA13),
   .op (.Dup dA4)]
def newpart1Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 : W) (rest : List W) : State :=
  let v0 : W := x0 * x1
  let v1 : W := v0 + x2
  let v2 : W := x10 * x13
  let v3 : W := v2 + v1
  {s with pc := N 7992,memory := s.memory,stack := x5::x15::v3::x3::x4::x5::x6::x7::x8::x9::x10::x11::x12::x13::x14::x15::x16::x17::rest}
theorem newpart1_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions newpart1Program {s with pc := N 7984,stack := x0::x1::x2::x3::x4::x5::x6::x7::x8::x9::x10::x11::x12::x13::x14::x15::x16::x17::rest} =
      some (newpart1Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 18) : rest.length + j < 1024 := by omega
  simp [hz,hzn,newpart1Program,newpart1Model,runInstructions,runInstr,List.exchange,succ_ofNat_mod,ofNat_add_mod,Nat.add_assoc,State.activeWordsAfterUInt256,literal_eq_ofNat,capacity]
def newpart2Program : List Instr :=
  [
  .op .MUL,
   .op .ADD,
   .op (.Swap sA0),
   .op (.Dup dA9),
   .op (.Dup dA6),
   .op (.Dup dA12),
   .op .MULMOD,
   .op .ADD]
def newpart2Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 : W) (rest : List W) : State :=
  let v0 : W := x0 * x1
  let v1 : W := v0 + x2
  let v2 : W := UInt256.mulMod x12 x7 x11
  let v3 : W := v2 + x3
  {s with pc := N 8000,memory := s.memory,stack := v3::v1::x4::x5::x6::x7::x8::x9::x10::x11::x12::x13::x14::x15::x16::x17::rest}
theorem newpart2_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions newpart2Program {s with pc := N 7992,stack := x0::x1::x2::x3::x4::x5::x6::x7::x8::x9::x10::x11::x12::x13::x14::x15::x16::x17::rest} =
      some (newpart2Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 19) : rest.length + j < 1024 := by omega
  simp [hz,hzn,newpart2Program,newpart2Model,runInstructions,runInstr,List.exchange,succ_ofNat_mod,ofNat_add_mod,Nat.add_assoc,State.activeWordsAfterUInt256,literal_eq_ofNat,capacity]
def newpart3Program : List Instr :=
  [
  .op (.Dup dA9),
   .op (.Dup dA12),
   .op (.Dup dA10),
   .op .MULMOD,
   .op .ADD,
   .op (.Dup dA9),
   .op (.Dup dA14),
   .op (.Dup dA5)]
def newpart3Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 : W) (rest : List W) : State :=
  let v0 : W := UInt256.mulMod x8 x11 x9
  let v1 : W := v0 + x0
  {s with pc := N 8008,memory := s.memory,stack := x3::x13::x9::v1::x1::x2::x3::x4::x5::x6::x7::x8::x9::x10::x11::x12::x13::x14::x15::rest}
theorem newpart3_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions newpart3Program {s with pc := N 8000,stack := x0::x1::x2::x3::x4::x5::x6::x7::x8::x9::x10::x11::x12::x13::x14::x15::rest} =
      some (newpart3Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 19) : rest.length + j < 1024 := by omega
  simp [hz,hzn,newpart3Program,newpart3Model,runInstructions,runInstr,List.exchange,succ_ofNat_mod,ofNat_add_mod,Nat.add_assoc,State.activeWordsAfterUInt256,literal_eq_ofNat,capacity]
def newpart4Program : List Instr :=
  [
  .op .MULMOD,
   .op .ADD,
   .op (.Swap sA0),
   .op (.Dup dA12),
   .op .AND,
   .op (.Dup dA0),
   .push 1 96,
   .op .MSTORE]
def newpart4Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 : W) (rest : List W) : State :=
  let v0 : W := UInt256.mulMod x0 x1 x2
  let v1 : W := v0 + x3
  let v2 : W := UInt256.land x15 x4
  let v3 : ByteArray := MachineState.writeBytes s.memory (Data.Bytes.natToBytesPadded v2.toNat 32) 96
  {s with pc := N 8017,memory := v3,stack := v2::v1::x5::x6::x7::x8::x9::x10::x11::x12::x13::x14::x15::x16::x17::x18::rest}
theorem newpart4_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions newpart4Program {s with pc := N 8008,stack := x0::x1::x2::x3::x4::x5::x6::x7::x8::x9::x10::x11::x12::x13::x14::x15::x16::x17::x18::rest} =
      some (newpart4Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 19) : rest.length + j < 1024 := by omega
  have ha96 : (96 : W).toNat = 96 := rfl
  have hf96 := Monpro.activeWords_fix s 96 32 (by decide) (by norm_num) hact
  simp [hz,hzn,newpart4Program,newpart4Model,runInstructions,runInstr,List.exchange,succ_ofNat_mod,ofNat_add_mod,Nat.add_assoc,State.activeWordsAfterUInt256,literal_eq_ofNat,capacity,ha96,hf96]
def newpart5Program : List Instr :=
  [
  .op (.Dup dA9),
   .op (.Swap sA1),
   .op .SUB,
   .op (.Dup dA1),
   .op .ADD,
   .push 2 2048,
   .op .MULMOD,
   .push 2 2048,
   .op .MLOAD]
def newpart5Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 : W) (rest : List W) : State :=
  let v0 : W := x1 - x0
  let v1 : W := x9 + v0
  let v2 : W := UInt256.mulMod (N 2048) v1 x9
  let v3 : W := MachineState.readWord s.memory 2048
  {s with pc := N 8030,memory := s.memory,stack := v3::v2::x2::x3::x4::x5::x6::x7::x8::x9::x10::x11::x12::x13::x14::x15::rest}
theorem newpart5_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions newpart5Program {s with pc := N 8017,stack := x0::x1::x2::x3::x4::x5::x6::x7::x8::x9::x10::x11::x12::x13::x14::x15::rest} =
      some (newpart5Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 17) : rest.length + j < 1024 := by omega
  have ha2048 : (2048 : W).toNat = 2048 := rfl
  have hf2048 := Monpro.activeWords_fix s 2048 32 (by decide) (by norm_num) hact
  simp [hz,hzn,newpart5Program,newpart5Model,runInstructions,runInstr,List.exchange,succ_ofNat_mod,ofNat_add_mod,Nat.add_assoc,State.activeWordsAfterUInt256,literal_eq_ofNat,capacity,ha2048,hf2048]
def newpart6Program : List Instr :=
  [
  .push 1 160,
   .op .MLOAD,
   .op (.Dup dA10),
   .op (.Dup dA1),
   .op (.Dup dA3),
   .op .MULMOD,
   .op (.Swap sA6),
   .op .POP]
def newpart6Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 : W) (rest : List W) : State :=
  let v0 : W := MachineState.readWord s.memory 160
  let v1 : W := UInt256.mulMod x0 v0 x9
  {s with pc := N 8039,memory := s.memory,stack := v0::x0::x1::x2::x3::x4::v1::x6::x7::x8::x9::x10::x11::x12::x13::x14::x15::rest}
theorem newpart6_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions newpart6Program {s with pc := N 8030,stack := x0::x1::x2::x3::x4::x5::x6::x7::x8::x9::x10::x11::x12::x13::x14::x15::rest} =
      some (newpart6Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 20) : rest.length + j < 1024 := by omega
  have ha160 : (160 : W).toNat = 160 := rfl
  have hf160 := Monpro.activeWords_fix s 160 32 (by decide) (by norm_num) hact
  simp [hz,hzn,newpart6Program,newpart6Model,runInstructions,runInstr,List.exchange,succ_ofNat_mod,ofNat_add_mod,Nat.add_assoc,State.activeWordsAfterUInt256,literal_eq_ofNat,capacity,ha160,hf160]
def newpart7Program : List Instr :=
  [
  .op .MUL,
   .push 2 2016,
   .op .MLOAD,
   .op (.Swap sA5),
   .op (.Dup dA2),
   .op .ADD,
   .op (.Dup dA10),
   .op (.Dup dA4)]
def newpart7Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 : W) (rest : List W) : State :=
  let v0 : W := x0 * x1
  let v1 : W := MachineState.readWord s.memory 2016
  let v2 : W := x2 + x6
  {s with pc := N 8049,memory := s.memory,stack := x3::x10::v2::v0::x2::x3::x4::x5::v1::x7::x8::x9::x10::x11::x12::x13::x14::x15::x16::rest}
theorem newpart7_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions newpart7Program {s with pc := N 8039,stack := x0::x1::x2::x3::x4::x5::x6::x7::x8::x9::x10::x11::x12::x13::x14::x15::x16::rest} =
      some (newpart7Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 19) : rest.length + j < 1024 := by omega
  have ha2016 : (2016 : W).toNat = 2016 := rfl
  have hf2016 := Monpro.activeWords_fix s 2016 32 (by decide) (by norm_num) hact
  simp [hz,hzn,newpart7Program,newpart7Model,runInstructions,runInstr,List.exchange,succ_ofNat_mod,ofNat_add_mod,Nat.add_assoc,State.activeWordsAfterUInt256,literal_eq_ofNat,capacity,ha2016,hf2016]
def newpart8Program : List Instr :=
  [
  .op (.Dup dA8),
   .op .MULMOD,
   .op .ADD,
   .op (.Swap sA1),
   .op .ADD,
   .push 2 800,
   .op .MLOAD,
   .op (.Swap sA5)]
def newpart8Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 : W) (rest : List W) : State :=
  let v0 : W := UInt256.mulMod x8 x0 x1
  let v1 : W := v0 + x2
  let v2 : W := x4 + x3
  let v3 : W := MachineState.readWord s.memory 800
  {s with pc := N 8059,memory := s.memory,stack := x8::v2::v1::x5::x6::x7::v3::x9::x10::x11::x12::x13::x14::x15::x16::x17::x18::rest}
theorem newpart8_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions newpart8Program {s with pc := N 8049,stack := x0::x1::x2::x3::x4::x5::x6::x7::x8::x9::x10::x11::x12::x13::x14::x15::x16::x17::x18::rest} =
      some (newpart8Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 20) : rest.length + j < 1024 := by omega
  have ha800 : (800 : W).toNat = 800 := rfl
  have hf800 := Monpro.activeWords_fix s 800 32 (by decide) (by norm_num) hact
  simp [hz,hzn,newpart8Program,newpart8Model,runInstructions,runInstr,List.exchange,succ_ofNat_mod,ofNat_add_mod,Nat.add_assoc,State.activeWordsAfterUInt256,literal_eq_ofNat,capacity,ha800,hf800]
def newpart9Program : List Instr :=
  [
  .op (.Dup dA3),
   .op .MUL,
   .op .ADD,
   .op (.Dup dA11),
   .op (.Dup dA11),
   .op .MUL,
   .op .ADD,
   .op (.Dup dA13)]
def newpart9Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 : W) (rest : List W) : State :=
  let v0 : W := x3 * x0
  let v1 : W := v0 + x1
  let v2 : W := x11 * x12
  let v3 : W := v2 + v1
  {s with pc := N 8067,memory := s.memory,stack := x14::v3::x2::x3::x4::x5::x6::x7::x8::x9::x10::x11::x12::x13::x14::x15::x16::rest}
theorem newpart9_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions newpart9Program {s with pc := N 8059,stack := x0::x1::x2::x3::x4::x5::x6::x7::x8::x9::x10::x11::x12::x13::x14::x15::x16::rest} =
      some (newpart9Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 18) : rest.length + j < 1024 := by omega
  simp [hz,hzn,newpart9Program,newpart9Model,runInstructions,runInstr,List.exchange,succ_ofNat_mod,ofNat_add_mod,Nat.add_assoc,State.activeWordsAfterUInt256,literal_eq_ofNat,capacity]
def newpart10Program : List Instr :=
  [
  .op (.Dup dA9),
   .op .MUL,
   .op .ADD,
   .op (.Swap sA0),
   .op (.Dup dA9),
   .op (.Dup dA12),
   .op (.Dup dA12),
   .op .MULMOD]
def newpart10Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 : W) (rest : List W) : State :=
  let v0 : W := x9 * x0
  let v1 : W := v0 + x1
  let v2 : W := UInt256.mulMod x11 x12 x10
  {s with pc := N 8075,memory := s.memory,stack := v2::x2::v1::x3::x4::x5::x6::x7::x8::x9::x10::x11::x12::x13::x14::x15::x16::rest}
theorem newpart10_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions newpart10Program {s with pc := N 8067,stack := x0::x1::x2::x3::x4::x5::x6::x7::x8::x9::x10::x11::x12::x13::x14::x15::x16::rest} =
      some (newpart10Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 19) : rest.length + j < 1024 := by omega
  simp [hz,hzn,newpart10Program,newpart10Model,runInstructions,runInstr,List.exchange,succ_ofNat_mod,ofNat_add_mod,Nat.add_assoc,State.activeWordsAfterUInt256,literal_eq_ofNat,capacity]
def newpart11Program : List Instr :=
  [
  .op .ADD,
   .op (.Dup dA9),
   .op (.Dup dA14),
   .op (.Dup dA10),
   .op .MULMOD,
   .op .ADD,
   .op (.Swap sA0),
   .op (.Dup dA12)]
def newpart11Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 : W) (rest : List W) : State :=
  let v0 : W := x0 + x1
  let v1 : W := UInt256.mulMod x9 x14 x10
  let v2 : W := v1 + v0
  {s with pc := N 8083,memory := s.memory,stack := x13::x2::v2::x3::x4::x5::x6::x7::x8::x9::x10::x11::x12::x13::x14::x15::x16::rest}
theorem newpart11_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions newpart11Program {s with pc := N 8075,stack := x0::x1::x2::x3::x4::x5::x6::x7::x8::x9::x10::x11::x12::x13::x14::x15::x16::rest} =
      some (newpart11Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 19) : rest.length + j < 1024 := by omega
  simp [hz,hzn,newpart11Program,newpart11Model,runInstructions,runInstr,List.exchange,succ_ofNat_mod,ofNat_add_mod,Nat.add_assoc,State.activeWordsAfterUInt256,literal_eq_ofNat,capacity]
def newpart12Program : List Instr :=
  [
  .op .AND,
   .op (.Dup dA0),
   .push 1 128,
   .op .MSTORE,
   .op (.Dup dA9),
   .op (.Swap sA1),
   .op .SUB,
   .op (.Dup dA1)]
def newpart12Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 : W) (rest : List W) : State :=
  let v0 : W := UInt256.land x0 x1
  let v1 : ByteArray := MachineState.writeBytes s.memory (Data.Bytes.natToBytesPadded v0.toNat 32) 128
  let v2 : W := x2 - v0
  {s with pc := N 8092,memory := v1,stack := x10::v2::x10::x3::x4::x5::x6::x7::x8::x9::x10::x11::x12::x13::x14::x15::x16::rest}
theorem newpart12_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions newpart12Program {s with pc := N 8083,stack := x0::x1::x2::x3::x4::x5::x6::x7::x8::x9::x10::x11::x12::x13::x14::x15::x16::rest} =
      some (newpart12Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 18) : rest.length + j < 1024 := by omega
  have ha128 : (128 : W).toNat = 128 := rfl
  have hf128 := Monpro.activeWords_fix s 128 32 (by decide) (by norm_num) hact
  simp [hz,hzn,newpart12Program,newpart12Model,runInstructions,runInstr,List.exchange,succ_ofNat_mod,ofNat_add_mod,Nat.add_assoc,State.activeWordsAfterUInt256,literal_eq_ofNat,capacity,ha128,hf128]
def newpart13Program : List Instr :=
  [
  .op .ADD,
   .push 2 2048,
   .op .MULMOD,
   .push 2 2048,
   .op .MLOAD,
   .op (.Dup dA9),
   .op (.Dup dA1),
   .op (.Dup dA4)]
def newpart13Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 : W) (rest : List W) : State :=
  let v0 : W := x0 + x1
  let v1 : W := UInt256.mulMod (N 2048) v0 x2
  let v2 : W := MachineState.readWord s.memory 2048
  {s with pc := N 8104,memory := s.memory,stack := x3::v2::x10::v2::v1::x3::x4::x5::x6::x7::x8::x9::x10::x11::x12::x13::x14::x15::x16::rest}
theorem newpart13_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions newpart13Program {s with pc := N 8092,stack := x0::x1::x2::x3::x4::x5::x6::x7::x8::x9::x10::x11::x12::x13::x14::x15::x16::rest} =
      some (newpart13Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 19) : rest.length + j < 1024 := by omega
  have ha2048 : (2048 : W).toNat = 2048 := rfl
  have hf2048 := Monpro.activeWords_fix s 2048 32 (by decide) (by norm_num) hact
  simp [hz,hzn,newpart13Program,newpart13Model,runInstructions,runInstr,List.exchange,succ_ofNat_mod,ofNat_add_mod,Nat.add_assoc,State.activeWordsAfterUInt256,literal_eq_ofNat,capacity,ha2048,hf2048]
def newpart14Program : List Instr :=
  [
  .op .MULMOD,
   .op (.Dup dA10),
   .op (.Dup dA15),
   .op (.Dup dA13),
   .op .MULMOD,
   .op (.Swap sA1),
   .op (.Dup dA4),
   .op .MUL]
def newpart14Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 : W) (rest : List W) : State :=
  let v0 : W := UInt256.mulMod x0 x1 x2
  let v1 : W := UInt256.mulMod x13 x16 x12
  let v2 : W := x5 * x3
  {s with pc := N 8112,memory := s.memory,stack := v2::v0::v1::x4::x5::x6::x7::x8::x9::x10::x11::x12::x13::x14::x15::x16::x17::x18::rest}
theorem newpart14_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions newpart14Program {s with pc := N 8104,stack := x0::x1::x2::x3::x4::x5::x6::x7::x8::x9::x10::x11::x12::x13::x14::x15::x16::x17::x18::rest} =
      some (newpart14Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 20) : rest.length + j < 1024 := by omega
  simp [hz,hzn,newpart14Program,newpart14Model,runInstructions,runInstr,List.exchange,succ_ofNat_mod,ofNat_add_mod,Nat.add_assoc,State.activeWordsAfterUInt256,literal_eq_ofNat,capacity]
def newpart15Program : List Instr :=
  [
  .op (.Dup dA3),
   .op .ADD,
   .op (.Dup dA15),
   .op (.Dup dA13),
   .op .MUL,
   .op .ADD,
   .op (.Dup dA14),
   .op .AND]
def newpart15Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 : W) (rest : List W) : State :=
  let v0 : W := x3 + x0
  let v1 : W := x12 * x15
  let v2 : W := v1 + v0
  let v3 : W := UInt256.land x14 v2
  {s with pc := N 8120,memory := s.memory,stack := v3::x1::x2::x3::x4::x5::x6::x7::x8::x9::x10::x11::x12::x13::x14::x15::x16::x17::rest}
theorem newpart15_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions newpart15Program {s with pc := N 8112,stack := x0::x1::x2::x3::x4::x5::x6::x7::x8::x9::x10::x11::x12::x13::x14::x15::x16::x17::rest} =
      some (newpart15Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 20) : rest.length + j < 1024 := by omega
  simp [hz,hzn,newpart15Program,newpart15Model,runInstructions,runInstr,List.exchange,succ_ofNat_mod,ofNat_add_mod,Nat.add_assoc,State.activeWordsAfterUInt256,literal_eq_ofNat,capacity]
def newpart16Program : List Instr :=
  [
  .op (.Swap sA2),
   .op .ADD,
   .op .ADD,
   .op (.Dup dA1),
   .push 1 160,
   .op .MSTORE,
   .op .SUB,
   .op (.Dup dA8)]
def newpart16Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 : W) (rest : List W) : State :=
  let v0 : W := x3 + x1
  let v1 : W := v0 + x2
  let v2 : ByteArray := MachineState.writeBytes s.memory (Data.Bytes.natToBytesPadded x0.toNat 32) 160
  let v3 : W := v1 - x0
  {s with pc := N 8129,memory := v2,stack := x11::v3::x4::x5::x6::x7::x8::x9::x10::x11::x12::x13::x14::x15::x16::x17::rest}
theorem newpart16_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions newpart16Program {s with pc := N 8120,stack := x0::x1::x2::x3::x4::x5::x6::x7::x8::x9::x10::x11::x12::x13::x14::x15::x16::x17::rest} =
      some (newpart16Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 18) : rest.length + j < 1024 := by omega
  have ha160 : (160 : W).toNat = 160 := rfl
  have hf160 := Monpro.activeWords_fix s 160 32 (by decide) (by norm_num) hact
  simp [hz,hzn,newpart16Program,newpart16Model,runInstructions,runInstr,List.exchange,succ_ofNat_mod,ofNat_add_mod,Nat.add_assoc,State.activeWordsAfterUInt256,literal_eq_ofNat,capacity,ha160,hf160]
def newpart17Program : List Instr :=
  [
  .op .ADD,
   .push 2 2048,
   .op (.Dup dA9),
   .op (.Swap sA2),
   .op .POP,
   .op .MULMOD,
   .op (.Swap sA12)]
def newpart17Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 : W) (rest : List W) : State :=
  let v0 : W := x0 + x1
  let v1 : W := UInt256.mulMod (N 2048) v0 x9
  {s with pc := N 8138,memory := s.memory,stack := x15::x3::x4::x5::x6::x7::x8::x9::x10::x11::x12::x13::x14::v1::rest}
theorem newpart17_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions newpart17Program {s with pc := N 8129,stack := x0::x1::x2::x3::x4::x5::x6::x7::x8::x9::x10::x11::x12::x13::x14::x15::rest} =
      some (newpart17Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 17) : rest.length + j < 1024 := by omega
  simp [hz,hzn,newpart17Program,newpart17Model,runInstructions,runInstr,List.exchange,succ_ofNat_mod,ofNat_add_mod,Nat.add_assoc,State.activeWordsAfterUInt256,literal_eq_ofNat,capacity]
def newProgram : List Instr :=
  [
  .op .MUL,
   .op .ADD,
   .op (.Swap sA3),
   .op .MULMOD,
   .op .ADD,
   .op (.Swap sA0),
   .op (.Dup dA5),
   .op (.Dup dA11),
   .op .MUL,
   .op .ADD,
   .op (.Dup dA11),
   .op (.Dup dA9),
   .op .MUL,
   .op .ADD,
   .op (.Dup dA13),
   .op (.Dup dA4),
   .op .MUL,
   .op .ADD,
   .op (.Swap sA0),
   .op (.Dup dA9),
   .op (.Dup dA6),
   .op (.Dup dA12),
   .op .MULMOD,
   .op .ADD,
   .op (.Dup dA9),
   .op (.Dup dA12),
   .op (.Dup dA10),
   .op .MULMOD,
   .op .ADD,
   .op (.Dup dA9),
   .op (.Dup dA14),
   .op (.Dup dA5),
   .op .MULMOD,
   .op .ADD,
   .op (.Swap sA0),
   .op (.Dup dA12),
   .op .AND,
   .op (.Dup dA0),
   .push 1 96,
   .op .MSTORE,
   .op (.Dup dA9),
   .op (.Swap sA1),
   .op .SUB,
   .op (.Dup dA1),
   .op .ADD,
   .push 2 2048,
   .op .MULMOD,
   .push 2 2048,
   .op .MLOAD,
   .push 1 160,
   .op .MLOAD,
   .op (.Dup dA10),
   .op (.Dup dA1),
   .op (.Dup dA3),
   .op .MULMOD,
   .op (.Swap sA6),
   .op .POP,
   .op .MUL,
   .push 2 2016,
   .op .MLOAD,
   .op (.Swap sA5),
   .op (.Dup dA2),
   .op .ADD,
   .op (.Dup dA10),
   .op (.Dup dA4),
   .op (.Dup dA8),
   .op .MULMOD,
   .op .ADD,
   .op (.Swap sA1),
   .op .ADD,
   .push 2 800,
   .op .MLOAD,
   .op (.Swap sA5),
   .op (.Dup dA3),
   .op .MUL,
   .op .ADD,
   .op (.Dup dA11),
   .op (.Dup dA11),
   .op .MUL,
   .op .ADD,
   .op (.Dup dA13),
   .op (.Dup dA9),
   .op .MUL,
   .op .ADD,
   .op (.Swap sA0),
   .op (.Dup dA9),
   .op (.Dup dA12),
   .op (.Dup dA12),
   .op .MULMOD,
   .op .ADD,
   .op (.Dup dA9),
   .op (.Dup dA14),
   .op (.Dup dA10),
   .op .MULMOD,
   .op .ADD,
   .op (.Swap sA0),
   .op (.Dup dA12),
   .op .AND,
   .op (.Dup dA0),
   .push 1 128,
   .op .MSTORE,
   .op (.Dup dA9),
   .op (.Swap sA1),
   .op .SUB,
   .op (.Dup dA1),
   .op .ADD,
   .push 2 2048,
   .op .MULMOD,
   .push 2 2048,
   .op .MLOAD,
   .op (.Dup dA9),
   .op (.Dup dA1),
   .op (.Dup dA4),
   .op .MULMOD,
   .op (.Dup dA10),
   .op (.Dup dA15),
   .op (.Dup dA13),
   .op .MULMOD,
   .op (.Swap sA1),
   .op (.Dup dA4),
   .op .MUL,
   .op (.Dup dA3),
   .op .ADD,
   .op (.Dup dA15),
   .op (.Dup dA13),
   .op .MUL,
   .op .ADD,
   .op (.Dup dA14),
   .op .AND,
   .op (.Swap sA2),
   .op .ADD,
   .op .ADD,
   .op (.Dup dA1),
   .push 1 160,
   .op .MSTORE,
   .op .SUB,
   .op (.Dup dA8),
   .op .ADD,
   .push 2 2048,
   .op (.Dup dA9),
   .op (.Swap sA2),
   .op .POP,
   .op .MULMOD,
   .op (.Swap sA12)]
def newModel (s : State) (carry w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 : W) (rest : List W) : State :=
  let v0 : W := carry * w0
  let v1 : W := v0 + w1
  let v2 : W := UInt256.mulMod w5 w2 w3
  let v3 : W := v2 + w4
  let v4 : W := w14 * w9
  let v5 : W := v4 + v1
  let v6 : W := w12 * w15
  let v7 : W := v6 + v5
  let v8 : W := w7 * w17
  let v9 : W := v8 + v7
  let v10 : W := UInt256.mulMod w14 w9 w13
  let v11 : W := v10 + v3
  let v12 : W := UInt256.mulMod w12 w15 w13
  let v13 : W := v12 + v11
  let v14 : W := UInt256.mulMod w7 w17 w13
  let v15 : W := v14 + v13
  let v16 : W := UInt256.land w16 v9
  let v17 : ByteArray := MachineState.writeBytes s.memory (Data.Bytes.natToBytesPadded v16.toNat 32) 96
  let v18 : W := v15 - v16
  let v19 : W := w13 + v18
  let v20 : W := UInt256.mulMod (N 2048) v19 w13
  let v21 : W := MachineState.readWord v17 2048
  let v22 : W := MachineState.readWord v17 160
  let v23 : W := UInt256.mulMod v21 v22 w13
  let v24 : W := v22 * v21
  let v25 : W := MachineState.readWord v17 2016
  let v26 : W := v20 + v23
  let v27 : W := UInt256.mulMod v25 w6 w13
  let v28 : W := v27 + v26
  let v29 : W := v20 + v24
  let v30 : W := MachineState.readWord v17 800
  let v31 : W := w6 * v25
  let v32 : W := v31 + v29
  let v33 : W := w14 * w15
  let v34 : W := v33 + v32
  let v35 : W := w12 * w17
  let v36 : W := v35 + v34
  let v37 : W := UInt256.mulMod w14 w15 w13
  let v38 : W := v37 + v28
  let v39 : W := UInt256.mulMod w12 w17 w13
  let v40 : W := v39 + v38
  let v41 : W := UInt256.land w16 v36
  let v42 : ByteArray := MachineState.writeBytes v17 (Data.Bytes.natToBytesPadded v41.toNat 32) 128
  let v43 : W := v40 - v41
  let v44 : W := w13 + v43
  let v45 : W := UInt256.mulMod (N 2048) v44 w13
  let v46 : W := MachineState.readWord v42 2048
  let v47 : W := UInt256.mulMod w6 v46 w13
  let v48 : W := UInt256.mulMod w14 w17 w13
  let v49 : W := w6 * v46
  let v50 : W := v45 + v49
  let v51 : W := w14 * w17
  let v52 : W := v51 + v50
  let v53 : W := UInt256.land w16 v52
  let v54 : W := v45 + v47
  let v55 : W := v54 + v48
  let v56 : ByteArray := MachineState.writeBytes v42 (Data.Bytes.natToBytesPadded v53.toNat 32) 160
  let v57 : W := v55 - v53
  let v58 : W := w13 + v57
  let v59 : W := UInt256.mulMod (N 2048) v58 w13
  {s with pc := N 8138,memory := v56,stack := w19::w7::w8::v30::w10::w11::w12::w13::w14::w15::w16::w17::w18::v59::rest}
theorem new_run (s : State) (carry w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions newProgram {s with pc := N 7976,stack := carry::w0::w1::w2::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::w16::w17::w18::w19::rest} =
      some (newModel s carry w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 rest) := by
  let v0 : W := carry * w0
  let v1 : W := v0 + w1
  let v2 : W := UInt256.mulMod w5 w2 w3
  let v3 : W := v2 + w4
  let v4 : W := w14 * w9
  let v5 : W := v4 + v1
  let v6 : W := w12 * w15
  let v7 : W := v6 + v5
  let v8 : W := w7 * w17
  let v9 : W := v8 + v7
  let v10 : W := UInt256.mulMod w14 w9 w13
  let v11 : W := v10 + v3
  let v12 : W := UInt256.mulMod w12 w15 w13
  let v13 : W := v12 + v11
  let v14 : W := UInt256.mulMod w7 w17 w13
  let v15 : W := v14 + v13
  let v16 : W := UInt256.land w16 v9
  let v17 : ByteArray := MachineState.writeBytes s.memory (Data.Bytes.natToBytesPadded v16.toNat 32) 96
  let v18 : W := v15 - v16
  let v19 : W := w13 + v18
  let v20 : W := UInt256.mulMod (N 2048) v19 w13
  let v21 : W := MachineState.readWord v17 2048
  let v22 : W := MachineState.readWord v17 160
  let v23 : W := UInt256.mulMod v21 v22 w13
  let v24 : W := v22 * v21
  let v25 : W := MachineState.readWord v17 2016
  let v26 : W := v20 + v23
  let v27 : W := UInt256.mulMod v25 w6 w13
  let v28 : W := v27 + v26
  let v29 : W := v20 + v24
  let v30 : W := MachineState.readWord v17 800
  let v31 : W := w6 * v25
  let v32 : W := v31 + v29
  let v33 : W := w14 * w15
  let v34 : W := v33 + v32
  let v35 : W := w12 * w17
  let v36 : W := v35 + v34
  let v37 : W := UInt256.mulMod w14 w15 w13
  let v38 : W := v37 + v28
  let v39 : W := UInt256.mulMod w12 w17 w13
  let v40 : W := v39 + v38
  let v41 : W := UInt256.land w16 v36
  let v42 : ByteArray := MachineState.writeBytes v17 (Data.Bytes.natToBytesPadded v41.toNat 32) 128
  let v43 : W := v40 - v41
  let v44 : W := w13 + v43
  let v45 : W := UInt256.mulMod (N 2048) v44 w13
  let v46 : W := MachineState.readWord v42 2048
  let v47 : W := UInt256.mulMod w6 v46 w13
  let v48 : W := UInt256.mulMod w14 w17 w13
  let v49 : W := w6 * v46
  let v50 : W := v45 + v49
  let v51 : W := w14 * w17
  let v52 : W := v51 + v50
  let v53 : W := UInt256.land w16 v52
  let v54 : W := v45 + v47
  let v55 : W := v54 + v48
  let v56 : ByteArray := MachineState.writeBytes v42 (Data.Bytes.natToBytesPadded v53.toNat 32) 160
  let v57 : W := v55 - v53
  let v58 : W := w13 + v57
  let v59 : W := UInt256.mulMod (N 2048) v58 w13
  have h0 : runInstructions newpart0Program {s with pc := N 7976,memory := s.memory,stack := carry::w0::w1::w2::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::w16::w17::w18::w19::rest} = some {s with pc := N 7984,memory := s.memory,stack := w14::w9::v1::v3::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::w16::w17::w18::w19::rest} := by
    simpa only [newpart0Model,v0,v1,v2,v3] using newpart0_run (s) (carry) w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 rest hcap hact
  have h1 : runInstructions newpart1Program {s with pc := N 7984,memory := s.memory,stack := w14::w9::v1::v3::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::w16::w17::w18::w19::rest} = some {s with pc := N 7992,memory := s.memory,stack := w7::w17::v7::v3::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::w16::w17::w18::w19::rest} := by
    simpa only [newpart1Model,v4,v5,v6,v7] using newpart1_run (s) w14 w9 v1 v3 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 rest hcap hact
  have h2 : runInstructions newpart2Program {s with pc := N 7992,memory := s.memory,stack := w7::w17::v7::v3::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::w16::w17::w18::w19::rest} = some {s with pc := N 8000,memory := s.memory,stack := v11::v9::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::w16::w17::w18::w19::rest} := by
    simpa only [newpart2Model,v8,v9,v10,v11] using newpart2_run (s) w7 w17 v7 v3 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 rest hcap hact
  have h3 : runInstructions newpart3Program {s with pc := N 8000,memory := s.memory,stack := v11::v9::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::w16::w17::w18::w19::rest} = some {s with pc := N 8008,memory := s.memory,stack := w7::w17::w13::v13::v9::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::w16::w17::w18::w19::rest} := by
    simpa only [newpart3Model,v12,v13] using newpart3_run (s) v11 v9 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 rest hcap hact
  have h4 : runInstructions newpart4Program {s with pc := N 8008,memory := s.memory,stack := w7::w17::w13::v13::v9::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::w16::w17::w18::w19::rest} = some {s with pc := N 8017,memory := v17,stack := v16::v15::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::w16::w17::w18::w19::rest} := by
    simpa only [newpart4Model,v14,v15,v16,v17] using newpart4_run (s) w7 w17 w13 v13 v9 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 rest hcap hact
  have h5 : runInstructions newpart5Program {s with pc := N 8017,memory := v17,stack := v16::v15::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::w16::w17::w18::w19::rest} = some {s with pc := N 8030,memory := v17,stack := v21::v20::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::w16::w17::w18::w19::rest} := by
    simpa only [newpart5Model,v18,v19,v20,v21] using newpart5_run ({s with memory := v17}) v16 v15 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 rest hcap hact
  have h6 : runInstructions newpart6Program {s with pc := N 8030,memory := v17,stack := v21::v20::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::w16::w17::w18::w19::rest} = some {s with pc := N 8039,memory := v17,stack := v22::v21::v20::w6::w7::w8::v23::w10::w11::w12::w13::w14::w15::w16::w17::w18::w19::rest} := by
    simpa only [newpart6Model,v22,v23] using newpart6_run ({s with memory := v17}) v21 v20 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 rest hcap hact
  have h7 : runInstructions newpart7Program {s with pc := N 8039,memory := v17,stack := v22::v21::v20::w6::w7::w8::v23::w10::w11::w12::w13::w14::w15::w16::w17::w18::w19::rest} = some {s with pc := N 8049,memory := v17,stack := w6::w13::v26::v24::v20::w6::w7::w8::v25::w10::w11::w12::w13::w14::w15::w16::w17::w18::w19::rest} := by
    simpa only [newpart7Model,v24,v25,v26] using newpart7_run ({s with memory := v17}) v22 v21 v20 w6 w7 w8 v23 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 rest hcap hact
  have h8 : runInstructions newpart8Program {s with pc := N 8049,memory := v17,stack := w6::w13::v26::v24::v20::w6::w7::w8::v25::w10::w11::w12::w13::w14::w15::w16::w17::w18::w19::rest} = some {s with pc := N 8059,memory := v17,stack := v25::v29::v28::w6::w7::w8::v30::w10::w11::w12::w13::w14::w15::w16::w17::w18::w19::rest} := by
    simpa only [newpart8Model,v27,v28,v29,v30] using newpart8_run ({s with memory := v17}) w6 w13 v26 v24 v20 w6 w7 w8 v25 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 rest hcap hact
  have h9 : runInstructions newpart9Program {s with pc := N 8059,memory := v17,stack := v25::v29::v28::w6::w7::w8::v30::w10::w11::w12::w13::w14::w15::w16::w17::w18::w19::rest} = some {s with pc := N 8067,memory := v17,stack := w17::v34::v28::w6::w7::w8::v30::w10::w11::w12::w13::w14::w15::w16::w17::w18::w19::rest} := by
    simpa only [newpart9Model,v31,v32,v33,v34] using newpart9_run ({s with memory := v17}) v25 v29 v28 w6 w7 w8 v30 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 rest hcap hact
  have h10 : runInstructions newpart10Program {s with pc := N 8067,memory := v17,stack := w17::v34::v28::w6::w7::w8::v30::w10::w11::w12::w13::w14::w15::w16::w17::w18::w19::rest} = some {s with pc := N 8075,memory := v17,stack := v37::v28::v36::w6::w7::w8::v30::w10::w11::w12::w13::w14::w15::w16::w17::w18::w19::rest} := by
    simpa only [newpart10Model,v35,v36,v37] using newpart10_run ({s with memory := v17}) w17 v34 v28 w6 w7 w8 v30 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 rest hcap hact
  have h11 : runInstructions newpart11Program {s with pc := N 8075,memory := v17,stack := v37::v28::v36::w6::w7::w8::v30::w10::w11::w12::w13::w14::w15::w16::w17::w18::w19::rest} = some {s with pc := N 8083,memory := v17,stack := w16::v36::v40::w6::w7::w8::v30::w10::w11::w12::w13::w14::w15::w16::w17::w18::w19::rest} := by
    simpa only [newpart11Model,v38,v39,v40] using newpart11_run ({s with memory := v17}) v37 v28 v36 w6 w7 w8 v30 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 rest hcap hact
  have h12 : runInstructions newpart12Program {s with pc := N 8083,memory := v17,stack := w16::v36::v40::w6::w7::w8::v30::w10::w11::w12::w13::w14::w15::w16::w17::w18::w19::rest} = some {s with pc := N 8092,memory := v42,stack := w13::v43::w13::w6::w7::w8::v30::w10::w11::w12::w13::w14::w15::w16::w17::w18::w19::rest} := by
    simpa only [newpart12Model,v41,v42,v43] using newpart12_run ({s with memory := v17}) w16 v36 v40 w6 w7 w8 v30 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 rest hcap hact
  have h13 : runInstructions newpart13Program {s with pc := N 8092,memory := v42,stack := w13::v43::w13::w6::w7::w8::v30::w10::w11::w12::w13::w14::w15::w16::w17::w18::w19::rest} = some {s with pc := N 8104,memory := v42,stack := w6::v46::w13::v46::v45::w6::w7::w8::v30::w10::w11::w12::w13::w14::w15::w16::w17::w18::w19::rest} := by
    simpa only [newpart13Model,v44,v45,v46] using newpart13_run ({s with memory := v42}) w13 v43 w13 w6 w7 w8 v30 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 rest hcap hact
  have h14 : runInstructions newpart14Program {s with pc := N 8104,memory := v42,stack := w6::v46::w13::v46::v45::w6::w7::w8::v30::w10::w11::w12::w13::w14::w15::w16::w17::w18::w19::rest} = some {s with pc := N 8112,memory := v42,stack := v49::v47::v48::v45::w6::w7::w8::v30::w10::w11::w12::w13::w14::w15::w16::w17::w18::w19::rest} := by
    simpa only [newpart14Model,v47,v48,v49] using newpart14_run ({s with memory := v42}) w6 v46 w13 v46 v45 w6 w7 w8 v30 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 rest hcap hact
  have h15 : runInstructions newpart15Program {s with pc := N 8112,memory := v42,stack := v49::v47::v48::v45::w6::w7::w8::v30::w10::w11::w12::w13::w14::w15::w16::w17::w18::w19::rest} = some {s with pc := N 8120,memory := v42,stack := v53::v47::v48::v45::w6::w7::w8::v30::w10::w11::w12::w13::w14::w15::w16::w17::w18::w19::rest} := by
    simpa only [newpart15Model,v50,v51,v52,v53] using newpart15_run ({s with memory := v42}) v49 v47 v48 v45 w6 w7 w8 v30 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 rest hcap hact
  have h16 : runInstructions newpart16Program {s with pc := N 8120,memory := v42,stack := v53::v47::v48::v45::w6::w7::w8::v30::w10::w11::w12::w13::w14::w15::w16::w17::w18::w19::rest} = some {s with pc := N 8129,memory := v56,stack := w13::v57::w6::w7::w8::v30::w10::w11::w12::w13::w14::w15::w16::w17::w18::w19::rest} := by
    simpa only [newpart16Model,v54,v55,v56,v57] using newpart16_run ({s with memory := v42}) v53 v47 v48 v45 w6 w7 w8 v30 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 rest hcap hact
  have h17 : runInstructions newpart17Program {s with pc := N 8129,memory := v56,stack := w13::v57::w6::w7::w8::v30::w10::w11::w12::w13::w14::w15::w16::w17::w18::w19::rest} = some {s with pc := N 8138,memory := v56,stack := w19::w7::w8::v30::w10::w11::w12::w13::w14::w15::w16::w17::w18::v59::rest} := by
    simpa only [newpart17Model,v58,v59] using newpart17_run ({s with memory := v56}) w13 v57 w6 w7 w8 v30 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 rest hcap hact
  exact (runInstructions_append_some _ _ _ _ _ h0 (runInstructions_append_some _ _ _ _ _ h1 (runInstructions_append_some _ _ _ _ _ h2 (runInstructions_append_some _ _ _ _ _ h3 (runInstructions_append_some _ _ _ _ _ h4 (runInstructions_append_some _ _ _ _ _ h5 (runInstructions_append_some _ _ _ _ _ h6 (runInstructions_append_some _ _ _ _ _ h7 (runInstructions_append_some _ _ _ _ _ h8 (runInstructions_append_some _ _ _ _ _ h9 (runInstructions_append_some _ _ _ _ _ h10 (runInstructions_append_some _ _ _ _ _ h11 (runInstructions_append_some _ _ _ _ _ h12 (runInstructions_append_some _ _ _ _ _ h13 (runInstructions_append_some _ _ _ _ _ h14 (runInstructions_append_some _ _ _ _ _ h15 (runInstructions_append_some _ _ _ _ _ h16 h17)))))))))))))))))
#print axioms new_run
private theorem aux_shared0 (z1 : W) (z0 : ByteArray) :
    (MachineState.readWord (MachineState.writeBytes z0 (Data.Bytes.natToBytesPadded z1.toNat 32) 128) 2048) = (MachineState.readWord z0 2048) := by
  simp (disch := decide) only [addC,addA,addL,mulC,mmC,amC,andC,orC,xorC,eqC,read_disjoint,Challenge.EvmProof.Memory.readWord_writeWord]
private theorem aux_shared1 (w13 : W) (z0 : W) :
    (UInt256.mulMod (N 2048) z0 w13) = (UInt256.mulMod z0 (N 2048) w13) := by
  simp (disch := decide) only [addC,addA,addL,mulC,mmC,amC,andC,orC,xorC,eqC,read_disjoint,Challenge.EvmProof.Memory.readWord_writeWord]
private theorem aux_shared2 (z0 z1 : W) :
    (z0 * z1) = (z1 * z0) := by
  simp (disch := decide) only [addC,addA,addL,mulC,mmC,amC,andC,orC,xorC,eqC,read_disjoint,Challenge.EvmProof.Memory.readWord_writeWord]
private theorem aux_shared3 (z0 z1 : W) :
    (z0 + z1) = (z1 + z0) := by
  simp (disch := decide) only [addC,addA,addL,mulC,mmC,amC,andC,orC,xorC,eqC,read_disjoint,Challenge.EvmProof.Memory.readWord_writeWord]
private theorem aux_shared4 (w6 : W) (z0 : W) :
    (w6 * z0) = (z0 * w6) := by
  simp (disch := decide) only [addC,addA,addL,mulC,mmC,amC,andC,orC,xorC,eqC,read_disjoint,Challenge.EvmProof.Memory.readWord_writeWord]
private theorem aux_shared5 (w6 w13 : W) (z0 : W) :
    (UInt256.mulMod w6 z0 w13) = (UInt256.mulMod z0 w6 w13) := by
  simp (disch := decide) only [addC,addA,addL,mulC,mmC,amC,andC,orC,xorC,eqC,read_disjoint,Challenge.EvmProof.Memory.readWord_writeWord]
theorem same_state (s : State) (carry w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 : W) (rest : List W) :
    oldModel s carry w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 rest = newModel s carry w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 rest := by
  let o0 : W := carry * w0
  let o1 : W := o0 + w1
  let o2 : W := UInt256.mulMod w5 w2 w3
  let o3 : W := o2 + w4
  let o4 : W := w14 * w9
  let o5 : W := o4 + o1
  let o6 : W := w12 * w15
  let o7 : W := o6 + o5
  let o8 : W := w7 * w17
  let o9 : W := o8 + o7
  let o10 : W := UInt256.mulMod w14 w9 w13
  let o11 : W := o10 + o3
  let o12 : W := UInt256.mulMod w12 w15 w13
  let o13 : W := o12 + o11
  let o14 : W := UInt256.mulMod w7 w17 w13
  let o15 : W := o14 + o13
  let o16 : W := UInt256.land w16 o9
  let o17 : ByteArray := MachineState.writeBytes s.memory (Data.Bytes.natToBytesPadded o16.toNat 32) 96
  let o18 : W := o15 - o16
  let o19 : W := w13 + o18
  let o20 : W := UInt256.mulMod o19 (N 2048) w13
  let o21 : W := MachineState.readWord o17 2048
  let o22 : W := MachineState.readWord o17 160
  let o23 : W := MachineState.readWord o17 800
  let o24 : W := o21 * o22
  let o25 : W := o24 + o20
  let o26 : W := UInt256.mulMod o21 o22 w13
  let o27 : W := o26 + o20
  let o28 : W := MachineState.readWord o17 2016
  let o29 : W := o28 * w6
  let o30 : W := o29 + o25
  let o31 : W := UInt256.mulMod o28 w6 w13
  let o32 : W := o31 + o27
  let o33 : W := w14 * w15
  let o34 : W := o33 + o30
  let o35 : W := w12 * w17
  let o36 : W := o35 + o34
  let o37 : W := UInt256.mulMod w14 w15 w13
  let o38 : W := o37 + o32
  let o39 : W := UInt256.mulMod w12 w17 w13
  let o40 : W := o39 + o38
  let o41 : W := UInt256.land w16 o36
  let o42 : ByteArray := MachineState.writeBytes o17 (Data.Bytes.natToBytesPadded o41.toNat 32) 128
  let o43 : W := o40 - o41
  let o44 : W := w13 + o43
  let o45 : W := UInt256.mulMod o44 (N 2048) w13
  let o46 : W := MachineState.readWord o42 2048
  let o47 : W := UInt256.mulMod o46 w6 w13
  let o48 : W := o47 + o45
  let o49 : W := o46 * w6
  let o50 : W := o49 + o45
  let o51 : W := w14 * w17
  let o52 : W := o51 + o50
  let o53 : W := UInt256.mulMod w14 w17 w13
  let o54 : W := o53 + o48
  let o55 : W := UInt256.land w16 o52
  let o56 : W := o54 - o55
  let o57 : W := w13 + o56
  let o58 : W := UInt256.mulMod o57 (N 2048) w13
  let o59 : ByteArray := MachineState.writeBytes o42 (Data.Bytes.natToBytesPadded o55.toNat 32) 160
  let n0 : W := carry * w0
  let n1 : W := n0 + w1
  let n2 : W := UInt256.mulMod w5 w2 w3
  let n3 : W := n2 + w4
  let n4 : W := w14 * w9
  let n5 : W := n4 + n1
  let n6 : W := w12 * w15
  let n7 : W := n6 + n5
  let n8 : W := w7 * w17
  let n9 : W := n8 + n7
  let n10 : W := UInt256.mulMod w14 w9 w13
  let n11 : W := n10 + n3
  let n12 : W := UInt256.mulMod w12 w15 w13
  let n13 : W := n12 + n11
  let n14 : W := UInt256.mulMod w7 w17 w13
  let n15 : W := n14 + n13
  let n16 : W := UInt256.land w16 n9
  let n17 : ByteArray := MachineState.writeBytes s.memory (Data.Bytes.natToBytesPadded n16.toNat 32) 96
  let n18 : W := n15 - n16
  let n19 : W := w13 + n18
  let n20 : W := UInt256.mulMod (N 2048) n19 w13
  let n21 : W := MachineState.readWord n17 2048
  let n22 : W := MachineState.readWord n17 160
  let n23 : W := UInt256.mulMod n21 n22 w13
  let n24 : W := n22 * n21
  let n25 : W := MachineState.readWord n17 2016
  let n26 : W := n20 + n23
  let n27 : W := UInt256.mulMod n25 w6 w13
  let n28 : W := n27 + n26
  let n29 : W := n20 + n24
  let n30 : W := MachineState.readWord n17 800
  let n31 : W := w6 * n25
  let n32 : W := n31 + n29
  let n33 : W := w14 * w15
  let n34 : W := n33 + n32
  let n35 : W := w12 * w17
  let n36 : W := n35 + n34
  let n37 : W := UInt256.mulMod w14 w15 w13
  let n38 : W := n37 + n28
  let n39 : W := UInt256.mulMod w12 w17 w13
  let n40 : W := n39 + n38
  let n41 : W := UInt256.land w16 n36
  let n42 : ByteArray := MachineState.writeBytes n17 (Data.Bytes.natToBytesPadded n41.toNat 32) 128
  let n43 : W := n40 - n41
  let n44 : W := w13 + n43
  let n45 : W := UInt256.mulMod (N 2048) n44 w13
  let n46 : W := MachineState.readWord n42 2048
  let n47 : W := UInt256.mulMod w6 n46 w13
  let n48 : W := UInt256.mulMod w14 w17 w13
  let n49 : W := w6 * n46
  let n50 : W := n45 + n49
  let n51 : W := w14 * w17
  let n52 : W := n51 + n50
  let n53 : W := UInt256.land w16 n52
  let n54 : W := n45 + n47
  let n55 : W := n54 + n48
  let n56 : ByteArray := MachineState.writeBytes n42 (Data.Bytes.natToBytesPadded n53.toNat 32) 160
  let n57 : W := n55 - n53
  let n58 : W := w13 + n57
  let n59 : W := UInt256.mulMod (N 2048) n58 w13
  have eq_o46 : o46 = o21 := by
    simpa only [o46,o42,o21] using
      (aux_shared0  o41 o17)
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
    simp only [n5,o5,eq_n4,eq_n1]
  have eq_n6 : n6 = o6 := by
    simp only [n6,o6]
  have eq_n7 : n7 = o7 := by
    simp only [n7,o7,eq_n6,eq_n5]
  have eq_n8 : n8 = o8 := by
    simp only [n8,o8]
  have eq_n9 : n9 = o9 := by
    simp only [n9,o9,eq_n8,eq_n7]
  have eq_n10 : n10 = o10 := by
    simp only [n10,o10]
  have eq_n11 : n11 = o11 := by
    simp only [n11,o11,eq_n10,eq_n3]
  have eq_n12 : n12 = o12 := by
    simp only [n12,o12]
  have eq_n13 : n13 = o13 := by
    simp only [n13,o13,eq_n12,eq_n11]
  have eq_n14 : n14 = o14 := by
    simp only [n14,o14]
  have eq_n15 : n15 = o15 := by
    simp only [n15,o15,eq_n14,eq_n13]
  have eq_n16 : n16 = o16 := by
    simp only [n16,o16,eq_n9]
  have eq_n17 : n17 = o17 := by
    simp only [n17,o17,eq_n16]
  have eq_n18 : n18 = o18 := by
    simp only [n18,o18,eq_n15,eq_n16]
  have eq_n19 : n19 = o19 := by
    simp only [n19,o19,eq_n18]
  have eq_n20 : n20 = o20 := by
    simpa only [n20,o20,eq_n19] using
      (aux_shared1 w13 o19)
  have eq_n21 : n21 = o21 := by
    simp only [n21,o21,eq_n17]
  have eq_n22 : n22 = o22 := by
    simp only [n22,o22,eq_n17]
  have eq_n23 : n23 = o26 := by
    simp only [n23,o26,eq_n21,eq_n22]
  have eq_n24 : n24 = o24 := by
    simpa only [n24,o24,eq_n22,eq_n21] using
      (aux_shared2  o22 o21)
  have eq_n25 : n25 = o28 := by
    simp only [n25,o28,eq_n17]
  have eq_n26 : n26 = o27 := by
    simpa only [n26,o27,eq_n20,eq_n23] using
      (aux_shared3  o20 o26)
  have eq_n27 : n27 = o31 := by
    simp only [n27,o31,eq_n25]
  have eq_n28 : n28 = o32 := by
    simp only [n28,o32,eq_n27,eq_n26]
  have eq_n29 : n29 = o25 := by
    simpa only [n29,o25,eq_n20,eq_n24] using
      (aux_shared3  o20 o24)
  have eq_n30 : n30 = o23 := by
    simp only [n30,o23,eq_n17]
  have eq_n31 : n31 = o29 := by
    simpa only [n31,o29,eq_n25] using
      (aux_shared4 w6 o28)
  have eq_n32 : n32 = o30 := by
    simp only [n32,o30,eq_n31,eq_n29]
  have eq_n33 : n33 = o33 := by
    simp only [n33,o33]
  have eq_n34 : n34 = o34 := by
    simp only [n34,o34,eq_n33,eq_n32]
  have eq_n35 : n35 = o35 := by
    simp only [n35,o35]
  have eq_n36 : n36 = o36 := by
    simp only [n36,o36,eq_n35,eq_n34]
  have eq_n37 : n37 = o37 := by
    simp only [n37,o37]
  have eq_n38 : n38 = o38 := by
    simp only [n38,o38,eq_n37,eq_n28]
  have eq_n39 : n39 = o39 := by
    simp only [n39,o39]
  have eq_n40 : n40 = o40 := by
    simp only [n40,o40,eq_n39,eq_n38]
  have eq_n41 : n41 = o41 := by
    simp only [n41,o41,eq_n36]
  have eq_n42 : n42 = o42 := by
    simp only [n42,o42,eq_n17,eq_n41]
  have eq_n43 : n43 = o43 := by
    simp only [n43,o43,eq_n40,eq_n41]
  have eq_n44 : n44 = o44 := by
    simp only [n44,o44,eq_n43]
  have eq_n45 : n45 = o45 := by
    simpa only [n45,o45,eq_n44] using
      (aux_shared1 w13 o44)
  have eq_n46 : n46 = o21 := by
    simpa only [n46,n42,o21,eq_n17,eq_n41] using
      (aux_shared0  o41 o17)
  have eq_n47 : n47 = o47 := by
    simpa only [n47,o47,eq_n46,eq_o46] using
      (aux_shared5 w6 w13 o21)
  have eq_n48 : n48 = o53 := by
    simp only [n48,o53]
  have eq_n49 : n49 = o49 := by
    simpa only [n49,o49,eq_n46,eq_o46] using
      (aux_shared4 w6 o21)
  have eq_n50 : n50 = o50 := by
    simpa only [n50,o50,eq_n45,eq_n49] using
      (aux_shared3  o45 o49)
  have eq_n51 : n51 = o51 := by
    simp only [n51,o51]
  have eq_n52 : n52 = o52 := by
    simp only [n52,o52,eq_n51,eq_n50]
  have eq_n53 : n53 = o55 := by
    simp only [n53,o55,eq_n52]
  have eq_n54 : n54 = o48 := by
    simpa only [n54,o48,eq_n45,eq_n47] using
      (aux_shared3  o45 o47)
  have eq_n55 : n55 = o54 := by
    simpa only [n55,o54,eq_n54,eq_n48] using
      (aux_shared3  o48 o53)
  have eq_n56 : n56 = o59 := by
    simp only [n56,o59,eq_n42,eq_n53]
  have eq_n57 : n57 = o56 := by
    simp only [n57,o56,eq_n55,eq_n53]
  have eq_n58 : n58 = o57 := by
    simp only [n58,o57,eq_n57]
  have eq_n59 : n59 = o58 := by
    simpa only [n59,o58,eq_n58] using
      (aux_shared1 w13 o57)
  change {s with pc := N 8138,memory := o59,stack := w19::w7::w8::o23::w10::w11::w12::w13::w14::w15::w16::w17::w18::o58::rest} =
    {s with pc := N 8138,memory := n56,stack := w19::w7::w8::n30::w10::w11::w12::w13::w14::w15::w16::w17::w18::n59::rest}
  simp only [eq_o46,eq_n0,eq_n1,eq_n2,eq_n3,eq_n4,eq_n5,eq_n6,eq_n7,eq_n8,eq_n9,eq_n10,eq_n11,eq_n12,eq_n13,eq_n14,eq_n15,eq_n16,eq_n17,eq_n18,eq_n19,eq_n20,eq_n21,eq_n22,eq_n23,eq_n24,eq_n25,eq_n26,eq_n27,eq_n28,eq_n29,eq_n30,eq_n31,eq_n32,eq_n33,eq_n34,eq_n35,eq_n36,eq_n37,eq_n38,eq_n39,eq_n40,eq_n41,eq_n42,eq_n43,eq_n44,eq_n45,eq_n46,eq_n47,eq_n48,eq_n49,eq_n50,eq_n51,eq_n52,eq_n53,eq_n54,eq_n55,eq_n56,eq_n57,eq_n58,eq_n59]
def eval18 (s : State) : State :=
  productColumn18Model s (s.stack[0]!) (s.stack[1]!) (s.stack[2]!) (s.stack[3]!) (s.stack[4]!) (s.stack[5]!) (s.stack[6]!) (s.stack[7]!) (s.stack[8]!) (s.stack[9]!) (s.stack[10]!) (s.stack[11]!) (s.stack[12]!) (s.stack[13]!) (s.stack[14]!) (s.stack[15]!) (s.stack[16]!) (s.stack[17]!) (s.stack[18]!) (s.stack[19]!) (s.stack[20]!) (s.stack.drop 21)
def eval19 (s : State) : State :=
  productColumn19Model s (s.stack[0]!) (s.stack[1]!) (s.stack[2]!) (s.stack[3]!) (s.stack[4]!) (s.stack[5]!) (s.stack[6]!) (s.stack[7]!) (s.stack[8]!) (s.stack[9]!) (s.stack[10]!) (s.stack[11]!) (s.stack[12]!) (s.stack[13]!) (s.stack[14]!) (s.stack[15]!) (s.stack.drop 16)
theorem old_eval (s : State) (carry w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 : W) (rest : List W) :
    oldModel s carry w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 rest = eval19 (eval18 ({s with pc := N 7976,stack := carry::w0::w1::w2::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::w16::w17::w18::w19::rest})) := by
  rfl
#print axioms old_eval
#print axioms new_run
#print axioms same_state
end CycleSubmission.Prepared.ProductGroup10052
