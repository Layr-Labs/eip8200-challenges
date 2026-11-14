import Challenge.Modexp.Submission.Proofs.Prepared.LowOverlapPacking
import Challenge.Modexp.Submission.Proofs.Prepared.OverlapPackRaw5
import Challenge.Modexp.Submission.Proofs.Prepared.OverlapPacking
import Challenge.Modexp.Submission.Proofs.Prepared.StackArgs
import Challenge.Modexp.Submission.Proofs.Prepared.Arithmetic
import Challenge.Modexp.Submission.Proofs.Bytecode.WindowNibbleDefs
import Challenge.Modexp.Submission.Proofs.Fast.Exp
open CycleSubmission.SharedStackArgs
set_option warningAsError true
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option maxRecDepth 40000
set_option maxHeartbeats 8000000
namespace CycleSubmission.R5.ExecNorm
open EvmSemantics EvmSemantics.EVM YulEvmCompiler
open Challenge.Modexp.Submission.Proofs.Bytecode.WindowNibbleKernel
open Challenge.EvmProof.Word (succ_ofNat_mod ofNat_add_mod ofNat_sub_ofNat literal_eq_ofNat)
open Challenge.EvmProof.Stepper (runInstr)
open Challenge.Modexp.Submission.Proofs.Fast.Exp (activeWords_fix)
local notation "W" => UInt256
local notation "N" => UInt256.ofNat
private theorem hz : ({val := 0} : W) = N 0 := rfl
private theorem hzn : ({val := 0} : W).toNat = 0 := rfl
/-! ## norm: pc 5184..5188, 4 instructions -/
def normpart0Program : List Instr :=
  [
  .op .JUMPDEST,
   .op (.Dup dA8),
   .op (.Dup dA5),
   .op .LT]
def normpart0Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 : W) (rest : List W) : State :=
  let v0 : W := UInt256.lt x4 x8
  {s with pc := N 10195,memory := s.memory,stack := v0::x0::x1::x2::x3::x4::x5::x6::x7::x8::x9::x10::x11::rest}
theorem normpart0_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions normpart0Program {s with pc := N 10191,stack := x0::x1::x2::x3::x4::x5::x6::x7::x8::x9::x10::x11::rest} =
      some (normpart0Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 rest) := by
  have hc (j : Nat) (hj : j ≤ 27) : rest.length + j < 1024 := by omega
  have hcr : rest.length < 1024 := by omega
  simp [hz,hzn,normpart0Program,normpart0Model,runInstructions,runInstr,List.exchange,succ_ofNat_mod,ofNat_add_mod,ofNat_sub_ofNat,Nat.add_assoc,State.activeWordsAfterUInt256,literal_eq_ofNat,hc,hcr]
def normProgram : List Instr :=
  [
  .op .JUMPDEST,
   .op (.Dup dA8),
   .op (.Dup dA5),
   .op .LT]
def normModel (s : State) (a0 a1 a2 a3 a4 n1 n2 n3 n4 P inv cntp : W) (rest : List W) : State :=
  let v0 : W := UInt256.lt a4 n4
  {s with pc := N 10195,memory := s.memory,stack := v0::a0::a1::a2::a3::a4::n1::n2::n3::n4::P::inv::cntp::rest}
theorem norm_run (s : State) (a0 a1 a2 a3 a4 n1 n2 n3 n4 P inv cntp : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions normProgram {s with pc := N 10191,stack := a0::a1::a2::a3::a4::n1::n2::n3::n4::P::inv::cntp::rest} =
      some (normModel s a0 a1 a2 a3 a4 n1 n2 n3 n4 P inv cntp rest) := by
  let v0 : W := UInt256.lt a4 n4
  have h0 : runInstructions normpart0Program {s with pc := N 10191,memory := s.memory,stack := a0::a1::a2::a3::a4::n1::n2::n3::n4::P::inv::cntp::rest} = some {s with pc := N 10195,memory := s.memory,stack := v0::a0::a1::a2::a3::a4::n1::n2::n3::n4::P::inv::cntp::rest} := by
    simpa only [normpart0Model,v0] using normpart0_run (s) a0 a1 a2 a3 a4 n1 n2 n3 n4 P inv cntp rest hcap hact
  exact h0
def norm_o0 (a0 a1 a2 a3 a4 n1 n2 n3 n4 P inv cntp : W) : W :=
  (UInt256.lt a4 n4)
theorem norm_eq (s : State) (a0 a1 a2 a3 a4 n1 n2 n3 n4 P inv cntp : W) (rest : List W) :
    normModel s a0 a1 a2 a3 a4 n1 n2 n3 n4 P inv cntp rest =
      {s with pc := N 10195,stack := (norm_o0 a0 a1 a2 a3 a4 n1 n2 n3 n4 P inv cntp)::a0::a1::a2::a3::a4::n1::n2::n3::n4::P::inv::cntp::rest} := by
  simp only [normModel,norm_o0]
/-! ## blk5192: pc 5192..5261, 52 instructions -/
open CycleSubmission.Prepared.Arithmetic
open Challenge.Modexp.Submission.Proofs.Fast
def preparedpart0Program : List Instr :=
  [
  .push 1 255,
   .op (.Dup dA12),
   .op (.Dup dA2),
   .op .SUB,
   .op (.Dup dA7),
   .op (.Dup dA1),
   .op (.Dup dA3)]
def preparedpart0Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 : W) (rest : List W) : State :=
  let v0 : W := MachineState.readWord s.memory 160
  let v1 : W := x0 - v0
  {s with pc := N 10207,memory := s.memory,stack := (N 255)::v1::x5::v1::(N 255)::x0::x1::x2::x3::x4::x5::x6::x7::x8::x9::x10::x11::rest}
theorem preparedpart0_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) (hcache : MachineState.readWord s.memory 160 = x11) :
    runInstructions preparedpart0Program {s with pc := N 10199,stack := x0::x1::x2::x3::x4::x5::x6::x7::x8::x9::x10::x11::rest} =
      some (preparedpart0Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 17) : rest.length + j < 1024 := by omega
  have ha160 : (160 : W).toNat = 160 := rfl
  have hf160 := Monpro.activeWords_fix s 160 32 (by decide) (by norm_num) hact
  simp [hcache,hz,hzn,preparedpart0Program,preparedpart0Model,runInstructions,Challenge.EvmProof.Stepper.runInstr,List.exchange,Challenge.EvmProof.Word.succ_ofNat_mod,Challenge.EvmProof.Word.ofNat_add_mod,Nat.add_assoc,State.activeWordsAfterUInt256,Challenge.EvmProof.Word.literal_eq_ofNat,capacity,ha160,hf160]
def preparedpart1Program : List Instr :=
  [
  .op .SHR,
   .op (.Dup dA5),
   .op .SUB,
   .op .SUB,
   .op (.Dup dA9),
   .op (.Dup dA1),
   .op (.Dup dA4),
   .op .SHR]
def preparedpart1Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 : W) (rest : List W) : State :=
  let v0 : W := UInt256.shiftRight x1 x0
  let v1 : W := x6 - v0
  let v2 : W := v1 - x2
  let v3 : W := UInt256.shiftRight v2 x4
  {s with pc := N 10215,memory := s.memory,stack := v3::x11::v2::x3::x4::x5::x6::x7::x8::x9::x10::x11::x12::x13::x14::x15::x16::rest}
theorem preparedpart1_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) (hk_x0 : x0 = N 255) (hk_x4 : x4 = N 255) :
    runInstructions preparedpart1Program {s with pc := N 10207,stack := x0::x1::x2::x3::x4::x5::x6::x7::x8::x9::x10::x11::x12::x13::x14::x15::x16::rest} =
      some (preparedpart1Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 18) : rest.length + j < 1024 := by omega
  simp [hk_x0,hk_x4,hz,hzn,preparedpart1Program,preparedpart1Model,runInstructions,Challenge.EvmProof.Stepper.runInstr,List.exchange,Challenge.EvmProof.Word.succ_ofNat_mod,Challenge.EvmProof.Word.ofNat_add_mod,Nat.add_assoc,State.activeWordsAfterUInt256,Challenge.EvmProof.Word.literal_eq_ofNat,capacity]
def preparedpart2Program : List Instr :=
  [
  .op (.Dup dA7),
   .op .SUB,
   .op .SUB,
   .push 1 224,
   .op .MLOAD,
   .op (.Dup dA0),
   .op (.Dup dA2),
   .op .AND]
def preparedpart2Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 : W) (rest : List W) : State :=
  let v0 : W := x7 - x0
  let v1 : W := v0 - x1
  let v2 : W := MachineState.readWord s.memory 224
  let v3 : W := UInt256.land v1 v2
  {s with pc := N 10224,memory := s.memory,stack := v3::v2::v1::x2::x3::x4::x5::x6::x7::x8::x9::x10::x11::x12::x13::x14::x15::x16::rest}
theorem preparedpart2_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) (hk_x4 : x4 = N 255) :
    runInstructions preparedpart2Program {s with pc := N 10215,stack := x0::x1::x2::x3::x4::x5::x6::x7::x8::x9::x10::x11::x12::x13::x14::x15::x16::rest} =
      some (preparedpart2Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 19) : rest.length + j < 1024 := by omega
  have ha224 : (224 : W).toNat = 224 := rfl
  have hf224 := Monpro.activeWords_fix s 224 32 (by decide) (by norm_num) hact
  simp [hk_x4,hz,hzn,preparedpart2Program,preparedpart2Model,runInstructions,Challenge.EvmProof.Stepper.runInstr,List.exchange,Challenge.EvmProof.Word.succ_ofNat_mod,Challenge.EvmProof.Word.ofNat_add_mod,Nat.add_assoc,State.activeWordsAfterUInt256,Challenge.EvmProof.Word.literal_eq_ofNat,capacity,ha224,hf224]
def preparedpart3Program : List Instr :=
  [
  .op (.Swap sA2),
   .op (.Dup dA1),
   .op .AND,
   .op (.Swap sA3),
   .op .AND,
   .op (.Swap sA3),
   .op .SHR,
   .op (.Dup dA7)]
def preparedpart3Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 : W) (rest : List W) : State :=
  let v0 : W := UInt256.land x1 x3
  let v1 : W := UInt256.land x4 x1
  let v2 : W := UInt256.shiftRight x2 x5
  {s with pc := N 10232,memory := s.memory,stack := x9::v2::x0::v0::v1::x6::x7::x8::x9::x10::x11::x12::x13::x14::x15::x16::x17::rest}
theorem preparedpart3_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) (hk_x5 : x5 = N 255) :
    runInstructions preparedpart3Program {s with pc := N 10224,stack := x0::x1::x2::x3::x4::x5::x6::x7::x8::x9::x10::x11::x12::x13::x14::x15::x16::x17::rest} =
      some (preparedpart3Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 19) : rest.length + j < 1024 := by omega
  simp [hk_x5,hz,hzn,preparedpart3Program,preparedpart3Model,runInstructions,Challenge.EvmProof.Stepper.runInstr,List.exchange,Challenge.EvmProof.Word.succ_ofNat_mod,Challenge.EvmProof.Word.ofNat_add_mod,Nat.add_assoc,State.activeWordsAfterUInt256,Challenge.EvmProof.Word.literal_eq_ofNat,capacity]
def preparedpart4Program : List Instr :=
  [
  .op .SUB,
   .op (.Dup dA11),
   .op (.Swap sA0),
   .op .SUB,
   .op (.Dup dA0),
   .push 1 255,
   .op .SHR,
   .op (.Swap sA0)]
def preparedpart4Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 : W) (rest : List W) : State :=
  let v0 : W := x0 - x1
  let v1 : W := v0 - x12
  let v2 : W := UInt256.shiftRight v1 (N 255)
  {s with pc := N 10241,memory := s.memory,stack := v1::v2::x2::x3::x4::x5::x6::x7::x8::x9::x10::x11::x12::x13::x14::x15::x16::rest}
theorem preparedpart4_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions preparedpart4Program {s with pc := N 10232,stack := x0::x1::x2::x3::x4::x5::x6::x7::x8::x9::x10::x11::x12::x13::x14::x15::x16::rest} =
      some (preparedpart4Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 18) : rest.length + j < 1024 := by omega
  simp [hz,hzn,preparedpart4Program,preparedpart4Model,runInstructions,Challenge.EvmProof.Stepper.runInstr,List.exchange,Challenge.EvmProof.Word.succ_ofNat_mod,Challenge.EvmProof.Word.ofNat_add_mod,Nat.add_assoc,State.activeWordsAfterUInt256,Challenge.EvmProof.Word.literal_eq_ofNat,capacity]
def preparedpart5Program : List Instr :=
  [
  .push 1 224,
   .op .MLOAD,
   .op .AND,
   .op (.Swap sA0),
   .op (.Dup dA9),
   .op .SUB,
   .op (.Dup dA13),
   .op (.Swap sA0)]
def preparedpart5Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 : W) (rest : List W) : State :=
  let v0 : W := MachineState.readWord s.memory 224
  let v1 : W := UInt256.land v0 x0
  let v2 : W := x9 - x1
  {s with pc := N 10250,memory := s.memory,stack := v2::x13::v1::x2::x3::x4::x5::x6::x7::x8::x9::x10::x11::x12::x13::x14::x15::x16::rest}
theorem preparedpart5_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions preparedpart5Program {s with pc := N 10241,stack := x0::x1::x2::x3::x4::x5::x6::x7::x8::x9::x10::x11::x12::x13::x14::x15::x16::rest} =
      some (preparedpart5Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 18) : rest.length + j < 1024 := by omega
  have ha224 : (224 : W).toNat = 224 := rfl
  have hf224 := Monpro.activeWords_fix s 224 32 (by decide) (by norm_num) hact
  simp [hz,hzn,preparedpart5Program,preparedpart5Model,runInstructions,Challenge.EvmProof.Stepper.runInstr,List.exchange,Challenge.EvmProof.Word.succ_ofNat_mod,Challenge.EvmProof.Word.ofNat_add_mod,Nat.add_assoc,State.activeWordsAfterUInt256,Challenge.EvmProof.Word.literal_eq_ofNat,capacity,ha224,hf224]
def preparedpart6Program : List Instr :=
  [
  .op .SUB,
   .op (.Dup dA0),
   .push 1 255,
   .op .SHR]
def preparedpart6Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 : W) (rest : List W) : State :=
  let v0 : W := x0 - x1
  let v1 : W := UInt256.shiftRight v0 (N 255)
  {s with pc := N 10255,memory := s.memory,stack := v1::v0::x2::x3::x4::x5::x6::x7::x8::x9::x10::x11::x12::x13::x14::x15::x16::x17::rest}
theorem preparedpart6_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions preparedpart6Program {s with pc := N 10250,stack := x0::x1::x2::x3::x4::x5::x6::x7::x8::x9::x10::x11::x12::x13::x14::x15::x16::x17::rest} =
      some (preparedpart6Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 19) : rest.length + j < 1024 := by omega
  simp [hz,hzn,preparedpart6Program,preparedpart6Model,runInstructions,Challenge.EvmProof.Stepper.runInstr,List.exchange,Challenge.EvmProof.Word.succ_ofNat_mod,Challenge.EvmProof.Word.ofNat_add_mod,Nat.add_assoc,State.activeWordsAfterUInt256,Challenge.EvmProof.Word.literal_eq_ofNat,capacity]
def preparedProgram : List Instr :=
  [
  .push 1 255,
   .op (.Dup dA12),
   .op (.Dup dA2),
   .op .SUB,
   .op (.Dup dA7),
   .op (.Dup dA1),
   .op (.Dup dA3),
   .op .SHR,
   .op (.Dup dA5),
   .op .SUB,
   .op .SUB,
   .op (.Dup dA9),
   .op (.Dup dA1),
   .op (.Dup dA4),
   .op .SHR,
   .op (.Dup dA7),
   .op .SUB,
   .op .SUB,
   .push 1 224,
   .op .MLOAD,
   .op (.Dup dA0),
   .op (.Dup dA2),
   .op .AND,
   .op (.Swap sA2),
   .op (.Dup dA1),
   .op .AND,
   .op (.Swap sA3),
   .op .AND,
   .op (.Swap sA3),
   .op .SHR,
   .op (.Dup dA7),
   .op .SUB,
   .op (.Dup dA11),
   .op (.Swap sA0),
   .op .SUB,
   .op (.Dup dA0),
   .push 1 255,
   .op .SHR,
   .op (.Swap sA0),
   .push 1 224,
   .op .MLOAD,
   .op .AND,
   .op (.Swap sA0),
   .op (.Dup dA9),
   .op .SUB,
   .op (.Dup dA13),
   .op (.Swap sA0),
   .op .SUB,
   .op (.Dup dA0),
   .push 1 255,
   .op .SHR]
def preparedModel (s : State) (a0 a1 a2 a3 a4 n1 n2 n3 n4 P inv cntp : W) (rest : List W) : State :=
  let v0 : W := MachineState.readWord s.memory 160
  let v1 : W := a0 - v0
  let v2 : W := UInt256.shiftRight v1 (N 255)
  let v3 : W := a1 - v2
  let v4 : W := v3 - n1
  let v5 : W := UInt256.shiftRight v4 (N 255)
  let v6 : W := a2 - v5
  let v7 : W := v6 - n2
  let v8 : W := MachineState.readWord s.memory 224
  let v9 : W := UInt256.land v7 v8
  let v10 : W := UInt256.land v8 v4
  let v11 : W := UInt256.land v1 v8
  let v12 : W := UInt256.shiftRight v7 (N 255)
  let v13 : W := a3 - v12
  let v14 : W := v13 - n3
  let v15 : W := UInt256.shiftRight v14 (N 255)
  let v16 : W := MachineState.readWord s.memory 224
  let v17 : W := UInt256.land v16 v14
  let v18 : W := a4 - v15
  let v19 : W := v18 - n4
  let v20 : W := UInt256.shiftRight v19 (N 255)
  {s with pc := N 10255,memory := s.memory,stack := v20::v19::v17::v9::v10::v11::a0::a1::a2::a3::a4::n1::n2::n3::n4::P::inv::cntp::rest}
theorem prepared_run (s : State) (a0 a1 a2 a3 a4 n1 n2 n3 n4 P inv cntp : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) (hcache : MachineState.readWord s.memory 160 = cntp) :
    runInstructions preparedProgram {s with pc := N 10199,stack := a0::a1::a2::a3::a4::n1::n2::n3::n4::P::inv::cntp::rest} =
      some (preparedModel s a0 a1 a2 a3 a4 n1 n2 n3 n4 P inv cntp rest) := by
  let v0 : W := MachineState.readWord s.memory 160
  let v1 : W := a0 - v0
  let v2 : W := UInt256.shiftRight v1 (N 255)
  let v3 : W := a1 - v2
  let v4 : W := v3 - n1
  let v5 : W := UInt256.shiftRight v4 (N 255)
  let v6 : W := a2 - v5
  let v7 : W := v6 - n2
  let v8 : W := MachineState.readWord s.memory 224
  let v9 : W := UInt256.land v7 v8
  let v10 : W := UInt256.land v8 v4
  let v11 : W := UInt256.land v1 v8
  let v12 : W := UInt256.shiftRight v7 (N 255)
  let v13 : W := a3 - v12
  let v14 : W := v13 - n3
  let v15 : W := UInt256.shiftRight v14 (N 255)
  let v16 : W := MachineState.readWord s.memory 224
  let v17 : W := UInt256.land v16 v14
  let v18 : W := a4 - v15
  let v19 : W := v18 - n4
  let v20 : W := UInt256.shiftRight v19 (N 255)
  have h0 : runInstructions preparedpart0Program {s with pc := N 10199,memory := s.memory,stack := a0::a1::a2::a3::a4::n1::n2::n3::n4::P::inv::cntp::rest} = some {s with pc := N 10207,memory := s.memory,stack := (N 255)::v1::n1::v1::(N 255)::a0::a1::a2::a3::a4::n1::n2::n3::n4::P::inv::cntp::rest} := by
    simpa only [preparedpart0Model,v0,v1] using preparedpart0_run (s) a0 a1 a2 a3 a4 (n1) (n2) (n3) (n4) (P) (inv) (cntp) rest hcap hact hcache
  have h1 : runInstructions preparedpart1Program {s with pc := N 10207,memory := s.memory,stack := (N 255)::v1::n1::v1::(N 255)::a0::a1::a2::a3::a4::n1::n2::n3::n4::P::inv::cntp::rest} = some {s with pc := N 10215,memory := s.memory,stack := v5::n2::v4::v1::(N 255)::a0::a1::a2::a3::a4::n1::n2::n3::n4::P::inv::cntp::rest} := by
    simpa only [preparedpart1Model,v2,v3,v4,v5] using preparedpart1_run (s) ((N 255)) v1 (n1) v1 ((N 255)) a0 a1 a2 a3 a4 (n1) (n2) (n3) (n4) (P) (inv) (cntp) rest hcap hact (by rfl) (by rfl)
  have h2 : runInstructions preparedpart2Program {s with pc := N 10215,memory := s.memory,stack := v5::n2::v4::v1::(N 255)::a0::a1::a2::a3::a4::n1::n2::n3::n4::P::inv::cntp::rest} = some {s with pc := N 10224,memory := s.memory,stack := v9::v8::v7::v4::v1::(N 255)::a0::a1::a2::a3::a4::n1::n2::n3::n4::P::inv::cntp::rest} := by
    simpa only [preparedpart2Model,v6,v7,v8,v9] using preparedpart2_run (s) v5 (n2) v4 v1 ((N 255)) a0 a1 a2 a3 a4 (n1) (n2) (n3) (n4) (P) (inv) (cntp) rest hcap hact (by rfl)
  have h3 : runInstructions preparedpart3Program {s with pc := N 10224,memory := s.memory,stack := v9::v8::v7::v4::v1::(N 255)::a0::a1::a2::a3::a4::n1::n2::n3::n4::P::inv::cntp::rest} = some {s with pc := N 10232,memory := s.memory,stack := a3::v12::v9::v10::v11::a0::a1::a2::a3::a4::n1::n2::n3::n4::P::inv::cntp::rest} := by
    simpa only [preparedpart3Model,v10,v11,v12] using preparedpart3_run (s) v9 v8 v7 v4 v1 ((N 255)) a0 a1 a2 a3 a4 (n1) (n2) (n3) (n4) (P) (inv) (cntp) rest hcap hact (by rfl)
  have h4 : runInstructions preparedpart4Program {s with pc := N 10232,memory := s.memory,stack := a3::v12::v9::v10::v11::a0::a1::a2::a3::a4::n1::n2::n3::n4::P::inv::cntp::rest} = some {s with pc := N 10241,memory := s.memory,stack := v14::v15::v9::v10::v11::a0::a1::a2::a3::a4::n1::n2::n3::n4::P::inv::cntp::rest} := by
    simpa only [preparedpart4Model,v13,v14,v15] using preparedpart4_run (s) a3 v12 v9 v10 v11 a0 a1 a2 a3 a4 (n1) (n2) (n3) (n4) (P) (inv) (cntp) rest hcap hact
  have h5 : runInstructions preparedpart5Program {s with pc := N 10241,memory := s.memory,stack := v14::v15::v9::v10::v11::a0::a1::a2::a3::a4::n1::n2::n3::n4::P::inv::cntp::rest} = some {s with pc := N 10250,memory := s.memory,stack := v18::n4::v17::v9::v10::v11::a0::a1::a2::a3::a4::n1::n2::n3::n4::P::inv::cntp::rest} := by
    simpa only [preparedpart5Model,v16,v17,v18] using preparedpart5_run (s) v14 v15 v9 v10 v11 a0 a1 a2 a3 a4 (n1) (n2) (n3) (n4) (P) (inv) (cntp) rest hcap hact
  have h6 : runInstructions preparedpart6Program {s with pc := N 10250,memory := s.memory,stack := v18::n4::v17::v9::v10::v11::a0::a1::a2::a3::a4::n1::n2::n3::n4::P::inv::cntp::rest} = some {s with pc := N 10255,memory := s.memory,stack := v20::v19::v17::v9::v10::v11::a0::a1::a2::a3::a4::n1::n2::n3::n4::P::inv::cntp::rest} := by
    simpa only [preparedpart6Model,v19,v20] using preparedpart6_run (s) v18 (n4) v17 v9 v10 v11 a0 a1 a2 a3 a4 (n1) (n2) (n3) (n4) (P) (inv) (cntp) rest hcap hact
  exact (runInstructions_append_some _ _ _ _ _ h0 (runInstructions_append_some _ _ _ _ _ h1 (runInstructions_append_some _ _ _ _ _ h2 (runInstructions_append_some _ _ _ _ _ h3 (runInstructions_append_some _ _ _ _ _ h4 (runInstructions_append_some _ _ _ _ _ h5 h6))))))
#print axioms prepared_run
def blk5192Model (s : State) (a0 a1 a2 a3 a4 n1 n2 n3 n4 P inv cntp : W) (rest : List W) : State :=
  let v0 : W := MachineState.readWord s.memory 160
  let v1 : W := a0 - v0
  let v2 : W := UInt256.shiftRight v1 (N 255)
  let v3 : W := MachineState.readWord s.memory 224
  let v4 : W := UInt256.land v3 v1
  let v5 : W := a1 - v2
  let v6 : W := v5 - n1
  let v7 : W := UInt256.shiftRight v6 (N 255)
  let v8 : W := MachineState.readWord s.memory 224
  let v9 : W := UInt256.land v8 v6
  let v10 : W := a2 - v7
  let v11 : W := v10 - n2
  let v12 : W := UInt256.shiftRight v11 (N 255)
  let v13 : W := MachineState.readWord s.memory 224
  let v14 : W := UInt256.land v13 v11
  let v15 : W := a3 - v12
  let v16 : W := v15 - n3
  let v17 : W := UInt256.shiftRight v16 (N 255)
  let v18 : W := MachineState.readWord s.memory 224
  let v19 : W := UInt256.land v18 v16
  let v20 : W := a4 - v17
  let v21 : W := v20 - n4
  let v22 : W := UInt256.shiftRight v21 (N 255)
  {s with pc := N 10255,memory := s.memory,stack := v22::v21::v19::v14::v9::v4::a0::a1::a2::a3::a4::n1::n2::n3::n4::P::inv::cntp::rest}
def blk5192Program : List Instr := preparedProgram
private theorem prepared_model_eq (s : State) (a0 a1 a2 a3 a4 n1 n2 n3 n4 P inv cntp : W) (rest : List W) :
    preparedModel s a0 a1 a2 a3 a4 n1 n2 n3 n4 P inv cntp rest = blk5192Model s a0 a1 a2 a3 a4 n1 n2 n3 n4 P inv cntp rest := by
  simp (disch := decide) only [preparedModel,blk5192Model,addC,addA,addL,mulC,mmC,amC,andC,orC,xorC,eqC,read_disjoint]
theorem blk5192_run (s : State) (a0 a1 a2 a3 a4 n1 n2 n3 n4 P inv cntp : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) (hcache : MachineState.readWord s.memory 160 = cntp) :
    runInstructions blk5192Program {s with pc := N 10199,stack := a0::a1::a2::a3::a4::n1::n2::n3::n4::P::inv::cntp::rest} =
      some (blk5192Model s a0 a1 a2 a3 a4 n1 n2 n3 n4 P inv cntp rest) := by
  exact (prepared_run s a0 a1 a2 a3 a4 n1 n2 n3 n4 P inv cntp rest hcap hact hcache).trans
    (congrArg some (prepared_model_eq s a0 a1 a2 a3 a4 n1 n2 n3 n4 P inv cntp rest))
#print axioms blk5192_run
def blk5192_o0 (a0 a1 a2 a3 a4 n1 n2 n3 n4 P inv cntp n0 M : W) : W :=
  (UInt256.shiftRight ((a4 - (UInt256.shiftRight ((a3 - (UInt256.shiftRight ((a2 - (UInt256.shiftRight ((a1 - (UInt256.shiftRight (a0 - n0) (N 255))) - n1) (N 255))) - n2) (N 255))) - n3) (N 255))) - n4) (N 255))
def blk5192_o1 (a0 a1 a2 a3 a4 n1 n2 n3 n4 P inv cntp n0 M : W) : W :=
  ((a4 - (UInt256.shiftRight ((a3 - (UInt256.shiftRight ((a2 - (UInt256.shiftRight ((a1 - (UInt256.shiftRight (a0 - n0) (N 255))) - n1) (N 255))) - n2) (N 255))) - n3) (N 255))) - n4)
def blk5192_o2 (a0 a1 a2 a3 a4 n1 n2 n3 n4 P inv cntp n0 M : W) : W :=
  (UInt256.land M ((a3 - (UInt256.shiftRight ((a2 - (UInt256.shiftRight ((a1 - (UInt256.shiftRight (a0 - n0) (N 255))) - n1) (N 255))) - n2) (N 255))) - n3))
def blk5192_o3 (a0 a1 a2 a3 a4 n1 n2 n3 n4 P inv cntp n0 M : W) : W :=
  (UInt256.land M ((a2 - (UInt256.shiftRight ((a1 - (UInt256.shiftRight (a0 - n0) (N 255))) - n1) (N 255))) - n2))
def blk5192_o4 (a0 a1 a2 a3 a4 n1 n2 n3 n4 P inv cntp n0 M : W) : W :=
  (UInt256.land M ((a1 - (UInt256.shiftRight (a0 - n0) (N 255))) - n1))
def blk5192_o5 (a0 a1 a2 a3 a4 n1 n2 n3 n4 P inv cntp n0 M : W) : W :=
  (UInt256.land M (a0 - n0))
theorem blk5192_eq (s : State) (a0 a1 a2 a3 a4 n1 n2 n3 n4 P inv cntp n0 M : W) (rest : List W)
    (h_n0 : MachineState.readWord s.memory 160 = n0)
    (h_M : MachineState.readWord s.memory 224 = M) :
    blk5192Model s a0 a1 a2 a3 a4 n1 n2 n3 n4 P inv cntp rest =
      {s with pc := N 10255,stack := (blk5192_o0 a0 a1 a2 a3 a4 n1 n2 n3 n4 P inv cntp n0 M)::(blk5192_o1 a0 a1 a2 a3 a4 n1 n2 n3 n4 P inv cntp n0 M)::(blk5192_o2 a0 a1 a2 a3 a4 n1 n2 n3 n4 P inv cntp n0 M)::(blk5192_o3 a0 a1 a2 a3 a4 n1 n2 n3 n4 P inv cntp n0 M)::(blk5192_o4 a0 a1 a2 a3 a4 n1 n2 n3 n4 P inv cntp n0 M)::(blk5192_o5 a0 a1 a2 a3 a4 n1 n2 n3 n4 P inv cntp n0 M)::a0::a1::a2::a3::a4::n1::n2::n3::n4::P::inv::cntp::rest} := by
  simp only [blk5192Model,blk5192_o0,blk5192_o1,blk5192_o2,blk5192_o3,blk5192_o4,blk5192_o5,h_n0,h_M]
/-! ## blk5265: pc 5265..5275, 10 instructions -/
def blk5265part0Program : List Instr :=
  [
  .op (.Swap sA8),
   .op .POP,
   .op (.Swap sA6),
   .op .POP,
   .op (.Swap sA4),
   .op .POP,
   .op (.Swap sA2),
   .op .POP]
def blk5265part0Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 : W) (rest : List W) : State :=
  {s with pc := N 10267,memory := s.memory,stack := x4::x5::x3::x2::x1::x0::x10::x11::x12::x13::x14::x15::x16::rest}
theorem blk5265part0_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions blk5265part0Program {s with pc := N 10259,stack := x0::x1::x2::x3::x4::x5::x6::x7::x8::x9::x10::x11::x12::x13::x14::x15::x16::rest} =
      some (blk5265part0Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 rest) := by
  have hc (j : Nat) (hj : j ≤ 30) : rest.length + j < 1024 := by omega
  have hcr : rest.length < 1024 := by omega
  simp [hz,hzn,blk5265part0Program,blk5265part0Model,runInstructions,runInstr,List.exchange,succ_ofNat_mod,ofNat_add_mod,ofNat_sub_ofNat,Nat.add_assoc,State.activeWordsAfterUInt256,literal_eq_ofNat,hc,hcr]
def blk5265part1Program : List Instr :=
  [
  .op (.Swap sA0),
   .op .POP]
def blk5265part1Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 : W) (rest : List W) : State :=
  {s with pc := N 10269,memory := s.memory,stack := x0::x2::x3::x4::x5::x6::x7::x8::x9::x10::x11::x12::rest}
theorem blk5265part1_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions blk5265part1Program {s with pc := N 10267,stack := x0::x1::x2::x3::x4::x5::x6::x7::x8::x9::x10::x11::x12::rest} =
      some (blk5265part1Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 rest) := by
  have hc (j : Nat) (hj : j ≤ 26) : rest.length + j < 1024 := by omega
  have hcr : rest.length < 1024 := by omega
  simp [hz,hzn,blk5265part1Program,blk5265part1Model,runInstructions,runInstr,List.exchange,succ_ofNat_mod,ofNat_add_mod,ofNat_sub_ofNat,Nat.add_assoc,State.activeWordsAfterUInt256,literal_eq_ofNat,hc,hcr]
def blk5265Program : List Instr :=
  [
  .op (.Swap sA8),
   .op .POP,
   .op (.Swap sA6),
   .op .POP,
   .op (.Swap sA4),
   .op .POP,
   .op (.Swap sA2),
   .op .POP,
   .op (.Swap sA0),
   .op .POP]
def blk5265Model (s : State) (d4 d3 d2 d1 d0 a0 a1 a2 a3 a4 n1 n2 n3 n4 P inv cntp : W) (rest : List W) : State :=
  {s with pc := N 10269,memory := s.memory,stack := d0::d1::d2::d3::d4::n1::n2::n3::n4::P::inv::cntp::rest}
theorem blk5265_run (s : State) (d4 d3 d2 d1 d0 a0 a1 a2 a3 a4 n1 n2 n3 n4 P inv cntp : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions blk5265Program {s with pc := N 10259,stack := d4::d3::d2::d1::d0::a0::a1::a2::a3::a4::n1::n2::n3::n4::P::inv::cntp::rest} =
      some (blk5265Model s d4 d3 d2 d1 d0 a0 a1 a2 a3 a4 n1 n2 n3 n4 P inv cntp rest) := by
  have h0 : runInstructions blk5265part0Program {s with pc := N 10259,memory := s.memory,stack := d4::d3::d2::d1::d0::a0::a1::a2::a3::a4::n1::n2::n3::n4::P::inv::cntp::rest} = some {s with pc := N 10267,memory := s.memory,stack := d0::a0::d1::d2::d3::d4::n1::n2::n3::n4::P::inv::cntp::rest} := by
    simpa only [blk5265part0Model] using blk5265part0_run (s) d4 d3 d2 d1 d0 a0 a1 a2 a3 a4 n1 n2 n3 n4 P inv cntp rest hcap hact
  have h1 : runInstructions blk5265part1Program {s with pc := N 10267,memory := s.memory,stack := d0::a0::d1::d2::d3::d4::n1::n2::n3::n4::P::inv::cntp::rest} = some {s with pc := N 10269,memory := s.memory,stack := d0::d1::d2::d3::d4::n1::n2::n3::n4::P::inv::cntp::rest} := by
    simpa only [blk5265part1Model] using blk5265part1_run (s) d0 a0 d1 d2 d3 d4 n1 n2 n3 n4 P inv cntp rest hcap hact
  exact (runInstructions_append_some _ _ _ _ _ h0 h1)
theorem blk5265_eq (s : State) (d4 d3 d2 d1 d0 a0 a1 a2 a3 a4 n1 n2 n3 n4 P inv cntp : W) (rest : List W) :
    blk5265Model s d4 d3 d2 d1 d0 a0 a1 a2 a3 a4 n1 n2 n3 n4 P inv cntp rest =
      {s with pc := N 10269,stack := d0::d1::d2::d3::d4::n1::n2::n3::n4::P::inv::cntp::rest} := by
  simp only [blk5265Model]
/-! ## neg: pc 5279..5285, 6 instructions -/
def negpart0Program : List Instr :=
  [
  .op .JUMPDEST,
   .op .POP,
   .op .POP,
   .op .POP,
   .op .POP,
   .op .POP]
def negpart0Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 : W) (rest : List W) : State :=
  {s with pc := N 10279,memory := s.memory,stack := x5::x6::x7::x8::x9::x10::x11::x12::x13::x14::x15::x16::rest}
theorem negpart0_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions negpart0Program {s with pc := N 10273,stack := x0::x1::x2::x3::x4::x5::x6::x7::x8::x9::x10::x11::x12::x13::x14::x15::x16::rest} =
      some (negpart0Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 rest) := by
  have hc (j : Nat) (hj : j ≤ 30) : rest.length + j < 1024 := by omega
  have hcr : rest.length < 1024 := by omega
  simp [hz,hzn,negpart0Program,negpart0Model,runInstructions,runInstr,List.exchange,succ_ofNat_mod,ofNat_add_mod,ofNat_sub_ofNat,Nat.add_assoc,State.activeWordsAfterUInt256,literal_eq_ofNat,hc,hcr]
def negProgram : List Instr :=
  [
  .op .JUMPDEST,
   .op .POP,
   .op .POP,
   .op .POP,
   .op .POP,
   .op .POP]
def negModel (s : State) (d4 d3 d2 d1 d0 a0 a1 a2 a3 a4 n1 n2 n3 n4 P inv cntp : W) (rest : List W) : State :=
  {s with pc := N 10279,memory := s.memory,stack := a0::a1::a2::a3::a4::n1::n2::n3::n4::P::inv::cntp::rest}
theorem neg_run (s : State) (d4 d3 d2 d1 d0 a0 a1 a2 a3 a4 n1 n2 n3 n4 P inv cntp : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions negProgram {s with pc := N 10273,stack := d4::d3::d2::d1::d0::a0::a1::a2::a3::a4::n1::n2::n3::n4::P::inv::cntp::rest} =
      some (negModel s d4 d3 d2 d1 d0 a0 a1 a2 a3 a4 n1 n2 n3 n4 P inv cntp rest) := by
  have h0 : runInstructions negpart0Program {s with pc := N 10273,memory := s.memory,stack := d4::d3::d2::d1::d0::a0::a1::a2::a3::a4::n1::n2::n3::n4::P::inv::cntp::rest} = some {s with pc := N 10279,memory := s.memory,stack := a0::a1::a2::a3::a4::n1::n2::n3::n4::P::inv::cntp::rest} := by
    simpa only [negpart0Model] using negpart0_run (s) d4 d3 d2 d1 d0 a0 a1 a2 a3 a4 n1 n2 n3 n4 P inv cntp rest hcap hact
  exact h0
theorem neg_eq (s : State) (d4 d3 d2 d1 d0 a0 a1 a2 a3 a4 n1 n2 n3 n4 P inv cntp : W) (rest : List W) :
    negModel s d4 d3 d2 d1 d0 a0 a1 a2 a3 a4 n1 n2 n3 n4 P inv cntp rest =
      {s with pc := N 10279,stack := a0::a1::a2::a3::a4::n1::n2::n3::n4::P::inv::cntp::rest} := by
  simp only [negModel]
/-! ## done: pc 5285..5330, 35 instructions -/
def doneProgram : List Instr := OverlapPackRaw5.program
def doneModel (s : State) (a0 a1 a2 a3 a4 n1 n2 n3 n4 P inv cntp : W) (rest : List W) : State :=
 OverlapPackRaw5.model s a0 a1 a2 a3 a4 n1 n2 n3 n4 P inv cntp rest
theorem done_run (s : State) (a0 a1 a2 a3 a4 n1 n2 n3 n4 P inv cntp : W) (rest : List W)
 (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
 runInstructions doneProgram {s with pc := N 10279,stack := a0::a1::a2::a3::a4::n1::n2::n3::n4::P::inv::cntp::rest} =
 some (doneModel s a0 a1 a2 a3 a4 n1 n2 n3 n4 P inv cntp rest) :=
 OverlapPackRaw5.run s a0 a1 a2 a3 a4 n1 n2 n3 n4 P inv cntp rest hcap hact
def done_mem (mem : ByteArray) (a0 a1 a2 a3 a4 n1 n2 n3 n4 P inv cntp : W) : ByteArray :=
 LowOverlapPackingMemory.memory5 mem (fun | 0 => a0 | 1 => a1 | 2 => a2 | 3 => a3 | 4 => a4 | _ => N 0)
theorem done_eq (s : State) (a0 a1 a2 a3 a4 n1 n2 n3 n4 P inv cntp : W) (rest : List W) :
 doneModel s a0 a1 a2 a3 a4 n1 n2 n3 n4 P inv cntp rest =
 {s with pc := N 10294,memory := done_mem s.memory a0 a1 a2 a3 a4 n1 n2 n3 n4 P inv cntp,stack := n1::n2::n3::n4::P::inv::cntp::rest} := by rfl
end CycleSubmission.R5.ExecNorm
