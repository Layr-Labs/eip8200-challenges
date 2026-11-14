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
namespace R5CachedSuffix
def part0Program : List Instr := [.push 1 224,.op .MLOAD,.push 2 2170,.op .MLOAD,.op (.Dup dA1),.op .AND,.push 2 2200,.op .MLOAD]
def part0Model (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 w20 w21 w22 w23 w24 : W) (rest : List W) : State :=
  let v0 : W := MachineState.readWord (s.memory) 224
  let v1 : W := MachineState.readWord (s.memory) 2170
  let v2 : W := UInt256.land v0 v1
  let v3 : W := MachineState.readWord (s.memory) 2200
  {s with pc := N 8794,memory := s.memory,stack := v3::v2::v0::w0::w1::w2::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::w16::w17::w18::w19::w20::w21::w22::w23::w24::rest}
theorem part0_run (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 w20 w21 w22 w23 w24 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions part0Program {s with pc := N 8781,memory := s.memory,stack := w0::w1::w2::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::w16::w17::w18::w19::w20::w21::w22::w23::w24::rest} = some (part0Model s w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 w20 w21 w22 w23 w24 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 63) : rest.length+j < 1024 := by omega
  have ha224 : (224 : W).toNat = 224 := rfl
  have hf224 := Monpro.activeWords_fix s 224 32 (by decide) (by norm_num) hact
  have ha2170 : (2170 : W).toNat = 2170 := rfl
  have hf2170 := Monpro.activeWords_fix s 2170 32 (by decide) (by norm_num) hact
  have ha2200 : (2200 : W).toNat = 2200 := rfl
  have hf2200 := Monpro.activeWords_fix s 2200 32 (by decide) (by norm_num) hact
  simp [hz,hzn,part0Program,part0Model,runInstructions,runInstr,List.exchange,succ_ofNat_mod,ofNat_add_mod,Nat.add_assoc,State.activeWordsAfterUInt256,literal_eq_ofNat,capacity,ha224,hf224,ha2170,hf2170,ha2200,hf2200]
def part1Program : List Instr := [.op (.Dup dA2),.op .AND,.push 2 2208,.op .MLOAD,.push 1 176,.op .SHL,.push 2 2140,.op .MLOAD]
def part1Model (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 w20 w21 w22 w23 w24 w25 w26 w27 : W) (rest : List W) : State :=
  let v0 : W := UInt256.land w2 w0
  let v1 : W := MachineState.readWord (s.memory) 2208
  let v2 : W := UInt256.shiftLeft v1 (N 176)
  let v3 : W := MachineState.readWord (s.memory) 2140
  {s with pc := N 8807,memory := s.memory,stack := v3::v2::v0::w1::w2::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::w16::w17::w18::w19::w20::w21::w22::w23::w24::w25::w26::w27::rest}
theorem part1_run (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 w20 w21 w22 w23 w24 w25 w26 w27 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions part1Program {s with pc := N 8794,memory := s.memory,stack := w0::w1::w2::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::w16::w17::w18::w19::w20::w21::w22::w23::w24::w25::w26::w27::rest} = some (part1Model s w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 w20 w21 w22 w23 w24 w25 w26 w27 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 63) : rest.length+j < 1024 := by omega
  have ha2140 : (2140 : W).toNat = 2140 := rfl
  have hf2140 := Monpro.activeWords_fix s 2140 32 (by decide) (by norm_num) hact
  have ha2208 : (2208 : W).toNat = 2208 := rfl
  have hf2208 := Monpro.activeWords_fix s 2208 32 (by decide) (by norm_num) hact
  simp [hz,hzn,part1Program,part1Model,runInstructions,runInstr,List.exchange,succ_ofNat_mod,ofNat_add_mod,Nat.add_assoc,State.activeWordsAfterUInt256,literal_eq_ofNat,capacity,ha2140,hf2140,ha2208,hf2208]
def part2Program : List Instr := [.op (.Dup dA4),.op .AND,.op (.Swap sA3),.op .AND]
def part2Model (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 w20 w21 w22 w23 w24 w25 w26 w27 w28 w29 : W) (rest : List W) : State :=
  let v0 : W := UInt256.land w4 w0
  let v1 : W := UInt256.land w4 w1
  {s with pc := N 8811,memory := s.memory,stack := v1::w2::w3::v0::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::w16::w17::w18::w19::w20::w21::w22::w23::w24::w25::w26::w27::w28::w29::rest}
theorem part2_run (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 w20 w21 w22 w23 w24 w25 w26 w27 w28 w29 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions part2Program {s with pc := N 8807,memory := s.memory,stack := w0::w1::w2::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::w16::w17::w18::w19::w20::w21::w22::w23::w24::w25::w26::w27::w28::w29::rest} = some (part2Model s w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 w20 w21 w22 w23 w24 w25 w26 w27 w28 w29 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 63) : rest.length+j < 1024 := by omega
  simp [hz,hzn,part2Program,part2Model,runInstructions,runInstr,List.exchange,succ_ofNat_mod,ofNat_add_mod,Nat.add_assoc,State.activeWordsAfterUInt256,literal_eq_ofNat,capacity]
def program : List Instr := (part0Program++(part1Program++part2Program))
def model (s : State) (f0 f1 f2 f3 f4 f5 f6 cached f7 f8 f9 f10 f11 f12 f13 f14 f15 f16 f17 f18 f19 f20 f21 f22 f23 : W) (rest : List W) : State :=
  let v0 : W := MachineState.readWord (s.memory) 224
  let v1 : W := MachineState.readWord (s.memory) 2170
  let v2 : W := UInt256.land v0 v1
  let v3 : W := MachineState.readWord (s.memory) 2200
  let v4 : W := UInt256.land v0 v3
  let v5 : W := MachineState.readWord (s.memory) 2208
  let v6 : W := UInt256.shiftLeft v5 (N 176)
  let v7 : W := MachineState.readWord (s.memory) 2140
  let v8 : W := UInt256.land v0 v7
  let v9 : W := UInt256.land v0 v6
  {s with pc := N 8811,memory := s.memory,stack := v9::v4::v2::v8::f0::f1::f2::f3::f4::f5::f6::(cached)::f7::f8::f9::f10::f11::f12::f13::f14::f15::f16::f17::f18::f19::f20::f21::f22::f23::rest}
theorem run (s : State) (f0 f1 f2 f3 f4 f5 f6 cached f7 f8 f9 f10 f11 f12 f13 f14 f15 f16 f17 f18 f19 f20 f21 f22 f23 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions program {s with pc := N 8781,memory := s.memory,stack := f0::f1::f2::f3::f4::f5::f6::(cached)::f7::f8::f9::f10::f11::f12::f13::f14::f15::f16::f17::f18::f19::f20::f21::f22::f23::rest} = some (model s f0 f1 f2 f3 f4 f5 f6 cached f7 f8 f9 f10 f11 f12 f13 f14 f15 f16 f17 f18 f19 f20 f21 f22 f23 rest) := by
  let v0 : W := MachineState.readWord (s.memory) 224
  let v1 : W := MachineState.readWord (s.memory) 2170
  let v2 : W := UInt256.land v0 v1
  let v3 : W := MachineState.readWord (s.memory) 2200
  let v4 : W := UInt256.land v0 v3
  let v5 : W := MachineState.readWord (s.memory) 2208
  let v6 : W := UInt256.shiftLeft v5 (N 176)
  let v7 : W := MachineState.readWord (s.memory) 2140
  let v8 : W := UInt256.land v0 v7
  let v9 : W := UInt256.land v0 v6
  have h0 : runInstructions part0Program {s with pc := N 8781,memory := s.memory,stack := f0::f1::f2::f3::f4::f5::f6::(cached)::f7::f8::f9::f10::f11::f12::f13::f14::f15::f16::f17::f18::f19::f20::f21::f22::f23::rest} = some {s with pc := N 8794,memory := s.memory,stack := v3::v2::v0::f0::f1::f2::f3::f4::f5::f6::(cached)::f7::f8::f9::f10::f11::f12::f13::f14::f15::f16::f17::f18::f19::f20::f21::f22::f23::rest} := by
    simpa only [part0Model,v0,v1,v2,v3] using part0_run ({s with memory := s.memory}) f0 f1 f2 f3 f4 f5 f6 (cached) f7 f8 f9 f10 f11 f12 f13 f14 f15 f16 f17 f18 f19 f20 f21 f22 f23 rest hcap hact
  have h1 : runInstructions part1Program {s with pc := N 8794,memory := s.memory,stack := v3::v2::v0::f0::f1::f2::f3::f4::f5::f6::(cached)::f7::f8::f9::f10::f11::f12::f13::f14::f15::f16::f17::f18::f19::f20::f21::f22::f23::rest} = some {s with pc := N 8807,memory := s.memory,stack := v7::v6::v4::v2::v0::f0::f1::f2::f3::f4::f5::f6::(cached)::f7::f8::f9::f10::f11::f12::f13::f14::f15::f16::f17::f18::f19::f20::f21::f22::f23::rest} := by
    simpa only [part1Model,v4,v5,v6,v7] using part1_run ({s with memory := s.memory}) v3 v2 v0 f0 f1 f2 f3 f4 f5 f6 (cached) f7 f8 f9 f10 f11 f12 f13 f14 f15 f16 f17 f18 f19 f20 f21 f22 f23 rest hcap hact
  have h2 : runInstructions part2Program {s with pc := N 8807,memory := s.memory,stack := v7::v6::v4::v2::v0::f0::f1::f2::f3::f4::f5::f6::(cached)::f7::f8::f9::f10::f11::f12::f13::f14::f15::f16::f17::f18::f19::f20::f21::f22::f23::rest} = some {s with pc := N 8811,memory := s.memory,stack := v9::v4::v2::v8::f0::f1::f2::f3::f4::f5::f6::(cached)::f7::f8::f9::f10::f11::f12::f13::f14::f15::f16::f17::f18::f19::f20::f21::f22::f23::rest} := by
    simpa only [part2Model,v8,v9] using part2_run ({s with memory := s.memory}) v7 v6 v4 v2 v0 f0 f1 f2 f3 f4 f5 f6 (cached) f7 f8 f9 f10 f11 f12 f13 f14 f15 f16 f17 f18 f19 f20 f21 f22 f23 rest hcap hact
  exact (runInstructions_append_some _ _ _ _ _ h0 (runInstructions_append_some _ _ _ _ _ h1 h2))
end R5CachedSuffix
namespace R5CachedSuffix
theorem result_run (s : State) (f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 f16 f17 f18 f19 f20 f21 f22 f23 cached : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions program {s with pc := N 8781,stack := f0::f1::f2::f3::f4::f5::f6::cached::f7::f8::f9::f10::f11::f12::f13::f14::f15::f16::f17::f18::f19::f20::f21::f22::f23::rest} =
      some {s with pc := N 8811,memory := s.memory,stack := (CycleSubmission.R5.ExecPrologue.blk5467_o0 s.memory f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 f16 f17 f18 f19 f20 f21 f22 f23)::(CycleSubmission.R5.ExecPrologue.blk5467_o1 s.memory f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 f16 f17 f18 f19 f20 f21 f22 f23)::(CycleSubmission.R5.ExecPrologue.blk5467_o2 s.memory f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 f16 f17 f18 f19 f20 f21 f22 f23)::(CycleSubmission.R5.ExecPrologue.blk5467_o3 s.memory f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 f16 f17 f18 f19 f20 f21 f22 f23)::f0::f1::f2::f3::f4::f5::f6::cached::f7::f8::f9::f10::f11::f12::f13::f14::f15::f16::f17::f18::f19::f20::f21::f22::f23::rest} := by
  simpa only [model,CycleSubmission.R5.ExecPrologue.blk5467_o0,CycleSubmission.R5.ExecPrologue.blk5467_o1,CycleSubmission.R5.ExecPrologue.blk5467_o2,CycleSubmission.R5.ExecPrologue.blk5467_o3] using
    run s f0 f1 f2 f3 f4 f5 f6 cached f7 f8 f9 f10 f11 f12 f13 f14 f15 f16 f17 f18 f19 f20 f21 f22 f23 rest hcap hact
#print axioms result_run
end R5CachedSuffix
