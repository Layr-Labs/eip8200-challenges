import Challenge.Modexp.Submission.Proofs.Prepared.StackArgs
import Challenge.Modexp.Submission.Proofs.Prepared.Arithmetic
import Challenge.Modexp.Submission.Proofs.Cycle.DoubleInput
import Challenge.Modexp.Submission.Proofs.Fast.Monpro
import Challenge.Modexp.Submission.Proofs.Bytecode.WindowNibbleDefs
import Challenge.Modexp.Submission.Proofs.R5.ExecSquare
open CycleSubmission.SharedStackArgs
set_option maxRecDepth 40000
set_option maxHeartbeats 8000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
namespace R5LimbCacheRaw
open EvmSemantics EvmSemantics.EVM YulEvmCompiler
open Challenge.EvmProof.Word Challenge.EvmProof.Stepper
open CycleSubmission.Prepared.Arithmetic
open Challenge.Modexp.Submission.Proofs.Bytecode.WindowNibbleKernel
open Challenge.Modexp.Submission.Proofs.Fast
local notation "W" => UInt256
local notation "N" => UInt256.ofNat
def stage0Part0Program : List Instr :=
  [.op .JUMPDEST,
   .op (.Dup dA0),
   .op (.Dup dA0),
   .op .MUL,
   .op (.Dup dA11),
   .op .MUL,
   .push 1 16,
   .op .SHR]
def stage0Part0Model (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 : W) (rest : List W) : State :=
  let v0 : W := w0 * w0
  let v1 : W := w10 * v0
  let v2 : W := UInt256.shiftRight v1 (N 16)
  {s with pc := N 8652,memory := s.memory,stack := v2::w0::w1::w2::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::rest}
theorem stage0Part0_run (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions stage0Part0Program {s with pc := N 8643,memory := s.memory,stack := w0::w1::w2::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::rest} = some (stage0Part0Model s w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 63) : rest.length+j < 1024 := by omega
  simp [hz,hzn,stage0Part0Program,stage0Part0Model,runInstructions,runInstr,List.exchange,succ_ofNat_mod,ofNat_add_mod,Nat.add_assoc,State.activeWordsAfterUInt256,literal_eq_ofNat,capacity]
def stage0Part1Program : List Instr :=
  [.op (.Dup dA10),
   .op (.Dup dA11),
   .op (.Dup dA3),
   .op (.Dup dA0),
   .op (.Dup dA0),
   .op .ADD,
   .op (.Swap sA4),
   .op .MULMOD]
def stage0Part1Model (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 : W) (rest : List W) : State :=
  let v0 : W := w1 + w1
  let v1 : W := UInt256.mulMod w1 w1 w10
  {s with pc := N 8660,memory := s.memory,stack := v1::w10::w0::v0::w2::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::rest}
theorem stage0Part1_run (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions stage0Part1Program {s with pc := N 8652,memory := s.memory,stack := w0::w1::w2::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::rest} = some (stage0Part1Model s w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 63) : rest.length+j < 1024 := by omega
  simp [hz,hzn,stage0Part1Program,stage0Part1Model,runInstructions,runInstr,List.exchange,succ_ofNat_mod,ofNat_add_mod,Nat.add_assoc,State.activeWordsAfterUInt256,literal_eq_ofNat,capacity]
def stage0Part2Program : List Instr :=
  [.op (.Dup dA12),
   .op (.Dup dA15),
   .op (.Dup dA4),
   .op .MULMOD,
   .op .ADD,
   .push 2 2048,
   .op .MULMOD]
def stage0Part2Model (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 : W) (rest : List W) : State :=
  let v0 : W := UInt256.mulMod w2 w14 w12
  let v1 : W := v0 + w0
  let v2 : W := UInt256.mulMod (N 2048) v1 w1
  {s with pc := N 8669,memory := s.memory,stack := v2::w2::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::rest}
theorem stage0Part2_run (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions stage0Part2Program {s with pc := N 8660,memory := s.memory,stack := w0::w1::w2::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::rest} = some (stage0Part2Model s w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 63) : rest.length+j < 1024 := by omega
  simp [hz,hzn,stage0Part2Program,stage0Part2Model,runInstructions,runInstr,List.exchange,succ_ofNat_mod,ofNat_add_mod,Nat.add_assoc,State.activeWordsAfterUInt256,literal_eq_ofNat,capacity]
def stage0Program : List Instr := (stage0Part0Program++(stage0Part1Program++stage0Part2Program))
def stage0Model (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 : W) (rest : List W) : State :=
  let v0 : W := w0 * w0
  let v1 : W := w10 * v0
  let v2 : W := UInt256.shiftRight v1 (N 16)
  let v3 : W := w0 + w0
  let v4 : W := UInt256.mulMod w0 w0 w9
  let v5 : W := UInt256.mulMod v2 w11 w9
  let v6 : W := v5 + v4
  let v7 : W := UInt256.mulMod (N 2048) v6 w9
  {s with pc := N 8669,memory := s.memory,stack := v7::v2::v3::w1::w2::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::rest}
theorem stage0_run (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions stage0Program {s with pc := N 8643,memory := s.memory,stack := w0::w1::w2::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::rest} = some (stage0Model s w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 rest) := by
  let v0 : W := w0 * w0
  let v1 : W := w10 * v0
  let v2 : W := UInt256.shiftRight v1 (N 16)
  let v3 : W := w0 + w0
  let v4 : W := UInt256.mulMod w0 w0 w9
  let v5 : W := UInt256.mulMod v2 w11 w9
  let v6 : W := v5 + v4
  let v7 : W := UInt256.mulMod (N 2048) v6 w9
  have h0 : runInstructions stage0Part0Program {s with pc := N 8643,memory := s.memory,stack := w0::w1::w2::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::rest} = some {s with pc := N 8652,memory := s.memory,stack := v2::w0::w1::w2::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::rest} := by
    simpa only [stage0Part0Model,v0,v1,v2] using stage0Part0_run ({s with memory := s.memory}) w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 rest hcap hact
  have h1 : runInstructions stage0Part1Program {s with pc := N 8652,memory := s.memory,stack := v2::w0::w1::w2::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::rest} = some {s with pc := N 8660,memory := s.memory,stack := v4::w9::v2::v3::w1::w2::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::rest} := by
    simpa only [stage0Part1Model,v3,v4] using stage0Part1_run ({s with memory := s.memory}) v2 w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 rest hcap hact
  have h2 : runInstructions stage0Part2Program {s with pc := N 8660,memory := s.memory,stack := v4::w9::v2::v3::w1::w2::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::rest} = some {s with pc := N 8669,memory := s.memory,stack := v7::v2::v3::w1::w2::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::rest} := by
    simpa only [stage0Part2Model,v5,v6,v7] using stage0Part2_run ({s with memory := s.memory}) v4 w9 v2 v3 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 rest hcap hact
  exact (runInstructions_append_some _ _ _ _ _ h0 (runInstructions_append_some _ _ _ _ _ h1 h2))
def stage1Part0Program : List Instr :=
  [.op (.Dup dA0),
   .op (.Dup dA4),
   .op (.Dup dA4),
   .op .MUL,
   .op .ADD,
   .op (.Dup dA8),
   .op (.Dup dA3),
   .op .MUL]
def stage1Part0Model (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 : W) (rest : List W) : State :=
  let v0 : W := w2 * w3
  let v1 : W := v0 + w0
  let v2 : W := w1 * w7
  {s with pc := N 8677,memory := s.memory,stack := v2::v1::w0::w1::w2::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::rest}
theorem stage1Part0_run (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions stage1Part0Program {s with pc := N 8669,memory := s.memory,stack := w0::w1::w2::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::rest} = some (stage1Part0Model s w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 63) : rest.length+j < 1024 := by omega
  simp [hz,hzn,stage1Part0Program,stage1Part0Model,runInstructions,runInstr,List.exchange,succ_ofNat_mod,ofNat_add_mod,Nat.add_assoc,State.activeWordsAfterUInt256,literal_eq_ofNat,capacity]
def stage1Part1Program : List Instr :=
  [.op .ADD,
   .op (.Dup dA13),
   .op .MUL,
   .push 1 16,
   .op .SHR,
   .op (.Swap sA0),
   .op (.Dup dA12),
   .op (.Dup dA5)]
def stage1Part1Model (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 : W) (rest : List W) : State :=
  let v0 : W := w0 + w1
  let v1 : W := w14 * v0
  let v2 : W := UInt256.shiftRight v1 (N 16)
  {s with pc := N 8686,memory := s.memory,stack := w5::w13::w2::v2::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::w16::rest}
theorem stage1Part1_run (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions stage1Part1Program {s with pc := N 8677,memory := s.memory,stack := w0::w1::w2::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::w16::rest} = some (stage1Part1Model s w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 63) : rest.length+j < 1024 := by omega
  simp [hz,hzn,stage1Part1Program,stage1Part1Model,runInstructions,runInstr,List.exchange,succ_ofNat_mod,ofNat_add_mod,Nat.add_assoc,State.activeWordsAfterUInt256,literal_eq_ofNat,capacity]
def stage1Part2Program : List Instr :=
  [.op (.Dup dA5),
   .op .MULMOD,
   .op .ADD,
   .op (.Dup dA12),
   .op (.Dup dA9),
   .op (.Dup dA4),
   .op .MULMOD,
   .op .ADD]
def stage1Part2Model (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 : W) (rest : List W) : State :=
  let v0 : W := UInt256.mulMod w5 w0 w1
  let v1 : W := v0 + w2
  let v2 : W := UInt256.mulMod w4 w10 w14
  let v3 : W := v2 + v1
  {s with pc := N 8694,memory := s.memory,stack := v3::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::w16::w17::rest}
theorem stage1Part2_run (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions stage1Part2Program {s with pc := N 8686,memory := s.memory,stack := w0::w1::w2::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::w16::w17::rest} = some (stage1Part2Model s w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 63) : rest.length+j < 1024 := by omega
  simp [hz,hzn,stage1Part2Program,stage1Part2Model,runInstructions,runInstr,List.exchange,succ_ofNat_mod,ofNat_add_mod,Nat.add_assoc,State.activeWordsAfterUInt256,literal_eq_ofNat,capacity]
def stage1Part3Program : List Instr :=
  [.op (.Dup dA12),
   .op (.Dup dA15),
   .op (.Dup dA3),
   .op .MULMOD,
   .op .ADD,
   .op (.Dup dA12),
   .op (.Swap sA0)]
def stage1Part3Model (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 : W) (rest : List W) : State :=
  let v0 : W := UInt256.mulMod w1 w14 w12
  let v1 : W := v0 + w0
  {s with pc := N 8701,memory := s.memory,stack := v1::w12::w1::w2::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::rest}
theorem stage1Part3_run (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions stage1Part3Program {s with pc := N 8694,memory := s.memory,stack := w0::w1::w2::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::rest} = some (stage1Part3Model s w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 63) : rest.length+j < 1024 := by omega
  simp [hz,hzn,stage1Part3Program,stage1Part3Model,runInstructions,runInstr,List.exchange,succ_ofNat_mod,ofNat_add_mod,Nat.add_assoc,State.activeWordsAfterUInt256,literal_eq_ofNat,capacity]
def stage1Part4Program : List Instr :=
  [.push 2 2048,
   .op .MULMOD]
def stage1Part4Model (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 : W) (rest : List W) : State :=
  let v0 : W := UInt256.mulMod (N 2048) w0 w1
  {s with pc := N 8705,memory := s.memory,stack := v0::w2::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::w16::rest}
theorem stage1Part4_run (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions stage1Part4Program {s with pc := N 8701,memory := s.memory,stack := w0::w1::w2::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::w16::rest} = some (stage1Part4Model s w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 63) : rest.length+j < 1024 := by omega
  simp [hz,hzn,stage1Part4Program,stage1Part4Model,runInstructions,runInstr,List.exchange,succ_ofNat_mod,ofNat_add_mod,Nat.add_assoc,State.activeWordsAfterUInt256,literal_eq_ofNat,capacity]
def stage1Program : List Instr := (stage1Part0Program++(stage1Part1Program++(stage1Part2Program++(stage1Part3Program++stage1Part4Program))))
def stage1Model (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 : W) (rest : List W) : State :=
  let v0 : W := w2 * w3
  let v1 : W := v0 + w0
  let v2 : W := w1 * w7
  let v3 : W := v2 + v1
  let v4 : W := w12 * v3
  let v5 : W := UInt256.shiftRight v4 (N 16)
  let v6 : W := UInt256.mulMod w2 w3 w11
  let v7 : W := v6 + w0
  let v8 : W := UInt256.mulMod w1 w7 w11
  let v9 : W := v8 + v7
  let v10 : W := UInt256.mulMod v5 w13 w11
  let v11 : W := v10 + v9
  let v12 : W := UInt256.mulMod (N 2048) v11 w11
  {s with pc := N 8705,memory := s.memory,stack := v12::v5::w1::w2::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::rest}
theorem stage1_run (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions stage1Program {s with pc := N 8669,memory := s.memory,stack := w0::w1::w2::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::rest} = some (stage1Model s w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 rest) := by
  let v0 : W := w2 * w3
  let v1 : W := v0 + w0
  let v2 : W := w1 * w7
  let v3 : W := v2 + v1
  let v4 : W := w12 * v3
  let v5 : W := UInt256.shiftRight v4 (N 16)
  let v6 : W := UInt256.mulMod w2 w3 w11
  let v7 : W := v6 + w0
  let v8 : W := UInt256.mulMod w1 w7 w11
  let v9 : W := v8 + v7
  let v10 : W := UInt256.mulMod v5 w13 w11
  let v11 : W := v10 + v9
  let v12 : W := UInt256.mulMod (N 2048) v11 w11
  have h0 : runInstructions stage1Part0Program {s with pc := N 8669,memory := s.memory,stack := w0::w1::w2::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::rest} = some {s with pc := N 8677,memory := s.memory,stack := v2::v1::w0::w1::w2::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::rest} := by
    simpa only [stage1Part0Model,v0,v1,v2] using stage1Part0_run ({s with memory := s.memory}) w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 rest hcap hact
  have h1 : runInstructions stage1Part1Program {s with pc := N 8677,memory := s.memory,stack := v2::v1::w0::w1::w2::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::rest} = some {s with pc := N 8686,memory := s.memory,stack := w3::w11::w0::v5::w1::w2::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::rest} := by
    simpa only [stage1Part1Model,v3,v4,v5] using stage1Part1_run ({s with memory := s.memory}) v2 v1 w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 rest hcap hact
  have h2 : runInstructions stage1Part2Program {s with pc := N 8686,memory := s.memory,stack := w3::w11::w0::v5::w1::w2::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::rest} = some {s with pc := N 8694,memory := s.memory,stack := v9::v5::w1::w2::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::rest} := by
    simpa only [stage1Part2Model,v6,v7,v8,v9] using stage1Part2_run ({s with memory := s.memory}) w3 w11 w0 v5 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 rest hcap hact
  have h3 : runInstructions stage1Part3Program {s with pc := N 8694,memory := s.memory,stack := v9::v5::w1::w2::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::rest} = some {s with pc := N 8701,memory := s.memory,stack := v11::w11::v5::w1::w2::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::rest} := by
    simpa only [stage1Part3Model,v10,v11] using stage1Part3_run ({s with memory := s.memory}) v9 v5 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 rest hcap hact
  have h4 : runInstructions stage1Part4Program {s with pc := N 8701,memory := s.memory,stack := v11::w11::v5::w1::w2::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::rest} = some {s with pc := N 8705,memory := s.memory,stack := v12::v5::w1::w2::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::rest} := by
    simpa only [stage1Part4Model,v12] using stage1Part4_run ({s with memory := s.memory}) v11 w11 v5 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 rest hcap hact
  exact (runInstructions_append_some _ _ _ _ _ h0 (runInstructions_append_some _ _ _ _ _ h1 (runInstructions_append_some _ _ _ _ _ h2 (runInstructions_append_some _ _ _ _ _ h3 h4))))
def stage2Part0Program : List Instr :=
  [.op (.Dup dA0),
   .op (.Dup dA6),
   .op (.Dup dA5),
   .op .MUL,
   .op .ADD,
   .op (.Dup dA5),
   .op (.Dup dA0),
   .op .MUL]
def stage2Part0Model (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 : W) (rest : List W) : State :=
  let v0 : W := w3 * w5
  let v1 : W := v0 + w0
  let v2 : W := w4 * w4
  {s with pc := N 8713,memory := s.memory,stack := v2::v1::w0::w1::w2::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::rest}
theorem stage2Part0_run (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions stage2Part0Program {s with pc := N 8705,memory := s.memory,stack := w0::w1::w2::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::rest} = some (stage2Part0Model s w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 63) : rest.length+j < 1024 := by omega
  simp [hz,hzn,stage2Part0Program,stage2Part0Model,runInstructions,runInstr,List.exchange,succ_ofNat_mod,ofNat_add_mod,Nat.add_assoc,State.activeWordsAfterUInt256,literal_eq_ofNat,capacity]
def stage2Part1Program : List Instr :=
  [.op .ADD,
   .op (.Dup dA10),
   .op (.Dup dA4),
   .op .MUL,
   .op .ADD,
   .op (.Dup dA9),
   .op (.Dup dA3),
   .op .MUL]
def stage2Part1Model (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 : W) (rest : List W) : State :=
  let v0 : W := w0 + w1
  let v1 : W := w4 * w11
  let v2 : W := v1 + v0
  let v3 : W := w3 * w10
  {s with pc := N 8721,memory := s.memory,stack := v3::v2::w2::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::w16::w17::rest}
theorem stage2Part1_run (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions stage2Part1Program {s with pc := N 8713,memory := s.memory,stack := w0::w1::w2::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::w16::w17::rest} = some (stage2Part1Model s w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 63) : rest.length+j < 1024 := by omega
  simp [hz,hzn,stage2Part1Program,stage2Part1Model,runInstructions,runInstr,List.exchange,succ_ofNat_mod,ofNat_add_mod,Nat.add_assoc,State.activeWordsAfterUInt256,literal_eq_ofNat,capacity]
def stage2Part2Program : List Instr :=
  [.op .ADD,
   .op (.Dup dA14),
   .op .MUL,
   .push 1 16,
   .op .SHR,
   .op (.Swap sA0),
   .op (.Dup dA13),
   .op (.Dup dA7)]
def stage2Part2Model (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 : W) (rest : List W) : State :=
  let v0 : W := w0 + w1
  let v1 : W := w15 * v0
  let v2 : W := UInt256.shiftRight v1 (N 16)
  {s with pc := N 8730,memory := s.memory,stack := w7::w14::w2::v2::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::w16::w17::rest}
theorem stage2Part2_run (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions stage2Part2Program {s with pc := N 8721,memory := s.memory,stack := w0::w1::w2::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::w16::w17::rest} = some (stage2Part2Model s w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 63) : rest.length+j < 1024 := by omega
  simp [hz,hzn,stage2Part2Program,stage2Part2Model,runInstructions,runInstr,List.exchange,succ_ofNat_mod,ofNat_add_mod,Nat.add_assoc,State.activeWordsAfterUInt256,literal_eq_ofNat,capacity]
def stage2Part3Program : List Instr :=
  [.op (.Dup dA6),
   .op .MULMOD,
   .op .ADD,
   .op (.Dup dA13),
   .op (.Dup dA6),
   .op (.Dup dA0),
   .op (.Dup dA0),
   .op .ADD]
def stage2Part3Model (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 : W) (rest : List W) : State :=
  let v0 : W := UInt256.mulMod w6 w0 w1
  let v1 : W := v0 + w2
  let v2 : W := w7 + w7
  {s with pc := N 8738,memory := s.memory,stack := v2::w7::w15::v1::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::w16::w17::w18::rest}
theorem stage2Part3_run (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions stage2Part3Program {s with pc := N 8730,memory := s.memory,stack := w0::w1::w2::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::w16::w17::w18::rest} = some (stage2Part3Model s w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 63) : rest.length+j < 1024 := by omega
  simp [hz,hzn,stage2Part3Program,stage2Part3Model,runInstructions,runInstr,List.exchange,succ_ofNat_mod,ofNat_add_mod,Nat.add_assoc,State.activeWordsAfterUInt256,literal_eq_ofNat,capacity]
def stage2Part4Program : List Instr :=
  [.op (.Swap sA7),
   .op .MULMOD,
   .op .ADD,
   .op (.Dup dA13),
   .op (.Dup dA11),
   .op (.Dup dA5),
   .op .MULMOD,
   .op .ADD]
def stage2Part4Model (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 : W) (rest : List W) : State :=
  let v0 : W := UInt256.mulMod w8 w1 w2
  let v1 : W := v0 + w3
  let v2 : W := UInt256.mulMod w6 w13 w16
  let v3 : W := v2 + v1
  {s with pc := N 8746,memory := s.memory,stack := v3::w4::w5::w6::w7::w0::w9::w10::w11::w12::w13::w14::w15::w16::w17::w18::w19::rest}
theorem stage2Part4_run (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions stage2Part4Program {s with pc := N 8738,memory := s.memory,stack := w0::w1::w2::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::w16::w17::w18::w19::rest} = some (stage2Part4Model s w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 63) : rest.length+j < 1024 := by omega
  simp [hz,hzn,stage2Part4Program,stage2Part4Model,runInstructions,runInstr,List.exchange,succ_ofNat_mod,ofNat_add_mod,Nat.add_assoc,State.activeWordsAfterUInt256,literal_eq_ofNat,capacity]
def stage2Part5Program : List Instr :=
  [.op (.Dup dA13),
   .op (.Dup dA10),
   .op (.Dup dA4),
   .op .MULMOD,
   .op .ADD,
   .op (.Dup dA13),
   .push 1 160,
   .op .MLOAD]
def stage2Part5Model (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 : W) (rest : List W) : State :=
  let v0 : W := UInt256.mulMod w2 w9 w13
  let v1 : W := v0 + w0
  let v2 : W := MachineState.readWord (s.memory) 160
  {s with pc := N 8755,memory := s.memory,stack := v2::w13::v1::w1::w2::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::w16::rest}
theorem stage2Part5_run (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions stage2Part5Program {s with pc := N 8746,memory := s.memory,stack := w0::w1::w2::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::w16::rest} = some (stage2Part5Model s w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 63) : rest.length+j < 1024 := by omega
  have ha160 : (160 : W).toNat = 160 := rfl
  have hf160 := Monpro.activeWords_fix s 160 32 (by decide) (by norm_num) hact
  simp [hz,hzn,stage2Part5Program,stage2Part5Model,runInstructions,runInstr,List.exchange,succ_ofNat_mod,ofNat_add_mod,Nat.add_assoc,State.activeWordsAfterUInt256,literal_eq_ofNat,capacity,ha160,hf160]
def stage2Part6Program : List Instr :=
  [.op (.Dup dA3),
   .op .MULMOD,
   .op .ADD,
   .op (.Dup dA13),
   .op (.Swap sA0),
   .push 2 2048,
   .op .MULMOD]
def stage2Part6Model (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 : W) (rest : List W) : State :=
  let v0 : W := UInt256.mulMod w3 w0 w1
  let v1 : W := v0 + w2
  let v2 : W := UInt256.mulMod (N 2048) v1 w15
  {s with pc := N 8764,memory := s.memory,stack := v2::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::w16::w17::w18::rest}
theorem stage2Part6_run (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions stage2Part6Program {s with pc := N 8755,memory := s.memory,stack := w0::w1::w2::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::w16::w17::w18::rest} = some (stage2Part6Model s w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 63) : rest.length+j < 1024 := by omega
  simp [hz,hzn,stage2Part6Program,stage2Part6Model,runInstructions,runInstr,List.exchange,succ_ofNat_mod,ofNat_add_mod,Nat.add_assoc,State.activeWordsAfterUInt256,literal_eq_ofNat,capacity]
def stage2Program : List Instr := (stage2Part0Program++(stage2Part1Program++(stage2Part2Program++(stage2Part3Program++(stage2Part4Program++(stage2Part5Program++stage2Part6Program))))))
def stage2Model (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 : W) (rest : List W) : State :=
  let v0 : W := w3 * w5
  let v1 : W := v0 + w0
  let v2 : W := w4 * w4
  let v3 : W := v2 + v1
  let v4 : W := w2 * w9
  let v5 : W := v4 + v3
  let v6 : W := w1 * w8
  let v7 : W := v6 + v5
  let v8 : W := w13 * v7
  let v9 : W := UInt256.shiftRight v8 (N 16)
  let v10 : W := UInt256.mulMod w3 w5 w12
  let v11 : W := v10 + w0
  let v12 : W := w4 + w4
  let v13 : W := UInt256.mulMod w4 w4 w12
  let v14 : W := v13 + v11
  let v15 : W := UInt256.mulMod w2 w9 w12
  let v16 : W := v15 + v14
  let v17 : W := UInt256.mulMod w1 w8 w12
  let v18 : W := v17 + v16
  let v19 : W := MachineState.readWord (s.memory) 160
  let v20 : W := UInt256.mulMod v9 v19 w12
  let v21 : W := v20 + v18
  let v22 : W := UInt256.mulMod (N 2048) v21 w12
  {s with pc := N 8764,memory := s.memory,stack := v22::v9::w1::w2::w3::v12::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::rest}
theorem stage2_run (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions stage2Program {s with pc := N 8705,memory := s.memory,stack := w0::w1::w2::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::rest} = some (stage2Model s w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 rest) := by
  let v0 : W := w3 * w5
  let v1 : W := v0 + w0
  let v2 : W := w4 * w4
  let v3 : W := v2 + v1
  let v4 : W := w2 * w9
  let v5 : W := v4 + v3
  let v6 : W := w1 * w8
  let v7 : W := v6 + v5
  let v8 : W := w13 * v7
  let v9 : W := UInt256.shiftRight v8 (N 16)
  let v10 : W := UInt256.mulMod w3 w5 w12
  let v11 : W := v10 + w0
  let v12 : W := w4 + w4
  let v13 : W := UInt256.mulMod w4 w4 w12
  let v14 : W := v13 + v11
  let v15 : W := UInt256.mulMod w2 w9 w12
  let v16 : W := v15 + v14
  let v17 : W := UInt256.mulMod w1 w8 w12
  let v18 : W := v17 + v16
  let v19 : W := MachineState.readWord (s.memory) 160
  let v20 : W := UInt256.mulMod v9 v19 w12
  let v21 : W := v20 + v18
  let v22 : W := UInt256.mulMod (N 2048) v21 w12
  have h0 : runInstructions stage2Part0Program {s with pc := N 8705,memory := s.memory,stack := w0::w1::w2::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::rest} = some {s with pc := N 8713,memory := s.memory,stack := v2::v1::w0::w1::w2::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::rest} := by
    simpa only [stage2Part0Model,v0,v1,v2] using stage2Part0_run ({s with memory := s.memory}) w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 rest hcap hact
  have h1 : runInstructions stage2Part1Program {s with pc := N 8713,memory := s.memory,stack := v2::v1::w0::w1::w2::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::rest} = some {s with pc := N 8721,memory := s.memory,stack := v6::v5::w0::w1::w2::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::rest} := by
    simpa only [stage2Part1Model,v3,v4,v5,v6] using stage2Part1_run ({s with memory := s.memory}) v2 v1 w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 rest hcap hact
  have h2 : runInstructions stage2Part2Program {s with pc := N 8721,memory := s.memory,stack := v6::v5::w0::w1::w2::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::rest} = some {s with pc := N 8730,memory := s.memory,stack := w5::w12::w0::v9::w1::w2::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::rest} := by
    simpa only [stage2Part2Model,v7,v8,v9] using stage2Part2_run ({s with memory := s.memory}) v6 v5 w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 rest hcap hact
  have h3 : runInstructions stage2Part3Program {s with pc := N 8730,memory := s.memory,stack := w5::w12::w0::v9::w1::w2::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::rest} = some {s with pc := N 8738,memory := s.memory,stack := v12::w4::w12::v11::v9::w1::w2::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::rest} := by
    simpa only [stage2Part3Model,v10,v11,v12] using stage2Part3_run ({s with memory := s.memory}) w5 w12 w0 v9 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 rest hcap hact
  have h4 : runInstructions stage2Part4Program {s with pc := N 8738,memory := s.memory,stack := v12::w4::w12::v11::v9::w1::w2::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::rest} = some {s with pc := N 8746,memory := s.memory,stack := v16::v9::w1::w2::w3::v12::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::rest} := by
    simpa only [stage2Part4Model,v13,v14,v15,v16] using stage2Part4_run ({s with memory := s.memory}) v12 w4 w12 v11 v9 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 rest hcap hact
  have h5 : runInstructions stage2Part5Program {s with pc := N 8746,memory := s.memory,stack := v16::v9::w1::w2::w3::v12::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::rest} = some {s with pc := N 8755,memory := s.memory,stack := v19::w12::v18::v9::w1::w2::w3::v12::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::rest} := by
    simpa only [stage2Part5Model,v17,v18,v19] using stage2Part5_run ({s with memory := s.memory}) v16 v9 w1 w2 w3 v12 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 rest hcap hact
  have h6 : runInstructions stage2Part6Program {s with pc := N 8755,memory := s.memory,stack := v19::w12::v18::v9::w1::w2::w3::v12::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::rest} = some {s with pc := N 8764,memory := s.memory,stack := v22::v9::w1::w2::w3::v12::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::rest} := by
    simpa only [stage2Part6Model,v20,v21,v22] using stage2Part6_run ({s with memory := s.memory}) v19 w12 v18 v9 w1 w2 w3 v12 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 rest hcap hact
  exact (runInstructions_append_some _ _ _ _ _ h0 (runInstructions_append_some _ _ _ _ _ h1 (runInstructions_append_some _ _ _ _ _ h2 (runInstructions_append_some _ _ _ _ _ h3 (runInstructions_append_some _ _ _ _ _ h4 (runInstructions_append_some _ _ _ _ _ h5 h6))))))
def stage3Part0Program : List Instr :=
  [.op (.Dup dA0),
   .op (.Dup dA8),
   .op (.Dup dA6),
   .op .MUL,
   .op (.Dup dA8),
   .op (.Dup dA8),
   .op .MUL,
   .op .ADD]
def stage3Part0Model (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 : W) (rest : List W) : State :=
  let v0 : W := w4 * w7
  let v1 : W := w5 * w6
  let v2 : W := v1 + v0
  {s with pc := N 8772,memory := s.memory,stack := v2::w0::w0::w1::w2::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::w16::rest}
theorem stage3Part0_run (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions stage3Part0Program {s with pc := N 8764,memory := s.memory,stack := w0::w1::w2::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::w16::rest} = some (stage3Part0Model s w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 63) : rest.length+j < 1024 := by omega
  simp [hz,hzn,stage3Part0Program,stage3Part0Model,runInstructions,runInstr,List.exchange,succ_ofNat_mod,ofNat_add_mod,Nat.add_assoc,State.activeWordsAfterUInt256,literal_eq_ofNat,capacity]
def stage3Part1Program : List Instr :=
  [.op .ADD,
   .op (.Dup dA12),
   .op (.Dup dA5),
   .op .MUL,
   .op .ADD,
   .op (.Dup dA11),
   .op (.Dup dA4),
   .op .MUL]
def stage3Part1Model (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 : W) (rest : List W) : State :=
  let v0 : W := w0 + w1
  let v1 : W := w5 * w13
  let v2 : W := v1 + v0
  let v3 : W := w4 * w12
  {s with pc := N 8780,memory := s.memory,stack := v3::v2::w2::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::w16::w17::w18::rest}
theorem stage3Part1_run (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions stage3Part1Program {s with pc := N 8772,memory := s.memory,stack := w0::w1::w2::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::w16::w17::w18::rest} = some (stage3Part1Model s w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 63) : rest.length+j < 1024 := by omega
  simp [hz,hzn,stage3Part1Program,stage3Part1Model,runInstructions,runInstr,List.exchange,succ_ofNat_mod,ofNat_add_mod,Nat.add_assoc,State.activeWordsAfterUInt256,literal_eq_ofNat,capacity]
def stage3Part2Program : List Instr :=
  [.op .ADD,
   .op (.Dup dA10),
   .op (.Dup dA3),
   .op .MUL,
   .op .ADD,
   .op (.Dup dA15),
   .op .MUL,
   .push 1 16]
def stage3Part2Model (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 : W) (rest : List W) : State :=
  let v0 : W := w0 + w1
  let v1 : W := w3 * w11
  let v2 : W := v1 + v0
  let v3 : W := w16 * v2
  {s with pc := N 8789,memory := s.memory,stack := (N 16)::v3::w2::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::w16::w17::w18::rest}
theorem stage3Part2_run (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions stage3Part2Program {s with pc := N 8780,memory := s.memory,stack := w0::w1::w2::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::w16::w17::w18::rest} = some (stage3Part2Model s w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 63) : rest.length+j < 1024 := by omega
  simp [hz,hzn,stage3Part2Program,stage3Part2Model,runInstructions,runInstr,List.exchange,succ_ofNat_mod,ofNat_add_mod,Nat.add_assoc,State.activeWordsAfterUInt256,literal_eq_ofNat,capacity]
def stage3Part3Program : List Instr :=
  [.op .SHR,
   .op (.Swap sA0),
   .op (.Dup dA14),
   .op (.Dup dA9),
   .op (.Dup dA7),
   .op .MULMOD,
   .op (.Dup dA15),
   .op (.Dup dA9)]
def stage3Part3Model (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 : W) (rest : List W) : State :=
  let v0 : W := UInt256.shiftRight w1 w0
  let v1 : W := UInt256.mulMod w6 w9 w15
  {s with pc := N 8797,memory := s.memory,stack := w8::w15::v1::w2::v0::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::w16::w17::w18::rest}
theorem stage3Part3_run (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions stage3Part3Program {s with pc := N 8789,memory := s.memory,stack := w0::w1::w2::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::w16::w17::w18::rest} = some (stage3Part3Model s w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 63) : rest.length+j < 1024 := by omega
  simp [hz,hzn,stage3Part3Program,stage3Part3Model,runInstructions,runInstr,List.exchange,succ_ofNat_mod,ofNat_add_mod,Nat.add_assoc,State.activeWordsAfterUInt256,literal_eq_ofNat,capacity]
def stage3Part4Program : List Instr :=
  [.op (.Dup dA9),
   .op .MULMOD,
   .op .ADD,
   .op .ADD,
   .op (.Dup dA14),
   .op (.Dup dA13),
   .op (.Dup dA6),
   .op .MULMOD]
def stage3Part4Model (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 w20 : W) (rest : List W) : State :=
  let v0 : W := UInt256.mulMod w9 w0 w1
  let v1 : W := v0 + w2
  let v2 : W := v1 + w3
  let v3 : W := UInt256.mulMod w7 w15 w17
  {s with pc := N 8805,memory := s.memory,stack := v3::v2::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::w16::w17::w18::w19::w20::rest}
theorem stage3Part4_run (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 w20 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions stage3Part4Program {s with pc := N 8797,memory := s.memory,stack := w0::w1::w2::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::w16::w17::w18::w19::w20::rest} = some (stage3Part4Model s w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 w20 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 63) : rest.length+j < 1024 := by omega
  simp [hz,hzn,stage3Part4Program,stage3Part4Model,runInstructions,runInstr,List.exchange,succ_ofNat_mod,ofNat_add_mod,Nat.add_assoc,State.activeWordsAfterUInt256,literal_eq_ofNat,capacity]
def stage3Part5Program : List Instr :=
  [.op .ADD,
   .op (.Dup dA14),
   .op (.Dup dA12),
   .op (.Dup dA5),
   .op .MULMOD,
   .op .ADD,
   .op (.Dup dA14),
   .op (.Dup dA11)]
def stage3Part5Model (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 : W) (rest : List W) : State :=
  let v0 : W := w0 + w1
  let v1 : W := UInt256.mulMod w4 w12 w15
  let v2 : W := v1 + v0
  {s with pc := N 8813,memory := s.memory,stack := w11::w15::v2::w2::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::w16::w17::w18::rest}
theorem stage3Part5_run (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions stage3Part5Program {s with pc := N 8805,memory := s.memory,stack := w0::w1::w2::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::w16::w17::w18::rest} = some (stage3Part5Model s w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 63) : rest.length+j < 1024 := by omega
  simp [hz,hzn,stage3Part5Program,stage3Part5Model,runInstructions,runInstr,List.exchange,succ_ofNat_mod,ofNat_add_mod,Nat.add_assoc,State.activeWordsAfterUInt256,literal_eq_ofNat,capacity]
def stage3Part6Program : List Instr :=
  [.op (.Dup dA4),
   .op .MULMOD,
   .op .ADD,
   .op (.Dup dA14),
   .push 1 160,
   .op .MLOAD,
   .op (.Dup dA3),
   .op .MULMOD]
def stage3Part6Model (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 : W) (rest : List W) : State :=
  let v0 : W := UInt256.mulMod w4 w0 w1
  let v1 : W := v0 + w2
  let v2 : W := MachineState.readWord (s.memory) 160
  let v3 : W := UInt256.mulMod w3 v2 w16
  {s with pc := N 8822,memory := s.memory,stack := v3::v1::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::w16::w17::w18::w19::rest}
theorem stage3Part6_run (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions stage3Part6Program {s with pc := N 8813,memory := s.memory,stack := w0::w1::w2::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::w16::w17::w18::w19::rest} = some (stage3Part6Model s w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 63) : rest.length+j < 1024 := by omega
  have ha160 : (160 : W).toNat = 160 := rfl
  have hf160 := Monpro.activeWords_fix s 160 32 (by decide) (by norm_num) hact
  simp [hz,hzn,stage3Part6Program,stage3Part6Model,runInstructions,runInstr,List.exchange,succ_ofNat_mod,ofNat_add_mod,Nat.add_assoc,State.activeWordsAfterUInt256,literal_eq_ofNat,capacity,ha160,hf160]
def stage3Part7Program : List Instr :=
  [.op .ADD,
   .op (.Dup dA14),
   .op (.Swap sA0),
   .push 2 2048,
   .op .MULMOD]
def stage3Part7Model (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 : W) (rest : List W) : State :=
  let v0 : W := w0 + w1
  let v1 : W := UInt256.mulMod (N 2048) v0 w15
  {s with pc := N 8829,memory := s.memory,stack := v1::w2::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::w16::w17::w18::rest}
theorem stage3Part7_run (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions stage3Part7Program {s with pc := N 8822,memory := s.memory,stack := w0::w1::w2::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::w16::w17::w18::rest} = some (stage3Part7Model s w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 63) : rest.length+j < 1024 := by omega
  simp [hz,hzn,stage3Part7Program,stage3Part7Model,runInstructions,runInstr,List.exchange,succ_ofNat_mod,ofNat_add_mod,Nat.add_assoc,State.activeWordsAfterUInt256,literal_eq_ofNat,capacity]
def stage3Program : List Instr := (stage3Part0Program++(stage3Part1Program++(stage3Part2Program++(stage3Part3Program++(stage3Part4Program++(stage3Part5Program++(stage3Part6Program++stage3Part7Program)))))))
def stage3Model (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 : W) (rest : List W) : State :=
  let v0 : W := w4 * w7
  let v1 : W := w5 * w6
  let v2 : W := v1 + v0
  let v3 : W := v2 + w0
  let v4 : W := w3 * w11
  let v5 : W := v4 + v3
  let v6 : W := w2 * w10
  let v7 : W := v6 + v5
  let v8 : W := w1 * w9
  let v9 : W := v8 + v7
  let v10 : W := w14 * v9
  let v11 : W := UInt256.shiftRight v10 (N 16)
  let v12 : W := UInt256.mulMod w4 w7 w13
  let v13 : W := UInt256.mulMod w5 w6 w13
  let v14 : W := v13 + v12
  let v15 : W := v14 + w0
  let v16 : W := UInt256.mulMod w3 w11 w13
  let v17 : W := v16 + v15
  let v18 : W := UInt256.mulMod w2 w10 w13
  let v19 : W := v18 + v17
  let v20 : W := UInt256.mulMod w1 w9 w13
  let v21 : W := v20 + v19
  let v22 : W := MachineState.readWord (s.memory) 160
  let v23 : W := UInt256.mulMod v11 v22 w13
  let v24 : W := v23 + v21
  let v25 : W := UInt256.mulMod (N 2048) v24 w13
  {s with pc := N 8829,memory := s.memory,stack := v25::v11::w1::w2::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::w16::rest}
theorem stage3_run (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions stage3Program {s with pc := N 8764,memory := s.memory,stack := w0::w1::w2::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::w16::rest} = some (stage3Model s w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 rest) := by
  let v0 : W := w4 * w7
  let v1 : W := w5 * w6
  let v2 : W := v1 + v0
  let v3 : W := v2 + w0
  let v4 : W := w3 * w11
  let v5 : W := v4 + v3
  let v6 : W := w2 * w10
  let v7 : W := v6 + v5
  let v8 : W := w1 * w9
  let v9 : W := v8 + v7
  let v10 : W := w14 * v9
  let v11 : W := UInt256.shiftRight v10 (N 16)
  let v12 : W := UInt256.mulMod w4 w7 w13
  let v13 : W := UInt256.mulMod w5 w6 w13
  let v14 : W := v13 + v12
  let v15 : W := v14 + w0
  let v16 : W := UInt256.mulMod w3 w11 w13
  let v17 : W := v16 + v15
  let v18 : W := UInt256.mulMod w2 w10 w13
  let v19 : W := v18 + v17
  let v20 : W := UInt256.mulMod w1 w9 w13
  let v21 : W := v20 + v19
  let v22 : W := MachineState.readWord (s.memory) 160
  let v23 : W := UInt256.mulMod v11 v22 w13
  let v24 : W := v23 + v21
  let v25 : W := UInt256.mulMod (N 2048) v24 w13
  have h0 : runInstructions stage3Part0Program {s with pc := N 8764,memory := s.memory,stack := w0::w1::w2::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::w16::rest} = some {s with pc := N 8772,memory := s.memory,stack := v2::w0::w0::w1::w2::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::w16::rest} := by
    simpa only [stage3Part0Model,v0,v1,v2] using stage3Part0_run ({s with memory := s.memory}) w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 rest hcap hact
  have h1 : runInstructions stage3Part1Program {s with pc := N 8772,memory := s.memory,stack := v2::w0::w0::w1::w2::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::w16::rest} = some {s with pc := N 8780,memory := s.memory,stack := v6::v5::w0::w1::w2::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::w16::rest} := by
    simpa only [stage3Part1Model,v3,v4,v5,v6] using stage3Part1_run ({s with memory := s.memory}) v2 w0 w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 rest hcap hact
  have h2 : runInstructions stage3Part2Program {s with pc := N 8780,memory := s.memory,stack := v6::v5::w0::w1::w2::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::w16::rest} = some {s with pc := N 8789,memory := s.memory,stack := (N 16)::v10::w0::w1::w2::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::w16::rest} := by
    simpa only [stage3Part2Model,v7,v8,v9,v10] using stage3Part2_run ({s with memory := s.memory}) v6 v5 w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 rest hcap hact
  have h3 : runInstructions stage3Part3Program {s with pc := N 8789,memory := s.memory,stack := (N 16)::v10::w0::w1::w2::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::w16::rest} = some {s with pc := N 8797,memory := s.memory,stack := w6::w13::v12::w0::v11::w1::w2::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::w16::rest} := by
    simpa only [stage3Part3Model,v11,v12] using stage3Part3_run ({s with memory := s.memory}) (N 16) v10 w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 rest hcap hact
  have h4 : runInstructions stage3Part4Program {s with pc := N 8797,memory := s.memory,stack := w6::w13::v12::w0::v11::w1::w2::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::w16::rest} = some {s with pc := N 8805,memory := s.memory,stack := v16::v15::v11::w1::w2::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::w16::rest} := by
    simpa only [stage3Part4Model,v13,v14,v15,v16] using stage3Part4_run ({s with memory := s.memory}) w6 w13 v12 w0 v11 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 rest hcap hact
  have h5 : runInstructions stage3Part5Program {s with pc := N 8805,memory := s.memory,stack := v16::v15::v11::w1::w2::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::w16::rest} = some {s with pc := N 8813,memory := s.memory,stack := w9::w13::v19::v11::w1::w2::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::w16::rest} := by
    simpa only [stage3Part5Model,v17,v18,v19] using stage3Part5_run ({s with memory := s.memory}) v16 v15 v11 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 rest hcap hact
  have h6 : runInstructions stage3Part6Program {s with pc := N 8813,memory := s.memory,stack := w9::w13::v19::v11::w1::w2::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::w16::rest} = some {s with pc := N 8822,memory := s.memory,stack := v23::v21::v11::w1::w2::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::w16::rest} := by
    simpa only [stage3Part6Model,v20,v21,v22,v23] using stage3Part6_run ({s with memory := s.memory}) w9 w13 v19 v11 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 rest hcap hact
  have h7 : runInstructions stage3Part7Program {s with pc := N 8822,memory := s.memory,stack := v23::v21::v11::w1::w2::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::w16::rest} = some {s with pc := N 8829,memory := s.memory,stack := v25::v11::w1::w2::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::w16::rest} := by
    simpa only [stage3Part7Model,v24,v25] using stage3Part7_run ({s with memory := s.memory}) v23 v21 v11 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 rest hcap hact
  exact (runInstructions_append_some _ _ _ _ _ h0 (runInstructions_append_some _ _ _ _ _ h1 (runInstructions_append_some _ _ _ _ _ h2 (runInstructions_append_some _ _ _ _ _ h3 (runInstructions_append_some _ _ _ _ _ h4 (runInstructions_append_some _ _ _ _ _ h5 (runInstructions_append_some _ _ _ _ _ h6 h7)))))))
def stage4Part0Program : List Instr :=
  [.op (.Dup dA14),
   .op (.Dup dA6),
   .op (.Dup dA11),
   .op .MULMOD,
   .op (.Dup dA15),
   .op (.Dup dA8),
   .op (.Dup dA11),
   .op .MULMOD]
def stage4Part0Model (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 : W) (rest : List W) : State :=
  let v0 : W := UInt256.mulMod w9 w5 w14
  let v1 : W := UInt256.mulMod w8 w6 w14
  {s with pc := N 8837,memory := s.memory,stack := v1::v0::w0::w1::w2::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::w16::w17::rest}
theorem stage4Part0_run (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions stage4Part0Program {s with pc := N 8829,memory := s.memory,stack := w0::w1::w2::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::w16::w17::rest} = some (stage4Part0Model s w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 63) : rest.length+j < 1024 := by omega
  simp [hz,hzn,stage4Part0Program,stage4Part0Model,runInstructions,runInstr,List.exchange,succ_ofNat_mod,ofNat_add_mod,Nat.add_assoc,State.activeWordsAfterUInt256,literal_eq_ofNat,capacity]
def stage4Part1Program : List Instr :=
  [.op .ADD,
   .op (.Dup dA1),
   .op .ADD,
   .op (.Dup dA15),
   .op (.Dup dA9),
   .op (.Dup dA0),
   .op .MULMOD,
   .op .ADD]
def stage4Part1Model (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 : W) (rest : List W) : State :=
  let v0 : W := w0 + w1
  let v1 : W := w2 + v0
  let v2 : W := UInt256.mulMod w9 w9 w16
  let v3 : W := v2 + v1
  {s with pc := N 8845,memory := s.memory,stack := v3::w2::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::w16::w17::w18::w19::rest}
theorem stage4Part1_run (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions stage4Part1Program {s with pc := N 8837,memory := s.memory,stack := w0::w1::w2::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::w16::w17::w18::w19::rest} = some (stage4Part1Model s w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 63) : rest.length+j < 1024 := by omega
  simp [hz,hzn,stage4Part1Program,stage4Part1Model,runInstructions,runInstr,List.exchange,succ_ofNat_mod,ofNat_add_mod,Nat.add_assoc,State.activeWordsAfterUInt256,literal_eq_ofNat,capacity]
def stage4Part2Program : List Instr :=
  [.op (.Dup dA15),
   .op (.Dup dA15),
   .op (.Dup dA7),
   .op .MULMOD,
   .op .ADD,
   .op (.Dup dA15),
   .op (.Dup dA14),
   .op (.Dup dA6)]
def stage4Part2Model (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 : W) (rest : List W) : State :=
  let v0 : W := UInt256.mulMod w5 w14 w15
  let v1 : W := v0 + w0
  {s with pc := N 8853,memory := s.memory,stack := w4::w13::w15::v1::w1::w2::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::w16::w17::w18::rest}
theorem stage4Part2_run (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions stage4Part2Program {s with pc := N 8845,memory := s.memory,stack := w0::w1::w2::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::w16::w17::w18::rest} = some (stage4Part2Model s w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 63) : rest.length+j < 1024 := by omega
  simp [hz,hzn,stage4Part2Program,stage4Part2Model,runInstructions,runInstr,List.exchange,succ_ofNat_mod,ofNat_add_mod,Nat.add_assoc,State.activeWordsAfterUInt256,literal_eq_ofNat,capacity]
def stage4Part3Program : List Instr :=
  [.op .MULMOD,
   .op .ADD,
   .op (.Dup dA15),
   .op (.Dup dA13),
   .op (.Dup dA5),
   .op .MULMOD,
   .op .ADD,
   .op (.Dup dA15)]
def stage4Part3Model (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 w20 w21 : W) (rest : List W) : State :=
  let v0 : W := UInt256.mulMod w0 w1 w2
  let v1 : W := v0 + w3
  let v2 : W := UInt256.mulMod w6 w15 w18
  let v3 : W := v2 + v1
  {s with pc := N 8861,memory := s.memory,stack := w18::v3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::w16::w17::w18::w19::w20::w21::rest}
theorem stage4Part3_run (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 w20 w21 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions stage4Part3Program {s with pc := N 8853,memory := s.memory,stack := w0::w1::w2::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::w16::w17::w18::w19::w20::w21::rest} = some (stage4Part3Model s w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 w20 w21 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 63) : rest.length+j < 1024 := by omega
  simp [hz,hzn,stage4Part3Program,stage4Part3Model,runInstructions,runInstr,List.exchange,succ_ofNat_mod,ofNat_add_mod,Nat.add_assoc,State.activeWordsAfterUInt256,literal_eq_ofNat,capacity]
def stage4Part4Program : List Instr :=
  [.op (.Dup dA12),
   .op (.Dup dA4),
   .op .MULMOD,
   .op .ADD,
   .op (.Swap sA0),
   .op (.Dup dA10),
   .op (.Dup dA7),
   .op .MUL]
def stage4Part4Model (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 : W) (rest : List W) : State :=
  let v0 : W := UInt256.mulMod w3 w12 w0
  let v1 : W := v0 + w1
  let v2 : W := w7 * w11
  {s with pc := N 8869,memory := s.memory,stack := v2::w2::v1::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::w16::w17::w18::w19::rest}
theorem stage4Part4_run (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions stage4Part4Program {s with pc := N 8861,memory := s.memory,stack := w0::w1::w2::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::w16::w17::w18::w19::rest} = some (stage4Part4Model s w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 63) : rest.length+j < 1024 := by omega
  simp [hz,hzn,stage4Part4Program,stage4Part4Model,runInstructions,runInstr,List.exchange,succ_ofNat_mod,ofNat_add_mod,Nat.add_assoc,State.activeWordsAfterUInt256,literal_eq_ofNat,capacity]
def stage4Part5Program : List Instr :=
  [.op (.Dup dA10),
   .op (.Dup dA9),
   .op .MUL,
   .op .ADD,
   .op .ADD,
   .op (.Dup dA8),
   .op (.Dup dA0),
   .op (.Dup dA0)]
def stage4Part5Model (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 : W) (rest : List W) : State :=
  let v0 : W := w8 * w10
  let v1 : W := v0 + w0
  let v2 : W := v1 + w1
  {s with pc := N 8877,memory := s.memory,stack := w9::w9::w9::v2::w2::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::w16::w17::w18::w19::rest}
theorem stage4Part5_run (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions stage4Part5Program {s with pc := N 8869,memory := s.memory,stack := w0::w1::w2::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::w16::w17::w18::w19::rest} = some (stage4Part5Model s w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 63) : rest.length+j < 1024 := by omega
  simp [hz,hzn,stage4Part5Program,stage4Part5Model,runInstructions,runInstr,List.exchange,succ_ofNat_mod,ofNat_add_mod,Nat.add_assoc,State.activeWordsAfterUInt256,literal_eq_ofNat,capacity]
def stage4Part6Program : List Instr :=
  [.op .ADD,
   .op (.Swap sA9),
   .op .MUL,
   .op .ADD,
   .op (.Dup dA14),
   .op (.Dup dA6),
   .op .MUL,
   .op .ADD]
def stage4Part6Model (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 w20 w21 : W) (rest : List W) : State :=
  let v0 : W := w0 + w1
  let v1 : W := w11 * w2
  let v2 : W := v1 + w3
  let v3 : W := w8 * w17
  let v4 : W := v3 + v2
  {s with pc := N 8885,memory := s.memory,stack := v4::w4::w5::w6::w7::w8::w9::w10::v0::w12::w13::w14::w15::w16::w17::w18::w19::w20::w21::rest}
theorem stage4Part6_run (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 w20 w21 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions stage4Part6Program {s with pc := N 8877,memory := s.memory,stack := w0::w1::w2::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::w16::w17::w18::w19::w20::w21::rest} = some (stage4Part6Model s w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 w20 w21 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 63) : rest.length+j < 1024 := by omega
  simp [hz,hzn,stage4Part6Program,stage4Part6Model,runInstructions,runInstr,List.exchange,succ_ofNat_mod,ofNat_add_mod,Nat.add_assoc,State.activeWordsAfterUInt256,literal_eq_ofNat,capacity]
def stage4Part7Program : List Instr :=
  [.op (.Dup dA13),
   .op (.Dup dA5),
   .op .MUL,
   .op .ADD,
   .op (.Dup dA12),
   .op (.Dup dA4),
   .op .MUL,
   .op .ADD]
def stage4Part7Model (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 : W) (rest : List W) : State :=
  let v0 : W := w4 * w13
  let v1 : W := v0 + w0
  let v2 : W := w3 * w12
  let v3 : W := v2 + v1
  {s with pc := N 8893,memory := s.memory,stack := v3::w1::w2::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::w16::w17::w18::rest}
theorem stage4Part7_run (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions stage4Part7Program {s with pc := N 8885,memory := s.memory,stack := w0::w1::w2::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::w16::w17::w18::rest} = some (stage4Part7Model s w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 63) : rest.length+j < 1024 := by omega
  simp [hz,hzn,stage4Part7Program,stage4Part7Model,runInstructions,runInstr,List.exchange,succ_ofNat_mod,ofNat_add_mod,Nat.add_assoc,State.activeWordsAfterUInt256,literal_eq_ofNat,capacity]
def stage4Part8Program : List Instr :=
  [.op (.Dup dA11),
   .op (.Dup dA3),
   .op .MUL,
   .op .ADD,
   .push 1 192,
   .op .MLOAD,
   .op .MUL,
   .push 1 16]
def stage4Part8Model (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 : W) (rest : List W) : State :=
  let v0 : W := w2 * w11
  let v1 : W := v0 + w0
  let v2 : W := MachineState.readWord (s.memory) 192
  let v3 : W := v2 * v1
  {s with pc := N 8903,memory := s.memory,stack := (N 16)::v3::w1::w2::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::w16::w17::w18::rest}
theorem stage4Part8_run (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions stage4Part8Program {s with pc := N 8893,memory := s.memory,stack := w0::w1::w2::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::w16::w17::w18::rest} = some (stage4Part8Model s w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 63) : rest.length+j < 1024 := by omega
  have ha192 : (192 : W).toNat = 192 := rfl
  have hf192 := Monpro.activeWords_fix s 192 32 (by decide) (by norm_num) hact
  simp [hz,hzn,stage4Part8Program,stage4Part8Model,runInstructions,runInstr,List.exchange,succ_ofNat_mod,ofNat_add_mod,Nat.add_assoc,State.activeWordsAfterUInt256,literal_eq_ofNat,capacity,ha192,hf192]
def stage4Part9Program : List Instr :=
  [.op .SHR,
   .op (.Swap sA4),
   .op .POP,
   .op (.Dup dA14),
   .push 1 160,
   .op .MLOAD,
   .op (.Dup dA6),
   .op .MULMOD]
def stage4Part9Model (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 : W) (rest : List W) : State :=
  let v0 : W := UInt256.shiftRight w1 w0
  let v1 : W := MachineState.readWord (s.memory) 160
  let v2 : W := UInt256.mulMod v0 v1 w16
  {s with pc := N 8912,memory := s.memory,stack := v2::w2::w3::w4::w5::v0::w7::w8::w9::w10::w11::w12::w13::w14::w15::w16::w17::w18::w19::rest}
theorem stage4Part9_run (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions stage4Part9Program {s with pc := N 8903,memory := s.memory,stack := w0::w1::w2::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::w16::w17::w18::w19::rest} = some (stage4Part9Model s w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 63) : rest.length+j < 1024 := by omega
  have ha160 : (160 : W).toNat = 160 := rfl
  have hf160 := Monpro.activeWords_fix s 160 32 (by decide) (by norm_num) hact
  simp [hz,hzn,stage4Part9Program,stage4Part9Model,runInstructions,runInstr,List.exchange,succ_ofNat_mod,ofNat_add_mod,Nat.add_assoc,State.activeWordsAfterUInt256,literal_eq_ofNat,capacity,ha160,hf160]
def stage4Part10Program : List Instr :=
  [.op .ADD,
   .op (.Dup dA14),
   .op (.Swap sA0),
   .push 2 2048,
   .op .MULMOD]
def stage4Part10Model (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 : W) (rest : List W) : State :=
  let v0 : W := w0 + w1
  let v1 : W := UInt256.mulMod (N 2048) v0 w15
  {s with pc := N 8919,memory := s.memory,stack := v1::w2::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::w16::w17::w18::rest}
theorem stage4Part10_run (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions stage4Part10Program {s with pc := N 8912,memory := s.memory,stack := w0::w1::w2::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::w16::w17::w18::rest} = some (stage4Part10Model s w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 63) : rest.length+j < 1024 := by omega
  simp [hz,hzn,stage4Part10Program,stage4Part10Model,runInstructions,runInstr,List.exchange,succ_ofNat_mod,ofNat_add_mod,Nat.add_assoc,State.activeWordsAfterUInt256,literal_eq_ofNat,capacity]
def stage4Program : List Instr := (stage4Part0Program++(stage4Part1Program++(stage4Part2Program++(stage4Part3Program++(stage4Part4Program++(stage4Part5Program++(stage4Part6Program++(stage4Part7Program++(stage4Part8Program++(stage4Part9Program++stage4Part10Program))))))))))
def stage4Model (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 : W) (rest : List W) : State :=
  let v0 : W := UInt256.mulMod w9 w5 w14
  let v1 : W := UInt256.mulMod w8 w6 w14
  let v2 : W := v1 + v0
  let v3 : W := w0 + v2
  let v4 : W := UInt256.mulMod w7 w7 w14
  let v5 : W := v4 + v3
  let v6 : W := UInt256.mulMod w4 w13 w14
  let v7 : W := v6 + v5
  let v8 : W := UInt256.mulMod w3 w12 w14
  let v9 : W := v8 + v7
  let v10 : W := UInt256.mulMod w2 w11 w14
  let v11 : W := v10 + v9
  let v12 : W := UInt256.mulMod w1 w10 w14
  let v13 : W := v12 + v11
  let v14 : W := w5 * w9
  let v15 : W := w6 * w8
  let v16 : W := v15 + v14
  let v17 : W := v16 + w0
  let v18 : W := w7 + w7
  let v19 : W := w7 * w7
  let v20 : W := v19 + v17
  let v21 : W := w4 * w13
  let v22 : W := v21 + v20
  let v23 : W := w3 * w12
  let v24 : W := v23 + v22
  let v25 : W := w2 * w11
  let v26 : W := v25 + v24
  let v27 : W := w1 * w10
  let v28 : W := v27 + v26
  let v29 : W := MachineState.readWord (s.memory) 192
  let v30 : W := v29 * v28
  let v31 : W := UInt256.shiftRight v30 (N 16)
  let v32 : W := MachineState.readWord (s.memory) 160
  let v33 : W := UInt256.mulMod v31 v32 w14
  let v34 : W := v33 + v13
  let v35 : W := UInt256.mulMod (N 2048) v34 w14
  {s with pc := N 8919,memory := s.memory,stack := v35::w1::w2::w3::v31::w5::w6::v18::w8::w9::w10::w11::w12::w13::w14::w15::w16::w17::rest}
theorem stage4_run (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions stage4Program {s with pc := N 8829,memory := s.memory,stack := w0::w1::w2::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::w16::w17::rest} = some (stage4Model s w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 rest) := by
  let v0 : W := UInt256.mulMod w9 w5 w14
  let v1 : W := UInt256.mulMod w8 w6 w14
  let v2 : W := v1 + v0
  let v3 : W := w0 + v2
  let v4 : W := UInt256.mulMod w7 w7 w14
  let v5 : W := v4 + v3
  let v6 : W := UInt256.mulMod w4 w13 w14
  let v7 : W := v6 + v5
  let v8 : W := UInt256.mulMod w3 w12 w14
  let v9 : W := v8 + v7
  let v10 : W := UInt256.mulMod w2 w11 w14
  let v11 : W := v10 + v9
  let v12 : W := UInt256.mulMod w1 w10 w14
  let v13 : W := v12 + v11
  let v14 : W := w5 * w9
  let v15 : W := w6 * w8
  let v16 : W := v15 + v14
  let v17 : W := v16 + w0
  let v18 : W := w7 + w7
  let v19 : W := w7 * w7
  let v20 : W := v19 + v17
  let v21 : W := w4 * w13
  let v22 : W := v21 + v20
  let v23 : W := w3 * w12
  let v24 : W := v23 + v22
  let v25 : W := w2 * w11
  let v26 : W := v25 + v24
  let v27 : W := w1 * w10
  let v28 : W := v27 + v26
  let v29 : W := MachineState.readWord (s.memory) 192
  let v30 : W := v29 * v28
  let v31 : W := UInt256.shiftRight v30 (N 16)
  let v32 : W := MachineState.readWord (s.memory) 160
  let v33 : W := UInt256.mulMod v31 v32 w14
  let v34 : W := v33 + v13
  let v35 : W := UInt256.mulMod (N 2048) v34 w14
  have h0 : runInstructions stage4Part0Program {s with pc := N 8829,memory := s.memory,stack := w0::w1::w2::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::w16::w17::rest} = some {s with pc := N 8837,memory := s.memory,stack := v1::v0::w0::w1::w2::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::w16::w17::rest} := by
    simpa only [stage4Part0Model,v0,v1] using stage4Part0_run ({s with memory := s.memory}) w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 rest hcap hact
  have h1 : runInstructions stage4Part1Program {s with pc := N 8837,memory := s.memory,stack := v1::v0::w0::w1::w2::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::w16::w17::rest} = some {s with pc := N 8845,memory := s.memory,stack := v5::w0::w1::w2::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::w16::w17::rest} := by
    simpa only [stage4Part1Model,v2,v3,v4,v5] using stage4Part1_run ({s with memory := s.memory}) v1 v0 w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 rest hcap hact
  have h2 : runInstructions stage4Part2Program {s with pc := N 8845,memory := s.memory,stack := v5::w0::w1::w2::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::w16::w17::rest} = some {s with pc := N 8853,memory := s.memory,stack := w3::w12::w14::v7::w0::w1::w2::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::w16::w17::rest} := by
    simpa only [stage4Part2Model,v6,v7] using stage4Part2_run ({s with memory := s.memory}) v5 w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 rest hcap hact
  have h3 : runInstructions stage4Part3Program {s with pc := N 8853,memory := s.memory,stack := w3::w12::w14::v7::w0::w1::w2::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::w16::w17::rest} = some {s with pc := N 8861,memory := s.memory,stack := w14::v11::w0::w1::w2::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::w16::w17::rest} := by
    simpa only [stage4Part3Model,v8,v9,v10,v11] using stage4Part3_run ({s with memory := s.memory}) w3 w12 w14 v7 w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 rest hcap hact
  have h4 : runInstructions stage4Part4Program {s with pc := N 8861,memory := s.memory,stack := w14::v11::w0::w1::w2::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::w16::w17::rest} = some {s with pc := N 8869,memory := s.memory,stack := v14::w0::v13::w1::w2::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::w16::w17::rest} := by
    simpa only [stage4Part4Model,v12,v13,v14] using stage4Part4_run ({s with memory := s.memory}) w14 v11 w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 rest hcap hact
  have h5 : runInstructions stage4Part5Program {s with pc := N 8869,memory := s.memory,stack := v14::w0::v13::w1::w2::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::w16::w17::rest} = some {s with pc := N 8877,memory := s.memory,stack := w7::w7::w7::v17::v13::w1::w2::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::w16::w17::rest} := by
    simpa only [stage4Part5Model,v15,v16,v17] using stage4Part5_run ({s with memory := s.memory}) v14 w0 v13 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 rest hcap hact
  have h6 : runInstructions stage4Part6Program {s with pc := N 8877,memory := s.memory,stack := w7::w7::w7::v17::v13::w1::w2::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::w16::w17::rest} = some {s with pc := N 8885,memory := s.memory,stack := v22::v13::w1::w2::w3::w4::w5::w6::v18::w8::w9::w10::w11::w12::w13::w14::w15::w16::w17::rest} := by
    simpa only [stage4Part6Model,v18,v19,v20,v21,v22] using stage4Part6_run ({s with memory := s.memory}) w7 w7 w7 v17 v13 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 rest hcap hact
  have h7 : runInstructions stage4Part7Program {s with pc := N 8885,memory := s.memory,stack := v22::v13::w1::w2::w3::w4::w5::w6::v18::w8::w9::w10::w11::w12::w13::w14::w15::w16::w17::rest} = some {s with pc := N 8893,memory := s.memory,stack := v26::v13::w1::w2::w3::w4::w5::w6::v18::w8::w9::w10::w11::w12::w13::w14::w15::w16::w17::rest} := by
    simpa only [stage4Part7Model,v23,v24,v25,v26] using stage4Part7_run ({s with memory := s.memory}) v22 v13 w1 w2 w3 w4 w5 w6 v18 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 rest hcap hact
  have h8 : runInstructions stage4Part8Program {s with pc := N 8893,memory := s.memory,stack := v26::v13::w1::w2::w3::w4::w5::w6::v18::w8::w9::w10::w11::w12::w13::w14::w15::w16::w17::rest} = some {s with pc := N 8903,memory := s.memory,stack := (N 16)::v30::v13::w1::w2::w3::w4::w5::w6::v18::w8::w9::w10::w11::w12::w13::w14::w15::w16::w17::rest} := by
    simpa only [stage4Part8Model,v27,v28,v29,v30] using stage4Part8_run ({s with memory := s.memory}) v26 v13 w1 w2 w3 w4 w5 w6 v18 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 rest hcap hact
  have h9 : runInstructions stage4Part9Program {s with pc := N 8903,memory := s.memory,stack := (N 16)::v30::v13::w1::w2::w3::w4::w5::w6::v18::w8::w9::w10::w11::w12::w13::w14::w15::w16::w17::rest} = some {s with pc := N 8912,memory := s.memory,stack := v33::v13::w1::w2::w3::v31::w5::w6::v18::w8::w9::w10::w11::w12::w13::w14::w15::w16::w17::rest} := by
    simpa only [stage4Part9Model,v31,v32,v33] using stage4Part9_run ({s with memory := s.memory}) (N 16) v30 v13 w1 w2 w3 w4 w5 w6 v18 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 rest hcap hact
  have h10 : runInstructions stage4Part10Program {s with pc := N 8912,memory := s.memory,stack := v33::v13::w1::w2::w3::v31::w5::w6::v18::w8::w9::w10::w11::w12::w13::w14::w15::w16::w17::rest} = some {s with pc := N 8919,memory := s.memory,stack := v35::w1::w2::w3::v31::w5::w6::v18::w8::w9::w10::w11::w12::w13::w14::w15::w16::w17::rest} := by
    simpa only [stage4Part10Model,v34,v35] using stage4Part10_run ({s with memory := s.memory}) v33 v13 w1 w2 w3 v31 w5 w6 v18 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 rest hcap hact
  exact (runInstructions_append_some _ _ _ _ _ h0 (runInstructions_append_some _ _ _ _ _ h1 (runInstructions_append_some _ _ _ _ _ h2 (runInstructions_append_some _ _ _ _ _ h3 (runInstructions_append_some _ _ _ _ _ h4 (runInstructions_append_some _ _ _ _ _ h5 (runInstructions_append_some _ _ _ _ _ h6 (runInstructions_append_some _ _ _ _ _ h7 (runInstructions_append_some _ _ _ _ _ h8 (runInstructions_append_some _ _ _ _ _ h9 h10))))))))))
def stage5Part0Program : List Instr :=
  [.op (.Dup dA0),
   .op (.Dup dA10),
   .op (.Dup dA8),
   .op .MUL,
   .op (.Dup dA10),
   .op (.Dup dA10),
   .op .MUL,
   .op .ADD]
def stage5Part0Model (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 : W) (rest : List W) : State :=
  let v0 : W := w6 * w9
  let v1 : W := w7 * w8
  let v2 : W := v1 + v0
  {s with pc := N 8927,memory := s.memory,stack := v2::w0::w0::w1::w2::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::w16::w17::rest}
theorem stage5Part0_run (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions stage5Part0Program {s with pc := N 8919,memory := s.memory,stack := w0::w1::w2::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::w16::w17::rest} = some (stage5Part0Model s w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 63) : rest.length+j < 1024 := by omega
  simp [hz,hzn,stage5Part0Program,stage5Part0Model,runInstructions,runInstr,List.exchange,succ_ofNat_mod,ofNat_add_mod,Nat.add_assoc,State.activeWordsAfterUInt256,literal_eq_ofNat,capacity]
def stage5Part1Program : List Instr :=
  [.op .ADD,
   .op (.Dup dA14),
   .op (.Dup dA5),
   .op .MUL,
   .op .ADD,
   .op (.Dup dA13),
   .op (.Dup dA4),
   .op .MUL]
def stage5Part1Model (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 : W) (rest : List W) : State :=
  let v0 : W := w0 + w1
  let v1 : W := w5 * w15
  let v2 : W := v1 + v0
  let v3 : W := w4 * w14
  {s with pc := N 8935,memory := s.memory,stack := v3::v2::w2::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::w16::w17::w18::w19::rest}
theorem stage5Part1_run (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions stage5Part1Program {s with pc := N 8927,memory := s.memory,stack := w0::w1::w2::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::w16::w17::w18::w19::rest} = some (stage5Part1Model s w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 63) : rest.length+j < 1024 := by omega
  simp [hz,hzn,stage5Part1Program,stage5Part1Model,runInstructions,runInstr,List.exchange,succ_ofNat_mod,ofNat_add_mod,Nat.add_assoc,State.activeWordsAfterUInt256,literal_eq_ofNat,capacity]
def stage5Part2Program : List Instr :=
  [.op .ADD,
   .op (.Dup dA12),
   .op (.Dup dA3),
   .op .MUL,
   .op .ADD,
   .op (.Dup dA11),
   .op (.Dup dA6),
   .op .MUL]
def stage5Part2Model (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 : W) (rest : List W) : State :=
  let v0 : W := w0 + w1
  let v1 : W := w3 * w13
  let v2 : W := v1 + v0
  let v3 : W := w6 * w12
  {s with pc := N 8943,memory := s.memory,stack := v3::v2::w2::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::w16::w17::w18::w19::rest}
theorem stage5Part2_run (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions stage5Part2Program {s with pc := N 8935,memory := s.memory,stack := w0::w1::w2::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::w16::w17::w18::w19::rest} = some (stage5Part2Model s w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 63) : rest.length+j < 1024 := by omega
  simp [hz,hzn,stage5Part2Program,stage5Part2Model,runInstructions,runInstr,List.exchange,succ_ofNat_mod,ofNat_add_mod,Nat.add_assoc,State.activeWordsAfterUInt256,literal_eq_ofNat,capacity]
def stage5Part3Program : List Instr :=
  [.op .ADD,
   .op (.Swap sA0),
   .op (.Dup dA15),
   .op (.Dup dA0),
   .op (.Dup dA12),
   .op (.Dup dA10),
   .op .MULMOD,
   .op (.Swap sA0)]
def stage5Part3Model (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 : W) (rest : List W) : State :=
  let v0 : W := w0 + w1
  let v1 : W := UInt256.mulMod w8 w11 w16
  {s with pc := N 8951,memory := s.memory,stack := w16::v1::w2::v0::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::w16::w17::w18::w19::rest}
theorem stage5Part3_run (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions stage5Part3Program {s with pc := N 8943,memory := s.memory,stack := w0::w1::w2::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::w16::w17::w18::w19::rest} = some (stage5Part3Model s w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 63) : rest.length+j < 1024 := by omega
  simp [hz,hzn,stage5Part3Program,stage5Part3Model,runInstructions,runInstr,List.exchange,succ_ofNat_mod,ofNat_add_mod,Nat.add_assoc,State.activeWordsAfterUInt256,literal_eq_ofNat,capacity]
def stage5Part4Program : List Instr :=
  [.op (.Dup dA11),
   .op (.Dup dA11),
   .op .MULMOD,
   .op .ADD,
   .op .ADD,
   .op (.Dup dA15),
   .op (.Dup dA15),
   .op (.Dup dA6)]
def stage5Part4Model (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 w20 : W) (rest : List W) : State :=
  let v0 : W := UInt256.mulMod w10 w11 w0
  let v1 : W := v0 + w1
  let v2 : W := v1 + w2
  {s with pc := N 8959,memory := s.memory,stack := w6::w16::w17::v2::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::w16::w17::w18::w19::w20::rest}
theorem stage5Part4_run (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 w20 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions stage5Part4Program {s with pc := N 8951,memory := s.memory,stack := w0::w1::w2::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::w16::w17::w18::w19::w20::rest} = some (stage5Part4Model s w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 w20 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 63) : rest.length+j < 1024 := by omega
  simp [hz,hzn,stage5Part4Program,stage5Part4Model,runInstructions,runInstr,List.exchange,succ_ofNat_mod,ofNat_add_mod,Nat.add_assoc,State.activeWordsAfterUInt256,literal_eq_ofNat,capacity]
def stage5Part5Program : List Instr :=
  [.op .MULMOD,
   .op .ADD,
   .op (.Dup dA15),
   .op (.Dup dA14),
   .op (.Dup dA5),
   .op .MULMOD,
   .op .ADD,
   .op (.Dup dA15)]
def stage5Part5Model (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 w20 w21 : W) (rest : List W) : State :=
  let v0 : W := UInt256.mulMod w0 w1 w2
  let v1 : W := v0 + w3
  let v2 : W := UInt256.mulMod w6 w16 w18
  let v3 : W := v2 + v1
  {s with pc := N 8967,memory := s.memory,stack := w18::v3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::w16::w17::w18::w19::w20::w21::rest}
theorem stage5Part5_run (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 w20 w21 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions stage5Part5Program {s with pc := N 8959,memory := s.memory,stack := w0::w1::w2::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::w16::w17::w18::w19::w20::w21::rest} = some (stage5Part5Model s w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 w20 w21 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 63) : rest.length+j < 1024 := by omega
  simp [hz,hzn,stage5Part5Program,stage5Part5Model,runInstructions,runInstr,List.exchange,succ_ofNat_mod,ofNat_add_mod,Nat.add_assoc,State.activeWordsAfterUInt256,literal_eq_ofNat,capacity]
def stage5Part6Program : List Instr :=
  [.op (.Dup dA13),
   .op (.Dup dA4),
   .op .MULMOD,
   .op .ADD,
   .op (.Dup dA15),
   .op (.Dup dA12),
   .op (.Dup dA7),
   .op .MULMOD]
def stage5Part6Model (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 : W) (rest : List W) : State :=
  let v0 : W := UInt256.mulMod w3 w13 w0
  let v1 : W := v0 + w1
  let v2 : W := UInt256.mulMod w6 w12 w16
  {s with pc := N 8975,memory := s.memory,stack := v2::v1::w2::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::w16::w17::w18::w19::rest}
theorem stage5Part6_run (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions stage5Part6Program {s with pc := N 8967,memory := s.memory,stack := w0::w1::w2::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::w16::w17::w18::w19::rest} = some (stage5Part6Model s w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 63) : rest.length+j < 1024 := by omega
  simp [hz,hzn,stage5Part6Program,stage5Part6Model,runInstructions,runInstr,List.exchange,succ_ofNat_mod,ofNat_add_mod,Nat.add_assoc,State.activeWordsAfterUInt256,literal_eq_ofNat,capacity]
def stage5Part7Program : List Instr :=
  [.op .ADD,
   .op (.Swap sA0),
   .push 30 1766847064778384329583297500742918515827483896875618958121606201292619775,
   .op .AND,
   .op (.Dup dA0),
   .op (.Swap sA6),
   .op .POP,
   .op (.Dup dA15)]
def stage5Part7Model (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 : W) (rest : List W) : State :=
  let v0 : W := w0 + w1
  let v1 : W := UInt256.land (N 1766847064778384329583297500742918515827483896875618958121606201292619775) w2
  {s with pc := N 9013,memory := s.memory,stack := w16::v1::v0::w3::w4::w5::w6::v1::w8::w9::w10::w11::w12::w13::w14::w15::w16::w17::w18::w19::rest}
theorem stage5Part7_run (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions stage5Part7Program {s with pc := N 8975,memory := s.memory,stack := w0::w1::w2::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::w16::w17::w18::w19::rest} = some (stage5Part7Model s w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 63) : rest.length+j < 1024 := by omega
  simp [hz,hzn,stage5Part7Program,stage5Part7Model,runInstructions,runInstr,List.exchange,succ_ofNat_mod,ofNat_add_mod,Nat.add_assoc,State.activeWordsAfterUInt256,literal_eq_ofNat,capacity]
def stage5Part8Program : List Instr :=
  [.op (.Swap sA1),
   .op .SUB,
   .op (.Dup dA1),
   .op .ADD,
   .push 2 2048,
   .op .MULMOD]
def stage5Part8Model (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 : W) (rest : List W) : State :=
  let v0 : W := w2 - w1
  let v1 : W := w0 + v0
  let v2 : W := UInt256.mulMod (N 2048) v1 w0
  {s with pc := N 9021,memory := s.memory,stack := v2::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::w16::w17::w18::w19::rest}
theorem stage5Part8_run (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions stage5Part8Program {s with pc := N 9013,memory := s.memory,stack := w0::w1::w2::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::w16::w17::w18::w19::rest} = some (stage5Part8Model s w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 63) : rest.length+j < 1024 := by omega
  simp [hz,hzn,stage5Part8Program,stage5Part8Model,runInstructions,runInstr,List.exchange,succ_ofNat_mod,ofNat_add_mod,Nat.add_assoc,State.activeWordsAfterUInt256,literal_eq_ofNat,capacity]
def stage5Program : List Instr := (stage5Part0Program++(stage5Part1Program++(stage5Part2Program++(stage5Part3Program++(stage5Part4Program++(stage5Part5Program++(stage5Part6Program++(stage5Part7Program++stage5Part8Program))))))))
def stage5Model (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 : W) (rest : List W) : State :=
  let v0 : W := w6 * w9
  let v1 : W := w7 * w8
  let v2 : W := v1 + v0
  let v3 : W := v2 + w0
  let v4 : W := w3 * w13
  let v5 : W := v4 + v3
  let v6 : W := w2 * w12
  let v7 : W := v6 + v5
  let v8 : W := w1 * w11
  let v9 : W := v8 + v7
  let v10 : W := w4 * w10
  let v11 : W := v10 + v9
  let v12 : W := UInt256.mulMod w6 w9 w14
  let v13 : W := UInt256.mulMod w7 w8 w14
  let v14 : W := v13 + v12
  let v15 : W := v14 + w0
  let v16 : W := UInt256.mulMod w3 w13 w14
  let v17 : W := v16 + v15
  let v18 : W := UInt256.mulMod w2 w12 w14
  let v19 : W := v18 + v17
  let v20 : W := UInt256.mulMod w1 w11 w14
  let v21 : W := v20 + v19
  let v22 : W := UInt256.mulMod w4 w10 w14
  let v23 : W := v22 + v21
  let v24 : W := UInt256.land (N 1766847064778384329583297500742918515827483896875618958121606201292619775) v11
  let v25 : W := v23 - v24
  let v26 : W := w14 + v25
  let v27 : W := UInt256.mulMod (N 2048) v26 w14
  {s with pc := N 9021,memory := s.memory,stack := v27::w1::w2::w3::w4::v24::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::w16::w17::rest}
theorem stage5_run (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions stage5Program {s with pc := N 8919,memory := s.memory,stack := w0::w1::w2::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::w16::w17::rest} = some (stage5Model s w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 rest) := by
  let v0 : W := w6 * w9
  let v1 : W := w7 * w8
  let v2 : W := v1 + v0
  let v3 : W := v2 + w0
  let v4 : W := w3 * w13
  let v5 : W := v4 + v3
  let v6 : W := w2 * w12
  let v7 : W := v6 + v5
  let v8 : W := w1 * w11
  let v9 : W := v8 + v7
  let v10 : W := w4 * w10
  let v11 : W := v10 + v9
  let v12 : W := UInt256.mulMod w6 w9 w14
  let v13 : W := UInt256.mulMod w7 w8 w14
  let v14 : W := v13 + v12
  let v15 : W := v14 + w0
  let v16 : W := UInt256.mulMod w3 w13 w14
  let v17 : W := v16 + v15
  let v18 : W := UInt256.mulMod w2 w12 w14
  let v19 : W := v18 + v17
  let v20 : W := UInt256.mulMod w1 w11 w14
  let v21 : W := v20 + v19
  let v22 : W := UInt256.mulMod w4 w10 w14
  let v23 : W := v22 + v21
  let v24 : W := UInt256.land (N 1766847064778384329583297500742918515827483896875618958121606201292619775) v11
  let v25 : W := v23 - v24
  let v26 : W := w14 + v25
  let v27 : W := UInt256.mulMod (N 2048) v26 w14
  have h0 : runInstructions stage5Part0Program {s with pc := N 8919,memory := s.memory,stack := w0::w1::w2::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::w16::w17::rest} = some {s with pc := N 8927,memory := s.memory,stack := v2::w0::w0::w1::w2::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::w16::w17::rest} := by
    simpa only [stage5Part0Model,v0,v1,v2] using stage5Part0_run ({s with memory := s.memory}) w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 rest hcap hact
  have h1 : runInstructions stage5Part1Program {s with pc := N 8927,memory := s.memory,stack := v2::w0::w0::w1::w2::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::w16::w17::rest} = some {s with pc := N 8935,memory := s.memory,stack := v6::v5::w0::w1::w2::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::w16::w17::rest} := by
    simpa only [stage5Part1Model,v3,v4,v5,v6] using stage5Part1_run ({s with memory := s.memory}) v2 w0 w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 rest hcap hact
  have h2 : runInstructions stage5Part2Program {s with pc := N 8935,memory := s.memory,stack := v6::v5::w0::w1::w2::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::w16::w17::rest} = some {s with pc := N 8943,memory := s.memory,stack := v10::v9::w0::w1::w2::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::w16::w17::rest} := by
    simpa only [stage5Part2Model,v7,v8,v9,v10] using stage5Part2_run ({s with memory := s.memory}) v6 v5 w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 rest hcap hact
  have h3 : runInstructions stage5Part3Program {s with pc := N 8943,memory := s.memory,stack := v10::v9::w0::w1::w2::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::w16::w17::rest} = some {s with pc := N 8951,memory := s.memory,stack := w14::v12::w0::v11::w1::w2::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::w16::w17::rest} := by
    simpa only [stage5Part3Model,v11,v12] using stage5Part3_run ({s with memory := s.memory}) v10 v9 w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 rest hcap hact
  have h4 : runInstructions stage5Part4Program {s with pc := N 8951,memory := s.memory,stack := w14::v12::w0::v11::w1::w2::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::w16::w17::rest} = some {s with pc := N 8959,memory := s.memory,stack := w3::w13::w14::v15::v11::w1::w2::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::w16::w17::rest} := by
    simpa only [stage5Part4Model,v13,v14,v15] using stage5Part4_run ({s with memory := s.memory}) w14 v12 w0 v11 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 rest hcap hact
  have h5 : runInstructions stage5Part5Program {s with pc := N 8959,memory := s.memory,stack := w3::w13::w14::v15::v11::w1::w2::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::w16::w17::rest} = some {s with pc := N 8967,memory := s.memory,stack := w14::v19::v11::w1::w2::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::w16::w17::rest} := by
    simpa only [stage5Part5Model,v16,v17,v18,v19] using stage5Part5_run ({s with memory := s.memory}) w3 w13 w14 v15 v11 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 rest hcap hact
  have h6 : runInstructions stage5Part6Program {s with pc := N 8967,memory := s.memory,stack := w14::v19::v11::w1::w2::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::w16::w17::rest} = some {s with pc := N 8975,memory := s.memory,stack := v22::v21::v11::w1::w2::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::w16::w17::rest} := by
    simpa only [stage5Part6Model,v20,v21,v22] using stage5Part6_run ({s with memory := s.memory}) w14 v19 v11 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 rest hcap hact
  have h7 : runInstructions stage5Part7Program {s with pc := N 8975,memory := s.memory,stack := v22::v21::v11::w1::w2::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::w16::w17::rest} = some {s with pc := N 9013,memory := s.memory,stack := w14::v24::v23::w1::w2::w3::w4::v24::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::w16::w17::rest} := by
    simpa only [stage5Part7Model,v23,v24] using stage5Part7_run ({s with memory := s.memory}) v22 v21 v11 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 rest hcap hact
  have h8 : runInstructions stage5Part8Program {s with pc := N 9013,memory := s.memory,stack := w14::v24::v23::w1::w2::w3::w4::v24::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::w16::w17::rest} = some {s with pc := N 9021,memory := s.memory,stack := v27::w1::w2::w3::w4::v24::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::w16::w17::rest} := by
    simpa only [stage5Part8Model,v25,v26,v27] using stage5Part8_run ({s with memory := s.memory}) w14 v24 v23 w1 w2 w3 w4 v24 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 rest hcap hact
  exact (runInstructions_append_some _ _ _ _ _ h0 (runInstructions_append_some _ _ _ _ _ h1 (runInstructions_append_some _ _ _ _ _ h2 (runInstructions_append_some _ _ _ _ _ h3 (runInstructions_append_some _ _ _ _ _ h4 (runInstructions_append_some _ _ _ _ _ h5 (runInstructions_append_some _ _ _ _ _ h6 (runInstructions_append_some _ _ _ _ _ h7 h8))))))))
def stage6Part0Program : List Instr :=
  [.op (.Dup dA0),
   .op (.Dup dA10),
   .op (.Dup dA9),
   .op .MUL,
   .op .ADD,
   .op (.Dup dA9),
   .op (.Dup dA0),
   .op .MUL]
def stage6Part0Model (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 : W) (rest : List W) : State :=
  let v0 : W := w7 * w9
  let v1 : W := v0 + w0
  let v2 : W := w8 * w8
  {s with pc := N 9029,memory := s.memory,stack := v2::v1::w0::w1::w2::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::w16::w17::rest}
theorem stage6Part0_run (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions stage6Part0Program {s with pc := N 9021,memory := s.memory,stack := w0::w1::w2::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::w16::w17::rest} = some (stage6Part0Model s w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 63) : rest.length+j < 1024 := by omega
  simp [hz,hzn,stage6Part0Program,stage6Part0Model,runInstructions,runInstr,List.exchange,succ_ofNat_mod,ofNat_add_mod,Nat.add_assoc,State.activeWordsAfterUInt256,literal_eq_ofNat,capacity]
def stage6Part1Program : List Instr :=
  [.op .ADD,
   .op (.Dup dA14),
   .op (.Dup dA4),
   .op .MUL,
   .op .ADD,
   .op (.Dup dA13),
   .op (.Dup dA3),
   .op .MUL]
def stage6Part1Model (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 : W) (rest : List W) : State :=
  let v0 : W := w0 + w1
  let v1 : W := w4 * w15
  let v2 : W := v1 + v0
  let v3 : W := w3 * w14
  {s with pc := N 9037,memory := s.memory,stack := v3::v2::w2::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::w16::w17::w18::w19::rest}
theorem stage6Part1_run (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions stage6Part1Program {s with pc := N 9029,memory := s.memory,stack := w0::w1::w2::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::w16::w17::w18::w19::rest} = some (stage6Part1Model s w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 63) : rest.length+j < 1024 := by omega
  simp [hz,hzn,stage6Part1Program,stage6Part1Model,runInstructions,runInstr,List.exchange,succ_ofNat_mod,ofNat_add_mod,Nat.add_assoc,State.activeWordsAfterUInt256,literal_eq_ofNat,capacity]
def stage6Part2Program : List Instr :=
  [.op .ADD,
   .op (.Dup dA12),
   .op (.Dup dA6),
   .op .MUL,
   .op .ADD,
   .op (.Swap sA0),
   .op (.Dup dA15),
   .op (.Dup dA11)]
def stage6Part2Model (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 : W) (rest : List W) : State :=
  let v0 : W := w0 + w1
  let v1 : W := w6 * w13
  let v2 : W := v1 + v0
  {s with pc := N 9045,memory := s.memory,stack := w11::w16::w2::v2::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::w16::w17::w18::w19::rest}
theorem stage6Part2_run (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions stage6Part2Program {s with pc := N 9037,memory := s.memory,stack := w0::w1::w2::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::w16::w17::w18::w19::rest} = some (stage6Part2Model s w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 63) : rest.length+j < 1024 := by omega
  simp [hz,hzn,stage6Part2Program,stage6Part2Model,runInstructions,runInstr,List.exchange,succ_ofNat_mod,ofNat_add_mod,Nat.add_assoc,State.activeWordsAfterUInt256,literal_eq_ofNat,capacity]
def stage6Part3Program : List Instr :=
  [.op (.Dup dA10),
   .op .MULMOD,
   .op .ADD,
   .op (.Dup dA15),
   .op (.Dup dA10),
   .op (.Dup dA0),
   .op (.Dup dA0),
   .op .ADD]
def stage6Part3Model (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 w20 : W) (rest : List W) : State :=
  let v0 : W := UInt256.mulMod w10 w0 w1
  let v1 : W := v0 + w2
  let v2 : W := w11 + w11
  {s with pc := N 9053,memory := s.memory,stack := v2::w11::w17::v1::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::w16::w17::w18::w19::w20::rest}
theorem stage6Part3_run (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 w20 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions stage6Part3Program {s with pc := N 9045,memory := s.memory,stack := w0::w1::w2::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::w16::w17::w18::w19::w20::rest} = some (stage6Part3Model s w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 w20 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 63) : rest.length+j < 1024 := by omega
  simp [hz,hzn,stage6Part3Program,stage6Part3Model,runInstructions,runInstr,List.exchange,succ_ofNat_mod,ofNat_add_mod,Nat.add_assoc,State.activeWordsAfterUInt256,literal_eq_ofNat,capacity]
def stage6Part4Program : List Instr :=
  [.op (.Swap sA11),
   .op .MULMOD,
   .op .ADD,
   .op (.Dup dA15),
   .op (.Dup dA15),
   .op (.Dup dA5),
   .op .MULMOD,
   .op .ADD]
def stage6Part4Model (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 w20 w21 : W) (rest : List W) : State :=
  let v0 : W := UInt256.mulMod w12 w1 w2
  let v1 : W := v0 + w3
  let v2 : W := UInt256.mulMod w6 w17 w18
  let v3 : W := v2 + v1
  {s with pc := N 9061,memory := s.memory,stack := v3::w4::w5::w6::w7::w8::w9::w10::w11::w0::w13::w14::w15::w16::w17::w18::w19::w20::w21::rest}
theorem stage6Part4_run (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 w20 w21 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions stage6Part4Program {s with pc := N 9053,memory := s.memory,stack := w0::w1::w2::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::w16::w17::w18::w19::w20::w21::rest} = some (stage6Part4Model s w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 w20 w21 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 63) : rest.length+j < 1024 := by omega
  simp [hz,hzn,stage6Part4Program,stage6Part4Model,runInstructions,runInstr,List.exchange,succ_ofNat_mod,ofNat_add_mod,Nat.add_assoc,State.activeWordsAfterUInt256,literal_eq_ofNat,capacity]
def stage6Part5Program : List Instr :=
  [.op (.Dup dA15),
   .op (.Dup dA14),
   .op (.Dup dA4),
   .op .MULMOD,
   .op .ADD,
   .op (.Dup dA15),
   .op (.Dup dA13),
   .op (.Dup dA7)]
def stage6Part5Model (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 : W) (rest : List W) : State :=
  let v0 : W := UInt256.mulMod w2 w13 w15
  let v1 : W := v0 + w0
  {s with pc := N 9069,memory := s.memory,stack := w5::w12::w15::v1::w1::w2::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::w16::w17::w18::rest}
theorem stage6Part5_run (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions stage6Part5Program {s with pc := N 9061,memory := s.memory,stack := w0::w1::w2::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::w16::w17::w18::rest} = some (stage6Part5Model s w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 63) : rest.length+j < 1024 := by omega
  simp [hz,hzn,stage6Part5Program,stage6Part5Model,runInstructions,runInstr,List.exchange,succ_ofNat_mod,ofNat_add_mod,Nat.add_assoc,State.activeWordsAfterUInt256,literal_eq_ofNat,capacity]
def stage6Part6Program : List Instr :=
  [.op .MULMOD,
   .op .ADD,
   .op (.Swap sA0),
   .push 30 1766847064778384329583297500742918515827483896875618958121606201292619775,
   .op .AND,
   .op (.Dup dA0),
   .op (.Swap sA7),
   .op .POP]
def stage6Part6Model (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 w20 w21 : W) (rest : List W) : State :=
  let v0 : W := UInt256.mulMod w0 w1 w2
  let v1 : W := v0 + w3
  let v2 : W := UInt256.land (N 1766847064778384329583297500742918515827483896875618958121606201292619775) w4
  {s with pc := N 9107,memory := s.memory,stack := v2::v1::w5::w6::w7::w8::w9::v2::w11::w12::w13::w14::w15::w16::w17::w18::w19::w20::w21::rest}
theorem stage6Part6_run (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 w20 w21 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions stage6Part6Program {s with pc := N 9069,memory := s.memory,stack := w0::w1::w2::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::w16::w17::w18::w19::w20::w21::rest} = some (stage6Part6Model s w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 w20 w21 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 63) : rest.length+j < 1024 := by omega
  simp [hz,hzn,stage6Part6Program,stage6Part6Model,runInstructions,runInstr,List.exchange,succ_ofNat_mod,ofNat_add_mod,Nat.add_assoc,State.activeWordsAfterUInt256,literal_eq_ofNat,capacity]
def stage6Part7Program : List Instr :=
  [.op (.Dup dA15),
   .op (.Swap sA1),
   .op .SUB,
   .op (.Dup dA1),
   .op .ADD,
   .push 2 2048,
   .op .MULMOD]
def stage6Part7Model (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 : W) (rest : List W) : State :=
  let v0 : W := w1 - w0
  let v1 : W := w15 + v0
  let v2 : W := UInt256.mulMod (N 2048) v1 w15
  {s with pc := N 9116,memory := s.memory,stack := v2::w2::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::w16::w17::w18::rest}
theorem stage6Part7_run (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions stage6Part7Program {s with pc := N 9107,memory := s.memory,stack := w0::w1::w2::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::w16::w17::w18::rest} = some (stage6Part7Model s w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 63) : rest.length+j < 1024 := by omega
  simp [hz,hzn,stage6Part7Program,stage6Part7Model,runInstructions,runInstr,List.exchange,succ_ofNat_mod,ofNat_add_mod,Nat.add_assoc,State.activeWordsAfterUInt256,literal_eq_ofNat,capacity]
def stage6Program : List Instr := (stage6Part0Program++(stage6Part1Program++(stage6Part2Program++(stage6Part3Program++(stage6Part4Program++(stage6Part5Program++(stage6Part6Program++stage6Part7Program)))))))
def stage6Model (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 : W) (rest : List W) : State :=
  let v0 : W := w7 * w9
  let v1 : W := v0 + w0
  let v2 : W := w8 * w8
  let v3 : W := v2 + v1
  let v4 : W := w2 * w13
  let v5 : W := v4 + v3
  let v6 : W := w1 * w12
  let v7 : W := v6 + v5
  let v8 : W := w4 * w11
  let v9 : W := v8 + v7
  let v10 : W := UInt256.mulMod w7 w9 w14
  let v11 : W := v10 + w0
  let v12 : W := w8 + w8
  let v13 : W := UInt256.mulMod w8 w8 w14
  let v14 : W := v13 + v11
  let v15 : W := UInt256.mulMod w2 w13 w14
  let v16 : W := v15 + v14
  let v17 : W := UInt256.mulMod w1 w12 w14
  let v18 : W := v17 + v16
  let v19 : W := UInt256.mulMod w4 w11 w14
  let v20 : W := v19 + v18
  let v21 : W := UInt256.land (N 1766847064778384329583297500742918515827483896875618958121606201292619775) v9
  let v22 : W := v20 - v21
  let v23 : W := w14 + v22
  let v24 : W := UInt256.mulMod (N 2048) v23 w14
  {s with pc := N 9116,memory := s.memory,stack := v24::w1::w2::w3::w4::w5::v21::w7::v12::w9::w10::w11::w12::w13::w14::w15::w16::w17::rest}
theorem stage6_run (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions stage6Program {s with pc := N 9021,memory := s.memory,stack := w0::w1::w2::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::w16::w17::rest} = some (stage6Model s w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 rest) := by
  let v0 : W := w7 * w9
  let v1 : W := v0 + w0
  let v2 : W := w8 * w8
  let v3 : W := v2 + v1
  let v4 : W := w2 * w13
  let v5 : W := v4 + v3
  let v6 : W := w1 * w12
  let v7 : W := v6 + v5
  let v8 : W := w4 * w11
  let v9 : W := v8 + v7
  let v10 : W := UInt256.mulMod w7 w9 w14
  let v11 : W := v10 + w0
  let v12 : W := w8 + w8
  let v13 : W := UInt256.mulMod w8 w8 w14
  let v14 : W := v13 + v11
  let v15 : W := UInt256.mulMod w2 w13 w14
  let v16 : W := v15 + v14
  let v17 : W := UInt256.mulMod w1 w12 w14
  let v18 : W := v17 + v16
  let v19 : W := UInt256.mulMod w4 w11 w14
  let v20 : W := v19 + v18
  let v21 : W := UInt256.land (N 1766847064778384329583297500742918515827483896875618958121606201292619775) v9
  let v22 : W := v20 - v21
  let v23 : W := w14 + v22
  let v24 : W := UInt256.mulMod (N 2048) v23 w14
  have h0 : runInstructions stage6Part0Program {s with pc := N 9021,memory := s.memory,stack := w0::w1::w2::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::w16::w17::rest} = some {s with pc := N 9029,memory := s.memory,stack := v2::v1::w0::w1::w2::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::w16::w17::rest} := by
    simpa only [stage6Part0Model,v0,v1,v2] using stage6Part0_run ({s with memory := s.memory}) w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 rest hcap hact
  have h1 : runInstructions stage6Part1Program {s with pc := N 9029,memory := s.memory,stack := v2::v1::w0::w1::w2::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::w16::w17::rest} = some {s with pc := N 9037,memory := s.memory,stack := v6::v5::w0::w1::w2::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::w16::w17::rest} := by
    simpa only [stage6Part1Model,v3,v4,v5,v6] using stage6Part1_run ({s with memory := s.memory}) v2 v1 w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 rest hcap hact
  have h2 : runInstructions stage6Part2Program {s with pc := N 9037,memory := s.memory,stack := v6::v5::w0::w1::w2::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::w16::w17::rest} = some {s with pc := N 9045,memory := s.memory,stack := w9::w14::w0::v9::w1::w2::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::w16::w17::rest} := by
    simpa only [stage6Part2Model,v7,v8,v9] using stage6Part2_run ({s with memory := s.memory}) v6 v5 w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 rest hcap hact
  have h3 : runInstructions stage6Part3Program {s with pc := N 9045,memory := s.memory,stack := w9::w14::w0::v9::w1::w2::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::w16::w17::rest} = some {s with pc := N 9053,memory := s.memory,stack := v12::w8::w14::v11::v9::w1::w2::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::w16::w17::rest} := by
    simpa only [stage6Part3Model,v10,v11,v12] using stage6Part3_run ({s with memory := s.memory}) w9 w14 w0 v9 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 rest hcap hact
  have h4 : runInstructions stage6Part4Program {s with pc := N 9053,memory := s.memory,stack := v12::w8::w14::v11::v9::w1::w2::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::w16::w17::rest} = some {s with pc := N 9061,memory := s.memory,stack := v16::v9::w1::w2::w3::w4::w5::w6::w7::v12::w9::w10::w11::w12::w13::w14::w15::w16::w17::rest} := by
    simpa only [stage6Part4Model,v13,v14,v15,v16] using stage6Part4_run ({s with memory := s.memory}) v12 w8 w14 v11 v9 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 rest hcap hact
  have h5 : runInstructions stage6Part5Program {s with pc := N 9061,memory := s.memory,stack := v16::v9::w1::w2::w3::w4::w5::w6::w7::v12::w9::w10::w11::w12::w13::w14::w15::w16::w17::rest} = some {s with pc := N 9069,memory := s.memory,stack := w4::w11::w14::v18::v9::w1::w2::w3::w4::w5::w6::w7::v12::w9::w10::w11::w12::w13::w14::w15::w16::w17::rest} := by
    simpa only [stage6Part5Model,v17,v18] using stage6Part5_run ({s with memory := s.memory}) v16 v9 w1 w2 w3 w4 w5 w6 w7 v12 w9 w10 w11 w12 w13 w14 w15 w16 w17 rest hcap hact
  have h6 : runInstructions stage6Part6Program {s with pc := N 9069,memory := s.memory,stack := w4::w11::w14::v18::v9::w1::w2::w3::w4::w5::w6::w7::v12::w9::w10::w11::w12::w13::w14::w15::w16::w17::rest} = some {s with pc := N 9107,memory := s.memory,stack := v21::v20::w1::w2::w3::w4::w5::v21::w7::v12::w9::w10::w11::w12::w13::w14::w15::w16::w17::rest} := by
    simpa only [stage6Part6Model,v19,v20,v21] using stage6Part6_run ({s with memory := s.memory}) w4 w11 w14 v18 v9 w1 w2 w3 w4 w5 w6 w7 v12 w9 w10 w11 w12 w13 w14 w15 w16 w17 rest hcap hact
  have h7 : runInstructions stage6Part7Program {s with pc := N 9107,memory := s.memory,stack := v21::v20::w1::w2::w3::w4::w5::v21::w7::v12::w9::w10::w11::w12::w13::w14::w15::w16::w17::rest} = some {s with pc := N 9116,memory := s.memory,stack := v24::w1::w2::w3::w4::w5::v21::w7::v12::w9::w10::w11::w12::w13::w14::w15::w16::w17::rest} := by
    simpa only [stage6Part7Model,v22,v23,v24] using stage6Part7_run ({s with memory := s.memory}) v21 v20 w1 w2 w3 w4 w5 v21 w7 v12 w9 w10 w11 w12 w13 w14 w15 w16 w17 rest hcap hact
  exact (runInstructions_append_some _ _ _ _ _ h0 (runInstructions_append_some _ _ _ _ _ h1 (runInstructions_append_some _ _ _ _ _ h2 (runInstructions_append_some _ _ _ _ _ h3 (runInstructions_append_some _ _ _ _ _ h4 (runInstructions_append_some _ _ _ _ _ h5 (runInstructions_append_some _ _ _ _ _ h6 h7)))))))
def stage7Part0Program : List Instr :=
  [.op (.Dup dA0),
   .op (.Dup dA10),
   .op (.Dup dA10),
   .op .MUL,
   .op .ADD,
   .op (.Dup dA14),
   .op (.Dup dA3),
   .op .MUL]
def stage7Part0Model (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 : W) (rest : List W) : State :=
  let v0 : W := w8 * w9
  let v1 : W := v0 + w0
  let v2 : W := w1 * w13
  {s with pc := N 9124,memory := s.memory,stack := v2::v1::w0::w1::w2::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::w16::w17::rest}
theorem stage7Part0_run (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions stage7Part0Program {s with pc := N 9116,memory := s.memory,stack := w0::w1::w2::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::w16::w17::rest} = some (stage7Part0Model s w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 63) : rest.length+j < 1024 := by omega
  simp [hz,hzn,stage7Part0Program,stage7Part0Model,runInstructions,runInstr,List.exchange,succ_ofNat_mod,ofNat_add_mod,Nat.add_assoc,State.activeWordsAfterUInt256,literal_eq_ofNat,capacity]
def stage7Part1Program : List Instr :=
  [.op .ADD,
   .op (.Dup dA13),
   .op (.Dup dA6),
   .op .MUL,
   .op .ADD,
   .push 30 1766847064778384329583297500742918515827483896875618958121606201292619775,
   .op .AND,
   .op (.Swap sA7)]
def stage7Part1Model (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 : W) (rest : List W) : State :=
  let v0 : W := w0 + w1
  let v1 : W := w6 * w14
  let v2 : W := v1 + v0
  let v3 : W := UInt256.land (N 1766847064778384329583297500742918515827483896875618958121606201292619775) v2
  {s with pc := N 9162,memory := s.memory,stack := w9::w2::w3::w4::w5::w6::w7::w8::v3::w10::w11::w12::w13::w14::w15::w16::w17::w18::w19::rest}
theorem stage7Part1_run (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions stage7Part1Program {s with pc := N 9124,memory := s.memory,stack := w0::w1::w2::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::w16::w17::w18::w19::rest} = some (stage7Part1Model s w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 63) : rest.length+j < 1024 := by omega
  simp [hz,hzn,stage7Part1Program,stage7Part1Model,runInstructions,runInstr,List.exchange,succ_ofNat_mod,ofNat_add_mod,Nat.add_assoc,State.activeWordsAfterUInt256,literal_eq_ofNat,capacity]
def stage7Part2Program : List Instr :=
  [.op .POP,
   .op (.Dup dA14),
   .op (.Dup dA9),
   .op (.Dup dA11),
   .op .MULMOD,
   .op .ADD,
   .op (.Dup dA14),
   .op (.Dup dA2)]
def stage7Part2Model (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 : W) (rest : List W) : State :=
  let v0 : W := UInt256.mulMod w10 w9 w15
  let v1 : W := v0 + w1
  {s with pc := N 9170,memory := s.memory,stack := w2::w15::v1::w2::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::w16::w17::w18::rest}
theorem stage7Part2_run (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions stage7Part2Program {s with pc := N 9162,memory := s.memory,stack := w0::w1::w2::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::w16::w17::w18::rest} = some (stage7Part2Model s w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 63) : rest.length+j < 1024 := by omega
  simp [hz,hzn,stage7Part2Program,stage7Part2Model,runInstructions,runInstr,List.exchange,succ_ofNat_mod,ofNat_add_mod,Nat.add_assoc,State.activeWordsAfterUInt256,literal_eq_ofNat,capacity]
def stage7Part3Program : List Instr :=
  [.op (.Dup dA15),
   .op .MULMOD,
   .op .ADD,
   .op (.Dup dA14),
   .op (.Dup dA5),
   .op (.Dup dA14),
   .op .MULMOD,
   .op .ADD]
def stage7Part3Model (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 : W) (rest : List W) : State :=
  let v0 : W := UInt256.mulMod w15 w0 w1
  let v1 : W := v0 + w2
  let v2 : W := UInt256.mulMod w14 w6 w16
  let v3 : W := v2 + v1
  {s with pc := N 9178,memory := s.memory,stack := v3::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::w16::w17::w18::w19::rest}
theorem stage7Part3_run (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions stage7Part3Program {s with pc := N 9170,memory := s.memory,stack := w0::w1::w2::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::w16::w17::w18::w19::rest} = some (stage7Part3Model s w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 63) : rest.length+j < 1024 := by omega
  simp [hz,hzn,stage7Part3Program,stage7Part3Model,runInstructions,runInstr,List.exchange,succ_ofNat_mod,ofNat_add_mod,Nat.add_assoc,State.activeWordsAfterUInt256,literal_eq_ofNat,capacity]
def stage7Part4Program : List Instr :=
  [.push 2 2048,
   .op (.Dup dA15),
   .op (.Dup dA9),
   .op (.Dup dA1),
   .op (.Swap sA3),
   .op .SUB,
   .op .ADD,
   .op .MULMOD]
def stage7Part4Model (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 : W) (rest : List W) : State :=
  let v0 : W := w0 - w7
  let v1 : W := v0 + w14
  let v2 : W := UInt256.mulMod v1 (N 2048) w14
  {s with pc := N 9188,memory := s.memory,stack := v2::w1::w2::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::w16::w17::rest}
theorem stage7Part4_run (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions stage7Part4Program {s with pc := N 9178,memory := s.memory,stack := w0::w1::w2::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::w16::w17::rest} = some (stage7Part4Model s w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 63) : rest.length+j < 1024 := by omega
  simp [hz,hzn,stage7Part4Program,stage7Part4Model,runInstructions,runInstr,List.exchange,succ_ofNat_mod,ofNat_add_mod,Nat.add_assoc,State.activeWordsAfterUInt256,literal_eq_ofNat,capacity]
def stage7Program : List Instr := (stage7Part0Program++(stage7Part1Program++(stage7Part2Program++(stage7Part3Program++stage7Part4Program))))
def stage7Model (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 : W) (rest : List W) : State :=
  let v0 : W := w8 * w9
  let v1 : W := v0 + w0
  let v2 : W := w1 * w13
  let v3 : W := v2 + v1
  let v4 : W := w4 * w12
  let v5 : W := v4 + v3
  let v6 : W := UInt256.land (N 1766847064778384329583297500742918515827483896875618958121606201292619775) v5
  let v7 : W := UInt256.mulMod w9 w8 w14
  let v8 : W := v7 + w0
  let v9 : W := UInt256.mulMod w13 w1 w14
  let v10 : W := v9 + v8
  let v11 : W := UInt256.mulMod w12 w4 w14
  let v12 : W := v11 + v10
  let v13 : W := v12 - v6
  let v14 : W := v13 + w14
  let v15 : W := UInt256.mulMod v14 (N 2048) w14
  {s with pc := N 9188,memory := s.memory,stack := v15::w1::w2::w3::w4::w5::w6::v6::w8::w9::w10::w11::w12::w13::w14::w15::w16::w17::rest}
theorem stage7_run (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions stage7Program {s with pc := N 9116,memory := s.memory,stack := w0::w1::w2::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::w16::w17::rest} = some (stage7Model s w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 rest) := by
  let v0 : W := w8 * w9
  let v1 : W := v0 + w0
  let v2 : W := w1 * w13
  let v3 : W := v2 + v1
  let v4 : W := w4 * w12
  let v5 : W := v4 + v3
  let v6 : W := UInt256.land (N 1766847064778384329583297500742918515827483896875618958121606201292619775) v5
  let v7 : W := UInt256.mulMod w9 w8 w14
  let v8 : W := v7 + w0
  let v9 : W := UInt256.mulMod w13 w1 w14
  let v10 : W := v9 + v8
  let v11 : W := UInt256.mulMod w12 w4 w14
  let v12 : W := v11 + v10
  let v13 : W := v12 - v6
  let v14 : W := v13 + w14
  let v15 : W := UInt256.mulMod v14 (N 2048) w14
  have h0 : runInstructions stage7Part0Program {s with pc := N 9116,memory := s.memory,stack := w0::w1::w2::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::w16::w17::rest} = some {s with pc := N 9124,memory := s.memory,stack := v2::v1::w0::w1::w2::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::w16::w17::rest} := by
    simpa only [stage7Part0Model,v0,v1,v2] using stage7Part0_run ({s with memory := s.memory}) w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 rest hcap hact
  have h1 : runInstructions stage7Part1Program {s with pc := N 9124,memory := s.memory,stack := v2::v1::w0::w1::w2::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::w16::w17::rest} = some {s with pc := N 9162,memory := s.memory,stack := w7::w0::w1::w2::w3::w4::w5::w6::v6::w8::w9::w10::w11::w12::w13::w14::w15::w16::w17::rest} := by
    simpa only [stage7Part1Model,v3,v4,v5,v6] using stage7Part1_run ({s with memory := s.memory}) v2 v1 w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 rest hcap hact
  have h2 : runInstructions stage7Part2Program {s with pc := N 9162,memory := s.memory,stack := w7::w0::w1::w2::w3::w4::w5::w6::v6::w8::w9::w10::w11::w12::w13::w14::w15::w16::w17::rest} = some {s with pc := N 9170,memory := s.memory,stack := w1::w14::v8::w1::w2::w3::w4::w5::w6::v6::w8::w9::w10::w11::w12::w13::w14::w15::w16::w17::rest} := by
    simpa only [stage7Part2Model,v7,v8] using stage7Part2_run ({s with memory := s.memory}) w7 w0 w1 w2 w3 w4 w5 w6 v6 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 rest hcap hact
  have h3 : runInstructions stage7Part3Program {s with pc := N 9170,memory := s.memory,stack := w1::w14::v8::w1::w2::w3::w4::w5::w6::v6::w8::w9::w10::w11::w12::w13::w14::w15::w16::w17::rest} = some {s with pc := N 9178,memory := s.memory,stack := v12::w1::w2::w3::w4::w5::w6::v6::w8::w9::w10::w11::w12::w13::w14::w15::w16::w17::rest} := by
    simpa only [stage7Part3Model,v9,v10,v11,v12] using stage7Part3_run ({s with memory := s.memory}) w1 w14 v8 w1 w2 w3 w4 w5 w6 v6 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 rest hcap hact
  have h4 : runInstructions stage7Part4Program {s with pc := N 9178,memory := s.memory,stack := v12::w1::w2::w3::w4::w5::w6::v6::w8::w9::w10::w11::w12::w13::w14::w15::w16::w17::rest} = some {s with pc := N 9188,memory := s.memory,stack := v15::w1::w2::w3::w4::w5::w6::v6::w8::w9::w10::w11::w12::w13::w14::w15::w16::w17::rest} := by
    simpa only [stage7Part4Model,v13,v14,v15] using stage7Part4_run ({s with memory := s.memory}) v12 w1 w2 w3 w4 w5 w6 v6 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 rest hcap hact
  exact (runInstructions_append_some _ _ _ _ _ h0 (runInstructions_append_some _ _ _ _ _ h1 (runInstructions_append_some _ _ _ _ _ h2 (runInstructions_append_some _ _ _ _ _ h3 h4))))
def stage8Part0Program : List Instr :=
  [.op (.Dup dA0),
   .op (.Dup dA10),
   .op (.Dup dA0),
   .op .MUL,
   .op .ADD,
   .op (.Dup dA5),
   .op (.Dup dA15),
   .op .MUL]
def stage8Part0Model (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 : W) (rest : List W) : State :=
  let v0 : W := w9 * w9
  let v1 : W := v0 + w0
  let v2 : W := w13 * w4
  {s with pc := N 9196,memory := s.memory,stack := v2::v1::w0::w1::w2::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::w16::w17::rest}
theorem stage8Part0_run (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions stage8Part0Program {s with pc := N 9188,memory := s.memory,stack := w0::w1::w2::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::w16::w17::rest} = some (stage8Part0Model s w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 63) : rest.length+j < 1024 := by omega
  simp [hz,hzn,stage8Part0Program,stage8Part0Model,runInstructions,runInstr,List.exchange,succ_ofNat_mod,ofNat_add_mod,Nat.add_assoc,State.activeWordsAfterUInt256,literal_eq_ofNat,capacity]
def stage8Part1Program : List Instr :=
  [.op .ADD,
   .push 30 1766847064778384329583297500742918515827483896875618958121606201292619775,
   .op .AND,
   .op (.Swap sA8),
   .op .POP,
   .op (.Dup dA14),
   .op (.Dup dA10),
   .op (.Dup dA0)]
def stage8Part1Model (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 : W) (rest : List W) : State :=
  let v0 : W := w0 + w1
  let v1 : W := UInt256.land (N 1766847064778384329583297500742918515827483896875618958121606201292619775) v0
  {s with pc := N 9234,memory := s.memory,stack := w11::w11::w16::w2::w3::w4::w5::w6::w7::w8::w9::v1::w11::w12::w13::w14::w15::w16::w17::w18::w19::rest}
theorem stage8Part1_run (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions stage8Part1Program {s with pc := N 9196,memory := s.memory,stack := w0::w1::w2::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::w16::w17::w18::w19::rest} = some (stage8Part1Model s w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 63) : rest.length+j < 1024 := by omega
  simp [hz,hzn,stage8Part1Program,stage8Part1Model,runInstructions,runInstr,List.exchange,succ_ofNat_mod,ofNat_add_mod,Nat.add_assoc,State.activeWordsAfterUInt256,literal_eq_ofNat,capacity]
def stage8Part2Program : List Instr :=
  [.op .MULMOD,
   .op .ADD,
   .op (.Dup dA14),
   .op (.Dup dA5),
   .op (.Dup dA15),
   .op .MULMOD,
   .op .ADD,
   .push 2 2048]
def stage8Part2Model (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 w20 : W) (rest : List W) : State :=
  let v0 : W := UInt256.mulMod w0 w1 w2
  let v1 : W := v0 + w3
  let v2 : W := UInt256.mulMod w16 w7 w17
  let v3 : W := v2 + v1
  {s with pc := N 9244,memory := s.memory,stack := (N 2048)::v3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::w16::w17::w18::w19::w20::rest}
theorem stage8Part2_run (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 w20 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions stage8Part2Program {s with pc := N 9234,memory := s.memory,stack := w0::w1::w2::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::w16::w17::w18::w19::w20::rest} = some (stage8Part2Model s w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 w20 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 63) : rest.length+j < 1024 := by omega
  simp [hz,hzn,stage8Part2Program,stage8Part2Model,runInstructions,runInstr,List.exchange,succ_ofNat_mod,ofNat_add_mod,Nat.add_assoc,State.activeWordsAfterUInt256,literal_eq_ofNat,capacity]
def stage8Part3Program : List Instr :=
  [.op (.Dup dA15),
   .op (.Dup dA10),
   .op (.Dup dA1),
   .op (.Swap sA3),
   .op .SUB,
   .op .ADD,
   .op .MULMOD]
def stage8Part3Model (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 : W) (rest : List W) : State :=
  let v0 : W := w1 - w9
  let v1 : W := v0 + w15
  let v2 : W := UInt256.mulMod v1 w0 w15
  {s with pc := N 9251,memory := s.memory,stack := v2::w2::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::w16::w17::w18::rest}
theorem stage8Part3_run (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions stage8Part3Program {s with pc := N 9244,memory := s.memory,stack := w0::w1::w2::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::w16::w17::w18::rest} = some (stage8Part3Model s w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 63) : rest.length+j < 1024 := by omega
  simp [hz,hzn,stage8Part3Program,stage8Part3Model,runInstructions,runInstr,List.exchange,succ_ofNat_mod,ofNat_add_mod,Nat.add_assoc,State.activeWordsAfterUInt256,literal_eq_ofNat,capacity]
def stage8Program : List Instr := (stage8Part0Program++(stage8Part1Program++(stage8Part2Program++stage8Part3Program)))
def stage8Model (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 : W) (rest : List W) : State :=
  let v0 : W := w9 * w9
  let v1 : W := v0 + w0
  let v2 : W := w13 * w4
  let v3 : W := v2 + v1
  let v4 : W := UInt256.land (N 1766847064778384329583297500742918515827483896875618958121606201292619775) v3
  let v5 : W := UInt256.mulMod w9 w9 w14
  let v6 : W := v5 + w0
  let v7 : W := UInt256.mulMod w13 w4 w14
  let v8 : W := v7 + v6
  let v9 : W := v8 - v4
  let v10 : W := v9 + w14
  let v11 : W := UInt256.mulMod v10 (N 2048) w14
  {s with pc := N 9251,memory := s.memory,stack := v11::w1::w2::w3::w4::w5::w6::w7::v4::w9::w10::w11::w12::w13::w14::w15::w16::w17::rest}
theorem stage8_run (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions stage8Program {s with pc := N 9188,memory := s.memory,stack := w0::w1::w2::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::w16::w17::rest} = some (stage8Model s w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 rest) := by
  let v0 : W := w9 * w9
  let v1 : W := v0 + w0
  let v2 : W := w13 * w4
  let v3 : W := v2 + v1
  let v4 : W := UInt256.land (N 1766847064778384329583297500742918515827483896875618958121606201292619775) v3
  let v5 : W := UInt256.mulMod w9 w9 w14
  let v6 : W := v5 + w0
  let v7 : W := UInt256.mulMod w13 w4 w14
  let v8 : W := v7 + v6
  let v9 : W := v8 - v4
  let v10 : W := v9 + w14
  let v11 : W := UInt256.mulMod v10 (N 2048) w14
  have h0 : runInstructions stage8Part0Program {s with pc := N 9188,memory := s.memory,stack := w0::w1::w2::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::w16::w17::rest} = some {s with pc := N 9196,memory := s.memory,stack := v2::v1::w0::w1::w2::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::w16::w17::rest} := by
    simpa only [stage8Part0Model,v0,v1,v2] using stage8Part0_run ({s with memory := s.memory}) w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 rest hcap hact
  have h1 : runInstructions stage8Part1Program {s with pc := N 9196,memory := s.memory,stack := v2::v1::w0::w1::w2::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::w16::w17::rest} = some {s with pc := N 9234,memory := s.memory,stack := w9::w9::w14::w0::w1::w2::w3::w4::w5::w6::w7::v4::w9::w10::w11::w12::w13::w14::w15::w16::w17::rest} := by
    simpa only [stage8Part1Model,v3,v4] using stage8Part1_run ({s with memory := s.memory}) v2 v1 w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 rest hcap hact
  have h2 : runInstructions stage8Part2Program {s with pc := N 9234,memory := s.memory,stack := w9::w9::w14::w0::w1::w2::w3::w4::w5::w6::w7::v4::w9::w10::w11::w12::w13::w14::w15::w16::w17::rest} = some {s with pc := N 9244,memory := s.memory,stack := (N 2048)::v8::w1::w2::w3::w4::w5::w6::w7::v4::w9::w10::w11::w12::w13::w14::w15::w16::w17::rest} := by
    simpa only [stage8Part2Model,v5,v6,v7,v8] using stage8Part2_run ({s with memory := s.memory}) w9 w9 w14 w0 w1 w2 w3 w4 w5 w6 w7 v4 w9 w10 w11 w12 w13 w14 w15 w16 w17 rest hcap hact
  have h3 : runInstructions stage8Part3Program {s with pc := N 9244,memory := s.memory,stack := (N 2048)::v8::w1::w2::w3::w4::w5::w6::w7::v4::w9::w10::w11::w12::w13::w14::w15::w16::w17::rest} = some {s with pc := N 9251,memory := s.memory,stack := v11::w1::w2::w3::w4::w5::w6::w7::v4::w9::w10::w11::w12::w13::w14::w15::w16::w17::rest} := by
    simpa only [stage8Part3Model,v9,v10,v11] using stage8Part3_run ({s with memory := s.memory}) (N 2048) v8 w1 w2 w3 w4 w5 w6 w7 v4 w9 w10 w11 w12 w13 w14 w15 w16 w17 rest hcap hact
  exact (runInstructions_append_some _ _ _ _ _ h0 (runInstructions_append_some _ _ _ _ _ h1 (runInstructions_append_some _ _ _ _ _ h2 h3)))
def stage9Part0Program : List Instr :=
  [.op (.Swap sA8),
   .op .POP,
   .op .POP,
   .op .POP,
   .op .POP,
   .op .POP,
   .push 1 1,
   .op (.Dup dA13)]
def stage9Part0Model (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 : W) (rest : List W) : State :=
  {s with pc := N 9260,memory := s.memory,stack := w17::(N 1)::w5::w6::w7::w8::w0::w10::w11::w12::w13::w14::w15::w16::w17::rest}
theorem stage9Part0_run (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions stage9Part0Program {s with pc := N 9251,memory := s.memory,stack := w0::w1::w2::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::w16::w17::rest} = some (stage9Part0Model s w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 63) : rest.length+j < 1024 := by omega
  simp [hz,hzn,stage9Part0Program,stage9Part0Model,runInstructions,runInstr,List.exchange,succ_ofNat_mod,ofNat_add_mod,Nat.add_assoc,State.activeWordsAfterUInt256,literal_eq_ofNat,capacity]
def stage9Part1Program : List Instr :=
  [.op .SUB,
   .op (.Swap sA12)]
def stage9Part1Model (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 : W) (rest : List W) : State :=
  let v0 : W := w0 - w1
  {s with pc := N 9262,memory := s.memory,stack := w14::w2::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::v0::rest}
theorem stage9Part1_run (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions stage9Part1Program {s with pc := N 9260,memory := s.memory,stack := w0::w1::w2::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::rest} = some (stage9Part1Model s w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 63) : rest.length+j < 1024 := by omega
  simp [hz,hzn,stage9Part1Program,stage9Part1Model,runInstructions,runInstr,List.exchange,succ_ofNat_mod,ofNat_add_mod,Nat.add_assoc,State.activeWordsAfterUInt256,literal_eq_ofNat,capacity]
def stage9Program : List Instr := (stage9Part0Program++stage9Part1Program)
def stage9Model (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 : W) (rest : List W) : State :=
  let v0 : W := w17 - (N 1)
  {s with pc := N 9262,memory := s.memory,stack := w17::w5::w6::w7::w8::w0::w10::w11::w12::w13::w14::w15::w16::v0::rest}
theorem stage9_run (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions stage9Program {s with pc := N 9251,memory := s.memory,stack := w0::w1::w2::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::w16::w17::rest} = some (stage9Model s w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 rest) := by
  let v0 : W := w17 - (N 1)
  have h0 : runInstructions stage9Part0Program {s with pc := N 9251,memory := s.memory,stack := w0::w1::w2::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::w16::w17::rest} = some {s with pc := N 9260,memory := s.memory,stack := w17::(N 1)::w5::w6::w7::w8::w0::w10::w11::w12::w13::w14::w15::w16::w17::rest} := by
    simpa only [stage9Part0Model] using stage9Part0_run ({s with memory := s.memory}) w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 rest hcap hact
  have h1 : runInstructions stage9Part1Program {s with pc := N 9260,memory := s.memory,stack := w17::(N 1)::w5::w6::w7::w8::w0::w10::w11::w12::w13::w14::w15::w16::w17::rest} = some {s with pc := N 9262,memory := s.memory,stack := w17::w5::w6::w7::w8::w0::w10::w11::w12::w13::w14::w15::w16::v0::rest} := by
    simpa only [stage9Part1Model,v0] using stage9Part1_run ({s with memory := s.memory}) w17 (N 1) w5 w6 w7 w8 w0 w10 w11 w12 w13 w14 w15 w16 w17 rest hcap hact
  exact (runInstructions_append_some _ _ _ _ _ h0 h1)
end R5LimbCacheRaw
