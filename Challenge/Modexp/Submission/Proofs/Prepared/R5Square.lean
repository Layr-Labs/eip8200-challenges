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
namespace NextR5Columns
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
def stage0Part0Model (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 : W) (rest : List W) : State :=
  let v0 : W := (w0) * (w0)
  let v1 : W := (w10) * (v0)
  let v2 : W := UInt256.shiftRight (v1) (N 16)
  {s with pc := N 4027, stack := (v2) :: (w0) :: (w1) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: rest}
theorem stage0Part0_run (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions stage0Part0Program {s with pc := N 4018, stack := (w0) :: (w1) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: rest} =
      some (stage0Part0Model s w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 63) : rest.length + j < 1024 := by omega
  simp [hz, hzn, stage0Part0Program, stage0Part0Model, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, capacity]

def stage0Part1Program : List Instr :=
  [.op (.Dup dA10),
   .op (.Dup dA11),
   .op (.Dup dA3),
   .op (.Dup dA0),
   .op (.Dup dA0),
   .op .ADD,
   .op (.Swap sA4),
   .op .MULMOD]
def stage0Part1Model (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 : W) (rest : List W) : State :=
  let v0 : W := (w1) + (w1)
  let v1 : W := UInt256.mulMod (w1) (w1) (w10)
  {s with pc := N 4035, stack := (v1) :: (w10) :: (w0) :: (v0) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: rest}
theorem stage0Part1_run (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions stage0Part1Program {s with pc := N 4027, stack := (w0) :: (w1) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: rest} =
      some (stage0Part1Model s w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 63) : rest.length + j < 1024 := by omega
  simp [hz, hzn, stage0Part1Program, stage0Part1Model, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, capacity]

def stage0Part2Program : List Instr :=
  [.op (.Dup dA12),
   .push 1 160,
   .op .MLOAD,
   .op (.Dup dA4),
   .op .MULMOD,
   .op .ADD,
   .push 2 2048,
   .op .MULMOD]
def stage0Part2Model (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 : W) (rest : List W) : State :=
  let v0 : W := MachineState.readWord s.memory 160
  let v1 : W := UInt256.mulMod (w2) (v0) (w12)
  let v2 : W := (v1) + (w0)
  let v3 : W := UInt256.mulMod (N 2048) (v2) (w1)
  {s with pc := N 4046, stack := (v3) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: rest}
theorem stage0Part2_run (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions stage0Part2Program {s with pc := N 4035, stack := (w0) :: (w1) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: rest} =
      some (stage0Part2Model s w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 63) : rest.length + j < 1024 := by omega
  have ha160 : (160 : W).toNat = 160 := rfl
  have hf160 := Monpro.activeWords_fix s 160 32 (by decide) (by norm_num) hact
  simp [hz, hzn, stage0Part2Program, stage0Part2Model, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, capacity, ha160, hf160]

def stage0Program : List Instr := (stage0Part0Program ++ (stage0Part1Program ++ (stage0Part2Program)))
def stage0Model (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 : W) (rest : List W) : State :=
  let v0 : W := (w0) * (w0)
  let v1 : W := (w10) * (v0)
  let v2 : W := UInt256.shiftRight (v1) (N 16)
  let v3 : W := (w0) + (w0)
  let v4 : W := UInt256.mulMod (w0) (w0) (w9)
  let v5 : W := MachineState.readWord s.memory 160
  let v6 : W := UInt256.mulMod (v2) (v5) (w9)
  let v7 : W := (v6) + (v4)
  let v8 : W := UInt256.mulMod (N 2048) (v7) (w9)
  {s with pc := N 4046, stack := (v8) :: (v2) :: (v3) :: (w1) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: rest}
theorem stage0_run (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions stage0Program {s with pc := N 4018, stack := (w0) :: (w1) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: rest} = some (stage0Model s w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 rest) := by
  let v0 : W := (w0) * (w0)
  let v1 : W := (w10) * (v0)
  let v2 : W := UInt256.shiftRight (v1) (N 16)
  let v3 : W := (w0) + (w0)
  let v4 : W := UInt256.mulMod (w0) (w0) (w9)
  let v5 : W := MachineState.readWord s.memory 160
  let v6 : W := UInt256.mulMod (v2) (v5) (w9)
  let v7 : W := (v6) + (v4)
  let v8 : W := UInt256.mulMod (N 2048) (v7) (w9)
  have h0 : runInstructions stage0Part0Program {s with pc := N 4018, stack := (w0) :: (w1) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: rest} = some {s with pc := N 4027, stack := (v2) :: (w0) :: (w1) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: rest} := by
    simpa only [stage0Part0Model, v0, v1, v2] using stage0Part0_run s (w0) (w1) (w2) (w3) (w4) (w5) (w6) (w7) (w8) (w9) (w10) (w11) rest hcap hact
  have h1 : runInstructions stage0Part1Program {s with pc := N 4027, stack := (v2) :: (w0) :: (w1) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: rest} = some {s with pc := N 4035, stack := (v4) :: (w9) :: (v2) :: (v3) :: (w1) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: rest} := by
    simpa only [stage0Part1Model, v3, v4] using stage0Part1_run s (v2) (w0) (w1) (w2) (w3) (w4) (w5) (w6) (w7) (w8) (w9) (w10) (w11) rest hcap hact
  have h2 : runInstructions stage0Part2Program {s with pc := N 4035, stack := (v4) :: (w9) :: (v2) :: (v3) :: (w1) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: rest} = some {s with pc := N 4046, stack := (v8) :: (v2) :: (v3) :: (w1) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: rest} := by
    simpa only [stage0Part2Model, v5, v6, v7, v8] using stage0Part2_run s (v4) (w9) (v2) (v3) (w1) (w2) (w3) (w4) (w5) (w6) (w7) (w8) (w9) (w10) (w11) rest hcap hact
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
def stage1Part0Model (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 : W) (rest : List W) : State :=
  let v0 : W := (w2) * (w3)
  let v1 : W := (v0) + (w0)
  let v2 : W := (w1) * (w7)
  {s with pc := N 4054, stack := (v2) :: (v1) :: (w0) :: (w1) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: rest}
theorem stage1Part0_run (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions stage1Part0Program {s with pc := N 4046, stack := (w0) :: (w1) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: rest} =
      some (stage1Part0Model s w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 63) : rest.length + j < 1024 := by omega
  simp [hz, hzn, stage1Part0Program, stage1Part0Model, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, capacity]

def stage1Part1Program : List Instr :=
  [.op .ADD,
   .op (.Dup dA13),
   .op .MUL,
   .push 1 16,
   .op .SHR,
   .op (.Swap sA0),
   .op (.Dup dA12),
   .op (.Dup dA5)]
def stage1Part1Model (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 : W) (rest : List W) : State :=
  let v0 : W := (w0) + (w1)
  let v1 : W := (w14) * (v0)
  let v2 : W := UInt256.shiftRight (v1) (N 16)
  {s with pc := N 4063, stack := (w5) :: (w13) :: (w2) :: (v2) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: (w15) :: rest}
theorem stage1Part1_run (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions stage1Part1Program {s with pc := N 4054, stack := (w0) :: (w1) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: (w15) :: rest} =
      some (stage1Part1Model s w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 63) : rest.length + j < 1024 := by omega
  simp [hz, hzn, stage1Part1Program, stage1Part1Model, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, capacity]

def stage1Part2Program : List Instr :=
  [.op (.Dup dA5),
   .op .MULMOD,
   .op .ADD,
   .op (.Dup dA12),
   .op (.Dup dA9),
   .op (.Dup dA4),
   .op .MULMOD,
   .op .ADD]
def stage1Part2Model (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 : W) (rest : List W) : State :=
  let v0 : W := UInt256.mulMod (w5) (w0) (w1)
  let v1 : W := (v0) + (w2)
  let v2 : W := UInt256.mulMod (w4) (w10) (w14)
  let v3 : W := (v2) + (v1)
  {s with pc := N 4071, stack := (v3) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: (w15) :: (w16) :: rest}
theorem stage1Part2_run (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions stage1Part2Program {s with pc := N 4063, stack := (w0) :: (w1) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: (w15) :: (w16) :: rest} =
      some (stage1Part2Model s w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 63) : rest.length + j < 1024 := by omega
  simp [hz, hzn, stage1Part2Program, stage1Part2Model, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, capacity]

def stage1Part3Program : List Instr :=
  [.op (.Dup dA12),
   .push 1 160,
   .op .MLOAD,
   .op (.Dup dA3),
   .op .MULMOD,
   .op .ADD,
   .op (.Dup dA12),
   .op (.Swap sA0)]
def stage1Part3Model (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 : W) (rest : List W) : State :=
  let v0 : W := MachineState.readWord s.memory 160
  let v1 : W := UInt256.mulMod (w1) (v0) (w12)
  let v2 : W := (v1) + (w0)
  {s with pc := N 4080, stack := (v2) :: (w12) :: (w1) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: rest}
theorem stage1Part3_run (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions stage1Part3Program {s with pc := N 4071, stack := (w0) :: (w1) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: rest} =
      some (stage1Part3Model s w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 63) : rest.length + j < 1024 := by omega
  have ha160 : (160 : W).toNat = 160 := rfl
  have hf160 := Monpro.activeWords_fix s 160 32 (by decide) (by norm_num) hact
  simp [hz, hzn, stage1Part3Program, stage1Part3Model, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, capacity, ha160, hf160]

def stage1Part4Program : List Instr :=
  [.push 2 2048,
   .op .MULMOD]
def stage1Part4Model (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 : W) (rest : List W) : State :=
  let v0 : W := UInt256.mulMod (N 2048) (w0) (w1)
  {s with pc := N 4084, stack := (v0) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: (w15) :: rest}
theorem stage1Part4_run (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions stage1Part4Program {s with pc := N 4080, stack := (w0) :: (w1) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: (w15) :: rest} =
      some (stage1Part4Model s w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 63) : rest.length + j < 1024 := by omega
  simp [hz, hzn, stage1Part4Program, stage1Part4Model, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, capacity]

def stage1Program : List Instr := (stage1Part0Program ++ (stage1Part1Program ++ (stage1Part2Program ++ (stage1Part3Program ++ (stage1Part4Program)))))
def stage1Model (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 : W) (rest : List W) : State :=
  let v0 : W := (w2) * (w3)
  let v1 : W := (v0) + (w0)
  let v2 : W := (w1) * (w7)
  let v3 : W := (v2) + (v1)
  let v4 : W := (w12) * (v3)
  let v5 : W := UInt256.shiftRight (v4) (N 16)
  let v6 : W := UInt256.mulMod (w2) (w3) (w11)
  let v7 : W := (v6) + (w0)
  let v8 : W := UInt256.mulMod (w1) (w7) (w11)
  let v9 : W := (v8) + (v7)
  let v10 : W := MachineState.readWord s.memory 160
  let v11 : W := UInt256.mulMod (v5) (v10) (w11)
  let v12 : W := (v11) + (v9)
  let v13 : W := UInt256.mulMod (N 2048) (v12) (w11)
  {s with pc := N 4084, stack := (v13) :: (v5) :: (w1) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: rest}
theorem stage1_run (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions stage1Program {s with pc := N 4046, stack := (w0) :: (w1) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: rest} = some (stage1Model s w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 rest) := by
  let v0 : W := (w2) * (w3)
  let v1 : W := (v0) + (w0)
  let v2 : W := (w1) * (w7)
  let v3 : W := (v2) + (v1)
  let v4 : W := (w12) * (v3)
  let v5 : W := UInt256.shiftRight (v4) (N 16)
  let v6 : W := UInt256.mulMod (w2) (w3) (w11)
  let v7 : W := (v6) + (w0)
  let v8 : W := UInt256.mulMod (w1) (w7) (w11)
  let v9 : W := (v8) + (v7)
  let v10 : W := MachineState.readWord s.memory 160
  let v11 : W := UInt256.mulMod (v5) (v10) (w11)
  let v12 : W := (v11) + (v9)
  let v13 : W := UInt256.mulMod (N 2048) (v12) (w11)
  have h0 : runInstructions stage1Part0Program {s with pc := N 4046, stack := (w0) :: (w1) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: rest} = some {s with pc := N 4054, stack := (v2) :: (v1) :: (w0) :: (w1) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: rest} := by
    simpa only [stage1Part0Model, v0, v1, v2] using stage1Part0_run s (w0) (w1) (w2) (w3) (w4) (w5) (w6) (w7) (w8) (w9) (w10) (w11) (w12) (w13) rest hcap hact
  have h1 : runInstructions stage1Part1Program {s with pc := N 4054, stack := (v2) :: (v1) :: (w0) :: (w1) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: rest} = some {s with pc := N 4063, stack := (w3) :: (w11) :: (w0) :: (v5) :: (w1) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: rest} := by
    simpa only [stage1Part1Model, v3, v4, v5] using stage1Part1_run s (v2) (v1) (w0) (w1) (w2) (w3) (w4) (w5) (w6) (w7) (w8) (w9) (w10) (w11) (w12) (w13) rest hcap hact
  have h2 : runInstructions stage1Part2Program {s with pc := N 4063, stack := (w3) :: (w11) :: (w0) :: (v5) :: (w1) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: rest} = some {s with pc := N 4071, stack := (v9) :: (v5) :: (w1) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: rest} := by
    simpa only [stage1Part2Model, v6, v7, v8, v9] using stage1Part2_run s (w3) (w11) (w0) (v5) (w1) (w2) (w3) (w4) (w5) (w6) (w7) (w8) (w9) (w10) (w11) (w12) (w13) rest hcap hact
  have h3 : runInstructions stage1Part3Program {s with pc := N 4071, stack := (v9) :: (v5) :: (w1) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: rest} = some {s with pc := N 4080, stack := (v12) :: (w11) :: (v5) :: (w1) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: rest} := by
    simpa only [stage1Part3Model, v10, v11, v12] using stage1Part3_run s (v9) (v5) (w1) (w2) (w3) (w4) (w5) (w6) (w7) (w8) (w9) (w10) (w11) (w12) (w13) rest hcap hact
  have h4 : runInstructions stage1Part4Program {s with pc := N 4080, stack := (v12) :: (w11) :: (v5) :: (w1) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: rest} = some {s with pc := N 4084, stack := (v13) :: (v5) :: (w1) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: rest} := by
    simpa only [stage1Part4Model, v13] using stage1Part4_run s (v12) (w11) (v5) (w1) (w2) (w3) (w4) (w5) (w6) (w7) (w8) (w9) (w10) (w11) (w12) (w13) rest hcap hact
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
def stage2Part0Model (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 : W) (rest : List W) : State :=
  let v0 : W := (w3) * (w5)
  let v1 : W := (v0) + (w0)
  let v2 : W := (w4) * (w4)
  {s with pc := N 4092, stack := (v2) :: (v1) :: (w0) :: (w1) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: rest}
theorem stage2Part0_run (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions stage2Part0Program {s with pc := N 4084, stack := (w0) :: (w1) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: rest} =
      some (stage2Part0Model s w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 63) : rest.length + j < 1024 := by omega
  simp [hz, hzn, stage2Part0Program, stage2Part0Model, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, capacity]

def stage2Part1Program : List Instr :=
  [.op .ADD,
   .op (.Dup dA10),
   .op (.Dup dA4),
   .op .MUL,
   .op .ADD,
   .op (.Dup dA9),
   .op (.Dup dA3),
   .op .MUL]
def stage2Part1Model (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 : W) (rest : List W) : State :=
  let v0 : W := (w0) + (w1)
  let v1 : W := (w4) * (w11)
  let v2 : W := (v1) + (v0)
  let v3 : W := (w3) * (w10)
  {s with pc := N 4100, stack := (v3) :: (v2) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: (w15) :: (w16) :: rest}
theorem stage2Part1_run (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions stage2Part1Program {s with pc := N 4092, stack := (w0) :: (w1) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: (w15) :: (w16) :: rest} =
      some (stage2Part1Model s w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 63) : rest.length + j < 1024 := by omega
  simp [hz, hzn, stage2Part1Program, stage2Part1Model, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, capacity]

def stage2Part2Program : List Instr :=
  [.op .ADD,
   .op (.Dup dA14),
   .op .MUL,
   .push 1 16,
   .op .SHR,
   .op (.Swap sA0),
   .op (.Dup dA13),
   .op (.Dup dA7)]
def stage2Part2Model (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 : W) (rest : List W) : State :=
  let v0 : W := (w0) + (w1)
  let v1 : W := (w15) * (v0)
  let v2 : W := UInt256.shiftRight (v1) (N 16)
  {s with pc := N 4109, stack := (w7) :: (w14) :: (w2) :: (v2) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: (w15) :: (w16) :: rest}
theorem stage2Part2_run (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions stage2Part2Program {s with pc := N 4100, stack := (w0) :: (w1) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: (w15) :: (w16) :: rest} =
      some (stage2Part2Model s w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 63) : rest.length + j < 1024 := by omega
  simp [hz, hzn, stage2Part2Program, stage2Part2Model, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, capacity]

def stage2Part3Program : List Instr :=
  [.op (.Dup dA6),
   .op .MULMOD,
   .op .ADD,
   .op (.Dup dA13),
   .op (.Dup dA6),
   .op (.Dup dA0),
   .op (.Dup dA0),
   .op .ADD]
def stage2Part3Model (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 : W) (rest : List W) : State :=
  let v0 : W := UInt256.mulMod (w6) (w0) (w1)
  let v1 : W := (v0) + (w2)
  let v2 : W := (w7) + (w7)
  {s with pc := N 4117, stack := (v2) :: (w7) :: (w15) :: (v1) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: (w15) :: (w16) :: (w17) :: rest}
theorem stage2Part3_run (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions stage2Part3Program {s with pc := N 4109, stack := (w0) :: (w1) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: (w15) :: (w16) :: (w17) :: rest} =
      some (stage2Part3Model s w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 63) : rest.length + j < 1024 := by omega
  simp [hz, hzn, stage2Part3Program, stage2Part3Model, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, capacity]

def stage2Part4Program : List Instr :=
  [.op (.Swap sA7),
   .op .MULMOD,
   .op .ADD,
   .op (.Dup dA13),
   .op (.Dup dA11),
   .op (.Dup dA5),
   .op .MULMOD,
   .op .ADD]
def stage2Part4Model (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 : W) (rest : List W) : State :=
  let v0 : W := UInt256.mulMod (w8) (w1) (w2)
  let v1 : W := (v0) + (w3)
  let v2 : W := UInt256.mulMod (w6) (w13) (w16)
  let v3 : W := (v2) + (v1)
  {s with pc := N 4125, stack := (v3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w0) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: (w15) :: (w16) :: (w17) :: (w18) :: rest}
theorem stage2Part4_run (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions stage2Part4Program {s with pc := N 4117, stack := (w0) :: (w1) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: (w15) :: (w16) :: (w17) :: (w18) :: rest} =
      some (stage2Part4Model s w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 63) : rest.length + j < 1024 := by omega
  simp [hz, hzn, stage2Part4Program, stage2Part4Model, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, capacity]

def stage2Part5Program : List Instr :=
  [.op (.Dup dA13),
   .op (.Dup dA10),
   .op (.Dup dA4),
   .op .MULMOD,
   .op .ADD,
   .op (.Dup dA13),
   .push 1 160,
   .op .MLOAD]
def stage2Part5Model (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 : W) (rest : List W) : State :=
  let v0 : W := UInt256.mulMod (w2) (w9) (w13)
  let v1 : W := (v0) + (w0)
  let v2 : W := MachineState.readWord s.memory 160
  {s with pc := N 4134, stack := (v2) :: (w13) :: (v1) :: (w1) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: (w15) :: rest}
theorem stage2Part5_run (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions stage2Part5Program {s with pc := N 4125, stack := (w0) :: (w1) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: (w15) :: rest} =
      some (stage2Part5Model s w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 63) : rest.length + j < 1024 := by omega
  have ha160 : (160 : W).toNat = 160 := rfl
  have hf160 := Monpro.activeWords_fix s 160 32 (by decide) (by norm_num) hact
  simp [hz, hzn, stage2Part5Program, stage2Part5Model, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, capacity, ha160, hf160]

def stage2Part6Program : List Instr :=
  [.op (.Dup dA3),
   .op .MULMOD,
   .op .ADD,
   .op (.Dup dA13),
   .op (.Swap sA0),
   .push 2 2048,
   .op .MULMOD]
def stage2Part6Model (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 : W) (rest : List W) : State :=
  let v0 : W := UInt256.mulMod (w3) (w0) (w1)
  let v1 : W := (v0) + (w2)
  let v2 : W := UInt256.mulMod (N 2048) (v1) (w15)
  {s with pc := N 4143, stack := (v2) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: (w15) :: (w16) :: (w17) :: rest}
theorem stage2Part6_run (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions stage2Part6Program {s with pc := N 4134, stack := (w0) :: (w1) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: (w15) :: (w16) :: (w17) :: rest} =
      some (stage2Part6Model s w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 63) : rest.length + j < 1024 := by omega
  simp [hz, hzn, stage2Part6Program, stage2Part6Model, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, capacity]

def stage2Program : List Instr := (stage2Part0Program ++ (stage2Part1Program ++ (stage2Part2Program ++ (stage2Part3Program ++ (stage2Part4Program ++ (stage2Part5Program ++ (stage2Part6Program)))))))
def stage2Model (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 : W) (rest : List W) : State :=
  let v0 : W := (w3) * (w5)
  let v1 : W := (v0) + (w0)
  let v2 : W := (w4) * (w4)
  let v3 : W := (v2) + (v1)
  let v4 : W := (w2) * (w9)
  let v5 : W := (v4) + (v3)
  let v6 : W := (w1) * (w8)
  let v7 : W := (v6) + (v5)
  let v8 : W := (w13) * (v7)
  let v9 : W := UInt256.shiftRight (v8) (N 16)
  let v10 : W := UInt256.mulMod (w3) (w5) (w12)
  let v11 : W := (v10) + (w0)
  let v12 : W := (w4) + (w4)
  let v13 : W := UInt256.mulMod (w4) (w4) (w12)
  let v14 : W := (v13) + (v11)
  let v15 : W := UInt256.mulMod (w2) (w9) (w12)
  let v16 : W := (v15) + (v14)
  let v17 : W := UInt256.mulMod (w1) (w8) (w12)
  let v18 : W := (v17) + (v16)
  let v19 : W := MachineState.readWord s.memory 160
  let v20 : W := UInt256.mulMod (v9) (v19) (w12)
  let v21 : W := (v20) + (v18)
  let v22 : W := UInt256.mulMod (N 2048) (v21) (w12)
  {s with pc := N 4143, stack := (v22) :: (v9) :: (w1) :: (w2) :: (w3) :: (v12) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: rest}
theorem stage2_run (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions stage2Program {s with pc := N 4084, stack := (w0) :: (w1) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: rest} = some (stage2Model s w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 rest) := by
  let v0 : W := (w3) * (w5)
  let v1 : W := (v0) + (w0)
  let v2 : W := (w4) * (w4)
  let v3 : W := (v2) + (v1)
  let v4 : W := (w2) * (w9)
  let v5 : W := (v4) + (v3)
  let v6 : W := (w1) * (w8)
  let v7 : W := (v6) + (v5)
  let v8 : W := (w13) * (v7)
  let v9 : W := UInt256.shiftRight (v8) (N 16)
  let v10 : W := UInt256.mulMod (w3) (w5) (w12)
  let v11 : W := (v10) + (w0)
  let v12 : W := (w4) + (w4)
  let v13 : W := UInt256.mulMod (w4) (w4) (w12)
  let v14 : W := (v13) + (v11)
  let v15 : W := UInt256.mulMod (w2) (w9) (w12)
  let v16 : W := (v15) + (v14)
  let v17 : W := UInt256.mulMod (w1) (w8) (w12)
  let v18 : W := (v17) + (v16)
  let v19 : W := MachineState.readWord s.memory 160
  let v20 : W := UInt256.mulMod (v9) (v19) (w12)
  let v21 : W := (v20) + (v18)
  let v22 : W := UInt256.mulMod (N 2048) (v21) (w12)
  have h0 : runInstructions stage2Part0Program {s with pc := N 4084, stack := (w0) :: (w1) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: rest} = some {s with pc := N 4092, stack := (v2) :: (v1) :: (w0) :: (w1) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: rest} := by
    simpa only [stage2Part0Model, v0, v1, v2] using stage2Part0_run s (w0) (w1) (w2) (w3) (w4) (w5) (w6) (w7) (w8) (w9) (w10) (w11) (w12) (w13) (w14) rest hcap hact
  have h1 : runInstructions stage2Part1Program {s with pc := N 4092, stack := (v2) :: (v1) :: (w0) :: (w1) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: rest} = some {s with pc := N 4100, stack := (v6) :: (v5) :: (w0) :: (w1) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: rest} := by
    simpa only [stage2Part1Model, v3, v4, v5, v6] using stage2Part1_run s (v2) (v1) (w0) (w1) (w2) (w3) (w4) (w5) (w6) (w7) (w8) (w9) (w10) (w11) (w12) (w13) (w14) rest hcap hact
  have h2 : runInstructions stage2Part2Program {s with pc := N 4100, stack := (v6) :: (v5) :: (w0) :: (w1) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: rest} = some {s with pc := N 4109, stack := (w5) :: (w12) :: (w0) :: (v9) :: (w1) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: rest} := by
    simpa only [stage2Part2Model, v7, v8, v9] using stage2Part2_run s (v6) (v5) (w0) (w1) (w2) (w3) (w4) (w5) (w6) (w7) (w8) (w9) (w10) (w11) (w12) (w13) (w14) rest hcap hact
  have h3 : runInstructions stage2Part3Program {s with pc := N 4109, stack := (w5) :: (w12) :: (w0) :: (v9) :: (w1) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: rest} = some {s with pc := N 4117, stack := (v12) :: (w4) :: (w12) :: (v11) :: (v9) :: (w1) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: rest} := by
    simpa only [stage2Part3Model, v10, v11, v12] using stage2Part3_run s (w5) (w12) (w0) (v9) (w1) (w2) (w3) (w4) (w5) (w6) (w7) (w8) (w9) (w10) (w11) (w12) (w13) (w14) rest hcap hact
  have h4 : runInstructions stage2Part4Program {s with pc := N 4117, stack := (v12) :: (w4) :: (w12) :: (v11) :: (v9) :: (w1) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: rest} = some {s with pc := N 4125, stack := (v16) :: (v9) :: (w1) :: (w2) :: (w3) :: (v12) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: rest} := by
    simpa only [stage2Part4Model, v13, v14, v15, v16] using stage2Part4_run s (v12) (w4) (w12) (v11) (v9) (w1) (w2) (w3) (w4) (w5) (w6) (w7) (w8) (w9) (w10) (w11) (w12) (w13) (w14) rest hcap hact
  have h5 : runInstructions stage2Part5Program {s with pc := N 4125, stack := (v16) :: (v9) :: (w1) :: (w2) :: (w3) :: (v12) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: rest} = some {s with pc := N 4134, stack := (v19) :: (w12) :: (v18) :: (v9) :: (w1) :: (w2) :: (w3) :: (v12) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: rest} := by
    simpa only [stage2Part5Model, v17, v18, v19] using stage2Part5_run s (v16) (v9) (w1) (w2) (w3) (v12) (w5) (w6) (w7) (w8) (w9) (w10) (w11) (w12) (w13) (w14) rest hcap hact
  have h6 : runInstructions stage2Part6Program {s with pc := N 4134, stack := (v19) :: (w12) :: (v18) :: (v9) :: (w1) :: (w2) :: (w3) :: (v12) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: rest} = some {s with pc := N 4143, stack := (v22) :: (v9) :: (w1) :: (w2) :: (w3) :: (v12) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: rest} := by
    simpa only [stage2Part6Model, v20, v21, v22] using stage2Part6_run s (v19) (w12) (v18) (v9) (w1) (w2) (w3) (v12) (w5) (w6) (w7) (w8) (w9) (w10) (w11) (w12) (w13) (w14) rest hcap hact
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
def stage3Part0Model (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 : W) (rest : List W) : State :=
  let v0 : W := (w4) * (w7)
  let v1 : W := (w5) * (w6)
  let v2 : W := (v1) + (v0)
  {s with pc := N 4151, stack := (v2) :: (w0) :: (w0) :: (w1) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: (w15) :: rest}
theorem stage3Part0_run (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions stage3Part0Program {s with pc := N 4143, stack := (w0) :: (w1) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: (w15) :: rest} =
      some (stage3Part0Model s w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 63) : rest.length + j < 1024 := by omega
  simp [hz, hzn, stage3Part0Program, stage3Part0Model, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, capacity]

def stage3Part1Program : List Instr :=
  [.op .ADD,
   .op (.Dup dA12),
   .op (.Dup dA5),
   .op .MUL,
   .op .ADD,
   .op (.Dup dA11),
   .op (.Dup dA4),
   .op .MUL]
def stage3Part1Model (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 : W) (rest : List W) : State :=
  let v0 : W := (w0) + (w1)
  let v1 : W := (w5) * (w13)
  let v2 : W := (v1) + (v0)
  let v3 : W := (w4) * (w12)
  {s with pc := N 4159, stack := (v3) :: (v2) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: (w15) :: (w16) :: (w17) :: rest}
theorem stage3Part1_run (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions stage3Part1Program {s with pc := N 4151, stack := (w0) :: (w1) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: (w15) :: (w16) :: (w17) :: rest} =
      some (stage3Part1Model s w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 63) : rest.length + j < 1024 := by omega
  simp [hz, hzn, stage3Part1Program, stage3Part1Model, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, capacity]

def stage3Part2Program : List Instr :=
  [.op .ADD,
   .op (.Dup dA10),
   .op (.Dup dA3),
   .op .MUL,
   .op .ADD,
   .op (.Dup dA15),
   .op .MUL,
   .push 1 16]
def stage3Part2Model (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 : W) (rest : List W) : State :=
  let v0 : W := (w0) + (w1)
  let v1 : W := (w3) * (w11)
  let v2 : W := (v1) + (v0)
  let v3 : W := (w16) * (v2)
  {s with pc := N 4168, stack := (N 16) :: (v3) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: (w15) :: (w16) :: (w17) :: rest}
theorem stage3Part2_run (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions stage3Part2Program {s with pc := N 4159, stack := (w0) :: (w1) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: (w15) :: (w16) :: (w17) :: rest} =
      some (stage3Part2Model s w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 63) : rest.length + j < 1024 := by omega
  simp [hz, hzn, stage3Part2Program, stage3Part2Model, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, capacity]

def stage3Part3Program : List Instr :=
  [.op .SHR,
   .op (.Swap sA0),
   .op (.Dup dA14),
   .op (.Dup dA9),
   .op (.Dup dA7),
   .op .MULMOD,
   .op (.Dup dA15),
   .op (.Dup dA9)]
def stage3Part3Model (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 : W) (rest : List W) : State :=
  let v0 : W := UInt256.shiftRight (w1) (w0)
  let v1 : W := UInt256.mulMod (w6) (w9) (w15)
  {s with pc := N 4176, stack := (w8) :: (w15) :: (v1) :: (w2) :: (v0) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: (w15) :: (w16) :: (w17) :: rest}
theorem stage3Part3_run (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions stage3Part3Program {s with pc := N 4168, stack := (w0) :: (w1) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: (w15) :: (w16) :: (w17) :: rest} =
      some (stage3Part3Model s w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 63) : rest.length + j < 1024 := by omega
  simp [hz, hzn, stage3Part3Program, stage3Part3Model, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, capacity]

def stage3Part4Program : List Instr :=
  [.op (.Dup dA9),
   .op .MULMOD,
   .op .ADD,
   .op .ADD,
   .op (.Dup dA14),
   .op (.Dup dA13),
   .op (.Dup dA6),
   .op .MULMOD]
def stage3Part4Model (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 : W) (rest : List W) : State :=
  let v0 : W := UInt256.mulMod (w9) (w0) (w1)
  let v1 : W := (v0) + (w2)
  let v2 : W := (v1) + (w3)
  let v3 : W := UInt256.mulMod (w7) (w15) (w17)
  {s with pc := N 4184, stack := (v3) :: (v2) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: (w15) :: (w16) :: (w17) :: (w18) :: (w19) :: rest}
theorem stage3Part4_run (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions stage3Part4Program {s with pc := N 4176, stack := (w0) :: (w1) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: (w15) :: (w16) :: (w17) :: (w18) :: (w19) :: rest} =
      some (stage3Part4Model s w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 63) : rest.length + j < 1024 := by omega
  simp [hz, hzn, stage3Part4Program, stage3Part4Model, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, capacity]

def stage3Part5Program : List Instr :=
  [.op .ADD,
   .op (.Dup dA14),
   .op (.Dup dA12),
   .op (.Dup dA5),
   .op .MULMOD,
   .op .ADD,
   .op (.Dup dA14),
   .op (.Dup dA11)]
def stage3Part5Model (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 : W) (rest : List W) : State :=
  let v0 : W := (w0) + (w1)
  let v1 : W := UInt256.mulMod (w4) (w12) (w15)
  let v2 : W := (v1) + (v0)
  {s with pc := N 4192, stack := (w11) :: (w15) :: (v2) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: (w15) :: (w16) :: (w17) :: rest}
theorem stage3Part5_run (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions stage3Part5Program {s with pc := N 4184, stack := (w0) :: (w1) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: (w15) :: (w16) :: (w17) :: rest} =
      some (stage3Part5Model s w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 63) : rest.length + j < 1024 := by omega
  simp [hz, hzn, stage3Part5Program, stage3Part5Model, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, capacity]

def stage3Part6Program : List Instr :=
  [.op (.Dup dA4),
   .op .MULMOD,
   .op .ADD,
   .op (.Dup dA14),
   .push 1 160,
   .op .MLOAD,
   .op (.Dup dA3),
   .op .MULMOD]
def stage3Part6Model (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 : W) (rest : List W) : State :=
  let v0 : W := UInt256.mulMod (w4) (w0) (w1)
  let v1 : W := (v0) + (w2)
  let v2 : W := MachineState.readWord s.memory 160
  let v3 : W := UInt256.mulMod (w3) (v2) (w16)
  {s with pc := N 4201, stack := (v3) :: (v1) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: (w15) :: (w16) :: (w17) :: (w18) :: rest}
theorem stage3Part6_run (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions stage3Part6Program {s with pc := N 4192, stack := (w0) :: (w1) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: (w15) :: (w16) :: (w17) :: (w18) :: rest} =
      some (stage3Part6Model s w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 63) : rest.length + j < 1024 := by omega
  have ha160 : (160 : W).toNat = 160 := rfl
  have hf160 := Monpro.activeWords_fix s 160 32 (by decide) (by norm_num) hact
  simp [hz, hzn, stage3Part6Program, stage3Part6Model, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, capacity, ha160, hf160]

def stage3Part7Program : List Instr :=
  [.op .ADD,
   .op (.Dup dA14),
   .op (.Swap sA0),
   .push 2 2048,
   .op .MULMOD]
def stage3Part7Model (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 : W) (rest : List W) : State :=
  let v0 : W := (w0) + (w1)
  let v1 : W := UInt256.mulMod (N 2048) (v0) (w15)
  {s with pc := N 4208, stack := (v1) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: (w15) :: (w16) :: (w17) :: rest}
theorem stage3Part7_run (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions stage3Part7Program {s with pc := N 4201, stack := (w0) :: (w1) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: (w15) :: (w16) :: (w17) :: rest} =
      some (stage3Part7Model s w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 63) : rest.length + j < 1024 := by omega
  simp [hz, hzn, stage3Part7Program, stage3Part7Model, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, capacity]

def stage3Program : List Instr := (stage3Part0Program ++ (stage3Part1Program ++ (stage3Part2Program ++ (stage3Part3Program ++ (stage3Part4Program ++ (stage3Part5Program ++ (stage3Part6Program ++ (stage3Part7Program))))))))
def stage3Model (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 : W) (rest : List W) : State :=
  let v0 : W := (w4) * (w7)
  let v1 : W := (w5) * (w6)
  let v2 : W := (v1) + (v0)
  let v3 : W := (v2) + (w0)
  let v4 : W := (w3) * (w11)
  let v5 : W := (v4) + (v3)
  let v6 : W := (w2) * (w10)
  let v7 : W := (v6) + (v5)
  let v8 : W := (w1) * (w9)
  let v9 : W := (v8) + (v7)
  let v10 : W := (w14) * (v9)
  let v11 : W := UInt256.shiftRight (v10) (N 16)
  let v12 : W := UInt256.mulMod (w4) (w7) (w13)
  let v13 : W := UInt256.mulMod (w5) (w6) (w13)
  let v14 : W := (v13) + (v12)
  let v15 : W := (v14) + (w0)
  let v16 : W := UInt256.mulMod (w3) (w11) (w13)
  let v17 : W := (v16) + (v15)
  let v18 : W := UInt256.mulMod (w2) (w10) (w13)
  let v19 : W := (v18) + (v17)
  let v20 : W := UInt256.mulMod (w1) (w9) (w13)
  let v21 : W := (v20) + (v19)
  let v22 : W := MachineState.readWord s.memory 160
  let v23 : W := UInt256.mulMod (v11) (v22) (w13)
  let v24 : W := (v23) + (v21)
  let v25 : W := UInt256.mulMod (N 2048) (v24) (w13)
  {s with pc := N 4208, stack := (v25) :: (v11) :: (w1) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: (w15) :: rest}
theorem stage3_run (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions stage3Program {s with pc := N 4143, stack := (w0) :: (w1) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: (w15) :: rest} = some (stage3Model s w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 rest) := by
  let v0 : W := (w4) * (w7)
  let v1 : W := (w5) * (w6)
  let v2 : W := (v1) + (v0)
  let v3 : W := (v2) + (w0)
  let v4 : W := (w3) * (w11)
  let v5 : W := (v4) + (v3)
  let v6 : W := (w2) * (w10)
  let v7 : W := (v6) + (v5)
  let v8 : W := (w1) * (w9)
  let v9 : W := (v8) + (v7)
  let v10 : W := (w14) * (v9)
  let v11 : W := UInt256.shiftRight (v10) (N 16)
  let v12 : W := UInt256.mulMod (w4) (w7) (w13)
  let v13 : W := UInt256.mulMod (w5) (w6) (w13)
  let v14 : W := (v13) + (v12)
  let v15 : W := (v14) + (w0)
  let v16 : W := UInt256.mulMod (w3) (w11) (w13)
  let v17 : W := (v16) + (v15)
  let v18 : W := UInt256.mulMod (w2) (w10) (w13)
  let v19 : W := (v18) + (v17)
  let v20 : W := UInt256.mulMod (w1) (w9) (w13)
  let v21 : W := (v20) + (v19)
  let v22 : W := MachineState.readWord s.memory 160
  let v23 : W := UInt256.mulMod (v11) (v22) (w13)
  let v24 : W := (v23) + (v21)
  let v25 : W := UInt256.mulMod (N 2048) (v24) (w13)
  have h0 : runInstructions stage3Part0Program {s with pc := N 4143, stack := (w0) :: (w1) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: (w15) :: rest} = some {s with pc := N 4151, stack := (v2) :: (w0) :: (w0) :: (w1) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: (w15) :: rest} := by
    simpa only [stage3Part0Model, v0, v1, v2] using stage3Part0_run s (w0) (w1) (w2) (w3) (w4) (w5) (w6) (w7) (w8) (w9) (w10) (w11) (w12) (w13) (w14) (w15) rest hcap hact
  have h1 : runInstructions stage3Part1Program {s with pc := N 4151, stack := (v2) :: (w0) :: (w0) :: (w1) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: (w15) :: rest} = some {s with pc := N 4159, stack := (v6) :: (v5) :: (w0) :: (w1) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: (w15) :: rest} := by
    simpa only [stage3Part1Model, v3, v4, v5, v6] using stage3Part1_run s (v2) (w0) (w0) (w1) (w2) (w3) (w4) (w5) (w6) (w7) (w8) (w9) (w10) (w11) (w12) (w13) (w14) (w15) rest hcap hact
  have h2 : runInstructions stage3Part2Program {s with pc := N 4159, stack := (v6) :: (v5) :: (w0) :: (w1) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: (w15) :: rest} = some {s with pc := N 4168, stack := (N 16) :: (v10) :: (w0) :: (w1) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: (w15) :: rest} := by
    simpa only [stage3Part2Model, v7, v8, v9, v10] using stage3Part2_run s (v6) (v5) (w0) (w1) (w2) (w3) (w4) (w5) (w6) (w7) (w8) (w9) (w10) (w11) (w12) (w13) (w14) (w15) rest hcap hact
  have h3 : runInstructions stage3Part3Program {s with pc := N 4168, stack := (N 16) :: (v10) :: (w0) :: (w1) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: (w15) :: rest} = some {s with pc := N 4176, stack := (w6) :: (w13) :: (v12) :: (w0) :: (v11) :: (w1) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: (w15) :: rest} := by
    simpa only [stage3Part3Model, v11, v12] using stage3Part3_run s (N 16) (v10) (w0) (w1) (w2) (w3) (w4) (w5) (w6) (w7) (w8) (w9) (w10) (w11) (w12) (w13) (w14) (w15) rest hcap hact
  have h4 : runInstructions stage3Part4Program {s with pc := N 4176, stack := (w6) :: (w13) :: (v12) :: (w0) :: (v11) :: (w1) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: (w15) :: rest} = some {s with pc := N 4184, stack := (v16) :: (v15) :: (v11) :: (w1) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: (w15) :: rest} := by
    simpa only [stage3Part4Model, v13, v14, v15, v16] using stage3Part4_run s (w6) (w13) (v12) (w0) (v11) (w1) (w2) (w3) (w4) (w5) (w6) (w7) (w8) (w9) (w10) (w11) (w12) (w13) (w14) (w15) rest hcap hact
  have h5 : runInstructions stage3Part5Program {s with pc := N 4184, stack := (v16) :: (v15) :: (v11) :: (w1) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: (w15) :: rest} = some {s with pc := N 4192, stack := (w9) :: (w13) :: (v19) :: (v11) :: (w1) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: (w15) :: rest} := by
    simpa only [stage3Part5Model, v17, v18, v19] using stage3Part5_run s (v16) (v15) (v11) (w1) (w2) (w3) (w4) (w5) (w6) (w7) (w8) (w9) (w10) (w11) (w12) (w13) (w14) (w15) rest hcap hact
  have h6 : runInstructions stage3Part6Program {s with pc := N 4192, stack := (w9) :: (w13) :: (v19) :: (v11) :: (w1) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: (w15) :: rest} = some {s with pc := N 4201, stack := (v23) :: (v21) :: (v11) :: (w1) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: (w15) :: rest} := by
    simpa only [stage3Part6Model, v20, v21, v22, v23] using stage3Part6_run s (w9) (w13) (v19) (v11) (w1) (w2) (w3) (w4) (w5) (w6) (w7) (w8) (w9) (w10) (w11) (w12) (w13) (w14) (w15) rest hcap hact
  have h7 : runInstructions stage3Part7Program {s with pc := N 4201, stack := (v23) :: (v21) :: (v11) :: (w1) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: (w15) :: rest} = some {s with pc := N 4208, stack := (v25) :: (v11) :: (w1) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: (w15) :: rest} := by
    simpa only [stage3Part7Model, v24, v25] using stage3Part7_run s (v23) (v21) (v11) (w1) (w2) (w3) (w4) (w5) (w6) (w7) (w8) (w9) (w10) (w11) (w12) (w13) (w14) (w15) rest hcap hact
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
def stage4Part0Model (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 : W) (rest : List W) : State :=
  let v0 : W := UInt256.mulMod (w9) (w5) (w14)
  let v1 : W := UInt256.mulMod (w8) (w6) (w14)
  {s with pc := N 4216, stack := (v1) :: (v0) :: (w0) :: (w1) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: (w15) :: (w16) :: rest}
theorem stage4Part0_run (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions stage4Part0Program {s with pc := N 4208, stack := (w0) :: (w1) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: (w15) :: (w16) :: rest} =
      some (stage4Part0Model s w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 63) : rest.length + j < 1024 := by omega
  simp [hz, hzn, stage4Part0Program, stage4Part0Model, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, capacity]

def stage4Part1Program : List Instr :=
  [.op .ADD,
   .op (.Dup dA1),
   .op .ADD,
   .op (.Dup dA15),
   .op (.Dup dA9),
   .op (.Dup dA0),
   .op .MULMOD,
   .op .ADD]
def stage4Part1Model (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 : W) (rest : List W) : State :=
  let v0 : W := (w0) + (w1)
  let v1 : W := (w2) + (v0)
  let v2 : W := UInt256.mulMod (w9) (w9) (w16)
  let v3 : W := (v2) + (v1)
  {s with pc := N 4224, stack := (v3) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: (w15) :: (w16) :: (w17) :: (w18) :: rest}
theorem stage4Part1_run (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions stage4Part1Program {s with pc := N 4216, stack := (w0) :: (w1) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: (w15) :: (w16) :: (w17) :: (w18) :: rest} =
      some (stage4Part1Model s w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 63) : rest.length + j < 1024 := by omega
  simp [hz, hzn, stage4Part1Program, stage4Part1Model, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, capacity]

def stage4Part2Program : List Instr :=
  [.op (.Dup dA15),
   .op (.Dup dA15),
   .op (.Dup dA7),
   .op .MULMOD,
   .op .ADD,
   .op (.Dup dA15),
   .op (.Dup dA14),
   .op (.Dup dA6)]
def stage4Part2Model (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 : W) (rest : List W) : State :=
  let v0 : W := UInt256.mulMod (w5) (w14) (w15)
  let v1 : W := (v0) + (w0)
  {s with pc := N 4232, stack := (w4) :: (w13) :: (w15) :: (v1) :: (w1) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: (w15) :: (w16) :: (w17) :: rest}
theorem stage4Part2_run (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions stage4Part2Program {s with pc := N 4224, stack := (w0) :: (w1) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: (w15) :: (w16) :: (w17) :: rest} =
      some (stage4Part2Model s w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 63) : rest.length + j < 1024 := by omega
  simp [hz, hzn, stage4Part2Program, stage4Part2Model, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, capacity]

def stage4Part3Program : List Instr :=
  [.op .MULMOD,
   .op .ADD,
   .op (.Dup dA15),
   .op (.Dup dA13),
   .op (.Dup dA5),
   .op .MULMOD,
   .op .ADD,
   .op (.Dup dA15)]
def stage4Part3Model (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 w20 : W) (rest : List W) : State :=
  let v0 : W := UInt256.mulMod (w0) (w1) (w2)
  let v1 : W := (v0) + (w3)
  let v2 : W := UInt256.mulMod (w6) (w15) (w18)
  let v3 : W := (v2) + (v1)
  {s with pc := N 4240, stack := (w18) :: (v3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: (w15) :: (w16) :: (w17) :: (w18) :: (w19) :: (w20) :: rest}
theorem stage4Part3_run (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 w20 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions stage4Part3Program {s with pc := N 4232, stack := (w0) :: (w1) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: (w15) :: (w16) :: (w17) :: (w18) :: (w19) :: (w20) :: rest} =
      some (stage4Part3Model s w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 w20 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 63) : rest.length + j < 1024 := by omega
  simp [hz, hzn, stage4Part3Program, stage4Part3Model, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, capacity]

def stage4Part4Program : List Instr :=
  [.op (.Dup dA12),
   .op (.Dup dA4),
   .op .MULMOD,
   .op .ADD,
   .op (.Swap sA0),
   .op (.Dup dA10),
   .op (.Dup dA7),
   .op .MUL]
def stage4Part4Model (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 : W) (rest : List W) : State :=
  let v0 : W := UInt256.mulMod (w3) (w12) (w0)
  let v1 : W := (v0) + (w1)
  let v2 : W := (w7) * (w11)
  {s with pc := N 4248, stack := (v2) :: (w2) :: (v1) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: (w15) :: (w16) :: (w17) :: (w18) :: rest}
theorem stage4Part4_run (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions stage4Part4Program {s with pc := N 4240, stack := (w0) :: (w1) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: (w15) :: (w16) :: (w17) :: (w18) :: rest} =
      some (stage4Part4Model s w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 63) : rest.length + j < 1024 := by omega
  simp [hz, hzn, stage4Part4Program, stage4Part4Model, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, capacity]

def stage4Part5Program : List Instr :=
  [.op (.Dup dA10),
   .op (.Dup dA9),
   .op .MUL,
   .op .ADD,
   .op .ADD,
   .op (.Dup dA8),
   .op (.Dup dA0),
   .op (.Dup dA0)]
def stage4Part5Model (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 : W) (rest : List W) : State :=
  let v0 : W := (w8) * (w10)
  let v1 : W := (v0) + (w0)
  let v2 : W := (v1) + (w1)
  {s with pc := N 4256, stack := (w9) :: (w9) :: (w9) :: (v2) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: (w15) :: (w16) :: (w17) :: (w18) :: rest}
theorem stage4Part5_run (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions stage4Part5Program {s with pc := N 4248, stack := (w0) :: (w1) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: (w15) :: (w16) :: (w17) :: (w18) :: rest} =
      some (stage4Part5Model s w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 63) : rest.length + j < 1024 := by omega
  simp [hz, hzn, stage4Part5Program, stage4Part5Model, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, capacity]

def stage4Part6Program : List Instr :=
  [.op .ADD,
   .op (.Swap sA9),
   .op .MUL,
   .op .ADD,
   .op (.Dup dA14),
   .op (.Dup dA6),
   .op .MUL,
   .op .ADD]
def stage4Part6Model (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 w20 : W) (rest : List W) : State :=
  let v0 : W := (w0) + (w1)
  let v1 : W := (w11) * (w2)
  let v2 : W := (v1) + (w3)
  let v3 : W := (w8) * (w17)
  let v4 : W := (v3) + (v2)
  {s with pc := N 4264, stack := (v4) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (v0) :: (w12) :: (w13) :: (w14) :: (w15) :: (w16) :: (w17) :: (w18) :: (w19) :: (w20) :: rest}
theorem stage4Part6_run (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 w20 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions stage4Part6Program {s with pc := N 4256, stack := (w0) :: (w1) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: (w15) :: (w16) :: (w17) :: (w18) :: (w19) :: (w20) :: rest} =
      some (stage4Part6Model s w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 w20 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 63) : rest.length + j < 1024 := by omega
  simp [hz, hzn, stage4Part6Program, stage4Part6Model, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, capacity]

def stage4Part7Program : List Instr :=
  [.op (.Dup dA13),
   .op (.Dup dA5),
   .op .MUL,
   .op .ADD,
   .op (.Dup dA12),
   .op (.Dup dA4),
   .op .MUL,
   .op .ADD]
def stage4Part7Model (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 : W) (rest : List W) : State :=
  let v0 : W := (w4) * (w13)
  let v1 : W := (v0) + (w0)
  let v2 : W := (w3) * (w12)
  let v3 : W := (v2) + (v1)
  {s with pc := N 4272, stack := (v3) :: (w1) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: (w15) :: (w16) :: (w17) :: rest}
theorem stage4Part7_run (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions stage4Part7Program {s with pc := N 4264, stack := (w0) :: (w1) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: (w15) :: (w16) :: (w17) :: rest} =
      some (stage4Part7Model s w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 63) : rest.length + j < 1024 := by omega
  simp [hz, hzn, stage4Part7Program, stage4Part7Model, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, capacity]

def stage4Part8Program : List Instr :=
  [.op (.Dup dA11),
   .op (.Dup dA3),
   .op .MUL,
   .op .ADD,
   .push 1 192,
   .op .MLOAD,
   .op .MUL,
   .push 1 16]
def stage4Part8Model (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 : W) (rest : List W) : State :=
  let v0 : W := (w2) * (w11)
  let v1 : W := (v0) + (w0)
  let v2 : W := MachineState.readWord s.memory 192
  let v3 : W := (v2) * (v1)
  {s with pc := N 4282, stack := (N 16) :: (v3) :: (w1) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: (w15) :: (w16) :: (w17) :: rest}
theorem stage4Part8_run (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions stage4Part8Program {s with pc := N 4272, stack := (w0) :: (w1) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: (w15) :: (w16) :: (w17) :: rest} =
      some (stage4Part8Model s w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 63) : rest.length + j < 1024 := by omega
  have ha192 : (192 : W).toNat = 192 := rfl
  have hf192 := Monpro.activeWords_fix s 192 32 (by decide) (by norm_num) hact
  simp [hz, hzn, stage4Part8Program, stage4Part8Model, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, capacity, ha192, hf192]

def stage4Part9Program : List Instr :=
  [.op .SHR,
   .op (.Swap sA4),
   .op .POP,
   .op (.Dup dA14),
   .push 1 160,
   .op .MLOAD,
   .op (.Dup dA6),
   .op .MULMOD]
def stage4Part9Model (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 : W) (rest : List W) : State :=
  let v0 : W := UInt256.shiftRight (w1) (w0)
  let v1 : W := MachineState.readWord s.memory 160
  let v2 : W := UInt256.mulMod (v0) (v1) (w16)
  {s with pc := N 4291, stack := (v2) :: (w2) :: (w3) :: (w4) :: (w5) :: (v0) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: (w15) :: (w16) :: (w17) :: (w18) :: rest}
theorem stage4Part9_run (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions stage4Part9Program {s with pc := N 4282, stack := (w0) :: (w1) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: (w15) :: (w16) :: (w17) :: (w18) :: rest} =
      some (stage4Part9Model s w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 63) : rest.length + j < 1024 := by omega
  have ha160 : (160 : W).toNat = 160 := rfl
  have hf160 := Monpro.activeWords_fix s 160 32 (by decide) (by norm_num) hact
  simp [hz, hzn, stage4Part9Program, stage4Part9Model, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, capacity, ha160, hf160]

def stage4Part10Program : List Instr :=
  [.op .ADD,
   .op (.Dup dA14),
   .op (.Swap sA0),
   .push 2 2048,
   .op .MULMOD]
def stage4Part10Model (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 : W) (rest : List W) : State :=
  let v0 : W := (w0) + (w1)
  let v1 : W := UInt256.mulMod (N 2048) (v0) (w15)
  {s with pc := N 4298, stack := (v1) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: (w15) :: (w16) :: (w17) :: rest}
theorem stage4Part10_run (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions stage4Part10Program {s with pc := N 4291, stack := (w0) :: (w1) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: (w15) :: (w16) :: (w17) :: rest} =
      some (stage4Part10Model s w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 63) : rest.length + j < 1024 := by omega
  simp [hz, hzn, stage4Part10Program, stage4Part10Model, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, capacity]

def stage4Program : List Instr := (stage4Part0Program ++ (stage4Part1Program ++ (stage4Part2Program ++ (stage4Part3Program ++ (stage4Part4Program ++ (stage4Part5Program ++ (stage4Part6Program ++ (stage4Part7Program ++ (stage4Part8Program ++ (stage4Part9Program ++ (stage4Part10Program)))))))))))
def stage4Model (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 : W) (rest : List W) : State :=
  let v0 : W := UInt256.mulMod (w9) (w5) (w14)
  let v1 : W := UInt256.mulMod (w8) (w6) (w14)
  let v2 : W := (v1) + (v0)
  let v3 : W := (w0) + (v2)
  let v4 : W := UInt256.mulMod (w7) (w7) (w14)
  let v5 : W := (v4) + (v3)
  let v6 : W := UInt256.mulMod (w4) (w13) (w14)
  let v7 : W := (v6) + (v5)
  let v8 : W := UInt256.mulMod (w3) (w12) (w14)
  let v9 : W := (v8) + (v7)
  let v10 : W := UInt256.mulMod (w2) (w11) (w14)
  let v11 : W := (v10) + (v9)
  let v12 : W := UInt256.mulMod (w1) (w10) (w14)
  let v13 : W := (v12) + (v11)
  let v14 : W := (w5) * (w9)
  let v15 : W := (w6) * (w8)
  let v16 : W := (v15) + (v14)
  let v17 : W := (v16) + (w0)
  let v18 : W := (w7) + (w7)
  let v19 : W := (w7) * (w7)
  let v20 : W := (v19) + (v17)
  let v21 : W := (w4) * (w13)
  let v22 : W := (v21) + (v20)
  let v23 : W := (w3) * (w12)
  let v24 : W := (v23) + (v22)
  let v25 : W := (w2) * (w11)
  let v26 : W := (v25) + (v24)
  let v27 : W := (w1) * (w10)
  let v28 : W := (v27) + (v26)
  let v29 : W := MachineState.readWord s.memory 192
  let v30 : W := (v29) * (v28)
  let v31 : W := UInt256.shiftRight (v30) (N 16)
  let v32 : W := MachineState.readWord s.memory 160
  let v33 : W := UInt256.mulMod (v31) (v32) (w14)
  let v34 : W := (v33) + (v13)
  let v35 : W := UInt256.mulMod (N 2048) (v34) (w14)
  {s with pc := N 4298, stack := (v35) :: (w1) :: (w2) :: (w3) :: (v31) :: (w5) :: (w6) :: (v18) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: (w15) :: (w16) :: rest}
theorem stage4_run (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions stage4Program {s with pc := N 4208, stack := (w0) :: (w1) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: (w15) :: (w16) :: rest} = some (stage4Model s w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 rest) := by
  let v0 : W := UInt256.mulMod (w9) (w5) (w14)
  let v1 : W := UInt256.mulMod (w8) (w6) (w14)
  let v2 : W := (v1) + (v0)
  let v3 : W := (w0) + (v2)
  let v4 : W := UInt256.mulMod (w7) (w7) (w14)
  let v5 : W := (v4) + (v3)
  let v6 : W := UInt256.mulMod (w4) (w13) (w14)
  let v7 : W := (v6) + (v5)
  let v8 : W := UInt256.mulMod (w3) (w12) (w14)
  let v9 : W := (v8) + (v7)
  let v10 : W := UInt256.mulMod (w2) (w11) (w14)
  let v11 : W := (v10) + (v9)
  let v12 : W := UInt256.mulMod (w1) (w10) (w14)
  let v13 : W := (v12) + (v11)
  let v14 : W := (w5) * (w9)
  let v15 : W := (w6) * (w8)
  let v16 : W := (v15) + (v14)
  let v17 : W := (v16) + (w0)
  let v18 : W := (w7) + (w7)
  let v19 : W := (w7) * (w7)
  let v20 : W := (v19) + (v17)
  let v21 : W := (w4) * (w13)
  let v22 : W := (v21) + (v20)
  let v23 : W := (w3) * (w12)
  let v24 : W := (v23) + (v22)
  let v25 : W := (w2) * (w11)
  let v26 : W := (v25) + (v24)
  let v27 : W := (w1) * (w10)
  let v28 : W := (v27) + (v26)
  let v29 : W := MachineState.readWord s.memory 192
  let v30 : W := (v29) * (v28)
  let v31 : W := UInt256.shiftRight (v30) (N 16)
  let v32 : W := MachineState.readWord s.memory 160
  let v33 : W := UInt256.mulMod (v31) (v32) (w14)
  let v34 : W := (v33) + (v13)
  let v35 : W := UInt256.mulMod (N 2048) (v34) (w14)
  have h0 : runInstructions stage4Part0Program {s with pc := N 4208, stack := (w0) :: (w1) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: (w15) :: (w16) :: rest} = some {s with pc := N 4216, stack := (v1) :: (v0) :: (w0) :: (w1) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: (w15) :: (w16) :: rest} := by
    simpa only [stage4Part0Model, v0, v1] using stage4Part0_run s (w0) (w1) (w2) (w3) (w4) (w5) (w6) (w7) (w8) (w9) (w10) (w11) (w12) (w13) (w14) (w15) (w16) rest hcap hact
  have h1 : runInstructions stage4Part1Program {s with pc := N 4216, stack := (v1) :: (v0) :: (w0) :: (w1) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: (w15) :: (w16) :: rest} = some {s with pc := N 4224, stack := (v5) :: (w0) :: (w1) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: (w15) :: (w16) :: rest} := by
    simpa only [stage4Part1Model, v2, v3, v4, v5] using stage4Part1_run s (v1) (v0) (w0) (w1) (w2) (w3) (w4) (w5) (w6) (w7) (w8) (w9) (w10) (w11) (w12) (w13) (w14) (w15) (w16) rest hcap hact
  have h2 : runInstructions stage4Part2Program {s with pc := N 4224, stack := (v5) :: (w0) :: (w1) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: (w15) :: (w16) :: rest} = some {s with pc := N 4232, stack := (w3) :: (w12) :: (w14) :: (v7) :: (w0) :: (w1) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: (w15) :: (w16) :: rest} := by
    simpa only [stage4Part2Model, v6, v7] using stage4Part2_run s (v5) (w0) (w1) (w2) (w3) (w4) (w5) (w6) (w7) (w8) (w9) (w10) (w11) (w12) (w13) (w14) (w15) (w16) rest hcap hact
  have h3 : runInstructions stage4Part3Program {s with pc := N 4232, stack := (w3) :: (w12) :: (w14) :: (v7) :: (w0) :: (w1) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: (w15) :: (w16) :: rest} = some {s with pc := N 4240, stack := (w14) :: (v11) :: (w0) :: (w1) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: (w15) :: (w16) :: rest} := by
    simpa only [stage4Part3Model, v8, v9, v10, v11] using stage4Part3_run s (w3) (w12) (w14) (v7) (w0) (w1) (w2) (w3) (w4) (w5) (w6) (w7) (w8) (w9) (w10) (w11) (w12) (w13) (w14) (w15) (w16) rest hcap hact
  have h4 : runInstructions stage4Part4Program {s with pc := N 4240, stack := (w14) :: (v11) :: (w0) :: (w1) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: (w15) :: (w16) :: rest} = some {s with pc := N 4248, stack := (v14) :: (w0) :: (v13) :: (w1) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: (w15) :: (w16) :: rest} := by
    simpa only [stage4Part4Model, v12, v13, v14] using stage4Part4_run s (w14) (v11) (w0) (w1) (w2) (w3) (w4) (w5) (w6) (w7) (w8) (w9) (w10) (w11) (w12) (w13) (w14) (w15) (w16) rest hcap hact
  have h5 : runInstructions stage4Part5Program {s with pc := N 4248, stack := (v14) :: (w0) :: (v13) :: (w1) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: (w15) :: (w16) :: rest} = some {s with pc := N 4256, stack := (w7) :: (w7) :: (w7) :: (v17) :: (v13) :: (w1) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: (w15) :: (w16) :: rest} := by
    simpa only [stage4Part5Model, v15, v16, v17] using stage4Part5_run s (v14) (w0) (v13) (w1) (w2) (w3) (w4) (w5) (w6) (w7) (w8) (w9) (w10) (w11) (w12) (w13) (w14) (w15) (w16) rest hcap hact
  have h6 : runInstructions stage4Part6Program {s with pc := N 4256, stack := (w7) :: (w7) :: (w7) :: (v17) :: (v13) :: (w1) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: (w15) :: (w16) :: rest} = some {s with pc := N 4264, stack := (v22) :: (v13) :: (w1) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (v18) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: (w15) :: (w16) :: rest} := by
    simpa only [stage4Part6Model, v18, v19, v20, v21, v22] using stage4Part6_run s (w7) (w7) (w7) (v17) (v13) (w1) (w2) (w3) (w4) (w5) (w6) (w7) (w8) (w9) (w10) (w11) (w12) (w13) (w14) (w15) (w16) rest hcap hact
  have h7 : runInstructions stage4Part7Program {s with pc := N 4264, stack := (v22) :: (v13) :: (w1) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (v18) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: (w15) :: (w16) :: rest} = some {s with pc := N 4272, stack := (v26) :: (v13) :: (w1) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (v18) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: (w15) :: (w16) :: rest} := by
    simpa only [stage4Part7Model, v23, v24, v25, v26] using stage4Part7_run s (v22) (v13) (w1) (w2) (w3) (w4) (w5) (w6) (v18) (w8) (w9) (w10) (w11) (w12) (w13) (w14) (w15) (w16) rest hcap hact
  have h8 : runInstructions stage4Part8Program {s with pc := N 4272, stack := (v26) :: (v13) :: (w1) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (v18) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: (w15) :: (w16) :: rest} = some {s with pc := N 4282, stack := (N 16) :: (v30) :: (v13) :: (w1) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (v18) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: (w15) :: (w16) :: rest} := by
    simpa only [stage4Part8Model, v27, v28, v29, v30] using stage4Part8_run s (v26) (v13) (w1) (w2) (w3) (w4) (w5) (w6) (v18) (w8) (w9) (w10) (w11) (w12) (w13) (w14) (w15) (w16) rest hcap hact
  have h9 : runInstructions stage4Part9Program {s with pc := N 4282, stack := (N 16) :: (v30) :: (v13) :: (w1) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (v18) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: (w15) :: (w16) :: rest} = some {s with pc := N 4291, stack := (v33) :: (v13) :: (w1) :: (w2) :: (w3) :: (v31) :: (w5) :: (w6) :: (v18) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: (w15) :: (w16) :: rest} := by
    simpa only [stage4Part9Model, v31, v32, v33] using stage4Part9_run s (N 16) (v30) (v13) (w1) (w2) (w3) (w4) (w5) (w6) (v18) (w8) (w9) (w10) (w11) (w12) (w13) (w14) (w15) (w16) rest hcap hact
  have h10 : runInstructions stage4Part10Program {s with pc := N 4291, stack := (v33) :: (v13) :: (w1) :: (w2) :: (w3) :: (v31) :: (w5) :: (w6) :: (v18) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: (w15) :: (w16) :: rest} = some {s with pc := N 4298, stack := (v35) :: (w1) :: (w2) :: (w3) :: (v31) :: (w5) :: (w6) :: (v18) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: (w15) :: (w16) :: rest} := by
    simpa only [stage4Part10Model, v34, v35] using stage4Part10_run s (v33) (v13) (w1) (w2) (w3) (v31) (w5) (w6) (v18) (w8) (w9) (w10) (w11) (w12) (w13) (w14) (w15) (w16) rest hcap hact
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
def stage5Part0Model (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 : W) (rest : List W) : State :=
  let v0 : W := (w6) * (w9)
  let v1 : W := (w7) * (w8)
  let v2 : W := (v1) + (v0)
  {s with pc := N 4306, stack := (v2) :: (w0) :: (w0) :: (w1) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: (w15) :: (w16) :: rest}
theorem stage5Part0_run (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions stage5Part0Program {s with pc := N 4298, stack := (w0) :: (w1) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: (w15) :: (w16) :: rest} =
      some (stage5Part0Model s w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 63) : rest.length + j < 1024 := by omega
  simp [hz, hzn, stage5Part0Program, stage5Part0Model, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, capacity]

def stage5Part1Program : List Instr :=
  [.op .ADD,
   .op (.Dup dA14),
   .op (.Dup dA5),
   .op .MUL,
   .op .ADD,
   .op (.Dup dA13),
   .op (.Dup dA4),
   .op .MUL]
def stage5Part1Model (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 : W) (rest : List W) : State :=
  let v0 : W := (w0) + (w1)
  let v1 : W := (w5) * (w15)
  let v2 : W := (v1) + (v0)
  let v3 : W := (w4) * (w14)
  {s with pc := N 4314, stack := (v3) :: (v2) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: (w15) :: (w16) :: (w17) :: (w18) :: rest}
theorem stage5Part1_run (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions stage5Part1Program {s with pc := N 4306, stack := (w0) :: (w1) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: (w15) :: (w16) :: (w17) :: (w18) :: rest} =
      some (stage5Part1Model s w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 63) : rest.length + j < 1024 := by omega
  simp [hz, hzn, stage5Part1Program, stage5Part1Model, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, capacity]

def stage5Part2Program : List Instr :=
  [.op .ADD,
   .op (.Dup dA12),
   .op (.Dup dA3),
   .op .MUL,
   .op .ADD,
   .op (.Dup dA11),
   .op (.Dup dA6),
   .op .MUL]
def stage5Part2Model (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 : W) (rest : List W) : State :=
  let v0 : W := (w0) + (w1)
  let v1 : W := (w3) * (w13)
  let v2 : W := (v1) + (v0)
  let v3 : W := (w6) * (w12)
  {s with pc := N 4322, stack := (v3) :: (v2) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: (w15) :: (w16) :: (w17) :: (w18) :: rest}
theorem stage5Part2_run (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions stage5Part2Program {s with pc := N 4314, stack := (w0) :: (w1) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: (w15) :: (w16) :: (w17) :: (w18) :: rest} =
      some (stage5Part2Model s w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 63) : rest.length + j < 1024 := by omega
  simp [hz, hzn, stage5Part2Program, stage5Part2Model, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, capacity]

def stage5Part3Program : List Instr :=
  [.op .ADD,
   .op (.Swap sA0),
   .op (.Dup dA15),
   .op (.Dup dA0),
   .op (.Dup dA12),
   .op (.Dup dA10),
   .op .MULMOD,
   .op (.Swap sA0)]
def stage5Part3Model (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 : W) (rest : List W) : State :=
  let v0 : W := (w0) + (w1)
  let v1 : W := UInt256.mulMod (w8) (w11) (w16)
  {s with pc := N 4330, stack := (w16) :: (v1) :: (w2) :: (v0) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: (w15) :: (w16) :: (w17) :: (w18) :: rest}
theorem stage5Part3_run (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions stage5Part3Program {s with pc := N 4322, stack := (w0) :: (w1) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: (w15) :: (w16) :: (w17) :: (w18) :: rest} =
      some (stage5Part3Model s w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 63) : rest.length + j < 1024 := by omega
  simp [hz, hzn, stage5Part3Program, stage5Part3Model, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, capacity]

def stage5Part4Program : List Instr :=
  [.op (.Dup dA11),
   .op (.Dup dA11),
   .op .MULMOD,
   .op .ADD,
   .op .ADD,
   .op (.Dup dA15),
   .op (.Dup dA15),
   .op (.Dup dA6)]
def stage5Part4Model (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 : W) (rest : List W) : State :=
  let v0 : W := UInt256.mulMod (w10) (w11) (w0)
  let v1 : W := (v0) + (w1)
  let v2 : W := (v1) + (w2)
  {s with pc := N 4338, stack := (w6) :: (w16) :: (w17) :: (v2) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: (w15) :: (w16) :: (w17) :: (w18) :: (w19) :: rest}
theorem stage5Part4_run (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions stage5Part4Program {s with pc := N 4330, stack := (w0) :: (w1) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: (w15) :: (w16) :: (w17) :: (w18) :: (w19) :: rest} =
      some (stage5Part4Model s w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 63) : rest.length + j < 1024 := by omega
  simp [hz, hzn, stage5Part4Program, stage5Part4Model, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, capacity]

def stage5Part5Program : List Instr :=
  [.op .MULMOD,
   .op .ADD,
   .op (.Dup dA15),
   .op (.Dup dA14),
   .op (.Dup dA5),
   .op .MULMOD,
   .op .ADD,
   .op (.Dup dA15)]
def stage5Part5Model (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 w20 : W) (rest : List W) : State :=
  let v0 : W := UInt256.mulMod (w0) (w1) (w2)
  let v1 : W := (v0) + (w3)
  let v2 : W := UInt256.mulMod (w6) (w16) (w18)
  let v3 : W := (v2) + (v1)
  {s with pc := N 4346, stack := (w18) :: (v3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: (w15) :: (w16) :: (w17) :: (w18) :: (w19) :: (w20) :: rest}
theorem stage5Part5_run (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 w20 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions stage5Part5Program {s with pc := N 4338, stack := (w0) :: (w1) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: (w15) :: (w16) :: (w17) :: (w18) :: (w19) :: (w20) :: rest} =
      some (stage5Part5Model s w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 w20 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 63) : rest.length + j < 1024 := by omega
  simp [hz, hzn, stage5Part5Program, stage5Part5Model, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, capacity]

def stage5Part6Program : List Instr :=
  [.op (.Dup dA13),
   .op (.Dup dA4),
   .op .MULMOD,
   .op .ADD,
   .op (.Dup dA15),
   .op (.Dup dA12),
   .op (.Dup dA7),
   .op .MULMOD]
def stage5Part6Model (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 : W) (rest : List W) : State :=
  let v0 : W := UInt256.mulMod (w3) (w13) (w0)
  let v1 : W := (v0) + (w1)
  let v2 : W := UInt256.mulMod (w6) (w12) (w16)
  {s with pc := N 4354, stack := (v2) :: (v1) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: (w15) :: (w16) :: (w17) :: (w18) :: rest}
theorem stage5Part6_run (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions stage5Part6Program {s with pc := N 4346, stack := (w0) :: (w1) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: (w15) :: (w16) :: (w17) :: (w18) :: rest} =
      some (stage5Part6Model s w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 63) : rest.length + j < 1024 := by omega
  simp [hz, hzn, stage5Part6Program, stage5Part6Model, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, capacity]

def stage5Part7Program : List Instr :=
  [.op .ADD,
   .op (.Swap sA0),
   .push 30 1766847064778384329583297500742918515827483896875618958121606201292619775,
   .op .AND,
   .op (.Dup dA0),
   .op (.Swap sA6),
   .op .POP,
   .op (.Dup dA15)]
def stage5Part7Model (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 : W) (rest : List W) : State :=
  let v0 : W := (w0) + (w1)
  let v1 : W := UInt256.land (N 1766847064778384329583297500742918515827483896875618958121606201292619775) (w2)
  {s with pc := N 4392, stack := (w16) :: (v1) :: (v0) :: (w3) :: (w4) :: (w5) :: (w6) :: (v1) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: (w15) :: (w16) :: (w17) :: (w18) :: rest}
theorem stage5Part7_run (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions stage5Part7Program {s with pc := N 4354, stack := (w0) :: (w1) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: (w15) :: (w16) :: (w17) :: (w18) :: rest} =
      some (stage5Part7Model s w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 63) : rest.length + j < 1024 := by omega
  simp [hz, hzn, stage5Part7Program, stage5Part7Model, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, capacity]

def stage5Part8Program : List Instr :=
  [.op (.Swap sA1),
   .op .SUB,
   .op (.Dup dA1),
   .op .ADD,
   .push 2 2048,
   .op .MULMOD]
def stage5Part8Model (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 : W) (rest : List W) : State :=
  let v0 : W := (w2) - (w1)
  let v1 : W := (w0) + (v0)
  let v2 : W := UInt256.mulMod (N 2048) (v1) (w0)
  {s with pc := N 4400, stack := (v2) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: (w15) :: (w16) :: (w17) :: (w18) :: rest}
theorem stage5Part8_run (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions stage5Part8Program {s with pc := N 4392, stack := (w0) :: (w1) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: (w15) :: (w16) :: (w17) :: (w18) :: rest} =
      some (stage5Part8Model s w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 63) : rest.length + j < 1024 := by omega
  simp [hz, hzn, stage5Part8Program, stage5Part8Model, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, capacity]

def stage5Program : List Instr := (stage5Part0Program ++ (stage5Part1Program ++ (stage5Part2Program ++ (stage5Part3Program ++ (stage5Part4Program ++ (stage5Part5Program ++ (stage5Part6Program ++ (stage5Part7Program ++ (stage5Part8Program)))))))))
def stage5Model (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 : W) (rest : List W) : State :=
  let v0 : W := (w6) * (w9)
  let v1 : W := (w7) * (w8)
  let v2 : W := (v1) + (v0)
  let v3 : W := (v2) + (w0)
  let v4 : W := (w3) * (w13)
  let v5 : W := (v4) + (v3)
  let v6 : W := (w2) * (w12)
  let v7 : W := (v6) + (v5)
  let v8 : W := (w1) * (w11)
  let v9 : W := (v8) + (v7)
  let v10 : W := (w4) * (w10)
  let v11 : W := (v10) + (v9)
  let v12 : W := UInt256.mulMod (w6) (w9) (w14)
  let v13 : W := UInt256.mulMod (w7) (w8) (w14)
  let v14 : W := (v13) + (v12)
  let v15 : W := (v14) + (w0)
  let v16 : W := UInt256.mulMod (w3) (w13) (w14)
  let v17 : W := (v16) + (v15)
  let v18 : W := UInt256.mulMod (w2) (w12) (w14)
  let v19 : W := (v18) + (v17)
  let v20 : W := UInt256.mulMod (w1) (w11) (w14)
  let v21 : W := (v20) + (v19)
  let v22 : W := UInt256.mulMod (w4) (w10) (w14)
  let v23 : W := (v22) + (v21)
  let v24 : W := UInt256.land (N 1766847064778384329583297500742918515827483896875618958121606201292619775) (v11)
  let v25 : W := (v23) - (v24)
  let v26 : W := (w14) + (v25)
  let v27 : W := UInt256.mulMod (N 2048) (v26) (w14)
  {s with pc := N 4400, stack := (v27) :: (w1) :: (w2) :: (w3) :: (w4) :: (v24) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: (w15) :: (w16) :: rest}
theorem stage5_run (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions stage5Program {s with pc := N 4298, stack := (w0) :: (w1) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: (w15) :: (w16) :: rest} = some (stage5Model s w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 rest) := by
  let v0 : W := (w6) * (w9)
  let v1 : W := (w7) * (w8)
  let v2 : W := (v1) + (v0)
  let v3 : W := (v2) + (w0)
  let v4 : W := (w3) * (w13)
  let v5 : W := (v4) + (v3)
  let v6 : W := (w2) * (w12)
  let v7 : W := (v6) + (v5)
  let v8 : W := (w1) * (w11)
  let v9 : W := (v8) + (v7)
  let v10 : W := (w4) * (w10)
  let v11 : W := (v10) + (v9)
  let v12 : W := UInt256.mulMod (w6) (w9) (w14)
  let v13 : W := UInt256.mulMod (w7) (w8) (w14)
  let v14 : W := (v13) + (v12)
  let v15 : W := (v14) + (w0)
  let v16 : W := UInt256.mulMod (w3) (w13) (w14)
  let v17 : W := (v16) + (v15)
  let v18 : W := UInt256.mulMod (w2) (w12) (w14)
  let v19 : W := (v18) + (v17)
  let v20 : W := UInt256.mulMod (w1) (w11) (w14)
  let v21 : W := (v20) + (v19)
  let v22 : W := UInt256.mulMod (w4) (w10) (w14)
  let v23 : W := (v22) + (v21)
  let v24 : W := UInt256.land (N 1766847064778384329583297500742918515827483896875618958121606201292619775) (v11)
  let v25 : W := (v23) - (v24)
  let v26 : W := (w14) + (v25)
  let v27 : W := UInt256.mulMod (N 2048) (v26) (w14)
  have h0 : runInstructions stage5Part0Program {s with pc := N 4298, stack := (w0) :: (w1) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: (w15) :: (w16) :: rest} = some {s with pc := N 4306, stack := (v2) :: (w0) :: (w0) :: (w1) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: (w15) :: (w16) :: rest} := by
    simpa only [stage5Part0Model, v0, v1, v2] using stage5Part0_run s (w0) (w1) (w2) (w3) (w4) (w5) (w6) (w7) (w8) (w9) (w10) (w11) (w12) (w13) (w14) (w15) (w16) rest hcap hact
  have h1 : runInstructions stage5Part1Program {s with pc := N 4306, stack := (v2) :: (w0) :: (w0) :: (w1) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: (w15) :: (w16) :: rest} = some {s with pc := N 4314, stack := (v6) :: (v5) :: (w0) :: (w1) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: (w15) :: (w16) :: rest} := by
    simpa only [stage5Part1Model, v3, v4, v5, v6] using stage5Part1_run s (v2) (w0) (w0) (w1) (w2) (w3) (w4) (w5) (w6) (w7) (w8) (w9) (w10) (w11) (w12) (w13) (w14) (w15) (w16) rest hcap hact
  have h2 : runInstructions stage5Part2Program {s with pc := N 4314, stack := (v6) :: (v5) :: (w0) :: (w1) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: (w15) :: (w16) :: rest} = some {s with pc := N 4322, stack := (v10) :: (v9) :: (w0) :: (w1) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: (w15) :: (w16) :: rest} := by
    simpa only [stage5Part2Model, v7, v8, v9, v10] using stage5Part2_run s (v6) (v5) (w0) (w1) (w2) (w3) (w4) (w5) (w6) (w7) (w8) (w9) (w10) (w11) (w12) (w13) (w14) (w15) (w16) rest hcap hact
  have h3 : runInstructions stage5Part3Program {s with pc := N 4322, stack := (v10) :: (v9) :: (w0) :: (w1) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: (w15) :: (w16) :: rest} = some {s with pc := N 4330, stack := (w14) :: (v12) :: (w0) :: (v11) :: (w1) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: (w15) :: (w16) :: rest} := by
    simpa only [stage5Part3Model, v11, v12] using stage5Part3_run s (v10) (v9) (w0) (w1) (w2) (w3) (w4) (w5) (w6) (w7) (w8) (w9) (w10) (w11) (w12) (w13) (w14) (w15) (w16) rest hcap hact
  have h4 : runInstructions stage5Part4Program {s with pc := N 4330, stack := (w14) :: (v12) :: (w0) :: (v11) :: (w1) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: (w15) :: (w16) :: rest} = some {s with pc := N 4338, stack := (w3) :: (w13) :: (w14) :: (v15) :: (v11) :: (w1) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: (w15) :: (w16) :: rest} := by
    simpa only [stage5Part4Model, v13, v14, v15] using stage5Part4_run s (w14) (v12) (w0) (v11) (w1) (w2) (w3) (w4) (w5) (w6) (w7) (w8) (w9) (w10) (w11) (w12) (w13) (w14) (w15) (w16) rest hcap hact
  have h5 : runInstructions stage5Part5Program {s with pc := N 4338, stack := (w3) :: (w13) :: (w14) :: (v15) :: (v11) :: (w1) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: (w15) :: (w16) :: rest} = some {s with pc := N 4346, stack := (w14) :: (v19) :: (v11) :: (w1) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: (w15) :: (w16) :: rest} := by
    simpa only [stage5Part5Model, v16, v17, v18, v19] using stage5Part5_run s (w3) (w13) (w14) (v15) (v11) (w1) (w2) (w3) (w4) (w5) (w6) (w7) (w8) (w9) (w10) (w11) (w12) (w13) (w14) (w15) (w16) rest hcap hact
  have h6 : runInstructions stage5Part6Program {s with pc := N 4346, stack := (w14) :: (v19) :: (v11) :: (w1) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: (w15) :: (w16) :: rest} = some {s with pc := N 4354, stack := (v22) :: (v21) :: (v11) :: (w1) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: (w15) :: (w16) :: rest} := by
    simpa only [stage5Part6Model, v20, v21, v22] using stage5Part6_run s (w14) (v19) (v11) (w1) (w2) (w3) (w4) (w5) (w6) (w7) (w8) (w9) (w10) (w11) (w12) (w13) (w14) (w15) (w16) rest hcap hact
  have h7 : runInstructions stage5Part7Program {s with pc := N 4354, stack := (v22) :: (v21) :: (v11) :: (w1) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: (w15) :: (w16) :: rest} = some {s with pc := N 4392, stack := (w14) :: (v24) :: (v23) :: (w1) :: (w2) :: (w3) :: (w4) :: (v24) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: (w15) :: (w16) :: rest} := by
    simpa only [stage5Part7Model, v23, v24] using stage5Part7_run s (v22) (v21) (v11) (w1) (w2) (w3) (w4) (w5) (w6) (w7) (w8) (w9) (w10) (w11) (w12) (w13) (w14) (w15) (w16) rest hcap hact
  have h8 : runInstructions stage5Part8Program {s with pc := N 4392, stack := (w14) :: (v24) :: (v23) :: (w1) :: (w2) :: (w3) :: (w4) :: (v24) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: (w15) :: (w16) :: rest} = some {s with pc := N 4400, stack := (v27) :: (w1) :: (w2) :: (w3) :: (w4) :: (v24) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: (w15) :: (w16) :: rest} := by
    simpa only [stage5Part8Model, v25, v26, v27] using stage5Part8_run s (w14) (v24) (v23) (w1) (w2) (w3) (w4) (v24) (w6) (w7) (w8) (w9) (w10) (w11) (w12) (w13) (w14) (w15) (w16) rest hcap hact
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
def stage6Part0Model (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 : W) (rest : List W) : State :=
  let v0 : W := (w7) * (w9)
  let v1 : W := (v0) + (w0)
  let v2 : W := (w8) * (w8)
  {s with pc := N 4408, stack := (v2) :: (v1) :: (w0) :: (w1) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: (w15) :: (w16) :: rest}
theorem stage6Part0_run (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions stage6Part0Program {s with pc := N 4400, stack := (w0) :: (w1) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: (w15) :: (w16) :: rest} =
      some (stage6Part0Model s w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 63) : rest.length + j < 1024 := by omega
  simp [hz, hzn, stage6Part0Program, stage6Part0Model, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, capacity]

def stage6Part1Program : List Instr :=
  [.op .ADD,
   .op (.Dup dA14),
   .op (.Dup dA4),
   .op .MUL,
   .op .ADD,
   .op (.Dup dA13),
   .op (.Dup dA3),
   .op .MUL]
def stage6Part1Model (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 : W) (rest : List W) : State :=
  let v0 : W := (w0) + (w1)
  let v1 : W := (w4) * (w15)
  let v2 : W := (v1) + (v0)
  let v3 : W := (w3) * (w14)
  {s with pc := N 4416, stack := (v3) :: (v2) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: (w15) :: (w16) :: (w17) :: (w18) :: rest}
theorem stage6Part1_run (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions stage6Part1Program {s with pc := N 4408, stack := (w0) :: (w1) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: (w15) :: (w16) :: (w17) :: (w18) :: rest} =
      some (stage6Part1Model s w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 63) : rest.length + j < 1024 := by omega
  simp [hz, hzn, stage6Part1Program, stage6Part1Model, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, capacity]

def stage6Part2Program : List Instr :=
  [.op .ADD,
   .op (.Dup dA12),
   .op (.Dup dA6),
   .op .MUL,
   .op .ADD,
   .op (.Swap sA0),
   .op (.Dup dA15),
   .op (.Dup dA11)]
def stage6Part2Model (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 : W) (rest : List W) : State :=
  let v0 : W := (w0) + (w1)
  let v1 : W := (w6) * (w13)
  let v2 : W := (v1) + (v0)
  {s with pc := N 4424, stack := (w11) :: (w16) :: (w2) :: (v2) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: (w15) :: (w16) :: (w17) :: (w18) :: rest}
theorem stage6Part2_run (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions stage6Part2Program {s with pc := N 4416, stack := (w0) :: (w1) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: (w15) :: (w16) :: (w17) :: (w18) :: rest} =
      some (stage6Part2Model s w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 63) : rest.length + j < 1024 := by omega
  simp [hz, hzn, stage6Part2Program, stage6Part2Model, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, capacity]

def stage6Part3Program : List Instr :=
  [.op (.Dup dA10),
   .op .MULMOD,
   .op .ADD,
   .op (.Dup dA15),
   .op (.Dup dA10),
   .op (.Dup dA0),
   .op (.Dup dA0),
   .op .ADD]
def stage6Part3Model (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 : W) (rest : List W) : State :=
  let v0 : W := UInt256.mulMod (w10) (w0) (w1)
  let v1 : W := (v0) + (w2)
  let v2 : W := (w11) + (w11)
  {s with pc := N 4432, stack := (v2) :: (w11) :: (w17) :: (v1) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: (w15) :: (w16) :: (w17) :: (w18) :: (w19) :: rest}
theorem stage6Part3_run (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions stage6Part3Program {s with pc := N 4424, stack := (w0) :: (w1) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: (w15) :: (w16) :: (w17) :: (w18) :: (w19) :: rest} =
      some (stage6Part3Model s w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 63) : rest.length + j < 1024 := by omega
  simp [hz, hzn, stage6Part3Program, stage6Part3Model, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, capacity]

def stage6Part4Program : List Instr :=
  [.op (.Swap sA11),
   .op .MULMOD,
   .op .ADD,
   .op (.Dup dA15),
   .op (.Dup dA15),
   .op (.Dup dA5),
   .op .MULMOD,
   .op .ADD]
def stage6Part4Model (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 w20 : W) (rest : List W) : State :=
  let v0 : W := UInt256.mulMod (w12) (w1) (w2)
  let v1 : W := (v0) + (w3)
  let v2 : W := UInt256.mulMod (w6) (w17) (w18)
  let v3 : W := (v2) + (v1)
  {s with pc := N 4440, stack := (v3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w0) :: (w13) :: (w14) :: (w15) :: (w16) :: (w17) :: (w18) :: (w19) :: (w20) :: rest}
theorem stage6Part4_run (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 w20 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions stage6Part4Program {s with pc := N 4432, stack := (w0) :: (w1) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: (w15) :: (w16) :: (w17) :: (w18) :: (w19) :: (w20) :: rest} =
      some (stage6Part4Model s w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 w20 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 63) : rest.length + j < 1024 := by omega
  simp [hz, hzn, stage6Part4Program, stage6Part4Model, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, capacity]

def stage6Part5Program : List Instr :=
  [.op (.Dup dA15),
   .op (.Dup dA14),
   .op (.Dup dA4),
   .op .MULMOD,
   .op .ADD,
   .op (.Dup dA15),
   .op (.Dup dA13),
   .op (.Dup dA7)]
def stage6Part5Model (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 : W) (rest : List W) : State :=
  let v0 : W := UInt256.mulMod (w2) (w13) (w15)
  let v1 : W := (v0) + (w0)
  {s with pc := N 4448, stack := (w5) :: (w12) :: (w15) :: (v1) :: (w1) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: (w15) :: (w16) :: (w17) :: rest}
theorem stage6Part5_run (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions stage6Part5Program {s with pc := N 4440, stack := (w0) :: (w1) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: (w15) :: (w16) :: (w17) :: rest} =
      some (stage6Part5Model s w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 63) : rest.length + j < 1024 := by omega
  simp [hz, hzn, stage6Part5Program, stage6Part5Model, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, capacity]

def stage6Part6Program : List Instr :=
  [.op .MULMOD,
   .op .ADD,
   .op (.Swap sA0),
   .push 30 1766847064778384329583297500742918515827483896875618958121606201292619775,
   .op .AND,
   .op (.Dup dA0),
   .op (.Swap sA7),
   .op .POP]
def stage6Part6Model (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 w20 : W) (rest : List W) : State :=
  let v0 : W := UInt256.mulMod (w0) (w1) (w2)
  let v1 : W := (v0) + (w3)
  let v2 : W := UInt256.land (N 1766847064778384329583297500742918515827483896875618958121606201292619775) (w4)
  {s with pc := N 4486, stack := (v2) :: (v1) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (v2) :: (w11) :: (w12) :: (w13) :: (w14) :: (w15) :: (w16) :: (w17) :: (w18) :: (w19) :: (w20) :: rest}
theorem stage6Part6_run (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 w20 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions stage6Part6Program {s with pc := N 4448, stack := (w0) :: (w1) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: (w15) :: (w16) :: (w17) :: (w18) :: (w19) :: (w20) :: rest} =
      some (stage6Part6Model s w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 w20 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 63) : rest.length + j < 1024 := by omega
  simp [hz, hzn, stage6Part6Program, stage6Part6Model, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, capacity]

def stage6Part7Program : List Instr :=
  [.op (.Dup dA15),
   .op (.Swap sA1),
   .op .SUB,
   .op (.Dup dA1),
   .op .ADD,
   .push 2 2048,
   .op .MULMOD]
def stage6Part7Model (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 : W) (rest : List W) : State :=
  let v0 : W := (w1) - (w0)
  let v1 : W := (w15) + (v0)
  let v2 : W := UInt256.mulMod (N 2048) (v1) (w15)
  {s with pc := N 4495, stack := (v2) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: (w15) :: (w16) :: (w17) :: rest}
theorem stage6Part7_run (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions stage6Part7Program {s with pc := N 4486, stack := (w0) :: (w1) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: (w15) :: (w16) :: (w17) :: rest} =
      some (stage6Part7Model s w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 63) : rest.length + j < 1024 := by omega
  simp [hz, hzn, stage6Part7Program, stage6Part7Model, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, capacity]

def stage6Program : List Instr := (stage6Part0Program ++ (stage6Part1Program ++ (stage6Part2Program ++ (stage6Part3Program ++ (stage6Part4Program ++ (stage6Part5Program ++ (stage6Part6Program ++ (stage6Part7Program))))))))
def stage6Model (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 : W) (rest : List W) : State :=
  let v0 : W := (w7) * (w9)
  let v1 : W := (v0) + (w0)
  let v2 : W := (w8) * (w8)
  let v3 : W := (v2) + (v1)
  let v4 : W := (w2) * (w13)
  let v5 : W := (v4) + (v3)
  let v6 : W := (w1) * (w12)
  let v7 : W := (v6) + (v5)
  let v8 : W := (w4) * (w11)
  let v9 : W := (v8) + (v7)
  let v10 : W := UInt256.mulMod (w7) (w9) (w14)
  let v11 : W := (v10) + (w0)
  let v12 : W := (w8) + (w8)
  let v13 : W := UInt256.mulMod (w8) (w8) (w14)
  let v14 : W := (v13) + (v11)
  let v15 : W := UInt256.mulMod (w2) (w13) (w14)
  let v16 : W := (v15) + (v14)
  let v17 : W := UInt256.mulMod (w1) (w12) (w14)
  let v18 : W := (v17) + (v16)
  let v19 : W := UInt256.mulMod (w4) (w11) (w14)
  let v20 : W := (v19) + (v18)
  let v21 : W := UInt256.land (N 1766847064778384329583297500742918515827483896875618958121606201292619775) (v9)
  let v22 : W := (v20) - (v21)
  let v23 : W := (w14) + (v22)
  let v24 : W := UInt256.mulMod (N 2048) (v23) (w14)
  {s with pc := N 4495, stack := (v24) :: (w1) :: (w2) :: (w3) :: (w4) :: (w5) :: (v21) :: (w7) :: (v12) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: (w15) :: (w16) :: rest}
theorem stage6_run (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions stage6Program {s with pc := N 4400, stack := (w0) :: (w1) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: (w15) :: (w16) :: rest} = some (stage6Model s w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 rest) := by
  let v0 : W := (w7) * (w9)
  let v1 : W := (v0) + (w0)
  let v2 : W := (w8) * (w8)
  let v3 : W := (v2) + (v1)
  let v4 : W := (w2) * (w13)
  let v5 : W := (v4) + (v3)
  let v6 : W := (w1) * (w12)
  let v7 : W := (v6) + (v5)
  let v8 : W := (w4) * (w11)
  let v9 : W := (v8) + (v7)
  let v10 : W := UInt256.mulMod (w7) (w9) (w14)
  let v11 : W := (v10) + (w0)
  let v12 : W := (w8) + (w8)
  let v13 : W := UInt256.mulMod (w8) (w8) (w14)
  let v14 : W := (v13) + (v11)
  let v15 : W := UInt256.mulMod (w2) (w13) (w14)
  let v16 : W := (v15) + (v14)
  let v17 : W := UInt256.mulMod (w1) (w12) (w14)
  let v18 : W := (v17) + (v16)
  let v19 : W := UInt256.mulMod (w4) (w11) (w14)
  let v20 : W := (v19) + (v18)
  let v21 : W := UInt256.land (N 1766847064778384329583297500742918515827483896875618958121606201292619775) (v9)
  let v22 : W := (v20) - (v21)
  let v23 : W := (w14) + (v22)
  let v24 : W := UInt256.mulMod (N 2048) (v23) (w14)
  have h0 : runInstructions stage6Part0Program {s with pc := N 4400, stack := (w0) :: (w1) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: (w15) :: (w16) :: rest} = some {s with pc := N 4408, stack := (v2) :: (v1) :: (w0) :: (w1) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: (w15) :: (w16) :: rest} := by
    simpa only [stage6Part0Model, v0, v1, v2] using stage6Part0_run s (w0) (w1) (w2) (w3) (w4) (w5) (w6) (w7) (w8) (w9) (w10) (w11) (w12) (w13) (w14) (w15) (w16) rest hcap hact
  have h1 : runInstructions stage6Part1Program {s with pc := N 4408, stack := (v2) :: (v1) :: (w0) :: (w1) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: (w15) :: (w16) :: rest} = some {s with pc := N 4416, stack := (v6) :: (v5) :: (w0) :: (w1) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: (w15) :: (w16) :: rest} := by
    simpa only [stage6Part1Model, v3, v4, v5, v6] using stage6Part1_run s (v2) (v1) (w0) (w1) (w2) (w3) (w4) (w5) (w6) (w7) (w8) (w9) (w10) (w11) (w12) (w13) (w14) (w15) (w16) rest hcap hact
  have h2 : runInstructions stage6Part2Program {s with pc := N 4416, stack := (v6) :: (v5) :: (w0) :: (w1) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: (w15) :: (w16) :: rest} = some {s with pc := N 4424, stack := (w9) :: (w14) :: (w0) :: (v9) :: (w1) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: (w15) :: (w16) :: rest} := by
    simpa only [stage6Part2Model, v7, v8, v9] using stage6Part2_run s (v6) (v5) (w0) (w1) (w2) (w3) (w4) (w5) (w6) (w7) (w8) (w9) (w10) (w11) (w12) (w13) (w14) (w15) (w16) rest hcap hact
  have h3 : runInstructions stage6Part3Program {s with pc := N 4424, stack := (w9) :: (w14) :: (w0) :: (v9) :: (w1) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: (w15) :: (w16) :: rest} = some {s with pc := N 4432, stack := (v12) :: (w8) :: (w14) :: (v11) :: (v9) :: (w1) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: (w15) :: (w16) :: rest} := by
    simpa only [stage6Part3Model, v10, v11, v12] using stage6Part3_run s (w9) (w14) (w0) (v9) (w1) (w2) (w3) (w4) (w5) (w6) (w7) (w8) (w9) (w10) (w11) (w12) (w13) (w14) (w15) (w16) rest hcap hact
  have h4 : runInstructions stage6Part4Program {s with pc := N 4432, stack := (v12) :: (w8) :: (w14) :: (v11) :: (v9) :: (w1) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: (w15) :: (w16) :: rest} = some {s with pc := N 4440, stack := (v16) :: (v9) :: (w1) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (v12) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: (w15) :: (w16) :: rest} := by
    simpa only [stage6Part4Model, v13, v14, v15, v16] using stage6Part4_run s (v12) (w8) (w14) (v11) (v9) (w1) (w2) (w3) (w4) (w5) (w6) (w7) (w8) (w9) (w10) (w11) (w12) (w13) (w14) (w15) (w16) rest hcap hact
  have h5 : runInstructions stage6Part5Program {s with pc := N 4440, stack := (v16) :: (v9) :: (w1) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (v12) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: (w15) :: (w16) :: rest} = some {s with pc := N 4448, stack := (w4) :: (w11) :: (w14) :: (v18) :: (v9) :: (w1) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (v12) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: (w15) :: (w16) :: rest} := by
    simpa only [stage6Part5Model, v17, v18] using stage6Part5_run s (v16) (v9) (w1) (w2) (w3) (w4) (w5) (w6) (w7) (v12) (w9) (w10) (w11) (w12) (w13) (w14) (w15) (w16) rest hcap hact
  have h6 : runInstructions stage6Part6Program {s with pc := N 4448, stack := (w4) :: (w11) :: (w14) :: (v18) :: (v9) :: (w1) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (v12) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: (w15) :: (w16) :: rest} = some {s with pc := N 4486, stack := (v21) :: (v20) :: (w1) :: (w2) :: (w3) :: (w4) :: (w5) :: (v21) :: (w7) :: (v12) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: (w15) :: (w16) :: rest} := by
    simpa only [stage6Part6Model, v19, v20, v21] using stage6Part6_run s (w4) (w11) (w14) (v18) (v9) (w1) (w2) (w3) (w4) (w5) (w6) (w7) (v12) (w9) (w10) (w11) (w12) (w13) (w14) (w15) (w16) rest hcap hact
  have h7 : runInstructions stage6Part7Program {s with pc := N 4486, stack := (v21) :: (v20) :: (w1) :: (w2) :: (w3) :: (w4) :: (w5) :: (v21) :: (w7) :: (v12) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: (w15) :: (w16) :: rest} = some {s with pc := N 4495, stack := (v24) :: (w1) :: (w2) :: (w3) :: (w4) :: (w5) :: (v21) :: (w7) :: (v12) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: (w15) :: (w16) :: rest} := by
    simpa only [stage6Part7Model, v22, v23, v24] using stage6Part7_run s (v21) (v20) (w1) (w2) (w3) (w4) (w5) (v21) (w7) (v12) (w9) (w10) (w11) (w12) (w13) (w14) (w15) (w16) rest hcap hact
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
def stage7Part0Model (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 : W) (rest : List W) : State :=
  let v0 : W := (w8) * (w9)
  let v1 : W := (v0) + (w0)
  let v2 : W := (w1) * (w13)
  {s with pc := N 4503, stack := (v2) :: (v1) :: (w0) :: (w1) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: (w15) :: (w16) :: rest}
theorem stage7Part0_run (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions stage7Part0Program {s with pc := N 4495, stack := (w0) :: (w1) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: (w15) :: (w16) :: rest} =
      some (stage7Part0Model s w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 63) : rest.length + j < 1024 := by omega
  simp [hz, hzn, stage7Part0Program, stage7Part0Model, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, capacity]

def stage7Part1Program : List Instr :=
  [.op .ADD,
   .op (.Dup dA13),
   .op (.Dup dA6),
   .op .MUL,
   .op .ADD,
   .push 30 1766847064778384329583297500742918515827483896875618958121606201292619775,
   .op .AND,
   .op (.Swap sA7)]
def stage7Part1Model (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 : W) (rest : List W) : State :=
  let v0 : W := (w0) + (w1)
  let v1 : W := (w6) * (w14)
  let v2 : W := (v1) + (v0)
  let v3 : W := UInt256.land (N 1766847064778384329583297500742918515827483896875618958121606201292619775) (v2)
  {s with pc := N 4541, stack := (w9) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (v3) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: (w15) :: (w16) :: (w17) :: (w18) :: rest}
theorem stage7Part1_run (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions stage7Part1Program {s with pc := N 4503, stack := (w0) :: (w1) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: (w15) :: (w16) :: (w17) :: (w18) :: rest} =
      some (stage7Part1Model s w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 63) : rest.length + j < 1024 := by omega
  simp [hz, hzn, stage7Part1Program, stage7Part1Model, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, capacity]

def stage7Part2Program : List Instr :=
  [.op .POP,
   .op (.Dup dA14),
   .op (.Dup dA9),
   .op (.Dup dA11),
   .op .MULMOD,
   .op .ADD,
   .op (.Dup dA14),
   .op (.Dup dA2)]
def stage7Part2Model (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 : W) (rest : List W) : State :=
  let v0 : W := UInt256.mulMod (w10) (w9) (w15)
  let v1 : W := (v0) + (w1)
  {s with pc := N 4549, stack := (w2) :: (w15) :: (v1) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: (w15) :: (w16) :: (w17) :: rest}
theorem stage7Part2_run (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions stage7Part2Program {s with pc := N 4541, stack := (w0) :: (w1) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: (w15) :: (w16) :: (w17) :: rest} =
      some (stage7Part2Model s w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 63) : rest.length + j < 1024 := by omega
  simp [hz, hzn, stage7Part2Program, stage7Part2Model, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, capacity]

def stage7Part3Program : List Instr :=
  [.op (.Dup dA15),
   .op .MULMOD,
   .op .ADD,
   .op (.Dup dA14),
   .op (.Dup dA5),
   .op (.Dup dA14),
   .op .MULMOD,
   .op .ADD]
def stage7Part3Model (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 : W) (rest : List W) : State :=
  let v0 : W := UInt256.mulMod (w15) (w0) (w1)
  let v1 : W := (v0) + (w2)
  let v2 : W := UInt256.mulMod (w14) (w6) (w16)
  let v3 : W := (v2) + (v1)
  {s with pc := N 4557, stack := (v3) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: (w15) :: (w16) :: (w17) :: (w18) :: rest}
theorem stage7Part3_run (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions stage7Part3Program {s with pc := N 4549, stack := (w0) :: (w1) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: (w15) :: (w16) :: (w17) :: (w18) :: rest} =
      some (stage7Part3Model s w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 63) : rest.length + j < 1024 := by omega
  simp [hz, hzn, stage7Part3Program, stage7Part3Model, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, capacity]

def stage7Part4Program : List Instr :=
  [.push 2 2048,
   .op (.Dup dA15),
   .op (.Dup dA9),
   .op (.Dup dA1),
   .op (.Swap sA3),
   .op .SUB,
   .op .ADD,
   .op .MULMOD]
def stage7Part4Model (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 : W) (rest : List W) : State :=
  let v0 : W := (w0) - (w7)
  let v1 : W := (v0) + (w14)
  let v2 : W := UInt256.mulMod (v1) (N 2048) (w14)
  {s with pc := N 4567, stack := (v2) :: (w1) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: (w15) :: (w16) :: rest}
theorem stage7Part4_run (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions stage7Part4Program {s with pc := N 4557, stack := (w0) :: (w1) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: (w15) :: (w16) :: rest} =
      some (stage7Part4Model s w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 63) : rest.length + j < 1024 := by omega
  simp [hz, hzn, stage7Part4Program, stage7Part4Model, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, capacity]

def stage7Program : List Instr := (stage7Part0Program ++ (stage7Part1Program ++ (stage7Part2Program ++ (stage7Part3Program ++ (stage7Part4Program)))))
def stage7Model (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 : W) (rest : List W) : State :=
  let v0 : W := (w8) * (w9)
  let v1 : W := (v0) + (w0)
  let v2 : W := (w1) * (w13)
  let v3 : W := (v2) + (v1)
  let v4 : W := (w4) * (w12)
  let v5 : W := (v4) + (v3)
  let v6 : W := UInt256.land (N 1766847064778384329583297500742918515827483896875618958121606201292619775) (v5)
  let v7 : W := UInt256.mulMod (w9) (w8) (w14)
  let v8 : W := (v7) + (w0)
  let v9 : W := UInt256.mulMod (w13) (w1) (w14)
  let v10 : W := (v9) + (v8)
  let v11 : W := UInt256.mulMod (w12) (w4) (w14)
  let v12 : W := (v11) + (v10)
  let v13 : W := (v12) - (v6)
  let v14 : W := (v13) + (w14)
  let v15 : W := UInt256.mulMod (v14) (N 2048) (w14)
  {s with pc := N 4567, stack := (v15) :: (w1) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (v6) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: (w15) :: (w16) :: rest}
theorem stage7_run (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions stage7Program {s with pc := N 4495, stack := (w0) :: (w1) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: (w15) :: (w16) :: rest} = some (stage7Model s w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 rest) := by
  let v0 : W := (w8) * (w9)
  let v1 : W := (v0) + (w0)
  let v2 : W := (w1) * (w13)
  let v3 : W := (v2) + (v1)
  let v4 : W := (w4) * (w12)
  let v5 : W := (v4) + (v3)
  let v6 : W := UInt256.land (N 1766847064778384329583297500742918515827483896875618958121606201292619775) (v5)
  let v7 : W := UInt256.mulMod (w9) (w8) (w14)
  let v8 : W := (v7) + (w0)
  let v9 : W := UInt256.mulMod (w13) (w1) (w14)
  let v10 : W := (v9) + (v8)
  let v11 : W := UInt256.mulMod (w12) (w4) (w14)
  let v12 : W := (v11) + (v10)
  let v13 : W := (v12) - (v6)
  let v14 : W := (v13) + (w14)
  let v15 : W := UInt256.mulMod (v14) (N 2048) (w14)
  have h0 : runInstructions stage7Part0Program {s with pc := N 4495, stack := (w0) :: (w1) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: (w15) :: (w16) :: rest} = some {s with pc := N 4503, stack := (v2) :: (v1) :: (w0) :: (w1) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: (w15) :: (w16) :: rest} := by
    simpa only [stage7Part0Model, v0, v1, v2] using stage7Part0_run s (w0) (w1) (w2) (w3) (w4) (w5) (w6) (w7) (w8) (w9) (w10) (w11) (w12) (w13) (w14) (w15) (w16) rest hcap hact
  have h1 : runInstructions stage7Part1Program {s with pc := N 4503, stack := (v2) :: (v1) :: (w0) :: (w1) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: (w15) :: (w16) :: rest} = some {s with pc := N 4541, stack := (w7) :: (w0) :: (w1) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (v6) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: (w15) :: (w16) :: rest} := by
    simpa only [stage7Part1Model, v3, v4, v5, v6] using stage7Part1_run s (v2) (v1) (w0) (w1) (w2) (w3) (w4) (w5) (w6) (w7) (w8) (w9) (w10) (w11) (w12) (w13) (w14) (w15) (w16) rest hcap hact
  have h2 : runInstructions stage7Part2Program {s with pc := N 4541, stack := (w7) :: (w0) :: (w1) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (v6) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: (w15) :: (w16) :: rest} = some {s with pc := N 4549, stack := (w1) :: (w14) :: (v8) :: (w1) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (v6) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: (w15) :: (w16) :: rest} := by
    simpa only [stage7Part2Model, v7, v8] using stage7Part2_run s (w7) (w0) (w1) (w2) (w3) (w4) (w5) (w6) (v6) (w8) (w9) (w10) (w11) (w12) (w13) (w14) (w15) (w16) rest hcap hact
  have h3 : runInstructions stage7Part3Program {s with pc := N 4549, stack := (w1) :: (w14) :: (v8) :: (w1) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (v6) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: (w15) :: (w16) :: rest} = some {s with pc := N 4557, stack := (v12) :: (w1) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (v6) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: (w15) :: (w16) :: rest} := by
    simpa only [stage7Part3Model, v9, v10, v11, v12] using stage7Part3_run s (w1) (w14) (v8) (w1) (w2) (w3) (w4) (w5) (w6) (v6) (w8) (w9) (w10) (w11) (w12) (w13) (w14) (w15) (w16) rest hcap hact
  have h4 : runInstructions stage7Part4Program {s with pc := N 4557, stack := (v12) :: (w1) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (v6) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: (w15) :: (w16) :: rest} = some {s with pc := N 4567, stack := (v15) :: (w1) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (v6) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: (w15) :: (w16) :: rest} := by
    simpa only [stage7Part4Model, v13, v14, v15] using stage7Part4_run s (v12) (w1) (w2) (w3) (w4) (w5) (w6) (v6) (w8) (w9) (w10) (w11) (w12) (w13) (w14) (w15) (w16) rest hcap hact
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
def stage8Part0Model (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 : W) (rest : List W) : State :=
  let v0 : W := (w9) * (w9)
  let v1 : W := (v0) + (w0)
  let v2 : W := (w13) * (w4)
  {s with pc := N 4575, stack := (v2) :: (v1) :: (w0) :: (w1) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: (w15) :: (w16) :: rest}
theorem stage8Part0_run (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions stage8Part0Program {s with pc := N 4567, stack := (w0) :: (w1) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: (w15) :: (w16) :: rest} =
      some (stage8Part0Model s w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 63) : rest.length + j < 1024 := by omega
  simp [hz, hzn, stage8Part0Program, stage8Part0Model, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, capacity]

def stage8Part1Program : List Instr :=
  [.op .ADD,
   .push 30 1766847064778384329583297500742918515827483896875618958121606201292619775,
   .op .AND,
   .op (.Swap sA8),
   .op .POP,
   .op (.Dup dA14),
   .op (.Dup dA10),
   .op (.Dup dA0)]
def stage8Part1Model (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 : W) (rest : List W) : State :=
  let v0 : W := (w0) + (w1)
  let v1 : W := UInt256.land (N 1766847064778384329583297500742918515827483896875618958121606201292619775) (v0)
  {s with pc := N 4613, stack := (w11) :: (w11) :: (w16) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (v1) :: (w11) :: (w12) :: (w13) :: (w14) :: (w15) :: (w16) :: (w17) :: (w18) :: rest}
theorem stage8Part1_run (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions stage8Part1Program {s with pc := N 4575, stack := (w0) :: (w1) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: (w15) :: (w16) :: (w17) :: (w18) :: rest} =
      some (stage8Part1Model s w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 63) : rest.length + j < 1024 := by omega
  simp [hz, hzn, stage8Part1Program, stage8Part1Model, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, capacity]

def stage8Part2Program : List Instr :=
  [.op .MULMOD,
   .op .ADD,
   .op (.Dup dA14),
   .op (.Dup dA5),
   .op (.Dup dA15),
   .op .MULMOD,
   .op .ADD,
   .push 2 2048]
def stage8Part2Model (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 : W) (rest : List W) : State :=
  let v0 : W := UInt256.mulMod (w0) (w1) (w2)
  let v1 : W := (v0) + (w3)
  let v2 : W := UInt256.mulMod (w16) (w7) (w17)
  let v3 : W := (v2) + (v1)
  {s with pc := N 4623, stack := (N 2048) :: (v3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: (w15) :: (w16) :: (w17) :: (w18) :: (w19) :: rest}
theorem stage8Part2_run (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions stage8Part2Program {s with pc := N 4613, stack := (w0) :: (w1) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: (w15) :: (w16) :: (w17) :: (w18) :: (w19) :: rest} =
      some (stage8Part2Model s w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 63) : rest.length + j < 1024 := by omega
  simp [hz, hzn, stage8Part2Program, stage8Part2Model, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, capacity]

def stage8Part3Program : List Instr :=
  [.op (.Dup dA15),
   .op (.Dup dA10),
   .op (.Dup dA1),
   .op (.Swap sA3),
   .op .SUB,
   .op .ADD,
   .op .MULMOD]
def stage8Part3Model (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 : W) (rest : List W) : State :=
  let v0 : W := (w1) - (w9)
  let v1 : W := (v0) + (w15)
  let v2 : W := UInt256.mulMod (v1) (w0) (w15)
  {s with pc := N 4630, stack := (v2) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: (w15) :: (w16) :: (w17) :: rest}
theorem stage8Part3_run (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions stage8Part3Program {s with pc := N 4623, stack := (w0) :: (w1) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: (w15) :: (w16) :: (w17) :: rest} =
      some (stage8Part3Model s w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 63) : rest.length + j < 1024 := by omega
  simp [hz, hzn, stage8Part3Program, stage8Part3Model, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, capacity]

def stage8Program : List Instr := (stage8Part0Program ++ (stage8Part1Program ++ (stage8Part2Program ++ (stage8Part3Program))))
def stage8Model (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 : W) (rest : List W) : State :=
  let v0 : W := (w9) * (w9)
  let v1 : W := (v0) + (w0)
  let v2 : W := (w13) * (w4)
  let v3 : W := (v2) + (v1)
  let v4 : W := UInt256.land (N 1766847064778384329583297500742918515827483896875618958121606201292619775) (v3)
  let v5 : W := UInt256.mulMod (w9) (w9) (w14)
  let v6 : W := (v5) + (w0)
  let v7 : W := UInt256.mulMod (w13) (w4) (w14)
  let v8 : W := (v7) + (v6)
  let v9 : W := (v8) - (v4)
  let v10 : W := (v9) + (w14)
  let v11 : W := UInt256.mulMod (v10) (N 2048) (w14)
  {s with pc := N 4630, stack := (v11) :: (w1) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (v4) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: (w15) :: (w16) :: rest}
theorem stage8_run (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions stage8Program {s with pc := N 4567, stack := (w0) :: (w1) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: (w15) :: (w16) :: rest} = some (stage8Model s w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 rest) := by
  let v0 : W := (w9) * (w9)
  let v1 : W := (v0) + (w0)
  let v2 : W := (w13) * (w4)
  let v3 : W := (v2) + (v1)
  let v4 : W := UInt256.land (N 1766847064778384329583297500742918515827483896875618958121606201292619775) (v3)
  let v5 : W := UInt256.mulMod (w9) (w9) (w14)
  let v6 : W := (v5) + (w0)
  let v7 : W := UInt256.mulMod (w13) (w4) (w14)
  let v8 : W := (v7) + (v6)
  let v9 : W := (v8) - (v4)
  let v10 : W := (v9) + (w14)
  let v11 : W := UInt256.mulMod (v10) (N 2048) (w14)
  have h0 : runInstructions stage8Part0Program {s with pc := N 4567, stack := (w0) :: (w1) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: (w15) :: (w16) :: rest} = some {s with pc := N 4575, stack := (v2) :: (v1) :: (w0) :: (w1) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: (w15) :: (w16) :: rest} := by
    simpa only [stage8Part0Model, v0, v1, v2] using stage8Part0_run s (w0) (w1) (w2) (w3) (w4) (w5) (w6) (w7) (w8) (w9) (w10) (w11) (w12) (w13) (w14) (w15) (w16) rest hcap hact
  have h1 : runInstructions stage8Part1Program {s with pc := N 4575, stack := (v2) :: (v1) :: (w0) :: (w1) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: (w15) :: (w16) :: rest} = some {s with pc := N 4613, stack := (w9) :: (w9) :: (w14) :: (w0) :: (w1) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (v4) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: (w15) :: (w16) :: rest} := by
    simpa only [stage8Part1Model, v3, v4] using stage8Part1_run s (v2) (v1) (w0) (w1) (w2) (w3) (w4) (w5) (w6) (w7) (w8) (w9) (w10) (w11) (w12) (w13) (w14) (w15) (w16) rest hcap hact
  have h2 : runInstructions stage8Part2Program {s with pc := N 4613, stack := (w9) :: (w9) :: (w14) :: (w0) :: (w1) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (v4) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: (w15) :: (w16) :: rest} = some {s with pc := N 4623, stack := (N 2048) :: (v8) :: (w1) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (v4) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: (w15) :: (w16) :: rest} := by
    simpa only [stage8Part2Model, v5, v6, v7, v8] using stage8Part2_run s (w9) (w9) (w14) (w0) (w1) (w2) (w3) (w4) (w5) (w6) (w7) (v4) (w9) (w10) (w11) (w12) (w13) (w14) (w15) (w16) rest hcap hact
  have h3 : runInstructions stage8Part3Program {s with pc := N 4623, stack := (N 2048) :: (v8) :: (w1) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (v4) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: (w15) :: (w16) :: rest} = some {s with pc := N 4630, stack := (v11) :: (w1) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (v4) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: (w15) :: (w16) :: rest} := by
    simpa only [stage8Part3Model, v9, v10, v11] using stage8Part3_run s (N 2048) (v8) (w1) (w2) (w3) (w4) (w5) (w6) (w7) (v4) (w9) (w10) (w11) (w12) (w13) (w14) (w15) (w16) rest hcap hact
  exact (runInstructions_append_some _ _ _ _ _ h0 (runInstructions_append_some _ _ _ _ _ h1 (runInstructions_append_some _ _ _ _ _ h2 h3)))

def stage9Part0Program : List Instr :=
  [.op (.Swap sA8),
   .op .POP,
   .op .POP,
   .op .POP,
   .op .POP,
   .op .POP,
   .push 1 1,
   .op (.Dup dA12)]
def stage9Part0Model (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 : W) (rest : List W) : State :=
  {s with pc := N 4639, stack := (w16) :: (N 1) :: (w5) :: (w6) :: (w7) :: (w8) :: (w0) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: (w15) :: (w16) :: rest}
theorem stage9Part0_run (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions stage9Part0Program {s with pc := N 4630, stack := (w0) :: (w1) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: (w15) :: (w16) :: rest} =
      some (stage9Part0Model s w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 63) : rest.length + j < 1024 := by omega
  simp [hz, hzn, stage9Part0Program, stage9Part0Model, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, capacity]

def stage9Part1Program : List Instr :=
  [.op .SUB,
   .op (.Swap sA11)]
def stage9Part1Model (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 : W) (rest : List W) : State :=
  let v0 : W := (w0) - (w1)
  {s with pc := N 4641, stack := (w13) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (v0) :: rest}
theorem stage9Part1_run (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions stage9Part1Program {s with pc := N 4639, stack := (w0) :: (w1) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: rest} =
      some (stage9Part1Model s w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 63) : rest.length + j < 1024 := by omega
  simp [hz, hzn, stage9Part1Program, stage9Part1Model, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, capacity]

def stage9Program : List Instr := (stage9Part0Program ++ (stage9Part1Program))
def stage9Model (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 : W) (rest : List W) : State :=
  let v0 : W := (w16) - (N 1)
  {s with pc := N 4641, stack := (w16) :: (w5) :: (w6) :: (w7) :: (w8) :: (w0) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: (w15) :: (v0) :: rest}
theorem stage9_run (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions stage9Program {s with pc := N 4630, stack := (w0) :: (w1) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: (w15) :: (w16) :: rest} = some (stage9Model s w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 rest) := by
  let v0 : W := (w16) - (N 1)
  have h0 : runInstructions stage9Part0Program {s with pc := N 4630, stack := (w0) :: (w1) :: (w2) :: (w3) :: (w4) :: (w5) :: (w6) :: (w7) :: (w8) :: (w9) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: (w15) :: (w16) :: rest} = some {s with pc := N 4639, stack := (w16) :: (N 1) :: (w5) :: (w6) :: (w7) :: (w8) :: (w0) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: (w15) :: (w16) :: rest} := by
    simpa only [stage9Part0Model] using stage9Part0_run s (w0) (w1) (w2) (w3) (w4) (w5) (w6) (w7) (w8) (w9) (w10) (w11) (w12) (w13) (w14) (w15) (w16) rest hcap hact
  have h1 : runInstructions stage9Part1Program {s with pc := N 4639, stack := (w16) :: (N 1) :: (w5) :: (w6) :: (w7) :: (w8) :: (w0) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: (w15) :: (w16) :: rest} = some {s with pc := N 4641, stack := (w16) :: (w5) :: (w6) :: (w7) :: (w8) :: (w0) :: (w10) :: (w11) :: (w12) :: (w13) :: (w14) :: (w15) :: (v0) :: rest} := by
    simpa only [stage9Part1Model, v0] using stage9Part1_run s (w16) (N 1) (w5) (w6) (w7) (w8) (w0) (w10) (w11) (w12) (w13) (w14) (w15) (w16) rest hcap hact
  exact (runInstructions_append_some _ _ _ _ _ h0 h1)

end NextR5Columns
set_option warningAsError true
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 1000000
namespace R5SharedTools
open EvmSemantics Challenge.EvmProof.Word CycleSubmission.DoubleInput

theorem add_toNat_le (a b : UInt256) : (a+b).toNat ≤ a.toNat+b.toNat := by
  rw [word_toNat_add]
  exact Nat.mod_le _ _

theorem residue_lt (a b p : UInt256) (hp : 0 < p.toNat) :
    (UInt256.mulMod a b p).toNat < p.toNat := by
  rw [mulMod_nat _ _ _ hp]
  exact Nat.mod_lt _ hp

/-- A generic extra-residue sum replaces a fixed number of column terms. -/
theorem high_double_biased_extra (a b p h digit factor : UInt256)
    (hp : 0 < p.toNat) (ha : a.toNat+a.toNat < 2^256)
    (hd : digit.toNat < p.toNat)
    (hroom : 3*p.toNat+h.toNat ≤ 2^256) :
    UInt256.mulMod factor
      (p + ((UInt256.mulMod b (a+a) p + h)-digit)) p =
      UInt256.mulMod factor
        (p + (((UInt256.mulMod b a p+UInt256.mulMod b a p)+h)-digit)) p := by
  have hm := residue_lt b a p hp
  have hn := residue_lt b (a+a) p hp
  have hb0 := add_toNat_le (UInt256.mulMod b a p) (UInt256.mulMod b a p)
  have hb1 := add_toNat_le (UInt256.mulMod b a p+UInt256.mulMod b a p) h
  have hb2 := add_toNat_le (UInt256.mulMod b (a+a) p) h
  have hnew : (UInt256.mulMod b (a+a) p+h).toNat+p.toNat < 2^256 := by omega
  have hold : (UInt256.mulMod b a p+UInt256.mulMod b a p+h).toNat+p.toNat < 2^256 := by omega
  have he := congrArg UInt256.toNat
    (high_double a b p h (UInt256.ofNat 1) hp ha (by omega))
  have hone : (UInt256.ofNat 1).toNat = 1 := by norm_num [word_toNat_ofNat]
  simp only [mulMod_nat _ _ _ hp, hone, Nat.one_mul] at he
  exact biased_congruent _ _ digit p factor hp hd hnew hold he

theorem sum_toNat_le (xs : List UInt256) :
    (xs.foldr (fun a b => a+b) (UInt256.ofNat 0)).toNat ≤
      (xs.map UInt256.toNat).sum := by
  induction xs with
  | nil => exact Nat.le_refl 0
  | cons a xs ih =>
      simp only [List.foldr_cons, List.map_cons, List.sum_cons]
      exact (add_toNat_le _ _).trans (Nat.add_le_add_left ih _)

theorem sum_map_le (xs : List UInt256) (p : Nat) :
    (∀ x ∈ xs, x.toNat ≤ p) → (xs.map UInt256.toNat).sum ≤ xs.length*p := by
  induction xs with
  | nil => intro _; simp
  | cons a xs ih =>
      intro hall
      have ha := hall a (by simp)
      have ht := ih (fun x hx => hall x (by simp [hx]))
      simp only [List.map_cons, List.sum_cons, List.length_cons]
      calc
        _ ≤ p + xs.length*p := Nat.add_le_add ha ht
        _ = _ := by rw [Nat.add_mul, Nat.one_mul]; omega

theorem high_double_list_radix240 (a b factor : UInt256) (xs : List UInt256)
    (ha : a.toNat < 2^240) (hlen : xs.length ≤ 29)
    (hxs : ∀ x ∈ xs, x.toNat ≤ CycleSubmission.WordArithmetic.P.toNat) :
    let p := CycleSubmission.WordArithmetic.P
    let h := xs.foldr (fun x y => x+y) (UInt256.ofNat 0)
    UInt256.mulMod factor (UInt256.mulMod b (a+a) p+h) p =
      UInt256.mulMod factor ((UInt256.mulMod b a p+UInt256.mulMod b a p)+h) p := by
  dsimp only
  have hp : 0 < CycleSubmission.WordArithmetic.P.toNat := by
    rw [CycleSubmission.WordArithmetic.pValue]
    norm_num [HistoricalSearch.CRTColumn.residueModulus]
  have h32 : 32*CycleSubmission.WordArithmetic.P.toNat ≤ 2^256 := by
    rw [CycleSubmission.WordArithmetic.pValue]
    norm_num [HistoricalSearch.CRTColumn.residueModulus]
  have hs := (sum_toNat_le xs).trans (sum_map_le xs _ hxs)
  have hm := Nat.mul_le_mul_right CycleSubmission.WordArithmetic.P.toNat hlen
  exact high_double a b CycleSubmission.WordArithmetic.P _ factor hp
    (by omega) (by omega)

theorem word_add0 (a : UInt256) : a+UInt256.ofNat 0 = a := by
  apply word_ext
  change (a.val+0).val = a.val.val
  rw [add_zero]

theorem mask240_literal : UInt256.ofNat (2^240-1) =
    UInt256.ofNat 1766847064778384329583297500742918515827483896875618958121606201292619775 := by
  have h : (2:Nat)^240-1 = 1766847064778384329583297500742918515827483896875618958121606201292619775 := by norm_num
  rw [h]

theorem mask240_lt_p (w : UInt256) :
    (UInt256.land (UInt256.ofNat (2^240-1)) w).toNat < CycleSubmission.WordArithmetic.P.toNat := by
  rw [HistoricalSearch.WordCancellation.land_comm]
  change (w &&& UInt256.ofNat (2^240-1)).toNat < _
  rw [HistoricalSearch.WordCancellation.mask_toNat _ 240 (by decide)]
  exact (Nat.mod_lt _ (Nat.two_pow_pos 240)).trans (by
    rw [CycleSubmission.WordArithmetic.pValue]
    norm_num [HistoricalSearch.CRTColumn.residueModulus])

theorem high_double_biased_list_radix240 (a b factor digit : UInt256) (xs : List UInt256)
    (ha : a.toNat < 2^240) (hlen : xs.length ≤ 28)
    (hxs : ∀ x ∈ xs, x.toNat ≤ CycleSubmission.WordArithmetic.P.toNat)
    (hd : digit.toNat < CycleSubmission.WordArithmetic.P.toNat) :
    let p := CycleSubmission.WordArithmetic.P
    let h := xs.foldr (fun x y => x+y) (UInt256.ofNat 0)
    UInt256.mulMod factor (p+((UInt256.mulMod b (a+a) p+h)-digit)) p =
      UInt256.mulMod factor (p+(((UInt256.mulMod b a p+UInt256.mulMod b a p)+h)-digit)) p := by
  dsimp only
  have hp : 0 < CycleSubmission.WordArithmetic.P.toNat := by
    rw [CycleSubmission.WordArithmetic.pValue]
    norm_num [HistoricalSearch.CRTColumn.residueModulus]
  have h32 : 32*CycleSubmission.WordArithmetic.P.toNat ≤ 2^256 := by
    rw [CycleSubmission.WordArithmetic.pValue]
    norm_num [HistoricalSearch.CRTColumn.residueModulus]
  have hs := (sum_toNat_le xs).trans (sum_map_le xs _ hxs)
  have hm := Nat.mul_le_mul_right CycleSubmission.WordArithmetic.P.toNat hlen
  exact high_double_biased_extra a b CycleSubmission.WordArithmetic.P _ digit factor hp
    (by omega) hd (by omega)

end R5SharedTools

set_option maxRecDepth 40000
set_option maxHeartbeats 8000000

namespace R5SharedMath1
open EvmSemantics Challenge.EvmProof.Word CycleSubmission.Prepared.Arithmetic R5SharedTools
local notation "W" => UInt256
local notation "N" => UInt256.ofNat
def loOld (c q0 a0 a1 n0 n1 p inv : W) : W := ([((q0)*(n1)), ((a0)*(a1)), ((a0)*(a1)), c].foldr (fun x y => x+y) (N 0))
def loNew (c q0 a0 a1 n0 n1 p inv : W) : W := ([((q0)*(n1)), ((a0+a0)*(a1)), c].foldr (fun x y => x+y) (N 0))
def hiOld (c q0 a0 a1 n0 n1 p inv : W) : W := ([(UInt256.mulMod (q0) (n1) p), (UInt256.mulMod (a0) (a1) p), (UInt256.mulMod (a0) (a1) p), c].foldr (fun x y => x+y) (N 0))
def hiNew (c q0 a0 a1 n0 n1 p inv : W) : W := ([(UInt256.mulMod (q0) (n1) p), (UInt256.mulMod (a0+a0) (a1) p), c].foldr (fun x y => x+y) (N 0))
def qOld (c q0 a0 a1 n0 n1 p inv : W) : W := UInt256.shiftRight (inv*(loOld c q0 a0 a1 n0 n1 p inv)) (N 16)
def qNew (c q0 a0 a1 n0 n1 p inv : W) : W := UInt256.shiftRight (inv*(loNew c q0 a0 a1 n0 n1 p inv)) (N 16)
def cOld (c q0 a0 a1 n0 n1 p inv : W) : W := UInt256.mulMod (N 2048) ((UInt256.mulMod (qOld c q0 a0 a1 n0 n1 p inv) (n0) p)+(hiOld c q0 a0 a1 n0 n1 p inv)) p
def cNew (c q0 a0 a1 n0 n1 p inv : W) : W := UInt256.mulMod (N 2048) ((UInt256.mulMod (qNew c q0 a0 a1 n0 n1 p inv) (n0) p)+(hiNew c q0 a0 a1 n0 n1 p inv)) p
theorem q_same (c q0 a0 a1 n0 n1 p inv : W) : qNew c q0 a0 a1 n0 n1 p inv = qOld c q0 a0 a1 n0 n1 p inv := by
  have h0 : (a0+a0)*a1 = a0*a1+a0*a1 := by simpa only [mulC] using CycleSubmission.DoubleInput.low_double a0 a1
  simp only [qNew, qOld, loNew, loOld, List.foldr_cons, List.foldr_nil, word_add0, h0, addA, addL, addC]
theorem c_same (c q0 a0 a1 n0 n1 p inv : W)
    (ha0 : a0.toNat < 2^240)
    (hp : p = CycleSubmission.WordArithmetic.P) (hc : c.toNat < p.toNat) :
    cNew c q0 a0 a1 n0 n1 p inv = cOld c q0 a0 a1 n0 n1 p inv := by
  subst p
  let p := CycleSubmission.WordArithmetic.P
  have hp0 : 0 < p.toNat := by
    dsimp only [p]
    rw [CycleSubmission.WordArithmetic.pValue]
    norm_num [HistoricalSearch.CRTColumn.residueModulus]
  let red : List W → W := fun xs => UInt256.mulMod (N 2048) (xs.foldr (fun x y => x+y) (N 0)) p
  let ys0 : List W := [(UInt256.mulMod (qOld c q0 a0 a1 n0 n1 p inv) (n0) p), (UInt256.mulMod (q0) (n1) p), c]
  have hb0 : ∀ x ∈ ys0, x.toNat ≤ p.toNat := by
    intro x hx
    simp [ys0] at hx
    rcases hx with rfl | rfl | rfl
    all_goals first
      | exact Nat.le_of_lt hc
      | exact Nat.le_of_lt (residue_lt _ _ _ hp0)
  have hh0 := high_double_list_radix240 a0 a1 (N 2048) ys0 ha0 (by simp [ys0]) hb0
  have step0 : red [(UInt256.mulMod (qOld c q0 a0 a1 n0 n1 p inv) (n0) p), (UInt256.mulMod (q0) (n1) p), (UInt256.mulMod (a0+a0) (a1) p), c] = red [(UInt256.mulMod (qOld c q0 a0 a1 n0 n1 p inv) (n0) p), (UInt256.mulMod (q0) (n1) p), (UInt256.mulMod (a0) (a1) p), (UInt256.mulMod (a0) (a1) p), c] := by
    simpa only [red, ys0, List.foldr_cons, List.foldr_nil, word_add0, addA, addL, addC, mmC] using hh0
  simpa only [cNew, cOld, hiNew, hiOld, q_same, red, List.foldr_cons, List.foldr_nil] using step0
theorem old_q_matches (c q0 q1 q2 q3 q4 a0 a1 a2 a3 a4 n0 n1 n2 n3 n4 p inv cnt z0 z1 z2 z3 : W) : qOld c q0 a0 a1 n0 n1 p inv = CycleSubmission.R5.ExecSquare.sqCol1_o1 c q0 a0 a1 a2 a3 a4 n1 n2 n3 n4 p inv cnt n0 := by
  simp only [qOld, loOld, CycleSubmission.R5.ExecSquare.sqCol1_o1, List.foldr_cons, List.foldr_nil, word_add0, mask240_literal, addA, addL, addC, mulC]
theorem old_c_matches (c q0 q1 q2 q3 q4 a0 a1 a2 a3 a4 n0 n1 n2 n3 n4 p inv cnt z0 z1 z2 z3 : W) : cOld c q0 a0 a1 n0 n1 p inv = CycleSubmission.R5.ExecSquare.sqCol1_o0 c q0 a0 a1 a2 a3 a4 n1 n2 n3 n4 p inv cnt n0 := by
  simp only [cOld, hiOld, qOld, loOld, CycleSubmission.R5.ExecSquare.sqCol1_o0, List.foldr_cons, List.foldr_nil, word_add0, mask240_literal, addA, addL, addC, mulC, mmC]
end R5SharedMath1

namespace R5SharedMath2
open EvmSemantics Challenge.EvmProof.Word CycleSubmission.Prepared.Arithmetic R5SharedTools
local notation "W" => UInt256
local notation "N" => UInt256.ofNat
def loOld (c q0 q1 a0 a1 a2 n0 n1 n2 p inv : W) : W := ([((q1)*(n1)), ((q0)*(n2)), ((a1)*(a1)), ((a0)*(a2)), ((a0)*(a2)), c].foldr (fun x y => x+y) (N 0))
def loNew (c q0 q1 a0 a1 a2 n0 n1 n2 p inv : W) : W := ([((q1)*(n1)), ((q0)*(n2)), ((a1)*(a1)), ((a0+a0)*(a2)), c].foldr (fun x y => x+y) (N 0))
def hiOld (c q0 q1 a0 a1 a2 n0 n1 n2 p inv : W) : W := ([(UInt256.mulMod (q1) (n1) p), (UInt256.mulMod (q0) (n2) p), (UInt256.mulMod (a1) (a1) p), (UInt256.mulMod (a0) (a2) p), (UInt256.mulMod (a0) (a2) p), c].foldr (fun x y => x+y) (N 0))
def hiNew (c q0 q1 a0 a1 a2 n0 n1 n2 p inv : W) : W := ([(UInt256.mulMod (q1) (n1) p), (UInt256.mulMod (q0) (n2) p), (UInt256.mulMod (a1) (a1) p), (UInt256.mulMod (a0+a0) (a2) p), c].foldr (fun x y => x+y) (N 0))
def qOld (c q0 q1 a0 a1 a2 n0 n1 n2 p inv : W) : W := UInt256.shiftRight (inv*(loOld c q0 q1 a0 a1 a2 n0 n1 n2 p inv)) (N 16)
def qNew (c q0 q1 a0 a1 a2 n0 n1 n2 p inv : W) : W := UInt256.shiftRight (inv*(loNew c q0 q1 a0 a1 a2 n0 n1 n2 p inv)) (N 16)
def cOld (c q0 q1 a0 a1 a2 n0 n1 n2 p inv : W) : W := UInt256.mulMod (N 2048) ((UInt256.mulMod (qOld c q0 q1 a0 a1 a2 n0 n1 n2 p inv) (n0) p)+(hiOld c q0 q1 a0 a1 a2 n0 n1 n2 p inv)) p
def cNew (c q0 q1 a0 a1 a2 n0 n1 n2 p inv : W) : W := UInt256.mulMod (N 2048) ((UInt256.mulMod (qNew c q0 q1 a0 a1 a2 n0 n1 n2 p inv) (n0) p)+(hiNew c q0 q1 a0 a1 a2 n0 n1 n2 p inv)) p
theorem q_same (c q0 q1 a0 a1 a2 n0 n1 n2 p inv : W) : qNew c q0 q1 a0 a1 a2 n0 n1 n2 p inv = qOld c q0 q1 a0 a1 a2 n0 n1 n2 p inv := by
  have h0 : (a0+a0)*a2 = a0*a2+a0*a2 := by simpa only [mulC] using CycleSubmission.DoubleInput.low_double a0 a2
  simp only [qNew, qOld, loNew, loOld, List.foldr_cons, List.foldr_nil, word_add0, h0, addA, addL, addC]
theorem c_same (c q0 q1 a0 a1 a2 n0 n1 n2 p inv : W)
    (ha0 : a0.toNat < 2^240)
    (hp : p = CycleSubmission.WordArithmetic.P) (hc : c.toNat < p.toNat) :
    cNew c q0 q1 a0 a1 a2 n0 n1 n2 p inv = cOld c q0 q1 a0 a1 a2 n0 n1 n2 p inv := by
  subst p
  let p := CycleSubmission.WordArithmetic.P
  have hp0 : 0 < p.toNat := by
    dsimp only [p]
    rw [CycleSubmission.WordArithmetic.pValue]
    norm_num [HistoricalSearch.CRTColumn.residueModulus]
  let red : List W → W := fun xs => UInt256.mulMod (N 2048) (xs.foldr (fun x y => x+y) (N 0)) p
  let ys0 : List W := [(UInt256.mulMod (qOld c q0 q1 a0 a1 a2 n0 n1 n2 p inv) (n0) p), (UInt256.mulMod (q1) (n1) p), (UInt256.mulMod (q0) (n2) p), (UInt256.mulMod (a1) (a1) p), c]
  have hb0 : ∀ x ∈ ys0, x.toNat ≤ p.toNat := by
    intro x hx
    simp [ys0] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl
    all_goals first
      | exact Nat.le_of_lt hc
      | exact Nat.le_of_lt (residue_lt _ _ _ hp0)
  have hh0 := high_double_list_radix240 a0 a2 (N 2048) ys0 ha0 (by simp [ys0]) hb0
  have step0 : red [(UInt256.mulMod (qOld c q0 q1 a0 a1 a2 n0 n1 n2 p inv) (n0) p), (UInt256.mulMod (q1) (n1) p), (UInt256.mulMod (q0) (n2) p), (UInt256.mulMod (a1) (a1) p), (UInt256.mulMod (a0+a0) (a2) p), c] = red [(UInt256.mulMod (qOld c q0 q1 a0 a1 a2 n0 n1 n2 p inv) (n0) p), (UInt256.mulMod (q1) (n1) p), (UInt256.mulMod (q0) (n2) p), (UInt256.mulMod (a1) (a1) p), (UInt256.mulMod (a0) (a2) p), (UInt256.mulMod (a0) (a2) p), c] := by
    simpa only [red, ys0, List.foldr_cons, List.foldr_nil, word_add0, addA, addL, addC, mmC] using hh0
  simpa only [cNew, cOld, hiNew, hiOld, q_same, red, List.foldr_cons, List.foldr_nil] using step0
theorem old_q_matches (c q0 q1 q2 q3 q4 a0 a1 a2 a3 a4 n0 n1 n2 n3 n4 p inv cnt z0 z1 z2 z3 : W) : qOld c q0 q1 a0 a1 a2 n0 n1 n2 p inv = CycleSubmission.R5.ExecSquare.sqCol2_o1 c q1 q0 a0 a1 a2 a3 a4 n1 n2 n3 n4 p inv cnt n0 := by
  simp only [qOld, loOld, CycleSubmission.R5.ExecSquare.sqCol2_o1, List.foldr_cons, List.foldr_nil, word_add0, mask240_literal, addA, addL, addC, mulC]
theorem old_c_matches (c q0 q1 q2 q3 q4 a0 a1 a2 a3 a4 n0 n1 n2 n3 n4 p inv cnt z0 z1 z2 z3 : W) : cOld c q0 q1 a0 a1 a2 n0 n1 n2 p inv = CycleSubmission.R5.ExecSquare.sqCol2_o0 c q1 q0 a0 a1 a2 a3 a4 n1 n2 n3 n4 p inv cnt n0 := by
  simp only [cOld, hiOld, qOld, loOld, CycleSubmission.R5.ExecSquare.sqCol2_o0, List.foldr_cons, List.foldr_nil, word_add0, mask240_literal, addA, addL, addC, mulC, mmC]
end R5SharedMath2

namespace R5SharedMath3
open EvmSemantics Challenge.EvmProof.Word CycleSubmission.Prepared.Arithmetic R5SharedTools
local notation "W" => UInt256
local notation "N" => UInt256.ofNat
def loOld (c q0 q1 q2 a0 a1 a2 a3 n0 n1 n2 n3 p inv : W) : W := ([((q2)*(n1)), ((q1)*(n2)), ((q0)*(n3)), ((a0)*(a3)), ((a0)*(a3)), ((a1)*(a2)), ((a1)*(a2)), c].foldr (fun x y => x+y) (N 0))
def loNew (c q0 q1 q2 a0 a1 a2 a3 n0 n1 n2 n3 p inv : W) : W := ([((q2)*(n1)), ((q1)*(n2)), ((q0)*(n3)), ((a0+a0)*(a3)), ((a1+a1)*(a2)), c].foldr (fun x y => x+y) (N 0))
def hiOld (c q0 q1 q2 a0 a1 a2 a3 n0 n1 n2 n3 p inv : W) : W := ([(UInt256.mulMod (q2) (n1) p), (UInt256.mulMod (q1) (n2) p), (UInt256.mulMod (q0) (n3) p), (UInt256.mulMod (a0) (a3) p), (UInt256.mulMod (a0) (a3) p), (UInt256.mulMod (a1) (a2) p), (UInt256.mulMod (a1) (a2) p), c].foldr (fun x y => x+y) (N 0))
def hiNew (c q0 q1 q2 a0 a1 a2 a3 n0 n1 n2 n3 p inv : W) : W := ([(UInt256.mulMod (q2) (n1) p), (UInt256.mulMod (q1) (n2) p), (UInt256.mulMod (q0) (n3) p), (UInt256.mulMod (a0+a0) (a3) p), (UInt256.mulMod (a1+a1) (a2) p), c].foldr (fun x y => x+y) (N 0))
def qOld (c q0 q1 q2 a0 a1 a2 a3 n0 n1 n2 n3 p inv : W) : W := UInt256.shiftRight (inv*(loOld c q0 q1 q2 a0 a1 a2 a3 n0 n1 n2 n3 p inv)) (N 16)
def qNew (c q0 q1 q2 a0 a1 a2 a3 n0 n1 n2 n3 p inv : W) : W := UInt256.shiftRight (inv*(loNew c q0 q1 q2 a0 a1 a2 a3 n0 n1 n2 n3 p inv)) (N 16)
def cOld (c q0 q1 q2 a0 a1 a2 a3 n0 n1 n2 n3 p inv : W) : W := UInt256.mulMod (N 2048) ((UInt256.mulMod (qOld c q0 q1 q2 a0 a1 a2 a3 n0 n1 n2 n3 p inv) (n0) p)+(hiOld c q0 q1 q2 a0 a1 a2 a3 n0 n1 n2 n3 p inv)) p
def cNew (c q0 q1 q2 a0 a1 a2 a3 n0 n1 n2 n3 p inv : W) : W := UInt256.mulMod (N 2048) ((UInt256.mulMod (qNew c q0 q1 q2 a0 a1 a2 a3 n0 n1 n2 n3 p inv) (n0) p)+(hiNew c q0 q1 q2 a0 a1 a2 a3 n0 n1 n2 n3 p inv)) p
theorem q_same (c q0 q1 q2 a0 a1 a2 a3 n0 n1 n2 n3 p inv : W) : qNew c q0 q1 q2 a0 a1 a2 a3 n0 n1 n2 n3 p inv = qOld c q0 q1 q2 a0 a1 a2 a3 n0 n1 n2 n3 p inv := by
  have h0 : (a0+a0)*a3 = a0*a3+a0*a3 := by simpa only [mulC] using CycleSubmission.DoubleInput.low_double a0 a3
  have h1 : (a1+a1)*a2 = a1*a2+a1*a2 := by simpa only [mulC] using CycleSubmission.DoubleInput.low_double a1 a2
  simp only [qNew, qOld, loNew, loOld, List.foldr_cons, List.foldr_nil, word_add0, h0, h1, addA, addL, addC]
theorem c_same (c q0 q1 q2 a0 a1 a2 a3 n0 n1 n2 n3 p inv : W)
    (ha0 : a0.toNat < 2^240) (ha1 : a1.toNat < 2^240)
    (hp : p = CycleSubmission.WordArithmetic.P) (hc : c.toNat < p.toNat) :
    cNew c q0 q1 q2 a0 a1 a2 a3 n0 n1 n2 n3 p inv = cOld c q0 q1 q2 a0 a1 a2 a3 n0 n1 n2 n3 p inv := by
  subst p
  let p := CycleSubmission.WordArithmetic.P
  have hp0 : 0 < p.toNat := by
    dsimp only [p]
    rw [CycleSubmission.WordArithmetic.pValue]
    norm_num [HistoricalSearch.CRTColumn.residueModulus]
  let red : List W → W := fun xs => UInt256.mulMod (N 2048) (xs.foldr (fun x y => x+y) (N 0)) p
  let ys0 : List W := [(UInt256.mulMod (qOld c q0 q1 q2 a0 a1 a2 a3 n0 n1 n2 n3 p inv) (n0) p), (UInt256.mulMod (q2) (n1) p), (UInt256.mulMod (q1) (n2) p), (UInt256.mulMod (q0) (n3) p), (UInt256.mulMod (a1+a1) (a2) p), c]
  have hb0 : ∀ x ∈ ys0, x.toNat ≤ p.toNat := by
    intro x hx
    simp [ys0] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl
    all_goals first
      | exact Nat.le_of_lt hc
      | exact Nat.le_of_lt (residue_lt _ _ _ hp0)
  have hh0 := high_double_list_radix240 a0 a3 (N 2048) ys0 ha0 (by simp [ys0]) hb0
  have step0 : red [(UInt256.mulMod (qOld c q0 q1 q2 a0 a1 a2 a3 n0 n1 n2 n3 p inv) (n0) p), (UInt256.mulMod (q2) (n1) p), (UInt256.mulMod (q1) (n2) p), (UInt256.mulMod (q0) (n3) p), (UInt256.mulMod (a0+a0) (a3) p), (UInt256.mulMod (a1+a1) (a2) p), c] = red [(UInt256.mulMod (qOld c q0 q1 q2 a0 a1 a2 a3 n0 n1 n2 n3 p inv) (n0) p), (UInt256.mulMod (q2) (n1) p), (UInt256.mulMod (q1) (n2) p), (UInt256.mulMod (q0) (n3) p), (UInt256.mulMod (a0) (a3) p), (UInt256.mulMod (a0) (a3) p), (UInt256.mulMod (a1+a1) (a2) p), c] := by
    simpa only [red, ys0, List.foldr_cons, List.foldr_nil, word_add0, addA, addL, addC, mmC] using hh0
  let ys1 : List W := [(UInt256.mulMod (qOld c q0 q1 q2 a0 a1 a2 a3 n0 n1 n2 n3 p inv) (n0) p), (UInt256.mulMod (q2) (n1) p), (UInt256.mulMod (q1) (n2) p), (UInt256.mulMod (q0) (n3) p), (UInt256.mulMod (a0) (a3) p), (UInt256.mulMod (a0) (a3) p), c]
  have hb1 : ∀ x ∈ ys1, x.toNat ≤ p.toNat := by
    intro x hx
    simp [ys1] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals first
      | exact Nat.le_of_lt hc
      | exact Nat.le_of_lt (residue_lt _ _ _ hp0)
  have hh1 := high_double_list_radix240 a1 a2 (N 2048) ys1 ha1 (by simp [ys1]) hb1
  have step1 : red [(UInt256.mulMod (qOld c q0 q1 q2 a0 a1 a2 a3 n0 n1 n2 n3 p inv) (n0) p), (UInt256.mulMod (q2) (n1) p), (UInt256.mulMod (q1) (n2) p), (UInt256.mulMod (q0) (n3) p), (UInt256.mulMod (a0) (a3) p), (UInt256.mulMod (a0) (a3) p), (UInt256.mulMod (a1+a1) (a2) p), c] = red [(UInt256.mulMod (qOld c q0 q1 q2 a0 a1 a2 a3 n0 n1 n2 n3 p inv) (n0) p), (UInt256.mulMod (q2) (n1) p), (UInt256.mulMod (q1) (n2) p), (UInt256.mulMod (q0) (n3) p), (UInt256.mulMod (a0) (a3) p), (UInt256.mulMod (a0) (a3) p), (UInt256.mulMod (a1) (a2) p), (UInt256.mulMod (a1) (a2) p), c] := by
    simpa only [red, ys1, List.foldr_cons, List.foldr_nil, word_add0, addA, addL, addC, mmC] using hh1
  simpa only [cNew, cOld, hiNew, hiOld, q_same, red, List.foldr_cons, List.foldr_nil] using step0.trans step1
theorem old_q_matches (c q0 q1 q2 q3 q4 a0 a1 a2 a3 a4 n0 n1 n2 n3 n4 p inv cnt z0 z1 z2 z3 : W) : qOld c q0 q1 q2 a0 a1 a2 a3 n0 n1 n2 n3 p inv = CycleSubmission.R5.ExecSquare.sqCol3_o1 c q2 q1 q0 a0 a1 a2 a3 a4 n1 n2 n3 n4 p inv cnt n0 := by
  simp only [qOld, loOld, CycleSubmission.R5.ExecSquare.sqCol3_o1, List.foldr_cons, List.foldr_nil, word_add0, mask240_literal, addA, addL, addC, mulC]
theorem old_c_matches (c q0 q1 q2 q3 q4 a0 a1 a2 a3 a4 n0 n1 n2 n3 n4 p inv cnt z0 z1 z2 z3 : W) : cOld c q0 q1 q2 a0 a1 a2 a3 n0 n1 n2 n3 p inv = CycleSubmission.R5.ExecSquare.sqCol3_o0 c q2 q1 q0 a0 a1 a2 a3 a4 n1 n2 n3 n4 p inv cnt n0 := by
  simp only [cOld, hiOld, qOld, loOld, CycleSubmission.R5.ExecSquare.sqCol3_o0, List.foldr_cons, List.foldr_nil, word_add0, mask240_literal, addA, addL, addC, mulC, mmC]
end R5SharedMath3

namespace R5SharedMath4
open EvmSemantics Challenge.EvmProof.Word CycleSubmission.Prepared.Arithmetic R5SharedTools
local notation "W" => UInt256
local notation "N" => UInt256.ofNat
def loOld (c q0 q1 q2 q3 a0 a1 a2 a3 a4 n0 n1 n2 n3 n4 p inv : W) : W := ([((q3)*(n1)), ((q2)*(n2)), ((q1)*(n3)), ((q0)*(n4)), ((a2)*(a2)), ((a0)*(a4)), ((a0)*(a4)), ((a1)*(a3)), ((a1)*(a3)), c].foldr (fun x y => x+y) (N 0))
def loNew (c q0 q1 q2 q3 a0 a1 a2 a3 a4 n0 n1 n2 n3 n4 p inv : W) : W := ([((q3)*(n1)), ((q2)*(n2)), ((q1)*(n3)), ((q0)*(n4)), ((a2)*(a2)), ((a0+a0)*(a4)), ((a1+a1)*(a3)), c].foldr (fun x y => x+y) (N 0))
def hiOld (c q0 q1 q2 q3 a0 a1 a2 a3 a4 n0 n1 n2 n3 n4 p inv : W) : W := ([(UInt256.mulMod (q3) (n1) p), (UInt256.mulMod (q2) (n2) p), (UInt256.mulMod (q1) (n3) p), (UInt256.mulMod (q0) (n4) p), (UInt256.mulMod (a2) (a2) p), (UInt256.mulMod (a0) (a4) p), (UInt256.mulMod (a0) (a4) p), (UInt256.mulMod (a1) (a3) p), (UInt256.mulMod (a1) (a3) p), c].foldr (fun x y => x+y) (N 0))
def hiNew (c q0 q1 q2 q3 a0 a1 a2 a3 a4 n0 n1 n2 n3 n4 p inv : W) : W := ([(UInt256.mulMod (q3) (n1) p), (UInt256.mulMod (q2) (n2) p), (UInt256.mulMod (q1) (n3) p), (UInt256.mulMod (q0) (n4) p), (UInt256.mulMod (a2) (a2) p), (UInt256.mulMod (a0+a0) (a4) p), (UInt256.mulMod (a1+a1) (a3) p), c].foldr (fun x y => x+y) (N 0))
def qOld (c q0 q1 q2 q3 a0 a1 a2 a3 a4 n0 n1 n2 n3 n4 p inv : W) : W := UInt256.shiftRight (inv*(loOld c q0 q1 q2 q3 a0 a1 a2 a3 a4 n0 n1 n2 n3 n4 p inv)) (N 16)
def qNew (c q0 q1 q2 q3 a0 a1 a2 a3 a4 n0 n1 n2 n3 n4 p inv : W) : W := UInt256.shiftRight (inv*(loNew c q0 q1 q2 q3 a0 a1 a2 a3 a4 n0 n1 n2 n3 n4 p inv)) (N 16)
def cOld (c q0 q1 q2 q3 a0 a1 a2 a3 a4 n0 n1 n2 n3 n4 p inv : W) : W := UInt256.mulMod (N 2048) ((UInt256.mulMod (qOld c q0 q1 q2 q3 a0 a1 a2 a3 a4 n0 n1 n2 n3 n4 p inv) (n0) p)+(hiOld c q0 q1 q2 q3 a0 a1 a2 a3 a4 n0 n1 n2 n3 n4 p inv)) p
def cNew (c q0 q1 q2 q3 a0 a1 a2 a3 a4 n0 n1 n2 n3 n4 p inv : W) : W := UInt256.mulMod (N 2048) ((UInt256.mulMod (qNew c q0 q1 q2 q3 a0 a1 a2 a3 a4 n0 n1 n2 n3 n4 p inv) (n0) p)+(hiNew c q0 q1 q2 q3 a0 a1 a2 a3 a4 n0 n1 n2 n3 n4 p inv)) p
theorem q_same (c q0 q1 q2 q3 a0 a1 a2 a3 a4 n0 n1 n2 n3 n4 p inv : W) : qNew c q0 q1 q2 q3 a0 a1 a2 a3 a4 n0 n1 n2 n3 n4 p inv = qOld c q0 q1 q2 q3 a0 a1 a2 a3 a4 n0 n1 n2 n3 n4 p inv := by
  have h0 : (a0+a0)*a4 = a0*a4+a0*a4 := by simpa only [mulC] using CycleSubmission.DoubleInput.low_double a0 a4
  have h1 : (a1+a1)*a3 = a1*a3+a1*a3 := by simpa only [mulC] using CycleSubmission.DoubleInput.low_double a1 a3
  simp only [qNew, qOld, loNew, loOld, List.foldr_cons, List.foldr_nil, word_add0, h0, h1, addA, addL, addC]
theorem c_same (c q0 q1 q2 q3 a0 a1 a2 a3 a4 n0 n1 n2 n3 n4 p inv : W)
    (ha0 : a0.toNat < 2^240) (ha1 : a1.toNat < 2^240)
    (hp : p = CycleSubmission.WordArithmetic.P) (hc : c.toNat < p.toNat) :
    cNew c q0 q1 q2 q3 a0 a1 a2 a3 a4 n0 n1 n2 n3 n4 p inv = cOld c q0 q1 q2 q3 a0 a1 a2 a3 a4 n0 n1 n2 n3 n4 p inv := by
  subst p
  let p := CycleSubmission.WordArithmetic.P
  have hp0 : 0 < p.toNat := by
    dsimp only [p]
    rw [CycleSubmission.WordArithmetic.pValue]
    norm_num [HistoricalSearch.CRTColumn.residueModulus]
  let red : List W → W := fun xs => UInt256.mulMod (N 2048) (xs.foldr (fun x y => x+y) (N 0)) p
  let ys0 : List W := [(UInt256.mulMod (qOld c q0 q1 q2 q3 a0 a1 a2 a3 a4 n0 n1 n2 n3 n4 p inv) (n0) p), (UInt256.mulMod (q3) (n1) p), (UInt256.mulMod (q2) (n2) p), (UInt256.mulMod (q1) (n3) p), (UInt256.mulMod (q0) (n4) p), (UInt256.mulMod (a2) (a2) p), (UInt256.mulMod (a1+a1) (a3) p), c]
  have hb0 : ∀ x ∈ ys0, x.toNat ≤ p.toNat := by
    intro x hx
    simp [ys0] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals first
      | exact Nat.le_of_lt hc
      | exact Nat.le_of_lt (residue_lt _ _ _ hp0)
  have hh0 := high_double_list_radix240 a0 a4 (N 2048) ys0 ha0 (by simp [ys0]) hb0
  have step0 : red [(UInt256.mulMod (qOld c q0 q1 q2 q3 a0 a1 a2 a3 a4 n0 n1 n2 n3 n4 p inv) (n0) p), (UInt256.mulMod (q3) (n1) p), (UInt256.mulMod (q2) (n2) p), (UInt256.mulMod (q1) (n3) p), (UInt256.mulMod (q0) (n4) p), (UInt256.mulMod (a2) (a2) p), (UInt256.mulMod (a0+a0) (a4) p), (UInt256.mulMod (a1+a1) (a3) p), c] = red [(UInt256.mulMod (qOld c q0 q1 q2 q3 a0 a1 a2 a3 a4 n0 n1 n2 n3 n4 p inv) (n0) p), (UInt256.mulMod (q3) (n1) p), (UInt256.mulMod (q2) (n2) p), (UInt256.mulMod (q1) (n3) p), (UInt256.mulMod (q0) (n4) p), (UInt256.mulMod (a2) (a2) p), (UInt256.mulMod (a0) (a4) p), (UInt256.mulMod (a0) (a4) p), (UInt256.mulMod (a1+a1) (a3) p), c] := by
    simpa only [red, ys0, List.foldr_cons, List.foldr_nil, word_add0, addA, addL, addC, mmC] using hh0
  let ys1 : List W := [(UInt256.mulMod (qOld c q0 q1 q2 q3 a0 a1 a2 a3 a4 n0 n1 n2 n3 n4 p inv) (n0) p), (UInt256.mulMod (q3) (n1) p), (UInt256.mulMod (q2) (n2) p), (UInt256.mulMod (q1) (n3) p), (UInt256.mulMod (q0) (n4) p), (UInt256.mulMod (a2) (a2) p), (UInt256.mulMod (a0) (a4) p), (UInt256.mulMod (a0) (a4) p), c]
  have hb1 : ∀ x ∈ ys1, x.toNat ≤ p.toNat := by
    intro x hx
    simp [ys1] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals first
      | exact Nat.le_of_lt hc
      | exact Nat.le_of_lt (residue_lt _ _ _ hp0)
  have hh1 := high_double_list_radix240 a1 a3 (N 2048) ys1 ha1 (by simp [ys1]) hb1
  have step1 : red [(UInt256.mulMod (qOld c q0 q1 q2 q3 a0 a1 a2 a3 a4 n0 n1 n2 n3 n4 p inv) (n0) p), (UInt256.mulMod (q3) (n1) p), (UInt256.mulMod (q2) (n2) p), (UInt256.mulMod (q1) (n3) p), (UInt256.mulMod (q0) (n4) p), (UInt256.mulMod (a2) (a2) p), (UInt256.mulMod (a0) (a4) p), (UInt256.mulMod (a0) (a4) p), (UInt256.mulMod (a1+a1) (a3) p), c] = red [(UInt256.mulMod (qOld c q0 q1 q2 q3 a0 a1 a2 a3 a4 n0 n1 n2 n3 n4 p inv) (n0) p), (UInt256.mulMod (q3) (n1) p), (UInt256.mulMod (q2) (n2) p), (UInt256.mulMod (q1) (n3) p), (UInt256.mulMod (q0) (n4) p), (UInt256.mulMod (a2) (a2) p), (UInt256.mulMod (a0) (a4) p), (UInt256.mulMod (a0) (a4) p), (UInt256.mulMod (a1) (a3) p), (UInt256.mulMod (a1) (a3) p), c] := by
    simpa only [red, ys1, List.foldr_cons, List.foldr_nil, word_add0, addA, addL, addC, mmC] using hh1
  simpa only [cNew, cOld, hiNew, hiOld, q_same, red, List.foldr_cons, List.foldr_nil] using step0.trans step1
theorem old_q_matches (c q0 q1 q2 q3 q4 a0 a1 a2 a3 a4 n0 n1 n2 n3 n4 p inv cnt z0 z1 z2 z3 : W) : qOld c q0 q1 q2 q3 a0 a1 a2 a3 a4 n0 n1 n2 n3 n4 p inv = CycleSubmission.R5.ExecSquare.sqCol4_o4 c q3 q2 q1 q0 a0 a1 a2 a3 a4 n1 n2 n3 n4 p inv cnt n0 := by
  simp only [qOld, loOld, CycleSubmission.R5.ExecSquare.sqCol4_o4, List.foldr_cons, List.foldr_nil, word_add0, mask240_literal, addA, addL, addC, mulC]
theorem old_c_matches (c q0 q1 q2 q3 q4 a0 a1 a2 a3 a4 n0 n1 n2 n3 n4 p inv cnt z0 z1 z2 z3 : W) : cOld c q0 q1 q2 q3 a0 a1 a2 a3 a4 n0 n1 n2 n3 n4 p inv = CycleSubmission.R5.ExecSquare.sqCol4_o0 c q3 q2 q1 q0 a0 a1 a2 a3 a4 n1 n2 n3 n4 p inv cnt n0 := by
  simp only [cOld, hiOld, qOld, loOld, CycleSubmission.R5.ExecSquare.sqCol4_o0, List.foldr_cons, List.foldr_nil, word_add0, mask240_literal, addA, addL, addC, mulC, mmC]
end R5SharedMath4

namespace R5SharedMath5
open EvmSemantics Challenge.EvmProof.Word CycleSubmission.Prepared.Arithmetic R5SharedTools
local notation "W" => UInt256
local notation "N" => UInt256.ofNat
def loOld (c q1 q2 q3 q4 a1 a2 a3 a4 n1 n2 n3 n4 p : W) : W := ([((q4)*(n1)), ((q3)*(n2)), ((q2)*(n3)), ((q1)*(n4)), ((a1)*(a4)), ((a1)*(a4)), ((a2)*(a3)), ((a2)*(a3)), c].foldr (fun x y => x+y) (N 0))
def loNew (c q1 q2 q3 q4 a1 a2 a3 a4 n1 n2 n3 n4 p : W) : W := ([((q4)*(n1)), ((q3)*(n2)), ((q2)*(n3)), ((q1)*(n4)), ((a1+a1)*(a4)), ((a2+a2)*(a3)), c].foldr (fun x y => x+y) (N 0))
def hiOld (c q1 q2 q3 q4 a1 a2 a3 a4 n1 n2 n3 n4 p : W) : W := ([(UInt256.mulMod (q4) (n1) p), (UInt256.mulMod (q3) (n2) p), (UInt256.mulMod (q2) (n3) p), (UInt256.mulMod (q1) (n4) p), (UInt256.mulMod (a1) (a4) p), (UInt256.mulMod (a1) (a4) p), (UInt256.mulMod (a2) (a3) p), (UInt256.mulMod (a2) (a3) p), c].foldr (fun x y => x+y) (N 0))
def hiNew (c q1 q2 q3 q4 a1 a2 a3 a4 n1 n2 n3 n4 p : W) : W := ([(UInt256.mulMod (q4) (n1) p), (UInt256.mulMod (q3) (n2) p), (UInt256.mulMod (q2) (n3) p), (UInt256.mulMod (q1) (n4) p), (UInt256.mulMod (a1+a1) (a4) p), (UInt256.mulMod (a2+a2) (a3) p), c].foldr (fun x y => x+y) (N 0))
def qOld (c q1 q2 q3 q4 a1 a2 a3 a4 n1 n2 n3 n4 p : W) : W := UInt256.land (N (2^240-1)) (loOld c q1 q2 q3 q4 a1 a2 a3 a4 n1 n2 n3 n4 p)
def qNew (c q1 q2 q3 q4 a1 a2 a3 a4 n1 n2 n3 n4 p : W) : W := UInt256.land (N (2^240-1)) (loNew c q1 q2 q3 q4 a1 a2 a3 a4 n1 n2 n3 n4 p)
def cOld (c q1 q2 q3 q4 a1 a2 a3 a4 n1 n2 n3 n4 p : W) : W := UInt256.mulMod (N 2048) (p+((hiOld c q1 q2 q3 q4 a1 a2 a3 a4 n1 n2 n3 n4 p)-(qOld c q1 q2 q3 q4 a1 a2 a3 a4 n1 n2 n3 n4 p))) p
def cNew (c q1 q2 q3 q4 a1 a2 a3 a4 n1 n2 n3 n4 p : W) : W := UInt256.mulMod (N 2048) (p+((hiNew c q1 q2 q3 q4 a1 a2 a3 a4 n1 n2 n3 n4 p)-(qNew c q1 q2 q3 q4 a1 a2 a3 a4 n1 n2 n3 n4 p))) p
theorem q_same (c q1 q2 q3 q4 a1 a2 a3 a4 n1 n2 n3 n4 p : W) : qNew c q1 q2 q3 q4 a1 a2 a3 a4 n1 n2 n3 n4 p = qOld c q1 q2 q3 q4 a1 a2 a3 a4 n1 n2 n3 n4 p := by
  have h0 : (a1+a1)*a4 = a1*a4+a1*a4 := by simpa only [mulC] using CycleSubmission.DoubleInput.low_double a1 a4
  have h1 : (a2+a2)*a3 = a2*a3+a2*a3 := by simpa only [mulC] using CycleSubmission.DoubleInput.low_double a2 a3
  simp only [qNew, qOld, loNew, loOld, List.foldr_cons, List.foldr_nil, word_add0, h0, h1, addA, addL, addC]
theorem c_same (c q1 q2 q3 q4 a1 a2 a3 a4 n1 n2 n3 n4 p : W)
    (ha1 : a1.toNat < 2^240) (ha2 : a2.toNat < 2^240)
    (hp : p = CycleSubmission.WordArithmetic.P) (hc : c.toNat < p.toNat) :
    cNew c q1 q2 q3 q4 a1 a2 a3 a4 n1 n2 n3 n4 p = cOld c q1 q2 q3 q4 a1 a2 a3 a4 n1 n2 n3 n4 p := by
  subst p
  let p := CycleSubmission.WordArithmetic.P
  have hp0 : 0 < p.toNat := by
    dsimp only [p]
    rw [CycleSubmission.WordArithmetic.pValue]
    norm_num [HistoricalSearch.CRTColumn.residueModulus]
  let red : List W → W := fun xs => UInt256.mulMod (N 2048) (p+((xs.foldr (fun x y => x+y) (N 0))-(qOld c q1 q2 q3 q4 a1 a2 a3 a4 n1 n2 n3 n4 p))) p
  have hd : (qOld c q1 q2 q3 q4 a1 a2 a3 a4 n1 n2 n3 n4 p).toNat < p.toNat := mask240_lt_p (loOld c q1 q2 q3 q4 a1 a2 a3 a4 n1 n2 n3 n4 p)
  let ys0 : List W := [(UInt256.mulMod (q4) (n1) p), (UInt256.mulMod (q3) (n2) p), (UInt256.mulMod (q2) (n3) p), (UInt256.mulMod (q1) (n4) p), (UInt256.mulMod (a2+a2) (a3) p), c]
  have hb0 : ∀ x ∈ ys0, x.toNat ≤ p.toNat := by
    intro x hx
    simp [ys0] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl
    all_goals first
      | exact Nat.le_of_lt hc
      | exact Nat.le_of_lt (residue_lt _ _ _ hp0)
  have hh0 := high_double_biased_list_radix240 a1 a4 (N 2048) (qOld c q1 q2 q3 q4 a1 a2 a3 a4 n1 n2 n3 n4 p) ys0 ha1 (by simp [ys0]) hb0 hd
  have step0 : red [(UInt256.mulMod (q4) (n1) p), (UInt256.mulMod (q3) (n2) p), (UInt256.mulMod (q2) (n3) p), (UInt256.mulMod (q1) (n4) p), (UInt256.mulMod (a1+a1) (a4) p), (UInt256.mulMod (a2+a2) (a3) p), c] = red [(UInt256.mulMod (q4) (n1) p), (UInt256.mulMod (q3) (n2) p), (UInt256.mulMod (q2) (n3) p), (UInt256.mulMod (q1) (n4) p), (UInt256.mulMod (a1) (a4) p), (UInt256.mulMod (a1) (a4) p), (UInt256.mulMod (a2+a2) (a3) p), c] := by
    simpa only [red, ys0, List.foldr_cons, List.foldr_nil, word_add0, addA, addL, addC, mmC] using hh0
  let ys1 : List W := [(UInt256.mulMod (q4) (n1) p), (UInt256.mulMod (q3) (n2) p), (UInt256.mulMod (q2) (n3) p), (UInt256.mulMod (q1) (n4) p), (UInt256.mulMod (a1) (a4) p), (UInt256.mulMod (a1) (a4) p), c]
  have hb1 : ∀ x ∈ ys1, x.toNat ≤ p.toNat := by
    intro x hx
    simp [ys1] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals first
      | exact Nat.le_of_lt hc
      | exact Nat.le_of_lt (residue_lt _ _ _ hp0)
  have hh1 := high_double_biased_list_radix240 a2 a3 (N 2048) (qOld c q1 q2 q3 q4 a1 a2 a3 a4 n1 n2 n3 n4 p) ys1 ha2 (by simp [ys1]) hb1 hd
  have step1 : red [(UInt256.mulMod (q4) (n1) p), (UInt256.mulMod (q3) (n2) p), (UInt256.mulMod (q2) (n3) p), (UInt256.mulMod (q1) (n4) p), (UInt256.mulMod (a1) (a4) p), (UInt256.mulMod (a1) (a4) p), (UInt256.mulMod (a2+a2) (a3) p), c] = red [(UInt256.mulMod (q4) (n1) p), (UInt256.mulMod (q3) (n2) p), (UInt256.mulMod (q2) (n3) p), (UInt256.mulMod (q1) (n4) p), (UInt256.mulMod (a1) (a4) p), (UInt256.mulMod (a1) (a4) p), (UInt256.mulMod (a2) (a3) p), (UInt256.mulMod (a2) (a3) p), c] := by
    simpa only [red, ys1, List.foldr_cons, List.foldr_nil, word_add0, addA, addL, addC, mmC] using hh1
  simpa only [cNew, cOld, hiNew, hiOld, q_same, red, List.foldr_cons, List.foldr_nil] using step0.trans step1
theorem old_q_matches (c q0 q1 q2 q3 q4 a0 a1 a2 a3 a4 n0 n1 n2 n3 n4 p inv cnt z0 z1 z2 z3 : W) : qOld c q1 q2 q3 q4 a1 a2 a3 a4 n1 n2 n3 n4 p = CycleSubmission.R5.ExecSquare.sqCol5_o5 c q3 q2 q1 q4 a0 a1 a2 a3 a4 n1 n2 n3 n4 p inv cnt := by
  simp only [qOld, loOld, CycleSubmission.R5.ExecSquare.sqCol5_o5, List.foldr_cons, List.foldr_nil, word_add0, mask240_literal, addA, addL, addC, mulC]
theorem old_c_matches (c q0 q1 q2 q3 q4 a0 a1 a2 a3 a4 n0 n1 n2 n3 n4 p inv cnt z0 z1 z2 z3 : W) : cOld c q1 q2 q3 q4 a1 a2 a3 a4 n1 n2 n3 n4 p = CycleSubmission.R5.ExecSquare.sqCol5_o0 c q3 q2 q1 q4 a0 a1 a2 a3 a4 n1 n2 n3 n4 p inv cnt := by
  simp only [cOld, hiOld, qOld, loOld, CycleSubmission.R5.ExecSquare.sqCol5_o0, List.foldr_cons, List.foldr_nil, word_add0, mask240_literal, addA, addL, addC, mulC, mmC]
end R5SharedMath5

namespace R5SharedMath6
open EvmSemantics Challenge.EvmProof.Word CycleSubmission.Prepared.Arithmetic R5SharedTools
local notation "W" => UInt256
local notation "N" => UInt256.ofNat
def loOld (c q2 q3 q4 a2 a3 a4 n2 n3 n4 p : W) : W := ([((q4)*(n2)), ((q3)*(n3)), ((q2)*(n4)), ((a3)*(a3)), ((a2)*(a4)), ((a2)*(a4)), c].foldr (fun x y => x+y) (N 0))
def loNew (c q2 q3 q4 a2 a3 a4 n2 n3 n4 p : W) : W := ([((q4)*(n2)), ((q3)*(n3)), ((q2)*(n4)), ((a3)*(a3)), ((a2+a2)*(a4)), c].foldr (fun x y => x+y) (N 0))
def hiOld (c q2 q3 q4 a2 a3 a4 n2 n3 n4 p : W) : W := ([(UInt256.mulMod (q4) (n2) p), (UInt256.mulMod (q3) (n3) p), (UInt256.mulMod (q2) (n4) p), (UInt256.mulMod (a3) (a3) p), (UInt256.mulMod (a2) (a4) p), (UInt256.mulMod (a2) (a4) p), c].foldr (fun x y => x+y) (N 0))
def hiNew (c q2 q3 q4 a2 a3 a4 n2 n3 n4 p : W) : W := ([(UInt256.mulMod (q4) (n2) p), (UInt256.mulMod (q3) (n3) p), (UInt256.mulMod (q2) (n4) p), (UInt256.mulMod (a3) (a3) p), (UInt256.mulMod (a2+a2) (a4) p), c].foldr (fun x y => x+y) (N 0))
def qOld (c q2 q3 q4 a2 a3 a4 n2 n3 n4 p : W) : W := UInt256.land (N (2^240-1)) (loOld c q2 q3 q4 a2 a3 a4 n2 n3 n4 p)
def qNew (c q2 q3 q4 a2 a3 a4 n2 n3 n4 p : W) : W := UInt256.land (N (2^240-1)) (loNew c q2 q3 q4 a2 a3 a4 n2 n3 n4 p)
def cOld (c q2 q3 q4 a2 a3 a4 n2 n3 n4 p : W) : W := UInt256.mulMod (N 2048) (p+((hiOld c q2 q3 q4 a2 a3 a4 n2 n3 n4 p)-(qOld c q2 q3 q4 a2 a3 a4 n2 n3 n4 p))) p
def cNew (c q2 q3 q4 a2 a3 a4 n2 n3 n4 p : W) : W := UInt256.mulMod (N 2048) (p+((hiNew c q2 q3 q4 a2 a3 a4 n2 n3 n4 p)-(qNew c q2 q3 q4 a2 a3 a4 n2 n3 n4 p))) p
theorem q_same (c q2 q3 q4 a2 a3 a4 n2 n3 n4 p : W) : qNew c q2 q3 q4 a2 a3 a4 n2 n3 n4 p = qOld c q2 q3 q4 a2 a3 a4 n2 n3 n4 p := by
  have h0 : (a2+a2)*a4 = a2*a4+a2*a4 := by simpa only [mulC] using CycleSubmission.DoubleInput.low_double a2 a4
  simp only [qNew, qOld, loNew, loOld, List.foldr_cons, List.foldr_nil, word_add0, h0, addA, addL, addC]
theorem c_same (c q2 q3 q4 a2 a3 a4 n2 n3 n4 p : W)
    (ha2 : a2.toNat < 2^240)
    (hp : p = CycleSubmission.WordArithmetic.P) (hc : c.toNat < p.toNat) :
    cNew c q2 q3 q4 a2 a3 a4 n2 n3 n4 p = cOld c q2 q3 q4 a2 a3 a4 n2 n3 n4 p := by
  subst p
  let p := CycleSubmission.WordArithmetic.P
  have hp0 : 0 < p.toNat := by
    dsimp only [p]
    rw [CycleSubmission.WordArithmetic.pValue]
    norm_num [HistoricalSearch.CRTColumn.residueModulus]
  let red : List W → W := fun xs => UInt256.mulMod (N 2048) (p+((xs.foldr (fun x y => x+y) (N 0))-(qOld c q2 q3 q4 a2 a3 a4 n2 n3 n4 p))) p
  have hd : (qOld c q2 q3 q4 a2 a3 a4 n2 n3 n4 p).toNat < p.toNat := mask240_lt_p (loOld c q2 q3 q4 a2 a3 a4 n2 n3 n4 p)
  let ys0 : List W := [(UInt256.mulMod (q4) (n2) p), (UInt256.mulMod (q3) (n3) p), (UInt256.mulMod (q2) (n4) p), (UInt256.mulMod (a3) (a3) p), c]
  have hb0 : ∀ x ∈ ys0, x.toNat ≤ p.toNat := by
    intro x hx
    simp [ys0] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl
    all_goals first
      | exact Nat.le_of_lt hc
      | exact Nat.le_of_lt (residue_lt _ _ _ hp0)
  have hh0 := high_double_biased_list_radix240 a2 a4 (N 2048) (qOld c q2 q3 q4 a2 a3 a4 n2 n3 n4 p) ys0 ha2 (by simp [ys0]) hb0 hd
  have step0 : red [(UInt256.mulMod (q4) (n2) p), (UInt256.mulMod (q3) (n3) p), (UInt256.mulMod (q2) (n4) p), (UInt256.mulMod (a3) (a3) p), (UInt256.mulMod (a2+a2) (a4) p), c] = red [(UInt256.mulMod (q4) (n2) p), (UInt256.mulMod (q3) (n3) p), (UInt256.mulMod (q2) (n4) p), (UInt256.mulMod (a3) (a3) p), (UInt256.mulMod (a2) (a4) p), (UInt256.mulMod (a2) (a4) p), c] := by
    simpa only [red, ys0, List.foldr_cons, List.foldr_nil, word_add0, addA, addL, addC, mmC] using hh0
  simpa only [cNew, cOld, hiNew, hiOld, q_same, red, List.foldr_cons, List.foldr_nil] using step0
theorem old_q_matches (c q0 q1 q2 q3 q4 a0 a1 a2 a3 a4 n0 n1 n2 n3 n4 p inv cnt z0 z1 z2 z3 : W) : qOld c q2 q3 q4 a2 a3 a4 n2 n3 n4 p = CycleSubmission.R5.ExecSquare.sqCol6_o6 c q3 q2 q1 q4 z0 a1 a2 a3 a4 n1 n2 n3 n4 p inv cnt := by
  simp only [qOld, loOld, CycleSubmission.R5.ExecSquare.sqCol6_o6, List.foldr_cons, List.foldr_nil, word_add0, mask240_literal, addA, addL, addC, mulC]
theorem old_c_matches (c q0 q1 q2 q3 q4 a0 a1 a2 a3 a4 n0 n1 n2 n3 n4 p inv cnt z0 z1 z2 z3 : W) : cOld c q2 q3 q4 a2 a3 a4 n2 n3 n4 p = CycleSubmission.R5.ExecSquare.sqCol6_o0 c q3 q2 q1 q4 z0 a1 a2 a3 a4 n1 n2 n3 n4 p inv cnt := by
  simp only [cOld, hiOld, qOld, loOld, CycleSubmission.R5.ExecSquare.sqCol6_o0, List.foldr_cons, List.foldr_nil, word_add0, mask240_literal, addA, addL, addC, mulC, mmC]
end R5SharedMath6

namespace R5SharedMath7
open EvmSemantics Challenge.EvmProof.Word CycleSubmission.Prepared.Arithmetic R5SharedTools
local notation "W" => UInt256
local notation "N" => UInt256.ofNat
def loOld (c q3 q4 a3 a4 n3 n4 p : W) : W := ([((q4)*(n3)), ((q3)*(n4)), ((a3)*(a4)), ((a3)*(a4)), c].foldr (fun x y => x+y) (N 0))
def loNew (c q3 q4 a3 a4 n3 n4 p : W) : W := ([((q4)*(n3)), ((q3)*(n4)), ((a3+a3)*(a4)), c].foldr (fun x y => x+y) (N 0))
def hiOld (c q3 q4 a3 a4 n3 n4 p : W) : W := ([(UInt256.mulMod (q4) (n3) p), (UInt256.mulMod (q3) (n4) p), (UInt256.mulMod (a3) (a4) p), (UInt256.mulMod (a3) (a4) p), c].foldr (fun x y => x+y) (N 0))
def hiNew (c q3 q4 a3 a4 n3 n4 p : W) : W := ([(UInt256.mulMod (q4) (n3) p), (UInt256.mulMod (q3) (n4) p), (UInt256.mulMod (a3+a3) (a4) p), c].foldr (fun x y => x+y) (N 0))
def qOld (c q3 q4 a3 a4 n3 n4 p : W) : W := UInt256.land (N (2^240-1)) (loOld c q3 q4 a3 a4 n3 n4 p)
def qNew (c q3 q4 a3 a4 n3 n4 p : W) : W := UInt256.land (N (2^240-1)) (loNew c q3 q4 a3 a4 n3 n4 p)
def cOld (c q3 q4 a3 a4 n3 n4 p : W) : W := UInt256.mulMod (N 2048) (p+((hiOld c q3 q4 a3 a4 n3 n4 p)-(qOld c q3 q4 a3 a4 n3 n4 p))) p
def cNew (c q3 q4 a3 a4 n3 n4 p : W) : W := UInt256.mulMod (N 2048) (p+((hiNew c q3 q4 a3 a4 n3 n4 p)-(qNew c q3 q4 a3 a4 n3 n4 p))) p
theorem q_same (c q3 q4 a3 a4 n3 n4 p : W) : qNew c q3 q4 a3 a4 n3 n4 p = qOld c q3 q4 a3 a4 n3 n4 p := by
  have h0 : (a3+a3)*a4 = a3*a4+a3*a4 := by simpa only [mulC] using CycleSubmission.DoubleInput.low_double a3 a4
  simp only [qNew, qOld, loNew, loOld, List.foldr_cons, List.foldr_nil, word_add0, h0, addA, addL, addC]
theorem c_same (c q3 q4 a3 a4 n3 n4 p : W)
    (ha3 : a3.toNat < 2^240)
    (hp : p = CycleSubmission.WordArithmetic.P) (hc : c.toNat < p.toNat) :
    cNew c q3 q4 a3 a4 n3 n4 p = cOld c q3 q4 a3 a4 n3 n4 p := by
  subst p
  let p := CycleSubmission.WordArithmetic.P
  have hp0 : 0 < p.toNat := by
    dsimp only [p]
    rw [CycleSubmission.WordArithmetic.pValue]
    norm_num [HistoricalSearch.CRTColumn.residueModulus]
  let red : List W → W := fun xs => UInt256.mulMod (N 2048) (p+((xs.foldr (fun x y => x+y) (N 0))-(qOld c q3 q4 a3 a4 n3 n4 p))) p
  have hd : (qOld c q3 q4 a3 a4 n3 n4 p).toNat < p.toNat := mask240_lt_p (loOld c q3 q4 a3 a4 n3 n4 p)
  let ys0 : List W := [(UInt256.mulMod (q4) (n3) p), (UInt256.mulMod (q3) (n4) p), c]
  have hb0 : ∀ x ∈ ys0, x.toNat ≤ p.toNat := by
    intro x hx
    simp [ys0] at hx
    rcases hx with rfl | rfl | rfl
    all_goals first
      | exact Nat.le_of_lt hc
      | exact Nat.le_of_lt (residue_lt _ _ _ hp0)
  have hh0 := high_double_biased_list_radix240 a3 a4 (N 2048) (qOld c q3 q4 a3 a4 n3 n4 p) ys0 ha3 (by simp [ys0]) hb0 hd
  have step0 : red [(UInt256.mulMod (q4) (n3) p), (UInt256.mulMod (q3) (n4) p), (UInt256.mulMod (a3+a3) (a4) p), c] = red [(UInt256.mulMod (q4) (n3) p), (UInt256.mulMod (q3) (n4) p), (UInt256.mulMod (a3) (a4) p), (UInt256.mulMod (a3) (a4) p), c] := by
    simpa only [red, ys0, List.foldr_cons, List.foldr_nil, word_add0, addA, addL, addC, mmC] using hh0
  simpa only [cNew, cOld, hiNew, hiOld, q_same, red, List.foldr_cons, List.foldr_nil] using step0
theorem old_q_matches (c q0 q1 q2 q3 q4 a0 a1 a2 a3 a4 n0 n1 n2 n3 n4 p inv cnt z0 z1 z2 z3 : W) : qOld c q3 q4 a3 a4 n3 n4 p = CycleSubmission.R5.ExecSquare.sqCol7_o7 c q3 q2 q1 q4 z0 z1 a2 a3 a4 n1 n2 n3 n4 p inv cnt := by
  simp only [qOld, loOld, CycleSubmission.R5.ExecSquare.sqCol7_o7, List.foldr_cons, List.foldr_nil, word_add0, mask240_literal, addA, addL, addC, mulC]
theorem old_c_matches (c q0 q1 q2 q3 q4 a0 a1 a2 a3 a4 n0 n1 n2 n3 n4 p inv cnt z0 z1 z2 z3 : W) : cOld c q3 q4 a3 a4 n3 n4 p = CycleSubmission.R5.ExecSquare.sqCol7_o0 c q3 q2 q1 q4 z0 z1 a2 a3 a4 n1 n2 n3 n4 p inv cnt := by
  simp only [cOld, hiOld, qOld, loOld, CycleSubmission.R5.ExecSquare.sqCol7_o0, List.foldr_cons, List.foldr_nil, word_add0, mask240_literal, addA, addL, addC, mulC, mmC]
end R5SharedMath7
namespace NextR5Columns
open EvmSemantics EvmSemantics.EVM YulEvmCompiler Challenge.EvmProof.Word CycleSubmission.Prepared.Arithmetic R5SharedTools
open Challenge.Modexp.Submission.Proofs.Bytecode.WindowNibbleKernel
local notation "W" => UInt256
local notation "N" => UInt256.ofNat
def history0 (s : State) (c q0 q1 q2 q3 q4 a0 a1 a2 a3 a4 n0 n1 n2 n3 n4 p inv cnt z0 z1 z2 z3 : W) (rest : List W) : State := {s with pc := N 4046, stack := (CycleSubmission.R5.ExecSquare.sqCol0_o0 (a0) (a1) (a2) (a3) (a4) (n1) (n2) (n3) (n4) (p) (inv) (cnt) (n0)) :: (CycleSubmission.R5.ExecSquare.sqCol0_o1 (a0) (a1) (a2) (a3) (a4) (n1) (n2) (n3) (n4) (p) (inv) (cnt) (n0)) :: ((a0+a0)) :: (a1) :: (a2) :: (a3) :: (a4) :: (n1) :: (n2) :: (n3) :: (n4) :: (p) :: (inv) :: (cnt) :: rest}
theorem stage0_history (s : State) (c q0 q1 q2 q3 q4 a0 a1 a2 a3 a4 n0 n1 n2 n3 n4 p inv cnt z0 z1 z2 z3 : W) (rest : List W)
    (hn0 : MachineState.readWord s.memory 160 = n0) (hi : MachineState.readWord s.memory 192 = inv)
    (hp : p = CycleSubmission.WordArithmetic.P)
    (ha0 : a0.toNat < 2^240) (ha1 : a1.toNat < 2^240) (ha2 : a2.toNat < 2^240) (ha3 : a3.toNat < 2^240)
    (hc : c.toNat < p.toNat) :
    stage0Model (s) (a0) (a1) (a2) (a3) (a4) (n1) (n2) (n3) (n4) (p) (inv) (cnt) (rest) = history0 (s) (c) (q0) (q1) (q2) (q3) (q4) (a0) (a1) (a2) (a3) (a4) (n0) (n1) (n2) (n3) (n4) (p) (inv) (cnt) (z0) (z1) (z2) (z3) (rest) := by
  simp only [stage0Model, history0, hn0, hi, word_add0, mask240_literal, addA, addL, addC, mulC, mmC, andC, CycleSubmission.R5.ExecSquare.sqCol0_o0, CycleSubmission.R5.ExecSquare.sqCol0_o1]
theorem run_stage0 (s : State) (c q0 q1 q2 q3 q4 a0 a1 a2 a3 a4 n0 n1 n2 n3 n4 p inv cnt z0 z1 z2 z3 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat)
    (hn0 : MachineState.readWord s.memory 160 = n0) (hi : MachineState.readWord s.memory 192 = inv)
    (hp : p = CycleSubmission.WordArithmetic.P)
    (ha0 : a0.toNat < 2^240) (ha1 : a1.toNat < 2^240) (ha2 : a2.toNat < 2^240) (ha3 : a3.toNat < 2^240)
    (hc : c.toNat < p.toNat) :
    runInstructions stage0Program {s with pc := N 4018, stack := (a0) :: (a1) :: (a2) :: (a3) :: (a4) :: (n1) :: (n2) :: (n3) :: (n4) :: (p) :: (inv) :: (cnt) :: rest} = some (history0 (s) (c) (q0) (q1) (q2) (q3) (q4) (a0) (a1) (a2) (a3) (a4) (n0) (n1) (n2) (n3) (n4) (p) (inv) (cnt) (z0) (z1) (z2) (z3) (rest)) := by
  exact (stage0_run (s) (a0) (a1) (a2) (a3) (a4) (n1) (n2) (n3) (n4) (p) (inv) (cnt) (rest) (hcap) (hact)).trans (congrArg some (stage0_history (s) (c) (q0) (q1) (q2) (q3) (q4) (a0) (a1) (a2) (a3) (a4) (n0) (n1) (n2) (n3) (n4) (p) (inv) (cnt) (z0) (z1) (z2) (z3) (rest) (hn0) (hi) (hp) (ha0) (ha1) (ha2) (ha3) (hc)))
def history1 (s : State) (c q0 q1 q2 q3 q4 a0 a1 a2 a3 a4 n0 n1 n2 n3 n4 p inv cnt z0 z1 z2 z3 : W) (rest : List W) : State := {s with pc := N 4084, stack := (CycleSubmission.R5.ExecSquare.sqCol1_o0 (c) (q0) (a0) (a1) (a2) (a3) (a4) (n1) (n2) (n3) (n4) (p) (inv) (cnt) (n0)) :: (CycleSubmission.R5.ExecSquare.sqCol1_o1 (c) (q0) (a0) (a1) (a2) (a3) (a4) (n1) (n2) (n3) (n4) (p) (inv) (cnt) (n0)) :: (q0) :: ((a0+a0)) :: (a1) :: (a2) :: (a3) :: (a4) :: (n1) :: (n2) :: (n3) :: (n4) :: (p) :: (inv) :: (cnt) :: rest}
theorem stage1_history (s : State) (c q0 q1 q2 q3 q4 a0 a1 a2 a3 a4 n0 n1 n2 n3 n4 p inv cnt z0 z1 z2 z3 : W) (rest : List W)
    (hn0 : MachineState.readWord s.memory 160 = n0) (hi : MachineState.readWord s.memory 192 = inv)
    (hp : p = CycleSubmission.WordArithmetic.P)
    (ha0 : a0.toNat < 2^240) (ha1 : a1.toNat < 2^240) (ha2 : a2.toNat < 2^240) (ha3 : a3.toNat < 2^240)
    (hc : c.toNat < p.toNat) :
    stage1Model (s) (c) (q0) ((a0+a0)) (a1) (a2) (a3) (a4) (n1) (n2) (n3) (n4) (p) (inv) (cnt) (rest) = history1 (s) (c) (q0) (q1) (q2) (q3) (q4) (a0) (a1) (a2) (a3) (a4) (n0) (n1) (n2) (n3) (n4) (p) (inv) (cnt) (z0) (z1) (z2) (z3) (rest) := by
  calc
    stage1Model (s) (c) (q0) ((a0+a0)) (a1) (a2) (a3) (a4) (n1) (n2) (n3) (n4) (p) (inv) (cnt) (rest) = {s with pc := N 4084, stack := (R5SharedMath1.cNew (c) (q0) (a0) (a1) (n0) (n1) (p) (inv)) :: (R5SharedMath1.qNew (c) (q0) (a0) (a1) (n0) (n1) (p) (inv)) :: (q0) :: ((a0+a0)) :: (a1) :: (a2) :: (a3) :: (a4) :: (n1) :: (n2) :: (n3) :: (n4) :: (p) :: (inv) :: (cnt) :: rest} := by
      simp only [stage1Model, R5SharedMath1.cNew, R5SharedMath1.qNew, R5SharedMath1.hiNew, R5SharedMath1.loNew, hn0, hi, List.foldr_cons, List.foldr_nil, word_add0, mask240_literal, addA, addL, addC, mulC, mmC, andC]
    _ = history1 (s) (c) (q0) (q1) (q2) (q3) (q4) (a0) (a1) (a2) (a3) (a4) (n0) (n1) (n2) (n3) (n4) (p) (inv) (cnt) (z0) (z1) (z2) (z3) (rest) := by
      have heC := R5SharedMath1.c_same (c) (q0) (a0) (a1) (n0) (n1) (p) (inv) (ha0) (hp) (hc)
      have heQ := R5SharedMath1.q_same (c) (q0) (a0) (a1) (n0) (n1) (p) (inv)
      have hoC := R5SharedMath1.old_c_matches (c) (q0) (q1) (q2) (q3) (q4) (a0) (a1) (a2) (a3) (a4) (n0) (n1) (n2) (n3) (n4) (p) (inv) (cnt) (z0) (z1) (z2) (z3)
      have hoQ := R5SharedMath1.old_q_matches (c) (q0) (q1) (q2) (q3) (q4) (a0) (a1) (a2) (a3) (a4) (n0) (n1) (n2) (n3) (n4) (p) (inv) (cnt) (z0) (z1) (z2) (z3)
      simp only [history1, heC, heQ, hoC, hoQ]
theorem run_stage1 (s : State) (c q0 q1 q2 q3 q4 a0 a1 a2 a3 a4 n0 n1 n2 n3 n4 p inv cnt z0 z1 z2 z3 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat)
    (hn0 : MachineState.readWord s.memory 160 = n0) (hi : MachineState.readWord s.memory 192 = inv)
    (hp : p = CycleSubmission.WordArithmetic.P)
    (ha0 : a0.toNat < 2^240) (ha1 : a1.toNat < 2^240) (ha2 : a2.toNat < 2^240) (ha3 : a3.toNat < 2^240)
    (hc : c.toNat < p.toNat) :
    runInstructions stage1Program {s with pc := N 4046, stack := (c) :: (q0) :: ((a0+a0)) :: (a1) :: (a2) :: (a3) :: (a4) :: (n1) :: (n2) :: (n3) :: (n4) :: (p) :: (inv) :: (cnt) :: rest} = some (history1 (s) (c) (q0) (q1) (q2) (q3) (q4) (a0) (a1) (a2) (a3) (a4) (n0) (n1) (n2) (n3) (n4) (p) (inv) (cnt) (z0) (z1) (z2) (z3) (rest)) := by
  exact (stage1_run (s) (c) (q0) ((a0+a0)) (a1) (a2) (a3) (a4) (n1) (n2) (n3) (n4) (p) (inv) (cnt) (rest) (hcap) (hact)).trans (congrArg some (stage1_history (s) (c) (q0) (q1) (q2) (q3) (q4) (a0) (a1) (a2) (a3) (a4) (n0) (n1) (n2) (n3) (n4) (p) (inv) (cnt) (z0) (z1) (z2) (z3) (rest) (hn0) (hi) (hp) (ha0) (ha1) (ha2) (ha3) (hc)))
def history2 (s : State) (c q0 q1 q2 q3 q4 a0 a1 a2 a3 a4 n0 n1 n2 n3 n4 p inv cnt z0 z1 z2 z3 : W) (rest : List W) : State := {s with pc := N 4143, stack := (CycleSubmission.R5.ExecSquare.sqCol2_o0 (c) (q1) (q0) (a0) (a1) (a2) (a3) (a4) (n1) (n2) (n3) (n4) (p) (inv) (cnt) (n0)) :: (CycleSubmission.R5.ExecSquare.sqCol2_o1 (c) (q1) (q0) (a0) (a1) (a2) (a3) (a4) (n1) (n2) (n3) (n4) (p) (inv) (cnt) (n0)) :: (q1) :: (q0) :: ((a0+a0)) :: ((a1+a1)) :: (a2) :: (a3) :: (a4) :: (n1) :: (n2) :: (n3) :: (n4) :: (p) :: (inv) :: (cnt) :: rest}
theorem stage2_history (s : State) (c q0 q1 q2 q3 q4 a0 a1 a2 a3 a4 n0 n1 n2 n3 n4 p inv cnt z0 z1 z2 z3 : W) (rest : List W)
    (hn0 : MachineState.readWord s.memory 160 = n0) (hi : MachineState.readWord s.memory 192 = inv)
    (hp : p = CycleSubmission.WordArithmetic.P)
    (ha0 : a0.toNat < 2^240) (ha1 : a1.toNat < 2^240) (ha2 : a2.toNat < 2^240) (ha3 : a3.toNat < 2^240)
    (hc : c.toNat < p.toNat) :
    stage2Model (s) (c) (q1) (q0) ((a0+a0)) (a1) (a2) (a3) (a4) (n1) (n2) (n3) (n4) (p) (inv) (cnt) (rest) = history2 (s) (c) (q0) (q1) (q2) (q3) (q4) (a0) (a1) (a2) (a3) (a4) (n0) (n1) (n2) (n3) (n4) (p) (inv) (cnt) (z0) (z1) (z2) (z3) (rest) := by
  calc
    stage2Model (s) (c) (q1) (q0) ((a0+a0)) (a1) (a2) (a3) (a4) (n1) (n2) (n3) (n4) (p) (inv) (cnt) (rest) = {s with pc := N 4143, stack := (R5SharedMath2.cNew (c) (q0) (q1) (a0) (a1) (a2) (n0) (n1) (n2) (p) (inv)) :: (R5SharedMath2.qNew (c) (q0) (q1) (a0) (a1) (a2) (n0) (n1) (n2) (p) (inv)) :: (q1) :: (q0) :: ((a0+a0)) :: ((a1+a1)) :: (a2) :: (a3) :: (a4) :: (n1) :: (n2) :: (n3) :: (n4) :: (p) :: (inv) :: (cnt) :: rest} := by
      simp only [stage2Model, R5SharedMath2.cNew, R5SharedMath2.qNew, R5SharedMath2.hiNew, R5SharedMath2.loNew, hn0, hi, List.foldr_cons, List.foldr_nil, word_add0, mask240_literal, addA, addL, addC, mulC, mmC, andC]
    _ = history2 (s) (c) (q0) (q1) (q2) (q3) (q4) (a0) (a1) (a2) (a3) (a4) (n0) (n1) (n2) (n3) (n4) (p) (inv) (cnt) (z0) (z1) (z2) (z3) (rest) := by
      have heC := R5SharedMath2.c_same (c) (q0) (q1) (a0) (a1) (a2) (n0) (n1) (n2) (p) (inv) (ha0) (hp) (hc)
      have heQ := R5SharedMath2.q_same (c) (q0) (q1) (a0) (a1) (a2) (n0) (n1) (n2) (p) (inv)
      have hoC := R5SharedMath2.old_c_matches (c) (q0) (q1) (q2) (q3) (q4) (a0) (a1) (a2) (a3) (a4) (n0) (n1) (n2) (n3) (n4) (p) (inv) (cnt) (z0) (z1) (z2) (z3)
      have hoQ := R5SharedMath2.old_q_matches (c) (q0) (q1) (q2) (q3) (q4) (a0) (a1) (a2) (a3) (a4) (n0) (n1) (n2) (n3) (n4) (p) (inv) (cnt) (z0) (z1) (z2) (z3)
      simp only [history2, heC, heQ, hoC, hoQ]
theorem run_stage2 (s : State) (c q0 q1 q2 q3 q4 a0 a1 a2 a3 a4 n0 n1 n2 n3 n4 p inv cnt z0 z1 z2 z3 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat)
    (hn0 : MachineState.readWord s.memory 160 = n0) (hi : MachineState.readWord s.memory 192 = inv)
    (hp : p = CycleSubmission.WordArithmetic.P)
    (ha0 : a0.toNat < 2^240) (ha1 : a1.toNat < 2^240) (ha2 : a2.toNat < 2^240) (ha3 : a3.toNat < 2^240)
    (hc : c.toNat < p.toNat) :
    runInstructions stage2Program {s with pc := N 4084, stack := (c) :: (q1) :: (q0) :: ((a0+a0)) :: (a1) :: (a2) :: (a3) :: (a4) :: (n1) :: (n2) :: (n3) :: (n4) :: (p) :: (inv) :: (cnt) :: rest} = some (history2 (s) (c) (q0) (q1) (q2) (q3) (q4) (a0) (a1) (a2) (a3) (a4) (n0) (n1) (n2) (n3) (n4) (p) (inv) (cnt) (z0) (z1) (z2) (z3) (rest)) := by
  exact (stage2_run (s) (c) (q1) (q0) ((a0+a0)) (a1) (a2) (a3) (a4) (n1) (n2) (n3) (n4) (p) (inv) (cnt) (rest) (hcap) (hact)).trans (congrArg some (stage2_history (s) (c) (q0) (q1) (q2) (q3) (q4) (a0) (a1) (a2) (a3) (a4) (n0) (n1) (n2) (n3) (n4) (p) (inv) (cnt) (z0) (z1) (z2) (z3) (rest) (hn0) (hi) (hp) (ha0) (ha1) (ha2) (ha3) (hc)))
def history3 (s : State) (c q0 q1 q2 q3 q4 a0 a1 a2 a3 a4 n0 n1 n2 n3 n4 p inv cnt z0 z1 z2 z3 : W) (rest : List W) : State := {s with pc := N 4208, stack := (CycleSubmission.R5.ExecSquare.sqCol3_o0 (c) (q2) (q1) (q0) (a0) (a1) (a2) (a3) (a4) (n1) (n2) (n3) (n4) (p) (inv) (cnt) (n0)) :: (CycleSubmission.R5.ExecSquare.sqCol3_o1 (c) (q2) (q1) (q0) (a0) (a1) (a2) (a3) (a4) (n1) (n2) (n3) (n4) (p) (inv) (cnt) (n0)) :: (q2) :: (q1) :: (q0) :: ((a0+a0)) :: ((a1+a1)) :: (a2) :: (a3) :: (a4) :: (n1) :: (n2) :: (n3) :: (n4) :: (p) :: (inv) :: (cnt) :: rest}
theorem stage3_history (s : State) (c q0 q1 q2 q3 q4 a0 a1 a2 a3 a4 n0 n1 n2 n3 n4 p inv cnt z0 z1 z2 z3 : W) (rest : List W)
    (hn0 : MachineState.readWord s.memory 160 = n0) (hi : MachineState.readWord s.memory 192 = inv)
    (hp : p = CycleSubmission.WordArithmetic.P)
    (ha0 : a0.toNat < 2^240) (ha1 : a1.toNat < 2^240) (ha2 : a2.toNat < 2^240) (ha3 : a3.toNat < 2^240)
    (hc : c.toNat < p.toNat) :
    stage3Model (s) (c) (q2) (q1) (q0) ((a0+a0)) ((a1+a1)) (a2) (a3) (a4) (n1) (n2) (n3) (n4) (p) (inv) (cnt) (rest) = history3 (s) (c) (q0) (q1) (q2) (q3) (q4) (a0) (a1) (a2) (a3) (a4) (n0) (n1) (n2) (n3) (n4) (p) (inv) (cnt) (z0) (z1) (z2) (z3) (rest) := by
  calc
    stage3Model (s) (c) (q2) (q1) (q0) ((a0+a0)) ((a1+a1)) (a2) (a3) (a4) (n1) (n2) (n3) (n4) (p) (inv) (cnt) (rest) = {s with pc := N 4208, stack := (R5SharedMath3.cNew (c) (q0) (q1) (q2) (a0) (a1) (a2) (a3) (n0) (n1) (n2) (n3) (p) (inv)) :: (R5SharedMath3.qNew (c) (q0) (q1) (q2) (a0) (a1) (a2) (a3) (n0) (n1) (n2) (n3) (p) (inv)) :: (q2) :: (q1) :: (q0) :: ((a0+a0)) :: ((a1+a1)) :: (a2) :: (a3) :: (a4) :: (n1) :: (n2) :: (n3) :: (n4) :: (p) :: (inv) :: (cnt) :: rest} := by
      simp only [stage3Model, R5SharedMath3.cNew, R5SharedMath3.qNew, R5SharedMath3.hiNew, R5SharedMath3.loNew, hn0, hi, List.foldr_cons, List.foldr_nil, word_add0, mask240_literal, addA, addL, addC, mulC, mmC, andC]
    _ = history3 (s) (c) (q0) (q1) (q2) (q3) (q4) (a0) (a1) (a2) (a3) (a4) (n0) (n1) (n2) (n3) (n4) (p) (inv) (cnt) (z0) (z1) (z2) (z3) (rest) := by
      have heC := R5SharedMath3.c_same (c) (q0) (q1) (q2) (a0) (a1) (a2) (a3) (n0) (n1) (n2) (n3) (p) (inv) (ha0) (ha1) (hp) (hc)
      have heQ := R5SharedMath3.q_same (c) (q0) (q1) (q2) (a0) (a1) (a2) (a3) (n0) (n1) (n2) (n3) (p) (inv)
      have hoC := R5SharedMath3.old_c_matches (c) (q0) (q1) (q2) (q3) (q4) (a0) (a1) (a2) (a3) (a4) (n0) (n1) (n2) (n3) (n4) (p) (inv) (cnt) (z0) (z1) (z2) (z3)
      have hoQ := R5SharedMath3.old_q_matches (c) (q0) (q1) (q2) (q3) (q4) (a0) (a1) (a2) (a3) (a4) (n0) (n1) (n2) (n3) (n4) (p) (inv) (cnt) (z0) (z1) (z2) (z3)
      simp only [history3, heC, heQ, hoC, hoQ]
theorem run_stage3 (s : State) (c q0 q1 q2 q3 q4 a0 a1 a2 a3 a4 n0 n1 n2 n3 n4 p inv cnt z0 z1 z2 z3 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat)
    (hn0 : MachineState.readWord s.memory 160 = n0) (hi : MachineState.readWord s.memory 192 = inv)
    (hp : p = CycleSubmission.WordArithmetic.P)
    (ha0 : a0.toNat < 2^240) (ha1 : a1.toNat < 2^240) (ha2 : a2.toNat < 2^240) (ha3 : a3.toNat < 2^240)
    (hc : c.toNat < p.toNat) :
    runInstructions stage3Program {s with pc := N 4143, stack := (c) :: (q2) :: (q1) :: (q0) :: ((a0+a0)) :: ((a1+a1)) :: (a2) :: (a3) :: (a4) :: (n1) :: (n2) :: (n3) :: (n4) :: (p) :: (inv) :: (cnt) :: rest} = some (history3 (s) (c) (q0) (q1) (q2) (q3) (q4) (a0) (a1) (a2) (a3) (a4) (n0) (n1) (n2) (n3) (n4) (p) (inv) (cnt) (z0) (z1) (z2) (z3) (rest)) := by
  exact (stage3_run (s) (c) (q2) (q1) (q0) ((a0+a0)) ((a1+a1)) (a2) (a3) (a4) (n1) (n2) (n3) (n4) (p) (inv) (cnt) (rest) (hcap) (hact)).trans (congrArg some (stage3_history (s) (c) (q0) (q1) (q2) (q3) (q4) (a0) (a1) (a2) (a3) (a4) (n0) (n1) (n2) (n3) (n4) (p) (inv) (cnt) (z0) (z1) (z2) (z3) (rest) (hn0) (hi) (hp) (ha0) (ha1) (ha2) (ha3) (hc)))
def history4 (s : State) (c q0 q1 q2 q3 q4 a0 a1 a2 a3 a4 n0 n1 n2 n3 n4 p inv cnt z0 z1 z2 z3 : W) (rest : List W) : State := {s with pc := N 4298, stack := (CycleSubmission.R5.ExecSquare.sqCol4_o0 (c) (q3) (q2) (q1) (q0) (a0) (a1) (a2) (a3) (a4) (n1) (n2) (n3) (n4) (p) (inv) (cnt) (n0)) :: (q3) :: (q2) :: (q1) :: (CycleSubmission.R5.ExecSquare.sqCol4_o4 (c) (q3) (q2) (q1) (q0) (a0) (a1) (a2) (a3) (a4) (n1) (n2) (n3) (n4) (p) (inv) (cnt) (n0)) :: ((a0+a0)) :: ((a1+a1)) :: ((a2+a2)) :: (a3) :: (a4) :: (n1) :: (n2) :: (n3) :: (n4) :: (p) :: (inv) :: (cnt) :: rest}
theorem stage4_history (s : State) (c q0 q1 q2 q3 q4 a0 a1 a2 a3 a4 n0 n1 n2 n3 n4 p inv cnt z0 z1 z2 z3 : W) (rest : List W)
    (hn0 : MachineState.readWord s.memory 160 = n0) (hi : MachineState.readWord s.memory 192 = inv)
    (hp : p = CycleSubmission.WordArithmetic.P)
    (ha0 : a0.toNat < 2^240) (ha1 : a1.toNat < 2^240) (ha2 : a2.toNat < 2^240) (ha3 : a3.toNat < 2^240)
    (hc : c.toNat < p.toNat) :
    stage4Model (s) (c) (q3) (q2) (q1) (q0) ((a0+a0)) ((a1+a1)) (a2) (a3) (a4) (n1) (n2) (n3) (n4) (p) (inv) (cnt) (rest) = history4 (s) (c) (q0) (q1) (q2) (q3) (q4) (a0) (a1) (a2) (a3) (a4) (n0) (n1) (n2) (n3) (n4) (p) (inv) (cnt) (z0) (z1) (z2) (z3) (rest) := by
  calc
    stage4Model (s) (c) (q3) (q2) (q1) (q0) ((a0+a0)) ((a1+a1)) (a2) (a3) (a4) (n1) (n2) (n3) (n4) (p) (inv) (cnt) (rest) = {s with pc := N 4298, stack := (R5SharedMath4.cNew (c) (q0) (q1) (q2) (q3) (a0) (a1) (a2) (a3) (a4) (n0) (n1) (n2) (n3) (n4) (p) (inv)) :: (q3) :: (q2) :: (q1) :: (R5SharedMath4.qNew (c) (q0) (q1) (q2) (q3) (a0) (a1) (a2) (a3) (a4) (n0) (n1) (n2) (n3) (n4) (p) (inv)) :: ((a0+a0)) :: ((a1+a1)) :: ((a2+a2)) :: (a3) :: (a4) :: (n1) :: (n2) :: (n3) :: (n4) :: (p) :: (inv) :: (cnt) :: rest} := by
      simp only [stage4Model, R5SharedMath4.cNew, R5SharedMath4.qNew, R5SharedMath4.hiNew, R5SharedMath4.loNew, hn0, hi, List.foldr_cons, List.foldr_nil, word_add0, mask240_literal, addA, addL, addC, mulC, mmC, andC]
    _ = history4 (s) (c) (q0) (q1) (q2) (q3) (q4) (a0) (a1) (a2) (a3) (a4) (n0) (n1) (n2) (n3) (n4) (p) (inv) (cnt) (z0) (z1) (z2) (z3) (rest) := by
      have heC := R5SharedMath4.c_same (c) (q0) (q1) (q2) (q3) (a0) (a1) (a2) (a3) (a4) (n0) (n1) (n2) (n3) (n4) (p) (inv) (ha0) (ha1) (hp) (hc)
      have heQ := R5SharedMath4.q_same (c) (q0) (q1) (q2) (q3) (a0) (a1) (a2) (a3) (a4) (n0) (n1) (n2) (n3) (n4) (p) (inv)
      have hoC := R5SharedMath4.old_c_matches (c) (q0) (q1) (q2) (q3) (q4) (a0) (a1) (a2) (a3) (a4) (n0) (n1) (n2) (n3) (n4) (p) (inv) (cnt) (z0) (z1) (z2) (z3)
      have hoQ := R5SharedMath4.old_q_matches (c) (q0) (q1) (q2) (q3) (q4) (a0) (a1) (a2) (a3) (a4) (n0) (n1) (n2) (n3) (n4) (p) (inv) (cnt) (z0) (z1) (z2) (z3)
      simp only [history4, heC, heQ, hoC, hoQ]
theorem run_stage4 (s : State) (c q0 q1 q2 q3 q4 a0 a1 a2 a3 a4 n0 n1 n2 n3 n4 p inv cnt z0 z1 z2 z3 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat)
    (hn0 : MachineState.readWord s.memory 160 = n0) (hi : MachineState.readWord s.memory 192 = inv)
    (hp : p = CycleSubmission.WordArithmetic.P)
    (ha0 : a0.toNat < 2^240) (ha1 : a1.toNat < 2^240) (ha2 : a2.toNat < 2^240) (ha3 : a3.toNat < 2^240)
    (hc : c.toNat < p.toNat) :
    runInstructions stage4Program {s with pc := N 4208, stack := (c) :: (q3) :: (q2) :: (q1) :: (q0) :: ((a0+a0)) :: ((a1+a1)) :: (a2) :: (a3) :: (a4) :: (n1) :: (n2) :: (n3) :: (n4) :: (p) :: (inv) :: (cnt) :: rest} = some (history4 (s) (c) (q0) (q1) (q2) (q3) (q4) (a0) (a1) (a2) (a3) (a4) (n0) (n1) (n2) (n3) (n4) (p) (inv) (cnt) (z0) (z1) (z2) (z3) (rest)) := by
  exact (stage4_run (s) (c) (q3) (q2) (q1) (q0) ((a0+a0)) ((a1+a1)) (a2) (a3) (a4) (n1) (n2) (n3) (n4) (p) (inv) (cnt) (rest) (hcap) (hact)).trans (congrArg some (stage4_history (s) (c) (q0) (q1) (q2) (q3) (q4) (a0) (a1) (a2) (a3) (a4) (n0) (n1) (n2) (n3) (n4) (p) (inv) (cnt) (z0) (z1) (z2) (z3) (rest) (hn0) (hi) (hp) (ha0) (ha1) (ha2) (ha3) (hc)))
def history5 (s : State) (c q0 q1 q2 q3 q4 a0 a1 a2 a3 a4 n0 n1 n2 n3 n4 p inv cnt z0 z1 z2 z3 : W) (rest : List W) : State := {s with pc := N 4400, stack := (CycleSubmission.R5.ExecSquare.sqCol5_o0 (c) (q3) (q2) (q1) (q4) (a0) (a1) (a2) (a3) (a4) (n1) (n2) (n3) (n4) (p) (inv) (cnt)) :: (q3) :: (q2) :: (q1) :: (q4) :: (CycleSubmission.R5.ExecSquare.sqCol5_o5 (c) (q3) (q2) (q1) (q4) (a0) (a1) (a2) (a3) (a4) (n1) (n2) (n3) (n4) (p) (inv) (cnt)) :: ((a1+a1)) :: ((a2+a2)) :: (a3) :: (a4) :: (n1) :: (n2) :: (n3) :: (n4) :: (p) :: (inv) :: (cnt) :: rest}
theorem stage5_history (s : State) (c q0 q1 q2 q3 q4 a0 a1 a2 a3 a4 n0 n1 n2 n3 n4 p inv cnt z0 z1 z2 z3 : W) (rest : List W)
    (hn0 : MachineState.readWord s.memory 160 = n0) (hi : MachineState.readWord s.memory 192 = inv)
    (hp : p = CycleSubmission.WordArithmetic.P)
    (ha0 : a0.toNat < 2^240) (ha1 : a1.toNat < 2^240) (ha2 : a2.toNat < 2^240) (ha3 : a3.toNat < 2^240)
    (hc : c.toNat < p.toNat) :
    stage5Model (s) (c) (q3) (q2) (q1) (q4) ((a0+a0)) ((a1+a1)) ((a2+a2)) (a3) (a4) (n1) (n2) (n3) (n4) (p) (inv) (cnt) (rest) = history5 (s) (c) (q0) (q1) (q2) (q3) (q4) (a0) (a1) (a2) (a3) (a4) (n0) (n1) (n2) (n3) (n4) (p) (inv) (cnt) (z0) (z1) (z2) (z3) (rest) := by
  calc
    stage5Model (s) (c) (q3) (q2) (q1) (q4) ((a0+a0)) ((a1+a1)) ((a2+a2)) (a3) (a4) (n1) (n2) (n3) (n4) (p) (inv) (cnt) (rest) = {s with pc := N 4400, stack := (R5SharedMath5.cNew (c) (q1) (q2) (q3) (q4) (a1) (a2) (a3) (a4) (n1) (n2) (n3) (n4) (p)) :: (q3) :: (q2) :: (q1) :: (q4) :: (R5SharedMath5.qNew (c) (q1) (q2) (q3) (q4) (a1) (a2) (a3) (a4) (n1) (n2) (n3) (n4) (p)) :: ((a1+a1)) :: ((a2+a2)) :: (a3) :: (a4) :: (n1) :: (n2) :: (n3) :: (n4) :: (p) :: (inv) :: (cnt) :: rest} := by
      simp only [stage5Model, R5SharedMath5.cNew, R5SharedMath5.qNew, R5SharedMath5.hiNew, R5SharedMath5.loNew, hn0, hi, List.foldr_cons, List.foldr_nil, word_add0, mask240_literal, addA, addL, addC, mulC, mmC, andC]
    _ = history5 (s) (c) (q0) (q1) (q2) (q3) (q4) (a0) (a1) (a2) (a3) (a4) (n0) (n1) (n2) (n3) (n4) (p) (inv) (cnt) (z0) (z1) (z2) (z3) (rest) := by
      have heC := R5SharedMath5.c_same (c) (q1) (q2) (q3) (q4) (a1) (a2) (a3) (a4) (n1) (n2) (n3) (n4) (p) (ha1) (ha2) (hp) (hc)
      have heQ := R5SharedMath5.q_same (c) (q1) (q2) (q3) (q4) (a1) (a2) (a3) (a4) (n1) (n2) (n3) (n4) (p)
      have hoC := R5SharedMath5.old_c_matches (c) (q0) (q1) (q2) (q3) (q4) (a0) (a1) (a2) (a3) (a4) (n0) (n1) (n2) (n3) (n4) (p) (inv) (cnt) (z0) (z1) (z2) (z3)
      have hoQ := R5SharedMath5.old_q_matches (c) (q0) (q1) (q2) (q3) (q4) (a0) (a1) (a2) (a3) (a4) (n0) (n1) (n2) (n3) (n4) (p) (inv) (cnt) (z0) (z1) (z2) (z3)
      simp only [history5, heC, heQ, hoC, hoQ]
theorem run_stage5 (s : State) (c q0 q1 q2 q3 q4 a0 a1 a2 a3 a4 n0 n1 n2 n3 n4 p inv cnt z0 z1 z2 z3 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat)
    (hn0 : MachineState.readWord s.memory 160 = n0) (hi : MachineState.readWord s.memory 192 = inv)
    (hp : p = CycleSubmission.WordArithmetic.P)
    (ha0 : a0.toNat < 2^240) (ha1 : a1.toNat < 2^240) (ha2 : a2.toNat < 2^240) (ha3 : a3.toNat < 2^240)
    (hc : c.toNat < p.toNat) :
    runInstructions stage5Program {s with pc := N 4298, stack := (c) :: (q3) :: (q2) :: (q1) :: (q4) :: ((a0+a0)) :: ((a1+a1)) :: ((a2+a2)) :: (a3) :: (a4) :: (n1) :: (n2) :: (n3) :: (n4) :: (p) :: (inv) :: (cnt) :: rest} = some (history5 (s) (c) (q0) (q1) (q2) (q3) (q4) (a0) (a1) (a2) (a3) (a4) (n0) (n1) (n2) (n3) (n4) (p) (inv) (cnt) (z0) (z1) (z2) (z3) (rest)) := by
  exact (stage5_run (s) (c) (q3) (q2) (q1) (q4) ((a0+a0)) ((a1+a1)) ((a2+a2)) (a3) (a4) (n1) (n2) (n3) (n4) (p) (inv) (cnt) (rest) (hcap) (hact)).trans (congrArg some (stage5_history (s) (c) (q0) (q1) (q2) (q3) (q4) (a0) (a1) (a2) (a3) (a4) (n0) (n1) (n2) (n3) (n4) (p) (inv) (cnt) (z0) (z1) (z2) (z3) (rest) (hn0) (hi) (hp) (ha0) (ha1) (ha2) (ha3) (hc)))
def history6 (s : State) (c q0 q1 q2 q3 q4 a0 a1 a2 a3 a4 n0 n1 n2 n3 n4 p inv cnt z0 z1 z2 z3 : W) (rest : List W) : State := {s with pc := N 4495, stack := (CycleSubmission.R5.ExecSquare.sqCol6_o0 (c) (q3) (q2) (q1) (q4) (z0) (a1) (a2) (a3) (a4) (n1) (n2) (n3) (n4) (p) (inv) (cnt)) :: (q3) :: (q2) :: (q1) :: (q4) :: (z0) :: (CycleSubmission.R5.ExecSquare.sqCol6_o6 (c) (q3) (q2) (q1) (q4) (z0) (a1) (a2) (a3) (a4) (n1) (n2) (n3) (n4) (p) (inv) (cnt)) :: ((a2+a2)) :: ((a3+a3)) :: (a4) :: (n1) :: (n2) :: (n3) :: (n4) :: (p) :: (inv) :: (cnt) :: rest}
theorem stage6_history (s : State) (c q0 q1 q2 q3 q4 a0 a1 a2 a3 a4 n0 n1 n2 n3 n4 p inv cnt z0 z1 z2 z3 : W) (rest : List W)
    (hn0 : MachineState.readWord s.memory 160 = n0) (hi : MachineState.readWord s.memory 192 = inv)
    (hp : p = CycleSubmission.WordArithmetic.P)
    (ha0 : a0.toNat < 2^240) (ha1 : a1.toNat < 2^240) (ha2 : a2.toNat < 2^240) (ha3 : a3.toNat < 2^240)
    (hc : c.toNat < p.toNat) :
    stage6Model (s) (c) (q3) (q2) (q1) (q4) (z0) ((a1+a1)) ((a2+a2)) (a3) (a4) (n1) (n2) (n3) (n4) (p) (inv) (cnt) (rest) = history6 (s) (c) (q0) (q1) (q2) (q3) (q4) (a0) (a1) (a2) (a3) (a4) (n0) (n1) (n2) (n3) (n4) (p) (inv) (cnt) (z0) (z1) (z2) (z3) (rest) := by
  calc
    stage6Model (s) (c) (q3) (q2) (q1) (q4) (z0) ((a1+a1)) ((a2+a2)) (a3) (a4) (n1) (n2) (n3) (n4) (p) (inv) (cnt) (rest) = {s with pc := N 4495, stack := (R5SharedMath6.cNew (c) (q2) (q3) (q4) (a2) (a3) (a4) (n2) (n3) (n4) (p)) :: (q3) :: (q2) :: (q1) :: (q4) :: (z0) :: (R5SharedMath6.qNew (c) (q2) (q3) (q4) (a2) (a3) (a4) (n2) (n3) (n4) (p)) :: ((a2+a2)) :: ((a3+a3)) :: (a4) :: (n1) :: (n2) :: (n3) :: (n4) :: (p) :: (inv) :: (cnt) :: rest} := by
      simp only [stage6Model, R5SharedMath6.cNew, R5SharedMath6.qNew, R5SharedMath6.hiNew, R5SharedMath6.loNew, hn0, hi, List.foldr_cons, List.foldr_nil, word_add0, mask240_literal, addA, addL, addC, mulC, mmC, andC]
    _ = history6 (s) (c) (q0) (q1) (q2) (q3) (q4) (a0) (a1) (a2) (a3) (a4) (n0) (n1) (n2) (n3) (n4) (p) (inv) (cnt) (z0) (z1) (z2) (z3) (rest) := by
      have heC := R5SharedMath6.c_same (c) (q2) (q3) (q4) (a2) (a3) (a4) (n2) (n3) (n4) (p) (ha2) (hp) (hc)
      have heQ := R5SharedMath6.q_same (c) (q2) (q3) (q4) (a2) (a3) (a4) (n2) (n3) (n4) (p)
      have hoC := R5SharedMath6.old_c_matches (c) (q0) (q1) (q2) (q3) (q4) (a0) (a1) (a2) (a3) (a4) (n0) (n1) (n2) (n3) (n4) (p) (inv) (cnt) (z0) (z1) (z2) (z3)
      have hoQ := R5SharedMath6.old_q_matches (c) (q0) (q1) (q2) (q3) (q4) (a0) (a1) (a2) (a3) (a4) (n0) (n1) (n2) (n3) (n4) (p) (inv) (cnt) (z0) (z1) (z2) (z3)
      simp only [history6, heC, heQ, hoC, hoQ]
theorem run_stage6 (s : State) (c q0 q1 q2 q3 q4 a0 a1 a2 a3 a4 n0 n1 n2 n3 n4 p inv cnt z0 z1 z2 z3 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat)
    (hn0 : MachineState.readWord s.memory 160 = n0) (hi : MachineState.readWord s.memory 192 = inv)
    (hp : p = CycleSubmission.WordArithmetic.P)
    (ha0 : a0.toNat < 2^240) (ha1 : a1.toNat < 2^240) (ha2 : a2.toNat < 2^240) (ha3 : a3.toNat < 2^240)
    (hc : c.toNat < p.toNat) :
    runInstructions stage6Program {s with pc := N 4400, stack := (c) :: (q3) :: (q2) :: (q1) :: (q4) :: (z0) :: ((a1+a1)) :: ((a2+a2)) :: (a3) :: (a4) :: (n1) :: (n2) :: (n3) :: (n4) :: (p) :: (inv) :: (cnt) :: rest} = some (history6 (s) (c) (q0) (q1) (q2) (q3) (q4) (a0) (a1) (a2) (a3) (a4) (n0) (n1) (n2) (n3) (n4) (p) (inv) (cnt) (z0) (z1) (z2) (z3) (rest)) := by
  exact (stage6_run (s) (c) (q3) (q2) (q1) (q4) (z0) ((a1+a1)) ((a2+a2)) (a3) (a4) (n1) (n2) (n3) (n4) (p) (inv) (cnt) (rest) (hcap) (hact)).trans (congrArg some (stage6_history (s) (c) (q0) (q1) (q2) (q3) (q4) (a0) (a1) (a2) (a3) (a4) (n0) (n1) (n2) (n3) (n4) (p) (inv) (cnt) (z0) (z1) (z2) (z3) (rest) (hn0) (hi) (hp) (ha0) (ha1) (ha2) (ha3) (hc)))
def history7 (s : State) (c q0 q1 q2 q3 q4 a0 a1 a2 a3 a4 n0 n1 n2 n3 n4 p inv cnt z0 z1 z2 z3 : W) (rest : List W) : State := {s with pc := N 4567, stack := (CycleSubmission.R5.ExecSquare.sqCol7_o0 (c) (q3) (q2) (q1) (q4) (z0) (z1) (a2) (a3) (a4) (n1) (n2) (n3) (n4) (p) (inv) (cnt)) :: (q3) :: (q2) :: (q1) :: (q4) :: (z0) :: (z1) :: (CycleSubmission.R5.ExecSquare.sqCol7_o7 (c) (q3) (q2) (q1) (q4) (z0) (z1) (a2) (a3) (a4) (n1) (n2) (n3) (n4) (p) (inv) (cnt)) :: ((a3+a3)) :: (a4) :: (n1) :: (n2) :: (n3) :: (n4) :: (p) :: (inv) :: (cnt) :: rest}
theorem stage7_history (s : State) (c q0 q1 q2 q3 q4 a0 a1 a2 a3 a4 n0 n1 n2 n3 n4 p inv cnt z0 z1 z2 z3 : W) (rest : List W)
    (hn0 : MachineState.readWord s.memory 160 = n0) (hi : MachineState.readWord s.memory 192 = inv)
    (hp : p = CycleSubmission.WordArithmetic.P)
    (ha0 : a0.toNat < 2^240) (ha1 : a1.toNat < 2^240) (ha2 : a2.toNat < 2^240) (ha3 : a3.toNat < 2^240)
    (hc : c.toNat < p.toNat) :
    stage7Model (s) (c) (q3) (q2) (q1) (q4) (z0) (z1) ((a2+a2)) ((a3+a3)) (a4) (n1) (n2) (n3) (n4) (p) (inv) (cnt) (rest) = history7 (s) (c) (q0) (q1) (q2) (q3) (q4) (a0) (a1) (a2) (a3) (a4) (n0) (n1) (n2) (n3) (n4) (p) (inv) (cnt) (z0) (z1) (z2) (z3) (rest) := by
  calc
    stage7Model (s) (c) (q3) (q2) (q1) (q4) (z0) (z1) ((a2+a2)) ((a3+a3)) (a4) (n1) (n2) (n3) (n4) (p) (inv) (cnt) (rest) = {s with pc := N 4567, stack := (R5SharedMath7.cNew (c) (q3) (q4) (a3) (a4) (n3) (n4) (p)) :: (q3) :: (q2) :: (q1) :: (q4) :: (z0) :: (z1) :: (R5SharedMath7.qNew (c) (q3) (q4) (a3) (a4) (n3) (n4) (p)) :: ((a3+a3)) :: (a4) :: (n1) :: (n2) :: (n3) :: (n4) :: (p) :: (inv) :: (cnt) :: rest} := by
      simp only [stage7Model, R5SharedMath7.cNew, R5SharedMath7.qNew, R5SharedMath7.hiNew, R5SharedMath7.loNew, hn0, hi, List.foldr_cons, List.foldr_nil, word_add0, mask240_literal, addA, addL, addC, mulC, mmC, andC]
    _ = history7 (s) (c) (q0) (q1) (q2) (q3) (q4) (a0) (a1) (a2) (a3) (a4) (n0) (n1) (n2) (n3) (n4) (p) (inv) (cnt) (z0) (z1) (z2) (z3) (rest) := by
      have heC := R5SharedMath7.c_same (c) (q3) (q4) (a3) (a4) (n3) (n4) (p) (ha3) (hp) (hc)
      have heQ := R5SharedMath7.q_same (c) (q3) (q4) (a3) (a4) (n3) (n4) (p)
      have hoC := R5SharedMath7.old_c_matches (c) (q0) (q1) (q2) (q3) (q4) (a0) (a1) (a2) (a3) (a4) (n0) (n1) (n2) (n3) (n4) (p) (inv) (cnt) (z0) (z1) (z2) (z3)
      have hoQ := R5SharedMath7.old_q_matches (c) (q0) (q1) (q2) (q3) (q4) (a0) (a1) (a2) (a3) (a4) (n0) (n1) (n2) (n3) (n4) (p) (inv) (cnt) (z0) (z1) (z2) (z3)
      simp only [history7, heC, heQ, hoC, hoQ]
theorem run_stage7 (s : State) (c q0 q1 q2 q3 q4 a0 a1 a2 a3 a4 n0 n1 n2 n3 n4 p inv cnt z0 z1 z2 z3 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat)
    (hn0 : MachineState.readWord s.memory 160 = n0) (hi : MachineState.readWord s.memory 192 = inv)
    (hp : p = CycleSubmission.WordArithmetic.P)
    (ha0 : a0.toNat < 2^240) (ha1 : a1.toNat < 2^240) (ha2 : a2.toNat < 2^240) (ha3 : a3.toNat < 2^240)
    (hc : c.toNat < p.toNat) :
    runInstructions stage7Program {s with pc := N 4495, stack := (c) :: (q3) :: (q2) :: (q1) :: (q4) :: (z0) :: (z1) :: ((a2+a2)) :: ((a3+a3)) :: (a4) :: (n1) :: (n2) :: (n3) :: (n4) :: (p) :: (inv) :: (cnt) :: rest} = some (history7 (s) (c) (q0) (q1) (q2) (q3) (q4) (a0) (a1) (a2) (a3) (a4) (n0) (n1) (n2) (n3) (n4) (p) (inv) (cnt) (z0) (z1) (z2) (z3) (rest)) := by
  exact (stage7_run (s) (c) (q3) (q2) (q1) (q4) (z0) (z1) ((a2+a2)) ((a3+a3)) (a4) (n1) (n2) (n3) (n4) (p) (inv) (cnt) (rest) (hcap) (hact)).trans (congrArg some (stage7_history (s) (c) (q0) (q1) (q2) (q3) (q4) (a0) (a1) (a2) (a3) (a4) (n0) (n1) (n2) (n3) (n4) (p) (inv) (cnt) (z0) (z1) (z2) (z3) (rest) (hn0) (hi) (hp) (ha0) (ha1) (ha2) (ha3) (hc)))
def history8 (s : State) (c q0 q1 q2 q3 q4 a0 a1 a2 a3 a4 n0 n1 n2 n3 n4 p inv cnt z0 z1 z2 z3 : W) (rest : List W) : State := {s with pc := N 4630, stack := (CycleSubmission.R5.ExecSquare.sqCol8_o0 (c) (q3) (q2) (q1) (q4) (z0) (z1) (z2) (a3) (a4) (n1) (n2) (n3) (n4) (p) (inv) (cnt)) :: (q3) :: (q2) :: (q1) :: (q4) :: (z0) :: (z1) :: (z2) :: (CycleSubmission.R5.ExecSquare.sqCol8_o8 (c) (q3) (q2) (q1) (q4) (z0) (z1) (z2) (a3) (a4) (n1) (n2) (n3) (n4) (p) (inv) (cnt)) :: (a4) :: (n1) :: (n2) :: (n3) :: (n4) :: (p) :: (inv) :: (cnt) :: rest}
theorem stage8_history (s : State) (c q0 q1 q2 q3 q4 a0 a1 a2 a3 a4 n0 n1 n2 n3 n4 p inv cnt z0 z1 z2 z3 : W) (rest : List W)
    (hn0 : MachineState.readWord s.memory 160 = n0) (hi : MachineState.readWord s.memory 192 = inv)
    (hp : p = CycleSubmission.WordArithmetic.P)
    (ha0 : a0.toNat < 2^240) (ha1 : a1.toNat < 2^240) (ha2 : a2.toNat < 2^240) (ha3 : a3.toNat < 2^240)
    (hc : c.toNat < p.toNat) :
    stage8Model (s) (c) (q3) (q2) (q1) (q4) (z0) (z1) (z2) ((a3+a3)) (a4) (n1) (n2) (n3) (n4) (p) (inv) (cnt) (rest) = history8 (s) (c) (q0) (q1) (q2) (q3) (q4) (a0) (a1) (a2) (a3) (a4) (n0) (n1) (n2) (n3) (n4) (p) (inv) (cnt) (z0) (z1) (z2) (z3) (rest) := by
  simp only [stage8Model, history8, hn0, hi, word_add0, mask240_literal, addA, addL, addC, mulC, mmC, andC, CycleSubmission.R5.ExecSquare.sqCol8_o0, CycleSubmission.R5.ExecSquare.sqCol8_o8]
theorem run_stage8 (s : State) (c q0 q1 q2 q3 q4 a0 a1 a2 a3 a4 n0 n1 n2 n3 n4 p inv cnt z0 z1 z2 z3 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat)
    (hn0 : MachineState.readWord s.memory 160 = n0) (hi : MachineState.readWord s.memory 192 = inv)
    (hp : p = CycleSubmission.WordArithmetic.P)
    (ha0 : a0.toNat < 2^240) (ha1 : a1.toNat < 2^240) (ha2 : a2.toNat < 2^240) (ha3 : a3.toNat < 2^240)
    (hc : c.toNat < p.toNat) :
    runInstructions stage8Program {s with pc := N 4567, stack := (c) :: (q3) :: (q2) :: (q1) :: (q4) :: (z0) :: (z1) :: (z2) :: ((a3+a3)) :: (a4) :: (n1) :: (n2) :: (n3) :: (n4) :: (p) :: (inv) :: (cnt) :: rest} = some (history8 (s) (c) (q0) (q1) (q2) (q3) (q4) (a0) (a1) (a2) (a3) (a4) (n0) (n1) (n2) (n3) (n4) (p) (inv) (cnt) (z0) (z1) (z2) (z3) (rest)) := by
  exact (stage8_run (s) (c) (q3) (q2) (q1) (q4) (z0) (z1) (z2) ((a3+a3)) (a4) (n1) (n2) (n3) (n4) (p) (inv) (cnt) (rest) (hcap) (hact)).trans (congrArg some (stage8_history (s) (c) (q0) (q1) (q2) (q3) (q4) (a0) (a1) (a2) (a3) (a4) (n0) (n1) (n2) (n3) (n4) (p) (inv) (cnt) (z0) (z1) (z2) (z3) (rest) (hn0) (hi) (hp) (ha0) (ha1) (ha2) (ha3) (hc)))
def history9 (s : State) (c q0 q1 q2 q3 q4 a0 a1 a2 a3 a4 n0 n1 n2 n3 n4 p inv cnt z0 z1 z2 z3 : W) (rest : List W) : State := {s with pc := N 4641, stack := (cnt) :: (z0) :: (z1) :: (z2) :: (z3) :: (c) :: (n1) :: (n2) :: (n3) :: (n4) :: (p) :: (inv) :: (cnt-N 1) :: rest}
theorem stage9_history (s : State) (c q0 q1 q2 q3 q4 a0 a1 a2 a3 a4 n0 n1 n2 n3 n4 p inv cnt z0 z1 z2 z3 : W) (rest : List W)
    (hn0 : MachineState.readWord s.memory 160 = n0) (hi : MachineState.readWord s.memory 192 = inv)
    (hp : p = CycleSubmission.WordArithmetic.P)
    (ha0 : a0.toNat < 2^240) (ha1 : a1.toNat < 2^240) (ha2 : a2.toNat < 2^240) (ha3 : a3.toNat < 2^240)
    (hc : c.toNat < p.toNat) :
    stage9Model (s) (c) (q3) (q2) (q1) (q4) (z0) (z1) (z2) (z3) (a4) (n1) (n2) (n3) (n4) (p) (inv) (cnt) (rest) = history9 (s) (c) (q0) (q1) (q2) (q3) (q4) (a0) (a1) (a2) (a3) (a4) (n0) (n1) (n2) (n3) (n4) (p) (inv) (cnt) (z0) (z1) (z2) (z3) (rest) := by
  simp only [stage9Model, history9, hn0, hi, word_add0, mask240_literal, addA, addL, addC, mulC, mmC, andC]
theorem run_stage9 (s : State) (c q0 q1 q2 q3 q4 a0 a1 a2 a3 a4 n0 n1 n2 n3 n4 p inv cnt z0 z1 z2 z3 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat)
    (hn0 : MachineState.readWord s.memory 160 = n0) (hi : MachineState.readWord s.memory 192 = inv)
    (hp : p = CycleSubmission.WordArithmetic.P)
    (ha0 : a0.toNat < 2^240) (ha1 : a1.toNat < 2^240) (ha2 : a2.toNat < 2^240) (ha3 : a3.toNat < 2^240)
    (hc : c.toNat < p.toNat) :
    runInstructions stage9Program {s with pc := N 4630, stack := (c) :: (q3) :: (q2) :: (q1) :: (q4) :: (z0) :: (z1) :: (z2) :: (z3) :: (a4) :: (n1) :: (n2) :: (n3) :: (n4) :: (p) :: (inv) :: (cnt) :: rest} = some (history9 (s) (c) (q0) (q1) (q2) (q3) (q4) (a0) (a1) (a2) (a3) (a4) (n0) (n1) (n2) (n3) (n4) (p) (inv) (cnt) (z0) (z1) (z2) (z3) (rest)) := by
  exact (stage9_run (s) (c) (q3) (q2) (q1) (q4) (z0) (z1) (z2) (z3) (a4) (n1) (n2) (n3) (n4) (p) (inv) (cnt) (rest) (hcap) (hact)).trans (congrArg some (stage9_history (s) (c) (q0) (q1) (q2) (q3) (q4) (a0) (a1) (a2) (a3) (a4) (n0) (n1) (n2) (n3) (n4) (p) (inv) (cnt) (z0) (z1) (z2) (z3) (rest) (hn0) (hi) (hp) (ha0) (ha1) (ha2) (ha3) (hc)))
end NextR5Columns

namespace CycleSubmission.R5.SquareRun
open EvmSemantics CycleSubmission.R5.ExecSquare
def sqV0_0 (a0 a1 a2 a3 a4 n1 n2 n3 n4 P inv cnt n0 : UInt256) : UInt256 :=
  sqCol0_o0 a0 a1 a2 a3 a4 n1 n2 n3 n4 P inv cnt n0

def sqV0_1 (a0 a1 a2 a3 a4 n1 n2 n3 n4 P inv cnt n0 : UInt256) : UInt256 :=
  sqCol0_o1 a0 a1 a2 a3 a4 n1 n2 n3 n4 P inv cnt n0

def sqV1_0 (a0 a1 a2 a3 a4 n1 n2 n3 n4 P inv cnt n0 : UInt256) : UInt256 :=
  sqCol1_o0 ((sqV0_0 a0 a1 a2 a3 a4 n1 n2 n3 n4 P inv cnt n0)) ((sqV0_1 a0 a1 a2 a3 a4 n1 n2 n3 n4 P inv cnt n0)) a0 a1 a2 a3 a4 n1 n2 n3 n4 P inv cnt n0

def sqV1_1 (a0 a1 a2 a3 a4 n1 n2 n3 n4 P inv cnt n0 : UInt256) : UInt256 :=
  sqCol1_o1 ((sqV0_0 a0 a1 a2 a3 a4 n1 n2 n3 n4 P inv cnt n0)) ((sqV0_1 a0 a1 a2 a3 a4 n1 n2 n3 n4 P inv cnt n0)) a0 a1 a2 a3 a4 n1 n2 n3 n4 P inv cnt n0

def sqV2_0 (a0 a1 a2 a3 a4 n1 n2 n3 n4 P inv cnt n0 : UInt256) : UInt256 :=
  sqCol2_o0 ((sqV1_0 a0 a1 a2 a3 a4 n1 n2 n3 n4 P inv cnt n0)) ((sqV1_1 a0 a1 a2 a3 a4 n1 n2 n3 n4 P inv cnt n0)) ((sqV0_1 a0 a1 a2 a3 a4 n1 n2 n3 n4 P inv cnt n0)) a0 a1 a2 a3 a4 n1 n2 n3 n4 P inv cnt n0

def sqV2_1 (a0 a1 a2 a3 a4 n1 n2 n3 n4 P inv cnt n0 : UInt256) : UInt256 :=
  sqCol2_o1 ((sqV1_0 a0 a1 a2 a3 a4 n1 n2 n3 n4 P inv cnt n0)) ((sqV1_1 a0 a1 a2 a3 a4 n1 n2 n3 n4 P inv cnt n0)) ((sqV0_1 a0 a1 a2 a3 a4 n1 n2 n3 n4 P inv cnt n0)) a0 a1 a2 a3 a4 n1 n2 n3 n4 P inv cnt n0

def sqV3_0 (a0 a1 a2 a3 a4 n1 n2 n3 n4 P inv cnt n0 : UInt256) : UInt256 :=
  sqCol3_o0 ((sqV2_0 a0 a1 a2 a3 a4 n1 n2 n3 n4 P inv cnt n0)) ((sqV2_1 a0 a1 a2 a3 a4 n1 n2 n3 n4 P inv cnt n0)) ((sqV1_1 a0 a1 a2 a3 a4 n1 n2 n3 n4 P inv cnt n0)) ((sqV0_1 a0 a1 a2 a3 a4 n1 n2 n3 n4 P inv cnt n0)) a0 a1 a2 a3 a4 n1 n2 n3 n4 P inv cnt n0

def sqV3_1 (a0 a1 a2 a3 a4 n1 n2 n3 n4 P inv cnt n0 : UInt256) : UInt256 :=
  sqCol3_o1 ((sqV2_0 a0 a1 a2 a3 a4 n1 n2 n3 n4 P inv cnt n0)) ((sqV2_1 a0 a1 a2 a3 a4 n1 n2 n3 n4 P inv cnt n0)) ((sqV1_1 a0 a1 a2 a3 a4 n1 n2 n3 n4 P inv cnt n0)) ((sqV0_1 a0 a1 a2 a3 a4 n1 n2 n3 n4 P inv cnt n0)) a0 a1 a2 a3 a4 n1 n2 n3 n4 P inv cnt n0

def sqV4_0 (a0 a1 a2 a3 a4 n1 n2 n3 n4 P inv cnt n0 : UInt256) : UInt256 :=
  sqCol4_o0 ((sqV3_0 a0 a1 a2 a3 a4 n1 n2 n3 n4 P inv cnt n0)) ((sqV3_1 a0 a1 a2 a3 a4 n1 n2 n3 n4 P inv cnt n0)) ((sqV2_1 a0 a1 a2 a3 a4 n1 n2 n3 n4 P inv cnt n0)) ((sqV1_1 a0 a1 a2 a3 a4 n1 n2 n3 n4 P inv cnt n0)) ((sqV0_1 a0 a1 a2 a3 a4 n1 n2 n3 n4 P inv cnt n0)) a0 a1 a2 a3 a4 n1 n2 n3 n4 P inv cnt n0

def sqV4_4 (a0 a1 a2 a3 a4 n1 n2 n3 n4 P inv cnt n0 : UInt256) : UInt256 :=
  sqCol4_o4 ((sqV3_0 a0 a1 a2 a3 a4 n1 n2 n3 n4 P inv cnt n0)) ((sqV3_1 a0 a1 a2 a3 a4 n1 n2 n3 n4 P inv cnt n0)) ((sqV2_1 a0 a1 a2 a3 a4 n1 n2 n3 n4 P inv cnt n0)) ((sqV1_1 a0 a1 a2 a3 a4 n1 n2 n3 n4 P inv cnt n0)) ((sqV0_1 a0 a1 a2 a3 a4 n1 n2 n3 n4 P inv cnt n0)) a0 a1 a2 a3 a4 n1 n2 n3 n4 P inv cnt n0

def sqV5_0 (a0 a1 a2 a3 a4 n1 n2 n3 n4 P inv cnt n0 : UInt256) : UInt256 :=
  sqCol5_o0 ((sqV4_0 a0 a1 a2 a3 a4 n1 n2 n3 n4 P inv cnt n0)) ((sqV3_1 a0 a1 a2 a3 a4 n1 n2 n3 n4 P inv cnt n0)) ((sqV2_1 a0 a1 a2 a3 a4 n1 n2 n3 n4 P inv cnt n0)) ((sqV1_1 a0 a1 a2 a3 a4 n1 n2 n3 n4 P inv cnt n0)) ((sqV4_4 a0 a1 a2 a3 a4 n1 n2 n3 n4 P inv cnt n0)) a0 a1 a2 a3 a4 n1 n2 n3 n4 P inv cnt

def sqV5_5 (a0 a1 a2 a3 a4 n1 n2 n3 n4 P inv cnt n0 : UInt256) : UInt256 :=
  sqCol5_o5 ((sqV4_0 a0 a1 a2 a3 a4 n1 n2 n3 n4 P inv cnt n0)) ((sqV3_1 a0 a1 a2 a3 a4 n1 n2 n3 n4 P inv cnt n0)) ((sqV2_1 a0 a1 a2 a3 a4 n1 n2 n3 n4 P inv cnt n0)) ((sqV1_1 a0 a1 a2 a3 a4 n1 n2 n3 n4 P inv cnt n0)) ((sqV4_4 a0 a1 a2 a3 a4 n1 n2 n3 n4 P inv cnt n0)) a0 a1 a2 a3 a4 n1 n2 n3 n4 P inv cnt

def sqV6_0 (a0 a1 a2 a3 a4 n1 n2 n3 n4 P inv cnt n0 : UInt256) : UInt256 :=
  sqCol6_o0 ((sqV5_0 a0 a1 a2 a3 a4 n1 n2 n3 n4 P inv cnt n0)) ((sqV3_1 a0 a1 a2 a3 a4 n1 n2 n3 n4 P inv cnt n0)) ((sqV2_1 a0 a1 a2 a3 a4 n1 n2 n3 n4 P inv cnt n0)) ((sqV1_1 a0 a1 a2 a3 a4 n1 n2 n3 n4 P inv cnt n0)) ((sqV4_4 a0 a1 a2 a3 a4 n1 n2 n3 n4 P inv cnt n0)) ((sqV5_5 a0 a1 a2 a3 a4 n1 n2 n3 n4 P inv cnt n0)) a1 a2 a3 a4 n1 n2 n3 n4 P inv cnt

def sqV6_6 (a0 a1 a2 a3 a4 n1 n2 n3 n4 P inv cnt n0 : UInt256) : UInt256 :=
  sqCol6_o6 ((sqV5_0 a0 a1 a2 a3 a4 n1 n2 n3 n4 P inv cnt n0)) ((sqV3_1 a0 a1 a2 a3 a4 n1 n2 n3 n4 P inv cnt n0)) ((sqV2_1 a0 a1 a2 a3 a4 n1 n2 n3 n4 P inv cnt n0)) ((sqV1_1 a0 a1 a2 a3 a4 n1 n2 n3 n4 P inv cnt n0)) ((sqV4_4 a0 a1 a2 a3 a4 n1 n2 n3 n4 P inv cnt n0)) ((sqV5_5 a0 a1 a2 a3 a4 n1 n2 n3 n4 P inv cnt n0)) a1 a2 a3 a4 n1 n2 n3 n4 P inv cnt

def sqV7_0 (a0 a1 a2 a3 a4 n1 n2 n3 n4 P inv cnt n0 : UInt256) : UInt256 :=
  sqCol7_o0 ((sqV6_0 a0 a1 a2 a3 a4 n1 n2 n3 n4 P inv cnt n0)) ((sqV3_1 a0 a1 a2 a3 a4 n1 n2 n3 n4 P inv cnt n0)) ((sqV2_1 a0 a1 a2 a3 a4 n1 n2 n3 n4 P inv cnt n0)) ((sqV1_1 a0 a1 a2 a3 a4 n1 n2 n3 n4 P inv cnt n0)) ((sqV4_4 a0 a1 a2 a3 a4 n1 n2 n3 n4 P inv cnt n0)) ((sqV5_5 a0 a1 a2 a3 a4 n1 n2 n3 n4 P inv cnt n0)) ((sqV6_6 a0 a1 a2 a3 a4 n1 n2 n3 n4 P inv cnt n0)) a2 a3 a4 n1 n2 n3 n4 P inv cnt

def sqV7_7 (a0 a1 a2 a3 a4 n1 n2 n3 n4 P inv cnt n0 : UInt256) : UInt256 :=
  sqCol7_o7 ((sqV6_0 a0 a1 a2 a3 a4 n1 n2 n3 n4 P inv cnt n0)) ((sqV3_1 a0 a1 a2 a3 a4 n1 n2 n3 n4 P inv cnt n0)) ((sqV2_1 a0 a1 a2 a3 a4 n1 n2 n3 n4 P inv cnt n0)) ((sqV1_1 a0 a1 a2 a3 a4 n1 n2 n3 n4 P inv cnt n0)) ((sqV4_4 a0 a1 a2 a3 a4 n1 n2 n3 n4 P inv cnt n0)) ((sqV5_5 a0 a1 a2 a3 a4 n1 n2 n3 n4 P inv cnt n0)) ((sqV6_6 a0 a1 a2 a3 a4 n1 n2 n3 n4 P inv cnt n0)) a2 a3 a4 n1 n2 n3 n4 P inv cnt

def sqV8_0 (a0 a1 a2 a3 a4 n1 n2 n3 n4 P inv cnt n0 : UInt256) : UInt256 :=
  sqCol8_o0 ((sqV7_0 a0 a1 a2 a3 a4 n1 n2 n3 n4 P inv cnt n0)) ((sqV3_1 a0 a1 a2 a3 a4 n1 n2 n3 n4 P inv cnt n0)) ((sqV2_1 a0 a1 a2 a3 a4 n1 n2 n3 n4 P inv cnt n0)) ((sqV1_1 a0 a1 a2 a3 a4 n1 n2 n3 n4 P inv cnt n0)) ((sqV4_4 a0 a1 a2 a3 a4 n1 n2 n3 n4 P inv cnt n0)) ((sqV5_5 a0 a1 a2 a3 a4 n1 n2 n3 n4 P inv cnt n0)) ((sqV6_6 a0 a1 a2 a3 a4 n1 n2 n3 n4 P inv cnt n0)) ((sqV7_7 a0 a1 a2 a3 a4 n1 n2 n3 n4 P inv cnt n0)) a3 a4 n1 n2 n3 n4 P inv cnt

def sqV8_8 (a0 a1 a2 a3 a4 n1 n2 n3 n4 P inv cnt n0 : UInt256) : UInt256 :=
  sqCol8_o8 ((sqV7_0 a0 a1 a2 a3 a4 n1 n2 n3 n4 P inv cnt n0)) ((sqV3_1 a0 a1 a2 a3 a4 n1 n2 n3 n4 P inv cnt n0)) ((sqV2_1 a0 a1 a2 a3 a4 n1 n2 n3 n4 P inv cnt n0)) ((sqV1_1 a0 a1 a2 a3 a4 n1 n2 n3 n4 P inv cnt n0)) ((sqV4_4 a0 a1 a2 a3 a4 n1 n2 n3 n4 P inv cnt n0)) ((sqV5_5 a0 a1 a2 a3 a4 n1 n2 n3 n4 P inv cnt n0)) ((sqV6_6 a0 a1 a2 a3 a4 n1 n2 n3 n4 P inv cnt n0)) ((sqV7_7 a0 a1 a2 a3 a4 n1 n2 n3 n4 P inv cnt n0)) a3 a4 n1 n2 n3 n4 P inv cnt

def sqV9_12 (a0 a1 a2 a3 a4 n1 n2 n3 n4 P inv cnt n0 : UInt256) : UInt256 :=
  sqTail_o12 ((sqV8_0 a0 a1 a2 a3 a4 n1 n2 n3 n4 P inv cnt n0)) ((sqV3_1 a0 a1 a2 a3 a4 n1 n2 n3 n4 P inv cnt n0)) ((sqV2_1 a0 a1 a2 a3 a4 n1 n2 n3 n4 P inv cnt n0)) ((sqV1_1 a0 a1 a2 a3 a4 n1 n2 n3 n4 P inv cnt n0)) ((sqV4_4 a0 a1 a2 a3 a4 n1 n2 n3 n4 P inv cnt n0)) ((sqV5_5 a0 a1 a2 a3 a4 n1 n2 n3 n4 P inv cnt n0)) ((sqV6_6 a0 a1 a2 a3 a4 n1 n2 n3 n4 P inv cnt n0)) ((sqV7_7 a0 a1 a2 a3 a4 n1 n2 n3 n4 P inv cnt n0)) ((sqV8_8 a0 a1 a2 a3 a4 n1 n2 n3 n4 P inv cnt n0)) a4 n1 n2 n3 n4 P inv cnt


end CycleSubmission.R5.SquareRun

namespace CycleSubmission.Prepared.R5Square
open EvmSemantics EvmSemantics.EVM YulEvmCompiler
open Challenge.Modexp.Submission.Proofs.Bytecode.WindowNibbleKernel
open CycleSubmission.R5.SquareRun
def newProgram : List Instr := (NextR5Columns.stage0Program ++ (NextR5Columns.stage1Program ++ (NextR5Columns.stage2Program ++ (NextR5Columns.stage3Program ++ (NextR5Columns.stage4Program ++ (NextR5Columns.stage5Program ++ (NextR5Columns.stage6Program ++ (NextR5Columns.stage7Program ++ (NextR5Columns.stage8Program ++ (NextR5Columns.stage9Program))))))))))
theorem new_run (s : State) (a0 a1 a2 a3 a4 n1 n2 n3 n4 P inv cnt n0 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat)
    (hn0 : MachineState.readWord s.memory 160 = n0) (hi : MachineState.readWord s.memory 192 = inv)
    (hp : P = CycleSubmission.WordArithmetic.P)
    (ha0 : a0.toNat < 2^240) (ha1 : a1.toNat < 2^240) (ha2 : a2.toNat < 2^240) (ha3 : a3.toNat < 2^240) :
    runInstructions newProgram {s with pc := UInt256.ofNat 4018, stack := (a0) :: (a1) :: (a2) :: (a3) :: (a4) :: (n1) :: (n2) :: (n3) :: (n4) :: (P) :: (inv) :: (cnt) :: rest} = some {s with pc := UInt256.ofNat 4641, stack := (cnt) :: (sqV5_5 (a0) (a1) (a2) (a3) (a4) (n1) (n2) (n3) (n4) (P) (inv) (cnt) (n0)) :: (sqV6_6 (a0) (a1) (a2) (a3) (a4) (n1) (n2) (n3) (n4) (P) (inv) (cnt) (n0)) :: (sqV7_7 (a0) (a1) (a2) (a3) (a4) (n1) (n2) (n3) (n4) (P) (inv) (cnt) (n0)) :: (sqV8_8 (a0) (a1) (a2) (a3) (a4) (n1) (n2) (n3) (n4) (P) (inv) (cnt) (n0)) :: (sqV8_0 (a0) (a1) (a2) (a3) (a4) (n1) (n2) (n3) (n4) (P) (inv) (cnt) (n0)) :: (n1) :: (n2) :: (n3) :: (n4) :: (P) :: (inv) :: (sqV9_12 (a0) (a1) (a2) (a3) (a4) (n1) (n2) (n3) (n4) (P) (inv) (cnt) (n0)) :: rest} := by
  let C0 : UInt256 := sqV0_0 (a0) (a1) (a2) (a3) (a4) (n1) (n2) (n3) (n4) (P) (inv) (cnt) (n0)
  let Q0 : UInt256 := sqV0_1 (a0) (a1) (a2) (a3) (a4) (n1) (n2) (n3) (n4) (P) (inv) (cnt) (n0)
  let C1 : UInt256 := sqV1_0 (a0) (a1) (a2) (a3) (a4) (n1) (n2) (n3) (n4) (P) (inv) (cnt) (n0)
  let Q1 : UInt256 := sqV1_1 (a0) (a1) (a2) (a3) (a4) (n1) (n2) (n3) (n4) (P) (inv) (cnt) (n0)
  let C2 : UInt256 := sqV2_0 (a0) (a1) (a2) (a3) (a4) (n1) (n2) (n3) (n4) (P) (inv) (cnt) (n0)
  let Q2 : UInt256 := sqV2_1 (a0) (a1) (a2) (a3) (a4) (n1) (n2) (n3) (n4) (P) (inv) (cnt) (n0)
  let C3 : UInt256 := sqV3_0 (a0) (a1) (a2) (a3) (a4) (n1) (n2) (n3) (n4) (P) (inv) (cnt) (n0)
  let Q3 : UInt256 := sqV3_1 (a0) (a1) (a2) (a3) (a4) (n1) (n2) (n3) (n4) (P) (inv) (cnt) (n0)
  let C4 : UInt256 := sqV4_0 (a0) (a1) (a2) (a3) (a4) (n1) (n2) (n3) (n4) (P) (inv) (cnt) (n0)
  let Q4 : UInt256 := sqV4_4 (a0) (a1) (a2) (a3) (a4) (n1) (n2) (n3) (n4) (P) (inv) (cnt) (n0)
  let C5 : UInt256 := sqV5_0 (a0) (a1) (a2) (a3) (a4) (n1) (n2) (n3) (n4) (P) (inv) (cnt) (n0)
  let Z0 : UInt256 := sqV5_5 (a0) (a1) (a2) (a3) (a4) (n1) (n2) (n3) (n4) (P) (inv) (cnt) (n0)
  let C6 : UInt256 := sqV6_0 (a0) (a1) (a2) (a3) (a4) (n1) (n2) (n3) (n4) (P) (inv) (cnt) (n0)
  let Z1 : UInt256 := sqV6_6 (a0) (a1) (a2) (a3) (a4) (n1) (n2) (n3) (n4) (P) (inv) (cnt) (n0)
  let C7 : UInt256 := sqV7_0 (a0) (a1) (a2) (a3) (a4) (n1) (n2) (n3) (n4) (P) (inv) (cnt) (n0)
  let Z2 : UInt256 := sqV7_7 (a0) (a1) (a2) (a3) (a4) (n1) (n2) (n3) (n4) (P) (inv) (cnt) (n0)
  let C8 : UInt256 := sqV8_0 (a0) (a1) (a2) (a3) (a4) (n1) (n2) (n3) (n4) (P) (inv) (cnt) (n0)
  let Z3 : UInt256 := sqV8_8 (a0) (a1) (a2) (a3) (a4) (n1) (n2) (n3) (n4) (P) (inv) (cnt) (n0)
  let D : UInt256 := sqV9_12 (a0) (a1) (a2) (a3) (a4) (n1) (n2) (n3) (n4) (P) (inv) (cnt) (n0)
  have hp0 : 0 < P.toNat := by
    rw [hp, CycleSubmission.WordArithmetic.pValue]
    norm_num [HistoricalSearch.CRTColumn.residueModulus]
  have hc0 : C0.toNat < P.toNat := by
    change (UInt256.mulMod _ _ P).toNat < P.toNat
    exact R5SharedTools.residue_lt _ _ _ hp0
  have hc1 : C1.toNat < P.toNat := by
    change (UInt256.mulMod _ _ P).toNat < P.toNat
    exact R5SharedTools.residue_lt _ _ _ hp0
  have hc2 : C2.toNat < P.toNat := by
    change (UInt256.mulMod _ _ P).toNat < P.toNat
    exact R5SharedTools.residue_lt _ _ _ hp0
  have hc3 : C3.toNat < P.toNat := by
    change (UInt256.mulMod _ _ P).toNat < P.toNat
    exact R5SharedTools.residue_lt _ _ _ hp0
  have hc4 : C4.toNat < P.toNat := by
    change (UInt256.mulMod _ _ P).toNat < P.toNat
    exact R5SharedTools.residue_lt _ _ _ hp0
  have hc5 : C5.toNat < P.toNat := by
    change (UInt256.mulMod _ _ P).toNat < P.toNat
    exact R5SharedTools.residue_lt _ _ _ hp0
  have hc6 : C6.toNat < P.toNat := by
    change (UInt256.mulMod _ _ P).toNat < P.toNat
    exact R5SharedTools.residue_lt _ _ _ hp0
  have hc7 : C7.toNat < P.toNat := by
    change (UInt256.mulMod _ _ P).toNat < P.toNat
    exact R5SharedTools.residue_lt _ _ _ hp0
  have hc8 : C8.toNat < P.toNat := by
    change (UInt256.mulMod _ _ P).toNat < P.toNat
    exact R5SharedTools.residue_lt _ _ _ hp0
  have h0 : runInstructions NextR5Columns.stage0Program {s with pc := UInt256.ofNat 4018, stack := (a0) :: (a1) :: (a2) :: (a3) :: (a4) :: (n1) :: (n2) :: (n3) :: (n4) :: (P) :: (inv) :: (cnt) :: rest} = some {s with pc := UInt256.ofNat 4046, stack := (C0) :: (Q0) :: ((a0+a0)) :: (a1) :: (a2) :: (a3) :: (a4) :: (n1) :: (n2) :: (n3) :: (n4) :: (P) :: (inv) :: (cnt) :: rest} := by
    simpa only [NextR5Columns.history0, C0, Q0, sqV0_0, sqV0_1] using NextR5Columns.run_stage0 (s) (UInt256.ofNat 0) (UInt256.ofNat 0) (UInt256.ofNat 0) (UInt256.ofNat 0) (UInt256.ofNat 0) (UInt256.ofNat 0) (a0) (a1) (a2) (a3) (a4) (n0) (n1) (n2) (n3) (n4) (P) (inv) (cnt) (UInt256.ofNat 0) (UInt256.ofNat 0) (UInt256.ofNat 0) (UInt256.ofNat 0) (rest) (hcap) (hact) (hn0) (hi) (hp) (ha0) (ha1) (ha2) (ha3) (hp0)
  have h1 : runInstructions NextR5Columns.stage1Program {s with pc := UInt256.ofNat 4046, stack := (C0) :: (Q0) :: ((a0+a0)) :: (a1) :: (a2) :: (a3) :: (a4) :: (n1) :: (n2) :: (n3) :: (n4) :: (P) :: (inv) :: (cnt) :: rest} = some {s with pc := UInt256.ofNat 4084, stack := (C1) :: (Q1) :: (Q0) :: ((a0+a0)) :: (a1) :: (a2) :: (a3) :: (a4) :: (n1) :: (n2) :: (n3) :: (n4) :: (P) :: (inv) :: (cnt) :: rest} := by
    simpa only [NextR5Columns.history1, C1, Q1, sqV1_0, sqV1_1] using NextR5Columns.run_stage1 (s) (C0) (Q0) (UInt256.ofNat 0) (UInt256.ofNat 0) (UInt256.ofNat 0) (UInt256.ofNat 0) (a0) (a1) (a2) (a3) (a4) (n0) (n1) (n2) (n3) (n4) (P) (inv) (cnt) (UInt256.ofNat 0) (UInt256.ofNat 0) (UInt256.ofNat 0) (UInt256.ofNat 0) (rest) (hcap) (hact) (hn0) (hi) (hp) (ha0) (ha1) (ha2) (ha3) (hc0)
  have h2 : runInstructions NextR5Columns.stage2Program {s with pc := UInt256.ofNat 4084, stack := (C1) :: (Q1) :: (Q0) :: ((a0+a0)) :: (a1) :: (a2) :: (a3) :: (a4) :: (n1) :: (n2) :: (n3) :: (n4) :: (P) :: (inv) :: (cnt) :: rest} = some {s with pc := UInt256.ofNat 4143, stack := (C2) :: (Q2) :: (Q1) :: (Q0) :: ((a0+a0)) :: ((a1+a1)) :: (a2) :: (a3) :: (a4) :: (n1) :: (n2) :: (n3) :: (n4) :: (P) :: (inv) :: (cnt) :: rest} := by
    simpa only [NextR5Columns.history2, C2, Q2, sqV2_0, sqV2_1] using NextR5Columns.run_stage2 (s) (C1) (Q0) (Q1) (UInt256.ofNat 0) (UInt256.ofNat 0) (UInt256.ofNat 0) (a0) (a1) (a2) (a3) (a4) (n0) (n1) (n2) (n3) (n4) (P) (inv) (cnt) (UInt256.ofNat 0) (UInt256.ofNat 0) (UInt256.ofNat 0) (UInt256.ofNat 0) (rest) (hcap) (hact) (hn0) (hi) (hp) (ha0) (ha1) (ha2) (ha3) (hc1)
  have h3 : runInstructions NextR5Columns.stage3Program {s with pc := UInt256.ofNat 4143, stack := (C2) :: (Q2) :: (Q1) :: (Q0) :: ((a0+a0)) :: ((a1+a1)) :: (a2) :: (a3) :: (a4) :: (n1) :: (n2) :: (n3) :: (n4) :: (P) :: (inv) :: (cnt) :: rest} = some {s with pc := UInt256.ofNat 4208, stack := (C3) :: (Q3) :: (Q2) :: (Q1) :: (Q0) :: ((a0+a0)) :: ((a1+a1)) :: (a2) :: (a3) :: (a4) :: (n1) :: (n2) :: (n3) :: (n4) :: (P) :: (inv) :: (cnt) :: rest} := by
    simpa only [NextR5Columns.history3, C3, Q3, sqV3_0, sqV3_1] using NextR5Columns.run_stage3 (s) (C2) (Q0) (Q1) (Q2) (UInt256.ofNat 0) (UInt256.ofNat 0) (a0) (a1) (a2) (a3) (a4) (n0) (n1) (n2) (n3) (n4) (P) (inv) (cnt) (UInt256.ofNat 0) (UInt256.ofNat 0) (UInt256.ofNat 0) (UInt256.ofNat 0) (rest) (hcap) (hact) (hn0) (hi) (hp) (ha0) (ha1) (ha2) (ha3) (hc2)
  have h4 : runInstructions NextR5Columns.stage4Program {s with pc := UInt256.ofNat 4208, stack := (C3) :: (Q3) :: (Q2) :: (Q1) :: (Q0) :: ((a0+a0)) :: ((a1+a1)) :: (a2) :: (a3) :: (a4) :: (n1) :: (n2) :: (n3) :: (n4) :: (P) :: (inv) :: (cnt) :: rest} = some {s with pc := UInt256.ofNat 4298, stack := (C4) :: (Q3) :: (Q2) :: (Q1) :: (Q4) :: ((a0+a0)) :: ((a1+a1)) :: ((a2+a2)) :: (a3) :: (a4) :: (n1) :: (n2) :: (n3) :: (n4) :: (P) :: (inv) :: (cnt) :: rest} := by
    simpa only [NextR5Columns.history4, C4, Q4, sqV4_0, sqV4_4] using NextR5Columns.run_stage4 (s) (C3) (Q0) (Q1) (Q2) (Q3) (UInt256.ofNat 0) (a0) (a1) (a2) (a3) (a4) (n0) (n1) (n2) (n3) (n4) (P) (inv) (cnt) (UInt256.ofNat 0) (UInt256.ofNat 0) (UInt256.ofNat 0) (UInt256.ofNat 0) (rest) (hcap) (hact) (hn0) (hi) (hp) (ha0) (ha1) (ha2) (ha3) (hc3)
  have h5 : runInstructions NextR5Columns.stage5Program {s with pc := UInt256.ofNat 4298, stack := (C4) :: (Q3) :: (Q2) :: (Q1) :: (Q4) :: ((a0+a0)) :: ((a1+a1)) :: ((a2+a2)) :: (a3) :: (a4) :: (n1) :: (n2) :: (n3) :: (n4) :: (P) :: (inv) :: (cnt) :: rest} = some {s with pc := UInt256.ofNat 4400, stack := (C5) :: (Q3) :: (Q2) :: (Q1) :: (Q4) :: (Z0) :: ((a1+a1)) :: ((a2+a2)) :: (a3) :: (a4) :: (n1) :: (n2) :: (n3) :: (n4) :: (P) :: (inv) :: (cnt) :: rest} := by
    simpa only [NextR5Columns.history5, C5, Z0, sqV5_0, sqV5_5] using NextR5Columns.run_stage5 (s) (C4) (Q0) (Q1) (Q2) (Q3) (Q4) (a0) (a1) (a2) (a3) (a4) (n0) (n1) (n2) (n3) (n4) (P) (inv) (cnt) (UInt256.ofNat 0) (UInt256.ofNat 0) (UInt256.ofNat 0) (UInt256.ofNat 0) (rest) (hcap) (hact) (hn0) (hi) (hp) (ha0) (ha1) (ha2) (ha3) (hc4)
  have h6 : runInstructions NextR5Columns.stage6Program {s with pc := UInt256.ofNat 4400, stack := (C5) :: (Q3) :: (Q2) :: (Q1) :: (Q4) :: (Z0) :: ((a1+a1)) :: ((a2+a2)) :: (a3) :: (a4) :: (n1) :: (n2) :: (n3) :: (n4) :: (P) :: (inv) :: (cnt) :: rest} = some {s with pc := UInt256.ofNat 4495, stack := (C6) :: (Q3) :: (Q2) :: (Q1) :: (Q4) :: (Z0) :: (Z1) :: ((a2+a2)) :: ((a3+a3)) :: (a4) :: (n1) :: (n2) :: (n3) :: (n4) :: (P) :: (inv) :: (cnt) :: rest} := by
    simpa only [NextR5Columns.history6, C6, Z1, sqV6_0, sqV6_6] using NextR5Columns.run_stage6 (s) (C5) (Q0) (Q1) (Q2) (Q3) (Q4) (a0) (a1) (a2) (a3) (a4) (n0) (n1) (n2) (n3) (n4) (P) (inv) (cnt) (Z0) (UInt256.ofNat 0) (UInt256.ofNat 0) (UInt256.ofNat 0) (rest) (hcap) (hact) (hn0) (hi) (hp) (ha0) (ha1) (ha2) (ha3) (hc5)
  have h7 : runInstructions NextR5Columns.stage7Program {s with pc := UInt256.ofNat 4495, stack := (C6) :: (Q3) :: (Q2) :: (Q1) :: (Q4) :: (Z0) :: (Z1) :: ((a2+a2)) :: ((a3+a3)) :: (a4) :: (n1) :: (n2) :: (n3) :: (n4) :: (P) :: (inv) :: (cnt) :: rest} = some {s with pc := UInt256.ofNat 4567, stack := (C7) :: (Q3) :: (Q2) :: (Q1) :: (Q4) :: (Z0) :: (Z1) :: (Z2) :: ((a3+a3)) :: (a4) :: (n1) :: (n2) :: (n3) :: (n4) :: (P) :: (inv) :: (cnt) :: rest} := by
    simpa only [NextR5Columns.history7, C7, Z2, sqV7_0, sqV7_7] using NextR5Columns.run_stage7 (s) (C6) (Q0) (Q1) (Q2) (Q3) (Q4) (a0) (a1) (a2) (a3) (a4) (n0) (n1) (n2) (n3) (n4) (P) (inv) (cnt) (Z0) (Z1) (UInt256.ofNat 0) (UInt256.ofNat 0) (rest) (hcap) (hact) (hn0) (hi) (hp) (ha0) (ha1) (ha2) (ha3) (hc6)
  have h8 : runInstructions NextR5Columns.stage8Program {s with pc := UInt256.ofNat 4567, stack := (C7) :: (Q3) :: (Q2) :: (Q1) :: (Q4) :: (Z0) :: (Z1) :: (Z2) :: ((a3+a3)) :: (a4) :: (n1) :: (n2) :: (n3) :: (n4) :: (P) :: (inv) :: (cnt) :: rest} = some {s with pc := UInt256.ofNat 4630, stack := (C8) :: (Q3) :: (Q2) :: (Q1) :: (Q4) :: (Z0) :: (Z1) :: (Z2) :: (Z3) :: (a4) :: (n1) :: (n2) :: (n3) :: (n4) :: (P) :: (inv) :: (cnt) :: rest} := by
    simpa only [NextR5Columns.history8, C8, Z3, sqV8_0, sqV8_8] using NextR5Columns.run_stage8 (s) (C7) (Q0) (Q1) (Q2) (Q3) (Q4) (a0) (a1) (a2) (a3) (a4) (n0) (n1) (n2) (n3) (n4) (P) (inv) (cnt) (Z0) (Z1) (Z2) (UInt256.ofNat 0) (rest) (hcap) (hact) (hn0) (hi) (hp) (ha0) (ha1) (ha2) (ha3) (hc7)
  have h9 : runInstructions NextR5Columns.stage9Program {s with pc := UInt256.ofNat 4630, stack := (C8) :: (Q3) :: (Q2) :: (Q1) :: (Q4) :: (Z0) :: (Z1) :: (Z2) :: (Z3) :: (a4) :: (n1) :: (n2) :: (n3) :: (n4) :: (P) :: (inv) :: (cnt) :: rest} = some {s with pc := UInt256.ofNat 4641, stack := (cnt) :: (Z0) :: (Z1) :: (Z2) :: (Z3) :: (C8) :: (n1) :: (n2) :: (n3) :: (n4) :: (P) :: (inv) :: (D) :: rest} := by
    simpa only [NextR5Columns.history9, D, sqV9_12, CycleSubmission.R5.ExecSquare.sqTail_o12] using NextR5Columns.run_stage9 (s) (C8) (Q0) (Q1) (Q2) (Q3) (Q4) (a0) (a1) (a2) (a3) (a4) (n0) (n1) (n2) (n3) (n4) (P) (inv) (cnt) (Z0) (Z1) (Z2) (Z3) (rest) (hcap) (hact) (hn0) (hi) (hp) (ha0) (ha1) (ha2) (ha3) (hc8)
  exact (runInstructions_append_some _ _ _ _ _ h0 (runInstructions_append_some _ _ _ _ _ h1 (runInstructions_append_some _ _ _ _ _ h2 (runInstructions_append_some _ _ _ _ _ h3 (runInstructions_append_some _ _ _ _ _ h4 (runInstructions_append_some _ _ _ _ _ h5 (runInstructions_append_some _ _ _ _ _ h6 (runInstructions_append_some _ _ _ _ _ h7 (runInstructions_append_some _ _ _ _ _ h8 h9)))))))))
#print axioms new_run
end CycleSubmission.Prepared.R5Square
