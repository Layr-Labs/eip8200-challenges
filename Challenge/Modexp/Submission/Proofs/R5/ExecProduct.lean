import Challenge.Modexp.Submission.Proofs.Prepared.StackArgs
import Challenge.Modexp.Submission.Proofs.Bytecode.WindowNibbleDefs
import Challenge.Modexp.Submission.Proofs.Fast.Exp

open CycleSubmission.SharedStackArgs

set_option warningAsError true
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option maxRecDepth 40000
set_option maxHeartbeats 8000000

namespace CycleSubmission.R5.ExecProduct
open EvmSemantics EvmSemantics.EVM YulEvmCompiler
open Challenge.Modexp.Submission.Proofs.Bytecode.WindowNibbleKernel
open Challenge.EvmProof.Word (succ_ofNat_mod ofNat_add_mod ofNat_sub_ofNat literal_eq_ofNat)
open Challenge.EvmProof.Stepper (runInstr)
open Challenge.Modexp.Submission.Proofs.Fast.Exp (activeWords_fix)

local notation "W" => UInt256
local notation "N" => UInt256.ofNat

private theorem hz : ({val := 0} : W) = N 0 := rfl
private theorem hzn : ({val := 0} : W).toNat = 0 := rfl

/-! ## prCol0: pc 4716..4745, 22 instructions -/

def p0c0P : List Instr :=
  [.push 0 0,
   .op .MLOAD,
   .op (.Dup dA1),
   .op .MUL,
   .op (.Dup dA11),
   .op .MUL,
   .push 1 16,
   .op .SHR]

def p0c0M (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 : W) (rest : List W) : State :=
  let v0 : W := MachineState.readWord s.memory 0
  let v1 : W := x0 * v0
  let v2 : W := x10 * v1
  let v3 : W := UInt256.shiftRight v2 (N 16)
  {s with pc := N 4535, memory := s.memory, stack := v3 :: x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: rest}

theorem p0c0_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions p0c0P {s with pc := N 4526, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: rest} =
      some (p0c0M s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 rest) := by
  have hc (j : Nat) (hj : j ≤ 27) : rest.length + j < 1024 := by omega
  have hcr : rest.length < 1024 := by omega
  have ha0 : (0 : W).toNat = 0 := rfl
  have hf0 := activeWords_fix s 0 32 (by decide) (by norm_num) hact
  simp [hz, hzn, p0c0P, p0c0M, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, ofNat_sub_ofNat, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, hc, hcr, ha0, hf0]

def p0c1P : List Instr :=
  [.op (.Dup dA10),
   .op (.Dup dA11),
   .push 0 0,
   .op .MLOAD,
   .op (.Dup dA4),
   .op .MULMOD,
   .op (.Dup dA12),
   .push 1 160,
   .op .MLOAD]

def p0c1M (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 : W) (rest : List W) : State :=
  let v0 : W := MachineState.readWord s.memory 0
  let v1 : W := UInt256.mulMod x1 v0 x10
  let v2 : W := MachineState.readWord s.memory 160
  {s with pc := N 4545, memory := s.memory, stack := v2 :: x10 :: v1 :: x10 :: x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: rest}

theorem p0c1_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions p0c1P {s with pc := N 4535, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: rest} =
      some (p0c1M s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 rest) := by
  have hc (j : Nat) (hj : j ≤ 30) : rest.length + j < 1024 := by omega
  have hcr : rest.length < 1024 := by omega
  have ha0 : (0 : W).toNat = 0 := rfl
  have hf0 := activeWords_fix s 0 32 (by decide) (by norm_num) hact
  have ha160 : (160 : W).toNat = 160 := rfl
  have hf160 := activeWords_fix s 160 32 (by decide) (by norm_num) hact
  simp [hz, hzn, p0c1P, p0c1M, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, ofNat_sub_ofNat, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, hc, hcr, ha0, hf0, ha160, hf160]

def p0c2P : List Instr :=
  [.op (.Dup dA4),
   .op .MULMOD,
   .op .ADD,
   .push 2 2048,
   .op .MULMOD]

def p0c2M (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 : W) (rest : List W) : State :=
  let v0 : W := UInt256.mulMod x4 x0 x1
  let v1 : W := v0 + x2
  let v2 : W := UInt256.mulMod (N 2048) v1 x3
  {s with pc := N 4552, memory := s.memory, stack := v2 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: rest}

theorem p0c2_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions p0c2P {s with pc := N 4545, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: rest} =
      some (p0c2M s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 rest) := by
  have hc (j : Nat) (hj : j ≤ 30) : rest.length + j < 1024 := by omega
  have hcr : rest.length < 1024 := by omega
  simp [hz, hzn, p0c2P, p0c2M, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, ofNat_sub_ofNat, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, hc, hcr]

def prCol0Program : List Instr :=
  [.push 0 0,
   .op .MLOAD,
   .op (.Dup dA1),
   .op .MUL,
   .op (.Dup dA11),
   .op .MUL,
   .push 1 16,
   .op .SHR,
   .op (.Dup dA10),
   .op (.Dup dA11),
   .push 0 0,
   .op .MLOAD,
   .op (.Dup dA4),
   .op .MULMOD,
   .op (.Dup dA12),
   .push 1 160,
   .op .MLOAD,
   .op (.Dup dA4),
   .op .MULMOD,
   .op .ADD,
   .push 2 2048,
   .op .MULMOD]

def prCol0Model (s : State) (x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp : W) (rest : List W) : State :=
  let v0 : W := MachineState.readWord s.memory 0
  let v1 : W := x0 * v0
  let v2 : W := inv * v1
  let v3 : W := UInt256.shiftRight v2 (N 16)
  let v4 : W := MachineState.readWord s.memory 0
  let v5 : W := UInt256.mulMod x0 v4 P
  let v6 : W := MachineState.readWord s.memory 160
  let v7 : W := UInt256.mulMod v3 v6 P
  let v8 : W := v7 + v5
  let v9 : W := UInt256.mulMod (N 2048) v8 P
  {s with pc := N 4552, memory := s.memory, stack := v9 :: v3 :: x0 :: x1 :: x2 :: x3 :: x4 :: n1 :: n2 :: n3 :: n4 :: P :: inv :: cntp :: rest}

theorem prCol0_run (s : State) (x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions prCol0Program {s with pc := N 4526, stack := x0 :: x1 :: x2 :: x3 :: x4 :: n1 :: n2 :: n3 :: n4 :: P :: inv :: cntp :: rest} =
      some (prCol0Model s x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp rest) := by
  let v0 : W := MachineState.readWord s.memory 0
  let v1 : W := x0 * v0
  let v2 : W := inv * v1
  let v3 : W := UInt256.shiftRight v2 (N 16)
  let v4 : W := MachineState.readWord s.memory 0
  let v5 : W := UInt256.mulMod x0 v4 P
  let v6 : W := MachineState.readWord s.memory 160
  let v7 : W := UInt256.mulMod v3 v6 P
  let v8 : W := v7 + v5
  let v9 : W := UInt256.mulMod (N 2048) v8 P
  have h0 : runInstructions p0c0P {s with pc := N 4526, memory := s.memory, stack := x0 :: x1 :: x2 :: x3 :: x4 :: n1 :: n2 :: n3 :: n4 :: P :: inv :: cntp :: rest} = some {s with pc := N 4535, memory := s.memory, stack := v3 :: x0 :: x1 :: x2 :: x3 :: x4 :: n1 :: n2 :: n3 :: n4 :: P :: inv :: cntp :: rest} := by
    simpa only [p0c0M, v0, v1, v2, v3] using p0c0_run (s) x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp rest hcap hact
  have h1 : runInstructions p0c1P {s with pc := N 4535, memory := s.memory, stack := v3 :: x0 :: x1 :: x2 :: x3 :: x4 :: n1 :: n2 :: n3 :: n4 :: P :: inv :: cntp :: rest} = some {s with pc := N 4545, memory := s.memory, stack := v6 :: P :: v5 :: P :: v3 :: x0 :: x1 :: x2 :: x3 :: x4 :: n1 :: n2 :: n3 :: n4 :: P :: inv :: cntp :: rest} := by
    simpa only [p0c1M, v4, v5, v6] using p0c1_run (s) v3 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp rest hcap hact
  have h2 : runInstructions p0c2P {s with pc := N 4545, memory := s.memory, stack := v6 :: P :: v5 :: P :: v3 :: x0 :: x1 :: x2 :: x3 :: x4 :: n1 :: n2 :: n3 :: n4 :: P :: inv :: cntp :: rest} = some {s with pc := N 4552, memory := s.memory, stack := v9 :: v3 :: x0 :: x1 :: x2 :: x3 :: x4 :: n1 :: n2 :: n3 :: n4 :: P :: inv :: cntp :: rest} := by
    simpa only [p0c2M, v7, v8, v9] using p0c2_run (s) v6 P v5 P v3 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp rest hcap hact
  exact (runInstructions_append_some _ _ _ _ _ h0 (runInstructions_append_some _ _ _ _ _ h1 h2))

def prCol0_o0 (x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp b0 n0 : W) : W :=
  (UInt256.mulMod (N 2048) ((UInt256.mulMod (UInt256.shiftRight (inv * (x0 * b0)) (N 16)) n0 P) + (UInt256.mulMod x0 b0 P)) P)

def prCol0_o1 (x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp b0 n0 : W) : W :=
  (UInt256.shiftRight (inv * (x0 * b0)) (N 16))

theorem prCol0_eq (s : State) (x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp b0 n0 : W) (rest : List W)
    (h_b0 : MachineState.readWord s.memory 0 = b0)
    (h_n0 : MachineState.readWord s.memory 160 = n0) :
    prCol0Model s x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp rest =
      {s with pc := N 4552, stack := (prCol0_o0 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp b0 n0) :: (prCol0_o1 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp b0 n0) :: x0 :: x1 :: x2 :: x3 :: x4 :: n1 :: n2 :: n3 :: n4 :: P :: inv :: cntp :: rest} := by
  simp only [prCol0Model, prCol0_o0, prCol0_o1, h_b0, h_n0]

/-! ## prCol1: pc 4745..4800, 47 instructions -/

def p1c0P : List Instr :=
  [.op (.Dup dA0),
   .push 1 32,
   .op .MLOAD,
   .op (.Dup dA4),
   .op .MUL,
   .op .ADD,
   .push 0 0,
   .op .MLOAD]

def p1c0M (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 : W) (rest : List W) : State :=
  let v0 : W := MachineState.readWord s.memory 32
  let v1 : W := x2 * v0
  let v2 : W := v1 + x0
  let v3 : W := MachineState.readWord s.memory 0
  {s with pc := N 4561, memory := s.memory, stack := v3 :: v2 :: x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: rest}

theorem p1c0_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions p1c0P {s with pc := N 4552, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: rest} =
      some (p1c0M s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 rest) := by
  have hc (j : Nat) (hj : j ≤ 30) : rest.length + j < 1024 := by omega
  have hcr : rest.length < 1024 := by omega
  have ha32 : (32 : W).toNat = 32 := rfl
  have hf32 := activeWords_fix s 32 32 (by decide) (by norm_num) hact
  have ha0 : (0 : W).toNat = 0 := rfl
  have hf0 := activeWords_fix s 0 32 (by decide) (by norm_num) hact
  simp [hz, hzn, p1c0P, p1c0M, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, ofNat_sub_ofNat, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, hc, hcr, ha32, hf32, ha0, hf0]

def p1c1P : List Instr :=
  [.op (.Dup dA5),
   .op .MUL,
   .op .ADD,
   .op (.Dup dA8),
   .op (.Dup dA3),
   .op .MUL,
   .op .ADD,
   .op (.Dup dA13)]

def p1c1M (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 : W) (rest : List W) : State :=
  let v0 : W := x5 * x0
  let v1 : W := v0 + x1
  let v2 : W := x3 * x9
  let v3 : W := v2 + v1
  {s with pc := N 4569, memory := s.memory, stack := x14 :: v3 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: rest}

theorem p1c1_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions p1c1P {s with pc := N 4561, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: rest} =
      some (p1c1M s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 rest) := by
  have hc (j : Nat) (hj : j ≤ 30) : rest.length + j < 1024 := by omega
  have hcr : rest.length < 1024 := by omega
  simp [hz, hzn, p1c1P, p1c1M, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, ofNat_sub_ofNat, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, hc, hcr]

def p1c2P : List Instr :=
  [.op .MUL,
   .push 1 16,
   .op .SHR,
   .op (.Swap sA0),
   .op (.Dup dA12),
   .push 1 32,
   .op .MLOAD,
   .op (.Dup dA5)]

def p1c2M (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 : W) (rest : List W) : State :=
  let v0 : W := x0 * x1
  let v1 : W := UInt256.shiftRight v0 (N 16)
  let v2 : W := MachineState.readWord s.memory 32
  {s with pc := N 4579, memory := s.memory, stack := x4 :: v2 :: x13 :: x2 :: v1 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: rest}

theorem p1c2_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions p1c2P {s with pc := N 4569, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: rest} =
      some (p1c2M s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 rest) := by
  have hc (j : Nat) (hj : j ≤ 31) : rest.length + j < 1024 := by omega
  have hcr : rest.length < 1024 := by omega
  have ha32 : (32 : W).toNat = 32 := rfl
  have hf32 := activeWords_fix s 32 32 (by decide) (by norm_num) hact
  simp [hz, hzn, p1c2P, p1c2M, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, ofNat_sub_ofNat, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, hc, hcr, ha32, hf32]

def p1c3P : List Instr :=
  [.op .MULMOD,
   .op .ADD,
   .op (.Dup dA12),
   .push 0 0,
   .op .MLOAD,
   .op (.Dup dA6),
   .op .MULMOD,
   .op .ADD]

def p1c3M (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 : W) (rest : List W) : State :=
  let v0 : W := UInt256.mulMod x0 x1 x2
  let v1 : W := v0 + x3
  let v2 : W := MachineState.readWord s.memory 0
  let v3 : W := UInt256.mulMod x7 v2 x15
  let v4 : W := v3 + v1
  {s with pc := N 4587, memory := s.memory, stack := v4 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: rest}

theorem p1c3_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions p1c3P {s with pc := N 4579, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: rest} =
      some (p1c3M s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 rest) := by
  have hc (j : Nat) (hj : j ≤ 31) : rest.length + j < 1024 := by omega
  have hcr : rest.length < 1024 := by omega
  have ha0 : (0 : W).toNat = 0 := rfl
  have hf0 := activeWords_fix s 0 32 (by decide) (by norm_num) hact
  simp [hz, hzn, p1c3P, p1c3M, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, ofNat_sub_ofNat, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, hc, hcr, ha0, hf0]

def p1c4P : List Instr :=
  [.op (.Dup dA12),
   .op (.Dup dA9),
   .op (.Dup dA4),
   .op .MULMOD,
   .op .ADD,
   .op (.Dup dA12),
   .push 1 160,
   .op .MLOAD]

def p1c4M (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 : W) (rest : List W) : State :=
  let v0 : W := UInt256.mulMod x2 x8 x12
  let v1 : W := v0 + x0
  let v2 : W := MachineState.readWord s.memory 160
  {s with pc := N 4596, memory := s.memory, stack := v2 :: x12 :: v1 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: rest}

theorem p1c4_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions p1c4P {s with pc := N 4587, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: rest} =
      some (p1c4M s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 rest) := by
  have hc (j : Nat) (hj : j ≤ 31) : rest.length + j < 1024 := by omega
  have hcr : rest.length < 1024 := by omega
  have ha160 : (160 : W).toNat = 160 := rfl
  have hf160 := activeWords_fix s 160 32 (by decide) (by norm_num) hact
  simp [hz, hzn, p1c4P, p1c4M, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, ofNat_sub_ofNat, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, hc, hcr, ha160, hf160]

def p1c5P : List Instr :=
  [.op (.Dup dA3),
   .op .MULMOD,
   .op .ADD,
   .op (.Dup dA12),
   .op (.Swap sA0),
   .push 2 2048,
   .op .MULMOD]

def p1c5M (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 : W) (rest : List W) : State :=
  let v0 : W := UInt256.mulMod x3 x0 x1
  let v1 : W := v0 + x2
  let v2 : W := UInt256.mulMod (N 2048) v1 x14
  {s with pc := N 4605, memory := s.memory, stack := v2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: rest}

theorem p1c5_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions p1c5P {s with pc := N 4596, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: rest} =
      some (p1c5M s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 rest) := by
  have hc (j : Nat) (hj : j ≤ 31) : rest.length + j < 1024 := by omega
  have hcr : rest.length < 1024 := by omega
  simp [hz, hzn, p1c5P, p1c5M, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, ofNat_sub_ofNat, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, hc, hcr]

def prCol1Program : List Instr :=
  [.op (.Dup dA0),
   .push 1 32,
   .op .MLOAD,
   .op (.Dup dA4),
   .op .MUL,
   .op .ADD,
   .push 0 0,
   .op .MLOAD,
   .op (.Dup dA5),
   .op .MUL,
   .op .ADD,
   .op (.Dup dA8),
   .op (.Dup dA3),
   .op .MUL,
   .op .ADD,
   .op (.Dup dA13),
   .op .MUL,
   .push 1 16,
   .op .SHR,
   .op (.Swap sA0),
   .op (.Dup dA12),
   .push 1 32,
   .op .MLOAD,
   .op (.Dup dA5),
   .op .MULMOD,
   .op .ADD,
   .op (.Dup dA12),
   .push 0 0,
   .op .MLOAD,
   .op (.Dup dA6),
   .op .MULMOD,
   .op .ADD,
   .op (.Dup dA12),
   .op (.Dup dA9),
   .op (.Dup dA4),
   .op .MULMOD,
   .op .ADD,
   .op (.Dup dA12),
   .push 1 160,
   .op .MLOAD,
   .op (.Dup dA3),
   .op .MULMOD,
   .op .ADD,
   .op (.Dup dA12),
   .op (.Swap sA0),
   .push 2 2048,
   .op .MULMOD]

def prCol1Model (s : State) (c q0 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp : W) (rest : List W) : State :=
  let v0 : W := MachineState.readWord s.memory 32
  let v1 : W := x0 * v0
  let v2 : W := v1 + c
  let v3 : W := MachineState.readWord s.memory 0
  let v4 : W := x1 * v3
  let v5 : W := v4 + v2
  let v6 : W := q0 * n1
  let v7 : W := v6 + v5
  let v8 : W := inv * v7
  let v9 : W := UInt256.shiftRight v8 (N 16)
  let v10 : W := MachineState.readWord s.memory 32
  let v11 : W := UInt256.mulMod x0 v10 P
  let v12 : W := v11 + c
  let v13 : W := MachineState.readWord s.memory 0
  let v14 : W := UInt256.mulMod x1 v13 P
  let v15 : W := v14 + v12
  let v16 : W := UInt256.mulMod q0 n1 P
  let v17 : W := v16 + v15
  let v18 : W := MachineState.readWord s.memory 160
  let v19 : W := UInt256.mulMod v9 v18 P
  let v20 : W := v19 + v17
  let v21 : W := UInt256.mulMod (N 2048) v20 P
  {s with pc := N 4605, memory := s.memory, stack := v21 :: v9 :: q0 :: x0 :: x1 :: x2 :: x3 :: x4 :: n1 :: n2 :: n3 :: n4 :: P :: inv :: cntp :: rest}

theorem prCol1_run (s : State) (c q0 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions prCol1Program {s with pc := N 4552, stack := c :: q0 :: x0 :: x1 :: x2 :: x3 :: x4 :: n1 :: n2 :: n3 :: n4 :: P :: inv :: cntp :: rest} =
      some (prCol1Model s c q0 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp rest) := by
  let v0 : W := MachineState.readWord s.memory 32
  let v1 : W := x0 * v0
  let v2 : W := v1 + c
  let v3 : W := MachineState.readWord s.memory 0
  let v4 : W := x1 * v3
  let v5 : W := v4 + v2
  let v6 : W := q0 * n1
  let v7 : W := v6 + v5
  let v8 : W := inv * v7
  let v9 : W := UInt256.shiftRight v8 (N 16)
  let v10 : W := MachineState.readWord s.memory 32
  let v11 : W := UInt256.mulMod x0 v10 P
  let v12 : W := v11 + c
  let v13 : W := MachineState.readWord s.memory 0
  let v14 : W := UInt256.mulMod x1 v13 P
  let v15 : W := v14 + v12
  let v16 : W := UInt256.mulMod q0 n1 P
  let v17 : W := v16 + v15
  let v18 : W := MachineState.readWord s.memory 160
  let v19 : W := UInt256.mulMod v9 v18 P
  let v20 : W := v19 + v17
  let v21 : W := UInt256.mulMod (N 2048) v20 P
  have h0 : runInstructions p1c0P {s with pc := N 4552, memory := s.memory, stack := c :: q0 :: x0 :: x1 :: x2 :: x3 :: x4 :: n1 :: n2 :: n3 :: n4 :: P :: inv :: cntp :: rest} = some {s with pc := N 4561, memory := s.memory, stack := v3 :: v2 :: c :: q0 :: x0 :: x1 :: x2 :: x3 :: x4 :: n1 :: n2 :: n3 :: n4 :: P :: inv :: cntp :: rest} := by
    simpa only [p1c0M, v0, v1, v2, v3] using p1c0_run (s) c q0 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp rest hcap hact
  have h1 : runInstructions p1c1P {s with pc := N 4561, memory := s.memory, stack := v3 :: v2 :: c :: q0 :: x0 :: x1 :: x2 :: x3 :: x4 :: n1 :: n2 :: n3 :: n4 :: P :: inv :: cntp :: rest} = some {s with pc := N 4569, memory := s.memory, stack := inv :: v7 :: c :: q0 :: x0 :: x1 :: x2 :: x3 :: x4 :: n1 :: n2 :: n3 :: n4 :: P :: inv :: cntp :: rest} := by
    simpa only [p1c1M, v4, v5, v6, v7] using p1c1_run (s) v3 v2 c q0 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp rest hcap hact
  have h2 : runInstructions p1c2P {s with pc := N 4569, memory := s.memory, stack := inv :: v7 :: c :: q0 :: x0 :: x1 :: x2 :: x3 :: x4 :: n1 :: n2 :: n3 :: n4 :: P :: inv :: cntp :: rest} = some {s with pc := N 4579, memory := s.memory, stack := x0 :: v10 :: P :: c :: v9 :: q0 :: x0 :: x1 :: x2 :: x3 :: x4 :: n1 :: n2 :: n3 :: n4 :: P :: inv :: cntp :: rest} := by
    simpa only [p1c2M, v8, v9, v10] using p1c2_run (s) inv v7 c q0 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp rest hcap hact
  have h3 : runInstructions p1c3P {s with pc := N 4579, memory := s.memory, stack := x0 :: v10 :: P :: c :: v9 :: q0 :: x0 :: x1 :: x2 :: x3 :: x4 :: n1 :: n2 :: n3 :: n4 :: P :: inv :: cntp :: rest} = some {s with pc := N 4587, memory := s.memory, stack := v15 :: v9 :: q0 :: x0 :: x1 :: x2 :: x3 :: x4 :: n1 :: n2 :: n3 :: n4 :: P :: inv :: cntp :: rest} := by
    simpa only [p1c3M, v11, v12, v13, v14, v15] using p1c3_run (s) x0 v10 P c v9 q0 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp rest hcap hact
  have h4 : runInstructions p1c4P {s with pc := N 4587, memory := s.memory, stack := v15 :: v9 :: q0 :: x0 :: x1 :: x2 :: x3 :: x4 :: n1 :: n2 :: n3 :: n4 :: P :: inv :: cntp :: rest} = some {s with pc := N 4596, memory := s.memory, stack := v18 :: P :: v17 :: v9 :: q0 :: x0 :: x1 :: x2 :: x3 :: x4 :: n1 :: n2 :: n3 :: n4 :: P :: inv :: cntp :: rest} := by
    simpa only [p1c4M, v16, v17, v18] using p1c4_run (s) v15 v9 q0 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp rest hcap hact
  have h5 : runInstructions p1c5P {s with pc := N 4596, memory := s.memory, stack := v18 :: P :: v17 :: v9 :: q0 :: x0 :: x1 :: x2 :: x3 :: x4 :: n1 :: n2 :: n3 :: n4 :: P :: inv :: cntp :: rest} = some {s with pc := N 4605, memory := s.memory, stack := v21 :: v9 :: q0 :: x0 :: x1 :: x2 :: x3 :: x4 :: n1 :: n2 :: n3 :: n4 :: P :: inv :: cntp :: rest} := by
    simpa only [p1c5M, v19, v20, v21] using p1c5_run (s) v18 P v17 v9 q0 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp rest hcap hact
  exact (runInstructions_append_some _ _ _ _ _ h0 (runInstructions_append_some _ _ _ _ _ h1 (runInstructions_append_some _ _ _ _ _ h2 (runInstructions_append_some _ _ _ _ _ h3 (runInstructions_append_some _ _ _ _ _ h4 h5)))))

def prCol1_o0 (c q0 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp b0 b1 n0 : W) : W :=
  (UInt256.mulMod (N 2048) ((UInt256.mulMod (UInt256.shiftRight (inv * ((q0 * n1) + ((x1 * b0) + ((x0 * b1) + c)))) (N 16)) n0 P) + ((UInt256.mulMod q0 n1 P) + ((UInt256.mulMod x1 b0 P) + ((UInt256.mulMod x0 b1 P) + c)))) P)

def prCol1_o1 (c q0 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp b0 b1 n0 : W) : W :=
  (UInt256.shiftRight (inv * ((q0 * n1) + ((x1 * b0) + ((x0 * b1) + c)))) (N 16))

theorem prCol1_eq (s : State) (c q0 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp b0 b1 n0 : W) (rest : List W)
    (h_b0 : MachineState.readWord s.memory 0 = b0)
    (h_b1 : MachineState.readWord s.memory 32 = b1)
    (h_n0 : MachineState.readWord s.memory 160 = n0) :
    prCol1Model s c q0 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp rest =
      {s with pc := N 4605, stack := (prCol1_o0 c q0 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp b0 b1 n0) :: (prCol1_o1 c q0 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp b0 b1 n0) :: q0 :: x0 :: x1 :: x2 :: x3 :: x4 :: n1 :: n2 :: n3 :: n4 :: P :: inv :: cntp :: rest} := by
  simp only [prCol1Model, prCol1_o0, prCol1_o1, h_b0, h_b1, h_n0]

/-! ## prCol2: pc 3264..3342, 68 instructions -/

def p2c0P : List Instr :=
  [.op .JUMPDEST,
   .op (.Dup dA0),
   .push 1 64,
   .op .MLOAD,
   .op (.Dup dA5),
   .op .MUL,
   .op .ADD]

def p2c0M (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 : W) (rest : List W) : State :=
  let v0 : W := MachineState.readWord s.memory 64
  let v1 : W := x3 * v0
  let v2 : W := v1 + x0
  {s with pc := N 3144, memory := s.memory, stack := v2 :: x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: rest}

theorem p2c0_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions p2c0P {s with pc := N 3136, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: rest} =
      some (p2c0M s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 rest) := by
  have hc (j : Nat) (hj : j ≤ 31) : rest.length + j < 1024 := by omega
  have hcr : rest.length < 1024 := by omega
  have ha64 : (64 : W).toNat = 64 := rfl
  have hf64 := activeWords_fix s 64 32 (by decide) (by norm_num) hact
  simp [hz, hzn, p2c0P, p2c0M, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, ofNat_sub_ofNat, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, hc, hcr, ha64, hf64]

def p2c1P : List Instr :=
  [.push 1 32,
   .op .MLOAD,
   .op (.Dup dA6),
   .op .MUL,
   .op .ADD,
   .push 0 0,
   .op .MLOAD,
   .op (.Dup dA7)]

def p2c1M (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 : W) (rest : List W) : State :=
  let v0 : W := MachineState.readWord s.memory 32
  let v1 : W := x5 * v0
  let v2 : W := v1 + x0
  let v3 : W := MachineState.readWord s.memory 0
  {s with pc := N 3153, memory := s.memory, stack := x6 :: v3 :: v2 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: rest}

theorem p2c1_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions p2c1P {s with pc := N 3144, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: rest} =
      some (p2c1M s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 rest) := by
  have hc (j : Nat) (hj : j ≤ 31) : rest.length + j < 1024 := by omega
  have hcr : rest.length < 1024 := by omega
  have ha32 : (32 : W).toNat = 32 := rfl
  have hf32 := activeWords_fix s 32 32 (by decide) (by norm_num) hact
  have ha0 : (0 : W).toNat = 0 := rfl
  have hf0 := activeWords_fix s 0 32 (by decide) (by norm_num) hact
  simp [hz, hzn, p2c1P, p2c1M, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, ofNat_sub_ofNat, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, hc, hcr, ha32, hf32, ha0, hf0]

def p2c2P : List Instr :=
  [.op .MUL,
   .op .ADD,
   .op (.Dup dA10),
   .op (.Dup dA4),
   .op .MUL,
   .op .ADD,
   .op (.Dup dA9),
   .op (.Dup dA3)]

def p2c2M (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 : W) (rest : List W) : State :=
  let v0 : W := x0 * x1
  let v1 : W := v0 + x2
  let v2 : W := x5 * x12
  let v3 : W := v2 + v1
  {s with pc := N 3161, memory := s.memory, stack := x4 :: x11 :: v3 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: rest}

theorem p2c2_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions p2c2P {s with pc := N 3153, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: rest} =
      some (p2c2M s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 rest) := by
  have hc (j : Nat) (hj : j ≤ 31) : rest.length + j < 1024 := by omega
  have hcr : rest.length < 1024 := by omega
  simp [hz, hzn, p2c2P, p2c2M, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, ofNat_sub_ofNat, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, hc, hcr]

def p2c3P : List Instr :=
  [.op .MUL,
   .op .ADD,
   .op (.Dup dA14),
   .op .MUL,
   .push 1 16,
   .op .SHR,
   .op (.Swap sA0),
   .op (.Dup dA13)]

def p2c3M (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 : W) (rest : List W) : State :=
  let v0 : W := x0 * x1
  let v1 : W := v0 + x2
  let v2 : W := x16 * v1
  let v3 : W := UInt256.shiftRight v2 (N 16)
  {s with pc := N 3170, memory := s.memory, stack := x15 :: x3 :: v3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: rest}

theorem p2c3_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions p2c3P {s with pc := N 3161, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: rest} =
      some (p2c3M s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 rest) := by
  have hc (j : Nat) (hj : j ≤ 31) : rest.length + j < 1024 := by omega
  have hcr : rest.length < 1024 := by omega
  simp [hz, hzn, p2c3P, p2c3M, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, ofNat_sub_ofNat, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, hc, hcr]

def p2c4P : List Instr :=
  [.push 1 64,
   .op .MLOAD,
   .op (.Dup dA6),
   .op .MULMOD,
   .op .ADD,
   .op (.Dup dA13),
   .push 1 32,
   .op .MLOAD]

def p2c4M (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 : W) (rest : List W) : State :=
  let v0 : W := MachineState.readWord s.memory 64
  let v1 : W := UInt256.mulMod x5 v0 x0
  let v2 : W := v1 + x1
  let v3 : W := MachineState.readWord s.memory 32
  {s with pc := N 3180, memory := s.memory, stack := v3 :: x14 :: v2 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: rest}

theorem p2c4_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions p2c4P {s with pc := N 3170, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: rest} =
      some (p2c4M s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 rest) := by
  have hc (j : Nat) (hj : j ≤ 32) : rest.length + j < 1024 := by omega
  have hcr : rest.length < 1024 := by omega
  have ha64 : (64 : W).toNat = 64 := rfl
  have hf64 := activeWords_fix s 64 32 (by decide) (by norm_num) hact
  have ha32 : (32 : W).toNat = 32 := rfl
  have hf32 := activeWords_fix s 32 32 (by decide) (by norm_num) hact
  simp [hz, hzn, p2c4P, p2c4M, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, ofNat_sub_ofNat, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, hc, hcr, ha64, hf64, ha32, hf32]

def p2c5P : List Instr :=
  [.op (.Dup dA7),
   .op .MULMOD,
   .op .ADD,
   .op (.Dup dA13),
   .push 0 0,
   .op .MLOAD,
   .op (.Dup dA8),
   .op .MULMOD]

def p2c5M (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 : W) (rest : List W) : State :=
  let v0 : W := UInt256.mulMod x7 x0 x1
  let v1 : W := v0 + x2
  let v2 : W := MachineState.readWord s.memory 0
  let v3 : W := UInt256.mulMod x8 v2 x15
  {s with pc := N 3188, memory := s.memory, stack := v3 :: v1 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: rest}

theorem p2c5_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions p2c5P {s with pc := N 3180, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: rest} =
      some (p2c5M s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 rest) := by
  have hc (j : Nat) (hj : j ≤ 32) : rest.length + j < 1024 := by omega
  have hcr : rest.length < 1024 := by omega
  have ha0 : (0 : W).toNat = 0 := rfl
  have hf0 := activeWords_fix s 0 32 (by decide) (by norm_num) hact
  simp [hz, hzn, p2c5P, p2c5M, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, ofNat_sub_ofNat, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, hc, hcr, ha0, hf0]

def p2c6P : List Instr :=
  [.op .ADD,
   .op (.Dup dA13),
   .op (.Dup dA11),
   .op (.Dup dA5),
   .op .MULMOD,
   .op .ADD,
   .op (.Dup dA13),
   .op (.Dup dA10)]

def p2c6M (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 : W) (rest : List W) : State :=
  let v0 : W := x0 + x1
  let v1 : W := UInt256.mulMod x4 x11 x14
  let v2 : W := v1 + v0
  {s with pc := N 3196, memory := s.memory, stack := x10 :: x14 :: v2 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: rest}

theorem p2c6_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions p2c6P {s with pc := N 3188, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: rest} =
      some (p2c6M s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 rest) := by
  have hc (j : Nat) (hj : j ≤ 32) : rest.length + j < 1024 := by omega
  have hcr : rest.length < 1024 := by omega
  simp [hz, hzn, p2c6P, p2c6M, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, ofNat_sub_ofNat, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, hc, hcr]

def p2c7P : List Instr :=
  [.op (.Dup dA4),
   .op .MULMOD,
   .op .ADD,
   .op (.Dup dA13),
   .push 1 160,
   .op .MLOAD,
   .op (.Dup dA3),
   .op .MULMOD]

def p2c7M (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 : W) (rest : List W) : State :=
  let v0 : W := UInt256.mulMod x4 x0 x1
  let v1 : W := v0 + x2
  let v2 : W := MachineState.readWord s.memory 160
  let v3 : W := UInt256.mulMod x3 v2 x15
  {s with pc := N 3205, memory := s.memory, stack := v3 :: v1 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: rest}

theorem p2c7_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions p2c7P {s with pc := N 3196, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: rest} =
      some (p2c7M s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 rest) := by
  have hc (j : Nat) (hj : j ≤ 32) : rest.length + j < 1024 := by omega
  have hcr : rest.length < 1024 := by omega
  have ha160 : (160 : W).toNat = 160 := rfl
  have hf160 := activeWords_fix s 160 32 (by decide) (by norm_num) hact
  simp [hz, hzn, p2c7P, p2c7M, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, ofNat_sub_ofNat, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, hc, hcr, ha160, hf160]

def p2c8P : List Instr :=
  [.op .ADD,
   .op (.Dup dA13),
   .op (.Swap sA0),
   .push 2 2048,
   .op .MULMOD]

def p2c8M (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 : W) (rest : List W) : State :=
  let v0 : W := x0 + x1
  let v1 : W := UInt256.mulMod (N 2048) v0 x14
  {s with pc := N 3212, memory := s.memory, stack := v1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: rest}

theorem p2c8_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions p2c8P {s with pc := N 3205, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: rest} =
      some (p2c8M s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 rest) := by
  have hc (j : Nat) (hj : j ≤ 31) : rest.length + j < 1024 := by omega
  have hcr : rest.length < 1024 := by omega
  simp [hz, hzn, p2c8P, p2c8M, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, ofNat_sub_ofNat, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, hc, hcr]

def prCol2Program : List Instr :=
  [.op .JUMPDEST,
   .op (.Dup dA0),
   .push 1 64,
   .op .MLOAD,
   .op (.Dup dA5),
   .op .MUL,
   .op .ADD,
   .push 1 32,
   .op .MLOAD,
   .op (.Dup dA6),
   .op .MUL,
   .op .ADD,
   .push 0 0,
   .op .MLOAD,
   .op (.Dup dA7),
   .op .MUL,
   .op .ADD,
   .op (.Dup dA10),
   .op (.Dup dA4),
   .op .MUL,
   .op .ADD,
   .op (.Dup dA9),
   .op (.Dup dA3),
   .op .MUL,
   .op .ADD,
   .op (.Dup dA14),
   .op .MUL,
   .push 1 16,
   .op .SHR,
   .op (.Swap sA0),
   .op (.Dup dA13),
   .push 1 64,
   .op .MLOAD,
   .op (.Dup dA6),
   .op .MULMOD,
   .op .ADD,
   .op (.Dup dA13),
   .push 1 32,
   .op .MLOAD,
   .op (.Dup dA7),
   .op .MULMOD,
   .op .ADD,
   .op (.Dup dA13),
   .push 0 0,
   .op .MLOAD,
   .op (.Dup dA8),
   .op .MULMOD,
   .op .ADD,
   .op (.Dup dA13),
   .op (.Dup dA11),
   .op (.Dup dA5),
   .op .MULMOD,
   .op .ADD,
   .op (.Dup dA13),
   .op (.Dup dA10),
   .op (.Dup dA4),
   .op .MULMOD,
   .op .ADD,
   .op (.Dup dA13),
   .push 1 160,
   .op .MLOAD,
   .op (.Dup dA3),
   .op .MULMOD,
   .op .ADD,
   .op (.Dup dA13),
   .op (.Swap sA0),
   .push 2 2048,
   .op .MULMOD]

def prCol2Model (s : State) (c q1 q0 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp : W) (rest : List W) : State :=
  let v0 : W := MachineState.readWord s.memory 64
  let v1 : W := x0 * v0
  let v2 : W := v1 + c
  let v3 : W := MachineState.readWord s.memory 32
  let v4 : W := x1 * v3
  let v5 : W := v4 + v2
  let v6 : W := MachineState.readWord s.memory 0
  let v7 : W := x2 * v6
  let v8 : W := v7 + v5
  let v9 : W := q0 * n2
  let v10 : W := v9 + v8
  let v11 : W := q1 * n1
  let v12 : W := v11 + v10
  let v13 : W := inv * v12
  let v14 : W := UInt256.shiftRight v13 (N 16)
  let v15 : W := MachineState.readWord s.memory 64
  let v16 : W := UInt256.mulMod x0 v15 P
  let v17 : W := v16 + c
  let v18 : W := MachineState.readWord s.memory 32
  let v19 : W := UInt256.mulMod x1 v18 P
  let v20 : W := v19 + v17
  let v21 : W := MachineState.readWord s.memory 0
  let v22 : W := UInt256.mulMod x2 v21 P
  let v23 : W := v22 + v20
  let v24 : W := UInt256.mulMod q0 n2 P
  let v25 : W := v24 + v23
  let v26 : W := UInt256.mulMod q1 n1 P
  let v27 : W := v26 + v25
  let v28 : W := MachineState.readWord s.memory 160
  let v29 : W := UInt256.mulMod v14 v28 P
  let v30 : W := v29 + v27
  let v31 : W := UInt256.mulMod (N 2048) v30 P
  {s with pc := N 3212, memory := s.memory, stack := v31 :: v14 :: q1 :: q0 :: x0 :: x1 :: x2 :: x3 :: x4 :: n1 :: n2 :: n3 :: n4 :: P :: inv :: cntp :: rest}

theorem prCol2_run (s : State) (c q1 q0 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions prCol2Program {s with pc := N 3136, stack := c :: q1 :: q0 :: x0 :: x1 :: x2 :: x3 :: x4 :: n1 :: n2 :: n3 :: n4 :: P :: inv :: cntp :: rest} =
      some (prCol2Model s c q1 q0 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp rest) := by
  let v0 : W := MachineState.readWord s.memory 64
  let v1 : W := x0 * v0
  let v2 : W := v1 + c
  let v3 : W := MachineState.readWord s.memory 32
  let v4 : W := x1 * v3
  let v5 : W := v4 + v2
  let v6 : W := MachineState.readWord s.memory 0
  let v7 : W := x2 * v6
  let v8 : W := v7 + v5
  let v9 : W := q0 * n2
  let v10 : W := v9 + v8
  let v11 : W := q1 * n1
  let v12 : W := v11 + v10
  let v13 : W := inv * v12
  let v14 : W := UInt256.shiftRight v13 (N 16)
  let v15 : W := MachineState.readWord s.memory 64
  let v16 : W := UInt256.mulMod x0 v15 P
  let v17 : W := v16 + c
  let v18 : W := MachineState.readWord s.memory 32
  let v19 : W := UInt256.mulMod x1 v18 P
  let v20 : W := v19 + v17
  let v21 : W := MachineState.readWord s.memory 0
  let v22 : W := UInt256.mulMod x2 v21 P
  let v23 : W := v22 + v20
  let v24 : W := UInt256.mulMod q0 n2 P
  let v25 : W := v24 + v23
  let v26 : W := UInt256.mulMod q1 n1 P
  let v27 : W := v26 + v25
  let v28 : W := MachineState.readWord s.memory 160
  let v29 : W := UInt256.mulMod v14 v28 P
  let v30 : W := v29 + v27
  let v31 : W := UInt256.mulMod (N 2048) v30 P
  have h0 : runInstructions p2c0P {s with pc := N 3136, memory := s.memory, stack := c :: q1 :: q0 :: x0 :: x1 :: x2 :: x3 :: x4 :: n1 :: n2 :: n3 :: n4 :: P :: inv :: cntp :: rest} = some {s with pc := N 3144, memory := s.memory, stack := v2 :: c :: q1 :: q0 :: x0 :: x1 :: x2 :: x3 :: x4 :: n1 :: n2 :: n3 :: n4 :: P :: inv :: cntp :: rest} := by
    simpa only [p2c0M, v0, v1, v2] using p2c0_run (s) c q1 q0 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp rest hcap hact
  have h1 : runInstructions p2c1P {s with pc := N 3144, memory := s.memory, stack := v2 :: c :: q1 :: q0 :: x0 :: x1 :: x2 :: x3 :: x4 :: n1 :: n2 :: n3 :: n4 :: P :: inv :: cntp :: rest} = some {s with pc := N 3153, memory := s.memory, stack := x2 :: v6 :: v5 :: c :: q1 :: q0 :: x0 :: x1 :: x2 :: x3 :: x4 :: n1 :: n2 :: n3 :: n4 :: P :: inv :: cntp :: rest} := by
    simpa only [p2c1M, v3, v4, v5, v6] using p2c1_run (s) v2 c q1 q0 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp rest hcap hact
  have h2 : runInstructions p2c2P {s with pc := N 3153, memory := s.memory, stack := x2 :: v6 :: v5 :: c :: q1 :: q0 :: x0 :: x1 :: x2 :: x3 :: x4 :: n1 :: n2 :: n3 :: n4 :: P :: inv :: cntp :: rest} = some {s with pc := N 3161, memory := s.memory, stack := q1 :: n1 :: v10 :: c :: q1 :: q0 :: x0 :: x1 :: x2 :: x3 :: x4 :: n1 :: n2 :: n3 :: n4 :: P :: inv :: cntp :: rest} := by
    simpa only [p2c2M, v7, v8, v9, v10] using p2c2_run (s) x2 v6 v5 c q1 q0 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp rest hcap hact
  have h3 : runInstructions p2c3P {s with pc := N 3161, memory := s.memory, stack := q1 :: n1 :: v10 :: c :: q1 :: q0 :: x0 :: x1 :: x2 :: x3 :: x4 :: n1 :: n2 :: n3 :: n4 :: P :: inv :: cntp :: rest} = some {s with pc := N 3170, memory := s.memory, stack := P :: c :: v14 :: q1 :: q0 :: x0 :: x1 :: x2 :: x3 :: x4 :: n1 :: n2 :: n3 :: n4 :: P :: inv :: cntp :: rest} := by
    simpa only [p2c3M, v11, v12, v13, v14] using p2c3_run (s) q1 n1 v10 c q1 q0 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp rest hcap hact
  have h4 : runInstructions p2c4P {s with pc := N 3170, memory := s.memory, stack := P :: c :: v14 :: q1 :: q0 :: x0 :: x1 :: x2 :: x3 :: x4 :: n1 :: n2 :: n3 :: n4 :: P :: inv :: cntp :: rest} = some {s with pc := N 3180, memory := s.memory, stack := v18 :: P :: v17 :: v14 :: q1 :: q0 :: x0 :: x1 :: x2 :: x3 :: x4 :: n1 :: n2 :: n3 :: n4 :: P :: inv :: cntp :: rest} := by
    simpa only [p2c4M, v15, v16, v17, v18] using p2c4_run (s) P c v14 q1 q0 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp rest hcap hact
  have h5 : runInstructions p2c5P {s with pc := N 3180, memory := s.memory, stack := v18 :: P :: v17 :: v14 :: q1 :: q0 :: x0 :: x1 :: x2 :: x3 :: x4 :: n1 :: n2 :: n3 :: n4 :: P :: inv :: cntp :: rest} = some {s with pc := N 3188, memory := s.memory, stack := v22 :: v20 :: v14 :: q1 :: q0 :: x0 :: x1 :: x2 :: x3 :: x4 :: n1 :: n2 :: n3 :: n4 :: P :: inv :: cntp :: rest} := by
    simpa only [p2c5M, v19, v20, v21, v22] using p2c5_run (s) v18 P v17 v14 q1 q0 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp rest hcap hact
  have h6 : runInstructions p2c6P {s with pc := N 3188, memory := s.memory, stack := v22 :: v20 :: v14 :: q1 :: q0 :: x0 :: x1 :: x2 :: x3 :: x4 :: n1 :: n2 :: n3 :: n4 :: P :: inv :: cntp :: rest} = some {s with pc := N 3196, memory := s.memory, stack := n1 :: P :: v25 :: v14 :: q1 :: q0 :: x0 :: x1 :: x2 :: x3 :: x4 :: n1 :: n2 :: n3 :: n4 :: P :: inv :: cntp :: rest} := by
    simpa only [p2c6M, v23, v24, v25] using p2c6_run (s) v22 v20 v14 q1 q0 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp rest hcap hact
  have h7 : runInstructions p2c7P {s with pc := N 3196, memory := s.memory, stack := n1 :: P :: v25 :: v14 :: q1 :: q0 :: x0 :: x1 :: x2 :: x3 :: x4 :: n1 :: n2 :: n3 :: n4 :: P :: inv :: cntp :: rest} = some {s with pc := N 3205, memory := s.memory, stack := v29 :: v27 :: v14 :: q1 :: q0 :: x0 :: x1 :: x2 :: x3 :: x4 :: n1 :: n2 :: n3 :: n4 :: P :: inv :: cntp :: rest} := by
    simpa only [p2c7M, v26, v27, v28, v29] using p2c7_run (s) n1 P v25 v14 q1 q0 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp rest hcap hact
  have h8 : runInstructions p2c8P {s with pc := N 3205, memory := s.memory, stack := v29 :: v27 :: v14 :: q1 :: q0 :: x0 :: x1 :: x2 :: x3 :: x4 :: n1 :: n2 :: n3 :: n4 :: P :: inv :: cntp :: rest} = some {s with pc := N 3212, memory := s.memory, stack := v31 :: v14 :: q1 :: q0 :: x0 :: x1 :: x2 :: x3 :: x4 :: n1 :: n2 :: n3 :: n4 :: P :: inv :: cntp :: rest} := by
    simpa only [p2c8M, v30, v31] using p2c8_run (s) v29 v27 v14 q1 q0 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp rest hcap hact
  exact (runInstructions_append_some _ _ _ _ _ h0 (runInstructions_append_some _ _ _ _ _ h1 (runInstructions_append_some _ _ _ _ _ h2 (runInstructions_append_some _ _ _ _ _ h3 (runInstructions_append_some _ _ _ _ _ h4 (runInstructions_append_some _ _ _ _ _ h5 (runInstructions_append_some _ _ _ _ _ h6 (runInstructions_append_some _ _ _ _ _ h7 h8))))))))

def prCol2_o0 (c q1 q0 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp b0 b1 b2 n0 : W) : W :=
  (UInt256.mulMod (N 2048) ((UInt256.mulMod (UInt256.shiftRight (inv * ((q1 * n1) + ((q0 * n2) + ((x2 * b0) + ((x1 * b1) + ((x0 * b2) + c)))))) (N 16)) n0 P) + ((UInt256.mulMod q1 n1 P) + ((UInt256.mulMod q0 n2 P) + ((UInt256.mulMod x2 b0 P) + ((UInt256.mulMod x1 b1 P) + ((UInt256.mulMod x0 b2 P) + c)))))) P)

def prCol2_o1 (c q1 q0 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp b0 b1 b2 n0 : W) : W :=
  (UInt256.shiftRight (inv * ((q1 * n1) + ((q0 * n2) + ((x2 * b0) + ((x1 * b1) + ((x0 * b2) + c)))))) (N 16))

theorem prCol2_eq (s : State) (c q1 q0 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp b0 b1 b2 n0 : W) (rest : List W)
    (h_b0 : MachineState.readWord s.memory 0 = b0)
    (h_b1 : MachineState.readWord s.memory 32 = b1)
    (h_b2 : MachineState.readWord s.memory 64 = b2)
    (h_n0 : MachineState.readWord s.memory 160 = n0) :
    prCol2Model s c q1 q0 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp rest =
      {s with pc := N 3212, stack := (prCol2_o0 c q1 q0 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp b0 b1 b2 n0) :: (prCol2_o1 c q1 q0 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp b0 b1 b2 n0) :: q1 :: q0 :: x0 :: x1 :: x2 :: x3 :: x4 :: n1 :: n2 :: n3 :: n4 :: P :: inv :: cntp :: rest} := by
  simp only [prCol2Model, prCol2_o0, prCol2_o1, h_b0, h_b1, h_b2, h_n0]

/-! ## prCol3: pc 3342..3441, 87 instructions -/

def p3c0P : List Instr :=
  [.op (.Dup dA0),
   .push 1 96,
   .op .MLOAD,
   .op (.Dup dA6),
   .op .MUL,
   .op .ADD,
   .push 1 64,
   .op .MLOAD]

def p3c0M (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 : W) (rest : List W) : State :=
  let v0 : W := MachineState.readWord s.memory 96
  let v1 : W := x4 * v0
  let v2 : W := v1 + x0
  let v3 : W := MachineState.readWord s.memory 64
  {s with pc := N 3222, memory := s.memory, stack := v3 :: v2 :: x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: rest}

theorem p3c0_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions p3c0P {s with pc := N 3212, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: rest} =
      some (p3c0M s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 rest) := by
  have hc (j : Nat) (hj : j ≤ 32) : rest.length + j < 1024 := by omega
  have hcr : rest.length < 1024 := by omega
  have ha96 : (96 : W).toNat = 96 := rfl
  have hf96 := activeWords_fix s 96 32 (by decide) (by norm_num) hact
  have ha64 : (64 : W).toNat = 64 := rfl
  have hf64 := activeWords_fix s 64 32 (by decide) (by norm_num) hact
  simp [hz, hzn, p3c0P, p3c0M, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, ofNat_sub_ofNat, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, hc, hcr, ha96, hf96, ha64, hf64]

def p3c1P : List Instr :=
  [.op (.Dup dA7),
   .op .MUL,
   .op .ADD,
   .push 1 32,
   .op .MLOAD,
   .op (.Dup dA8),
   .op .MUL,
   .op .ADD]

def p3c1M (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 : W) (rest : List W) : State :=
  let v0 : W := x7 * x0
  let v1 : W := v0 + x1
  let v2 : W := MachineState.readWord s.memory 32
  let v3 : W := x8 * v2
  let v4 : W := v3 + v1
  {s with pc := N 3231, memory := s.memory, stack := v4 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: rest}

theorem p3c1_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions p3c1P {s with pc := N 3222, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: rest} =
      some (p3c1M s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 rest) := by
  have hc (j : Nat) (hj : j ≤ 32) : rest.length + j < 1024 := by omega
  have hcr : rest.length < 1024 := by omega
  have ha32 : (32 : W).toNat = 32 := rfl
  have hf32 := activeWords_fix s 32 32 (by decide) (by norm_num) hact
  simp [hz, hzn, p3c1P, p3c1M, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, ofNat_sub_ofNat, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, hc, hcr, ha32, hf32]

def p3c2P : List Instr :=
  [.push 0 0,
   .op .MLOAD,
   .op (.Dup dA9),
   .op .MUL,
   .op .ADD,
   .op (.Dup dA12),
   .op (.Dup dA5),
   .op .MUL]

def p3c2M (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 : W) (rest : List W) : State :=
  let v0 : W := MachineState.readWord s.memory 0
  let v1 : W := x8 * v0
  let v2 : W := v1 + x0
  let v3 : W := x4 * x12
  {s with pc := N 3239, memory := s.memory, stack := v3 :: v2 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: rest}

theorem p3c2_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions p3c2P {s with pc := N 3231, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: rest} =
      some (p3c2M s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 rest) := by
  have hc (j : Nat) (hj : j ≤ 32) : rest.length + j < 1024 := by omega
  have hcr : rest.length < 1024 := by omega
  have ha0 : (0 : W).toNat = 0 := rfl
  have hf0 := activeWords_fix s 0 32 (by decide) (by norm_num) hact
  simp [hz, hzn, p3c2P, p3c2M, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, ofNat_sub_ofNat, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, hc, hcr, ha0, hf0]

def p3c3P : List Instr :=
  [.op .ADD,
   .op (.Dup dA11),
   .op (.Dup dA4),
   .op .MUL,
   .op .ADD,
   .op (.Dup dA10),
   .op (.Dup dA3),
   .op .MUL]

def p3c3M (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 : W) (rest : List W) : State :=
  let v0 : W := x0 + x1
  let v1 : W := x4 * x12
  let v2 : W := v1 + v0
  let v3 : W := x3 * x11
  {s with pc := N 3247, memory := s.memory, stack := v3 :: v2 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: rest}

theorem p3c3_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions p3c3P {s with pc := N 3239, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: rest} =
      some (p3c3M s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 rest) := by
  have hc (j : Nat) (hj : j ≤ 32) : rest.length + j < 1024 := by omega
  have hcr : rest.length < 1024 := by omega
  simp [hz, hzn, p3c3P, p3c3M, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, ofNat_sub_ofNat, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, hc, hcr]

def p3c4P : List Instr :=
  [.op .ADD,
   .op (.Dup dA15),
   .op .MUL,
   .push 1 16,
   .op .SHR,
   .op (.Swap sA0),
   .op (.Dup dA14)]

def p3c4M (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 : W) (rest : List W) : State :=
  let v0 : W := x0 + x1
  let v1 : W := x16 * v0
  let v2 : W := UInt256.shiftRight v1 (N 16)
  {s with pc := N 3255, memory := s.memory, stack := x15 :: x2 :: v2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: rest}

theorem p3c4_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions p3c4P {s with pc := N 3247, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: rest} =
      some (p3c4M s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 rest) := by
  have hc (j : Nat) (hj : j ≤ 31) : rest.length + j < 1024 := by omega
  have hcr : rest.length < 1024 := by omega
  simp [hz, hzn, p3c4P, p3c4M, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, ofNat_sub_ofNat, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, hc, hcr]

def p3c5P : List Instr :=
  [.push 1 96,
   .op .MLOAD,
   .op (.Dup dA7),
   .op .MULMOD,
   .op .ADD,
   .op (.Dup dA14),
   .push 1 64,
   .op .MLOAD]

def p3c5M (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 : W) (rest : List W) : State :=
  let v0 : W := MachineState.readWord s.memory 96
  let v1 : W := UInt256.mulMod x6 v0 x0
  let v2 : W := v1 + x1
  let v3 : W := MachineState.readWord s.memory 64
  {s with pc := N 3265, memory := s.memory, stack := v3 :: x15 :: v2 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: rest}

theorem p3c5_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions p3c5P {s with pc := N 3255, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: rest} =
      some (p3c5M s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 rest) := by
  have hc (j : Nat) (hj : j ≤ 33) : rest.length + j < 1024 := by omega
  have hcr : rest.length < 1024 := by omega
  have ha96 : (96 : W).toNat = 96 := rfl
  have hf96 := activeWords_fix s 96 32 (by decide) (by norm_num) hact
  have ha64 : (64 : W).toNat = 64 := rfl
  have hf64 := activeWords_fix s 64 32 (by decide) (by norm_num) hact
  simp [hz, hzn, p3c5P, p3c5M, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, ofNat_sub_ofNat, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, hc, hcr, ha96, hf96, ha64, hf64]

def p3c6P : List Instr :=
  [.op (.Dup dA8),
   .op .MULMOD,
   .op .ADD,
   .op (.Dup dA14),
   .push 1 32,
   .op .MLOAD,
   .op (.Dup dA9),
   .op .MULMOD]

def p3c6M (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 : W) (rest : List W) : State :=
  let v0 : W := UInt256.mulMod x8 x0 x1
  let v1 : W := v0 + x2
  let v2 : W := MachineState.readWord s.memory 32
  let v3 : W := UInt256.mulMod x9 v2 x16
  {s with pc := N 3274, memory := s.memory, stack := v3 :: v1 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: x18 :: rest}

theorem p3c6_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions p3c6P {s with pc := N 3265, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: x18 :: rest} =
      some (p3c6M s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 rest) := by
  have hc (j : Nat) (hj : j ≤ 33) : rest.length + j < 1024 := by omega
  have hcr : rest.length < 1024 := by omega
  have ha32 : (32 : W).toNat = 32 := rfl
  have hf32 := activeWords_fix s 32 32 (by decide) (by norm_num) hact
  simp [hz, hzn, p3c6P, p3c6M, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, ofNat_sub_ofNat, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, hc, hcr, ha32, hf32]

def p3c7P : List Instr :=
  [.op .ADD,
   .op (.Dup dA14),
   .push 0 0,
   .op .MLOAD,
   .op (.Dup dA10),
   .op .MULMOD,
   .op .ADD,
   .op (.Dup dA14)]

def p3c7M (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 : W) (rest : List W) : State :=
  let v0 : W := x0 + x1
  let v1 : W := MachineState.readWord s.memory 0
  let v2 : W := UInt256.mulMod x9 v1 x15
  let v3 : W := v2 + v0
  {s with pc := N 3282, memory := s.memory, stack := x15 :: v3 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: rest}

theorem p3c7_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions p3c7P {s with pc := N 3274, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: rest} =
      some (p3c7M s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 rest) := by
  have hc (j : Nat) (hj : j ≤ 33) : rest.length + j < 1024 := by omega
  have hcr : rest.length < 1024 := by omega
  have ha0 : (0 : W).toNat = 0 := rfl
  have hf0 := activeWords_fix s 0 32 (by decide) (by norm_num) hact
  simp [hz, hzn, p3c7P, p3c7M, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, ofNat_sub_ofNat, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, hc, hcr, ha0, hf0]

def p3c8P : List Instr :=
  [.op (.Dup dA13),
   .op (.Dup dA6),
   .op .MULMOD,
   .op .ADD,
   .op (.Dup dA14),
   .op (.Dup dA12),
   .op (.Dup dA5),
   .op .MULMOD]

def p3c8M (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 : W) (rest : List W) : State :=
  let v0 : W := UInt256.mulMod x5 x13 x0
  let v1 : W := v0 + x1
  let v2 : W := UInt256.mulMod x4 x12 x15
  {s with pc := N 3290, memory := s.memory, stack := v2 :: v1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: rest}

theorem p3c8_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions p3c8P {s with pc := N 3282, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: rest} =
      some (p3c8M s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 rest) := by
  have hc (j : Nat) (hj : j ≤ 33) : rest.length + j < 1024 := by omega
  have hcr : rest.length < 1024 := by omega
  simp [hz, hzn, p3c8P, p3c8M, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, ofNat_sub_ofNat, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, hc, hcr]

def p3c9P : List Instr :=
  [.op .ADD,
   .op (.Dup dA14),
   .op (.Dup dA11),
   .op (.Dup dA4),
   .op .MULMOD,
   .op .ADD,
   .op (.Dup dA14)]

def p3c9M (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 : W) (rest : List W) : State :=
  let v0 : W := x0 + x1
  let v1 : W := UInt256.mulMod x3 x11 x15
  let v2 : W := v1 + v0
  {s with pc := N 3297, memory := s.memory, stack := x15 :: v2 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: rest}

theorem p3c9_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions p3c9P {s with pc := N 3290, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: rest} =
      some (p3c9M s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 rest) := by
  have hc (j : Nat) (hj : j ≤ 33) : rest.length + j < 1024 := by omega
  have hcr : rest.length < 1024 := by omega
  simp [hz, hzn, p3c9P, p3c9M, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, ofNat_sub_ofNat, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, hc, hcr]

def p3c10P : List Instr :=
  [.push 1 160,
   .op .MLOAD,
   .op (.Dup dA3),
   .op .MULMOD,
   .op .ADD,
   .op (.Dup dA14),
   .op (.Swap sA0)]

def p3c10M (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 : W) (rest : List W) : State :=
  let v0 : W := MachineState.readWord s.memory 160
  let v1 : W := UInt256.mulMod x2 v0 x0
  let v2 : W := v1 + x1
  {s with pc := N 3305, memory := s.memory, stack := v2 :: x15 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: rest}

theorem p3c10_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions p3c10P {s with pc := N 3297, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: rest} =
      some (p3c10M s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 rest) := by
  have hc (j : Nat) (hj : j ≤ 33) : rest.length + j < 1024 := by omega
  have hcr : rest.length < 1024 := by omega
  have ha160 : (160 : W).toNat = 160 := rfl
  have hf160 := activeWords_fix s 160 32 (by decide) (by norm_num) hact
  simp [hz, hzn, p3c10P, p3c10M, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, ofNat_sub_ofNat, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, hc, hcr, ha160, hf160]

def p3c11P : List Instr :=
  [.push 2 2048,
   .op .MULMOD]

def p3c11M (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 : W) (rest : List W) : State :=
  let v0 : W := UInt256.mulMod (N 2048) x0 x1
  {s with pc := N 3309, memory := s.memory, stack := v0 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: rest}

theorem p3c11_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions p3c11P {s with pc := N 3305, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: rest} =
      some (p3c11M s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 rest) := by
  have hc (j : Nat) (hj : j ≤ 32) : rest.length + j < 1024 := by omega
  have hcr : rest.length < 1024 := by omega
  simp [hz, hzn, p3c11P, p3c11M, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, ofNat_sub_ofNat, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, hc, hcr]

def prCol3Program : List Instr :=
  [.op (.Dup dA0),
   .push 1 96,
   .op .MLOAD,
   .op (.Dup dA6),
   .op .MUL,
   .op .ADD,
   .push 1 64,
   .op .MLOAD,
   .op (.Dup dA7),
   .op .MUL,
   .op .ADD,
   .push 1 32,
   .op .MLOAD,
   .op (.Dup dA8),
   .op .MUL,
   .op .ADD,
   .push 0 0,
   .op .MLOAD,
   .op (.Dup dA9),
   .op .MUL,
   .op .ADD,
   .op (.Dup dA12),
   .op (.Dup dA5),
   .op .MUL,
   .op .ADD,
   .op (.Dup dA11),
   .op (.Dup dA4),
   .op .MUL,
   .op .ADD,
   .op (.Dup dA10),
   .op (.Dup dA3),
   .op .MUL,
   .op .ADD,
   .op (.Dup dA15),
   .op .MUL,
   .push 1 16,
   .op .SHR,
   .op (.Swap sA0),
   .op (.Dup dA14),
   .push 1 96,
   .op .MLOAD,
   .op (.Dup dA7),
   .op .MULMOD,
   .op .ADD,
   .op (.Dup dA14),
   .push 1 64,
   .op .MLOAD,
   .op (.Dup dA8),
   .op .MULMOD,
   .op .ADD,
   .op (.Dup dA14),
   .push 1 32,
   .op .MLOAD,
   .op (.Dup dA9),
   .op .MULMOD,
   .op .ADD,
   .op (.Dup dA14),
   .push 0 0,
   .op .MLOAD,
   .op (.Dup dA10),
   .op .MULMOD,
   .op .ADD,
   .op (.Dup dA14),
   .op (.Dup dA13),
   .op (.Dup dA6),
   .op .MULMOD,
   .op .ADD,
   .op (.Dup dA14),
   .op (.Dup dA12),
   .op (.Dup dA5),
   .op .MULMOD,
   .op .ADD,
   .op (.Dup dA14),
   .op (.Dup dA11),
   .op (.Dup dA4),
   .op .MULMOD,
   .op .ADD,
   .op (.Dup dA14),
   .push 1 160,
   .op .MLOAD,
   .op (.Dup dA3),
   .op .MULMOD,
   .op .ADD,
   .op (.Dup dA14),
   .op (.Swap sA0),
   .push 2 2048,
   .op .MULMOD]

def prCol3Model (s : State) (c q2 q1 q0 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp : W) (rest : List W) : State :=
  let v0 : W := MachineState.readWord s.memory 96
  let v1 : W := x0 * v0
  let v2 : W := v1 + c
  let v3 : W := MachineState.readWord s.memory 64
  let v4 : W := x1 * v3
  let v5 : W := v4 + v2
  let v6 : W := MachineState.readWord s.memory 32
  let v7 : W := x2 * v6
  let v8 : W := v7 + v5
  let v9 : W := MachineState.readWord s.memory 0
  let v10 : W := x3 * v9
  let v11 : W := v10 + v8
  let v12 : W := q0 * n3
  let v13 : W := v12 + v11
  let v14 : W := q1 * n2
  let v15 : W := v14 + v13
  let v16 : W := q2 * n1
  let v17 : W := v16 + v15
  let v18 : W := inv * v17
  let v19 : W := UInt256.shiftRight v18 (N 16)
  let v20 : W := MachineState.readWord s.memory 96
  let v21 : W := UInt256.mulMod x0 v20 P
  let v22 : W := v21 + c
  let v23 : W := MachineState.readWord s.memory 64
  let v24 : W := UInt256.mulMod x1 v23 P
  let v25 : W := v24 + v22
  let v26 : W := MachineState.readWord s.memory 32
  let v27 : W := UInt256.mulMod x2 v26 P
  let v28 : W := v27 + v25
  let v29 : W := MachineState.readWord s.memory 0
  let v30 : W := UInt256.mulMod x3 v29 P
  let v31 : W := v30 + v28
  let v32 : W := UInt256.mulMod q0 n3 P
  let v33 : W := v32 + v31
  let v34 : W := UInt256.mulMod q1 n2 P
  let v35 : W := v34 + v33
  let v36 : W := UInt256.mulMod q2 n1 P
  let v37 : W := v36 + v35
  let v38 : W := MachineState.readWord s.memory 160
  let v39 : W := UInt256.mulMod v19 v38 P
  let v40 : W := v39 + v37
  let v41 : W := UInt256.mulMod (N 2048) v40 P
  {s with pc := N 3309, memory := s.memory, stack := v41 :: v19 :: q2 :: q1 :: q0 :: x0 :: x1 :: x2 :: x3 :: x4 :: n1 :: n2 :: n3 :: n4 :: P :: inv :: cntp :: rest}

theorem prCol3_run (s : State) (c q2 q1 q0 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions prCol3Program {s with pc := N 3212, stack := c :: q2 :: q1 :: q0 :: x0 :: x1 :: x2 :: x3 :: x4 :: n1 :: n2 :: n3 :: n4 :: P :: inv :: cntp :: rest} =
      some (prCol3Model s c q2 q1 q0 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp rest) := by
  let v0 : W := MachineState.readWord s.memory 96
  let v1 : W := x0 * v0
  let v2 : W := v1 + c
  let v3 : W := MachineState.readWord s.memory 64
  let v4 : W := x1 * v3
  let v5 : W := v4 + v2
  let v6 : W := MachineState.readWord s.memory 32
  let v7 : W := x2 * v6
  let v8 : W := v7 + v5
  let v9 : W := MachineState.readWord s.memory 0
  let v10 : W := x3 * v9
  let v11 : W := v10 + v8
  let v12 : W := q0 * n3
  let v13 : W := v12 + v11
  let v14 : W := q1 * n2
  let v15 : W := v14 + v13
  let v16 : W := q2 * n1
  let v17 : W := v16 + v15
  let v18 : W := inv * v17
  let v19 : W := UInt256.shiftRight v18 (N 16)
  let v20 : W := MachineState.readWord s.memory 96
  let v21 : W := UInt256.mulMod x0 v20 P
  let v22 : W := v21 + c
  let v23 : W := MachineState.readWord s.memory 64
  let v24 : W := UInt256.mulMod x1 v23 P
  let v25 : W := v24 + v22
  let v26 : W := MachineState.readWord s.memory 32
  let v27 : W := UInt256.mulMod x2 v26 P
  let v28 : W := v27 + v25
  let v29 : W := MachineState.readWord s.memory 0
  let v30 : W := UInt256.mulMod x3 v29 P
  let v31 : W := v30 + v28
  let v32 : W := UInt256.mulMod q0 n3 P
  let v33 : W := v32 + v31
  let v34 : W := UInt256.mulMod q1 n2 P
  let v35 : W := v34 + v33
  let v36 : W := UInt256.mulMod q2 n1 P
  let v37 : W := v36 + v35
  let v38 : W := MachineState.readWord s.memory 160
  let v39 : W := UInt256.mulMod v19 v38 P
  let v40 : W := v39 + v37
  let v41 : W := UInt256.mulMod (N 2048) v40 P
  have h0 : runInstructions p3c0P {s with pc := N 3212, memory := s.memory, stack := c :: q2 :: q1 :: q0 :: x0 :: x1 :: x2 :: x3 :: x4 :: n1 :: n2 :: n3 :: n4 :: P :: inv :: cntp :: rest} = some {s with pc := N 3222, memory := s.memory, stack := v3 :: v2 :: c :: q2 :: q1 :: q0 :: x0 :: x1 :: x2 :: x3 :: x4 :: n1 :: n2 :: n3 :: n4 :: P :: inv :: cntp :: rest} := by
    simpa only [p3c0M, v0, v1, v2, v3] using p3c0_run (s) c q2 q1 q0 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp rest hcap hact
  have h1 : runInstructions p3c1P {s with pc := N 3222, memory := s.memory, stack := v3 :: v2 :: c :: q2 :: q1 :: q0 :: x0 :: x1 :: x2 :: x3 :: x4 :: n1 :: n2 :: n3 :: n4 :: P :: inv :: cntp :: rest} = some {s with pc := N 3231, memory := s.memory, stack := v8 :: c :: q2 :: q1 :: q0 :: x0 :: x1 :: x2 :: x3 :: x4 :: n1 :: n2 :: n3 :: n4 :: P :: inv :: cntp :: rest} := by
    simpa only [p3c1M, v4, v5, v6, v7, v8] using p3c1_run (s) v3 v2 c q2 q1 q0 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp rest hcap hact
  have h2 : runInstructions p3c2P {s with pc := N 3231, memory := s.memory, stack := v8 :: c :: q2 :: q1 :: q0 :: x0 :: x1 :: x2 :: x3 :: x4 :: n1 :: n2 :: n3 :: n4 :: P :: inv :: cntp :: rest} = some {s with pc := N 3239, memory := s.memory, stack := v12 :: v11 :: c :: q2 :: q1 :: q0 :: x0 :: x1 :: x2 :: x3 :: x4 :: n1 :: n2 :: n3 :: n4 :: P :: inv :: cntp :: rest} := by
    simpa only [p3c2M, v9, v10, v11, v12] using p3c2_run (s) v8 c q2 q1 q0 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp rest hcap hact
  have h3 : runInstructions p3c3P {s with pc := N 3239, memory := s.memory, stack := v12 :: v11 :: c :: q2 :: q1 :: q0 :: x0 :: x1 :: x2 :: x3 :: x4 :: n1 :: n2 :: n3 :: n4 :: P :: inv :: cntp :: rest} = some {s with pc := N 3247, memory := s.memory, stack := v16 :: v15 :: c :: q2 :: q1 :: q0 :: x0 :: x1 :: x2 :: x3 :: x4 :: n1 :: n2 :: n3 :: n4 :: P :: inv :: cntp :: rest} := by
    simpa only [p3c3M, v13, v14, v15, v16] using p3c3_run (s) v12 v11 c q2 q1 q0 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp rest hcap hact
  have h4 : runInstructions p3c4P {s with pc := N 3247, memory := s.memory, stack := v16 :: v15 :: c :: q2 :: q1 :: q0 :: x0 :: x1 :: x2 :: x3 :: x4 :: n1 :: n2 :: n3 :: n4 :: P :: inv :: cntp :: rest} = some {s with pc := N 3255, memory := s.memory, stack := P :: c :: v19 :: q2 :: q1 :: q0 :: x0 :: x1 :: x2 :: x3 :: x4 :: n1 :: n2 :: n3 :: n4 :: P :: inv :: cntp :: rest} := by
    simpa only [p3c4M, v17, v18, v19] using p3c4_run (s) v16 v15 c q2 q1 q0 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp rest hcap hact
  have h5 : runInstructions p3c5P {s with pc := N 3255, memory := s.memory, stack := P :: c :: v19 :: q2 :: q1 :: q0 :: x0 :: x1 :: x2 :: x3 :: x4 :: n1 :: n2 :: n3 :: n4 :: P :: inv :: cntp :: rest} = some {s with pc := N 3265, memory := s.memory, stack := v23 :: P :: v22 :: v19 :: q2 :: q1 :: q0 :: x0 :: x1 :: x2 :: x3 :: x4 :: n1 :: n2 :: n3 :: n4 :: P :: inv :: cntp :: rest} := by
    simpa only [p3c5M, v20, v21, v22, v23] using p3c5_run (s) P c v19 q2 q1 q0 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp rest hcap hact
  have h6 : runInstructions p3c6P {s with pc := N 3265, memory := s.memory, stack := v23 :: P :: v22 :: v19 :: q2 :: q1 :: q0 :: x0 :: x1 :: x2 :: x3 :: x4 :: n1 :: n2 :: n3 :: n4 :: P :: inv :: cntp :: rest} = some {s with pc := N 3274, memory := s.memory, stack := v27 :: v25 :: v19 :: q2 :: q1 :: q0 :: x0 :: x1 :: x2 :: x3 :: x4 :: n1 :: n2 :: n3 :: n4 :: P :: inv :: cntp :: rest} := by
    simpa only [p3c6M, v24, v25, v26, v27] using p3c6_run (s) v23 P v22 v19 q2 q1 q0 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp rest hcap hact
  have h7 : runInstructions p3c7P {s with pc := N 3274, memory := s.memory, stack := v27 :: v25 :: v19 :: q2 :: q1 :: q0 :: x0 :: x1 :: x2 :: x3 :: x4 :: n1 :: n2 :: n3 :: n4 :: P :: inv :: cntp :: rest} = some {s with pc := N 3282, memory := s.memory, stack := P :: v31 :: v19 :: q2 :: q1 :: q0 :: x0 :: x1 :: x2 :: x3 :: x4 :: n1 :: n2 :: n3 :: n4 :: P :: inv :: cntp :: rest} := by
    simpa only [p3c7M, v28, v29, v30, v31] using p3c7_run (s) v27 v25 v19 q2 q1 q0 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp rest hcap hact
  have h8 : runInstructions p3c8P {s with pc := N 3282, memory := s.memory, stack := P :: v31 :: v19 :: q2 :: q1 :: q0 :: x0 :: x1 :: x2 :: x3 :: x4 :: n1 :: n2 :: n3 :: n4 :: P :: inv :: cntp :: rest} = some {s with pc := N 3290, memory := s.memory, stack := v34 :: v33 :: v19 :: q2 :: q1 :: q0 :: x0 :: x1 :: x2 :: x3 :: x4 :: n1 :: n2 :: n3 :: n4 :: P :: inv :: cntp :: rest} := by
    simpa only [p3c8M, v32, v33, v34] using p3c8_run (s) P v31 v19 q2 q1 q0 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp rest hcap hact
  have h9 : runInstructions p3c9P {s with pc := N 3290, memory := s.memory, stack := v34 :: v33 :: v19 :: q2 :: q1 :: q0 :: x0 :: x1 :: x2 :: x3 :: x4 :: n1 :: n2 :: n3 :: n4 :: P :: inv :: cntp :: rest} = some {s with pc := N 3297, memory := s.memory, stack := P :: v37 :: v19 :: q2 :: q1 :: q0 :: x0 :: x1 :: x2 :: x3 :: x4 :: n1 :: n2 :: n3 :: n4 :: P :: inv :: cntp :: rest} := by
    simpa only [p3c9M, v35, v36, v37] using p3c9_run (s) v34 v33 v19 q2 q1 q0 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp rest hcap hact
  have h10 : runInstructions p3c10P {s with pc := N 3297, memory := s.memory, stack := P :: v37 :: v19 :: q2 :: q1 :: q0 :: x0 :: x1 :: x2 :: x3 :: x4 :: n1 :: n2 :: n3 :: n4 :: P :: inv :: cntp :: rest} = some {s with pc := N 3305, memory := s.memory, stack := v40 :: P :: v19 :: q2 :: q1 :: q0 :: x0 :: x1 :: x2 :: x3 :: x4 :: n1 :: n2 :: n3 :: n4 :: P :: inv :: cntp :: rest} := by
    simpa only [p3c10M, v38, v39, v40] using p3c10_run (s) P v37 v19 q2 q1 q0 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp rest hcap hact
  have h11 : runInstructions p3c11P {s with pc := N 3305, memory := s.memory, stack := v40 :: P :: v19 :: q2 :: q1 :: q0 :: x0 :: x1 :: x2 :: x3 :: x4 :: n1 :: n2 :: n3 :: n4 :: P :: inv :: cntp :: rest} = some {s with pc := N 3309, memory := s.memory, stack := v41 :: v19 :: q2 :: q1 :: q0 :: x0 :: x1 :: x2 :: x3 :: x4 :: n1 :: n2 :: n3 :: n4 :: P :: inv :: cntp :: rest} := by
    simpa only [p3c11M, v41] using p3c11_run (s) v40 P v19 q2 q1 q0 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp rest hcap hact
  exact (runInstructions_append_some _ _ _ _ _ h0 (runInstructions_append_some _ _ _ _ _ h1 (runInstructions_append_some _ _ _ _ _ h2 (runInstructions_append_some _ _ _ _ _ h3 (runInstructions_append_some _ _ _ _ _ h4 (runInstructions_append_some _ _ _ _ _ h5 (runInstructions_append_some _ _ _ _ _ h6 (runInstructions_append_some _ _ _ _ _ h7 (runInstructions_append_some _ _ _ _ _ h8 (runInstructions_append_some _ _ _ _ _ h9 (runInstructions_append_some _ _ _ _ _ h10 h11)))))))))))

def prCol3_o0 (c q2 q1 q0 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp b0 b1 b2 b3 n0 : W) : W :=
  (UInt256.mulMod (N 2048) ((UInt256.mulMod (UInt256.shiftRight (inv * ((q2 * n1) + ((q1 * n2) + ((q0 * n3) + ((x3 * b0) + ((x2 * b1) + ((x1 * b2) + ((x0 * b3) + c)))))))) (N 16)) n0 P) + ((UInt256.mulMod q2 n1 P) + ((UInt256.mulMod q1 n2 P) + ((UInt256.mulMod q0 n3 P) + ((UInt256.mulMod x3 b0 P) + ((UInt256.mulMod x2 b1 P) + ((UInt256.mulMod x1 b2 P) + ((UInt256.mulMod x0 b3 P) + c)))))))) P)

def prCol3_o1 (c q2 q1 q0 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp b0 b1 b2 b3 n0 : W) : W :=
  (UInt256.shiftRight (inv * ((q2 * n1) + ((q1 * n2) + ((q0 * n3) + ((x3 * b0) + ((x2 * b1) + ((x1 * b2) + ((x0 * b3) + c)))))))) (N 16))

theorem prCol3_eq (s : State) (c q2 q1 q0 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp b0 b1 b2 b3 n0 : W) (rest : List W)
    (h_b0 : MachineState.readWord s.memory 0 = b0)
    (h_b1 : MachineState.readWord s.memory 32 = b1)
    (h_b2 : MachineState.readWord s.memory 64 = b2)
    (h_b3 : MachineState.readWord s.memory 96 = b3)
    (h_n0 : MachineState.readWord s.memory 160 = n0) :
    prCol3Model s c q2 q1 q0 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp rest =
      {s with pc := N 3309, stack := (prCol3_o0 c q2 q1 q0 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp b0 b1 b2 b3 n0) :: (prCol3_o1 c q2 q1 q0 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp b0 b1 b2 b3 n0) :: q2 :: q1 :: q0 :: x0 :: x1 :: x2 :: x3 :: x4 :: n1 :: n2 :: n3 :: n4 :: P :: inv :: cntp :: rest} := by
  simp only [prCol3Model, prCol3_o0, prCol3_o1, h_b0, h_b1, h_b2, h_b3, h_n0]

/-! ## prCol4: pc 3775..3901, 111 instructions -/

def p4c0P : List Instr :=
  [.op .JUMPDEST,
   .op (.Dup dA0),
   .op (.Dup dA15),
   .push 1 128,
   .op .MLOAD,
   .op (.Dup dA8),
   .op .MULMOD,
   .op .ADD]

def p4c0M (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 : W) (rest : List W) : State :=
  let v0 : W := MachineState.readWord s.memory 128
  let v1 : W := UInt256.mulMod x5 v0 x14
  let v2 : W := v1 + x0
  {s with pc := N 3640, memory := s.memory, stack := v2 :: x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: rest}

theorem p4c0_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions p4c0P {s with pc := N 3631, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: rest} =
      some (p4c0M s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 rest) := by
  have hc (j : Nat) (hj : j ≤ 34) : rest.length + j < 1024 := by omega
  have hcr : rest.length < 1024 := by omega
  have ha128 : (128 : W).toNat = 128 := rfl
  have hf128 := activeWords_fix s 128 32 (by decide) (by norm_num) hact
  simp [hz, hzn, p4c0P, p4c0M, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, ofNat_sub_ofNat, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, hc, hcr, ha128, hf128]

def p4c1P : List Instr :=
  [.op (.Dup dA15),
   .push 1 96,
   .op .MLOAD,
   .op (.Dup dA9),
   .op .MULMOD,
   .op .ADD,
   .op (.Dup dA15)]

def p4c1M (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 : W) (rest : List W) : State :=
  let v0 : W := MachineState.readWord s.memory 96
  let v1 : W := UInt256.mulMod x7 v0 x15
  let v2 : W := v1 + x0
  {s with pc := N 3648, memory := s.memory, stack := x15 :: v2 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: rest}

theorem p4c1_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions p4c1P {s with pc := N 3640, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: rest} =
      some (p4c1M s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 rest) := by
  have hc (j : Nat) (hj : j ≤ 34) : rest.length + j < 1024 := by omega
  have hcr : rest.length < 1024 := by omega
  have ha96 : (96 : W).toNat = 96 := rfl
  have hf96 := activeWords_fix s 96 32 (by decide) (by norm_num) hact
  simp [hz, hzn, p4c1P, p4c1M, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, ofNat_sub_ofNat, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, hc, hcr, ha96, hf96]

def p4c2P : List Instr :=
  [.push 1 64,
   .op .MLOAD,
   .op (.Dup dA10),
   .op .MULMOD,
   .op .ADD,
   .op (.Dup dA15),
   .push 1 32,
   .op .MLOAD]

def p4c2M (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 : W) (rest : List W) : State :=
  let v0 : W := MachineState.readWord s.memory 64
  let v1 : W := UInt256.mulMod x9 v0 x0
  let v2 : W := v1 + x1
  let v3 : W := MachineState.readWord s.memory 32
  {s with pc := N 3658, memory := s.memory, stack := v3 :: x16 :: v2 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: x18 :: rest}

theorem p4c2_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions p4c2P {s with pc := N 3648, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: x18 :: rest} =
      some (p4c2M s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 rest) := by
  have hc (j : Nat) (hj : j ≤ 34) : rest.length + j < 1024 := by omega
  have hcr : rest.length < 1024 := by omega
  have ha64 : (64 : W).toNat = 64 := rfl
  have hf64 := activeWords_fix s 64 32 (by decide) (by norm_num) hact
  have ha32 : (32 : W).toNat = 32 := rfl
  have hf32 := activeWords_fix s 32 32 (by decide) (by norm_num) hact
  simp [hz, hzn, p4c2P, p4c2M, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, ofNat_sub_ofNat, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, hc, hcr, ha64, hf64, ha32, hf32]

def p4c3P : List Instr :=
  [.op (.Dup dA11),
   .op .MULMOD,
   .op .ADD,
   .op (.Dup dA15),
   .push 0 0,
   .op .MLOAD,
   .op (.Dup dA12),
   .op .MULMOD]

def p4c3M (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 : W) (rest : List W) : State :=
  let v0 : W := UInt256.mulMod x11 x0 x1
  let v1 : W := v0 + x2
  let v2 : W := MachineState.readWord s.memory 0
  let v3 : W := UInt256.mulMod x12 v2 x17
  {s with pc := N 3666, memory := s.memory, stack := v3 :: v1 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: x18 :: x19 :: rest}

theorem p4c3_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions p4c3P {s with pc := N 3658, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: x18 :: x19 :: rest} =
      some (p4c3M s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 rest) := by
  have hc (j : Nat) (hj : j ≤ 34) : rest.length + j < 1024 := by omega
  have hcr : rest.length < 1024 := by omega
  have ha0 : (0 : W).toNat = 0 := rfl
  have hf0 := activeWords_fix s 0 32 (by decide) (by norm_num) hact
  simp [hz, hzn, p4c3P, p4c3M, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, ofNat_sub_ofNat, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, hc, hcr, ha0, hf0]

def p4c4P : List Instr :=
  [.op .ADD,
   .op (.Dup dA15),
   .op (.Dup dA15),
   .op (.Dup dA7),
   .op .MULMOD,
   .op .ADD,
   .op (.Dup dA15),
   .op (.Dup dA14)]

def p4c4M (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 : W) (rest : List W) : State :=
  let v0 : W := x0 + x1
  let v1 : W := UInt256.mulMod x6 x15 x16
  let v2 : W := v1 + v0
  {s with pc := N 3674, memory := s.memory, stack := x14 :: x16 :: v2 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: x18 :: rest}

theorem p4c4_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions p4c4P {s with pc := N 3666, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: x18 :: rest} =
      some (p4c4M s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 rest) := by
  have hc (j : Nat) (hj : j ≤ 34) : rest.length + j < 1024 := by omega
  have hcr : rest.length < 1024 := by omega
  simp [hz, hzn, p4c4P, p4c4M, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, ofNat_sub_ofNat, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, hc, hcr]

def p4c5P : List Instr :=
  [.op (.Dup dA6),
   .op .MULMOD,
   .op .ADD,
   .op (.Dup dA15),
   .op (.Dup dA13),
   .op (.Dup dA5),
   .op .MULMOD,
   .op .ADD]

def p4c5M (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 : W) (rest : List W) : State :=
  let v0 : W := UInt256.mulMod x6 x0 x1
  let v1 : W := v0 + x2
  let v2 : W := UInt256.mulMod x5 x14 x17
  let v3 : W := v2 + v1
  {s with pc := N 3682, memory := s.memory, stack := v3 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: x18 :: x19 :: rest}

theorem p4c5_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions p4c5P {s with pc := N 3674, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: x18 :: x19 :: rest} =
      some (p4c5M s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 rest) := by
  have hc (j : Nat) (hj : j ≤ 34) : rest.length + j < 1024 := by omega
  have hcr : rest.length < 1024 := by omega
  simp [hz, hzn, p4c5P, p4c5M, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, ofNat_sub_ofNat, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, hc, hcr]

def p4c6P : List Instr :=
  [.op (.Dup dA15),
   .op (.Dup dA12),
   .op (.Dup dA4),
   .op .MULMOD,
   .op .ADD,
   .op (.Swap sA0),
   .push 1 128,
   .op .MLOAD]

def p4c6M (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 : W) (rest : List W) : State :=
  let v0 : W := UInt256.mulMod x2 x11 x15
  let v1 : W := v0 + x0
  let v2 : W := MachineState.readWord s.memory 128
  {s with pc := N 3691, memory := s.memory, stack := v2 :: x1 :: v1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: rest}

theorem p4c6_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions p4c6P {s with pc := N 3682, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: rest} =
      some (p4c6M s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 rest) := by
  have hc (j : Nat) (hj : j ≤ 34) : rest.length + j < 1024 := by omega
  have hcr : rest.length < 1024 := by omega
  have ha128 : (128 : W).toNat = 128 := rfl
  have hf128 := activeWords_fix s 128 32 (by decide) (by norm_num) hact
  simp [hz, hzn, p4c6P, p4c6M, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, ofNat_sub_ofNat, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, hc, hcr, ha128, hf128]

def p4c7P : List Instr :=
  [.op (.Dup dA7),
   .op .MUL,
   .op .ADD,
   .push 1 96,
   .op .MLOAD,
   .op (.Dup dA8),
   .op .MUL,
   .op .ADD]

def p4c7M (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 : W) (rest : List W) : State :=
  let v0 : W := x7 * x0
  let v1 : W := v0 + x1
  let v2 : W := MachineState.readWord s.memory 96
  let v3 : W := x8 * v2
  let v4 : W := v3 + v1
  {s with pc := N 3700, memory := s.memory, stack := v4 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: x18 :: rest}

theorem p4c7_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions p4c7P {s with pc := N 3691, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: x18 :: rest} =
      some (p4c7M s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 rest) := by
  have hc (j : Nat) (hj : j ≤ 33) : rest.length + j < 1024 := by omega
  have hcr : rest.length < 1024 := by omega
  have ha96 : (96 : W).toNat = 96 := rfl
  have hf96 := activeWords_fix s 96 32 (by decide) (by norm_num) hact
  simp [hz, hzn, p4c7P, p4c7M, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, ofNat_sub_ofNat, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, hc, hcr, ha96, hf96]

def p4c8P : List Instr :=
  [.push 1 64,
   .op .MLOAD,
   .op (.Dup dA9),
   .op .MUL,
   .op .ADD,
   .push 1 32,
   .op .MLOAD,
   .op (.Dup dA10)]

def p4c8M (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 : W) (rest : List W) : State :=
  let v0 : W := MachineState.readWord s.memory 64
  let v1 : W := x8 * v0
  let v2 : W := v1 + x0
  let v3 : W := MachineState.readWord s.memory 32
  {s with pc := N 3710, memory := s.memory, stack := x9 :: v3 :: v2 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: rest}

theorem p4c8_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions p4c8P {s with pc := N 3700, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: rest} =
      some (p4c8M s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 rest) := by
  have hc (j : Nat) (hj : j ≤ 33) : rest.length + j < 1024 := by omega
  have hcr : rest.length < 1024 := by omega
  have ha64 : (64 : W).toNat = 64 := rfl
  have hf64 := activeWords_fix s 64 32 (by decide) (by norm_num) hact
  have ha32 : (32 : W).toNat = 32 := rfl
  have hf32 := activeWords_fix s 32 32 (by decide) (by norm_num) hact
  simp [hz, hzn, p4c8P, p4c8M, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, ofNat_sub_ofNat, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, hc, hcr, ha64, hf64, ha32, hf32]

def p4c9P : List Instr :=
  [.op .MUL,
   .op .ADD,
   .push 0 0,
   .op .MLOAD,
   .op (.Dup dA11),
   .op .MUL,
   .op .ADD,
   .op (.Dup dA14)]

def p4c9M (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 : W) (rest : List W) : State :=
  let v0 : W := x0 * x1
  let v1 : W := v0 + x2
  let v2 : W := MachineState.readWord s.memory 0
  let v3 : W := x12 * v2
  let v4 : W := v3 + v1
  {s with pc := N 3718, memory := s.memory, stack := x16 :: v4 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: x18 :: x19 :: rest}

theorem p4c9_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions p4c9P {s with pc := N 3710, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: x18 :: x19 :: rest} =
      some (p4c9M s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 rest) := by
  have hc (j : Nat) (hj : j ≤ 33) : rest.length + j < 1024 := by omega
  have hcr : rest.length < 1024 := by omega
  have ha0 : (0 : W).toNat = 0 := rfl
  have hf0 := activeWords_fix s 0 32 (by decide) (by norm_num) hact
  simp [hz, hzn, p4c9P, p4c9M, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, ofNat_sub_ofNat, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, hc, hcr, ha0, hf0]

def p4c10P : List Instr :=
  [.op (.Dup dA6),
   .op .MUL,
   .op .ADD,
   .op (.Dup dA13),
   .op (.Dup dA5),
   .op .MUL,
   .op .ADD,
   .op (.Dup dA12)]

def p4c10M (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 : W) (rest : List W) : State :=
  let v0 : W := x6 * x0
  let v1 : W := v0 + x1
  let v2 : W := x5 * x14
  let v3 : W := v2 + v1
  {s with pc := N 3726, memory := s.memory, stack := x13 :: v3 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: x18 :: rest}

theorem p4c10_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions p4c10P {s with pc := N 3718, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: x18 :: rest} =
      some (p4c10M s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 rest) := by
  have hc (j : Nat) (hj : j ≤ 33) : rest.length + j < 1024 := by omega
  have hcr : rest.length < 1024 := by omega
  simp [hz, hzn, p4c10P, p4c10M, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, ofNat_sub_ofNat, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, hc, hcr]

def p4c11P : List Instr :=
  [.op (.Dup dA4),
   .op .MUL,
   .op .ADD,
   .op (.Dup dA11),
   .op (.Dup dA3),
   .op .MUL,
   .op .ADD]

def p4c11M (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 : W) (rest : List W) : State :=
  let v0 : W := x4 * x0
  let v1 : W := v0 + x1
  let v2 : W := x3 * x12
  let v3 : W := v2 + v1
  {s with pc := N 3733, memory := s.memory, stack := v3 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: x18 :: rest}

theorem p4c11_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions p4c11P {s with pc := N 3726, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: x18 :: rest} =
      some (p4c11M s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 rest) := by
  have hc (j : Nat) (hj : j ≤ 33) : rest.length + j < 1024 := by omega
  have hcr : rest.length < 1024 := by omega
  simp [hz, hzn, p4c11P, p4c11M, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, ofNat_sub_ofNat, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, hc, hcr]

def p4c12P : List Instr :=
  [.push 1 192,
   .op .MLOAD,
   .op .MUL,
   .push 1 16,
   .op .SHR,
   .op (.Swap sA4),
   .op .POP,
   .op (.Dup dA14)]

def p4c12M (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 : W) (rest : List W) : State :=
  let v0 : W := MachineState.readWord s.memory 192
  let v1 : W := v0 * x0
  let v2 : W := UInt256.shiftRight v1 (N 16)
  {s with pc := N 3743, memory := s.memory, stack := x15 :: x1 :: x2 :: x3 :: x4 :: v2 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: rest}

theorem p4c12_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions p4c12P {s with pc := N 3733, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: rest} =
      some (p4c12M s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 rest) := by
  have hc (j : Nat) (hj : j ≤ 32) : rest.length + j < 1024 := by omega
  have hcr : rest.length < 1024 := by omega
  have ha192 : (192 : W).toNat = 192 := rfl
  have hf192 := activeWords_fix s 192 32 (by decide) (by norm_num) hact
  simp [hz, hzn, p4c12P, p4c12M, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, ofNat_sub_ofNat, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, hc, hcr, ha192, hf192]

def p4c13P : List Instr :=
  [.push 1 160,
   .op .MLOAD,
   .op (.Dup dA6),
   .op .MULMOD,
   .op .ADD,
   .op (.Dup dA14),
   .op (.Swap sA0)]

def p4c13M (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 : W) (rest : List W) : State :=
  let v0 : W := MachineState.readWord s.memory 160
  let v1 : W := UInt256.mulMod x5 v0 x0
  let v2 : W := v1 + x1
  {s with pc := N 3751, memory := s.memory, stack := v2 :: x15 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: rest}

theorem p4c13_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions p4c13P {s with pc := N 3743, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: rest} =
      some (p4c13M s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 rest) := by
  have hc (j : Nat) (hj : j ≤ 33) : rest.length + j < 1024 := by omega
  have hcr : rest.length < 1024 := by omega
  have ha160 : (160 : W).toNat = 160 := rfl
  have hf160 := activeWords_fix s 160 32 (by decide) (by norm_num) hact
  simp [hz, hzn, p4c13P, p4c13M, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, ofNat_sub_ofNat, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, hc, hcr, ha160, hf160]

def p4c14P : List Instr :=
  [.push 2 2048,
   .op .MULMOD]

def p4c14M (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 : W) (rest : List W) : State :=
  let v0 : W := UInt256.mulMod (N 2048) x0 x1
  {s with pc := N 3755, memory := s.memory, stack := v0 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: rest}

theorem p4c14_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions p4c14P {s with pc := N 3751, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: rest} =
      some (p4c14M s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 rest) := by
  have hc (j : Nat) (hj : j ≤ 32) : rest.length + j < 1024 := by omega
  have hcr : rest.length < 1024 := by omega
  simp [hz, hzn, p4c14P, p4c14M, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, ofNat_sub_ofNat, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, hc, hcr]

def prCol4Program : List Instr :=
  [.op .JUMPDEST,
   .op (.Dup dA0),
   .op (.Dup dA15),
   .push 1 128,
   .op .MLOAD,
   .op (.Dup dA8),
   .op .MULMOD,
   .op .ADD,
   .op (.Dup dA15),
   .push 1 96,
   .op .MLOAD,
   .op (.Dup dA9),
   .op .MULMOD,
   .op .ADD,
   .op (.Dup dA15),
   .push 1 64,
   .op .MLOAD,
   .op (.Dup dA10),
   .op .MULMOD,
   .op .ADD,
   .op (.Dup dA15),
   .push 1 32,
   .op .MLOAD,
   .op (.Dup dA11),
   .op .MULMOD,
   .op .ADD,
   .op (.Dup dA15),
   .push 0 0,
   .op .MLOAD,
   .op (.Dup dA12),
   .op .MULMOD,
   .op .ADD,
   .op (.Dup dA15),
   .op (.Dup dA15),
   .op (.Dup dA7),
   .op .MULMOD,
   .op .ADD,
   .op (.Dup dA15),
   .op (.Dup dA14),
   .op (.Dup dA6),
   .op .MULMOD,
   .op .ADD,
   .op (.Dup dA15),
   .op (.Dup dA13),
   .op (.Dup dA5),
   .op .MULMOD,
   .op .ADD,
   .op (.Dup dA15),
   .op (.Dup dA12),
   .op (.Dup dA4),
   .op .MULMOD,
   .op .ADD,
   .op (.Swap sA0),
   .push 1 128,
   .op .MLOAD,
   .op (.Dup dA7),
   .op .MUL,
   .op .ADD,
   .push 1 96,
   .op .MLOAD,
   .op (.Dup dA8),
   .op .MUL,
   .op .ADD,
   .push 1 64,
   .op .MLOAD,
   .op (.Dup dA9),
   .op .MUL,
   .op .ADD,
   .push 1 32,
   .op .MLOAD,
   .op (.Dup dA10),
   .op .MUL,
   .op .ADD,
   .push 0 0,
   .op .MLOAD,
   .op (.Dup dA11),
   .op .MUL,
   .op .ADD,
   .op (.Dup dA14),
   .op (.Dup dA6),
   .op .MUL,
   .op .ADD,
   .op (.Dup dA13),
   .op (.Dup dA5),
   .op .MUL,
   .op .ADD,
   .op (.Dup dA12),
   .op (.Dup dA4),
   .op .MUL,
   .op .ADD,
   .op (.Dup dA11),
   .op (.Dup dA3),
   .op .MUL,
   .op .ADD,
   .push 1 192,
   .op .MLOAD,
   .op .MUL,
   .push 1 16,
   .op .SHR,
   .op (.Swap sA4),
   .op .POP,
   .op (.Dup dA14),
   .push 1 160,
   .op .MLOAD,
   .op (.Dup dA6),
   .op .MULMOD,
   .op .ADD,
   .op (.Dup dA14),
   .op (.Swap sA0),
   .push 2 2048,
   .op .MULMOD]

def prCol4Model (s : State) (c q3 q2 q1 q0 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp : W) (rest : List W) : State :=
  let v0 : W := MachineState.readWord s.memory 128
  let v1 : W := UInt256.mulMod x0 v0 P
  let v2 : W := v1 + c
  let v3 : W := MachineState.readWord s.memory 96
  let v4 : W := UInt256.mulMod x1 v3 P
  let v5 : W := v4 + v2
  let v6 : W := MachineState.readWord s.memory 64
  let v7 : W := UInt256.mulMod x2 v6 P
  let v8 : W := v7 + v5
  let v9 : W := MachineState.readWord s.memory 32
  let v10 : W := UInt256.mulMod x3 v9 P
  let v11 : W := v10 + v8
  let v12 : W := MachineState.readWord s.memory 0
  let v13 : W := UInt256.mulMod x4 v12 P
  let v14 : W := v13 + v11
  let v15 : W := UInt256.mulMod q0 n4 P
  let v16 : W := v15 + v14
  let v17 : W := UInt256.mulMod q1 n3 P
  let v18 : W := v17 + v16
  let v19 : W := UInt256.mulMod q2 n2 P
  let v20 : W := v19 + v18
  let v21 : W := UInt256.mulMod q3 n1 P
  let v22 : W := v21 + v20
  let v23 : W := MachineState.readWord s.memory 128
  let v24 : W := x0 * v23
  let v25 : W := v24 + c
  let v26 : W := MachineState.readWord s.memory 96
  let v27 : W := x1 * v26
  let v28 : W := v27 + v25
  let v29 : W := MachineState.readWord s.memory 64
  let v30 : W := x2 * v29
  let v31 : W := v30 + v28
  let v32 : W := MachineState.readWord s.memory 32
  let v33 : W := x3 * v32
  let v34 : W := v33 + v31
  let v35 : W := MachineState.readWord s.memory 0
  let v36 : W := x4 * v35
  let v37 : W := v36 + v34
  let v38 : W := q0 * n4
  let v39 : W := v38 + v37
  let v40 : W := q1 * n3
  let v41 : W := v40 + v39
  let v42 : W := q2 * n2
  let v43 : W := v42 + v41
  let v44 : W := q3 * n1
  let v45 : W := v44 + v43
  let v46 : W := MachineState.readWord s.memory 192
  let v47 : W := v46 * v45
  let v48 : W := UInt256.shiftRight v47 (N 16)
  let v49 : W := MachineState.readWord s.memory 160
  let v50 : W := UInt256.mulMod v48 v49 P
  let v51 : W := v50 + v22
  let v52 : W := UInt256.mulMod (N 2048) v51 P
  {s with pc := N 3755, memory := s.memory, stack := v52 :: q3 :: q2 :: q1 :: v48 :: x0 :: x1 :: x2 :: x3 :: x4 :: n1 :: n2 :: n3 :: n4 :: P :: inv :: cntp :: rest}

theorem prCol4_run (s : State) (c q3 q2 q1 q0 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions prCol4Program {s with pc := N 3631, stack := c :: q3 :: q2 :: q1 :: q0 :: x0 :: x1 :: x2 :: x3 :: x4 :: n1 :: n2 :: n3 :: n4 :: P :: inv :: cntp :: rest} =
      some (prCol4Model s c q3 q2 q1 q0 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp rest) := by
  let v0 : W := MachineState.readWord s.memory 128
  let v1 : W := UInt256.mulMod x0 v0 P
  let v2 : W := v1 + c
  let v3 : W := MachineState.readWord s.memory 96
  let v4 : W := UInt256.mulMod x1 v3 P
  let v5 : W := v4 + v2
  let v6 : W := MachineState.readWord s.memory 64
  let v7 : W := UInt256.mulMod x2 v6 P
  let v8 : W := v7 + v5
  let v9 : W := MachineState.readWord s.memory 32
  let v10 : W := UInt256.mulMod x3 v9 P
  let v11 : W := v10 + v8
  let v12 : W := MachineState.readWord s.memory 0
  let v13 : W := UInt256.mulMod x4 v12 P
  let v14 : W := v13 + v11
  let v15 : W := UInt256.mulMod q0 n4 P
  let v16 : W := v15 + v14
  let v17 : W := UInt256.mulMod q1 n3 P
  let v18 : W := v17 + v16
  let v19 : W := UInt256.mulMod q2 n2 P
  let v20 : W := v19 + v18
  let v21 : W := UInt256.mulMod q3 n1 P
  let v22 : W := v21 + v20
  let v23 : W := MachineState.readWord s.memory 128
  let v24 : W := x0 * v23
  let v25 : W := v24 + c
  let v26 : W := MachineState.readWord s.memory 96
  let v27 : W := x1 * v26
  let v28 : W := v27 + v25
  let v29 : W := MachineState.readWord s.memory 64
  let v30 : W := x2 * v29
  let v31 : W := v30 + v28
  let v32 : W := MachineState.readWord s.memory 32
  let v33 : W := x3 * v32
  let v34 : W := v33 + v31
  let v35 : W := MachineState.readWord s.memory 0
  let v36 : W := x4 * v35
  let v37 : W := v36 + v34
  let v38 : W := q0 * n4
  let v39 : W := v38 + v37
  let v40 : W := q1 * n3
  let v41 : W := v40 + v39
  let v42 : W := q2 * n2
  let v43 : W := v42 + v41
  let v44 : W := q3 * n1
  let v45 : W := v44 + v43
  let v46 : W := MachineState.readWord s.memory 192
  let v47 : W := v46 * v45
  let v48 : W := UInt256.shiftRight v47 (N 16)
  let v49 : W := MachineState.readWord s.memory 160
  let v50 : W := UInt256.mulMod v48 v49 P
  let v51 : W := v50 + v22
  let v52 : W := UInt256.mulMod (N 2048) v51 P
  have h0 : runInstructions p4c0P {s with pc := N 3631, memory := s.memory, stack := c :: q3 :: q2 :: q1 :: q0 :: x0 :: x1 :: x2 :: x3 :: x4 :: n1 :: n2 :: n3 :: n4 :: P :: inv :: cntp :: rest} = some {s with pc := N 3640, memory := s.memory, stack := v2 :: c :: q3 :: q2 :: q1 :: q0 :: x0 :: x1 :: x2 :: x3 :: x4 :: n1 :: n2 :: n3 :: n4 :: P :: inv :: cntp :: rest} := by
    simpa only [p4c0M, v0, v1, v2] using p4c0_run (s) c q3 q2 q1 q0 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp rest hcap hact
  have h1 : runInstructions p4c1P {s with pc := N 3640, memory := s.memory, stack := v2 :: c :: q3 :: q2 :: q1 :: q0 :: x0 :: x1 :: x2 :: x3 :: x4 :: n1 :: n2 :: n3 :: n4 :: P :: inv :: cntp :: rest} = some {s with pc := N 3648, memory := s.memory, stack := P :: v5 :: c :: q3 :: q2 :: q1 :: q0 :: x0 :: x1 :: x2 :: x3 :: x4 :: n1 :: n2 :: n3 :: n4 :: P :: inv :: cntp :: rest} := by
    simpa only [p4c1M, v3, v4, v5] using p4c1_run (s) v2 c q3 q2 q1 q0 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp rest hcap hact
  have h2 : runInstructions p4c2P {s with pc := N 3648, memory := s.memory, stack := P :: v5 :: c :: q3 :: q2 :: q1 :: q0 :: x0 :: x1 :: x2 :: x3 :: x4 :: n1 :: n2 :: n3 :: n4 :: P :: inv :: cntp :: rest} = some {s with pc := N 3658, memory := s.memory, stack := v9 :: P :: v8 :: c :: q3 :: q2 :: q1 :: q0 :: x0 :: x1 :: x2 :: x3 :: x4 :: n1 :: n2 :: n3 :: n4 :: P :: inv :: cntp :: rest} := by
    simpa only [p4c2M, v6, v7, v8, v9] using p4c2_run (s) P v5 c q3 q2 q1 q0 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp rest hcap hact
  have h3 : runInstructions p4c3P {s with pc := N 3658, memory := s.memory, stack := v9 :: P :: v8 :: c :: q3 :: q2 :: q1 :: q0 :: x0 :: x1 :: x2 :: x3 :: x4 :: n1 :: n2 :: n3 :: n4 :: P :: inv :: cntp :: rest} = some {s with pc := N 3666, memory := s.memory, stack := v13 :: v11 :: c :: q3 :: q2 :: q1 :: q0 :: x0 :: x1 :: x2 :: x3 :: x4 :: n1 :: n2 :: n3 :: n4 :: P :: inv :: cntp :: rest} := by
    simpa only [p4c3M, v10, v11, v12, v13] using p4c3_run (s) v9 P v8 c q3 q2 q1 q0 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp rest hcap hact
  have h4 : runInstructions p4c4P {s with pc := N 3666, memory := s.memory, stack := v13 :: v11 :: c :: q3 :: q2 :: q1 :: q0 :: x0 :: x1 :: x2 :: x3 :: x4 :: n1 :: n2 :: n3 :: n4 :: P :: inv :: cntp :: rest} = some {s with pc := N 3674, memory := s.memory, stack := n3 :: P :: v16 :: c :: q3 :: q2 :: q1 :: q0 :: x0 :: x1 :: x2 :: x3 :: x4 :: n1 :: n2 :: n3 :: n4 :: P :: inv :: cntp :: rest} := by
    simpa only [p4c4M, v14, v15, v16] using p4c4_run (s) v13 v11 c q3 q2 q1 q0 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp rest hcap hact
  have h5 : runInstructions p4c5P {s with pc := N 3674, memory := s.memory, stack := n3 :: P :: v16 :: c :: q3 :: q2 :: q1 :: q0 :: x0 :: x1 :: x2 :: x3 :: x4 :: n1 :: n2 :: n3 :: n4 :: P :: inv :: cntp :: rest} = some {s with pc := N 3682, memory := s.memory, stack := v20 :: c :: q3 :: q2 :: q1 :: q0 :: x0 :: x1 :: x2 :: x3 :: x4 :: n1 :: n2 :: n3 :: n4 :: P :: inv :: cntp :: rest} := by
    simpa only [p4c5M, v17, v18, v19, v20] using p4c5_run (s) n3 P v16 c q3 q2 q1 q0 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp rest hcap hact
  have h6 : runInstructions p4c6P {s with pc := N 3682, memory := s.memory, stack := v20 :: c :: q3 :: q2 :: q1 :: q0 :: x0 :: x1 :: x2 :: x3 :: x4 :: n1 :: n2 :: n3 :: n4 :: P :: inv :: cntp :: rest} = some {s with pc := N 3691, memory := s.memory, stack := v23 :: c :: v22 :: q3 :: q2 :: q1 :: q0 :: x0 :: x1 :: x2 :: x3 :: x4 :: n1 :: n2 :: n3 :: n4 :: P :: inv :: cntp :: rest} := by
    simpa only [p4c6M, v21, v22, v23] using p4c6_run (s) v20 c q3 q2 q1 q0 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp rest hcap hact
  have h7 : runInstructions p4c7P {s with pc := N 3691, memory := s.memory, stack := v23 :: c :: v22 :: q3 :: q2 :: q1 :: q0 :: x0 :: x1 :: x2 :: x3 :: x4 :: n1 :: n2 :: n3 :: n4 :: P :: inv :: cntp :: rest} = some {s with pc := N 3700, memory := s.memory, stack := v28 :: v22 :: q3 :: q2 :: q1 :: q0 :: x0 :: x1 :: x2 :: x3 :: x4 :: n1 :: n2 :: n3 :: n4 :: P :: inv :: cntp :: rest} := by
    simpa only [p4c7M, v24, v25, v26, v27, v28] using p4c7_run (s) v23 c v22 q3 q2 q1 q0 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp rest hcap hact
  have h8 : runInstructions p4c8P {s with pc := N 3700, memory := s.memory, stack := v28 :: v22 :: q3 :: q2 :: q1 :: q0 :: x0 :: x1 :: x2 :: x3 :: x4 :: n1 :: n2 :: n3 :: n4 :: P :: inv :: cntp :: rest} = some {s with pc := N 3710, memory := s.memory, stack := x3 :: v32 :: v31 :: v22 :: q3 :: q2 :: q1 :: q0 :: x0 :: x1 :: x2 :: x3 :: x4 :: n1 :: n2 :: n3 :: n4 :: P :: inv :: cntp :: rest} := by
    simpa only [p4c8M, v29, v30, v31, v32] using p4c8_run (s) v28 v22 q3 q2 q1 q0 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp rest hcap hact
  have h9 : runInstructions p4c9P {s with pc := N 3710, memory := s.memory, stack := x3 :: v32 :: v31 :: v22 :: q3 :: q2 :: q1 :: q0 :: x0 :: x1 :: x2 :: x3 :: x4 :: n1 :: n2 :: n3 :: n4 :: P :: inv :: cntp :: rest} = some {s with pc := N 3718, memory := s.memory, stack := n4 :: v37 :: v22 :: q3 :: q2 :: q1 :: q0 :: x0 :: x1 :: x2 :: x3 :: x4 :: n1 :: n2 :: n3 :: n4 :: P :: inv :: cntp :: rest} := by
    simpa only [p4c9M, v33, v34, v35, v36, v37] using p4c9_run (s) x3 v32 v31 v22 q3 q2 q1 q0 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp rest hcap hact
  have h10 : runInstructions p4c10P {s with pc := N 3718, memory := s.memory, stack := n4 :: v37 :: v22 :: q3 :: q2 :: q1 :: q0 :: x0 :: x1 :: x2 :: x3 :: x4 :: n1 :: n2 :: n3 :: n4 :: P :: inv :: cntp :: rest} = some {s with pc := N 3726, memory := s.memory, stack := n2 :: v41 :: v22 :: q3 :: q2 :: q1 :: q0 :: x0 :: x1 :: x2 :: x3 :: x4 :: n1 :: n2 :: n3 :: n4 :: P :: inv :: cntp :: rest} := by
    simpa only [p4c10M, v38, v39, v40, v41] using p4c10_run (s) n4 v37 v22 q3 q2 q1 q0 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp rest hcap hact
  have h11 : runInstructions p4c11P {s with pc := N 3726, memory := s.memory, stack := n2 :: v41 :: v22 :: q3 :: q2 :: q1 :: q0 :: x0 :: x1 :: x2 :: x3 :: x4 :: n1 :: n2 :: n3 :: n4 :: P :: inv :: cntp :: rest} = some {s with pc := N 3733, memory := s.memory, stack := v45 :: v22 :: q3 :: q2 :: q1 :: q0 :: x0 :: x1 :: x2 :: x3 :: x4 :: n1 :: n2 :: n3 :: n4 :: P :: inv :: cntp :: rest} := by
    simpa only [p4c11M, v42, v43, v44, v45] using p4c11_run (s) n2 v41 v22 q3 q2 q1 q0 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp rest hcap hact
  have h12 : runInstructions p4c12P {s with pc := N 3733, memory := s.memory, stack := v45 :: v22 :: q3 :: q2 :: q1 :: q0 :: x0 :: x1 :: x2 :: x3 :: x4 :: n1 :: n2 :: n3 :: n4 :: P :: inv :: cntp :: rest} = some {s with pc := N 3743, memory := s.memory, stack := P :: v22 :: q3 :: q2 :: q1 :: v48 :: x0 :: x1 :: x2 :: x3 :: x4 :: n1 :: n2 :: n3 :: n4 :: P :: inv :: cntp :: rest} := by
    simpa only [p4c12M, v46, v47, v48] using p4c12_run (s) v45 v22 q3 q2 q1 q0 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp rest hcap hact
  have h13 : runInstructions p4c13P {s with pc := N 3743, memory := s.memory, stack := P :: v22 :: q3 :: q2 :: q1 :: v48 :: x0 :: x1 :: x2 :: x3 :: x4 :: n1 :: n2 :: n3 :: n4 :: P :: inv :: cntp :: rest} = some {s with pc := N 3751, memory := s.memory, stack := v51 :: P :: q3 :: q2 :: q1 :: v48 :: x0 :: x1 :: x2 :: x3 :: x4 :: n1 :: n2 :: n3 :: n4 :: P :: inv :: cntp :: rest} := by
    simpa only [p4c13M, v49, v50, v51] using p4c13_run (s) P v22 q3 q2 q1 v48 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp rest hcap hact
  have h14 : runInstructions p4c14P {s with pc := N 3751, memory := s.memory, stack := v51 :: P :: q3 :: q2 :: q1 :: v48 :: x0 :: x1 :: x2 :: x3 :: x4 :: n1 :: n2 :: n3 :: n4 :: P :: inv :: cntp :: rest} = some {s with pc := N 3755, memory := s.memory, stack := v52 :: q3 :: q2 :: q1 :: v48 :: x0 :: x1 :: x2 :: x3 :: x4 :: n1 :: n2 :: n3 :: n4 :: P :: inv :: cntp :: rest} := by
    simpa only [p4c14M, v52] using p4c14_run (s) v51 P q3 q2 q1 v48 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp rest hcap hact
  exact (runInstructions_append_some _ _ _ _ _ h0 (runInstructions_append_some _ _ _ _ _ h1 (runInstructions_append_some _ _ _ _ _ h2 (runInstructions_append_some _ _ _ _ _ h3 (runInstructions_append_some _ _ _ _ _ h4 (runInstructions_append_some _ _ _ _ _ h5 (runInstructions_append_some _ _ _ _ _ h6 (runInstructions_append_some _ _ _ _ _ h7 (runInstructions_append_some _ _ _ _ _ h8 (runInstructions_append_some _ _ _ _ _ h9 (runInstructions_append_some _ _ _ _ _ h10 (runInstructions_append_some _ _ _ _ _ h11 (runInstructions_append_some _ _ _ _ _ h12 (runInstructions_append_some _ _ _ _ _ h13 h14))))))))))))))

def prCol4_o0 (c q3 q2 q1 q0 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp b0 b1 b2 b3 b4 n0 : W) : W :=
  (UInt256.mulMod (N 2048) ((UInt256.mulMod (UInt256.shiftRight (inv * ((q3 * n1) + ((q2 * n2) + ((q1 * n3) + ((q0 * n4) + ((x4 * b0) + ((x3 * b1) + ((x2 * b2) + ((x1 * b3) + ((x0 * b4) + c)))))))))) (N 16)) n0 P) + ((UInt256.mulMod q3 n1 P) + ((UInt256.mulMod q2 n2 P) + ((UInt256.mulMod q1 n3 P) + ((UInt256.mulMod q0 n4 P) + ((UInt256.mulMod x4 b0 P) + ((UInt256.mulMod x3 b1 P) + ((UInt256.mulMod x2 b2 P) + ((UInt256.mulMod x1 b3 P) + ((UInt256.mulMod x0 b4 P) + c)))))))))) P)

def prCol4_o4 (c q3 q2 q1 q0 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp b0 b1 b2 b3 b4 n0 : W) : W :=
  (UInt256.shiftRight (inv * ((q3 * n1) + ((q2 * n2) + ((q1 * n3) + ((q0 * n4) + ((x4 * b0) + ((x3 * b1) + ((x2 * b2) + ((x1 * b3) + ((x0 * b4) + c)))))))))) (N 16))

theorem prCol4_eq (s : State) (c q3 q2 q1 q0 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp b0 b1 b2 b3 b4 n0 : W) (rest : List W)
    (h_b0 : MachineState.readWord s.memory 0 = b0)
    (h_b1 : MachineState.readWord s.memory 32 = b1)
    (h_b2 : MachineState.readWord s.memory 64 = b2)
    (h_b3 : MachineState.readWord s.memory 96 = b3)
    (h_b4 : MachineState.readWord s.memory 128 = b4)
    (h_n0 : MachineState.readWord s.memory 160 = n0)
    (h_inv : MachineState.readWord s.memory 192 = inv) :
    prCol4Model s c q3 q2 q1 q0 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp rest =
      {s with pc := N 3755, stack := (prCol4_o0 c q3 q2 q1 q0 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp b0 b1 b2 b3 b4 n0) :: q3 :: q2 :: q1 :: (prCol4_o4 c q3 q2 q1 q0 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp b0 b1 b2 b3 b4 n0) :: x0 :: x1 :: x2 :: x3 :: x4 :: n1 :: n2 :: n3 :: n4 :: P :: inv :: cntp :: rest} := by
  simp only [prCol4Model, prCol4_o0, prCol4_o4, h_b0, h_b1, h_b2, h_b3, h_b4, h_n0, h_inv]

def prCol5_o0 (c q3 q2 q1 q4 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp b1 b2 b3 b4 M : W) : W :=
  (UInt256.mulMod (P + (((UInt256.mulMod q4 n1 P) + ((UInt256.mulMod q3 n2 P) + ((UInt256.mulMod q2 n3 P) + ((UInt256.mulMod q1 n4 P) + ((UInt256.mulMod x4 b1 P) + ((UInt256.mulMod x3 b2 P) + ((UInt256.mulMod x2 b3 P) + ((UInt256.mulMod x1 b4 P) + c)))))))) - (UInt256.land M ((q4 * n1) + ((q3 * n2) + ((q2 * n3) + ((q1 * n4) + ((x4 * b1) + ((x3 * b2) + ((x2 * b3) + ((x1 * b4) + c))))))))))) (N 2048) P)

def prCol5_o5 (c q3 q2 q1 q4 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp b1 b2 b3 b4 M : W) : W :=
  (UInt256.land M ((q4 * n1) + ((q3 * n2) + ((q2 * n3) + ((q1 * n4) + ((x4 * b1) + ((x3 * b2) + ((x2 * b3) + ((x1 * b4) + c)))))))))

def prCol6_o0 (c q3 q2 q1 q4 z0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp b2 b3 b4 M : W) : W :=
  (UInt256.mulMod (P + (((UInt256.mulMod q4 n2 P) + ((UInt256.mulMod q3 n3 P) + ((UInt256.mulMod q2 n4 P) + ((UInt256.mulMod x4 b2 P) + ((UInt256.mulMod x3 b3 P) + ((UInt256.mulMod x2 b4 P) + c)))))) - (UInt256.land M ((q4 * n2) + ((q3 * n3) + ((q2 * n4) + ((x4 * b2) + ((x3 * b3) + ((x2 * b4) + c))))))))) (N 2048) P)

def prCol6_o6 (c q3 q2 q1 q4 z0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp b2 b3 b4 M : W) : W :=
  (UInt256.land M ((q4 * n2) + ((q3 * n3) + ((q2 * n4) + ((x4 * b2) + ((x3 * b3) + ((x2 * b4) + c)))))))

def prCol7_o0 (c q3 q2 q1 q4 z0 z1 x2 x3 x4 n1 n2 n3 n4 P inv cntp b3 b4 M : W) : W :=
  (UInt256.mulMod (P + (((UInt256.mulMod q4 n3 P) + ((UInt256.mulMod q3 n4 P) + ((UInt256.mulMod x4 b3 P) + ((UInt256.mulMod x3 b4 P) + c)))) - (UInt256.land M ((q4 * n3) + ((q3 * n4) + ((x4 * b3) + ((x3 * b4) + c))))))) (N 2048) P)

def prCol7_o7 (c q3 q2 q1 q4 z0 z1 x2 x3 x4 n1 n2 n3 n4 P inv cntp b3 b4 M : W) : W :=
  (UInt256.land M ((q4 * n3) + ((q3 * n4) + ((x4 * b3) + ((x3 * b4) + c)))))

def prCol8_o0 (c q3 q2 q1 q4 z0 z1 z2 x3 x4 n1 n2 n3 n4 P inv cntp b4 M : W) : W :=
  (UInt256.mulMod (P + (((UInt256.mulMod q4 n4 P) + ((UInt256.mulMod x4 b4 P) + c)) - (UInt256.land M ((q4 * n4) + ((x4 * b4) + c))))) (N 2048) P)

def prCol8_o8 (c q3 q2 q1 q4 z0 z1 z2 x3 x4 n1 n2 n3 n4 P inv cntp b4 M : W) : W :=
  (UInt256.land M ((q4 * n4) + ((x4 * b4) + c)))

end CycleSubmission.R5.ExecProduct
