import Challenge.Modexp.Submission.Proofs.Bytecode.WindowNibbleDefs
import Challenge.Modexp.Submission.Proofs.Fast.Exp

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

private theorem hz : ({val := 0} : UInt256) = UInt256.ofNat 0 := rfl
private theorem hzn : ({val := 0} : UInt256).toNat = 0 := rfl

/-! ## prCol0: pc 4716..4745, 23 instructions -/

def prCol0part0Program : List Instr :=
  [.push 0 0,
   .op .MLOAD,
   .op (.Dup ⟨1, by decide⟩),
   .op .MUL,
   .op (.Dup ⟨11, by decide⟩),
   .op .MUL,
   .push 2 16,
   .op .SHR]

def prCol0part0Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 : UInt256) (rest : List UInt256) : State :=
  let v0 : UInt256 := MachineState.readWord s.memory 0
  let v1 : UInt256 := x0 * v0
  let v2 : UInt256 := x10 * v1
  let v3 : UInt256 := UInt256.shiftRight v2 (UInt256.ofNat 16)
  {s with pc := UInt256.ofNat 4726, memory := s.memory, stack := v3 :: x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: rest}

theorem prCol0part0_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions prCol0part0Program {s with pc := UInt256.ofNat 4716, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: rest} =
      some (prCol0part0Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 rest) := by
  have hc (j : Nat) (hj : j ≤ 27) : rest.length + j < 1024 := by omega
  have hcr : rest.length < 1024 := by omega
  have ha0 : (0 : UInt256).toNat = 0 := rfl
  have hf0 := activeWords_fix s 0 32 (by decide) (by norm_num) hact
  simp [hz, hzn, prCol0part0Program, prCol0part0Model, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, ofNat_sub_ofNat, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, hc, hcr, ha0, hf0]

def prCol0part1Program : List Instr :=
  [.op (.Dup ⟨10, by decide⟩),
   .op (.Dup ⟨11, by decide⟩),
   .push 0 0,
   .op .MLOAD,
   .op (.Dup ⟨4, by decide⟩),
   .op .MULMOD,
   .op (.Dup ⟨12, by decide⟩),
   .push 1 160,
   .op .MLOAD]

def prCol0part1Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 : UInt256) (rest : List UInt256) : State :=
  let v0 : UInt256 := MachineState.readWord s.memory 0
  let v1 : UInt256 := UInt256.mulMod x1 v0 x10
  let v2 : UInt256 := MachineState.readWord s.memory 160
  {s with pc := UInt256.ofNat 4736, memory := s.memory, stack := v2 :: x10 :: v1 :: x10 :: x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: rest}

theorem prCol0part1_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions prCol0part1Program {s with pc := UInt256.ofNat 4726, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: rest} =
      some (prCol0part1Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 rest) := by
  have hc (j : Nat) (hj : j ≤ 30) : rest.length + j < 1024 := by omega
  have hcr : rest.length < 1024 := by omega
  have ha0 : (0 : UInt256).toNat = 0 := rfl
  have hf0 := activeWords_fix s 0 32 (by decide) (by norm_num) hact
  have ha160 : (160 : UInt256).toNat = 160 := rfl
  have hf160 := activeWords_fix s 160 32 (by decide) (by norm_num) hact
  simp [hz, hzn, prCol0part1Program, prCol0part1Model, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, ofNat_sub_ofNat, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, hc, hcr, ha0, hf0, ha160, hf160]

def prCol0part2Program : List Instr :=
  [.op (.Dup ⟨4, by decide⟩),
   .op .MULMOD,
   .op .ADD,
   .push 3 2048,
   .op .MULMOD,
   .op .JUMPDEST]

def prCol0part2Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 : UInt256) (rest : List UInt256) : State :=
  let v0 : UInt256 := UInt256.mulMod x4 x0 x1
  let v1 : UInt256 := v0 + x2
  let v2 : UInt256 := UInt256.mulMod (UInt256.ofNat 2048) v1 x3
  {s with pc := UInt256.ofNat 4745, memory := s.memory, stack := v2 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: rest}

theorem prCol0part2_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions prCol0part2Program {s with pc := UInt256.ofNat 4736, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: rest} =
      some (prCol0part2Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 rest) := by
  have hc (j : Nat) (hj : j ≤ 30) : rest.length + j < 1024 := by omega
  have hcr : rest.length < 1024 := by omega
  simp [hz, hzn, prCol0part2Program, prCol0part2Model, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, ofNat_sub_ofNat, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, hc, hcr]

def prCol0Program : List Instr :=
  [.push 0 0,
   .op .MLOAD,
   .op (.Dup ⟨1, by decide⟩),
   .op .MUL,
   .op (.Dup ⟨11, by decide⟩),
   .op .MUL,
   .push 2 16,
   .op .SHR,
   .op (.Dup ⟨10, by decide⟩),
   .op (.Dup ⟨11, by decide⟩),
   .push 0 0,
   .op .MLOAD,
   .op (.Dup ⟨4, by decide⟩),
   .op .MULMOD,
   .op (.Dup ⟨12, by decide⟩),
   .push 1 160,
   .op .MLOAD,
   .op (.Dup ⟨4, by decide⟩),
   .op .MULMOD,
   .op .ADD,
   .push 3 2048,
   .op .MULMOD,
   .op .JUMPDEST]

def prCol0Model (s : State) (x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp : UInt256) (rest : List UInt256) : State :=
  let v0 : UInt256 := MachineState.readWord s.memory 0
  let v1 : UInt256 := x0 * v0
  let v2 : UInt256 := inv * v1
  let v3 : UInt256 := UInt256.shiftRight v2 (UInt256.ofNat 16)
  let v4 : UInt256 := MachineState.readWord s.memory 0
  let v5 : UInt256 := UInt256.mulMod x0 v4 P
  let v6 : UInt256 := MachineState.readWord s.memory 160
  let v7 : UInt256 := UInt256.mulMod v3 v6 P
  let v8 : UInt256 := v7 + v5
  let v9 : UInt256 := UInt256.mulMod (UInt256.ofNat 2048) v8 P
  {s with pc := UInt256.ofNat 4745, memory := s.memory, stack := v9 :: v3 :: x0 :: x1 :: x2 :: x3 :: x4 :: n1 :: n2 :: n3 :: n4 :: P :: inv :: cntp :: rest}

theorem prCol0_run (s : State) (x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions prCol0Program {s with pc := UInt256.ofNat 4716, stack := x0 :: x1 :: x2 :: x3 :: x4 :: n1 :: n2 :: n3 :: n4 :: P :: inv :: cntp :: rest} =
      some (prCol0Model s x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp rest) := by
  let v0 : UInt256 := MachineState.readWord s.memory 0
  let v1 : UInt256 := x0 * v0
  let v2 : UInt256 := inv * v1
  let v3 : UInt256 := UInt256.shiftRight v2 (UInt256.ofNat 16)
  let v4 : UInt256 := MachineState.readWord s.memory 0
  let v5 : UInt256 := UInt256.mulMod x0 v4 P
  let v6 : UInt256 := MachineState.readWord s.memory 160
  let v7 : UInt256 := UInt256.mulMod v3 v6 P
  let v8 : UInt256 := v7 + v5
  let v9 : UInt256 := UInt256.mulMod (UInt256.ofNat 2048) v8 P
  have h0 : runInstructions prCol0part0Program {s with pc := UInt256.ofNat 4716, memory := s.memory, stack := x0 :: x1 :: x2 :: x3 :: x4 :: n1 :: n2 :: n3 :: n4 :: P :: inv :: cntp :: rest} = some {s with pc := UInt256.ofNat 4726, memory := s.memory, stack := v3 :: x0 :: x1 :: x2 :: x3 :: x4 :: n1 :: n2 :: n3 :: n4 :: P :: inv :: cntp :: rest} := by
    simpa only [prCol0part0Model, v0, v1, v2, v3] using prCol0part0_run (s) x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp rest hcap hact
  have h1 : runInstructions prCol0part1Program {s with pc := UInt256.ofNat 4726, memory := s.memory, stack := v3 :: x0 :: x1 :: x2 :: x3 :: x4 :: n1 :: n2 :: n3 :: n4 :: P :: inv :: cntp :: rest} = some {s with pc := UInt256.ofNat 4736, memory := s.memory, stack := v6 :: P :: v5 :: P :: v3 :: x0 :: x1 :: x2 :: x3 :: x4 :: n1 :: n2 :: n3 :: n4 :: P :: inv :: cntp :: rest} := by
    simpa only [prCol0part1Model, v4, v5, v6] using prCol0part1_run (s) v3 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp rest hcap hact
  have h2 : runInstructions prCol0part2Program {s with pc := UInt256.ofNat 4736, memory := s.memory, stack := v6 :: P :: v5 :: P :: v3 :: x0 :: x1 :: x2 :: x3 :: x4 :: n1 :: n2 :: n3 :: n4 :: P :: inv :: cntp :: rest} = some {s with pc := UInt256.ofNat 4745, memory := s.memory, stack := v9 :: v3 :: x0 :: x1 :: x2 :: x3 :: x4 :: n1 :: n2 :: n3 :: n4 :: P :: inv :: cntp :: rest} := by
    simpa only [prCol0part2Model, v7, v8, v9] using prCol0part2_run (s) v6 P v5 P v3 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp rest hcap hact
  exact (runInstructions_append_some _ _ _ _ _ h0 (runInstructions_append_some _ _ _ _ _ h1 h2))

def prCol0_o0 (x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp b0 n0 : UInt256) : UInt256 :=
  (UInt256.mulMod (UInt256.ofNat 2048) ((UInt256.mulMod (UInt256.shiftRight (inv * (x0 * b0)) (UInt256.ofNat 16)) n0 P) + (UInt256.mulMod x0 b0 P)) P)

def prCol0_o1 (x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp b0 n0 : UInt256) : UInt256 :=
  (UInt256.shiftRight (inv * (x0 * b0)) (UInt256.ofNat 16))

theorem prCol0_eq (s : State) (x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp b0 n0 : UInt256) (rest : List UInt256)
    (h_b0 : MachineState.readWord s.memory 0 = b0)
    (h_n0 : MachineState.readWord s.memory 160 = n0) :
    prCol0Model s x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp rest =
      {s with pc := UInt256.ofNat 4745, stack := (prCol0_o0 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp b0 n0) :: (prCol0_o1 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp b0 n0) :: x0 :: x1 :: x2 :: x3 :: x4 :: n1 :: n2 :: n3 :: n4 :: P :: inv :: cntp :: rest} := by
  simp only [prCol0Model, prCol0_o0, prCol0_o1, h_b0, h_n0]

/-! ## prCol1: pc 4745..4800, 47 instructions -/

def prCol1part0Program : List Instr :=
  [.op (.Dup ⟨0, by decide⟩),
   .push 1 32,
   .op .MLOAD,
   .op (.Dup ⟨4, by decide⟩),
   .op .MUL,
   .op .ADD,
   .push 1 0,
   .op .MLOAD]

def prCol1part0Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 : UInt256) (rest : List UInt256) : State :=
  let v0 : UInt256 := MachineState.readWord s.memory 32
  let v1 : UInt256 := x2 * v0
  let v2 : UInt256 := v1 + x0
  let v3 : UInt256 := MachineState.readWord s.memory 0
  {s with pc := UInt256.ofNat 4755, memory := s.memory, stack := v3 :: v2 :: x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: rest}

theorem prCol1part0_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions prCol1part0Program {s with pc := UInt256.ofNat 4745, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: rest} =
      some (prCol1part0Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 rest) := by
  have hc (j : Nat) (hj : j ≤ 30) : rest.length + j < 1024 := by omega
  have hcr : rest.length < 1024 := by omega
  have ha32 : (32 : UInt256).toNat = 32 := rfl
  have hf32 := activeWords_fix s 32 32 (by decide) (by norm_num) hact
  have ha0 : (0 : UInt256).toNat = 0 := rfl
  have hf0 := activeWords_fix s 0 32 (by decide) (by norm_num) hact
  simp [hz, hzn, prCol1part0Program, prCol1part0Model, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, ofNat_sub_ofNat, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, hc, hcr, ha32, hf32, ha0, hf0]

def prCol1part1Program : List Instr :=
  [.op (.Dup ⟨5, by decide⟩),
   .op .MUL,
   .op .ADD,
   .op (.Dup ⟨8, by decide⟩),
   .op (.Dup ⟨3, by decide⟩),
   .op .MUL,
   .op .ADD,
   .op (.Dup ⟨13, by decide⟩)]

def prCol1part1Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 : UInt256) (rest : List UInt256) : State :=
  let v0 : UInt256 := x5 * x0
  let v1 : UInt256 := v0 + x1
  let v2 : UInt256 := x3 * x9
  let v3 : UInt256 := v2 + v1
  {s with pc := UInt256.ofNat 4763, memory := s.memory, stack := x14 :: v3 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: rest}

theorem prCol1part1_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions prCol1part1Program {s with pc := UInt256.ofNat 4755, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: rest} =
      some (prCol1part1Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 rest) := by
  have hc (j : Nat) (hj : j ≤ 30) : rest.length + j < 1024 := by omega
  have hcr : rest.length < 1024 := by omega
  simp [hz, hzn, prCol1part1Program, prCol1part1Model, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, ofNat_sub_ofNat, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, hc, hcr]

def prCol1part2Program : List Instr :=
  [.op .MUL,
   .push 1 16,
   .op .SHR,
   .op (.Swap ⟨0, by decide⟩),
   .op (.Dup ⟨12, by decide⟩),
   .push 1 32,
   .op .MLOAD,
   .op (.Dup ⟨5, by decide⟩)]

def prCol1part2Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 : UInt256) (rest : List UInt256) : State :=
  let v0 : UInt256 := x0 * x1
  let v1 : UInt256 := UInt256.shiftRight v0 (UInt256.ofNat 16)
  let v2 : UInt256 := MachineState.readWord s.memory 32
  {s with pc := UInt256.ofNat 4773, memory := s.memory, stack := x4 :: v2 :: x13 :: x2 :: v1 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: rest}

theorem prCol1part2_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions prCol1part2Program {s with pc := UInt256.ofNat 4763, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: rest} =
      some (prCol1part2Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 rest) := by
  have hc (j : Nat) (hj : j ≤ 31) : rest.length + j < 1024 := by omega
  have hcr : rest.length < 1024 := by omega
  have ha32 : (32 : UInt256).toNat = 32 := rfl
  have hf32 := activeWords_fix s 32 32 (by decide) (by norm_num) hact
  simp [hz, hzn, prCol1part2Program, prCol1part2Model, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, ofNat_sub_ofNat, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, hc, hcr, ha32, hf32]

def prCol1part3Program : List Instr :=
  [.op .MULMOD,
   .op .ADD,
   .op (.Dup ⟨12, by decide⟩),
   .push 1 0,
   .op .MLOAD,
   .op (.Dup ⟨6, by decide⟩),
   .op .MULMOD,
   .op .ADD]

def prCol1part3Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 : UInt256) (rest : List UInt256) : State :=
  let v0 : UInt256 := UInt256.mulMod x0 x1 x2
  let v1 : UInt256 := v0 + x3
  let v2 : UInt256 := MachineState.readWord s.memory 0
  let v3 : UInt256 := UInt256.mulMod x7 v2 x15
  let v4 : UInt256 := v3 + v1
  {s with pc := UInt256.ofNat 4782, memory := s.memory, stack := v4 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: rest}

theorem prCol1part3_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions prCol1part3Program {s with pc := UInt256.ofNat 4773, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: rest} =
      some (prCol1part3Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 rest) := by
  have hc (j : Nat) (hj : j ≤ 31) : rest.length + j < 1024 := by omega
  have hcr : rest.length < 1024 := by omega
  have ha0 : (0 : UInt256).toNat = 0 := rfl
  have hf0 := activeWords_fix s 0 32 (by decide) (by norm_num) hact
  simp [hz, hzn, prCol1part3Program, prCol1part3Model, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, ofNat_sub_ofNat, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, hc, hcr, ha0, hf0]

def prCol1part4Program : List Instr :=
  [.op (.Dup ⟨12, by decide⟩),
   .op (.Dup ⟨9, by decide⟩),
   .op (.Dup ⟨4, by decide⟩),
   .op .MULMOD,
   .op .ADD,
   .op (.Dup ⟨12, by decide⟩),
   .push 1 160,
   .op .MLOAD]

def prCol1part4Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 : UInt256) (rest : List UInt256) : State :=
  let v0 : UInt256 := UInt256.mulMod x2 x8 x12
  let v1 : UInt256 := v0 + x0
  let v2 : UInt256 := MachineState.readWord s.memory 160
  {s with pc := UInt256.ofNat 4791, memory := s.memory, stack := v2 :: x12 :: v1 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: rest}

theorem prCol1part4_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions prCol1part4Program {s with pc := UInt256.ofNat 4782, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: rest} =
      some (prCol1part4Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 rest) := by
  have hc (j : Nat) (hj : j ≤ 31) : rest.length + j < 1024 := by omega
  have hcr : rest.length < 1024 := by omega
  have ha160 : (160 : UInt256).toNat = 160 := rfl
  have hf160 := activeWords_fix s 160 32 (by decide) (by norm_num) hact
  simp [hz, hzn, prCol1part4Program, prCol1part4Model, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, ofNat_sub_ofNat, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, hc, hcr, ha160, hf160]

def prCol1part5Program : List Instr :=
  [.op (.Dup ⟨3, by decide⟩),
   .op .MULMOD,
   .op .ADD,
   .op (.Dup ⟨12, by decide⟩),
   .op (.Swap ⟨0, by decide⟩),
   .push 2 2048,
   .op .MULMOD]

def prCol1part5Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 : UInt256) (rest : List UInt256) : State :=
  let v0 : UInt256 := UInt256.mulMod x3 x0 x1
  let v1 : UInt256 := v0 + x2
  let v2 : UInt256 := UInt256.mulMod (UInt256.ofNat 2048) v1 x14
  {s with pc := UInt256.ofNat 4800, memory := s.memory, stack := v2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: rest}

theorem prCol1part5_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions prCol1part5Program {s with pc := UInt256.ofNat 4791, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: rest} =
      some (prCol1part5Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 rest) := by
  have hc (j : Nat) (hj : j ≤ 31) : rest.length + j < 1024 := by omega
  have hcr : rest.length < 1024 := by omega
  simp [hz, hzn, prCol1part5Program, prCol1part5Model, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, ofNat_sub_ofNat, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, hc, hcr]

def prCol1Program : List Instr :=
  [.op (.Dup ⟨0, by decide⟩),
   .push 1 32,
   .op .MLOAD,
   .op (.Dup ⟨4, by decide⟩),
   .op .MUL,
   .op .ADD,
   .push 1 0,
   .op .MLOAD,
   .op (.Dup ⟨5, by decide⟩),
   .op .MUL,
   .op .ADD,
   .op (.Dup ⟨8, by decide⟩),
   .op (.Dup ⟨3, by decide⟩),
   .op .MUL,
   .op .ADD,
   .op (.Dup ⟨13, by decide⟩),
   .op .MUL,
   .push 1 16,
   .op .SHR,
   .op (.Swap ⟨0, by decide⟩),
   .op (.Dup ⟨12, by decide⟩),
   .push 1 32,
   .op .MLOAD,
   .op (.Dup ⟨5, by decide⟩),
   .op .MULMOD,
   .op .ADD,
   .op (.Dup ⟨12, by decide⟩),
   .push 1 0,
   .op .MLOAD,
   .op (.Dup ⟨6, by decide⟩),
   .op .MULMOD,
   .op .ADD,
   .op (.Dup ⟨12, by decide⟩),
   .op (.Dup ⟨9, by decide⟩),
   .op (.Dup ⟨4, by decide⟩),
   .op .MULMOD,
   .op .ADD,
   .op (.Dup ⟨12, by decide⟩),
   .push 1 160,
   .op .MLOAD,
   .op (.Dup ⟨3, by decide⟩),
   .op .MULMOD,
   .op .ADD,
   .op (.Dup ⟨12, by decide⟩),
   .op (.Swap ⟨0, by decide⟩),
   .push 2 2048,
   .op .MULMOD]

def prCol1Model (s : State) (c q0 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp : UInt256) (rest : List UInt256) : State :=
  let v0 : UInt256 := MachineState.readWord s.memory 32
  let v1 : UInt256 := x0 * v0
  let v2 : UInt256 := v1 + c
  let v3 : UInt256 := MachineState.readWord s.memory 0
  let v4 : UInt256 := x1 * v3
  let v5 : UInt256 := v4 + v2
  let v6 : UInt256 := q0 * n1
  let v7 : UInt256 := v6 + v5
  let v8 : UInt256 := inv * v7
  let v9 : UInt256 := UInt256.shiftRight v8 (UInt256.ofNat 16)
  let v10 : UInt256 := MachineState.readWord s.memory 32
  let v11 : UInt256 := UInt256.mulMod x0 v10 P
  let v12 : UInt256 := v11 + c
  let v13 : UInt256 := MachineState.readWord s.memory 0
  let v14 : UInt256 := UInt256.mulMod x1 v13 P
  let v15 : UInt256 := v14 + v12
  let v16 : UInt256 := UInt256.mulMod q0 n1 P
  let v17 : UInt256 := v16 + v15
  let v18 : UInt256 := MachineState.readWord s.memory 160
  let v19 : UInt256 := UInt256.mulMod v9 v18 P
  let v20 : UInt256 := v19 + v17
  let v21 : UInt256 := UInt256.mulMod (UInt256.ofNat 2048) v20 P
  {s with pc := UInt256.ofNat 4800, memory := s.memory, stack := v21 :: v9 :: q0 :: x0 :: x1 :: x2 :: x3 :: x4 :: n1 :: n2 :: n3 :: n4 :: P :: inv :: cntp :: rest}

theorem prCol1_run (s : State) (c q0 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions prCol1Program {s with pc := UInt256.ofNat 4745, stack := c :: q0 :: x0 :: x1 :: x2 :: x3 :: x4 :: n1 :: n2 :: n3 :: n4 :: P :: inv :: cntp :: rest} =
      some (prCol1Model s c q0 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp rest) := by
  let v0 : UInt256 := MachineState.readWord s.memory 32
  let v1 : UInt256 := x0 * v0
  let v2 : UInt256 := v1 + c
  let v3 : UInt256 := MachineState.readWord s.memory 0
  let v4 : UInt256 := x1 * v3
  let v5 : UInt256 := v4 + v2
  let v6 : UInt256 := q0 * n1
  let v7 : UInt256 := v6 + v5
  let v8 : UInt256 := inv * v7
  let v9 : UInt256 := UInt256.shiftRight v8 (UInt256.ofNat 16)
  let v10 : UInt256 := MachineState.readWord s.memory 32
  let v11 : UInt256 := UInt256.mulMod x0 v10 P
  let v12 : UInt256 := v11 + c
  let v13 : UInt256 := MachineState.readWord s.memory 0
  let v14 : UInt256 := UInt256.mulMod x1 v13 P
  let v15 : UInt256 := v14 + v12
  let v16 : UInt256 := UInt256.mulMod q0 n1 P
  let v17 : UInt256 := v16 + v15
  let v18 : UInt256 := MachineState.readWord s.memory 160
  let v19 : UInt256 := UInt256.mulMod v9 v18 P
  let v20 : UInt256 := v19 + v17
  let v21 : UInt256 := UInt256.mulMod (UInt256.ofNat 2048) v20 P
  have h0 : runInstructions prCol1part0Program {s with pc := UInt256.ofNat 4745, memory := s.memory, stack := c :: q0 :: x0 :: x1 :: x2 :: x3 :: x4 :: n1 :: n2 :: n3 :: n4 :: P :: inv :: cntp :: rest} = some {s with pc := UInt256.ofNat 4755, memory := s.memory, stack := v3 :: v2 :: c :: q0 :: x0 :: x1 :: x2 :: x3 :: x4 :: n1 :: n2 :: n3 :: n4 :: P :: inv :: cntp :: rest} := by
    simpa only [prCol1part0Model, v0, v1, v2, v3] using prCol1part0_run (s) c q0 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp rest hcap hact
  have h1 : runInstructions prCol1part1Program {s with pc := UInt256.ofNat 4755, memory := s.memory, stack := v3 :: v2 :: c :: q0 :: x0 :: x1 :: x2 :: x3 :: x4 :: n1 :: n2 :: n3 :: n4 :: P :: inv :: cntp :: rest} = some {s with pc := UInt256.ofNat 4763, memory := s.memory, stack := inv :: v7 :: c :: q0 :: x0 :: x1 :: x2 :: x3 :: x4 :: n1 :: n2 :: n3 :: n4 :: P :: inv :: cntp :: rest} := by
    simpa only [prCol1part1Model, v4, v5, v6, v7] using prCol1part1_run (s) v3 v2 c q0 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp rest hcap hact
  have h2 : runInstructions prCol1part2Program {s with pc := UInt256.ofNat 4763, memory := s.memory, stack := inv :: v7 :: c :: q0 :: x0 :: x1 :: x2 :: x3 :: x4 :: n1 :: n2 :: n3 :: n4 :: P :: inv :: cntp :: rest} = some {s with pc := UInt256.ofNat 4773, memory := s.memory, stack := x0 :: v10 :: P :: c :: v9 :: q0 :: x0 :: x1 :: x2 :: x3 :: x4 :: n1 :: n2 :: n3 :: n4 :: P :: inv :: cntp :: rest} := by
    simpa only [prCol1part2Model, v8, v9, v10] using prCol1part2_run (s) inv v7 c q0 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp rest hcap hact
  have h3 : runInstructions prCol1part3Program {s with pc := UInt256.ofNat 4773, memory := s.memory, stack := x0 :: v10 :: P :: c :: v9 :: q0 :: x0 :: x1 :: x2 :: x3 :: x4 :: n1 :: n2 :: n3 :: n4 :: P :: inv :: cntp :: rest} = some {s with pc := UInt256.ofNat 4782, memory := s.memory, stack := v15 :: v9 :: q0 :: x0 :: x1 :: x2 :: x3 :: x4 :: n1 :: n2 :: n3 :: n4 :: P :: inv :: cntp :: rest} := by
    simpa only [prCol1part3Model, v11, v12, v13, v14, v15] using prCol1part3_run (s) x0 v10 P c v9 q0 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp rest hcap hact
  have h4 : runInstructions prCol1part4Program {s with pc := UInt256.ofNat 4782, memory := s.memory, stack := v15 :: v9 :: q0 :: x0 :: x1 :: x2 :: x3 :: x4 :: n1 :: n2 :: n3 :: n4 :: P :: inv :: cntp :: rest} = some {s with pc := UInt256.ofNat 4791, memory := s.memory, stack := v18 :: P :: v17 :: v9 :: q0 :: x0 :: x1 :: x2 :: x3 :: x4 :: n1 :: n2 :: n3 :: n4 :: P :: inv :: cntp :: rest} := by
    simpa only [prCol1part4Model, v16, v17, v18] using prCol1part4_run (s) v15 v9 q0 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp rest hcap hact
  have h5 : runInstructions prCol1part5Program {s with pc := UInt256.ofNat 4791, memory := s.memory, stack := v18 :: P :: v17 :: v9 :: q0 :: x0 :: x1 :: x2 :: x3 :: x4 :: n1 :: n2 :: n3 :: n4 :: P :: inv :: cntp :: rest} = some {s with pc := UInt256.ofNat 4800, memory := s.memory, stack := v21 :: v9 :: q0 :: x0 :: x1 :: x2 :: x3 :: x4 :: n1 :: n2 :: n3 :: n4 :: P :: inv :: cntp :: rest} := by
    simpa only [prCol1part5Model, v19, v20, v21] using prCol1part5_run (s) v18 P v17 v9 q0 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp rest hcap hact
  exact (runInstructions_append_some _ _ _ _ _ h0 (runInstructions_append_some _ _ _ _ _ h1 (runInstructions_append_some _ _ _ _ _ h2 (runInstructions_append_some _ _ _ _ _ h3 (runInstructions_append_some _ _ _ _ _ h4 h5)))))

def prCol1_o0 (c q0 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp b0 b1 n0 : UInt256) : UInt256 :=
  (UInt256.mulMod (UInt256.ofNat 2048) ((UInt256.mulMod (UInt256.shiftRight (inv * ((q0 * n1) + ((x1 * b0) + ((x0 * b1) + c)))) (UInt256.ofNat 16)) n0 P) + ((UInt256.mulMod q0 n1 P) + ((UInt256.mulMod x1 b0 P) + ((UInt256.mulMod x0 b1 P) + c)))) P)

def prCol1_o1 (c q0 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp b0 b1 n0 : UInt256) : UInt256 :=
  (UInt256.shiftRight (inv * ((q0 * n1) + ((x1 * b0) + ((x0 * b1) + c)))) (UInt256.ofNat 16))

theorem prCol1_eq (s : State) (c q0 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp b0 b1 n0 : UInt256) (rest : List UInt256)
    (h_b0 : MachineState.readWord s.memory 0 = b0)
    (h_b1 : MachineState.readWord s.memory 32 = b1)
    (h_n0 : MachineState.readWord s.memory 160 = n0) :
    prCol1Model s c q0 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp rest =
      {s with pc := UInt256.ofNat 4800, stack := (prCol1_o0 c q0 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp b0 b1 n0) :: (prCol1_o1 c q0 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp b0 b1 n0) :: q0 :: x0 :: x1 :: x2 :: x3 :: x4 :: n1 :: n2 :: n3 :: n4 :: P :: inv :: cntp :: rest} := by
  simp only [prCol1Model, prCol1_o0, prCol1_o1, h_b0, h_b1, h_n0]

/-! ## prCol2: pc 3256..3334, 68 instructions -/

def prCol2part0Program : List Instr :=
  [.op .JUMPDEST,
   .op (.Dup ⟨0, by decide⟩),
   .push 1 64,
   .op .MLOAD,
   .op (.Dup ⟨5, by decide⟩),
   .op .MUL,
   .op .ADD]

def prCol2part0Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 : UInt256) (rest : List UInt256) : State :=
  let v0 : UInt256 := MachineState.readWord s.memory 64
  let v1 : UInt256 := x3 * v0
  let v2 : UInt256 := v1 + x0
  {s with pc := UInt256.ofNat 3264, memory := s.memory, stack := v2 :: x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: rest}

theorem prCol2part0_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions prCol2part0Program {s with pc := UInt256.ofNat 3256, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: rest} =
      some (prCol2part0Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 rest) := by
  have hc (j : Nat) (hj : j ≤ 31) : rest.length + j < 1024 := by omega
  have hcr : rest.length < 1024 := by omega
  have ha64 : (64 : UInt256).toNat = 64 := rfl
  have hf64 := activeWords_fix s 64 32 (by decide) (by norm_num) hact
  simp [hz, hzn, prCol2part0Program, prCol2part0Model, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, ofNat_sub_ofNat, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, hc, hcr, ha64, hf64]

def prCol2part1Program : List Instr :=
  [.push 1 32,
   .op .MLOAD,
   .op (.Dup ⟨6, by decide⟩),
   .op .MUL,
   .op .ADD,
   .push 1 0,
   .op .MLOAD,
   .op (.Dup ⟨7, by decide⟩)]

def prCol2part1Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 : UInt256) (rest : List UInt256) : State :=
  let v0 : UInt256 := MachineState.readWord s.memory 32
  let v1 : UInt256 := x5 * v0
  let v2 : UInt256 := v1 + x0
  let v3 : UInt256 := MachineState.readWord s.memory 0
  {s with pc := UInt256.ofNat 3274, memory := s.memory, stack := x6 :: v3 :: v2 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: rest}

theorem prCol2part1_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions prCol2part1Program {s with pc := UInt256.ofNat 3264, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: rest} =
      some (prCol2part1Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 rest) := by
  have hc (j : Nat) (hj : j ≤ 31) : rest.length + j < 1024 := by omega
  have hcr : rest.length < 1024 := by omega
  have ha32 : (32 : UInt256).toNat = 32 := rfl
  have hf32 := activeWords_fix s 32 32 (by decide) (by norm_num) hact
  have ha0 : (0 : UInt256).toNat = 0 := rfl
  have hf0 := activeWords_fix s 0 32 (by decide) (by norm_num) hact
  simp [hz, hzn, prCol2part1Program, prCol2part1Model, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, ofNat_sub_ofNat, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, hc, hcr, ha32, hf32, ha0, hf0]

def prCol2part2Program : List Instr :=
  [.op .MUL,
   .op .ADD,
   .op (.Dup ⟨10, by decide⟩),
   .op (.Dup ⟨4, by decide⟩),
   .op .MUL,
   .op .ADD,
   .op (.Dup ⟨9, by decide⟩),
   .op (.Dup ⟨3, by decide⟩)]

def prCol2part2Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 : UInt256) (rest : List UInt256) : State :=
  let v0 : UInt256 := x0 * x1
  let v1 : UInt256 := v0 + x2
  let v2 : UInt256 := x5 * x12
  let v3 : UInt256 := v2 + v1
  {s with pc := UInt256.ofNat 3282, memory := s.memory, stack := x4 :: x11 :: v3 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: rest}

theorem prCol2part2_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions prCol2part2Program {s with pc := UInt256.ofNat 3274, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: rest} =
      some (prCol2part2Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 rest) := by
  have hc (j : Nat) (hj : j ≤ 31) : rest.length + j < 1024 := by omega
  have hcr : rest.length < 1024 := by omega
  simp [hz, hzn, prCol2part2Program, prCol2part2Model, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, ofNat_sub_ofNat, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, hc, hcr]

def prCol2part3Program : List Instr :=
  [.op .MUL,
   .op .ADD,
   .op (.Dup ⟨14, by decide⟩),
   .op .MUL,
   .push 1 16,
   .op .SHR,
   .op (.Swap ⟨0, by decide⟩),
   .op (.Dup ⟨13, by decide⟩)]

def prCol2part3Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 : UInt256) (rest : List UInt256) : State :=
  let v0 : UInt256 := x0 * x1
  let v1 : UInt256 := v0 + x2
  let v2 : UInt256 := x16 * v1
  let v3 : UInt256 := UInt256.shiftRight v2 (UInt256.ofNat 16)
  {s with pc := UInt256.ofNat 3291, memory := s.memory, stack := x15 :: x3 :: v3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: rest}

theorem prCol2part3_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions prCol2part3Program {s with pc := UInt256.ofNat 3282, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: rest} =
      some (prCol2part3Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 rest) := by
  have hc (j : Nat) (hj : j ≤ 31) : rest.length + j < 1024 := by omega
  have hcr : rest.length < 1024 := by omega
  simp [hz, hzn, prCol2part3Program, prCol2part3Model, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, ofNat_sub_ofNat, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, hc, hcr]

def prCol2part4Program : List Instr :=
  [.push 1 64,
   .op .MLOAD,
   .op (.Dup ⟨6, by decide⟩),
   .op .MULMOD,
   .op .ADD,
   .op (.Dup ⟨13, by decide⟩),
   .push 1 32,
   .op .MLOAD]

def prCol2part4Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 : UInt256) (rest : List UInt256) : State :=
  let v0 : UInt256 := MachineState.readWord s.memory 64
  let v1 : UInt256 := UInt256.mulMod x5 v0 x0
  let v2 : UInt256 := v1 + x1
  let v3 : UInt256 := MachineState.readWord s.memory 32
  {s with pc := UInt256.ofNat 3301, memory := s.memory, stack := v3 :: x14 :: v2 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: rest}

theorem prCol2part4_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions prCol2part4Program {s with pc := UInt256.ofNat 3291, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: rest} =
      some (prCol2part4Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 rest) := by
  have hc (j : Nat) (hj : j ≤ 32) : rest.length + j < 1024 := by omega
  have hcr : rest.length < 1024 := by omega
  have ha64 : (64 : UInt256).toNat = 64 := rfl
  have hf64 := activeWords_fix s 64 32 (by decide) (by norm_num) hact
  have ha32 : (32 : UInt256).toNat = 32 := rfl
  have hf32 := activeWords_fix s 32 32 (by decide) (by norm_num) hact
  simp [hz, hzn, prCol2part4Program, prCol2part4Model, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, ofNat_sub_ofNat, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, hc, hcr, ha64, hf64, ha32, hf32]

def prCol2part5Program : List Instr :=
  [.op (.Dup ⟨7, by decide⟩),
   .op .MULMOD,
   .op .ADD,
   .op (.Dup ⟨13, by decide⟩),
   .push 1 0,
   .op .MLOAD,
   .op (.Dup ⟨8, by decide⟩),
   .op .MULMOD]

def prCol2part5Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 : UInt256) (rest : List UInt256) : State :=
  let v0 : UInt256 := UInt256.mulMod x7 x0 x1
  let v1 : UInt256 := v0 + x2
  let v2 : UInt256 := MachineState.readWord s.memory 0
  let v3 : UInt256 := UInt256.mulMod x8 v2 x15
  {s with pc := UInt256.ofNat 3310, memory := s.memory, stack := v3 :: v1 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: rest}

theorem prCol2part5_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions prCol2part5Program {s with pc := UInt256.ofNat 3301, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: rest} =
      some (prCol2part5Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 rest) := by
  have hc (j : Nat) (hj : j ≤ 32) : rest.length + j < 1024 := by omega
  have hcr : rest.length < 1024 := by omega
  have ha0 : (0 : UInt256).toNat = 0 := rfl
  have hf0 := activeWords_fix s 0 32 (by decide) (by norm_num) hact
  simp [hz, hzn, prCol2part5Program, prCol2part5Model, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, ofNat_sub_ofNat, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, hc, hcr, ha0, hf0]

def prCol2part6Program : List Instr :=
  [.op .ADD,
   .op (.Dup ⟨13, by decide⟩),
   .op (.Dup ⟨11, by decide⟩),
   .op (.Dup ⟨5, by decide⟩),
   .op .MULMOD,
   .op .ADD,
   .op (.Dup ⟨13, by decide⟩),
   .op (.Dup ⟨10, by decide⟩)]

def prCol2part6Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 : UInt256) (rest : List UInt256) : State :=
  let v0 : UInt256 := x0 + x1
  let v1 : UInt256 := UInt256.mulMod x4 x11 x14
  let v2 : UInt256 := v1 + v0
  {s with pc := UInt256.ofNat 3318, memory := s.memory, stack := x10 :: x14 :: v2 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: rest}

theorem prCol2part6_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions prCol2part6Program {s with pc := UInt256.ofNat 3310, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: rest} =
      some (prCol2part6Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 rest) := by
  have hc (j : Nat) (hj : j ≤ 32) : rest.length + j < 1024 := by omega
  have hcr : rest.length < 1024 := by omega
  simp [hz, hzn, prCol2part6Program, prCol2part6Model, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, ofNat_sub_ofNat, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, hc, hcr]

def prCol2part7Program : List Instr :=
  [.op (.Dup ⟨4, by decide⟩),
   .op .MULMOD,
   .op .ADD,
   .op (.Dup ⟨13, by decide⟩),
   .push 1 160,
   .op .MLOAD,
   .op (.Dup ⟨3, by decide⟩),
   .op .MULMOD]

def prCol2part7Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 : UInt256) (rest : List UInt256) : State :=
  let v0 : UInt256 := UInt256.mulMod x4 x0 x1
  let v1 : UInt256 := v0 + x2
  let v2 : UInt256 := MachineState.readWord s.memory 160
  let v3 : UInt256 := UInt256.mulMod x3 v2 x15
  {s with pc := UInt256.ofNat 3327, memory := s.memory, stack := v3 :: v1 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: rest}

theorem prCol2part7_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions prCol2part7Program {s with pc := UInt256.ofNat 3318, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: rest} =
      some (prCol2part7Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 rest) := by
  have hc (j : Nat) (hj : j ≤ 32) : rest.length + j < 1024 := by omega
  have hcr : rest.length < 1024 := by omega
  have ha160 : (160 : UInt256).toNat = 160 := rfl
  have hf160 := activeWords_fix s 160 32 (by decide) (by norm_num) hact
  simp [hz, hzn, prCol2part7Program, prCol2part7Model, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, ofNat_sub_ofNat, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, hc, hcr, ha160, hf160]

def prCol2part8Program : List Instr :=
  [.op .ADD,
   .op (.Dup ⟨13, by decide⟩),
   .op (.Swap ⟨0, by decide⟩),
   .push 2 2048,
   .op .MULMOD]

def prCol2part8Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 : UInt256) (rest : List UInt256) : State :=
  let v0 : UInt256 := x0 + x1
  let v1 : UInt256 := UInt256.mulMod (UInt256.ofNat 2048) v0 x14
  {s with pc := UInt256.ofNat 3334, memory := s.memory, stack := v1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: rest}

theorem prCol2part8_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions prCol2part8Program {s with pc := UInt256.ofNat 3327, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: rest} =
      some (prCol2part8Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 rest) := by
  have hc (j : Nat) (hj : j ≤ 31) : rest.length + j < 1024 := by omega
  have hcr : rest.length < 1024 := by omega
  simp [hz, hzn, prCol2part8Program, prCol2part8Model, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, ofNat_sub_ofNat, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, hc, hcr]

def prCol2Program : List Instr :=
  [.op .JUMPDEST,
   .op (.Dup ⟨0, by decide⟩),
   .push 1 64,
   .op .MLOAD,
   .op (.Dup ⟨5, by decide⟩),
   .op .MUL,
   .op .ADD,
   .push 1 32,
   .op .MLOAD,
   .op (.Dup ⟨6, by decide⟩),
   .op .MUL,
   .op .ADD,
   .push 1 0,
   .op .MLOAD,
   .op (.Dup ⟨7, by decide⟩),
   .op .MUL,
   .op .ADD,
   .op (.Dup ⟨10, by decide⟩),
   .op (.Dup ⟨4, by decide⟩),
   .op .MUL,
   .op .ADD,
   .op (.Dup ⟨9, by decide⟩),
   .op (.Dup ⟨3, by decide⟩),
   .op .MUL,
   .op .ADD,
   .op (.Dup ⟨14, by decide⟩),
   .op .MUL,
   .push 1 16,
   .op .SHR,
   .op (.Swap ⟨0, by decide⟩),
   .op (.Dup ⟨13, by decide⟩),
   .push 1 64,
   .op .MLOAD,
   .op (.Dup ⟨6, by decide⟩),
   .op .MULMOD,
   .op .ADD,
   .op (.Dup ⟨13, by decide⟩),
   .push 1 32,
   .op .MLOAD,
   .op (.Dup ⟨7, by decide⟩),
   .op .MULMOD,
   .op .ADD,
   .op (.Dup ⟨13, by decide⟩),
   .push 1 0,
   .op .MLOAD,
   .op (.Dup ⟨8, by decide⟩),
   .op .MULMOD,
   .op .ADD,
   .op (.Dup ⟨13, by decide⟩),
   .op (.Dup ⟨11, by decide⟩),
   .op (.Dup ⟨5, by decide⟩),
   .op .MULMOD,
   .op .ADD,
   .op (.Dup ⟨13, by decide⟩),
   .op (.Dup ⟨10, by decide⟩),
   .op (.Dup ⟨4, by decide⟩),
   .op .MULMOD,
   .op .ADD,
   .op (.Dup ⟨13, by decide⟩),
   .push 1 160,
   .op .MLOAD,
   .op (.Dup ⟨3, by decide⟩),
   .op .MULMOD,
   .op .ADD,
   .op (.Dup ⟨13, by decide⟩),
   .op (.Swap ⟨0, by decide⟩),
   .push 2 2048,
   .op .MULMOD]

def prCol2Model (s : State) (c q1 q0 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp : UInt256) (rest : List UInt256) : State :=
  let v0 : UInt256 := MachineState.readWord s.memory 64
  let v1 : UInt256 := x0 * v0
  let v2 : UInt256 := v1 + c
  let v3 : UInt256 := MachineState.readWord s.memory 32
  let v4 : UInt256 := x1 * v3
  let v5 : UInt256 := v4 + v2
  let v6 : UInt256 := MachineState.readWord s.memory 0
  let v7 : UInt256 := x2 * v6
  let v8 : UInt256 := v7 + v5
  let v9 : UInt256 := q0 * n2
  let v10 : UInt256 := v9 + v8
  let v11 : UInt256 := q1 * n1
  let v12 : UInt256 := v11 + v10
  let v13 : UInt256 := inv * v12
  let v14 : UInt256 := UInt256.shiftRight v13 (UInt256.ofNat 16)
  let v15 : UInt256 := MachineState.readWord s.memory 64
  let v16 : UInt256 := UInt256.mulMod x0 v15 P
  let v17 : UInt256 := v16 + c
  let v18 : UInt256 := MachineState.readWord s.memory 32
  let v19 : UInt256 := UInt256.mulMod x1 v18 P
  let v20 : UInt256 := v19 + v17
  let v21 : UInt256 := MachineState.readWord s.memory 0
  let v22 : UInt256 := UInt256.mulMod x2 v21 P
  let v23 : UInt256 := v22 + v20
  let v24 : UInt256 := UInt256.mulMod q0 n2 P
  let v25 : UInt256 := v24 + v23
  let v26 : UInt256 := UInt256.mulMod q1 n1 P
  let v27 : UInt256 := v26 + v25
  let v28 : UInt256 := MachineState.readWord s.memory 160
  let v29 : UInt256 := UInt256.mulMod v14 v28 P
  let v30 : UInt256 := v29 + v27
  let v31 : UInt256 := UInt256.mulMod (UInt256.ofNat 2048) v30 P
  {s with pc := UInt256.ofNat 3334, memory := s.memory, stack := v31 :: v14 :: q1 :: q0 :: x0 :: x1 :: x2 :: x3 :: x4 :: n1 :: n2 :: n3 :: n4 :: P :: inv :: cntp :: rest}

theorem prCol2_run (s : State) (c q1 q0 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions prCol2Program {s with pc := UInt256.ofNat 3256, stack := c :: q1 :: q0 :: x0 :: x1 :: x2 :: x3 :: x4 :: n1 :: n2 :: n3 :: n4 :: P :: inv :: cntp :: rest} =
      some (prCol2Model s c q1 q0 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp rest) := by
  let v0 : UInt256 := MachineState.readWord s.memory 64
  let v1 : UInt256 := x0 * v0
  let v2 : UInt256 := v1 + c
  let v3 : UInt256 := MachineState.readWord s.memory 32
  let v4 : UInt256 := x1 * v3
  let v5 : UInt256 := v4 + v2
  let v6 : UInt256 := MachineState.readWord s.memory 0
  let v7 : UInt256 := x2 * v6
  let v8 : UInt256 := v7 + v5
  let v9 : UInt256 := q0 * n2
  let v10 : UInt256 := v9 + v8
  let v11 : UInt256 := q1 * n1
  let v12 : UInt256 := v11 + v10
  let v13 : UInt256 := inv * v12
  let v14 : UInt256 := UInt256.shiftRight v13 (UInt256.ofNat 16)
  let v15 : UInt256 := MachineState.readWord s.memory 64
  let v16 : UInt256 := UInt256.mulMod x0 v15 P
  let v17 : UInt256 := v16 + c
  let v18 : UInt256 := MachineState.readWord s.memory 32
  let v19 : UInt256 := UInt256.mulMod x1 v18 P
  let v20 : UInt256 := v19 + v17
  let v21 : UInt256 := MachineState.readWord s.memory 0
  let v22 : UInt256 := UInt256.mulMod x2 v21 P
  let v23 : UInt256 := v22 + v20
  let v24 : UInt256 := UInt256.mulMod q0 n2 P
  let v25 : UInt256 := v24 + v23
  let v26 : UInt256 := UInt256.mulMod q1 n1 P
  let v27 : UInt256 := v26 + v25
  let v28 : UInt256 := MachineState.readWord s.memory 160
  let v29 : UInt256 := UInt256.mulMod v14 v28 P
  let v30 : UInt256 := v29 + v27
  let v31 : UInt256 := UInt256.mulMod (UInt256.ofNat 2048) v30 P
  have h0 : runInstructions prCol2part0Program {s with pc := UInt256.ofNat 3256, memory := s.memory, stack := c :: q1 :: q0 :: x0 :: x1 :: x2 :: x3 :: x4 :: n1 :: n2 :: n3 :: n4 :: P :: inv :: cntp :: rest} = some {s with pc := UInt256.ofNat 3264, memory := s.memory, stack := v2 :: c :: q1 :: q0 :: x0 :: x1 :: x2 :: x3 :: x4 :: n1 :: n2 :: n3 :: n4 :: P :: inv :: cntp :: rest} := by
    simpa only [prCol2part0Model, v0, v1, v2] using prCol2part0_run (s) c q1 q0 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp rest hcap hact
  have h1 : runInstructions prCol2part1Program {s with pc := UInt256.ofNat 3264, memory := s.memory, stack := v2 :: c :: q1 :: q0 :: x0 :: x1 :: x2 :: x3 :: x4 :: n1 :: n2 :: n3 :: n4 :: P :: inv :: cntp :: rest} = some {s with pc := UInt256.ofNat 3274, memory := s.memory, stack := x2 :: v6 :: v5 :: c :: q1 :: q0 :: x0 :: x1 :: x2 :: x3 :: x4 :: n1 :: n2 :: n3 :: n4 :: P :: inv :: cntp :: rest} := by
    simpa only [prCol2part1Model, v3, v4, v5, v6] using prCol2part1_run (s) v2 c q1 q0 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp rest hcap hact
  have h2 : runInstructions prCol2part2Program {s with pc := UInt256.ofNat 3274, memory := s.memory, stack := x2 :: v6 :: v5 :: c :: q1 :: q0 :: x0 :: x1 :: x2 :: x3 :: x4 :: n1 :: n2 :: n3 :: n4 :: P :: inv :: cntp :: rest} = some {s with pc := UInt256.ofNat 3282, memory := s.memory, stack := q1 :: n1 :: v10 :: c :: q1 :: q0 :: x0 :: x1 :: x2 :: x3 :: x4 :: n1 :: n2 :: n3 :: n4 :: P :: inv :: cntp :: rest} := by
    simpa only [prCol2part2Model, v7, v8, v9, v10] using prCol2part2_run (s) x2 v6 v5 c q1 q0 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp rest hcap hact
  have h3 : runInstructions prCol2part3Program {s with pc := UInt256.ofNat 3282, memory := s.memory, stack := q1 :: n1 :: v10 :: c :: q1 :: q0 :: x0 :: x1 :: x2 :: x3 :: x4 :: n1 :: n2 :: n3 :: n4 :: P :: inv :: cntp :: rest} = some {s with pc := UInt256.ofNat 3291, memory := s.memory, stack := P :: c :: v14 :: q1 :: q0 :: x0 :: x1 :: x2 :: x3 :: x4 :: n1 :: n2 :: n3 :: n4 :: P :: inv :: cntp :: rest} := by
    simpa only [prCol2part3Model, v11, v12, v13, v14] using prCol2part3_run (s) q1 n1 v10 c q1 q0 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp rest hcap hact
  have h4 : runInstructions prCol2part4Program {s with pc := UInt256.ofNat 3291, memory := s.memory, stack := P :: c :: v14 :: q1 :: q0 :: x0 :: x1 :: x2 :: x3 :: x4 :: n1 :: n2 :: n3 :: n4 :: P :: inv :: cntp :: rest} = some {s with pc := UInt256.ofNat 3301, memory := s.memory, stack := v18 :: P :: v17 :: v14 :: q1 :: q0 :: x0 :: x1 :: x2 :: x3 :: x4 :: n1 :: n2 :: n3 :: n4 :: P :: inv :: cntp :: rest} := by
    simpa only [prCol2part4Model, v15, v16, v17, v18] using prCol2part4_run (s) P c v14 q1 q0 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp rest hcap hact
  have h5 : runInstructions prCol2part5Program {s with pc := UInt256.ofNat 3301, memory := s.memory, stack := v18 :: P :: v17 :: v14 :: q1 :: q0 :: x0 :: x1 :: x2 :: x3 :: x4 :: n1 :: n2 :: n3 :: n4 :: P :: inv :: cntp :: rest} = some {s with pc := UInt256.ofNat 3310, memory := s.memory, stack := v22 :: v20 :: v14 :: q1 :: q0 :: x0 :: x1 :: x2 :: x3 :: x4 :: n1 :: n2 :: n3 :: n4 :: P :: inv :: cntp :: rest} := by
    simpa only [prCol2part5Model, v19, v20, v21, v22] using prCol2part5_run (s) v18 P v17 v14 q1 q0 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp rest hcap hact
  have h6 : runInstructions prCol2part6Program {s with pc := UInt256.ofNat 3310, memory := s.memory, stack := v22 :: v20 :: v14 :: q1 :: q0 :: x0 :: x1 :: x2 :: x3 :: x4 :: n1 :: n2 :: n3 :: n4 :: P :: inv :: cntp :: rest} = some {s with pc := UInt256.ofNat 3318, memory := s.memory, stack := n1 :: P :: v25 :: v14 :: q1 :: q0 :: x0 :: x1 :: x2 :: x3 :: x4 :: n1 :: n2 :: n3 :: n4 :: P :: inv :: cntp :: rest} := by
    simpa only [prCol2part6Model, v23, v24, v25] using prCol2part6_run (s) v22 v20 v14 q1 q0 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp rest hcap hact
  have h7 : runInstructions prCol2part7Program {s with pc := UInt256.ofNat 3318, memory := s.memory, stack := n1 :: P :: v25 :: v14 :: q1 :: q0 :: x0 :: x1 :: x2 :: x3 :: x4 :: n1 :: n2 :: n3 :: n4 :: P :: inv :: cntp :: rest} = some {s with pc := UInt256.ofNat 3327, memory := s.memory, stack := v29 :: v27 :: v14 :: q1 :: q0 :: x0 :: x1 :: x2 :: x3 :: x4 :: n1 :: n2 :: n3 :: n4 :: P :: inv :: cntp :: rest} := by
    simpa only [prCol2part7Model, v26, v27, v28, v29] using prCol2part7_run (s) n1 P v25 v14 q1 q0 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp rest hcap hact
  have h8 : runInstructions prCol2part8Program {s with pc := UInt256.ofNat 3327, memory := s.memory, stack := v29 :: v27 :: v14 :: q1 :: q0 :: x0 :: x1 :: x2 :: x3 :: x4 :: n1 :: n2 :: n3 :: n4 :: P :: inv :: cntp :: rest} = some {s with pc := UInt256.ofNat 3334, memory := s.memory, stack := v31 :: v14 :: q1 :: q0 :: x0 :: x1 :: x2 :: x3 :: x4 :: n1 :: n2 :: n3 :: n4 :: P :: inv :: cntp :: rest} := by
    simpa only [prCol2part8Model, v30, v31] using prCol2part8_run (s) v29 v27 v14 q1 q0 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp rest hcap hact
  exact (runInstructions_append_some _ _ _ _ _ h0 (runInstructions_append_some _ _ _ _ _ h1 (runInstructions_append_some _ _ _ _ _ h2 (runInstructions_append_some _ _ _ _ _ h3 (runInstructions_append_some _ _ _ _ _ h4 (runInstructions_append_some _ _ _ _ _ h5 (runInstructions_append_some _ _ _ _ _ h6 (runInstructions_append_some _ _ _ _ _ h7 h8))))))))

def prCol2_o0 (c q1 q0 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp b0 b1 b2 n0 : UInt256) : UInt256 :=
  (UInt256.mulMod (UInt256.ofNat 2048) ((UInt256.mulMod (UInt256.shiftRight (inv * ((q1 * n1) + ((q0 * n2) + ((x2 * b0) + ((x1 * b1) + ((x0 * b2) + c)))))) (UInt256.ofNat 16)) n0 P) + ((UInt256.mulMod q1 n1 P) + ((UInt256.mulMod q0 n2 P) + ((UInt256.mulMod x2 b0 P) + ((UInt256.mulMod x1 b1 P) + ((UInt256.mulMod x0 b2 P) + c)))))) P)

def prCol2_o1 (c q1 q0 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp b0 b1 b2 n0 : UInt256) : UInt256 :=
  (UInt256.shiftRight (inv * ((q1 * n1) + ((q0 * n2) + ((x2 * b0) + ((x1 * b1) + ((x0 * b2) + c)))))) (UInt256.ofNat 16))

theorem prCol2_eq (s : State) (c q1 q0 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp b0 b1 b2 n0 : UInt256) (rest : List UInt256)
    (h_b0 : MachineState.readWord s.memory 0 = b0)
    (h_b1 : MachineState.readWord s.memory 32 = b1)
    (h_b2 : MachineState.readWord s.memory 64 = b2)
    (h_n0 : MachineState.readWord s.memory 160 = n0) :
    prCol2Model s c q1 q0 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp rest =
      {s with pc := UInt256.ofNat 3334, stack := (prCol2_o0 c q1 q0 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp b0 b1 b2 n0) :: (prCol2_o1 c q1 q0 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp b0 b1 b2 n0) :: q1 :: q0 :: x0 :: x1 :: x2 :: x3 :: x4 :: n1 :: n2 :: n3 :: n4 :: P :: inv :: cntp :: rest} := by
  simp only [prCol2Model, prCol2_o0, prCol2_o1, h_b0, h_b1, h_b2, h_n0]

/-! ## prCol3: pc 3334..3433, 87 instructions -/

def prCol3part0Program : List Instr :=
  [.op (.Dup ⟨0, by decide⟩),
   .push 1 96,
   .op .MLOAD,
   .op (.Dup ⟨6, by decide⟩),
   .op .MUL,
   .op .ADD,
   .push 1 64,
   .op .MLOAD]

def prCol3part0Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 : UInt256) (rest : List UInt256) : State :=
  let v0 : UInt256 := MachineState.readWord s.memory 96
  let v1 : UInt256 := x4 * v0
  let v2 : UInt256 := v1 + x0
  let v3 : UInt256 := MachineState.readWord s.memory 64
  {s with pc := UInt256.ofNat 3344, memory := s.memory, stack := v3 :: v2 :: x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: rest}

theorem prCol3part0_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions prCol3part0Program {s with pc := UInt256.ofNat 3334, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: rest} =
      some (prCol3part0Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 rest) := by
  have hc (j : Nat) (hj : j ≤ 32) : rest.length + j < 1024 := by omega
  have hcr : rest.length < 1024 := by omega
  have ha96 : (96 : UInt256).toNat = 96 := rfl
  have hf96 := activeWords_fix s 96 32 (by decide) (by norm_num) hact
  have ha64 : (64 : UInt256).toNat = 64 := rfl
  have hf64 := activeWords_fix s 64 32 (by decide) (by norm_num) hact
  simp [hz, hzn, prCol3part0Program, prCol3part0Model, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, ofNat_sub_ofNat, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, hc, hcr, ha96, hf96, ha64, hf64]

def prCol3part1Program : List Instr :=
  [.op (.Dup ⟨7, by decide⟩),
   .op .MUL,
   .op .ADD,
   .push 1 32,
   .op .MLOAD,
   .op (.Dup ⟨8, by decide⟩),
   .op .MUL,
   .op .ADD]

def prCol3part1Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 : UInt256) (rest : List UInt256) : State :=
  let v0 : UInt256 := x7 * x0
  let v1 : UInt256 := v0 + x1
  let v2 : UInt256 := MachineState.readWord s.memory 32
  let v3 : UInt256 := x8 * v2
  let v4 : UInt256 := v3 + v1
  {s with pc := UInt256.ofNat 3353, memory := s.memory, stack := v4 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: rest}

theorem prCol3part1_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions prCol3part1Program {s with pc := UInt256.ofNat 3344, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: rest} =
      some (prCol3part1Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 rest) := by
  have hc (j : Nat) (hj : j ≤ 32) : rest.length + j < 1024 := by omega
  have hcr : rest.length < 1024 := by omega
  have ha32 : (32 : UInt256).toNat = 32 := rfl
  have hf32 := activeWords_fix s 32 32 (by decide) (by norm_num) hact
  simp [hz, hzn, prCol3part1Program, prCol3part1Model, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, ofNat_sub_ofNat, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, hc, hcr, ha32, hf32]

def prCol3part2Program : List Instr :=
  [.push 1 0,
   .op .MLOAD,
   .op (.Dup ⟨9, by decide⟩),
   .op .MUL,
   .op .ADD,
   .op (.Dup ⟨12, by decide⟩),
   .op (.Dup ⟨5, by decide⟩),
   .op .MUL]

def prCol3part2Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 : UInt256) (rest : List UInt256) : State :=
  let v0 : UInt256 := MachineState.readWord s.memory 0
  let v1 : UInt256 := x8 * v0
  let v2 : UInt256 := v1 + x0
  let v3 : UInt256 := x4 * x12
  {s with pc := UInt256.ofNat 3362, memory := s.memory, stack := v3 :: v2 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: rest}

theorem prCol3part2_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions prCol3part2Program {s with pc := UInt256.ofNat 3353, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: rest} =
      some (prCol3part2Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 rest) := by
  have hc (j : Nat) (hj : j ≤ 32) : rest.length + j < 1024 := by omega
  have hcr : rest.length < 1024 := by omega
  have ha0 : (0 : UInt256).toNat = 0 := rfl
  have hf0 := activeWords_fix s 0 32 (by decide) (by norm_num) hact
  simp [hz, hzn, prCol3part2Program, prCol3part2Model, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, ofNat_sub_ofNat, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, hc, hcr, ha0, hf0]

def prCol3part3Program : List Instr :=
  [.op .ADD,
   .op (.Dup ⟨11, by decide⟩),
   .op (.Dup ⟨4, by decide⟩),
   .op .MUL,
   .op .ADD,
   .op (.Dup ⟨10, by decide⟩),
   .op (.Dup ⟨3, by decide⟩),
   .op .MUL]

def prCol3part3Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 : UInt256) (rest : List UInt256) : State :=
  let v0 : UInt256 := x0 + x1
  let v1 : UInt256 := x4 * x12
  let v2 : UInt256 := v1 + v0
  let v3 : UInt256 := x3 * x11
  {s with pc := UInt256.ofNat 3370, memory := s.memory, stack := v3 :: v2 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: rest}

theorem prCol3part3_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions prCol3part3Program {s with pc := UInt256.ofNat 3362, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: rest} =
      some (prCol3part3Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 rest) := by
  have hc (j : Nat) (hj : j ≤ 32) : rest.length + j < 1024 := by omega
  have hcr : rest.length < 1024 := by omega
  simp [hz, hzn, prCol3part3Program, prCol3part3Model, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, ofNat_sub_ofNat, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, hc, hcr]

def prCol3part4Program : List Instr :=
  [.op .ADD,
   .op (.Dup ⟨15, by decide⟩),
   .op .MUL,
   .push 1 16,
   .op .SHR,
   .op (.Swap ⟨0, by decide⟩),
   .op (.Dup ⟨14, by decide⟩)]

def prCol3part4Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 : UInt256) (rest : List UInt256) : State :=
  let v0 : UInt256 := x0 + x1
  let v1 : UInt256 := x16 * v0
  let v2 : UInt256 := UInt256.shiftRight v1 (UInt256.ofNat 16)
  {s with pc := UInt256.ofNat 3378, memory := s.memory, stack := x15 :: x2 :: v2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: rest}

theorem prCol3part4_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions prCol3part4Program {s with pc := UInt256.ofNat 3370, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: rest} =
      some (prCol3part4Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 rest) := by
  have hc (j : Nat) (hj : j ≤ 31) : rest.length + j < 1024 := by omega
  have hcr : rest.length < 1024 := by omega
  simp [hz, hzn, prCol3part4Program, prCol3part4Model, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, ofNat_sub_ofNat, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, hc, hcr]

def prCol3part5Program : List Instr :=
  [.push 1 96,
   .op .MLOAD,
   .op (.Dup ⟨7, by decide⟩),
   .op .MULMOD,
   .op .ADD,
   .op (.Dup ⟨14, by decide⟩),
   .push 1 64,
   .op .MLOAD]

def prCol3part5Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 : UInt256) (rest : List UInt256) : State :=
  let v0 : UInt256 := MachineState.readWord s.memory 96
  let v1 : UInt256 := UInt256.mulMod x6 v0 x0
  let v2 : UInt256 := v1 + x1
  let v3 : UInt256 := MachineState.readWord s.memory 64
  {s with pc := UInt256.ofNat 3388, memory := s.memory, stack := v3 :: x15 :: v2 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: rest}

theorem prCol3part5_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions prCol3part5Program {s with pc := UInt256.ofNat 3378, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: rest} =
      some (prCol3part5Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 rest) := by
  have hc (j : Nat) (hj : j ≤ 33) : rest.length + j < 1024 := by omega
  have hcr : rest.length < 1024 := by omega
  have ha96 : (96 : UInt256).toNat = 96 := rfl
  have hf96 := activeWords_fix s 96 32 (by decide) (by norm_num) hact
  have ha64 : (64 : UInt256).toNat = 64 := rfl
  have hf64 := activeWords_fix s 64 32 (by decide) (by norm_num) hact
  simp [hz, hzn, prCol3part5Program, prCol3part5Model, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, ofNat_sub_ofNat, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, hc, hcr, ha96, hf96, ha64, hf64]

def prCol3part6Program : List Instr :=
  [.op (.Dup ⟨8, by decide⟩),
   .op .MULMOD,
   .op .ADD,
   .op (.Dup ⟨14, by decide⟩),
   .push 1 32,
   .op .MLOAD,
   .op (.Dup ⟨9, by decide⟩),
   .op .MULMOD]

def prCol3part6Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 : UInt256) (rest : List UInt256) : State :=
  let v0 : UInt256 := UInt256.mulMod x8 x0 x1
  let v1 : UInt256 := v0 + x2
  let v2 : UInt256 := MachineState.readWord s.memory 32
  let v3 : UInt256 := UInt256.mulMod x9 v2 x16
  {s with pc := UInt256.ofNat 3397, memory := s.memory, stack := v3 :: v1 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: x18 :: rest}

theorem prCol3part6_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions prCol3part6Program {s with pc := UInt256.ofNat 3388, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: x18 :: rest} =
      some (prCol3part6Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 rest) := by
  have hc (j : Nat) (hj : j ≤ 33) : rest.length + j < 1024 := by omega
  have hcr : rest.length < 1024 := by omega
  have ha32 : (32 : UInt256).toNat = 32 := rfl
  have hf32 := activeWords_fix s 32 32 (by decide) (by norm_num) hact
  simp [hz, hzn, prCol3part6Program, prCol3part6Model, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, ofNat_sub_ofNat, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, hc, hcr, ha32, hf32]

def prCol3part7Program : List Instr :=
  [.op .ADD,
   .op (.Dup ⟨14, by decide⟩),
   .push 1 0,
   .op .MLOAD,
   .op (.Dup ⟨10, by decide⟩),
   .op .MULMOD,
   .op .ADD,
   .op (.Dup ⟨14, by decide⟩)]

def prCol3part7Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 : UInt256) (rest : List UInt256) : State :=
  let v0 : UInt256 := x0 + x1
  let v1 : UInt256 := MachineState.readWord s.memory 0
  let v2 : UInt256 := UInt256.mulMod x9 v1 x15
  let v3 : UInt256 := v2 + v0
  {s with pc := UInt256.ofNat 3406, memory := s.memory, stack := x15 :: v3 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: rest}

theorem prCol3part7_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions prCol3part7Program {s with pc := UInt256.ofNat 3397, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: rest} =
      some (prCol3part7Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 rest) := by
  have hc (j : Nat) (hj : j ≤ 33) : rest.length + j < 1024 := by omega
  have hcr : rest.length < 1024 := by omega
  have ha0 : (0 : UInt256).toNat = 0 := rfl
  have hf0 := activeWords_fix s 0 32 (by decide) (by norm_num) hact
  simp [hz, hzn, prCol3part7Program, prCol3part7Model, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, ofNat_sub_ofNat, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, hc, hcr, ha0, hf0]

def prCol3part8Program : List Instr :=
  [.op (.Dup ⟨13, by decide⟩),
   .op (.Dup ⟨6, by decide⟩),
   .op .MULMOD,
   .op .ADD,
   .op (.Dup ⟨14, by decide⟩),
   .op (.Dup ⟨12, by decide⟩),
   .op (.Dup ⟨5, by decide⟩),
   .op .MULMOD]

def prCol3part8Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 : UInt256) (rest : List UInt256) : State :=
  let v0 : UInt256 := UInt256.mulMod x5 x13 x0
  let v1 : UInt256 := v0 + x1
  let v2 : UInt256 := UInt256.mulMod x4 x12 x15
  {s with pc := UInt256.ofNat 3414, memory := s.memory, stack := v2 :: v1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: rest}

theorem prCol3part8_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions prCol3part8Program {s with pc := UInt256.ofNat 3406, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: rest} =
      some (prCol3part8Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 rest) := by
  have hc (j : Nat) (hj : j ≤ 33) : rest.length + j < 1024 := by omega
  have hcr : rest.length < 1024 := by omega
  simp [hz, hzn, prCol3part8Program, prCol3part8Model, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, ofNat_sub_ofNat, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, hc, hcr]

def prCol3part9Program : List Instr :=
  [.op .ADD,
   .op (.Dup ⟨14, by decide⟩),
   .op (.Dup ⟨11, by decide⟩),
   .op (.Dup ⟨4, by decide⟩),
   .op .MULMOD,
   .op .ADD,
   .op (.Dup ⟨14, by decide⟩)]

def prCol3part9Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 : UInt256) (rest : List UInt256) : State :=
  let v0 : UInt256 := x0 + x1
  let v1 : UInt256 := UInt256.mulMod x3 x11 x15
  let v2 : UInt256 := v1 + v0
  {s with pc := UInt256.ofNat 3421, memory := s.memory, stack := x15 :: v2 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: rest}

theorem prCol3part9_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions prCol3part9Program {s with pc := UInt256.ofNat 3414, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: rest} =
      some (prCol3part9Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 rest) := by
  have hc (j : Nat) (hj : j ≤ 33) : rest.length + j < 1024 := by omega
  have hcr : rest.length < 1024 := by omega
  simp [hz, hzn, prCol3part9Program, prCol3part9Model, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, ofNat_sub_ofNat, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, hc, hcr]

def prCol3part10Program : List Instr :=
  [.push 1 160,
   .op .MLOAD,
   .op (.Dup ⟨3, by decide⟩),
   .op .MULMOD,
   .op .ADD,
   .op (.Dup ⟨14, by decide⟩),
   .op (.Swap ⟨0, by decide⟩)]

def prCol3part10Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 : UInt256) (rest : List UInt256) : State :=
  let v0 : UInt256 := MachineState.readWord s.memory 160
  let v1 : UInt256 := UInt256.mulMod x2 v0 x0
  let v2 : UInt256 := v1 + x1
  {s with pc := UInt256.ofNat 3429, memory := s.memory, stack := v2 :: x15 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: rest}

theorem prCol3part10_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions prCol3part10Program {s with pc := UInt256.ofNat 3421, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: rest} =
      some (prCol3part10Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 rest) := by
  have hc (j : Nat) (hj : j ≤ 33) : rest.length + j < 1024 := by omega
  have hcr : rest.length < 1024 := by omega
  have ha160 : (160 : UInt256).toNat = 160 := rfl
  have hf160 := activeWords_fix s 160 32 (by decide) (by norm_num) hact
  simp [hz, hzn, prCol3part10Program, prCol3part10Model, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, ofNat_sub_ofNat, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, hc, hcr, ha160, hf160]

def prCol3part11Program : List Instr :=
  [.push 2 2048,
   .op .MULMOD]

def prCol3part11Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 : UInt256) (rest : List UInt256) : State :=
  let v0 : UInt256 := UInt256.mulMod (UInt256.ofNat 2048) x0 x1
  {s with pc := UInt256.ofNat 3433, memory := s.memory, stack := v0 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: rest}

theorem prCol3part11_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions prCol3part11Program {s with pc := UInt256.ofNat 3429, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: rest} =
      some (prCol3part11Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 rest) := by
  have hc (j : Nat) (hj : j ≤ 32) : rest.length + j < 1024 := by omega
  have hcr : rest.length < 1024 := by omega
  simp [hz, hzn, prCol3part11Program, prCol3part11Model, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, ofNat_sub_ofNat, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, hc, hcr]

def prCol3Program : List Instr :=
  [.op (.Dup ⟨0, by decide⟩),
   .push 1 96,
   .op .MLOAD,
   .op (.Dup ⟨6, by decide⟩),
   .op .MUL,
   .op .ADD,
   .push 1 64,
   .op .MLOAD,
   .op (.Dup ⟨7, by decide⟩),
   .op .MUL,
   .op .ADD,
   .push 1 32,
   .op .MLOAD,
   .op (.Dup ⟨8, by decide⟩),
   .op .MUL,
   .op .ADD,
   .push 1 0,
   .op .MLOAD,
   .op (.Dup ⟨9, by decide⟩),
   .op .MUL,
   .op .ADD,
   .op (.Dup ⟨12, by decide⟩),
   .op (.Dup ⟨5, by decide⟩),
   .op .MUL,
   .op .ADD,
   .op (.Dup ⟨11, by decide⟩),
   .op (.Dup ⟨4, by decide⟩),
   .op .MUL,
   .op .ADD,
   .op (.Dup ⟨10, by decide⟩),
   .op (.Dup ⟨3, by decide⟩),
   .op .MUL,
   .op .ADD,
   .op (.Dup ⟨15, by decide⟩),
   .op .MUL,
   .push 1 16,
   .op .SHR,
   .op (.Swap ⟨0, by decide⟩),
   .op (.Dup ⟨14, by decide⟩),
   .push 1 96,
   .op .MLOAD,
   .op (.Dup ⟨7, by decide⟩),
   .op .MULMOD,
   .op .ADD,
   .op (.Dup ⟨14, by decide⟩),
   .push 1 64,
   .op .MLOAD,
   .op (.Dup ⟨8, by decide⟩),
   .op .MULMOD,
   .op .ADD,
   .op (.Dup ⟨14, by decide⟩),
   .push 1 32,
   .op .MLOAD,
   .op (.Dup ⟨9, by decide⟩),
   .op .MULMOD,
   .op .ADD,
   .op (.Dup ⟨14, by decide⟩),
   .push 1 0,
   .op .MLOAD,
   .op (.Dup ⟨10, by decide⟩),
   .op .MULMOD,
   .op .ADD,
   .op (.Dup ⟨14, by decide⟩),
   .op (.Dup ⟨13, by decide⟩),
   .op (.Dup ⟨6, by decide⟩),
   .op .MULMOD,
   .op .ADD,
   .op (.Dup ⟨14, by decide⟩),
   .op (.Dup ⟨12, by decide⟩),
   .op (.Dup ⟨5, by decide⟩),
   .op .MULMOD,
   .op .ADD,
   .op (.Dup ⟨14, by decide⟩),
   .op (.Dup ⟨11, by decide⟩),
   .op (.Dup ⟨4, by decide⟩),
   .op .MULMOD,
   .op .ADD,
   .op (.Dup ⟨14, by decide⟩),
   .push 1 160,
   .op .MLOAD,
   .op (.Dup ⟨3, by decide⟩),
   .op .MULMOD,
   .op .ADD,
   .op (.Dup ⟨14, by decide⟩),
   .op (.Swap ⟨0, by decide⟩),
   .push 2 2048,
   .op .MULMOD]

def prCol3Model (s : State) (c q2 q1 q0 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp : UInt256) (rest : List UInt256) : State :=
  let v0 : UInt256 := MachineState.readWord s.memory 96
  let v1 : UInt256 := x0 * v0
  let v2 : UInt256 := v1 + c
  let v3 : UInt256 := MachineState.readWord s.memory 64
  let v4 : UInt256 := x1 * v3
  let v5 : UInt256 := v4 + v2
  let v6 : UInt256 := MachineState.readWord s.memory 32
  let v7 : UInt256 := x2 * v6
  let v8 : UInt256 := v7 + v5
  let v9 : UInt256 := MachineState.readWord s.memory 0
  let v10 : UInt256 := x3 * v9
  let v11 : UInt256 := v10 + v8
  let v12 : UInt256 := q0 * n3
  let v13 : UInt256 := v12 + v11
  let v14 : UInt256 := q1 * n2
  let v15 : UInt256 := v14 + v13
  let v16 : UInt256 := q2 * n1
  let v17 : UInt256 := v16 + v15
  let v18 : UInt256 := inv * v17
  let v19 : UInt256 := UInt256.shiftRight v18 (UInt256.ofNat 16)
  let v20 : UInt256 := MachineState.readWord s.memory 96
  let v21 : UInt256 := UInt256.mulMod x0 v20 P
  let v22 : UInt256 := v21 + c
  let v23 : UInt256 := MachineState.readWord s.memory 64
  let v24 : UInt256 := UInt256.mulMod x1 v23 P
  let v25 : UInt256 := v24 + v22
  let v26 : UInt256 := MachineState.readWord s.memory 32
  let v27 : UInt256 := UInt256.mulMod x2 v26 P
  let v28 : UInt256 := v27 + v25
  let v29 : UInt256 := MachineState.readWord s.memory 0
  let v30 : UInt256 := UInt256.mulMod x3 v29 P
  let v31 : UInt256 := v30 + v28
  let v32 : UInt256 := UInt256.mulMod q0 n3 P
  let v33 : UInt256 := v32 + v31
  let v34 : UInt256 := UInt256.mulMod q1 n2 P
  let v35 : UInt256 := v34 + v33
  let v36 : UInt256 := UInt256.mulMod q2 n1 P
  let v37 : UInt256 := v36 + v35
  let v38 : UInt256 := MachineState.readWord s.memory 160
  let v39 : UInt256 := UInt256.mulMod v19 v38 P
  let v40 : UInt256 := v39 + v37
  let v41 : UInt256 := UInt256.mulMod (UInt256.ofNat 2048) v40 P
  {s with pc := UInt256.ofNat 3433, memory := s.memory, stack := v41 :: v19 :: q2 :: q1 :: q0 :: x0 :: x1 :: x2 :: x3 :: x4 :: n1 :: n2 :: n3 :: n4 :: P :: inv :: cntp :: rest}

theorem prCol3_run (s : State) (c q2 q1 q0 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions prCol3Program {s with pc := UInt256.ofNat 3334, stack := c :: q2 :: q1 :: q0 :: x0 :: x1 :: x2 :: x3 :: x4 :: n1 :: n2 :: n3 :: n4 :: P :: inv :: cntp :: rest} =
      some (prCol3Model s c q2 q1 q0 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp rest) := by
  let v0 : UInt256 := MachineState.readWord s.memory 96
  let v1 : UInt256 := x0 * v0
  let v2 : UInt256 := v1 + c
  let v3 : UInt256 := MachineState.readWord s.memory 64
  let v4 : UInt256 := x1 * v3
  let v5 : UInt256 := v4 + v2
  let v6 : UInt256 := MachineState.readWord s.memory 32
  let v7 : UInt256 := x2 * v6
  let v8 : UInt256 := v7 + v5
  let v9 : UInt256 := MachineState.readWord s.memory 0
  let v10 : UInt256 := x3 * v9
  let v11 : UInt256 := v10 + v8
  let v12 : UInt256 := q0 * n3
  let v13 : UInt256 := v12 + v11
  let v14 : UInt256 := q1 * n2
  let v15 : UInt256 := v14 + v13
  let v16 : UInt256 := q2 * n1
  let v17 : UInt256 := v16 + v15
  let v18 : UInt256 := inv * v17
  let v19 : UInt256 := UInt256.shiftRight v18 (UInt256.ofNat 16)
  let v20 : UInt256 := MachineState.readWord s.memory 96
  let v21 : UInt256 := UInt256.mulMod x0 v20 P
  let v22 : UInt256 := v21 + c
  let v23 : UInt256 := MachineState.readWord s.memory 64
  let v24 : UInt256 := UInt256.mulMod x1 v23 P
  let v25 : UInt256 := v24 + v22
  let v26 : UInt256 := MachineState.readWord s.memory 32
  let v27 : UInt256 := UInt256.mulMod x2 v26 P
  let v28 : UInt256 := v27 + v25
  let v29 : UInt256 := MachineState.readWord s.memory 0
  let v30 : UInt256 := UInt256.mulMod x3 v29 P
  let v31 : UInt256 := v30 + v28
  let v32 : UInt256 := UInt256.mulMod q0 n3 P
  let v33 : UInt256 := v32 + v31
  let v34 : UInt256 := UInt256.mulMod q1 n2 P
  let v35 : UInt256 := v34 + v33
  let v36 : UInt256 := UInt256.mulMod q2 n1 P
  let v37 : UInt256 := v36 + v35
  let v38 : UInt256 := MachineState.readWord s.memory 160
  let v39 : UInt256 := UInt256.mulMod v19 v38 P
  let v40 : UInt256 := v39 + v37
  let v41 : UInt256 := UInt256.mulMod (UInt256.ofNat 2048) v40 P
  have h0 : runInstructions prCol3part0Program {s with pc := UInt256.ofNat 3334, memory := s.memory, stack := c :: q2 :: q1 :: q0 :: x0 :: x1 :: x2 :: x3 :: x4 :: n1 :: n2 :: n3 :: n4 :: P :: inv :: cntp :: rest} = some {s with pc := UInt256.ofNat 3344, memory := s.memory, stack := v3 :: v2 :: c :: q2 :: q1 :: q0 :: x0 :: x1 :: x2 :: x3 :: x4 :: n1 :: n2 :: n3 :: n4 :: P :: inv :: cntp :: rest} := by
    simpa only [prCol3part0Model, v0, v1, v2, v3] using prCol3part0_run (s) c q2 q1 q0 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp rest hcap hact
  have h1 : runInstructions prCol3part1Program {s with pc := UInt256.ofNat 3344, memory := s.memory, stack := v3 :: v2 :: c :: q2 :: q1 :: q0 :: x0 :: x1 :: x2 :: x3 :: x4 :: n1 :: n2 :: n3 :: n4 :: P :: inv :: cntp :: rest} = some {s with pc := UInt256.ofNat 3353, memory := s.memory, stack := v8 :: c :: q2 :: q1 :: q0 :: x0 :: x1 :: x2 :: x3 :: x4 :: n1 :: n2 :: n3 :: n4 :: P :: inv :: cntp :: rest} := by
    simpa only [prCol3part1Model, v4, v5, v6, v7, v8] using prCol3part1_run (s) v3 v2 c q2 q1 q0 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp rest hcap hact
  have h2 : runInstructions prCol3part2Program {s with pc := UInt256.ofNat 3353, memory := s.memory, stack := v8 :: c :: q2 :: q1 :: q0 :: x0 :: x1 :: x2 :: x3 :: x4 :: n1 :: n2 :: n3 :: n4 :: P :: inv :: cntp :: rest} = some {s with pc := UInt256.ofNat 3362, memory := s.memory, stack := v12 :: v11 :: c :: q2 :: q1 :: q0 :: x0 :: x1 :: x2 :: x3 :: x4 :: n1 :: n2 :: n3 :: n4 :: P :: inv :: cntp :: rest} := by
    simpa only [prCol3part2Model, v9, v10, v11, v12] using prCol3part2_run (s) v8 c q2 q1 q0 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp rest hcap hact
  have h3 : runInstructions prCol3part3Program {s with pc := UInt256.ofNat 3362, memory := s.memory, stack := v12 :: v11 :: c :: q2 :: q1 :: q0 :: x0 :: x1 :: x2 :: x3 :: x4 :: n1 :: n2 :: n3 :: n4 :: P :: inv :: cntp :: rest} = some {s with pc := UInt256.ofNat 3370, memory := s.memory, stack := v16 :: v15 :: c :: q2 :: q1 :: q0 :: x0 :: x1 :: x2 :: x3 :: x4 :: n1 :: n2 :: n3 :: n4 :: P :: inv :: cntp :: rest} := by
    simpa only [prCol3part3Model, v13, v14, v15, v16] using prCol3part3_run (s) v12 v11 c q2 q1 q0 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp rest hcap hact
  have h4 : runInstructions prCol3part4Program {s with pc := UInt256.ofNat 3370, memory := s.memory, stack := v16 :: v15 :: c :: q2 :: q1 :: q0 :: x0 :: x1 :: x2 :: x3 :: x4 :: n1 :: n2 :: n3 :: n4 :: P :: inv :: cntp :: rest} = some {s with pc := UInt256.ofNat 3378, memory := s.memory, stack := P :: c :: v19 :: q2 :: q1 :: q0 :: x0 :: x1 :: x2 :: x3 :: x4 :: n1 :: n2 :: n3 :: n4 :: P :: inv :: cntp :: rest} := by
    simpa only [prCol3part4Model, v17, v18, v19] using prCol3part4_run (s) v16 v15 c q2 q1 q0 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp rest hcap hact
  have h5 : runInstructions prCol3part5Program {s with pc := UInt256.ofNat 3378, memory := s.memory, stack := P :: c :: v19 :: q2 :: q1 :: q0 :: x0 :: x1 :: x2 :: x3 :: x4 :: n1 :: n2 :: n3 :: n4 :: P :: inv :: cntp :: rest} = some {s with pc := UInt256.ofNat 3388, memory := s.memory, stack := v23 :: P :: v22 :: v19 :: q2 :: q1 :: q0 :: x0 :: x1 :: x2 :: x3 :: x4 :: n1 :: n2 :: n3 :: n4 :: P :: inv :: cntp :: rest} := by
    simpa only [prCol3part5Model, v20, v21, v22, v23] using prCol3part5_run (s) P c v19 q2 q1 q0 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp rest hcap hact
  have h6 : runInstructions prCol3part6Program {s with pc := UInt256.ofNat 3388, memory := s.memory, stack := v23 :: P :: v22 :: v19 :: q2 :: q1 :: q0 :: x0 :: x1 :: x2 :: x3 :: x4 :: n1 :: n2 :: n3 :: n4 :: P :: inv :: cntp :: rest} = some {s with pc := UInt256.ofNat 3397, memory := s.memory, stack := v27 :: v25 :: v19 :: q2 :: q1 :: q0 :: x0 :: x1 :: x2 :: x3 :: x4 :: n1 :: n2 :: n3 :: n4 :: P :: inv :: cntp :: rest} := by
    simpa only [prCol3part6Model, v24, v25, v26, v27] using prCol3part6_run (s) v23 P v22 v19 q2 q1 q0 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp rest hcap hact
  have h7 : runInstructions prCol3part7Program {s with pc := UInt256.ofNat 3397, memory := s.memory, stack := v27 :: v25 :: v19 :: q2 :: q1 :: q0 :: x0 :: x1 :: x2 :: x3 :: x4 :: n1 :: n2 :: n3 :: n4 :: P :: inv :: cntp :: rest} = some {s with pc := UInt256.ofNat 3406, memory := s.memory, stack := P :: v31 :: v19 :: q2 :: q1 :: q0 :: x0 :: x1 :: x2 :: x3 :: x4 :: n1 :: n2 :: n3 :: n4 :: P :: inv :: cntp :: rest} := by
    simpa only [prCol3part7Model, v28, v29, v30, v31] using prCol3part7_run (s) v27 v25 v19 q2 q1 q0 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp rest hcap hact
  have h8 : runInstructions prCol3part8Program {s with pc := UInt256.ofNat 3406, memory := s.memory, stack := P :: v31 :: v19 :: q2 :: q1 :: q0 :: x0 :: x1 :: x2 :: x3 :: x4 :: n1 :: n2 :: n3 :: n4 :: P :: inv :: cntp :: rest} = some {s with pc := UInt256.ofNat 3414, memory := s.memory, stack := v34 :: v33 :: v19 :: q2 :: q1 :: q0 :: x0 :: x1 :: x2 :: x3 :: x4 :: n1 :: n2 :: n3 :: n4 :: P :: inv :: cntp :: rest} := by
    simpa only [prCol3part8Model, v32, v33, v34] using prCol3part8_run (s) P v31 v19 q2 q1 q0 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp rest hcap hact
  have h9 : runInstructions prCol3part9Program {s with pc := UInt256.ofNat 3414, memory := s.memory, stack := v34 :: v33 :: v19 :: q2 :: q1 :: q0 :: x0 :: x1 :: x2 :: x3 :: x4 :: n1 :: n2 :: n3 :: n4 :: P :: inv :: cntp :: rest} = some {s with pc := UInt256.ofNat 3421, memory := s.memory, stack := P :: v37 :: v19 :: q2 :: q1 :: q0 :: x0 :: x1 :: x2 :: x3 :: x4 :: n1 :: n2 :: n3 :: n4 :: P :: inv :: cntp :: rest} := by
    simpa only [prCol3part9Model, v35, v36, v37] using prCol3part9_run (s) v34 v33 v19 q2 q1 q0 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp rest hcap hact
  have h10 : runInstructions prCol3part10Program {s with pc := UInt256.ofNat 3421, memory := s.memory, stack := P :: v37 :: v19 :: q2 :: q1 :: q0 :: x0 :: x1 :: x2 :: x3 :: x4 :: n1 :: n2 :: n3 :: n4 :: P :: inv :: cntp :: rest} = some {s with pc := UInt256.ofNat 3429, memory := s.memory, stack := v40 :: P :: v19 :: q2 :: q1 :: q0 :: x0 :: x1 :: x2 :: x3 :: x4 :: n1 :: n2 :: n3 :: n4 :: P :: inv :: cntp :: rest} := by
    simpa only [prCol3part10Model, v38, v39, v40] using prCol3part10_run (s) P v37 v19 q2 q1 q0 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp rest hcap hact
  have h11 : runInstructions prCol3part11Program {s with pc := UInt256.ofNat 3429, memory := s.memory, stack := v40 :: P :: v19 :: q2 :: q1 :: q0 :: x0 :: x1 :: x2 :: x3 :: x4 :: n1 :: n2 :: n3 :: n4 :: P :: inv :: cntp :: rest} = some {s with pc := UInt256.ofNat 3433, memory := s.memory, stack := v41 :: v19 :: q2 :: q1 :: q0 :: x0 :: x1 :: x2 :: x3 :: x4 :: n1 :: n2 :: n3 :: n4 :: P :: inv :: cntp :: rest} := by
    simpa only [prCol3part11Model, v41] using prCol3part11_run (s) v40 P v19 q2 q1 q0 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp rest hcap hact
  exact (runInstructions_append_some _ _ _ _ _ h0 (runInstructions_append_some _ _ _ _ _ h1 (runInstructions_append_some _ _ _ _ _ h2 (runInstructions_append_some _ _ _ _ _ h3 (runInstructions_append_some _ _ _ _ _ h4 (runInstructions_append_some _ _ _ _ _ h5 (runInstructions_append_some _ _ _ _ _ h6 (runInstructions_append_some _ _ _ _ _ h7 (runInstructions_append_some _ _ _ _ _ h8 (runInstructions_append_some _ _ _ _ _ h9 (runInstructions_append_some _ _ _ _ _ h10 h11)))))))))))

def prCol3_o0 (c q2 q1 q0 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp b0 b1 b2 b3 n0 : UInt256) : UInt256 :=
  (UInt256.mulMod (UInt256.ofNat 2048) ((UInt256.mulMod (UInt256.shiftRight (inv * ((q2 * n1) + ((q1 * n2) + ((q0 * n3) + ((x3 * b0) + ((x2 * b1) + ((x1 * b2) + ((x0 * b3) + c)))))))) (UInt256.ofNat 16)) n0 P) + ((UInt256.mulMod q2 n1 P) + ((UInt256.mulMod q1 n2 P) + ((UInt256.mulMod q0 n3 P) + ((UInt256.mulMod x3 b0 P) + ((UInt256.mulMod x2 b1 P) + ((UInt256.mulMod x1 b2 P) + ((UInt256.mulMod x0 b3 P) + c)))))))) P)

def prCol3_o1 (c q2 q1 q0 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp b0 b1 b2 b3 n0 : UInt256) : UInt256 :=
  (UInt256.shiftRight (inv * ((q2 * n1) + ((q1 * n2) + ((q0 * n3) + ((x3 * b0) + ((x2 * b1) + ((x1 * b2) + ((x0 * b3) + c)))))))) (UInt256.ofNat 16))

theorem prCol3_eq (s : State) (c q2 q1 q0 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp b0 b1 b2 b3 n0 : UInt256) (rest : List UInt256)
    (h_b0 : MachineState.readWord s.memory 0 = b0)
    (h_b1 : MachineState.readWord s.memory 32 = b1)
    (h_b2 : MachineState.readWord s.memory 64 = b2)
    (h_b3 : MachineState.readWord s.memory 96 = b3)
    (h_n0 : MachineState.readWord s.memory 160 = n0) :
    prCol3Model s c q2 q1 q0 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp rest =
      {s with pc := UInt256.ofNat 3433, stack := (prCol3_o0 c q2 q1 q0 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp b0 b1 b2 b3 n0) :: (prCol3_o1 c q2 q1 q0 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp b0 b1 b2 b3 n0) :: q2 :: q1 :: q0 :: x0 :: x1 :: x2 :: x3 :: x4 :: n1 :: n2 :: n3 :: n4 :: P :: inv :: cntp :: rest} := by
  simp only [prCol3Model, prCol3_o0, prCol3_o1, h_b0, h_b1, h_b2, h_b3, h_n0]

/-! ## prCol4: pc 3775..3901, 111 instructions -/

def prCol4part0Program : List Instr :=
  [.op .JUMPDEST,
   .op (.Dup ⟨0, by decide⟩),
   .op (.Dup ⟨15, by decide⟩),
   .push 1 128,
   .op .MLOAD,
   .op (.Dup ⟨8, by decide⟩),
   .op .MULMOD,
   .op .ADD]

def prCol4part0Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 : UInt256) (rest : List UInt256) : State :=
  let v0 : UInt256 := MachineState.readWord s.memory 128
  let v1 : UInt256 := UInt256.mulMod x5 v0 x14
  let v2 : UInt256 := v1 + x0
  {s with pc := UInt256.ofNat 3784, memory := s.memory, stack := v2 :: x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: rest}

theorem prCol4part0_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions prCol4part0Program {s with pc := UInt256.ofNat 3775, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: rest} =
      some (prCol4part0Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 rest) := by
  have hc (j : Nat) (hj : j ≤ 34) : rest.length + j < 1024 := by omega
  have hcr : rest.length < 1024 := by omega
  have ha128 : (128 : UInt256).toNat = 128 := rfl
  have hf128 := activeWords_fix s 128 32 (by decide) (by norm_num) hact
  simp [hz, hzn, prCol4part0Program, prCol4part0Model, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, ofNat_sub_ofNat, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, hc, hcr, ha128, hf128]

def prCol4part1Program : List Instr :=
  [.op (.Dup ⟨15, by decide⟩),
   .push 1 96,
   .op .MLOAD,
   .op (.Dup ⟨9, by decide⟩),
   .op .MULMOD,
   .op .ADD,
   .op (.Dup ⟨15, by decide⟩)]

def prCol4part1Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 : UInt256) (rest : List UInt256) : State :=
  let v0 : UInt256 := MachineState.readWord s.memory 96
  let v1 : UInt256 := UInt256.mulMod x7 v0 x15
  let v2 : UInt256 := v1 + x0
  {s with pc := UInt256.ofNat 3792, memory := s.memory, stack := x15 :: v2 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: rest}

theorem prCol4part1_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions prCol4part1Program {s with pc := UInt256.ofNat 3784, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: rest} =
      some (prCol4part1Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 rest) := by
  have hc (j : Nat) (hj : j ≤ 34) : rest.length + j < 1024 := by omega
  have hcr : rest.length < 1024 := by omega
  have ha96 : (96 : UInt256).toNat = 96 := rfl
  have hf96 := activeWords_fix s 96 32 (by decide) (by norm_num) hact
  simp [hz, hzn, prCol4part1Program, prCol4part1Model, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, ofNat_sub_ofNat, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, hc, hcr, ha96, hf96]

def prCol4part2Program : List Instr :=
  [.push 1 64,
   .op .MLOAD,
   .op (.Dup ⟨10, by decide⟩),
   .op .MULMOD,
   .op .ADD,
   .op (.Dup ⟨15, by decide⟩),
   .push 1 32,
   .op .MLOAD]

def prCol4part2Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 : UInt256) (rest : List UInt256) : State :=
  let v0 : UInt256 := MachineState.readWord s.memory 64
  let v1 : UInt256 := UInt256.mulMod x9 v0 x0
  let v2 : UInt256 := v1 + x1
  let v3 : UInt256 := MachineState.readWord s.memory 32
  {s with pc := UInt256.ofNat 3802, memory := s.memory, stack := v3 :: x16 :: v2 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: x18 :: rest}

theorem prCol4part2_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions prCol4part2Program {s with pc := UInt256.ofNat 3792, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: x18 :: rest} =
      some (prCol4part2Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 rest) := by
  have hc (j : Nat) (hj : j ≤ 34) : rest.length + j < 1024 := by omega
  have hcr : rest.length < 1024 := by omega
  have ha64 : (64 : UInt256).toNat = 64 := rfl
  have hf64 := activeWords_fix s 64 32 (by decide) (by norm_num) hact
  have ha32 : (32 : UInt256).toNat = 32 := rfl
  have hf32 := activeWords_fix s 32 32 (by decide) (by norm_num) hact
  simp [hz, hzn, prCol4part2Program, prCol4part2Model, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, ofNat_sub_ofNat, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, hc, hcr, ha64, hf64, ha32, hf32]

def prCol4part3Program : List Instr :=
  [.op (.Dup ⟨11, by decide⟩),
   .op .MULMOD,
   .op .ADD,
   .op (.Dup ⟨15, by decide⟩),
   .push 1 0,
   .op .MLOAD,
   .op (.Dup ⟨12, by decide⟩),
   .op .MULMOD]

def prCol4part3Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 : UInt256) (rest : List UInt256) : State :=
  let v0 : UInt256 := UInt256.mulMod x11 x0 x1
  let v1 : UInt256 := v0 + x2
  let v2 : UInt256 := MachineState.readWord s.memory 0
  let v3 : UInt256 := UInt256.mulMod x12 v2 x17
  {s with pc := UInt256.ofNat 3811, memory := s.memory, stack := v3 :: v1 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: x18 :: x19 :: rest}

theorem prCol4part3_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions prCol4part3Program {s with pc := UInt256.ofNat 3802, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: x18 :: x19 :: rest} =
      some (prCol4part3Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 rest) := by
  have hc (j : Nat) (hj : j ≤ 34) : rest.length + j < 1024 := by omega
  have hcr : rest.length < 1024 := by omega
  have ha0 : (0 : UInt256).toNat = 0 := rfl
  have hf0 := activeWords_fix s 0 32 (by decide) (by norm_num) hact
  simp [hz, hzn, prCol4part3Program, prCol4part3Model, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, ofNat_sub_ofNat, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, hc, hcr, ha0, hf0]

def prCol4part4Program : List Instr :=
  [.op .ADD,
   .op (.Dup ⟨15, by decide⟩),
   .op (.Dup ⟨15, by decide⟩),
   .op (.Dup ⟨7, by decide⟩),
   .op .MULMOD,
   .op .ADD,
   .op (.Dup ⟨15, by decide⟩),
   .op (.Dup ⟨14, by decide⟩)]

def prCol4part4Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 : UInt256) (rest : List UInt256) : State :=
  let v0 : UInt256 := x0 + x1
  let v1 : UInt256 := UInt256.mulMod x6 x15 x16
  let v2 : UInt256 := v1 + v0
  {s with pc := UInt256.ofNat 3819, memory := s.memory, stack := x14 :: x16 :: v2 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: x18 :: rest}

theorem prCol4part4_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions prCol4part4Program {s with pc := UInt256.ofNat 3811, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: x18 :: rest} =
      some (prCol4part4Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 rest) := by
  have hc (j : Nat) (hj : j ≤ 34) : rest.length + j < 1024 := by omega
  have hcr : rest.length < 1024 := by omega
  simp [hz, hzn, prCol4part4Program, prCol4part4Model, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, ofNat_sub_ofNat, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, hc, hcr]

def prCol4part5Program : List Instr :=
  [.op (.Dup ⟨6, by decide⟩),
   .op .MULMOD,
   .op .ADD,
   .op (.Dup ⟨15, by decide⟩),
   .op (.Dup ⟨13, by decide⟩),
   .op (.Dup ⟨5, by decide⟩),
   .op .MULMOD,
   .op .ADD]

def prCol4part5Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 : UInt256) (rest : List UInt256) : State :=
  let v0 : UInt256 := UInt256.mulMod x6 x0 x1
  let v1 : UInt256 := v0 + x2
  let v2 : UInt256 := UInt256.mulMod x5 x14 x17
  let v3 : UInt256 := v2 + v1
  {s with pc := UInt256.ofNat 3827, memory := s.memory, stack := v3 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: x18 :: x19 :: rest}

theorem prCol4part5_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions prCol4part5Program {s with pc := UInt256.ofNat 3819, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: x18 :: x19 :: rest} =
      some (prCol4part5Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 rest) := by
  have hc (j : Nat) (hj : j ≤ 34) : rest.length + j < 1024 := by omega
  have hcr : rest.length < 1024 := by omega
  simp [hz, hzn, prCol4part5Program, prCol4part5Model, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, ofNat_sub_ofNat, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, hc, hcr]

def prCol4part6Program : List Instr :=
  [.op (.Dup ⟨15, by decide⟩),
   .op (.Dup ⟨12, by decide⟩),
   .op (.Dup ⟨4, by decide⟩),
   .op .MULMOD,
   .op .ADD,
   .op (.Swap ⟨0, by decide⟩),
   .push 1 128,
   .op .MLOAD]

def prCol4part6Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 : UInt256) (rest : List UInt256) : State :=
  let v0 : UInt256 := UInt256.mulMod x2 x11 x15
  let v1 : UInt256 := v0 + x0
  let v2 : UInt256 := MachineState.readWord s.memory 128
  {s with pc := UInt256.ofNat 3836, memory := s.memory, stack := v2 :: x1 :: v1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: rest}

theorem prCol4part6_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions prCol4part6Program {s with pc := UInt256.ofNat 3827, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: rest} =
      some (prCol4part6Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 rest) := by
  have hc (j : Nat) (hj : j ≤ 34) : rest.length + j < 1024 := by omega
  have hcr : rest.length < 1024 := by omega
  have ha128 : (128 : UInt256).toNat = 128 := rfl
  have hf128 := activeWords_fix s 128 32 (by decide) (by norm_num) hact
  simp [hz, hzn, prCol4part6Program, prCol4part6Model, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, ofNat_sub_ofNat, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, hc, hcr, ha128, hf128]

def prCol4part7Program : List Instr :=
  [.op (.Dup ⟨7, by decide⟩),
   .op .MUL,
   .op .ADD,
   .push 1 96,
   .op .MLOAD,
   .op (.Dup ⟨8, by decide⟩),
   .op .MUL,
   .op .ADD]

def prCol4part7Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 : UInt256) (rest : List UInt256) : State :=
  let v0 : UInt256 := x7 * x0
  let v1 : UInt256 := v0 + x1
  let v2 : UInt256 := MachineState.readWord s.memory 96
  let v3 : UInt256 := x8 * v2
  let v4 : UInt256 := v3 + v1
  {s with pc := UInt256.ofNat 3845, memory := s.memory, stack := v4 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: x18 :: rest}

theorem prCol4part7_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions prCol4part7Program {s with pc := UInt256.ofNat 3836, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: x18 :: rest} =
      some (prCol4part7Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 rest) := by
  have hc (j : Nat) (hj : j ≤ 33) : rest.length + j < 1024 := by omega
  have hcr : rest.length < 1024 := by omega
  have ha96 : (96 : UInt256).toNat = 96 := rfl
  have hf96 := activeWords_fix s 96 32 (by decide) (by norm_num) hact
  simp [hz, hzn, prCol4part7Program, prCol4part7Model, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, ofNat_sub_ofNat, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, hc, hcr, ha96, hf96]

def prCol4part8Program : List Instr :=
  [.push 1 64,
   .op .MLOAD,
   .op (.Dup ⟨9, by decide⟩),
   .op .MUL,
   .op .ADD,
   .push 1 32,
   .op .MLOAD,
   .op (.Dup ⟨10, by decide⟩)]

def prCol4part8Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 : UInt256) (rest : List UInt256) : State :=
  let v0 : UInt256 := MachineState.readWord s.memory 64
  let v1 : UInt256 := x8 * v0
  let v2 : UInt256 := v1 + x0
  let v3 : UInt256 := MachineState.readWord s.memory 32
  {s with pc := UInt256.ofNat 3855, memory := s.memory, stack := x9 :: v3 :: v2 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: rest}

theorem prCol4part8_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions prCol4part8Program {s with pc := UInt256.ofNat 3845, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: rest} =
      some (prCol4part8Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 rest) := by
  have hc (j : Nat) (hj : j ≤ 33) : rest.length + j < 1024 := by omega
  have hcr : rest.length < 1024 := by omega
  have ha64 : (64 : UInt256).toNat = 64 := rfl
  have hf64 := activeWords_fix s 64 32 (by decide) (by norm_num) hact
  have ha32 : (32 : UInt256).toNat = 32 := rfl
  have hf32 := activeWords_fix s 32 32 (by decide) (by norm_num) hact
  simp [hz, hzn, prCol4part8Program, prCol4part8Model, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, ofNat_sub_ofNat, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, hc, hcr, ha64, hf64, ha32, hf32]

def prCol4part9Program : List Instr :=
  [.op .MUL,
   .op .ADD,
   .push 1 0,
   .op .MLOAD,
   .op (.Dup ⟨11, by decide⟩),
   .op .MUL,
   .op .ADD,
   .op (.Dup ⟨14, by decide⟩)]

def prCol4part9Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 : UInt256) (rest : List UInt256) : State :=
  let v0 : UInt256 := x0 * x1
  let v1 : UInt256 := v0 + x2
  let v2 : UInt256 := MachineState.readWord s.memory 0
  let v3 : UInt256 := x12 * v2
  let v4 : UInt256 := v3 + v1
  {s with pc := UInt256.ofNat 3864, memory := s.memory, stack := x16 :: v4 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: x18 :: x19 :: rest}

theorem prCol4part9_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions prCol4part9Program {s with pc := UInt256.ofNat 3855, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: x18 :: x19 :: rest} =
      some (prCol4part9Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 rest) := by
  have hc (j : Nat) (hj : j ≤ 33) : rest.length + j < 1024 := by omega
  have hcr : rest.length < 1024 := by omega
  have ha0 : (0 : UInt256).toNat = 0 := rfl
  have hf0 := activeWords_fix s 0 32 (by decide) (by norm_num) hact
  simp [hz, hzn, prCol4part9Program, prCol4part9Model, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, ofNat_sub_ofNat, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, hc, hcr, ha0, hf0]

def prCol4part10Program : List Instr :=
  [.op (.Dup ⟨6, by decide⟩),
   .op .MUL,
   .op .ADD,
   .op (.Dup ⟨13, by decide⟩),
   .op (.Dup ⟨5, by decide⟩),
   .op .MUL,
   .op .ADD,
   .op (.Dup ⟨12, by decide⟩)]

def prCol4part10Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 : UInt256) (rest : List UInt256) : State :=
  let v0 : UInt256 := x6 * x0
  let v1 : UInt256 := v0 + x1
  let v2 : UInt256 := x5 * x14
  let v3 : UInt256 := v2 + v1
  {s with pc := UInt256.ofNat 3872, memory := s.memory, stack := x13 :: v3 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: x18 :: rest}

theorem prCol4part10_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions prCol4part10Program {s with pc := UInt256.ofNat 3864, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: x18 :: rest} =
      some (prCol4part10Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 rest) := by
  have hc (j : Nat) (hj : j ≤ 33) : rest.length + j < 1024 := by omega
  have hcr : rest.length < 1024 := by omega
  simp [hz, hzn, prCol4part10Program, prCol4part10Model, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, ofNat_sub_ofNat, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, hc, hcr]

def prCol4part11Program : List Instr :=
  [.op (.Dup ⟨4, by decide⟩),
   .op .MUL,
   .op .ADD,
   .op (.Dup ⟨11, by decide⟩),
   .op (.Dup ⟨3, by decide⟩),
   .op .MUL,
   .op .ADD]

def prCol4part11Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 : UInt256) (rest : List UInt256) : State :=
  let v0 : UInt256 := x4 * x0
  let v1 : UInt256 := v0 + x1
  let v2 : UInt256 := x3 * x12
  let v3 : UInt256 := v2 + v1
  {s with pc := UInt256.ofNat 3879, memory := s.memory, stack := v3 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: x18 :: rest}

theorem prCol4part11_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions prCol4part11Program {s with pc := UInt256.ofNat 3872, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: x18 :: rest} =
      some (prCol4part11Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 rest) := by
  have hc (j : Nat) (hj : j ≤ 33) : rest.length + j < 1024 := by omega
  have hcr : rest.length < 1024 := by omega
  simp [hz, hzn, prCol4part11Program, prCol4part11Model, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, ofNat_sub_ofNat, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, hc, hcr]

def prCol4part12Program : List Instr :=
  [.push 1 192,
   .op .MLOAD,
   .op .MUL,
   .push 1 16,
   .op .SHR,
   .op (.Swap ⟨4, by decide⟩),
   .op .POP,
   .op (.Dup ⟨14, by decide⟩)]

def prCol4part12Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 : UInt256) (rest : List UInt256) : State :=
  let v0 : UInt256 := MachineState.readWord s.memory 192
  let v1 : UInt256 := v0 * x0
  let v2 : UInt256 := UInt256.shiftRight v1 (UInt256.ofNat 16)
  {s with pc := UInt256.ofNat 3889, memory := s.memory, stack := x15 :: x1 :: x2 :: x3 :: x4 :: v2 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: rest}

theorem prCol4part12_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions prCol4part12Program {s with pc := UInt256.ofNat 3879, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: rest} =
      some (prCol4part12Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 rest) := by
  have hc (j : Nat) (hj : j ≤ 32) : rest.length + j < 1024 := by omega
  have hcr : rest.length < 1024 := by omega
  have ha192 : (192 : UInt256).toNat = 192 := rfl
  have hf192 := activeWords_fix s 192 32 (by decide) (by norm_num) hact
  simp [hz, hzn, prCol4part12Program, prCol4part12Model, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, ofNat_sub_ofNat, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, hc, hcr, ha192, hf192]

def prCol4part13Program : List Instr :=
  [.push 1 160,
   .op .MLOAD,
   .op (.Dup ⟨6, by decide⟩),
   .op .MULMOD,
   .op .ADD,
   .op (.Dup ⟨14, by decide⟩),
   .op (.Swap ⟨0, by decide⟩)]

def prCol4part13Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 : UInt256) (rest : List UInt256) : State :=
  let v0 : UInt256 := MachineState.readWord s.memory 160
  let v1 : UInt256 := UInt256.mulMod x5 v0 x0
  let v2 : UInt256 := v1 + x1
  {s with pc := UInt256.ofNat 3897, memory := s.memory, stack := v2 :: x15 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: rest}

theorem prCol4part13_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions prCol4part13Program {s with pc := UInt256.ofNat 3889, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: rest} =
      some (prCol4part13Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 rest) := by
  have hc (j : Nat) (hj : j ≤ 33) : rest.length + j < 1024 := by omega
  have hcr : rest.length < 1024 := by omega
  have ha160 : (160 : UInt256).toNat = 160 := rfl
  have hf160 := activeWords_fix s 160 32 (by decide) (by norm_num) hact
  simp [hz, hzn, prCol4part13Program, prCol4part13Model, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, ofNat_sub_ofNat, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, hc, hcr, ha160, hf160]

def prCol4part14Program : List Instr :=
  [.push 2 2048,
   .op .MULMOD]

def prCol4part14Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 : UInt256) (rest : List UInt256) : State :=
  let v0 : UInt256 := UInt256.mulMod (UInt256.ofNat 2048) x0 x1
  {s with pc := UInt256.ofNat 3901, memory := s.memory, stack := v0 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: rest}

theorem prCol4part14_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions prCol4part14Program {s with pc := UInt256.ofNat 3897, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: rest} =
      some (prCol4part14Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 rest) := by
  have hc (j : Nat) (hj : j ≤ 32) : rest.length + j < 1024 := by omega
  have hcr : rest.length < 1024 := by omega
  simp [hz, hzn, prCol4part14Program, prCol4part14Model, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, ofNat_sub_ofNat, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, hc, hcr]

def prCol4Program : List Instr :=
  [.op .JUMPDEST,
   .op (.Dup ⟨0, by decide⟩),
   .op (.Dup ⟨15, by decide⟩),
   .push 1 128,
   .op .MLOAD,
   .op (.Dup ⟨8, by decide⟩),
   .op .MULMOD,
   .op .ADD,
   .op (.Dup ⟨15, by decide⟩),
   .push 1 96,
   .op .MLOAD,
   .op (.Dup ⟨9, by decide⟩),
   .op .MULMOD,
   .op .ADD,
   .op (.Dup ⟨15, by decide⟩),
   .push 1 64,
   .op .MLOAD,
   .op (.Dup ⟨10, by decide⟩),
   .op .MULMOD,
   .op .ADD,
   .op (.Dup ⟨15, by decide⟩),
   .push 1 32,
   .op .MLOAD,
   .op (.Dup ⟨11, by decide⟩),
   .op .MULMOD,
   .op .ADD,
   .op (.Dup ⟨15, by decide⟩),
   .push 1 0,
   .op .MLOAD,
   .op (.Dup ⟨12, by decide⟩),
   .op .MULMOD,
   .op .ADD,
   .op (.Dup ⟨15, by decide⟩),
   .op (.Dup ⟨15, by decide⟩),
   .op (.Dup ⟨7, by decide⟩),
   .op .MULMOD,
   .op .ADD,
   .op (.Dup ⟨15, by decide⟩),
   .op (.Dup ⟨14, by decide⟩),
   .op (.Dup ⟨6, by decide⟩),
   .op .MULMOD,
   .op .ADD,
   .op (.Dup ⟨15, by decide⟩),
   .op (.Dup ⟨13, by decide⟩),
   .op (.Dup ⟨5, by decide⟩),
   .op .MULMOD,
   .op .ADD,
   .op (.Dup ⟨15, by decide⟩),
   .op (.Dup ⟨12, by decide⟩),
   .op (.Dup ⟨4, by decide⟩),
   .op .MULMOD,
   .op .ADD,
   .op (.Swap ⟨0, by decide⟩),
   .push 1 128,
   .op .MLOAD,
   .op (.Dup ⟨7, by decide⟩),
   .op .MUL,
   .op .ADD,
   .push 1 96,
   .op .MLOAD,
   .op (.Dup ⟨8, by decide⟩),
   .op .MUL,
   .op .ADD,
   .push 1 64,
   .op .MLOAD,
   .op (.Dup ⟨9, by decide⟩),
   .op .MUL,
   .op .ADD,
   .push 1 32,
   .op .MLOAD,
   .op (.Dup ⟨10, by decide⟩),
   .op .MUL,
   .op .ADD,
   .push 1 0,
   .op .MLOAD,
   .op (.Dup ⟨11, by decide⟩),
   .op .MUL,
   .op .ADD,
   .op (.Dup ⟨14, by decide⟩),
   .op (.Dup ⟨6, by decide⟩),
   .op .MUL,
   .op .ADD,
   .op (.Dup ⟨13, by decide⟩),
   .op (.Dup ⟨5, by decide⟩),
   .op .MUL,
   .op .ADD,
   .op (.Dup ⟨12, by decide⟩),
   .op (.Dup ⟨4, by decide⟩),
   .op .MUL,
   .op .ADD,
   .op (.Dup ⟨11, by decide⟩),
   .op (.Dup ⟨3, by decide⟩),
   .op .MUL,
   .op .ADD,
   .push 1 192,
   .op .MLOAD,
   .op .MUL,
   .push 1 16,
   .op .SHR,
   .op (.Swap ⟨4, by decide⟩),
   .op .POP,
   .op (.Dup ⟨14, by decide⟩),
   .push 1 160,
   .op .MLOAD,
   .op (.Dup ⟨6, by decide⟩),
   .op .MULMOD,
   .op .ADD,
   .op (.Dup ⟨14, by decide⟩),
   .op (.Swap ⟨0, by decide⟩),
   .push 2 2048,
   .op .MULMOD]

def prCol4Model (s : State) (c q3 q2 q1 q0 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp : UInt256) (rest : List UInt256) : State :=
  let v0 : UInt256 := MachineState.readWord s.memory 128
  let v1 : UInt256 := UInt256.mulMod x0 v0 P
  let v2 : UInt256 := v1 + c
  let v3 : UInt256 := MachineState.readWord s.memory 96
  let v4 : UInt256 := UInt256.mulMod x1 v3 P
  let v5 : UInt256 := v4 + v2
  let v6 : UInt256 := MachineState.readWord s.memory 64
  let v7 : UInt256 := UInt256.mulMod x2 v6 P
  let v8 : UInt256 := v7 + v5
  let v9 : UInt256 := MachineState.readWord s.memory 32
  let v10 : UInt256 := UInt256.mulMod x3 v9 P
  let v11 : UInt256 := v10 + v8
  let v12 : UInt256 := MachineState.readWord s.memory 0
  let v13 : UInt256 := UInt256.mulMod x4 v12 P
  let v14 : UInt256 := v13 + v11
  let v15 : UInt256 := UInt256.mulMod q0 n4 P
  let v16 : UInt256 := v15 + v14
  let v17 : UInt256 := UInt256.mulMod q1 n3 P
  let v18 : UInt256 := v17 + v16
  let v19 : UInt256 := UInt256.mulMod q2 n2 P
  let v20 : UInt256 := v19 + v18
  let v21 : UInt256 := UInt256.mulMod q3 n1 P
  let v22 : UInt256 := v21 + v20
  let v23 : UInt256 := MachineState.readWord s.memory 128
  let v24 : UInt256 := x0 * v23
  let v25 : UInt256 := v24 + c
  let v26 : UInt256 := MachineState.readWord s.memory 96
  let v27 : UInt256 := x1 * v26
  let v28 : UInt256 := v27 + v25
  let v29 : UInt256 := MachineState.readWord s.memory 64
  let v30 : UInt256 := x2 * v29
  let v31 : UInt256 := v30 + v28
  let v32 : UInt256 := MachineState.readWord s.memory 32
  let v33 : UInt256 := x3 * v32
  let v34 : UInt256 := v33 + v31
  let v35 : UInt256 := MachineState.readWord s.memory 0
  let v36 : UInt256 := x4 * v35
  let v37 : UInt256 := v36 + v34
  let v38 : UInt256 := q0 * n4
  let v39 : UInt256 := v38 + v37
  let v40 : UInt256 := q1 * n3
  let v41 : UInt256 := v40 + v39
  let v42 : UInt256 := q2 * n2
  let v43 : UInt256 := v42 + v41
  let v44 : UInt256 := q3 * n1
  let v45 : UInt256 := v44 + v43
  let v46 : UInt256 := MachineState.readWord s.memory 192
  let v47 : UInt256 := v46 * v45
  let v48 : UInt256 := UInt256.shiftRight v47 (UInt256.ofNat 16)
  let v49 : UInt256 := MachineState.readWord s.memory 160
  let v50 : UInt256 := UInt256.mulMod v48 v49 P
  let v51 : UInt256 := v50 + v22
  let v52 : UInt256 := UInt256.mulMod (UInt256.ofNat 2048) v51 P
  {s with pc := UInt256.ofNat 3901, memory := s.memory, stack := v52 :: q3 :: q2 :: q1 :: v48 :: x0 :: x1 :: x2 :: x3 :: x4 :: n1 :: n2 :: n3 :: n4 :: P :: inv :: cntp :: rest}

theorem prCol4_run (s : State) (c q3 q2 q1 q0 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions prCol4Program {s with pc := UInt256.ofNat 3775, stack := c :: q3 :: q2 :: q1 :: q0 :: x0 :: x1 :: x2 :: x3 :: x4 :: n1 :: n2 :: n3 :: n4 :: P :: inv :: cntp :: rest} =
      some (prCol4Model s c q3 q2 q1 q0 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp rest) := by
  let v0 : UInt256 := MachineState.readWord s.memory 128
  let v1 : UInt256 := UInt256.mulMod x0 v0 P
  let v2 : UInt256 := v1 + c
  let v3 : UInt256 := MachineState.readWord s.memory 96
  let v4 : UInt256 := UInt256.mulMod x1 v3 P
  let v5 : UInt256 := v4 + v2
  let v6 : UInt256 := MachineState.readWord s.memory 64
  let v7 : UInt256 := UInt256.mulMod x2 v6 P
  let v8 : UInt256 := v7 + v5
  let v9 : UInt256 := MachineState.readWord s.memory 32
  let v10 : UInt256 := UInt256.mulMod x3 v9 P
  let v11 : UInt256 := v10 + v8
  let v12 : UInt256 := MachineState.readWord s.memory 0
  let v13 : UInt256 := UInt256.mulMod x4 v12 P
  let v14 : UInt256 := v13 + v11
  let v15 : UInt256 := UInt256.mulMod q0 n4 P
  let v16 : UInt256 := v15 + v14
  let v17 : UInt256 := UInt256.mulMod q1 n3 P
  let v18 : UInt256 := v17 + v16
  let v19 : UInt256 := UInt256.mulMod q2 n2 P
  let v20 : UInt256 := v19 + v18
  let v21 : UInt256 := UInt256.mulMod q3 n1 P
  let v22 : UInt256 := v21 + v20
  let v23 : UInt256 := MachineState.readWord s.memory 128
  let v24 : UInt256 := x0 * v23
  let v25 : UInt256 := v24 + c
  let v26 : UInt256 := MachineState.readWord s.memory 96
  let v27 : UInt256 := x1 * v26
  let v28 : UInt256 := v27 + v25
  let v29 : UInt256 := MachineState.readWord s.memory 64
  let v30 : UInt256 := x2 * v29
  let v31 : UInt256 := v30 + v28
  let v32 : UInt256 := MachineState.readWord s.memory 32
  let v33 : UInt256 := x3 * v32
  let v34 : UInt256 := v33 + v31
  let v35 : UInt256 := MachineState.readWord s.memory 0
  let v36 : UInt256 := x4 * v35
  let v37 : UInt256 := v36 + v34
  let v38 : UInt256 := q0 * n4
  let v39 : UInt256 := v38 + v37
  let v40 : UInt256 := q1 * n3
  let v41 : UInt256 := v40 + v39
  let v42 : UInt256 := q2 * n2
  let v43 : UInt256 := v42 + v41
  let v44 : UInt256 := q3 * n1
  let v45 : UInt256 := v44 + v43
  let v46 : UInt256 := MachineState.readWord s.memory 192
  let v47 : UInt256 := v46 * v45
  let v48 : UInt256 := UInt256.shiftRight v47 (UInt256.ofNat 16)
  let v49 : UInt256 := MachineState.readWord s.memory 160
  let v50 : UInt256 := UInt256.mulMod v48 v49 P
  let v51 : UInt256 := v50 + v22
  let v52 : UInt256 := UInt256.mulMod (UInt256.ofNat 2048) v51 P
  have h0 : runInstructions prCol4part0Program {s with pc := UInt256.ofNat 3775, memory := s.memory, stack := c :: q3 :: q2 :: q1 :: q0 :: x0 :: x1 :: x2 :: x3 :: x4 :: n1 :: n2 :: n3 :: n4 :: P :: inv :: cntp :: rest} = some {s with pc := UInt256.ofNat 3784, memory := s.memory, stack := v2 :: c :: q3 :: q2 :: q1 :: q0 :: x0 :: x1 :: x2 :: x3 :: x4 :: n1 :: n2 :: n3 :: n4 :: P :: inv :: cntp :: rest} := by
    simpa only [prCol4part0Model, v0, v1, v2] using prCol4part0_run (s) c q3 q2 q1 q0 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp rest hcap hact
  have h1 : runInstructions prCol4part1Program {s with pc := UInt256.ofNat 3784, memory := s.memory, stack := v2 :: c :: q3 :: q2 :: q1 :: q0 :: x0 :: x1 :: x2 :: x3 :: x4 :: n1 :: n2 :: n3 :: n4 :: P :: inv :: cntp :: rest} = some {s with pc := UInt256.ofNat 3792, memory := s.memory, stack := P :: v5 :: c :: q3 :: q2 :: q1 :: q0 :: x0 :: x1 :: x2 :: x3 :: x4 :: n1 :: n2 :: n3 :: n4 :: P :: inv :: cntp :: rest} := by
    simpa only [prCol4part1Model, v3, v4, v5] using prCol4part1_run (s) v2 c q3 q2 q1 q0 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp rest hcap hact
  have h2 : runInstructions prCol4part2Program {s with pc := UInt256.ofNat 3792, memory := s.memory, stack := P :: v5 :: c :: q3 :: q2 :: q1 :: q0 :: x0 :: x1 :: x2 :: x3 :: x4 :: n1 :: n2 :: n3 :: n4 :: P :: inv :: cntp :: rest} = some {s with pc := UInt256.ofNat 3802, memory := s.memory, stack := v9 :: P :: v8 :: c :: q3 :: q2 :: q1 :: q0 :: x0 :: x1 :: x2 :: x3 :: x4 :: n1 :: n2 :: n3 :: n4 :: P :: inv :: cntp :: rest} := by
    simpa only [prCol4part2Model, v6, v7, v8, v9] using prCol4part2_run (s) P v5 c q3 q2 q1 q0 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp rest hcap hact
  have h3 : runInstructions prCol4part3Program {s with pc := UInt256.ofNat 3802, memory := s.memory, stack := v9 :: P :: v8 :: c :: q3 :: q2 :: q1 :: q0 :: x0 :: x1 :: x2 :: x3 :: x4 :: n1 :: n2 :: n3 :: n4 :: P :: inv :: cntp :: rest} = some {s with pc := UInt256.ofNat 3811, memory := s.memory, stack := v13 :: v11 :: c :: q3 :: q2 :: q1 :: q0 :: x0 :: x1 :: x2 :: x3 :: x4 :: n1 :: n2 :: n3 :: n4 :: P :: inv :: cntp :: rest} := by
    simpa only [prCol4part3Model, v10, v11, v12, v13] using prCol4part3_run (s) v9 P v8 c q3 q2 q1 q0 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp rest hcap hact
  have h4 : runInstructions prCol4part4Program {s with pc := UInt256.ofNat 3811, memory := s.memory, stack := v13 :: v11 :: c :: q3 :: q2 :: q1 :: q0 :: x0 :: x1 :: x2 :: x3 :: x4 :: n1 :: n2 :: n3 :: n4 :: P :: inv :: cntp :: rest} = some {s with pc := UInt256.ofNat 3819, memory := s.memory, stack := n3 :: P :: v16 :: c :: q3 :: q2 :: q1 :: q0 :: x0 :: x1 :: x2 :: x3 :: x4 :: n1 :: n2 :: n3 :: n4 :: P :: inv :: cntp :: rest} := by
    simpa only [prCol4part4Model, v14, v15, v16] using prCol4part4_run (s) v13 v11 c q3 q2 q1 q0 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp rest hcap hact
  have h5 : runInstructions prCol4part5Program {s with pc := UInt256.ofNat 3819, memory := s.memory, stack := n3 :: P :: v16 :: c :: q3 :: q2 :: q1 :: q0 :: x0 :: x1 :: x2 :: x3 :: x4 :: n1 :: n2 :: n3 :: n4 :: P :: inv :: cntp :: rest} = some {s with pc := UInt256.ofNat 3827, memory := s.memory, stack := v20 :: c :: q3 :: q2 :: q1 :: q0 :: x0 :: x1 :: x2 :: x3 :: x4 :: n1 :: n2 :: n3 :: n4 :: P :: inv :: cntp :: rest} := by
    simpa only [prCol4part5Model, v17, v18, v19, v20] using prCol4part5_run (s) n3 P v16 c q3 q2 q1 q0 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp rest hcap hact
  have h6 : runInstructions prCol4part6Program {s with pc := UInt256.ofNat 3827, memory := s.memory, stack := v20 :: c :: q3 :: q2 :: q1 :: q0 :: x0 :: x1 :: x2 :: x3 :: x4 :: n1 :: n2 :: n3 :: n4 :: P :: inv :: cntp :: rest} = some {s with pc := UInt256.ofNat 3836, memory := s.memory, stack := v23 :: c :: v22 :: q3 :: q2 :: q1 :: q0 :: x0 :: x1 :: x2 :: x3 :: x4 :: n1 :: n2 :: n3 :: n4 :: P :: inv :: cntp :: rest} := by
    simpa only [prCol4part6Model, v21, v22, v23] using prCol4part6_run (s) v20 c q3 q2 q1 q0 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp rest hcap hact
  have h7 : runInstructions prCol4part7Program {s with pc := UInt256.ofNat 3836, memory := s.memory, stack := v23 :: c :: v22 :: q3 :: q2 :: q1 :: q0 :: x0 :: x1 :: x2 :: x3 :: x4 :: n1 :: n2 :: n3 :: n4 :: P :: inv :: cntp :: rest} = some {s with pc := UInt256.ofNat 3845, memory := s.memory, stack := v28 :: v22 :: q3 :: q2 :: q1 :: q0 :: x0 :: x1 :: x2 :: x3 :: x4 :: n1 :: n2 :: n3 :: n4 :: P :: inv :: cntp :: rest} := by
    simpa only [prCol4part7Model, v24, v25, v26, v27, v28] using prCol4part7_run (s) v23 c v22 q3 q2 q1 q0 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp rest hcap hact
  have h8 : runInstructions prCol4part8Program {s with pc := UInt256.ofNat 3845, memory := s.memory, stack := v28 :: v22 :: q3 :: q2 :: q1 :: q0 :: x0 :: x1 :: x2 :: x3 :: x4 :: n1 :: n2 :: n3 :: n4 :: P :: inv :: cntp :: rest} = some {s with pc := UInt256.ofNat 3855, memory := s.memory, stack := x3 :: v32 :: v31 :: v22 :: q3 :: q2 :: q1 :: q0 :: x0 :: x1 :: x2 :: x3 :: x4 :: n1 :: n2 :: n3 :: n4 :: P :: inv :: cntp :: rest} := by
    simpa only [prCol4part8Model, v29, v30, v31, v32] using prCol4part8_run (s) v28 v22 q3 q2 q1 q0 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp rest hcap hact
  have h9 : runInstructions prCol4part9Program {s with pc := UInt256.ofNat 3855, memory := s.memory, stack := x3 :: v32 :: v31 :: v22 :: q3 :: q2 :: q1 :: q0 :: x0 :: x1 :: x2 :: x3 :: x4 :: n1 :: n2 :: n3 :: n4 :: P :: inv :: cntp :: rest} = some {s with pc := UInt256.ofNat 3864, memory := s.memory, stack := n4 :: v37 :: v22 :: q3 :: q2 :: q1 :: q0 :: x0 :: x1 :: x2 :: x3 :: x4 :: n1 :: n2 :: n3 :: n4 :: P :: inv :: cntp :: rest} := by
    simpa only [prCol4part9Model, v33, v34, v35, v36, v37] using prCol4part9_run (s) x3 v32 v31 v22 q3 q2 q1 q0 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp rest hcap hact
  have h10 : runInstructions prCol4part10Program {s with pc := UInt256.ofNat 3864, memory := s.memory, stack := n4 :: v37 :: v22 :: q3 :: q2 :: q1 :: q0 :: x0 :: x1 :: x2 :: x3 :: x4 :: n1 :: n2 :: n3 :: n4 :: P :: inv :: cntp :: rest} = some {s with pc := UInt256.ofNat 3872, memory := s.memory, stack := n2 :: v41 :: v22 :: q3 :: q2 :: q1 :: q0 :: x0 :: x1 :: x2 :: x3 :: x4 :: n1 :: n2 :: n3 :: n4 :: P :: inv :: cntp :: rest} := by
    simpa only [prCol4part10Model, v38, v39, v40, v41] using prCol4part10_run (s) n4 v37 v22 q3 q2 q1 q0 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp rest hcap hact
  have h11 : runInstructions prCol4part11Program {s with pc := UInt256.ofNat 3872, memory := s.memory, stack := n2 :: v41 :: v22 :: q3 :: q2 :: q1 :: q0 :: x0 :: x1 :: x2 :: x3 :: x4 :: n1 :: n2 :: n3 :: n4 :: P :: inv :: cntp :: rest} = some {s with pc := UInt256.ofNat 3879, memory := s.memory, stack := v45 :: v22 :: q3 :: q2 :: q1 :: q0 :: x0 :: x1 :: x2 :: x3 :: x4 :: n1 :: n2 :: n3 :: n4 :: P :: inv :: cntp :: rest} := by
    simpa only [prCol4part11Model, v42, v43, v44, v45] using prCol4part11_run (s) n2 v41 v22 q3 q2 q1 q0 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp rest hcap hact
  have h12 : runInstructions prCol4part12Program {s with pc := UInt256.ofNat 3879, memory := s.memory, stack := v45 :: v22 :: q3 :: q2 :: q1 :: q0 :: x0 :: x1 :: x2 :: x3 :: x4 :: n1 :: n2 :: n3 :: n4 :: P :: inv :: cntp :: rest} = some {s with pc := UInt256.ofNat 3889, memory := s.memory, stack := P :: v22 :: q3 :: q2 :: q1 :: v48 :: x0 :: x1 :: x2 :: x3 :: x4 :: n1 :: n2 :: n3 :: n4 :: P :: inv :: cntp :: rest} := by
    simpa only [prCol4part12Model, v46, v47, v48] using prCol4part12_run (s) v45 v22 q3 q2 q1 q0 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp rest hcap hact
  have h13 : runInstructions prCol4part13Program {s with pc := UInt256.ofNat 3889, memory := s.memory, stack := P :: v22 :: q3 :: q2 :: q1 :: v48 :: x0 :: x1 :: x2 :: x3 :: x4 :: n1 :: n2 :: n3 :: n4 :: P :: inv :: cntp :: rest} = some {s with pc := UInt256.ofNat 3897, memory := s.memory, stack := v51 :: P :: q3 :: q2 :: q1 :: v48 :: x0 :: x1 :: x2 :: x3 :: x4 :: n1 :: n2 :: n3 :: n4 :: P :: inv :: cntp :: rest} := by
    simpa only [prCol4part13Model, v49, v50, v51] using prCol4part13_run (s) P v22 q3 q2 q1 v48 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp rest hcap hact
  have h14 : runInstructions prCol4part14Program {s with pc := UInt256.ofNat 3897, memory := s.memory, stack := v51 :: P :: q3 :: q2 :: q1 :: v48 :: x0 :: x1 :: x2 :: x3 :: x4 :: n1 :: n2 :: n3 :: n4 :: P :: inv :: cntp :: rest} = some {s with pc := UInt256.ofNat 3901, memory := s.memory, stack := v52 :: q3 :: q2 :: q1 :: v48 :: x0 :: x1 :: x2 :: x3 :: x4 :: n1 :: n2 :: n3 :: n4 :: P :: inv :: cntp :: rest} := by
    simpa only [prCol4part14Model, v52] using prCol4part14_run (s) v51 P q3 q2 q1 v48 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp rest hcap hact
  exact (runInstructions_append_some _ _ _ _ _ h0 (runInstructions_append_some _ _ _ _ _ h1 (runInstructions_append_some _ _ _ _ _ h2 (runInstructions_append_some _ _ _ _ _ h3 (runInstructions_append_some _ _ _ _ _ h4 (runInstructions_append_some _ _ _ _ _ h5 (runInstructions_append_some _ _ _ _ _ h6 (runInstructions_append_some _ _ _ _ _ h7 (runInstructions_append_some _ _ _ _ _ h8 (runInstructions_append_some _ _ _ _ _ h9 (runInstructions_append_some _ _ _ _ _ h10 (runInstructions_append_some _ _ _ _ _ h11 (runInstructions_append_some _ _ _ _ _ h12 (runInstructions_append_some _ _ _ _ _ h13 h14))))))))))))))

def prCol4_o0 (c q3 q2 q1 q0 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp b0 b1 b2 b3 b4 n0 : UInt256) : UInt256 :=
  (UInt256.mulMod (UInt256.ofNat 2048) ((UInt256.mulMod (UInt256.shiftRight (inv * ((q3 * n1) + ((q2 * n2) + ((q1 * n3) + ((q0 * n4) + ((x4 * b0) + ((x3 * b1) + ((x2 * b2) + ((x1 * b3) + ((x0 * b4) + c)))))))))) (UInt256.ofNat 16)) n0 P) + ((UInt256.mulMod q3 n1 P) + ((UInt256.mulMod q2 n2 P) + ((UInt256.mulMod q1 n3 P) + ((UInt256.mulMod q0 n4 P) + ((UInt256.mulMod x4 b0 P) + ((UInt256.mulMod x3 b1 P) + ((UInt256.mulMod x2 b2 P) + ((UInt256.mulMod x1 b3 P) + ((UInt256.mulMod x0 b4 P) + c)))))))))) P)

def prCol4_o4 (c q3 q2 q1 q0 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp b0 b1 b2 b3 b4 n0 : UInt256) : UInt256 :=
  (UInt256.shiftRight (inv * ((q3 * n1) + ((q2 * n2) + ((q1 * n3) + ((q0 * n4) + ((x4 * b0) + ((x3 * b1) + ((x2 * b2) + ((x1 * b3) + ((x0 * b4) + c)))))))))) (UInt256.ofNat 16))

theorem prCol4_eq (s : State) (c q3 q2 q1 q0 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp b0 b1 b2 b3 b4 n0 : UInt256) (rest : List UInt256)
    (h_b0 : MachineState.readWord s.memory 0 = b0)
    (h_b1 : MachineState.readWord s.memory 32 = b1)
    (h_b2 : MachineState.readWord s.memory 64 = b2)
    (h_b3 : MachineState.readWord s.memory 96 = b3)
    (h_b4 : MachineState.readWord s.memory 128 = b4)
    (h_n0 : MachineState.readWord s.memory 160 = n0)
    (h_inv : MachineState.readWord s.memory 192 = inv) :
    prCol4Model s c q3 q2 q1 q0 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp rest =
      {s with pc := UInt256.ofNat 3901, stack := (prCol4_o0 c q3 q2 q1 q0 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp b0 b1 b2 b3 b4 n0) :: q3 :: q2 :: q1 :: (prCol4_o4 c q3 q2 q1 q0 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp b0 b1 b2 b3 b4 n0) :: x0 :: x1 :: x2 :: x3 :: x4 :: n1 :: n2 :: n3 :: n4 :: P :: inv :: cntp :: rest} := by
  simp only [prCol4Model, prCol4_o0, prCol4_o4, h_b0, h_b1, h_b2, h_b3, h_b4, h_n0, h_inv]

/-! ## prCol5: pc 4857..4971, 102 instructions -/

def prCol5part0Program : List Instr :=
  [.op .JUMPDEST,
   .op (.Dup ⟨0, by decide⟩),
   .push 1 128,
   .op .MLOAD,
   .op (.Dup ⟨8, by decide⟩),
   .op .MUL,
   .op .ADD]

def prCol5part0Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 : UInt256) (rest : List UInt256) : State :=
  let v0 : UInt256 := MachineState.readWord s.memory 128
  let v1 : UInt256 := x6 * v0
  let v2 : UInt256 := v1 + x0
  {s with pc := UInt256.ofNat 4865, memory := s.memory, stack := v2 :: x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: rest}

theorem prCol5part0_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions prCol5part0Program {s with pc := UInt256.ofNat 4857, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: rest} =
      some (prCol5part0Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 rest) := by
  have hc (j : Nat) (hj : j ≤ 33) : rest.length + j < 1024 := by omega
  have hcr : rest.length < 1024 := by omega
  have ha128 : (128 : UInt256).toNat = 128 := rfl
  have hf128 := activeWords_fix s 128 32 (by decide) (by norm_num) hact
  simp [hz, hzn, prCol5part0Program, prCol5part0Model, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, ofNat_sub_ofNat, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, hc, hcr, ha128, hf128]

def prCol5part1Program : List Instr :=
  [.push 1 96,
   .op .MLOAD,
   .op (.Dup ⟨9, by decide⟩),
   .op .MUL,
   .op .ADD,
   .push 1 64,
   .op .MLOAD,
   .op (.Dup ⟨10, by decide⟩)]

def prCol5part1Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 : UInt256) (rest : List UInt256) : State :=
  let v0 : UInt256 := MachineState.readWord s.memory 96
  let v1 : UInt256 := x8 * v0
  let v2 : UInt256 := v1 + x0
  let v3 : UInt256 := MachineState.readWord s.memory 64
  {s with pc := UInt256.ofNat 4875, memory := s.memory, stack := x9 :: v3 :: v2 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: rest}

theorem prCol5part1_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions prCol5part1Program {s with pc := UInt256.ofNat 4865, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: rest} =
      some (prCol5part1Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 rest) := by
  have hc (j : Nat) (hj : j ≤ 33) : rest.length + j < 1024 := by omega
  have hcr : rest.length < 1024 := by omega
  have ha96 : (96 : UInt256).toNat = 96 := rfl
  have hf96 := activeWords_fix s 96 32 (by decide) (by norm_num) hact
  have ha64 : (64 : UInt256).toNat = 64 := rfl
  have hf64 := activeWords_fix s 64 32 (by decide) (by norm_num) hact
  simp [hz, hzn, prCol5part1Program, prCol5part1Model, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, ofNat_sub_ofNat, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, hc, hcr, ha96, hf96, ha64, hf64]

def prCol5part2Program : List Instr :=
  [.op .MUL,
   .op .ADD,
   .push 1 32,
   .op .MLOAD,
   .op (.Dup ⟨11, by decide⟩),
   .op .MUL,
   .op .ADD,
   .op (.Dup ⟨14, by decide⟩)]

def prCol5part2Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 : UInt256) (rest : List UInt256) : State :=
  let v0 : UInt256 := x0 * x1
  let v1 : UInt256 := v0 + x2
  let v2 : UInt256 := MachineState.readWord s.memory 32
  let v3 : UInt256 := x12 * v2
  let v4 : UInt256 := v3 + v1
  {s with pc := UInt256.ofNat 4884, memory := s.memory, stack := x16 :: v4 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: x18 :: x19 :: rest}

theorem prCol5part2_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions prCol5part2Program {s with pc := UInt256.ofNat 4875, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: x18 :: x19 :: rest} =
      some (prCol5part2Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 rest) := by
  have hc (j : Nat) (hj : j ≤ 33) : rest.length + j < 1024 := by omega
  have hcr : rest.length < 1024 := by omega
  have ha32 : (32 : UInt256).toNat = 32 := rfl
  have hf32 := activeWords_fix s 32 32 (by decide) (by norm_num) hact
  simp [hz, hzn, prCol5part2Program, prCol5part2Model, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, ofNat_sub_ofNat, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, hc, hcr, ha32, hf32]

def prCol5part3Program : List Instr :=
  [.op (.Dup ⟨5, by decide⟩),
   .op .MUL,
   .op .ADD,
   .op (.Dup ⟨13, by decide⟩),
   .op (.Dup ⟨4, by decide⟩),
   .op .MUL,
   .op .ADD,
   .op (.Dup ⟨12, by decide⟩)]

def prCol5part3Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 : UInt256) (rest : List UInt256) : State :=
  let v0 : UInt256 := x5 * x0
  let v1 : UInt256 := v0 + x1
  let v2 : UInt256 := x4 * x14
  let v3 : UInt256 := v2 + v1
  {s with pc := UInt256.ofNat 4892, memory := s.memory, stack := x13 :: v3 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: x18 :: rest}

theorem prCol5part3_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions prCol5part3Program {s with pc := UInt256.ofNat 4884, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: x18 :: rest} =
      some (prCol5part3Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 rest) := by
  have hc (j : Nat) (hj : j ≤ 33) : rest.length + j < 1024 := by omega
  have hcr : rest.length < 1024 := by omega
  simp [hz, hzn, prCol5part3Program, prCol5part3Model, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, ofNat_sub_ofNat, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, hc, hcr]

def prCol5part4Program : List Instr :=
  [.op (.Dup ⟨3, by decide⟩),
   .op .MUL,
   .op .ADD,
   .op (.Dup ⟨11, by decide⟩),
   .op (.Dup ⟨6, by decide⟩),
   .op .MUL,
   .op .ADD,
   .op (.Swap ⟨0, by decide⟩)]

def prCol5part4Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 : UInt256) (rest : List UInt256) : State :=
  let v0 : UInt256 := x3 * x0
  let v1 : UInt256 := v0 + x1
  let v2 : UInt256 := x6 * x12
  let v3 : UInt256 := v2 + v1
  {s with pc := UInt256.ofNat 4900, memory := s.memory, stack := x2 :: v3 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: x18 :: rest}

theorem prCol5part4_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions prCol5part4Program {s with pc := UInt256.ofNat 4892, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: x18 :: rest} =
      some (prCol5part4Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 rest) := by
  have hc (j : Nat) (hj : j ≤ 33) : rest.length + j < 1024 := by omega
  have hcr : rest.length < 1024 := by omega
  simp [hz, hzn, prCol5part4Program, prCol5part4Model, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, ofNat_sub_ofNat, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, hc, hcr]

def prCol5part5Program : List Instr :=
  [.op (.Dup ⟨15, by decide⟩),
   .push 1 128,
   .op .MLOAD,
   .op (.Dup ⟨9, by decide⟩),
   .op .MULMOD,
   .op .ADD,
   .op (.Dup ⟨15, by decide⟩)]

def prCol5part5Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 : UInt256) (rest : List UInt256) : State :=
  let v0 : UInt256 := MachineState.readWord s.memory 128
  let v1 : UInt256 := UInt256.mulMod x7 v0 x15
  let v2 : UInt256 := v1 + x0
  {s with pc := UInt256.ofNat 4908, memory := s.memory, stack := x15 :: v2 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: rest}

theorem prCol5part5_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions prCol5part5Program {s with pc := UInt256.ofNat 4900, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: rest} =
      some (prCol5part5Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 rest) := by
  have hc (j : Nat) (hj : j ≤ 34) : rest.length + j < 1024 := by omega
  have hcr : rest.length < 1024 := by omega
  have ha128 : (128 : UInt256).toNat = 128 := rfl
  have hf128 := activeWords_fix s 128 32 (by decide) (by norm_num) hact
  simp [hz, hzn, prCol5part5Program, prCol5part5Model, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, ofNat_sub_ofNat, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, hc, hcr, ha128, hf128]

def prCol5part6Program : List Instr :=
  [.push 1 96,
   .op .MLOAD,
   .op (.Dup ⟨10, by decide⟩),
   .op .MULMOD,
   .op .ADD,
   .op (.Dup ⟨15, by decide⟩),
   .push 1 64,
   .op .MLOAD]

def prCol5part6Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 : UInt256) (rest : List UInt256) : State :=
  let v0 : UInt256 := MachineState.readWord s.memory 96
  let v1 : UInt256 := UInt256.mulMod x9 v0 x0
  let v2 : UInt256 := v1 + x1
  let v3 : UInt256 := MachineState.readWord s.memory 64
  {s with pc := UInt256.ofNat 4918, memory := s.memory, stack := v3 :: x16 :: v2 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: x18 :: rest}

theorem prCol5part6_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions prCol5part6Program {s with pc := UInt256.ofNat 4908, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: x18 :: rest} =
      some (prCol5part6Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 rest) := by
  have hc (j : Nat) (hj : j ≤ 34) : rest.length + j < 1024 := by omega
  have hcr : rest.length < 1024 := by omega
  have ha96 : (96 : UInt256).toNat = 96 := rfl
  have hf96 := activeWords_fix s 96 32 (by decide) (by norm_num) hact
  have ha64 : (64 : UInt256).toNat = 64 := rfl
  have hf64 := activeWords_fix s 64 32 (by decide) (by norm_num) hact
  simp [hz, hzn, prCol5part6Program, prCol5part6Model, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, ofNat_sub_ofNat, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, hc, hcr, ha96, hf96, ha64, hf64]

def prCol5part7Program : List Instr :=
  [.op (.Dup ⟨11, by decide⟩),
   .op .MULMOD,
   .op .ADD,
   .op (.Dup ⟨15, by decide⟩),
   .push 1 32,
   .op .MLOAD,
   .op (.Dup ⟨12, by decide⟩),
   .op .MULMOD]

def prCol5part7Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 : UInt256) (rest : List UInt256) : State :=
  let v0 : UInt256 := UInt256.mulMod x11 x0 x1
  let v1 : UInt256 := v0 + x2
  let v2 : UInt256 := MachineState.readWord s.memory 32
  let v3 : UInt256 := UInt256.mulMod x12 v2 x17
  {s with pc := UInt256.ofNat 4927, memory := s.memory, stack := v3 :: v1 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: x18 :: x19 :: rest}

theorem prCol5part7_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions prCol5part7Program {s with pc := UInt256.ofNat 4918, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: x18 :: x19 :: rest} =
      some (prCol5part7Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 rest) := by
  have hc (j : Nat) (hj : j ≤ 34) : rest.length + j < 1024 := by omega
  have hcr : rest.length < 1024 := by omega
  have ha32 : (32 : UInt256).toNat = 32 := rfl
  have hf32 := activeWords_fix s 32 32 (by decide) (by norm_num) hact
  simp [hz, hzn, prCol5part7Program, prCol5part7Model, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, ofNat_sub_ofNat, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, hc, hcr, ha32, hf32]

def prCol5part8Program : List Instr :=
  [.op .ADD,
   .op (.Dup ⟨15, by decide⟩),
   .op (.Dup ⟨15, by decide⟩),
   .op (.Dup ⟨6, by decide⟩),
   .op .MULMOD,
   .op .ADD,
   .op (.Dup ⟨15, by decide⟩),
   .op (.Dup ⟨14, by decide⟩)]

def prCol5part8Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 : UInt256) (rest : List UInt256) : State :=
  let v0 : UInt256 := x0 + x1
  let v1 : UInt256 := UInt256.mulMod x5 x15 x16
  let v2 : UInt256 := v1 + v0
  {s with pc := UInt256.ofNat 4935, memory := s.memory, stack := x14 :: x16 :: v2 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: x18 :: rest}

theorem prCol5part8_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions prCol5part8Program {s with pc := UInt256.ofNat 4927, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: x18 :: rest} =
      some (prCol5part8Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 rest) := by
  have hc (j : Nat) (hj : j ≤ 34) : rest.length + j < 1024 := by omega
  have hcr : rest.length < 1024 := by omega
  simp [hz, hzn, prCol5part8Program, prCol5part8Model, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, ofNat_sub_ofNat, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, hc, hcr]

def prCol5part9Program : List Instr :=
  [.op (.Dup ⟨5, by decide⟩),
   .op .MULMOD,
   .op .ADD,
   .op (.Dup ⟨15, by decide⟩),
   .op (.Dup ⟨13, by decide⟩),
   .op (.Dup ⟨4, by decide⟩),
   .op .MULMOD,
   .op .ADD]

def prCol5part9Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 : UInt256) (rest : List UInt256) : State :=
  let v0 : UInt256 := UInt256.mulMod x5 x0 x1
  let v1 : UInt256 := v0 + x2
  let v2 : UInt256 := UInt256.mulMod x4 x14 x17
  let v3 : UInt256 := v2 + v1
  {s with pc := UInt256.ofNat 4943, memory := s.memory, stack := v3 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: x18 :: x19 :: rest}

theorem prCol5part9_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions prCol5part9Program {s with pc := UInt256.ofNat 4935, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: x18 :: x19 :: rest} =
      some (prCol5part9Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 rest) := by
  have hc (j : Nat) (hj : j ≤ 34) : rest.length + j < 1024 := by omega
  have hcr : rest.length < 1024 := by omega
  simp [hz, hzn, prCol5part9Program, prCol5part9Model, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, ofNat_sub_ofNat, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, hc, hcr]

def prCol5part10Program : List Instr :=
  [.op (.Dup ⟨15, by decide⟩),
   .op (.Dup ⟨12, by decide⟩),
   .op (.Dup ⟨7, by decide⟩),
   .op .MULMOD,
   .op .ADD,
   .op (.Dup ⟨15, by decide⟩),
   .op (.Swap ⟨0, by decide⟩),
   .op (.Dup ⟨2, by decide⟩)]

def prCol5part10Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 : UInt256) (rest : List UInt256) : State :=
  let v0 : UInt256 := UInt256.mulMod x5 x11 x15
  let v1 : UInt256 := v0 + x0
  {s with pc := UInt256.ofNat 4951, memory := s.memory, stack := x1 :: v1 :: x15 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: rest}

theorem prCol5part10_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions prCol5part10Program {s with pc := UInt256.ofNat 4943, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: rest} =
      some (prCol5part10Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 rest) := by
  have hc (j : Nat) (hj : j ≤ 34) : rest.length + j < 1024 := by omega
  have hcr : rest.length < 1024 := by omega
  simp [hz, hzn, prCol5part10Program, prCol5part10Model, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, ofNat_sub_ofNat, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, hc, hcr]

def prCol5part11Program : List Instr :=
  [.op .NOT,
   .op .ADDMOD,
   .push 1 5,
   .op .SHR,
   .op (.Dup ⟨1, by decide⟩),
   .push 1 224,
   .op .MLOAD,
   .op .AND]

def prCol5part11Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 : UInt256) (rest : List UInt256) : State :=
  let v0 : UInt256 := UInt256.lnot x0
  let v1 : UInt256 := UInt256.addMod v0 x1 x2
  let v2 : UInt256 := UInt256.shiftRight v1 (UInt256.ofNat 5)
  let v3 : UInt256 := MachineState.readWord s.memory 224
  let v4 : UInt256 := UInt256.land v3 x3
  {s with pc := UInt256.ofNat 4961, memory := s.memory, stack := v4 :: v2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: x18 :: x19 :: rest}

theorem prCol5part11_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions prCol5part11Program {s with pc := UInt256.ofNat 4951, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: x18 :: x19 :: rest} =
      some (prCol5part11Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 rest) := by
  have hc (j : Nat) (hj : j ≤ 33) : rest.length + j < 1024 := by omega
  have hcr : rest.length < 1024 := by omega
  have ha224 : (224 : UInt256).toNat = 224 := rfl
  have hf224 := activeWords_fix s 224 32 (by decide) (by norm_num) hact
  simp [hz, hzn, prCol5part11Program, prCol5part11Model, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, ofNat_sub_ofNat, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, hc, hcr, ha224, hf224]

def prCol5part12Program : List Instr :=
  [.op (.Swap ⟨6, by decide⟩),
   .op .POP,
   .push 1 16,
   .op .SHL,
   .op (.Swap ⟨0, by decide⟩),
   .push 1 240,
   .op .SHR,
   .op .ADD]

def prCol5part12Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 : UInt256) (rest : List UInt256) : State :=
  let v0 : UInt256 := UInt256.shiftLeft x1 (UInt256.ofNat 16)
  let v1 : UInt256 := UInt256.shiftRight x2 (UInt256.ofNat 240)
  let v2 : UInt256 := v1 + v0
  {s with pc := UInt256.ofNat 4971, memory := s.memory, stack := v2 :: x3 :: x4 :: x5 :: x6 :: x0 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: x18 :: rest}

theorem prCol5part12_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions prCol5part12Program {s with pc := UInt256.ofNat 4961, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: x18 :: rest} =
      some (prCol5part12Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 rest) := by
  have hc (j : Nat) (hj : j ≤ 32) : rest.length + j < 1024 := by omega
  have hcr : rest.length < 1024 := by omega
  simp [hz, hzn, prCol5part12Program, prCol5part12Model, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, ofNat_sub_ofNat, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, hc, hcr]

def prCol5Program : List Instr :=
  [.op .JUMPDEST,
   .op (.Dup ⟨0, by decide⟩),
   .push 1 128,
   .op .MLOAD,
   .op (.Dup ⟨8, by decide⟩),
   .op .MUL,
   .op .ADD,
   .push 1 96,
   .op .MLOAD,
   .op (.Dup ⟨9, by decide⟩),
   .op .MUL,
   .op .ADD,
   .push 1 64,
   .op .MLOAD,
   .op (.Dup ⟨10, by decide⟩),
   .op .MUL,
   .op .ADD,
   .push 1 32,
   .op .MLOAD,
   .op (.Dup ⟨11, by decide⟩),
   .op .MUL,
   .op .ADD,
   .op (.Dup ⟨14, by decide⟩),
   .op (.Dup ⟨5, by decide⟩),
   .op .MUL,
   .op .ADD,
   .op (.Dup ⟨13, by decide⟩),
   .op (.Dup ⟨4, by decide⟩),
   .op .MUL,
   .op .ADD,
   .op (.Dup ⟨12, by decide⟩),
   .op (.Dup ⟨3, by decide⟩),
   .op .MUL,
   .op .ADD,
   .op (.Dup ⟨11, by decide⟩),
   .op (.Dup ⟨6, by decide⟩),
   .op .MUL,
   .op .ADD,
   .op (.Swap ⟨0, by decide⟩),
   .op (.Dup ⟨15, by decide⟩),
   .push 1 128,
   .op .MLOAD,
   .op (.Dup ⟨9, by decide⟩),
   .op .MULMOD,
   .op .ADD,
   .op (.Dup ⟨15, by decide⟩),
   .push 1 96,
   .op .MLOAD,
   .op (.Dup ⟨10, by decide⟩),
   .op .MULMOD,
   .op .ADD,
   .op (.Dup ⟨15, by decide⟩),
   .push 1 64,
   .op .MLOAD,
   .op (.Dup ⟨11, by decide⟩),
   .op .MULMOD,
   .op .ADD,
   .op (.Dup ⟨15, by decide⟩),
   .push 1 32,
   .op .MLOAD,
   .op (.Dup ⟨12, by decide⟩),
   .op .MULMOD,
   .op .ADD,
   .op (.Dup ⟨15, by decide⟩),
   .op (.Dup ⟨15, by decide⟩),
   .op (.Dup ⟨6, by decide⟩),
   .op .MULMOD,
   .op .ADD,
   .op (.Dup ⟨15, by decide⟩),
   .op (.Dup ⟨14, by decide⟩),
   .op (.Dup ⟨5, by decide⟩),
   .op .MULMOD,
   .op .ADD,
   .op (.Dup ⟨15, by decide⟩),
   .op (.Dup ⟨13, by decide⟩),
   .op (.Dup ⟨4, by decide⟩),
   .op .MULMOD,
   .op .ADD,
   .op (.Dup ⟨15, by decide⟩),
   .op (.Dup ⟨12, by decide⟩),
   .op (.Dup ⟨7, by decide⟩),
   .op .MULMOD,
   .op .ADD,
   .op (.Dup ⟨15, by decide⟩),
   .op (.Swap ⟨0, by decide⟩),
   .op (.Dup ⟨2, by decide⟩),
   .op .NOT,
   .op .ADDMOD,
   .push 1 5,
   .op .SHR,
   .op (.Dup ⟨1, by decide⟩),
   .push 1 224,
   .op .MLOAD,
   .op .AND,
   .op (.Swap ⟨6, by decide⟩),
   .op .POP,
   .push 1 16,
   .op .SHL,
   .op (.Swap ⟨0, by decide⟩),
   .push 1 240,
   .op .SHR,
   .op .ADD]

def prCol5Model (s : State) (c q3 q2 q1 q4 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp : UInt256) (rest : List UInt256) : State :=
  let v0 : UInt256 := MachineState.readWord s.memory 128
  let v1 : UInt256 := x1 * v0
  let v2 : UInt256 := v1 + c
  let v3 : UInt256 := MachineState.readWord s.memory 96
  let v4 : UInt256 := x2 * v3
  let v5 : UInt256 := v4 + v2
  let v6 : UInt256 := MachineState.readWord s.memory 64
  let v7 : UInt256 := x3 * v6
  let v8 : UInt256 := v7 + v5
  let v9 : UInt256 := MachineState.readWord s.memory 32
  let v10 : UInt256 := x4 * v9
  let v11 : UInt256 := v10 + v8
  let v12 : UInt256 := q1 * n4
  let v13 : UInt256 := v12 + v11
  let v14 : UInt256 := q2 * n3
  let v15 : UInt256 := v14 + v13
  let v16 : UInt256 := q3 * n2
  let v17 : UInt256 := v16 + v15
  let v18 : UInt256 := q4 * n1
  let v19 : UInt256 := v18 + v17
  let v20 : UInt256 := MachineState.readWord s.memory 128
  let v21 : UInt256 := UInt256.mulMod x1 v20 P
  let v22 : UInt256 := v21 + c
  let v23 : UInt256 := MachineState.readWord s.memory 96
  let v24 : UInt256 := UInt256.mulMod x2 v23 P
  let v25 : UInt256 := v24 + v22
  let v26 : UInt256 := MachineState.readWord s.memory 64
  let v27 : UInt256 := UInt256.mulMod x3 v26 P
  let v28 : UInt256 := v27 + v25
  let v29 : UInt256 := MachineState.readWord s.memory 32
  let v30 : UInt256 := UInt256.mulMod x4 v29 P
  let v31 : UInt256 := v30 + v28
  let v32 : UInt256 := UInt256.mulMod q1 n4 P
  let v33 : UInt256 := v32 + v31
  let v34 : UInt256 := UInt256.mulMod q2 n3 P
  let v35 : UInt256 := v34 + v33
  let v36 : UInt256 := UInt256.mulMod q3 n2 P
  let v37 : UInt256 := v36 + v35
  let v38 : UInt256 := UInt256.mulMod q4 n1 P
  let v39 : UInt256 := v38 + v37
  let v40 : UInt256 := UInt256.lnot v19
  let v41 : UInt256 := UInt256.addMod v40 v39 P
  let v42 : UInt256 := UInt256.shiftRight v41 (UInt256.ofNat 5)
  let v43 : UInt256 := MachineState.readWord s.memory 224
  let v44 : UInt256 := UInt256.land v43 v19
  let v45 : UInt256 := UInt256.shiftLeft v42 (UInt256.ofNat 16)
  let v46 : UInt256 := UInt256.shiftRight v19 (UInt256.ofNat 240)
  let v47 : UInt256 := v46 + v45
  {s with pc := UInt256.ofNat 4971, memory := s.memory, stack := v47 :: q3 :: q2 :: q1 :: q4 :: v44 :: x1 :: x2 :: x3 :: x4 :: n1 :: n2 :: n3 :: n4 :: P :: inv :: cntp :: rest}

theorem prCol5_run (s : State) (c q3 q2 q1 q4 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions prCol5Program {s with pc := UInt256.ofNat 4857, stack := c :: q3 :: q2 :: q1 :: q4 :: x0 :: x1 :: x2 :: x3 :: x4 :: n1 :: n2 :: n3 :: n4 :: P :: inv :: cntp :: rest} =
      some (prCol5Model s c q3 q2 q1 q4 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp rest) := by
  let v0 : UInt256 := MachineState.readWord s.memory 128
  let v1 : UInt256 := x1 * v0
  let v2 : UInt256 := v1 + c
  let v3 : UInt256 := MachineState.readWord s.memory 96
  let v4 : UInt256 := x2 * v3
  let v5 : UInt256 := v4 + v2
  let v6 : UInt256 := MachineState.readWord s.memory 64
  let v7 : UInt256 := x3 * v6
  let v8 : UInt256 := v7 + v5
  let v9 : UInt256 := MachineState.readWord s.memory 32
  let v10 : UInt256 := x4 * v9
  let v11 : UInt256 := v10 + v8
  let v12 : UInt256 := q1 * n4
  let v13 : UInt256 := v12 + v11
  let v14 : UInt256 := q2 * n3
  let v15 : UInt256 := v14 + v13
  let v16 : UInt256 := q3 * n2
  let v17 : UInt256 := v16 + v15
  let v18 : UInt256 := q4 * n1
  let v19 : UInt256 := v18 + v17
  let v20 : UInt256 := MachineState.readWord s.memory 128
  let v21 : UInt256 := UInt256.mulMod x1 v20 P
  let v22 : UInt256 := v21 + c
  let v23 : UInt256 := MachineState.readWord s.memory 96
  let v24 : UInt256 := UInt256.mulMod x2 v23 P
  let v25 : UInt256 := v24 + v22
  let v26 : UInt256 := MachineState.readWord s.memory 64
  let v27 : UInt256 := UInt256.mulMod x3 v26 P
  let v28 : UInt256 := v27 + v25
  let v29 : UInt256 := MachineState.readWord s.memory 32
  let v30 : UInt256 := UInt256.mulMod x4 v29 P
  let v31 : UInt256 := v30 + v28
  let v32 : UInt256 := UInt256.mulMod q1 n4 P
  let v33 : UInt256 := v32 + v31
  let v34 : UInt256 := UInt256.mulMod q2 n3 P
  let v35 : UInt256 := v34 + v33
  let v36 : UInt256 := UInt256.mulMod q3 n2 P
  let v37 : UInt256 := v36 + v35
  let v38 : UInt256 := UInt256.mulMod q4 n1 P
  let v39 : UInt256 := v38 + v37
  let v40 : UInt256 := UInt256.lnot v19
  let v41 : UInt256 := UInt256.addMod v40 v39 P
  let v42 : UInt256 := UInt256.shiftRight v41 (UInt256.ofNat 5)
  let v43 : UInt256 := MachineState.readWord s.memory 224
  let v44 : UInt256 := UInt256.land v43 v19
  let v45 : UInt256 := UInt256.shiftLeft v42 (UInt256.ofNat 16)
  let v46 : UInt256 := UInt256.shiftRight v19 (UInt256.ofNat 240)
  let v47 : UInt256 := v46 + v45
  have h0 : runInstructions prCol5part0Program {s with pc := UInt256.ofNat 4857, memory := s.memory, stack := c :: q3 :: q2 :: q1 :: q4 :: x0 :: x1 :: x2 :: x3 :: x4 :: n1 :: n2 :: n3 :: n4 :: P :: inv :: cntp :: rest} = some {s with pc := UInt256.ofNat 4865, memory := s.memory, stack := v2 :: c :: q3 :: q2 :: q1 :: q4 :: x0 :: x1 :: x2 :: x3 :: x4 :: n1 :: n2 :: n3 :: n4 :: P :: inv :: cntp :: rest} := by
    simpa only [prCol5part0Model, v0, v1, v2] using prCol5part0_run (s) c q3 q2 q1 q4 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp rest hcap hact
  have h1 : runInstructions prCol5part1Program {s with pc := UInt256.ofNat 4865, memory := s.memory, stack := v2 :: c :: q3 :: q2 :: q1 :: q4 :: x0 :: x1 :: x2 :: x3 :: x4 :: n1 :: n2 :: n3 :: n4 :: P :: inv :: cntp :: rest} = some {s with pc := UInt256.ofNat 4875, memory := s.memory, stack := x3 :: v6 :: v5 :: c :: q3 :: q2 :: q1 :: q4 :: x0 :: x1 :: x2 :: x3 :: x4 :: n1 :: n2 :: n3 :: n4 :: P :: inv :: cntp :: rest} := by
    simpa only [prCol5part1Model, v3, v4, v5, v6] using prCol5part1_run (s) v2 c q3 q2 q1 q4 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp rest hcap hact
  have h2 : runInstructions prCol5part2Program {s with pc := UInt256.ofNat 4875, memory := s.memory, stack := x3 :: v6 :: v5 :: c :: q3 :: q2 :: q1 :: q4 :: x0 :: x1 :: x2 :: x3 :: x4 :: n1 :: n2 :: n3 :: n4 :: P :: inv :: cntp :: rest} = some {s with pc := UInt256.ofNat 4884, memory := s.memory, stack := n4 :: v11 :: c :: q3 :: q2 :: q1 :: q4 :: x0 :: x1 :: x2 :: x3 :: x4 :: n1 :: n2 :: n3 :: n4 :: P :: inv :: cntp :: rest} := by
    simpa only [prCol5part2Model, v7, v8, v9, v10, v11] using prCol5part2_run (s) x3 v6 v5 c q3 q2 q1 q4 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp rest hcap hact
  have h3 : runInstructions prCol5part3Program {s with pc := UInt256.ofNat 4884, memory := s.memory, stack := n4 :: v11 :: c :: q3 :: q2 :: q1 :: q4 :: x0 :: x1 :: x2 :: x3 :: x4 :: n1 :: n2 :: n3 :: n4 :: P :: inv :: cntp :: rest} = some {s with pc := UInt256.ofNat 4892, memory := s.memory, stack := n2 :: v15 :: c :: q3 :: q2 :: q1 :: q4 :: x0 :: x1 :: x2 :: x3 :: x4 :: n1 :: n2 :: n3 :: n4 :: P :: inv :: cntp :: rest} := by
    simpa only [prCol5part3Model, v12, v13, v14, v15] using prCol5part3_run (s) n4 v11 c q3 q2 q1 q4 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp rest hcap hact
  have h4 : runInstructions prCol5part4Program {s with pc := UInt256.ofNat 4892, memory := s.memory, stack := n2 :: v15 :: c :: q3 :: q2 :: q1 :: q4 :: x0 :: x1 :: x2 :: x3 :: x4 :: n1 :: n2 :: n3 :: n4 :: P :: inv :: cntp :: rest} = some {s with pc := UInt256.ofNat 4900, memory := s.memory, stack := c :: v19 :: q3 :: q2 :: q1 :: q4 :: x0 :: x1 :: x2 :: x3 :: x4 :: n1 :: n2 :: n3 :: n4 :: P :: inv :: cntp :: rest} := by
    simpa only [prCol5part4Model, v16, v17, v18, v19] using prCol5part4_run (s) n2 v15 c q3 q2 q1 q4 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp rest hcap hact
  have h5 : runInstructions prCol5part5Program {s with pc := UInt256.ofNat 4900, memory := s.memory, stack := c :: v19 :: q3 :: q2 :: q1 :: q4 :: x0 :: x1 :: x2 :: x3 :: x4 :: n1 :: n2 :: n3 :: n4 :: P :: inv :: cntp :: rest} = some {s with pc := UInt256.ofNat 4908, memory := s.memory, stack := P :: v22 :: v19 :: q3 :: q2 :: q1 :: q4 :: x0 :: x1 :: x2 :: x3 :: x4 :: n1 :: n2 :: n3 :: n4 :: P :: inv :: cntp :: rest} := by
    simpa only [prCol5part5Model, v20, v21, v22] using prCol5part5_run (s) c v19 q3 q2 q1 q4 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp rest hcap hact
  have h6 : runInstructions prCol5part6Program {s with pc := UInt256.ofNat 4908, memory := s.memory, stack := P :: v22 :: v19 :: q3 :: q2 :: q1 :: q4 :: x0 :: x1 :: x2 :: x3 :: x4 :: n1 :: n2 :: n3 :: n4 :: P :: inv :: cntp :: rest} = some {s with pc := UInt256.ofNat 4918, memory := s.memory, stack := v26 :: P :: v25 :: v19 :: q3 :: q2 :: q1 :: q4 :: x0 :: x1 :: x2 :: x3 :: x4 :: n1 :: n2 :: n3 :: n4 :: P :: inv :: cntp :: rest} := by
    simpa only [prCol5part6Model, v23, v24, v25, v26] using prCol5part6_run (s) P v22 v19 q3 q2 q1 q4 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp rest hcap hact
  have h7 : runInstructions prCol5part7Program {s with pc := UInt256.ofNat 4918, memory := s.memory, stack := v26 :: P :: v25 :: v19 :: q3 :: q2 :: q1 :: q4 :: x0 :: x1 :: x2 :: x3 :: x4 :: n1 :: n2 :: n3 :: n4 :: P :: inv :: cntp :: rest} = some {s with pc := UInt256.ofNat 4927, memory := s.memory, stack := v30 :: v28 :: v19 :: q3 :: q2 :: q1 :: q4 :: x0 :: x1 :: x2 :: x3 :: x4 :: n1 :: n2 :: n3 :: n4 :: P :: inv :: cntp :: rest} := by
    simpa only [prCol5part7Model, v27, v28, v29, v30] using prCol5part7_run (s) v26 P v25 v19 q3 q2 q1 q4 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp rest hcap hact
  have h8 : runInstructions prCol5part8Program {s with pc := UInt256.ofNat 4927, memory := s.memory, stack := v30 :: v28 :: v19 :: q3 :: q2 :: q1 :: q4 :: x0 :: x1 :: x2 :: x3 :: x4 :: n1 :: n2 :: n3 :: n4 :: P :: inv :: cntp :: rest} = some {s with pc := UInt256.ofNat 4935, memory := s.memory, stack := n3 :: P :: v33 :: v19 :: q3 :: q2 :: q1 :: q4 :: x0 :: x1 :: x2 :: x3 :: x4 :: n1 :: n2 :: n3 :: n4 :: P :: inv :: cntp :: rest} := by
    simpa only [prCol5part8Model, v31, v32, v33] using prCol5part8_run (s) v30 v28 v19 q3 q2 q1 q4 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp rest hcap hact
  have h9 : runInstructions prCol5part9Program {s with pc := UInt256.ofNat 4935, memory := s.memory, stack := n3 :: P :: v33 :: v19 :: q3 :: q2 :: q1 :: q4 :: x0 :: x1 :: x2 :: x3 :: x4 :: n1 :: n2 :: n3 :: n4 :: P :: inv :: cntp :: rest} = some {s with pc := UInt256.ofNat 4943, memory := s.memory, stack := v37 :: v19 :: q3 :: q2 :: q1 :: q4 :: x0 :: x1 :: x2 :: x3 :: x4 :: n1 :: n2 :: n3 :: n4 :: P :: inv :: cntp :: rest} := by
    simpa only [prCol5part9Model, v34, v35, v36, v37] using prCol5part9_run (s) n3 P v33 v19 q3 q2 q1 q4 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp rest hcap hact
  have h10 : runInstructions prCol5part10Program {s with pc := UInt256.ofNat 4943, memory := s.memory, stack := v37 :: v19 :: q3 :: q2 :: q1 :: q4 :: x0 :: x1 :: x2 :: x3 :: x4 :: n1 :: n2 :: n3 :: n4 :: P :: inv :: cntp :: rest} = some {s with pc := UInt256.ofNat 4951, memory := s.memory, stack := v19 :: v39 :: P :: v19 :: q3 :: q2 :: q1 :: q4 :: x0 :: x1 :: x2 :: x3 :: x4 :: n1 :: n2 :: n3 :: n4 :: P :: inv :: cntp :: rest} := by
    simpa only [prCol5part10Model, v38, v39] using prCol5part10_run (s) v37 v19 q3 q2 q1 q4 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp rest hcap hact
  have h11 : runInstructions prCol5part11Program {s with pc := UInt256.ofNat 4951, memory := s.memory, stack := v19 :: v39 :: P :: v19 :: q3 :: q2 :: q1 :: q4 :: x0 :: x1 :: x2 :: x3 :: x4 :: n1 :: n2 :: n3 :: n4 :: P :: inv :: cntp :: rest} = some {s with pc := UInt256.ofNat 4961, memory := s.memory, stack := v44 :: v42 :: v19 :: q3 :: q2 :: q1 :: q4 :: x0 :: x1 :: x2 :: x3 :: x4 :: n1 :: n2 :: n3 :: n4 :: P :: inv :: cntp :: rest} := by
    simpa only [prCol5part11Model, v40, v41, v42, v43, v44] using prCol5part11_run (s) v19 v39 P v19 q3 q2 q1 q4 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp rest hcap hact
  have h12 : runInstructions prCol5part12Program {s with pc := UInt256.ofNat 4961, memory := s.memory, stack := v44 :: v42 :: v19 :: q3 :: q2 :: q1 :: q4 :: x0 :: x1 :: x2 :: x3 :: x4 :: n1 :: n2 :: n3 :: n4 :: P :: inv :: cntp :: rest} = some {s with pc := UInt256.ofNat 4971, memory := s.memory, stack := v47 :: q3 :: q2 :: q1 :: q4 :: v44 :: x1 :: x2 :: x3 :: x4 :: n1 :: n2 :: n3 :: n4 :: P :: inv :: cntp :: rest} := by
    simpa only [prCol5part12Model, v45, v46, v47] using prCol5part12_run (s) v44 v42 v19 q3 q2 q1 q4 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp rest hcap hact
  exact (runInstructions_append_some _ _ _ _ _ h0 (runInstructions_append_some _ _ _ _ _ h1 (runInstructions_append_some _ _ _ _ _ h2 (runInstructions_append_some _ _ _ _ _ h3 (runInstructions_append_some _ _ _ _ _ h4 (runInstructions_append_some _ _ _ _ _ h5 (runInstructions_append_some _ _ _ _ _ h6 (runInstructions_append_some _ _ _ _ _ h7 (runInstructions_append_some _ _ _ _ _ h8 (runInstructions_append_some _ _ _ _ _ h9 (runInstructions_append_some _ _ _ _ _ h10 (runInstructions_append_some _ _ _ _ _ h11 h12))))))))))))

def prCol5_o0 (c q3 q2 q1 q4 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp b1 b2 b3 b4 M : UInt256) : UInt256 :=
  ((UInt256.shiftRight ((q4 * n1) + ((q3 * n2) + ((q2 * n3) + ((q1 * n4) + ((x4 * b1) + ((x3 * b2) + ((x2 * b3) + ((x1 * b4) + c)))))))) (UInt256.ofNat 240)) + (UInt256.shiftLeft (UInt256.shiftRight (UInt256.addMod (UInt256.lnot ((q4 * n1) + ((q3 * n2) + ((q2 * n3) + ((q1 * n4) + ((x4 * b1) + ((x3 * b2) + ((x2 * b3) + ((x1 * b4) + c))))))))) ((UInt256.mulMod q4 n1 P) + ((UInt256.mulMod q3 n2 P) + ((UInt256.mulMod q2 n3 P) + ((UInt256.mulMod q1 n4 P) + ((UInt256.mulMod x4 b1 P) + ((UInt256.mulMod x3 b2 P) + ((UInt256.mulMod x2 b3 P) + ((UInt256.mulMod x1 b4 P) + c)))))))) P) (UInt256.ofNat 5)) (UInt256.ofNat 16)))

def prCol5_o5 (c q3 q2 q1 q4 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp b1 b2 b3 b4 M : UInt256) : UInt256 :=
  (UInt256.land M ((q4 * n1) + ((q3 * n2) + ((q2 * n3) + ((q1 * n4) + ((x4 * b1) + ((x3 * b2) + ((x2 * b3) + ((x1 * b4) + c)))))))))

theorem prCol5_eq (s : State) (c q3 q2 q1 q4 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp b1 b2 b3 b4 M : UInt256) (rest : List UInt256)
    (h_b1 : MachineState.readWord s.memory 32 = b1)
    (h_b2 : MachineState.readWord s.memory 64 = b2)
    (h_b3 : MachineState.readWord s.memory 96 = b3)
    (h_b4 : MachineState.readWord s.memory 128 = b4)
    (h_M : MachineState.readWord s.memory 224 = M) :
    prCol5Model s c q3 q2 q1 q4 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp rest =
      {s with pc := UInt256.ofNat 4971, stack := (prCol5_o0 c q3 q2 q1 q4 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp b1 b2 b3 b4 M) :: q3 :: q2 :: q1 :: q4 :: (prCol5_o5 c q3 q2 q1 q4 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp b1 b2 b3 b4 M) :: x1 :: x2 :: x3 :: x4 :: n1 :: n2 :: n3 :: n4 :: P :: inv :: cntp :: rest} := by
  simp only [prCol5Model, prCol5_o0, prCol5_o5, h_b1, h_b2, h_b3, h_b4, h_M]

/-! ## prCol6: pc 4971..5062, 81 instructions -/

def prCol6part0Program : List Instr :=
  [.op (.Dup ⟨0, by decide⟩),
   .push 1 128,
   .op .MLOAD,
   .op (.Dup ⟨9, by decide⟩),
   .op .MUL,
   .op .ADD,
   .push 1 96,
   .op .MLOAD]

def prCol6part0Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 : UInt256) (rest : List UInt256) : State :=
  let v0 : UInt256 := MachineState.readWord s.memory 128
  let v1 : UInt256 := x7 * v0
  let v2 : UInt256 := v1 + x0
  let v3 : UInt256 := MachineState.readWord s.memory 96
  {s with pc := UInt256.ofNat 4981, memory := s.memory, stack := v3 :: v2 :: x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: rest}

theorem prCol6part0_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions prCol6part0Program {s with pc := UInt256.ofNat 4971, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: rest} =
      some (prCol6part0Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 rest) := by
  have hc (j : Nat) (hj : j ≤ 33) : rest.length + j < 1024 := by omega
  have hcr : rest.length < 1024 := by omega
  have ha128 : (128 : UInt256).toNat = 128 := rfl
  have hf128 := activeWords_fix s 128 32 (by decide) (by norm_num) hact
  have ha96 : (96 : UInt256).toNat = 96 := rfl
  have hf96 := activeWords_fix s 96 32 (by decide) (by norm_num) hact
  simp [hz, hzn, prCol6part0Program, prCol6part0Model, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, ofNat_sub_ofNat, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, hc, hcr, ha128, hf128, ha96, hf96]

def prCol6part1Program : List Instr :=
  [.op (.Dup ⟨10, by decide⟩),
   .op .MUL,
   .op .ADD,
   .push 1 64,
   .op .MLOAD,
   .op (.Dup ⟨11, by decide⟩),
   .op .MUL,
   .op .ADD]

def prCol6part1Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 : UInt256) (rest : List UInt256) : State :=
  let v0 : UInt256 := x10 * x0
  let v1 : UInt256 := v0 + x1
  let v2 : UInt256 := MachineState.readWord s.memory 64
  let v3 : UInt256 := x11 * v2
  let v4 : UInt256 := v3 + v1
  {s with pc := UInt256.ofNat 4990, memory := s.memory, stack := v4 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: x18 :: rest}

theorem prCol6part1_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions prCol6part1Program {s with pc := UInt256.ofNat 4981, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: x18 :: rest} =
      some (prCol6part1Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 rest) := by
  have hc (j : Nat) (hj : j ≤ 33) : rest.length + j < 1024 := by omega
  have hcr : rest.length < 1024 := by omega
  have ha64 : (64 : UInt256).toNat = 64 := rfl
  have hf64 := activeWords_fix s 64 32 (by decide) (by norm_num) hact
  simp [hz, hzn, prCol6part1Program, prCol6part1Model, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, ofNat_sub_ofNat, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, hc, hcr, ha64, hf64]

def prCol6part2Program : List Instr :=
  [.op (.Dup ⟨14, by decide⟩),
   .op (.Dup ⟨4, by decide⟩),
   .op .MUL,
   .op .ADD,
   .op (.Dup ⟨13, by decide⟩),
   .op (.Dup ⟨3, by decide⟩),
   .op .MUL,
   .op .ADD]

def prCol6part2Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 : UInt256) (rest : List UInt256) : State :=
  let v0 : UInt256 := x3 * x14
  let v1 : UInt256 := v0 + x0
  let v2 : UInt256 := x2 * x13
  let v3 : UInt256 := v2 + v1
  {s with pc := UInt256.ofNat 4998, memory := s.memory, stack := v3 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: rest}

theorem prCol6part2_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions prCol6part2Program {s with pc := UInt256.ofNat 4990, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: rest} =
      some (prCol6part2Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 rest) := by
  have hc (j : Nat) (hj : j ≤ 33) : rest.length + j < 1024 := by omega
  have hcr : rest.length < 1024 := by omega
  simp [hz, hzn, prCol6part2Program, prCol6part2Model, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, ofNat_sub_ofNat, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, hc, hcr]

def prCol6part3Program : List Instr :=
  [.op (.Dup ⟨12, by decide⟩),
   .op (.Dup ⟨6, by decide⟩),
   .op .MUL,
   .op .ADD,
   .op (.Swap ⟨0, by decide⟩),
   .op (.Dup ⟨15, by decide⟩),
   .push 1 128,
   .op .MLOAD]

def prCol6part3Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 : UInt256) (rest : List UInt256) : State :=
  let v0 : UInt256 := x5 * x12
  let v1 : UInt256 := v0 + x0
  let v2 : UInt256 := MachineState.readWord s.memory 128
  {s with pc := UInt256.ofNat 5007, memory := s.memory, stack := v2 :: x15 :: x1 :: v1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: rest}

theorem prCol6part3_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions prCol6part3Program {s with pc := UInt256.ofNat 4998, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: rest} =
      some (prCol6part3Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 rest) := by
  have hc (j : Nat) (hj : j ≤ 33) : rest.length + j < 1024 := by omega
  have hcr : rest.length < 1024 := by omega
  have ha128 : (128 : UInt256).toNat = 128 := rfl
  have hf128 := activeWords_fix s 128 32 (by decide) (by norm_num) hact
  simp [hz, hzn, prCol6part3Program, prCol6part3Model, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, ofNat_sub_ofNat, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, hc, hcr, ha128, hf128]

def prCol6part4Program : List Instr :=
  [.op (.Dup ⟨10, by decide⟩),
   .op .MULMOD,
   .op .ADD,
   .op (.Dup ⟨15, by decide⟩),
   .push 1 96,
   .op .MLOAD,
   .op (.Dup ⟨11, by decide⟩),
   .op .MULMOD]

def prCol6part4Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 : UInt256) (rest : List UInt256) : State :=
  let v0 : UInt256 := UInt256.mulMod x10 x0 x1
  let v1 : UInt256 := v0 + x2
  let v2 : UInt256 := MachineState.readWord s.memory 96
  let v3 : UInt256 := UInt256.mulMod x11 v2 x17
  {s with pc := UInt256.ofNat 5016, memory := s.memory, stack := v3 :: v1 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: x18 :: x19 :: rest}

theorem prCol6part4_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions prCol6part4Program {s with pc := UInt256.ofNat 5007, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: x18 :: x19 :: rest} =
      some (prCol6part4Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 rest) := by
  have hc (j : Nat) (hj : j ≤ 34) : rest.length + j < 1024 := by omega
  have hcr : rest.length < 1024 := by omega
  have ha96 : (96 : UInt256).toNat = 96 := rfl
  have hf96 := activeWords_fix s 96 32 (by decide) (by norm_num) hact
  simp [hz, hzn, prCol6part4Program, prCol6part4Model, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, ofNat_sub_ofNat, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, hc, hcr, ha96, hf96]

def prCol6part5Program : List Instr :=
  [.op .ADD,
   .op (.Dup ⟨15, by decide⟩),
   .push 1 64,
   .op .MLOAD,
   .op (.Dup ⟨12, by decide⟩),
   .op .MULMOD,
   .op .ADD,
   .op (.Dup ⟨15, by decide⟩)]

def prCol6part5Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 : UInt256) (rest : List UInt256) : State :=
  let v0 : UInt256 := x0 + x1
  let v1 : UInt256 := MachineState.readWord s.memory 64
  let v2 : UInt256 := UInt256.mulMod x11 v1 x16
  let v3 : UInt256 := v2 + v0
  {s with pc := UInt256.ofNat 5025, memory := s.memory, stack := x16 :: v3 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: x18 :: rest}

theorem prCol6part5_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions prCol6part5Program {s with pc := UInt256.ofNat 5016, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: x18 :: rest} =
      some (prCol6part5Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 rest) := by
  have hc (j : Nat) (hj : j ≤ 34) : rest.length + j < 1024 := by omega
  have hcr : rest.length < 1024 := by omega
  have ha64 : (64 : UInt256).toNat = 64 := rfl
  have hf64 := activeWords_fix s 64 32 (by decide) (by norm_num) hact
  simp [hz, hzn, prCol6part5Program, prCol6part5Model, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, ofNat_sub_ofNat, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, hc, hcr, ha64, hf64]

def prCol6part6Program : List Instr :=
  [.op (.Dup ⟨15, by decide⟩),
   .op (.Dup ⟨5, by decide⟩),
   .op .MULMOD,
   .op .ADD,
   .op (.Dup ⟨15, by decide⟩),
   .op (.Dup ⟨14, by decide⟩),
   .op (.Dup ⟨4, by decide⟩),
   .op .MULMOD]

def prCol6part6Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 : UInt256) (rest : List UInt256) : State :=
  let v0 : UInt256 := UInt256.mulMod x4 x15 x0
  let v1 : UInt256 := v0 + x1
  let v2 : UInt256 := UInt256.mulMod x3 x14 x16
  {s with pc := UInt256.ofNat 5033, memory := s.memory, stack := v2 :: v1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: x18 :: rest}

theorem prCol6part6_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions prCol6part6Program {s with pc := UInt256.ofNat 5025, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: x18 :: rest} =
      some (prCol6part6Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 rest) := by
  have hc (j : Nat) (hj : j ≤ 34) : rest.length + j < 1024 := by omega
  have hcr : rest.length < 1024 := by omega
  simp [hz, hzn, prCol6part6Program, prCol6part6Model, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, ofNat_sub_ofNat, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, hc, hcr]

def prCol6part7Program : List Instr :=
  [.op .ADD,
   .op (.Dup ⟨15, by decide⟩),
   .op (.Dup ⟨13, by decide⟩),
   .op (.Dup ⟨7, by decide⟩),
   .op .MULMOD,
   .op .ADD,
   .op (.Dup ⟨15, by decide⟩),
   .op (.Swap ⟨0, by decide⟩)]

def prCol6part7Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 : UInt256) (rest : List UInt256) : State :=
  let v0 : UInt256 := x0 + x1
  let v1 : UInt256 := UInt256.mulMod x6 x13 x16
  let v2 : UInt256 := v1 + v0
  {s with pc := UInt256.ofNat 5041, memory := s.memory, stack := v2 :: x16 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: x18 :: rest}

theorem prCol6part7_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions prCol6part7Program {s with pc := UInt256.ofNat 5033, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: x18 :: rest} =
      some (prCol6part7Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 rest) := by
  have hc (j : Nat) (hj : j ≤ 34) : rest.length + j < 1024 := by omega
  have hcr : rest.length < 1024 := by omega
  simp [hz, hzn, prCol6part7Program, prCol6part7Model, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, ofNat_sub_ofNat, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, hc, hcr]

def prCol6part8Program : List Instr :=
  [.op (.Dup ⟨2, by decide⟩),
   .op .NOT,
   .op .ADDMOD,
   .push 1 5,
   .op .SHR,
   .op (.Dup ⟨1, by decide⟩),
   .push 1 224,
   .op .MLOAD]

def prCol6part8Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 : UInt256) (rest : List UInt256) : State :=
  let v0 : UInt256 := UInt256.lnot x2
  let v1 : UInt256 := UInt256.addMod v0 x0 x1
  let v2 : UInt256 := UInt256.shiftRight v1 (UInt256.ofNat 5)
  let v3 : UInt256 := MachineState.readWord s.memory 224
  {s with pc := UInt256.ofNat 5051, memory := s.memory, stack := v3 :: x2 :: v2 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: x18 :: rest}

theorem prCol6part8_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions prCol6part8Program {s with pc := UInt256.ofNat 5041, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: x18 :: rest} =
      some (prCol6part8Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 rest) := by
  have hc (j : Nat) (hj : j ≤ 33) : rest.length + j < 1024 := by omega
  have hcr : rest.length < 1024 := by omega
  have ha224 : (224 : UInt256).toNat = 224 := rfl
  have hf224 := activeWords_fix s 224 32 (by decide) (by norm_num) hact
  simp [hz, hzn, prCol6part8Program, prCol6part8Model, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, ofNat_sub_ofNat, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, hc, hcr, ha224, hf224]

def prCol6part9Program : List Instr :=
  [.op .AND,
   .op (.Swap ⟨7, by decide⟩),
   .op .POP,
   .push 1 16,
   .op .SHL,
   .op (.Swap ⟨0, by decide⟩),
   .push 1 240,
   .op .SHR]

def prCol6part9Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 : UInt256) (rest : List UInt256) : State :=
  let v0 : UInt256 := UInt256.land x0 x1
  let v1 : UInt256 := UInt256.shiftLeft x2 (UInt256.ofNat 16)
  let v2 : UInt256 := UInt256.shiftRight x3 (UInt256.ofNat 240)
  {s with pc := UInt256.ofNat 5061, memory := s.memory, stack := v2 :: v1 :: x4 :: x5 :: x6 :: x7 :: x8 :: v0 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: x18 :: x19 :: rest}

theorem prCol6part9_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions prCol6part9Program {s with pc := UInt256.ofNat 5051, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: x18 :: x19 :: rest} =
      some (prCol6part9Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 rest) := by
  have hc (j : Nat) (hj : j ≤ 33) : rest.length + j < 1024 := by omega
  have hcr : rest.length < 1024 := by omega
  simp [hz, hzn, prCol6part9Program, prCol6part9Model, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, ofNat_sub_ofNat, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, hc, hcr]

def prCol6part10Program : List Instr :=
  [.op .ADD]

def prCol6part10Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 : UInt256) (rest : List UInt256) : State :=
  let v0 : UInt256 := x0 + x1
  {s with pc := UInt256.ofNat 5062, memory := s.memory, stack := v0 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: rest}

theorem prCol6part10_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions prCol6part10Program {s with pc := UInt256.ofNat 5061, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: rest} =
      some (prCol6part10Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 rest) := by
  have hc (j : Nat) (hj : j ≤ 31) : rest.length + j < 1024 := by omega
  have hcr : rest.length < 1024 := by omega
  simp [hz, hzn, prCol6part10Program, prCol6part10Model, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, ofNat_sub_ofNat, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, hc, hcr]

def prCol6Program : List Instr :=
  [.op (.Dup ⟨0, by decide⟩),
   .push 1 128,
   .op .MLOAD,
   .op (.Dup ⟨9, by decide⟩),
   .op .MUL,
   .op .ADD,
   .push 1 96,
   .op .MLOAD,
   .op (.Dup ⟨10, by decide⟩),
   .op .MUL,
   .op .ADD,
   .push 1 64,
   .op .MLOAD,
   .op (.Dup ⟨11, by decide⟩),
   .op .MUL,
   .op .ADD,
   .op (.Dup ⟨14, by decide⟩),
   .op (.Dup ⟨4, by decide⟩),
   .op .MUL,
   .op .ADD,
   .op (.Dup ⟨13, by decide⟩),
   .op (.Dup ⟨3, by decide⟩),
   .op .MUL,
   .op .ADD,
   .op (.Dup ⟨12, by decide⟩),
   .op (.Dup ⟨6, by decide⟩),
   .op .MUL,
   .op .ADD,
   .op (.Swap ⟨0, by decide⟩),
   .op (.Dup ⟨15, by decide⟩),
   .push 1 128,
   .op .MLOAD,
   .op (.Dup ⟨10, by decide⟩),
   .op .MULMOD,
   .op .ADD,
   .op (.Dup ⟨15, by decide⟩),
   .push 1 96,
   .op .MLOAD,
   .op (.Dup ⟨11, by decide⟩),
   .op .MULMOD,
   .op .ADD,
   .op (.Dup ⟨15, by decide⟩),
   .push 1 64,
   .op .MLOAD,
   .op (.Dup ⟨12, by decide⟩),
   .op .MULMOD,
   .op .ADD,
   .op (.Dup ⟨15, by decide⟩),
   .op (.Dup ⟨15, by decide⟩),
   .op (.Dup ⟨5, by decide⟩),
   .op .MULMOD,
   .op .ADD,
   .op (.Dup ⟨15, by decide⟩),
   .op (.Dup ⟨14, by decide⟩),
   .op (.Dup ⟨4, by decide⟩),
   .op .MULMOD,
   .op .ADD,
   .op (.Dup ⟨15, by decide⟩),
   .op (.Dup ⟨13, by decide⟩),
   .op (.Dup ⟨7, by decide⟩),
   .op .MULMOD,
   .op .ADD,
   .op (.Dup ⟨15, by decide⟩),
   .op (.Swap ⟨0, by decide⟩),
   .op (.Dup ⟨2, by decide⟩),
   .op .NOT,
   .op .ADDMOD,
   .push 1 5,
   .op .SHR,
   .op (.Dup ⟨1, by decide⟩),
   .push 1 224,
   .op .MLOAD,
   .op .AND,
   .op (.Swap ⟨7, by decide⟩),
   .op .POP,
   .push 1 16,
   .op .SHL,
   .op (.Swap ⟨0, by decide⟩),
   .push 1 240,
   .op .SHR,
   .op .ADD]

def prCol6Model (s : State) (c q3 q2 q1 q4 z0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp : UInt256) (rest : List UInt256) : State :=
  let v0 : UInt256 := MachineState.readWord s.memory 128
  let v1 : UInt256 := x2 * v0
  let v2 : UInt256 := v1 + c
  let v3 : UInt256 := MachineState.readWord s.memory 96
  let v4 : UInt256 := x3 * v3
  let v5 : UInt256 := v4 + v2
  let v6 : UInt256 := MachineState.readWord s.memory 64
  let v7 : UInt256 := x4 * v6
  let v8 : UInt256 := v7 + v5
  let v9 : UInt256 := q2 * n4
  let v10 : UInt256 := v9 + v8
  let v11 : UInt256 := q3 * n3
  let v12 : UInt256 := v11 + v10
  let v13 : UInt256 := q4 * n2
  let v14 : UInt256 := v13 + v12
  let v15 : UInt256 := MachineState.readWord s.memory 128
  let v16 : UInt256 := UInt256.mulMod x2 v15 P
  let v17 : UInt256 := v16 + c
  let v18 : UInt256 := MachineState.readWord s.memory 96
  let v19 : UInt256 := UInt256.mulMod x3 v18 P
  let v20 : UInt256 := v19 + v17
  let v21 : UInt256 := MachineState.readWord s.memory 64
  let v22 : UInt256 := UInt256.mulMod x4 v21 P
  let v23 : UInt256 := v22 + v20
  let v24 : UInt256 := UInt256.mulMod q2 n4 P
  let v25 : UInt256 := v24 + v23
  let v26 : UInt256 := UInt256.mulMod q3 n3 P
  let v27 : UInt256 := v26 + v25
  let v28 : UInt256 := UInt256.mulMod q4 n2 P
  let v29 : UInt256 := v28 + v27
  let v30 : UInt256 := UInt256.lnot v14
  let v31 : UInt256 := UInt256.addMod v30 v29 P
  let v32 : UInt256 := UInt256.shiftRight v31 (UInt256.ofNat 5)
  let v33 : UInt256 := MachineState.readWord s.memory 224
  let v34 : UInt256 := UInt256.land v33 v14
  let v35 : UInt256 := UInt256.shiftLeft v32 (UInt256.ofNat 16)
  let v36 : UInt256 := UInt256.shiftRight v14 (UInt256.ofNat 240)
  let v37 : UInt256 := v36 + v35
  {s with pc := UInt256.ofNat 5062, memory := s.memory, stack := v37 :: q3 :: q2 :: q1 :: q4 :: z0 :: v34 :: x2 :: x3 :: x4 :: n1 :: n2 :: n3 :: n4 :: P :: inv :: cntp :: rest}

theorem prCol6_run (s : State) (c q3 q2 q1 q4 z0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions prCol6Program {s with pc := UInt256.ofNat 4971, stack := c :: q3 :: q2 :: q1 :: q4 :: z0 :: x1 :: x2 :: x3 :: x4 :: n1 :: n2 :: n3 :: n4 :: P :: inv :: cntp :: rest} =
      some (prCol6Model s c q3 q2 q1 q4 z0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp rest) := by
  let v0 : UInt256 := MachineState.readWord s.memory 128
  let v1 : UInt256 := x2 * v0
  let v2 : UInt256 := v1 + c
  let v3 : UInt256 := MachineState.readWord s.memory 96
  let v4 : UInt256 := x3 * v3
  let v5 : UInt256 := v4 + v2
  let v6 : UInt256 := MachineState.readWord s.memory 64
  let v7 : UInt256 := x4 * v6
  let v8 : UInt256 := v7 + v5
  let v9 : UInt256 := q2 * n4
  let v10 : UInt256 := v9 + v8
  let v11 : UInt256 := q3 * n3
  let v12 : UInt256 := v11 + v10
  let v13 : UInt256 := q4 * n2
  let v14 : UInt256 := v13 + v12
  let v15 : UInt256 := MachineState.readWord s.memory 128
  let v16 : UInt256 := UInt256.mulMod x2 v15 P
  let v17 : UInt256 := v16 + c
  let v18 : UInt256 := MachineState.readWord s.memory 96
  let v19 : UInt256 := UInt256.mulMod x3 v18 P
  let v20 : UInt256 := v19 + v17
  let v21 : UInt256 := MachineState.readWord s.memory 64
  let v22 : UInt256 := UInt256.mulMod x4 v21 P
  let v23 : UInt256 := v22 + v20
  let v24 : UInt256 := UInt256.mulMod q2 n4 P
  let v25 : UInt256 := v24 + v23
  let v26 : UInt256 := UInt256.mulMod q3 n3 P
  let v27 : UInt256 := v26 + v25
  let v28 : UInt256 := UInt256.mulMod q4 n2 P
  let v29 : UInt256 := v28 + v27
  let v30 : UInt256 := UInt256.lnot v14
  let v31 : UInt256 := UInt256.addMod v30 v29 P
  let v32 : UInt256 := UInt256.shiftRight v31 (UInt256.ofNat 5)
  let v33 : UInt256 := MachineState.readWord s.memory 224
  let v34 : UInt256 := UInt256.land v33 v14
  let v35 : UInt256 := UInt256.shiftLeft v32 (UInt256.ofNat 16)
  let v36 : UInt256 := UInt256.shiftRight v14 (UInt256.ofNat 240)
  let v37 : UInt256 := v36 + v35
  have h0 : runInstructions prCol6part0Program {s with pc := UInt256.ofNat 4971, memory := s.memory, stack := c :: q3 :: q2 :: q1 :: q4 :: z0 :: x1 :: x2 :: x3 :: x4 :: n1 :: n2 :: n3 :: n4 :: P :: inv :: cntp :: rest} = some {s with pc := UInt256.ofNat 4981, memory := s.memory, stack := v3 :: v2 :: c :: q3 :: q2 :: q1 :: q4 :: z0 :: x1 :: x2 :: x3 :: x4 :: n1 :: n2 :: n3 :: n4 :: P :: inv :: cntp :: rest} := by
    simpa only [prCol6part0Model, v0, v1, v2, v3] using prCol6part0_run (s) c q3 q2 q1 q4 z0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp rest hcap hact
  have h1 : runInstructions prCol6part1Program {s with pc := UInt256.ofNat 4981, memory := s.memory, stack := v3 :: v2 :: c :: q3 :: q2 :: q1 :: q4 :: z0 :: x1 :: x2 :: x3 :: x4 :: n1 :: n2 :: n3 :: n4 :: P :: inv :: cntp :: rest} = some {s with pc := UInt256.ofNat 4990, memory := s.memory, stack := v8 :: c :: q3 :: q2 :: q1 :: q4 :: z0 :: x1 :: x2 :: x3 :: x4 :: n1 :: n2 :: n3 :: n4 :: P :: inv :: cntp :: rest} := by
    simpa only [prCol6part1Model, v4, v5, v6, v7, v8] using prCol6part1_run (s) v3 v2 c q3 q2 q1 q4 z0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp rest hcap hact
  have h2 : runInstructions prCol6part2Program {s with pc := UInt256.ofNat 4990, memory := s.memory, stack := v8 :: c :: q3 :: q2 :: q1 :: q4 :: z0 :: x1 :: x2 :: x3 :: x4 :: n1 :: n2 :: n3 :: n4 :: P :: inv :: cntp :: rest} = some {s with pc := UInt256.ofNat 4998, memory := s.memory, stack := v12 :: c :: q3 :: q2 :: q1 :: q4 :: z0 :: x1 :: x2 :: x3 :: x4 :: n1 :: n2 :: n3 :: n4 :: P :: inv :: cntp :: rest} := by
    simpa only [prCol6part2Model, v9, v10, v11, v12] using prCol6part2_run (s) v8 c q3 q2 q1 q4 z0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp rest hcap hact
  have h3 : runInstructions prCol6part3Program {s with pc := UInt256.ofNat 4998, memory := s.memory, stack := v12 :: c :: q3 :: q2 :: q1 :: q4 :: z0 :: x1 :: x2 :: x3 :: x4 :: n1 :: n2 :: n3 :: n4 :: P :: inv :: cntp :: rest} = some {s with pc := UInt256.ofNat 5007, memory := s.memory, stack := v15 :: P :: c :: v14 :: q3 :: q2 :: q1 :: q4 :: z0 :: x1 :: x2 :: x3 :: x4 :: n1 :: n2 :: n3 :: n4 :: P :: inv :: cntp :: rest} := by
    simpa only [prCol6part3Model, v13, v14, v15] using prCol6part3_run (s) v12 c q3 q2 q1 q4 z0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp rest hcap hact
  have h4 : runInstructions prCol6part4Program {s with pc := UInt256.ofNat 5007, memory := s.memory, stack := v15 :: P :: c :: v14 :: q3 :: q2 :: q1 :: q4 :: z0 :: x1 :: x2 :: x3 :: x4 :: n1 :: n2 :: n3 :: n4 :: P :: inv :: cntp :: rest} = some {s with pc := UInt256.ofNat 5016, memory := s.memory, stack := v19 :: v17 :: v14 :: q3 :: q2 :: q1 :: q4 :: z0 :: x1 :: x2 :: x3 :: x4 :: n1 :: n2 :: n3 :: n4 :: P :: inv :: cntp :: rest} := by
    simpa only [prCol6part4Model, v16, v17, v18, v19] using prCol6part4_run (s) v15 P c v14 q3 q2 q1 q4 z0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp rest hcap hact
  have h5 : runInstructions prCol6part5Program {s with pc := UInt256.ofNat 5016, memory := s.memory, stack := v19 :: v17 :: v14 :: q3 :: q2 :: q1 :: q4 :: z0 :: x1 :: x2 :: x3 :: x4 :: n1 :: n2 :: n3 :: n4 :: P :: inv :: cntp :: rest} = some {s with pc := UInt256.ofNat 5025, memory := s.memory, stack := P :: v23 :: v14 :: q3 :: q2 :: q1 :: q4 :: z0 :: x1 :: x2 :: x3 :: x4 :: n1 :: n2 :: n3 :: n4 :: P :: inv :: cntp :: rest} := by
    simpa only [prCol6part5Model, v20, v21, v22, v23] using prCol6part5_run (s) v19 v17 v14 q3 q2 q1 q4 z0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp rest hcap hact
  have h6 : runInstructions prCol6part6Program {s with pc := UInt256.ofNat 5025, memory := s.memory, stack := P :: v23 :: v14 :: q3 :: q2 :: q1 :: q4 :: z0 :: x1 :: x2 :: x3 :: x4 :: n1 :: n2 :: n3 :: n4 :: P :: inv :: cntp :: rest} = some {s with pc := UInt256.ofNat 5033, memory := s.memory, stack := v26 :: v25 :: v14 :: q3 :: q2 :: q1 :: q4 :: z0 :: x1 :: x2 :: x3 :: x4 :: n1 :: n2 :: n3 :: n4 :: P :: inv :: cntp :: rest} := by
    simpa only [prCol6part6Model, v24, v25, v26] using prCol6part6_run (s) P v23 v14 q3 q2 q1 q4 z0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp rest hcap hact
  have h7 : runInstructions prCol6part7Program {s with pc := UInt256.ofNat 5033, memory := s.memory, stack := v26 :: v25 :: v14 :: q3 :: q2 :: q1 :: q4 :: z0 :: x1 :: x2 :: x3 :: x4 :: n1 :: n2 :: n3 :: n4 :: P :: inv :: cntp :: rest} = some {s with pc := UInt256.ofNat 5041, memory := s.memory, stack := v29 :: P :: v14 :: q3 :: q2 :: q1 :: q4 :: z0 :: x1 :: x2 :: x3 :: x4 :: n1 :: n2 :: n3 :: n4 :: P :: inv :: cntp :: rest} := by
    simpa only [prCol6part7Model, v27, v28, v29] using prCol6part7_run (s) v26 v25 v14 q3 q2 q1 q4 z0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp rest hcap hact
  have h8 : runInstructions prCol6part8Program {s with pc := UInt256.ofNat 5041, memory := s.memory, stack := v29 :: P :: v14 :: q3 :: q2 :: q1 :: q4 :: z0 :: x1 :: x2 :: x3 :: x4 :: n1 :: n2 :: n3 :: n4 :: P :: inv :: cntp :: rest} = some {s with pc := UInt256.ofNat 5051, memory := s.memory, stack := v33 :: v14 :: v32 :: v14 :: q3 :: q2 :: q1 :: q4 :: z0 :: x1 :: x2 :: x3 :: x4 :: n1 :: n2 :: n3 :: n4 :: P :: inv :: cntp :: rest} := by
    simpa only [prCol6part8Model, v30, v31, v32, v33] using prCol6part8_run (s) v29 P v14 q3 q2 q1 q4 z0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp rest hcap hact
  have h9 : runInstructions prCol6part9Program {s with pc := UInt256.ofNat 5051, memory := s.memory, stack := v33 :: v14 :: v32 :: v14 :: q3 :: q2 :: q1 :: q4 :: z0 :: x1 :: x2 :: x3 :: x4 :: n1 :: n2 :: n3 :: n4 :: P :: inv :: cntp :: rest} = some {s with pc := UInt256.ofNat 5061, memory := s.memory, stack := v36 :: v35 :: q3 :: q2 :: q1 :: q4 :: z0 :: v34 :: x2 :: x3 :: x4 :: n1 :: n2 :: n3 :: n4 :: P :: inv :: cntp :: rest} := by
    simpa only [prCol6part9Model, v34, v35, v36] using prCol6part9_run (s) v33 v14 v32 v14 q3 q2 q1 q4 z0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp rest hcap hact
  have h10 : runInstructions prCol6part10Program {s with pc := UInt256.ofNat 5061, memory := s.memory, stack := v36 :: v35 :: q3 :: q2 :: q1 :: q4 :: z0 :: v34 :: x2 :: x3 :: x4 :: n1 :: n2 :: n3 :: n4 :: P :: inv :: cntp :: rest} = some {s with pc := UInt256.ofNat 5062, memory := s.memory, stack := v37 :: q3 :: q2 :: q1 :: q4 :: z0 :: v34 :: x2 :: x3 :: x4 :: n1 :: n2 :: n3 :: n4 :: P :: inv :: cntp :: rest} := by
    simpa only [prCol6part10Model, v37] using prCol6part10_run (s) v36 v35 q3 q2 q1 q4 z0 v34 x2 x3 x4 n1 n2 n3 n4 P inv cntp rest hcap hact
  exact (runInstructions_append_some _ _ _ _ _ h0 (runInstructions_append_some _ _ _ _ _ h1 (runInstructions_append_some _ _ _ _ _ h2 (runInstructions_append_some _ _ _ _ _ h3 (runInstructions_append_some _ _ _ _ _ h4 (runInstructions_append_some _ _ _ _ _ h5 (runInstructions_append_some _ _ _ _ _ h6 (runInstructions_append_some _ _ _ _ _ h7 (runInstructions_append_some _ _ _ _ _ h8 (runInstructions_append_some _ _ _ _ _ h9 h10))))))))))

def prCol6_o0 (c q3 q2 q1 q4 z0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp b2 b3 b4 M : UInt256) : UInt256 :=
  ((UInt256.shiftRight ((q4 * n2) + ((q3 * n3) + ((q2 * n4) + ((x4 * b2) + ((x3 * b3) + ((x2 * b4) + c)))))) (UInt256.ofNat 240)) + (UInt256.shiftLeft (UInt256.shiftRight (UInt256.addMod (UInt256.lnot ((q4 * n2) + ((q3 * n3) + ((q2 * n4) + ((x4 * b2) + ((x3 * b3) + ((x2 * b4) + c))))))) ((UInt256.mulMod q4 n2 P) + ((UInt256.mulMod q3 n3 P) + ((UInt256.mulMod q2 n4 P) + ((UInt256.mulMod x4 b2 P) + ((UInt256.mulMod x3 b3 P) + ((UInt256.mulMod x2 b4 P) + c)))))) P) (UInt256.ofNat 5)) (UInt256.ofNat 16)))

def prCol6_o6 (c q3 q2 q1 q4 z0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp b2 b3 b4 M : UInt256) : UInt256 :=
  (UInt256.land M ((q4 * n2) + ((q3 * n3) + ((q2 * n4) + ((x4 * b2) + ((x3 * b3) + ((x2 * b4) + c)))))))

theorem prCol6_eq (s : State) (c q3 q2 q1 q4 z0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp b2 b3 b4 M : UInt256) (rest : List UInt256)
    (h_b2 : MachineState.readWord s.memory 64 = b2)
    (h_b3 : MachineState.readWord s.memory 96 = b3)
    (h_b4 : MachineState.readWord s.memory 128 = b4)
    (h_M : MachineState.readWord s.memory 224 = M) :
    prCol6Model s c q3 q2 q1 q4 z0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp rest =
      {s with pc := UInt256.ofNat 5062, stack := (prCol6_o0 c q3 q2 q1 q4 z0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp b2 b3 b4 M) :: q3 :: q2 :: q1 :: q4 :: z0 :: (prCol6_o6 c q3 q2 q1 q4 z0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp b2 b3 b4 M) :: x2 :: x3 :: x4 :: n1 :: n2 :: n3 :: n4 :: P :: inv :: cntp :: rest} := by
  simp only [prCol6Model, prCol6_o0, prCol6_o6, h_b2, h_b3, h_b4, h_M]

/-! ## prCol7: pc 5062..5131, 61 instructions -/

def prCol7part0Program : List Instr :=
  [.op (.Dup ⟨0, by decide⟩),
   .push 1 128,
   .op .MLOAD,
   .op (.Dup ⟨10, by decide⟩),
   .op .MUL,
   .op .ADD,
   .push 1 96,
   .op .MLOAD]

def prCol7part0Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 : UInt256) (rest : List UInt256) : State :=
  let v0 : UInt256 := MachineState.readWord s.memory 128
  let v1 : UInt256 := x8 * v0
  let v2 : UInt256 := v1 + x0
  let v3 : UInt256 := MachineState.readWord s.memory 96
  {s with pc := UInt256.ofNat 5072, memory := s.memory, stack := v3 :: v2 :: x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: rest}

theorem prCol7part0_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions prCol7part0Program {s with pc := UInt256.ofNat 5062, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: rest} =
      some (prCol7part0Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 rest) := by
  have hc (j : Nat) (hj : j ≤ 33) : rest.length + j < 1024 := by omega
  have hcr : rest.length < 1024 := by omega
  have ha128 : (128 : UInt256).toNat = 128 := rfl
  have hf128 := activeWords_fix s 128 32 (by decide) (by norm_num) hact
  have ha96 : (96 : UInt256).toNat = 96 := rfl
  have hf96 := activeWords_fix s 96 32 (by decide) (by norm_num) hact
  simp [hz, hzn, prCol7part0Program, prCol7part0Model, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, ofNat_sub_ofNat, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, hc, hcr, ha128, hf128, ha96, hf96]

def prCol7part1Program : List Instr :=
  [.op (.Dup ⟨11, by decide⟩),
   .op .MUL,
   .op .ADD,
   .op (.Dup ⟨14, by decide⟩),
   .op (.Dup ⟨3, by decide⟩),
   .op .MUL,
   .op .ADD,
   .op (.Dup ⟨13, by decide⟩)]

def prCol7part1Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 : UInt256) (rest : List UInt256) : State :=
  let v0 : UInt256 := x11 * x0
  let v1 : UInt256 := v0 + x1
  let v2 : UInt256 := x3 * x15
  let v3 : UInt256 := v2 + v1
  {s with pc := UInt256.ofNat 5080, memory := s.memory, stack := x14 :: v3 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: x18 :: rest}

theorem prCol7part1_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions prCol7part1Program {s with pc := UInt256.ofNat 5072, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: x18 :: rest} =
      some (prCol7part1Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 rest) := by
  have hc (j : Nat) (hj : j ≤ 33) : rest.length + j < 1024 := by omega
  have hcr : rest.length < 1024 := by omega
  simp [hz, hzn, prCol7part1Program, prCol7part1Model, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, ofNat_sub_ofNat, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, hc, hcr]

def prCol7part2Program : List Instr :=
  [.op (.Dup ⟨6, by decide⟩),
   .op .MUL,
   .op .ADD,
   .op (.Swap ⟨0, by decide⟩),
   .op (.Dup ⟨15, by decide⟩),
   .push 1 128,
   .op .MLOAD,
   .op (.Dup ⟨11, by decide⟩)]

def prCol7part2Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 : UInt256) (rest : List UInt256) : State :=
  let v0 : UInt256 := x6 * x0
  let v1 : UInt256 := v0 + x1
  let v2 : UInt256 := MachineState.readWord s.memory 128
  {s with pc := UInt256.ofNat 5089, memory := s.memory, stack := x10 :: v2 :: x16 :: x2 :: v1 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: x18 :: rest}

theorem prCol7part2_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions prCol7part2Program {s with pc := UInt256.ofNat 5080, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: x18 :: rest} =
      some (prCol7part2Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 rest) := by
  have hc (j : Nat) (hj : j ≤ 34) : rest.length + j < 1024 := by omega
  have hcr : rest.length < 1024 := by omega
  have ha128 : (128 : UInt256).toNat = 128 := rfl
  have hf128 := activeWords_fix s 128 32 (by decide) (by norm_num) hact
  simp [hz, hzn, prCol7part2Program, prCol7part2Model, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, ofNat_sub_ofNat, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, hc, hcr, ha128, hf128]

def prCol7part3Program : List Instr :=
  [.op .MULMOD,
   .op .ADD,
   .op (.Dup ⟨15, by decide⟩),
   .push 1 96,
   .op .MLOAD,
   .op (.Dup ⟨12, by decide⟩),
   .op .MULMOD,
   .op .ADD]

def prCol7part3Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 : UInt256) (rest : List UInt256) : State :=
  let v0 : UInt256 := UInt256.mulMod x0 x1 x2
  let v1 : UInt256 := v0 + x3
  let v2 : UInt256 := MachineState.readWord s.memory 96
  let v3 : UInt256 := UInt256.mulMod x13 v2 x18
  let v4 : UInt256 := v3 + v1
  {s with pc := UInt256.ofNat 5098, memory := s.memory, stack := v4 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: x18 :: x19 :: x20 :: rest}

theorem prCol7part3_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions prCol7part3Program {s with pc := UInt256.ofNat 5089, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: x18 :: x19 :: x20 :: rest} =
      some (prCol7part3Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 rest) := by
  have hc (j : Nat) (hj : j ≤ 34) : rest.length + j < 1024 := by omega
  have hcr : rest.length < 1024 := by omega
  have ha96 : (96 : UInt256).toNat = 96 := rfl
  have hf96 := activeWords_fix s 96 32 (by decide) (by norm_num) hact
  simp [hz, hzn, prCol7part3Program, prCol7part3Model, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, ofNat_sub_ofNat, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, hc, hcr, ha96, hf96]

def prCol7part4Program : List Instr :=
  [.op (.Dup ⟨15, by decide⟩),
   .op (.Dup ⟨15, by decide⟩),
   .op (.Dup ⟨4, by decide⟩),
   .op .MULMOD,
   .op .ADD,
   .op (.Dup ⟨15, by decide⟩),
   .op (.Dup ⟨14, by decide⟩),
   .op (.Dup ⟨7, by decide⟩)]

def prCol7part4Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 : UInt256) (rest : List UInt256) : State :=
  let v0 : UInt256 := UInt256.mulMod x2 x14 x15
  let v1 : UInt256 := v0 + x0
  {s with pc := UInt256.ofNat 5106, memory := s.memory, stack := x5 :: x13 :: x15 :: v1 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: rest}

theorem prCol7part4_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions prCol7part4Program {s with pc := UInt256.ofNat 5098, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: rest} =
      some (prCol7part4Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 rest) := by
  have hc (j : Nat) (hj : j ≤ 34) : rest.length + j < 1024 := by omega
  have hcr : rest.length < 1024 := by omega
  simp [hz, hzn, prCol7part4Program, prCol7part4Model, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, ofNat_sub_ofNat, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, hc, hcr]

def prCol7part5Program : List Instr :=
  [.op .MULMOD,
   .op .ADD,
   .op (.Dup ⟨15, by decide⟩),
   .op (.Swap ⟨0, by decide⟩),
   .op (.Dup ⟨2, by decide⟩),
   .op .NOT,
   .op .ADDMOD]

def prCol7part5Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 : UInt256) (rest : List UInt256) : State :=
  let v0 : UInt256 := UInt256.mulMod x0 x1 x2
  let v1 : UInt256 := v0 + x3
  let v2 : UInt256 := UInt256.lnot x4
  let v3 : UInt256 := UInt256.addMod v2 v1 x18
  {s with pc := UInt256.ofNat 5113, memory := s.memory, stack := v3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: x18 :: x19 :: x20 :: rest}

theorem prCol7part5_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions prCol7part5Program {s with pc := UInt256.ofNat 5106, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: x18 :: x19 :: x20 :: rest} =
      some (prCol7part5Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 rest) := by
  have hc (j : Nat) (hj : j ≤ 34) : rest.length + j < 1024 := by omega
  have hcr : rest.length < 1024 := by omega
  simp [hz, hzn, prCol7part5Program, prCol7part5Model, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, ofNat_sub_ofNat, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, hc, hcr]

def prCol7part6Program : List Instr :=
  [.push 1 5,
   .op .SHR,
   .op (.Dup ⟨1, by decide⟩),
   .push 1 224,
   .op .MLOAD,
   .op .AND,
   .op (.Swap ⟨8, by decide⟩),
   .op .POP]

def prCol7part6Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 : UInt256) (rest : List UInt256) : State :=
  let v0 : UInt256 := UInt256.shiftRight x0 (UInt256.ofNat 5)
  let v1 : UInt256 := MachineState.readWord s.memory 224
  let v2 : UInt256 := UInt256.land v1 x1
  {s with pc := UInt256.ofNat 5123, memory := s.memory, stack := v0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: v2 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: rest}

theorem prCol7part6_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions prCol7part6Program {s with pc := UInt256.ofNat 5113, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: rest} =
      some (prCol7part6Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 rest) := by
  have hc (j : Nat) (hj : j ≤ 33) : rest.length + j < 1024 := by omega
  have hcr : rest.length < 1024 := by omega
  have ha224 : (224 : UInt256).toNat = 224 := rfl
  have hf224 := activeWords_fix s 224 32 (by decide) (by norm_num) hact
  simp [hz, hzn, prCol7part6Program, prCol7part6Model, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, ofNat_sub_ofNat, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, hc, hcr, ha224, hf224]

def prCol7part7Program : List Instr :=
  [.push 1 16,
   .op .SHL,
   .op (.Swap ⟨0, by decide⟩),
   .push 1 240,
   .op .SHR,
   .op .ADD]

def prCol7part7Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 : UInt256) (rest : List UInt256) : State :=
  let v0 : UInt256 := UInt256.shiftLeft x0 (UInt256.ofNat 16)
  let v1 : UInt256 := UInt256.shiftRight x1 (UInt256.ofNat 240)
  let v2 : UInt256 := v1 + v0
  {s with pc := UInt256.ofNat 5131, memory := s.memory, stack := v2 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: rest}

theorem prCol7part7_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions prCol7part7Program {s with pc := UInt256.ofNat 5123, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: rest} =
      some (prCol7part7Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 rest) := by
  have hc (j : Nat) (hj : j ≤ 32) : rest.length + j < 1024 := by omega
  have hcr : rest.length < 1024 := by omega
  simp [hz, hzn, prCol7part7Program, prCol7part7Model, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, ofNat_sub_ofNat, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, hc, hcr]

def prCol7Program : List Instr :=
  [.op (.Dup ⟨0, by decide⟩),
   .push 1 128,
   .op .MLOAD,
   .op (.Dup ⟨10, by decide⟩),
   .op .MUL,
   .op .ADD,
   .push 1 96,
   .op .MLOAD,
   .op (.Dup ⟨11, by decide⟩),
   .op .MUL,
   .op .ADD,
   .op (.Dup ⟨14, by decide⟩),
   .op (.Dup ⟨3, by decide⟩),
   .op .MUL,
   .op .ADD,
   .op (.Dup ⟨13, by decide⟩),
   .op (.Dup ⟨6, by decide⟩),
   .op .MUL,
   .op .ADD,
   .op (.Swap ⟨0, by decide⟩),
   .op (.Dup ⟨15, by decide⟩),
   .push 1 128,
   .op .MLOAD,
   .op (.Dup ⟨11, by decide⟩),
   .op .MULMOD,
   .op .ADD,
   .op (.Dup ⟨15, by decide⟩),
   .push 1 96,
   .op .MLOAD,
   .op (.Dup ⟨12, by decide⟩),
   .op .MULMOD,
   .op .ADD,
   .op (.Dup ⟨15, by decide⟩),
   .op (.Dup ⟨15, by decide⟩),
   .op (.Dup ⟨4, by decide⟩),
   .op .MULMOD,
   .op .ADD,
   .op (.Dup ⟨15, by decide⟩),
   .op (.Dup ⟨14, by decide⟩),
   .op (.Dup ⟨7, by decide⟩),
   .op .MULMOD,
   .op .ADD,
   .op (.Dup ⟨15, by decide⟩),
   .op (.Swap ⟨0, by decide⟩),
   .op (.Dup ⟨2, by decide⟩),
   .op .NOT,
   .op .ADDMOD,
   .push 1 5,
   .op .SHR,
   .op (.Dup ⟨1, by decide⟩),
   .push 1 224,
   .op .MLOAD,
   .op .AND,
   .op (.Swap ⟨8, by decide⟩),
   .op .POP,
   .push 1 16,
   .op .SHL,
   .op (.Swap ⟨0, by decide⟩),
   .push 1 240,
   .op .SHR,
   .op .ADD]

def prCol7Model (s : State) (c q3 q2 q1 q4 z0 z1 x2 x3 x4 n1 n2 n3 n4 P inv cntp : UInt256) (rest : List UInt256) : State :=
  let v0 : UInt256 := MachineState.readWord s.memory 128
  let v1 : UInt256 := x3 * v0
  let v2 : UInt256 := v1 + c
  let v3 : UInt256 := MachineState.readWord s.memory 96
  let v4 : UInt256 := x4 * v3
  let v5 : UInt256 := v4 + v2
  let v6 : UInt256 := q3 * n4
  let v7 : UInt256 := v6 + v5
  let v8 : UInt256 := q4 * n3
  let v9 : UInt256 := v8 + v7
  let v10 : UInt256 := MachineState.readWord s.memory 128
  let v11 : UInt256 := UInt256.mulMod x3 v10 P
  let v12 : UInt256 := v11 + c
  let v13 : UInt256 := MachineState.readWord s.memory 96
  let v14 : UInt256 := UInt256.mulMod x4 v13 P
  let v15 : UInt256 := v14 + v12
  let v16 : UInt256 := UInt256.mulMod q3 n4 P
  let v17 : UInt256 := v16 + v15
  let v18 : UInt256 := UInt256.mulMod q4 n3 P
  let v19 : UInt256 := v18 + v17
  let v20 : UInt256 := UInt256.lnot v9
  let v21 : UInt256 := UInt256.addMod v20 v19 P
  let v22 : UInt256 := UInt256.shiftRight v21 (UInt256.ofNat 5)
  let v23 : UInt256 := MachineState.readWord s.memory 224
  let v24 : UInt256 := UInt256.land v23 v9
  let v25 : UInt256 := UInt256.shiftLeft v22 (UInt256.ofNat 16)
  let v26 : UInt256 := UInt256.shiftRight v9 (UInt256.ofNat 240)
  let v27 : UInt256 := v26 + v25
  {s with pc := UInt256.ofNat 5131, memory := s.memory, stack := v27 :: q3 :: q2 :: q1 :: q4 :: z0 :: z1 :: v24 :: x3 :: x4 :: n1 :: n2 :: n3 :: n4 :: P :: inv :: cntp :: rest}

theorem prCol7_run (s : State) (c q3 q2 q1 q4 z0 z1 x2 x3 x4 n1 n2 n3 n4 P inv cntp : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions prCol7Program {s with pc := UInt256.ofNat 5062, stack := c :: q3 :: q2 :: q1 :: q4 :: z0 :: z1 :: x2 :: x3 :: x4 :: n1 :: n2 :: n3 :: n4 :: P :: inv :: cntp :: rest} =
      some (prCol7Model s c q3 q2 q1 q4 z0 z1 x2 x3 x4 n1 n2 n3 n4 P inv cntp rest) := by
  let v0 : UInt256 := MachineState.readWord s.memory 128
  let v1 : UInt256 := x3 * v0
  let v2 : UInt256 := v1 + c
  let v3 : UInt256 := MachineState.readWord s.memory 96
  let v4 : UInt256 := x4 * v3
  let v5 : UInt256 := v4 + v2
  let v6 : UInt256 := q3 * n4
  let v7 : UInt256 := v6 + v5
  let v8 : UInt256 := q4 * n3
  let v9 : UInt256 := v8 + v7
  let v10 : UInt256 := MachineState.readWord s.memory 128
  let v11 : UInt256 := UInt256.mulMod x3 v10 P
  let v12 : UInt256 := v11 + c
  let v13 : UInt256 := MachineState.readWord s.memory 96
  let v14 : UInt256 := UInt256.mulMod x4 v13 P
  let v15 : UInt256 := v14 + v12
  let v16 : UInt256 := UInt256.mulMod q3 n4 P
  let v17 : UInt256 := v16 + v15
  let v18 : UInt256 := UInt256.mulMod q4 n3 P
  let v19 : UInt256 := v18 + v17
  let v20 : UInt256 := UInt256.lnot v9
  let v21 : UInt256 := UInt256.addMod v20 v19 P
  let v22 : UInt256 := UInt256.shiftRight v21 (UInt256.ofNat 5)
  let v23 : UInt256 := MachineState.readWord s.memory 224
  let v24 : UInt256 := UInt256.land v23 v9
  let v25 : UInt256 := UInt256.shiftLeft v22 (UInt256.ofNat 16)
  let v26 : UInt256 := UInt256.shiftRight v9 (UInt256.ofNat 240)
  let v27 : UInt256 := v26 + v25
  have h0 : runInstructions prCol7part0Program {s with pc := UInt256.ofNat 5062, memory := s.memory, stack := c :: q3 :: q2 :: q1 :: q4 :: z0 :: z1 :: x2 :: x3 :: x4 :: n1 :: n2 :: n3 :: n4 :: P :: inv :: cntp :: rest} = some {s with pc := UInt256.ofNat 5072, memory := s.memory, stack := v3 :: v2 :: c :: q3 :: q2 :: q1 :: q4 :: z0 :: z1 :: x2 :: x3 :: x4 :: n1 :: n2 :: n3 :: n4 :: P :: inv :: cntp :: rest} := by
    simpa only [prCol7part0Model, v0, v1, v2, v3] using prCol7part0_run (s) c q3 q2 q1 q4 z0 z1 x2 x3 x4 n1 n2 n3 n4 P inv cntp rest hcap hact
  have h1 : runInstructions prCol7part1Program {s with pc := UInt256.ofNat 5072, memory := s.memory, stack := v3 :: v2 :: c :: q3 :: q2 :: q1 :: q4 :: z0 :: z1 :: x2 :: x3 :: x4 :: n1 :: n2 :: n3 :: n4 :: P :: inv :: cntp :: rest} = some {s with pc := UInt256.ofNat 5080, memory := s.memory, stack := n3 :: v7 :: c :: q3 :: q2 :: q1 :: q4 :: z0 :: z1 :: x2 :: x3 :: x4 :: n1 :: n2 :: n3 :: n4 :: P :: inv :: cntp :: rest} := by
    simpa only [prCol7part1Model, v4, v5, v6, v7] using prCol7part1_run (s) v3 v2 c q3 q2 q1 q4 z0 z1 x2 x3 x4 n1 n2 n3 n4 P inv cntp rest hcap hact
  have h2 : runInstructions prCol7part2Program {s with pc := UInt256.ofNat 5080, memory := s.memory, stack := n3 :: v7 :: c :: q3 :: q2 :: q1 :: q4 :: z0 :: z1 :: x2 :: x3 :: x4 :: n1 :: n2 :: n3 :: n4 :: P :: inv :: cntp :: rest} = some {s with pc := UInt256.ofNat 5089, memory := s.memory, stack := x3 :: v10 :: P :: c :: v9 :: q3 :: q2 :: q1 :: q4 :: z0 :: z1 :: x2 :: x3 :: x4 :: n1 :: n2 :: n3 :: n4 :: P :: inv :: cntp :: rest} := by
    simpa only [prCol7part2Model, v8, v9, v10] using prCol7part2_run (s) n3 v7 c q3 q2 q1 q4 z0 z1 x2 x3 x4 n1 n2 n3 n4 P inv cntp rest hcap hact
  have h3 : runInstructions prCol7part3Program {s with pc := UInt256.ofNat 5089, memory := s.memory, stack := x3 :: v10 :: P :: c :: v9 :: q3 :: q2 :: q1 :: q4 :: z0 :: z1 :: x2 :: x3 :: x4 :: n1 :: n2 :: n3 :: n4 :: P :: inv :: cntp :: rest} = some {s with pc := UInt256.ofNat 5098, memory := s.memory, stack := v15 :: v9 :: q3 :: q2 :: q1 :: q4 :: z0 :: z1 :: x2 :: x3 :: x4 :: n1 :: n2 :: n3 :: n4 :: P :: inv :: cntp :: rest} := by
    simpa only [prCol7part3Model, v11, v12, v13, v14, v15] using prCol7part3_run (s) x3 v10 P c v9 q3 q2 q1 q4 z0 z1 x2 x3 x4 n1 n2 n3 n4 P inv cntp rest hcap hact
  have h4 : runInstructions prCol7part4Program {s with pc := UInt256.ofNat 5098, memory := s.memory, stack := v15 :: v9 :: q3 :: q2 :: q1 :: q4 :: z0 :: z1 :: x2 :: x3 :: x4 :: n1 :: n2 :: n3 :: n4 :: P :: inv :: cntp :: rest} = some {s with pc := UInt256.ofNat 5106, memory := s.memory, stack := q4 :: n3 :: P :: v17 :: v9 :: q3 :: q2 :: q1 :: q4 :: z0 :: z1 :: x2 :: x3 :: x4 :: n1 :: n2 :: n3 :: n4 :: P :: inv :: cntp :: rest} := by
    simpa only [prCol7part4Model, v16, v17] using prCol7part4_run (s) v15 v9 q3 q2 q1 q4 z0 z1 x2 x3 x4 n1 n2 n3 n4 P inv cntp rest hcap hact
  have h5 : runInstructions prCol7part5Program {s with pc := UInt256.ofNat 5106, memory := s.memory, stack := q4 :: n3 :: P :: v17 :: v9 :: q3 :: q2 :: q1 :: q4 :: z0 :: z1 :: x2 :: x3 :: x4 :: n1 :: n2 :: n3 :: n4 :: P :: inv :: cntp :: rest} = some {s with pc := UInt256.ofNat 5113, memory := s.memory, stack := v21 :: v9 :: q3 :: q2 :: q1 :: q4 :: z0 :: z1 :: x2 :: x3 :: x4 :: n1 :: n2 :: n3 :: n4 :: P :: inv :: cntp :: rest} := by
    simpa only [prCol7part5Model, v18, v19, v20, v21] using prCol7part5_run (s) q4 n3 P v17 v9 q3 q2 q1 q4 z0 z1 x2 x3 x4 n1 n2 n3 n4 P inv cntp rest hcap hact
  have h6 : runInstructions prCol7part6Program {s with pc := UInt256.ofNat 5113, memory := s.memory, stack := v21 :: v9 :: q3 :: q2 :: q1 :: q4 :: z0 :: z1 :: x2 :: x3 :: x4 :: n1 :: n2 :: n3 :: n4 :: P :: inv :: cntp :: rest} = some {s with pc := UInt256.ofNat 5123, memory := s.memory, stack := v22 :: v9 :: q3 :: q2 :: q1 :: q4 :: z0 :: z1 :: v24 :: x3 :: x4 :: n1 :: n2 :: n3 :: n4 :: P :: inv :: cntp :: rest} := by
    simpa only [prCol7part6Model, v22, v23, v24] using prCol7part6_run (s) v21 v9 q3 q2 q1 q4 z0 z1 x2 x3 x4 n1 n2 n3 n4 P inv cntp rest hcap hact
  have h7 : runInstructions prCol7part7Program {s with pc := UInt256.ofNat 5123, memory := s.memory, stack := v22 :: v9 :: q3 :: q2 :: q1 :: q4 :: z0 :: z1 :: v24 :: x3 :: x4 :: n1 :: n2 :: n3 :: n4 :: P :: inv :: cntp :: rest} = some {s with pc := UInt256.ofNat 5131, memory := s.memory, stack := v27 :: q3 :: q2 :: q1 :: q4 :: z0 :: z1 :: v24 :: x3 :: x4 :: n1 :: n2 :: n3 :: n4 :: P :: inv :: cntp :: rest} := by
    simpa only [prCol7part7Model, v25, v26, v27] using prCol7part7_run (s) v22 v9 q3 q2 q1 q4 z0 z1 v24 x3 x4 n1 n2 n3 n4 P inv cntp rest hcap hact
  exact (runInstructions_append_some _ _ _ _ _ h0 (runInstructions_append_some _ _ _ _ _ h1 (runInstructions_append_some _ _ _ _ _ h2 (runInstructions_append_some _ _ _ _ _ h3 (runInstructions_append_some _ _ _ _ _ h4 (runInstructions_append_some _ _ _ _ _ h5 (runInstructions_append_some _ _ _ _ _ h6 h7)))))))

def prCol7_o0 (c q3 q2 q1 q4 z0 z1 x2 x3 x4 n1 n2 n3 n4 P inv cntp b3 b4 M : UInt256) : UInt256 :=
  ((UInt256.shiftRight ((q4 * n3) + ((q3 * n4) + ((x4 * b3) + ((x3 * b4) + c)))) (UInt256.ofNat 240)) + (UInt256.shiftLeft (UInt256.shiftRight (UInt256.addMod (UInt256.lnot ((q4 * n3) + ((q3 * n4) + ((x4 * b3) + ((x3 * b4) + c))))) ((UInt256.mulMod q4 n3 P) + ((UInt256.mulMod q3 n4 P) + ((UInt256.mulMod x4 b3 P) + ((UInt256.mulMod x3 b4 P) + c)))) P) (UInt256.ofNat 5)) (UInt256.ofNat 16)))

def prCol7_o7 (c q3 q2 q1 q4 z0 z1 x2 x3 x4 n1 n2 n3 n4 P inv cntp b3 b4 M : UInt256) : UInt256 :=
  (UInt256.land M ((q4 * n3) + ((q3 * n4) + ((x4 * b3) + ((x3 * b4) + c)))))

theorem prCol7_eq (s : State) (c q3 q2 q1 q4 z0 z1 x2 x3 x4 n1 n2 n3 n4 P inv cntp b3 b4 M : UInt256) (rest : List UInt256)
    (h_b3 : MachineState.readWord s.memory 96 = b3)
    (h_b4 : MachineState.readWord s.memory 128 = b4)
    (h_M : MachineState.readWord s.memory 224 = M) :
    prCol7Model s c q3 q2 q1 q4 z0 z1 x2 x3 x4 n1 n2 n3 n4 P inv cntp rest =
      {s with pc := UInt256.ofNat 5131, stack := (prCol7_o0 c q3 q2 q1 q4 z0 z1 x2 x3 x4 n1 n2 n3 n4 P inv cntp b3 b4 M) :: q3 :: q2 :: q1 :: q4 :: z0 :: z1 :: (prCol7_o7 c q3 q2 q1 q4 z0 z1 x2 x3 x4 n1 n2 n3 n4 P inv cntp b3 b4 M) :: x3 :: x4 :: n1 :: n2 :: n3 :: n4 :: P :: inv :: cntp :: rest} := by
  simp only [prCol7Model, prCol7_o0, prCol7_o7, h_b3, h_b4, h_M]

/-! ## prCol8: pc 5131..5178, 41 instructions -/

def prCol8part0Program : List Instr :=
  [.op (.Dup ⟨0, by decide⟩),
   .push 1 128,
   .op .MLOAD,
   .op (.Dup ⟨11, by decide⟩),
   .op .MUL,
   .op .ADD,
   .op (.Dup ⟨14, by decide⟩),
   .op (.Dup ⟨6, by decide⟩)]

def prCol8part0Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 : UInt256) (rest : List UInt256) : State :=
  let v0 : UInt256 := MachineState.readWord s.memory 128
  let v1 : UInt256 := x9 * v0
  let v2 : UInt256 := v1 + x0
  {s with pc := UInt256.ofNat 5140, memory := s.memory, stack := x4 :: x13 :: v2 :: x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: rest}

theorem prCol8part0_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions prCol8part0Program {s with pc := UInt256.ofNat 5131, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: rest} =
      some (prCol8part0Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 rest) := by
  have hc (j : Nat) (hj : j ≤ 33) : rest.length + j < 1024 := by omega
  have hcr : rest.length < 1024 := by omega
  have ha128 : (128 : UInt256).toNat = 128 := rfl
  have hf128 := activeWords_fix s 128 32 (by decide) (by norm_num) hact
  simp [hz, hzn, prCol8part0Program, prCol8part0Model, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, ofNat_sub_ofNat, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, hc, hcr, ha128, hf128]

def prCol8part1Program : List Instr :=
  [.op .MUL,
   .op .ADD,
   .op (.Swap ⟨0, by decide⟩),
   .op (.Dup ⟨15, by decide⟩),
   .push 1 128,
   .op .MLOAD,
   .op (.Dup ⟨12, by decide⟩),
   .op .MULMOD]

def prCol8part1Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 : UInt256) (rest : List UInt256) : State :=
  let v0 : UInt256 := x0 * x1
  let v1 : UInt256 := v0 + x2
  let v2 : UInt256 := MachineState.readWord s.memory 128
  let v3 : UInt256 := UInt256.mulMod x12 v2 x17
  {s with pc := UInt256.ofNat 5149, memory := s.memory, stack := v3 :: x3 :: v1 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: x18 :: x19 :: rest}

theorem prCol8part1_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions prCol8part1Program {s with pc := UInt256.ofNat 5140, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: x18 :: x19 :: rest} =
      some (prCol8part1Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 rest) := by
  have hc (j : Nat) (hj : j ≤ 34) : rest.length + j < 1024 := by omega
  have hcr : rest.length < 1024 := by omega
  have ha128 : (128 : UInt256).toNat = 128 := rfl
  have hf128 := activeWords_fix s 128 32 (by decide) (by norm_num) hact
  simp [hz, hzn, prCol8part1Program, prCol8part1Model, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, ofNat_sub_ofNat, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, hc, hcr, ha128, hf128]

def prCol8part2Program : List Instr :=
  [.op .ADD,
   .op (.Dup ⟨15, by decide⟩),
   .op (.Dup ⟨15, by decide⟩),
   .op (.Dup ⟨7, by decide⟩),
   .op .MULMOD,
   .op .ADD,
   .op (.Dup ⟨15, by decide⟩),
   .op (.Swap ⟨0, by decide⟩)]

def prCol8part2Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 : UInt256) (rest : List UInt256) : State :=
  let v0 : UInt256 := x0 + x1
  let v1 : UInt256 := UInt256.mulMod x6 x15 x16
  let v2 : UInt256 := v1 + v0
  {s with pc := UInt256.ofNat 5157, memory := s.memory, stack := v2 :: x16 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: x18 :: rest}

theorem prCol8part2_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions prCol8part2Program {s with pc := UInt256.ofNat 5149, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: x18 :: rest} =
      some (prCol8part2Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 rest) := by
  have hc (j : Nat) (hj : j ≤ 34) : rest.length + j < 1024 := by omega
  have hcr : rest.length < 1024 := by omega
  simp [hz, hzn, prCol8part2Program, prCol8part2Model, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, ofNat_sub_ofNat, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, hc, hcr]

def prCol8part3Program : List Instr :=
  [.op (.Dup ⟨2, by decide⟩),
   .op .NOT,
   .op .ADDMOD,
   .push 1 5,
   .op .SHR,
   .op (.Dup ⟨1, by decide⟩),
   .push 1 224,
   .op .MLOAD]

def prCol8part3Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 : UInt256) (rest : List UInt256) : State :=
  let v0 : UInt256 := UInt256.lnot x2
  let v1 : UInt256 := UInt256.addMod v0 x0 x1
  let v2 : UInt256 := UInt256.shiftRight v1 (UInt256.ofNat 5)
  let v3 : UInt256 := MachineState.readWord s.memory 224
  {s with pc := UInt256.ofNat 5167, memory := s.memory, stack := v3 :: x2 :: v2 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: x18 :: rest}

theorem prCol8part3_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions prCol8part3Program {s with pc := UInt256.ofNat 5157, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: x18 :: rest} =
      some (prCol8part3Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 rest) := by
  have hc (j : Nat) (hj : j ≤ 33) : rest.length + j < 1024 := by omega
  have hcr : rest.length < 1024 := by omega
  have ha224 : (224 : UInt256).toNat = 224 := rfl
  have hf224 := activeWords_fix s 224 32 (by decide) (by norm_num) hact
  simp [hz, hzn, prCol8part3Program, prCol8part3Model, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, ofNat_sub_ofNat, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, hc, hcr, ha224, hf224]

def prCol8part4Program : List Instr :=
  [.op .AND,
   .op (.Swap ⟨9, by decide⟩),
   .op .POP,
   .push 1 16,
   .op .SHL,
   .op (.Swap ⟨0, by decide⟩),
   .push 1 240,
   .op .SHR]

def prCol8part4Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 : UInt256) (rest : List UInt256) : State :=
  let v0 : UInt256 := UInt256.land x0 x1
  let v1 : UInt256 := UInt256.shiftLeft x2 (UInt256.ofNat 16)
  let v2 : UInt256 := UInt256.shiftRight x3 (UInt256.ofNat 240)
  {s with pc := UInt256.ofNat 5177, memory := s.memory, stack := v2 :: v1 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: v0 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: x18 :: x19 :: rest}

theorem prCol8part4_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions prCol8part4Program {s with pc := UInt256.ofNat 5167, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: x18 :: x19 :: rest} =
      some (prCol8part4Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 rest) := by
  have hc (j : Nat) (hj : j ≤ 33) : rest.length + j < 1024 := by omega
  have hcr : rest.length < 1024 := by omega
  simp [hz, hzn, prCol8part4Program, prCol8part4Model, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, ofNat_sub_ofNat, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, hc, hcr]

def prCol8part5Program : List Instr :=
  [.op .ADD]

def prCol8part5Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 : UInt256) (rest : List UInt256) : State :=
  let v0 : UInt256 := x0 + x1
  {s with pc := UInt256.ofNat 5178, memory := s.memory, stack := v0 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: rest}

theorem prCol8part5_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions prCol8part5Program {s with pc := UInt256.ofNat 5177, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: rest} =
      some (prCol8part5Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 rest) := by
  have hc (j : Nat) (hj : j ≤ 31) : rest.length + j < 1024 := by omega
  have hcr : rest.length < 1024 := by omega
  simp [hz, hzn, prCol8part5Program, prCol8part5Model, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, ofNat_sub_ofNat, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, hc, hcr]

def prCol8Program : List Instr :=
  [.op (.Dup ⟨0, by decide⟩),
   .push 1 128,
   .op .MLOAD,
   .op (.Dup ⟨11, by decide⟩),
   .op .MUL,
   .op .ADD,
   .op (.Dup ⟨14, by decide⟩),
   .op (.Dup ⟨6, by decide⟩),
   .op .MUL,
   .op .ADD,
   .op (.Swap ⟨0, by decide⟩),
   .op (.Dup ⟨15, by decide⟩),
   .push 1 128,
   .op .MLOAD,
   .op (.Dup ⟨12, by decide⟩),
   .op .MULMOD,
   .op .ADD,
   .op (.Dup ⟨15, by decide⟩),
   .op (.Dup ⟨15, by decide⟩),
   .op (.Dup ⟨7, by decide⟩),
   .op .MULMOD,
   .op .ADD,
   .op (.Dup ⟨15, by decide⟩),
   .op (.Swap ⟨0, by decide⟩),
   .op (.Dup ⟨2, by decide⟩),
   .op .NOT,
   .op .ADDMOD,
   .push 1 5,
   .op .SHR,
   .op (.Dup ⟨1, by decide⟩),
   .push 1 224,
   .op .MLOAD,
   .op .AND,
   .op (.Swap ⟨9, by decide⟩),
   .op .POP,
   .push 1 16,
   .op .SHL,
   .op (.Swap ⟨0, by decide⟩),
   .push 1 240,
   .op .SHR,
   .op .ADD]

def prCol8Model (s : State) (c q3 q2 q1 q4 z0 z1 z2 x3 x4 n1 n2 n3 n4 P inv cntp : UInt256) (rest : List UInt256) : State :=
  let v0 : UInt256 := MachineState.readWord s.memory 128
  let v1 : UInt256 := x4 * v0
  let v2 : UInt256 := v1 + c
  let v3 : UInt256 := q4 * n4
  let v4 : UInt256 := v3 + v2
  let v5 : UInt256 := MachineState.readWord s.memory 128
  let v6 : UInt256 := UInt256.mulMod x4 v5 P
  let v7 : UInt256 := v6 + c
  let v8 : UInt256 := UInt256.mulMod q4 n4 P
  let v9 : UInt256 := v8 + v7
  let v10 : UInt256 := UInt256.lnot v4
  let v11 : UInt256 := UInt256.addMod v10 v9 P
  let v12 : UInt256 := UInt256.shiftRight v11 (UInt256.ofNat 5)
  let v13 : UInt256 := MachineState.readWord s.memory 224
  let v14 : UInt256 := UInt256.land v13 v4
  let v15 : UInt256 := UInt256.shiftLeft v12 (UInt256.ofNat 16)
  let v16 : UInt256 := UInt256.shiftRight v4 (UInt256.ofNat 240)
  let v17 : UInt256 := v16 + v15
  {s with pc := UInt256.ofNat 5178, memory := s.memory, stack := v17 :: q3 :: q2 :: q1 :: q4 :: z0 :: z1 :: z2 :: v14 :: x4 :: n1 :: n2 :: n3 :: n4 :: P :: inv :: cntp :: rest}

theorem prCol8_run (s : State) (c q3 q2 q1 q4 z0 z1 z2 x3 x4 n1 n2 n3 n4 P inv cntp : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions prCol8Program {s with pc := UInt256.ofNat 5131, stack := c :: q3 :: q2 :: q1 :: q4 :: z0 :: z1 :: z2 :: x3 :: x4 :: n1 :: n2 :: n3 :: n4 :: P :: inv :: cntp :: rest} =
      some (prCol8Model s c q3 q2 q1 q4 z0 z1 z2 x3 x4 n1 n2 n3 n4 P inv cntp rest) := by
  let v0 : UInt256 := MachineState.readWord s.memory 128
  let v1 : UInt256 := x4 * v0
  let v2 : UInt256 := v1 + c
  let v3 : UInt256 := q4 * n4
  let v4 : UInt256 := v3 + v2
  let v5 : UInt256 := MachineState.readWord s.memory 128
  let v6 : UInt256 := UInt256.mulMod x4 v5 P
  let v7 : UInt256 := v6 + c
  let v8 : UInt256 := UInt256.mulMod q4 n4 P
  let v9 : UInt256 := v8 + v7
  let v10 : UInt256 := UInt256.lnot v4
  let v11 : UInt256 := UInt256.addMod v10 v9 P
  let v12 : UInt256 := UInt256.shiftRight v11 (UInt256.ofNat 5)
  let v13 : UInt256 := MachineState.readWord s.memory 224
  let v14 : UInt256 := UInt256.land v13 v4
  let v15 : UInt256 := UInt256.shiftLeft v12 (UInt256.ofNat 16)
  let v16 : UInt256 := UInt256.shiftRight v4 (UInt256.ofNat 240)
  let v17 : UInt256 := v16 + v15
  have h0 : runInstructions prCol8part0Program {s with pc := UInt256.ofNat 5131, memory := s.memory, stack := c :: q3 :: q2 :: q1 :: q4 :: z0 :: z1 :: z2 :: x3 :: x4 :: n1 :: n2 :: n3 :: n4 :: P :: inv :: cntp :: rest} = some {s with pc := UInt256.ofNat 5140, memory := s.memory, stack := q4 :: n4 :: v2 :: c :: q3 :: q2 :: q1 :: q4 :: z0 :: z1 :: z2 :: x3 :: x4 :: n1 :: n2 :: n3 :: n4 :: P :: inv :: cntp :: rest} := by
    simpa only [prCol8part0Model, v0, v1, v2] using prCol8part0_run (s) c q3 q2 q1 q4 z0 z1 z2 x3 x4 n1 n2 n3 n4 P inv cntp rest hcap hact
  have h1 : runInstructions prCol8part1Program {s with pc := UInt256.ofNat 5140, memory := s.memory, stack := q4 :: n4 :: v2 :: c :: q3 :: q2 :: q1 :: q4 :: z0 :: z1 :: z2 :: x3 :: x4 :: n1 :: n2 :: n3 :: n4 :: P :: inv :: cntp :: rest} = some {s with pc := UInt256.ofNat 5149, memory := s.memory, stack := v6 :: c :: v4 :: q3 :: q2 :: q1 :: q4 :: z0 :: z1 :: z2 :: x3 :: x4 :: n1 :: n2 :: n3 :: n4 :: P :: inv :: cntp :: rest} := by
    simpa only [prCol8part1Model, v3, v4, v5, v6] using prCol8part1_run (s) q4 n4 v2 c q3 q2 q1 q4 z0 z1 z2 x3 x4 n1 n2 n3 n4 P inv cntp rest hcap hact
  have h2 : runInstructions prCol8part2Program {s with pc := UInt256.ofNat 5149, memory := s.memory, stack := v6 :: c :: v4 :: q3 :: q2 :: q1 :: q4 :: z0 :: z1 :: z2 :: x3 :: x4 :: n1 :: n2 :: n3 :: n4 :: P :: inv :: cntp :: rest} = some {s with pc := UInt256.ofNat 5157, memory := s.memory, stack := v9 :: P :: v4 :: q3 :: q2 :: q1 :: q4 :: z0 :: z1 :: z2 :: x3 :: x4 :: n1 :: n2 :: n3 :: n4 :: P :: inv :: cntp :: rest} := by
    simpa only [prCol8part2Model, v7, v8, v9] using prCol8part2_run (s) v6 c v4 q3 q2 q1 q4 z0 z1 z2 x3 x4 n1 n2 n3 n4 P inv cntp rest hcap hact
  have h3 : runInstructions prCol8part3Program {s with pc := UInt256.ofNat 5157, memory := s.memory, stack := v9 :: P :: v4 :: q3 :: q2 :: q1 :: q4 :: z0 :: z1 :: z2 :: x3 :: x4 :: n1 :: n2 :: n3 :: n4 :: P :: inv :: cntp :: rest} = some {s with pc := UInt256.ofNat 5167, memory := s.memory, stack := v13 :: v4 :: v12 :: v4 :: q3 :: q2 :: q1 :: q4 :: z0 :: z1 :: z2 :: x3 :: x4 :: n1 :: n2 :: n3 :: n4 :: P :: inv :: cntp :: rest} := by
    simpa only [prCol8part3Model, v10, v11, v12, v13] using prCol8part3_run (s) v9 P v4 q3 q2 q1 q4 z0 z1 z2 x3 x4 n1 n2 n3 n4 P inv cntp rest hcap hact
  have h4 : runInstructions prCol8part4Program {s with pc := UInt256.ofNat 5167, memory := s.memory, stack := v13 :: v4 :: v12 :: v4 :: q3 :: q2 :: q1 :: q4 :: z0 :: z1 :: z2 :: x3 :: x4 :: n1 :: n2 :: n3 :: n4 :: P :: inv :: cntp :: rest} = some {s with pc := UInt256.ofNat 5177, memory := s.memory, stack := v16 :: v15 :: q3 :: q2 :: q1 :: q4 :: z0 :: z1 :: z2 :: v14 :: x4 :: n1 :: n2 :: n3 :: n4 :: P :: inv :: cntp :: rest} := by
    simpa only [prCol8part4Model, v14, v15, v16] using prCol8part4_run (s) v13 v4 v12 v4 q3 q2 q1 q4 z0 z1 z2 x3 x4 n1 n2 n3 n4 P inv cntp rest hcap hact
  have h5 : runInstructions prCol8part5Program {s with pc := UInt256.ofNat 5177, memory := s.memory, stack := v16 :: v15 :: q3 :: q2 :: q1 :: q4 :: z0 :: z1 :: z2 :: v14 :: x4 :: n1 :: n2 :: n3 :: n4 :: P :: inv :: cntp :: rest} = some {s with pc := UInt256.ofNat 5178, memory := s.memory, stack := v17 :: q3 :: q2 :: q1 :: q4 :: z0 :: z1 :: z2 :: v14 :: x4 :: n1 :: n2 :: n3 :: n4 :: P :: inv :: cntp :: rest} := by
    simpa only [prCol8part5Model, v17] using prCol8part5_run (s) v16 v15 q3 q2 q1 q4 z0 z1 z2 v14 x4 n1 n2 n3 n4 P inv cntp rest hcap hact
  exact (runInstructions_append_some _ _ _ _ _ h0 (runInstructions_append_some _ _ _ _ _ h1 (runInstructions_append_some _ _ _ _ _ h2 (runInstructions_append_some _ _ _ _ _ h3 (runInstructions_append_some _ _ _ _ _ h4 h5)))))

def prCol8_o0 (c q3 q2 q1 q4 z0 z1 z2 x3 x4 n1 n2 n3 n4 P inv cntp b4 M : UInt256) : UInt256 :=
  ((UInt256.shiftRight ((q4 * n4) + ((x4 * b4) + c)) (UInt256.ofNat 240)) + (UInt256.shiftLeft (UInt256.shiftRight (UInt256.addMod (UInt256.lnot ((q4 * n4) + ((x4 * b4) + c))) ((UInt256.mulMod q4 n4 P) + ((UInt256.mulMod x4 b4 P) + c)) P) (UInt256.ofNat 5)) (UInt256.ofNat 16)))

def prCol8_o8 (c q3 q2 q1 q4 z0 z1 z2 x3 x4 n1 n2 n3 n4 P inv cntp b4 M : UInt256) : UInt256 :=
  (UInt256.land M ((q4 * n4) + ((x4 * b4) + c)))

theorem prCol8_eq (s : State) (c q3 q2 q1 q4 z0 z1 z2 x3 x4 n1 n2 n3 n4 P inv cntp b4 M : UInt256) (rest : List UInt256)
    (h_b4 : MachineState.readWord s.memory 128 = b4)
    (h_M : MachineState.readWord s.memory 224 = M) :
    prCol8Model s c q3 q2 q1 q4 z0 z1 z2 x3 x4 n1 n2 n3 n4 P inv cntp rest =
      {s with pc := UInt256.ofNat 5178, stack := (prCol8_o0 c q3 q2 q1 q4 z0 z1 z2 x3 x4 n1 n2 n3 n4 P inv cntp b4 M) :: q3 :: q2 :: q1 :: q4 :: z0 :: z1 :: z2 :: (prCol8_o8 c q3 q2 q1 q4 z0 z1 z2 x3 x4 n1 n2 n3 n4 P inv cntp b4 M) :: x4 :: n1 :: n2 :: n3 :: n4 :: P :: inv :: cntp :: rest} := by
  simp only [prCol8Model, prCol8_o0, prCol8_o8, h_b4, h_M]

/-! ## prTail: pc 5178..5184, 6 instructions -/

def prTailpart0Program : List Instr :=
  [.op (.Swap ⟨8, by decide⟩),
   .op .POP,
   .op .POP,
   .op .POP,
   .op .POP,
   .op .POP]

def prTailpart0Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 : UInt256) (rest : List UInt256) : State :=
  {s with pc := UInt256.ofNat 5184, memory := s.memory, stack := x5 :: x6 :: x7 :: x8 :: x0 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: rest}

theorem prTailpart0_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions prTailpart0Program {s with pc := UInt256.ofNat 5178, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: rest} =
      some (prTailpart0Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 rest) := by
  have hc (j : Nat) (hj : j ≤ 30) : rest.length + j < 1024 := by omega
  have hcr : rest.length < 1024 := by omega
  simp [hz, hzn, prTailpart0Program, prTailpart0Model, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, ofNat_sub_ofNat, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, hc, hcr]

def prTailProgram : List Instr :=
  [.op (.Swap ⟨8, by decide⟩),
   .op .POP,
   .op .POP,
   .op .POP,
   .op .POP,
   .op .POP]

def prTailModel (s : State) (c q3 q2 q1 q4 z0 z1 z2 z3 x4 n1 n2 n3 n4 P inv cntp : UInt256) (rest : List UInt256) : State :=
  {s with pc := UInt256.ofNat 5184, memory := s.memory, stack := z0 :: z1 :: z2 :: z3 :: c :: n1 :: n2 :: n3 :: n4 :: P :: inv :: cntp :: rest}

theorem prTail_run (s : State) (c q3 q2 q1 q4 z0 z1 z2 z3 x4 n1 n2 n3 n4 P inv cntp : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions prTailProgram {s with pc := UInt256.ofNat 5178, stack := c :: q3 :: q2 :: q1 :: q4 :: z0 :: z1 :: z2 :: z3 :: x4 :: n1 :: n2 :: n3 :: n4 :: P :: inv :: cntp :: rest} =
      some (prTailModel s c q3 q2 q1 q4 z0 z1 z2 z3 x4 n1 n2 n3 n4 P inv cntp rest) := by
  have h0 : runInstructions prTailpart0Program {s with pc := UInt256.ofNat 5178, memory := s.memory, stack := c :: q3 :: q2 :: q1 :: q4 :: z0 :: z1 :: z2 :: z3 :: x4 :: n1 :: n2 :: n3 :: n4 :: P :: inv :: cntp :: rest} = some {s with pc := UInt256.ofNat 5184, memory := s.memory, stack := z0 :: z1 :: z2 :: z3 :: c :: n1 :: n2 :: n3 :: n4 :: P :: inv :: cntp :: rest} := by
    simpa only [prTailpart0Model] using prTailpart0_run (s) c q3 q2 q1 q4 z0 z1 z2 z3 x4 n1 n2 n3 n4 P inv cntp rest hcap hact
  exact h0

theorem prTail_eq (s : State) (c q3 q2 q1 q4 z0 z1 z2 z3 x4 n1 n2 n3 n4 P inv cntp : UInt256) (rest : List UInt256) :
    prTailModel s c q3 q2 q1 q4 z0 z1 z2 z3 x4 n1 n2 n3 n4 P inv cntp rest =
      {s with pc := UInt256.ofNat 5184, stack := z0 :: z1 :: z2 :: z3 :: c :: n1 :: n2 :: n3 :: n4 :: P :: inv :: cntp :: rest} := by
  simp only [prTailModel]

end CycleSubmission.R5.ExecProduct
