import Challenge.Modexp.Submission.Proofs.Bytecode.WindowNibbleDefs
import Challenge.Modexp.Submission.Proofs.Fast.Exp

set_option warningAsError true
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option maxRecDepth 40000
set_option maxHeartbeats 8000000

namespace CycleSubmission.R5.ExecSquare
open EvmSemantics EvmSemantics.EVM YulEvmCompiler
open Challenge.Modexp.Submission.Proofs.Bytecode.WindowNibbleKernel
open Challenge.EvmProof.Word (succ_ofNat_mod ofNat_add_mod ofNat_sub_ofNat literal_eq_ofNat)
open Challenge.EvmProof.Stepper (runInstr)
open Challenge.Modexp.Submission.Proofs.Fast.Exp (activeWords_fix)

private theorem hz : ({val := 0} : UInt256) = UInt256.ofNat 0 := rfl
private theorem hzn : ({val := 0} : UInt256).toNat = 0 := rfl

/-- Fusing two doubled cross products: `2(b + a) + c = 2b + (2a + c)` in `UInt256`. -/
theorem fusePair (a b c : UInt256) :
    ((b + a) + (b + a)) + c = (b + b) + ((a + a) + c) := by
  apply Challenge.EvmProof.Word.word_ext
  simp only [Challenge.EvmProof.Word.word_toNat_add]
  omega

/-! ## sqCol0: pc 4037..4063, 22 instructions -/

def sqCol0part0Program : List Instr :=
  [.op .JUMPDEST,
   .op (.Dup ⟨0, by decide⟩),
   .op (.Dup ⟨0, by decide⟩),
   .op .MUL,
   .op (.Dup ⟨11, by decide⟩),
   .op .MUL,
   .push 1 16,
   .op .SHR]

def sqCol0part0Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 : UInt256) (rest : List UInt256) : State :=
  let v0 : UInt256 := x0 * x0
  let v1 : UInt256 := x10 * v0
  let v2 : UInt256 := UInt256.shiftRight v1 (UInt256.ofNat 16)
  {s with pc := UInt256.ofNat 4046, memory := s.memory, stack := v2 :: x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: rest}

theorem sqCol0part0_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions sqCol0part0Program {s with pc := UInt256.ofNat 4037, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: rest} =
      some (sqCol0part0Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 rest) := by
  have hc (j : Nat) (hj : j ≤ 27) : rest.length + j < 1024 := by omega
  have hcr : rest.length < 1024 := by omega
  simp [hz, hzn, sqCol0part0Program, sqCol0part0Model, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, ofNat_sub_ofNat, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, hc, hcr]

def sqCol0part1Program : List Instr :=
  [.op (.Dup ⟨10, by decide⟩),
   .op (.Dup ⟨2, by decide⟩),
   .op (.Dup ⟨0, by decide⟩),
   .op .MULMOD,
   .op (.Dup ⟨11, by decide⟩),
   .push 1 160,
   .op .MLOAD,
   .op (.Dup ⟨3, by decide⟩)]

def sqCol0part1Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 : UInt256) (rest : List UInt256) : State :=
  let v0 : UInt256 := UInt256.mulMod x1 x1 x10
  let v1 : UInt256 := MachineState.readWord s.memory 160
  {s with pc := UInt256.ofNat 4055, memory := s.memory, stack := x0 :: v1 :: x10 :: v0 :: x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: rest}

theorem sqCol0part1_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions sqCol0part1Program {s with pc := UInt256.ofNat 4046, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: rest} =
      some (sqCol0part1Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 rest) := by
  have hc (j : Nat) (hj : j ≤ 30) : rest.length + j < 1024 := by omega
  have hcr : rest.length < 1024 := by omega
  have ha160 : (160 : UInt256).toNat = 160 := rfl
  have hf160 := activeWords_fix s 160 32 (by decide) (by norm_num) hact
  simp [hz, hzn, sqCol0part1Program, sqCol0part1Model, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, ofNat_sub_ofNat, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, hc, hcr, ha160, hf160]

def sqCol0part2Program : List Instr :=
  [.op .MULMOD,
   .op .ADD,
   .op (.Dup ⟨11, by decide⟩),
   .op (.Swap ⟨0, by decide⟩),
   .push 2 2048,
   .op .MULMOD]

def sqCol0part2Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 : UInt256) (rest : List UInt256) : State :=
  let v0 : UInt256 := UInt256.mulMod x0 x1 x2
  let v1 : UInt256 := v0 + x3
  let v2 : UInt256 := UInt256.mulMod (UInt256.ofNat 2048) v1 x14
  {s with pc := UInt256.ofNat 4063, memory := s.memory, stack := v2 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: rest}

theorem sqCol0part2_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions sqCol0part2Program {s with pc := UInt256.ofNat 4055, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: rest} =
      some (sqCol0part2Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 rest) := by
  have hc (j : Nat) (hj : j ≤ 30) : rest.length + j < 1024 := by omega
  have hcr : rest.length < 1024 := by omega
  simp [hz, hzn, sqCol0part2Program, sqCol0part2Model, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, ofNat_sub_ofNat, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, hc, hcr]

def sqCol0Program : List Instr :=
  [.op .JUMPDEST,
   .op (.Dup ⟨0, by decide⟩),
   .op (.Dup ⟨0, by decide⟩),
   .op .MUL,
   .op (.Dup ⟨11, by decide⟩),
   .op .MUL,
   .push 1 16,
   .op .SHR,
   .op (.Dup ⟨10, by decide⟩),
   .op (.Dup ⟨2, by decide⟩),
   .op (.Dup ⟨0, by decide⟩),
   .op .MULMOD,
   .op (.Dup ⟨11, by decide⟩),
   .push 1 160,
   .op .MLOAD,
   .op (.Dup ⟨3, by decide⟩),
   .op .MULMOD,
   .op .ADD,
   .op (.Dup ⟨11, by decide⟩),
   .op (.Swap ⟨0, by decide⟩),
   .push 2 2048,
   .op .MULMOD]

def sqCol0Model (s : State) (a0 a1 a2 a3 a4 n1 n2 n3 n4 P inv cnt : UInt256) (rest : List UInt256) : State :=
  let v0 : UInt256 := a0 * a0
  let v1 : UInt256 := inv * v0
  let v2 : UInt256 := UInt256.shiftRight v1 (UInt256.ofNat 16)
  let v3 : UInt256 := UInt256.mulMod a0 a0 P
  let v4 : UInt256 := MachineState.readWord s.memory 160
  let v5 : UInt256 := UInt256.mulMod v2 v4 P
  let v6 : UInt256 := v5 + v3
  let v7 : UInt256 := UInt256.mulMod (UInt256.ofNat 2048) v6 P
  {s with pc := UInt256.ofNat 4063, memory := s.memory, stack := v7 :: v2 :: a0 :: a1 :: a2 :: a3 :: a4 :: n1 :: n2 :: n3 :: n4 :: P :: inv :: cnt :: rest}

theorem sqCol0_run (s : State) (a0 a1 a2 a3 a4 n1 n2 n3 n4 P inv cnt : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions sqCol0Program {s with pc := UInt256.ofNat 4037, stack := a0 :: a1 :: a2 :: a3 :: a4 :: n1 :: n2 :: n3 :: n4 :: P :: inv :: cnt :: rest} =
      some (sqCol0Model s a0 a1 a2 a3 a4 n1 n2 n3 n4 P inv cnt rest) := by
  let v0 : UInt256 := a0 * a0
  let v1 : UInt256 := inv * v0
  let v2 : UInt256 := UInt256.shiftRight v1 (UInt256.ofNat 16)
  let v3 : UInt256 := UInt256.mulMod a0 a0 P
  let v4 : UInt256 := MachineState.readWord s.memory 160
  let v5 : UInt256 := UInt256.mulMod v2 v4 P
  let v6 : UInt256 := v5 + v3
  let v7 : UInt256 := UInt256.mulMod (UInt256.ofNat 2048) v6 P
  have h0 : runInstructions sqCol0part0Program {s with pc := UInt256.ofNat 4037, memory := s.memory, stack := a0 :: a1 :: a2 :: a3 :: a4 :: n1 :: n2 :: n3 :: n4 :: P :: inv :: cnt :: rest} = some {s with pc := UInt256.ofNat 4046, memory := s.memory, stack := v2 :: a0 :: a1 :: a2 :: a3 :: a4 :: n1 :: n2 :: n3 :: n4 :: P :: inv :: cnt :: rest} := by
    simpa only [sqCol0part0Model, v0, v1, v2] using sqCol0part0_run (s) a0 a1 a2 a3 a4 n1 n2 n3 n4 P inv cnt rest hcap hact
  have h1 : runInstructions sqCol0part1Program {s with pc := UInt256.ofNat 4046, memory := s.memory, stack := v2 :: a0 :: a1 :: a2 :: a3 :: a4 :: n1 :: n2 :: n3 :: n4 :: P :: inv :: cnt :: rest} = some {s with pc := UInt256.ofNat 4055, memory := s.memory, stack := v2 :: v4 :: P :: v3 :: v2 :: a0 :: a1 :: a2 :: a3 :: a4 :: n1 :: n2 :: n3 :: n4 :: P :: inv :: cnt :: rest} := by
    simpa only [sqCol0part1Model, v3, v4] using sqCol0part1_run (s) v2 a0 a1 a2 a3 a4 n1 n2 n3 n4 P inv cnt rest hcap hact
  have h2 : runInstructions sqCol0part2Program {s with pc := UInt256.ofNat 4055, memory := s.memory, stack := v2 :: v4 :: P :: v3 :: v2 :: a0 :: a1 :: a2 :: a3 :: a4 :: n1 :: n2 :: n3 :: n4 :: P :: inv :: cnt :: rest} = some {s with pc := UInt256.ofNat 4063, memory := s.memory, stack := v7 :: v2 :: a0 :: a1 :: a2 :: a3 :: a4 :: n1 :: n2 :: n3 :: n4 :: P :: inv :: cnt :: rest} := by
    simpa only [sqCol0part2Model, v5, v6, v7] using sqCol0part2_run (s) v2 v4 P v3 v2 a0 a1 a2 a3 a4 n1 n2 n3 n4 P inv cnt rest hcap hact
  exact (runInstructions_append_some _ _ _ _ _ h0 (runInstructions_append_some _ _ _ _ _ h1 h2))

def sqCol0_o0 (a0 a1 a2 a3 a4 n1 n2 n3 n4 P inv cnt n0 : UInt256) : UInt256 :=
  (UInt256.mulMod (UInt256.ofNat 2048) ((UInt256.mulMod (UInt256.shiftRight (inv * (a0 * a0)) (UInt256.ofNat 16)) n0 P) + (UInt256.mulMod a0 a0 P)) P)

def sqCol0_o1 (a0 a1 a2 a3 a4 n1 n2 n3 n4 P inv cnt n0 : UInt256) : UInt256 :=
  (UInt256.shiftRight (inv * (a0 * a0)) (UInt256.ofNat 16))

theorem sqCol0_eq (s : State) (a0 a1 a2 a3 a4 n1 n2 n3 n4 P inv cnt n0 : UInt256) (rest : List UInt256)
    (h_n0 : MachineState.readWord s.memory 160 = n0) :
    sqCol0Model s a0 a1 a2 a3 a4 n1 n2 n3 n4 P inv cnt rest =
      {s with pc := UInt256.ofNat 4063, stack := (sqCol0_o0 a0 a1 a2 a3 a4 n1 n2 n3 n4 P inv cnt n0) :: (sqCol0_o1 a0 a1 a2 a3 a4 n1 n2 n3 n4 P inv cnt n0) :: a0 :: a1 :: a2 :: a3 :: a4 :: n1 :: n2 :: n3 :: n4 :: P :: inv :: cnt :: rest} := by
  simp only [sqCol0Model, sqCol0_o0, sqCol0_o1, h_n0]

/-! ## sqCol1: pc 4063..4105, 38 instructions -/

def sqCol1part0Program : List Instr :=
  [.op (.Dup ⟨0, by decide⟩),
   .op (.Dup ⟨4, by decide⟩),
   .op (.Dup ⟨4, by decide⟩),
   .op .MUL,
   .op (.Dup ⟨0, by decide⟩),
   .op .ADD,
   .op .ADD,
   .op (.Dup ⟨8, by decide⟩)]

def sqCol1part0Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 : UInt256) (rest : List UInt256) : State :=
  let v0 : UInt256 := x2 * x3
  let v1 : UInt256 := v0 + v0
  let v2 : UInt256 := v1 + x0
  {s with pc := UInt256.ofNat 4071, memory := s.memory, stack := x7 :: v2 :: x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: rest}

theorem sqCol1part0_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions sqCol1part0Program {s with pc := UInt256.ofNat 4063, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: rest} =
      some (sqCol1part0Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 rest) := by
  have hc (j : Nat) (hj : j ≤ 30) : rest.length + j < 1024 := by omega
  have hcr : rest.length < 1024 := by omega
  simp [hz, hzn, sqCol1part0Program, sqCol1part0Model, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, ofNat_sub_ofNat, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, hc, hcr]

def sqCol1part1Program : List Instr :=
  [.op (.Dup ⟨3, by decide⟩),
   .op .MUL,
   .op .ADD,
   .op (.Dup ⟨13, by decide⟩),
   .op .MUL,
   .push 1 16,
   .op .SHR,
   .op (.Swap ⟨0, by decide⟩)]

def sqCol1part1Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 : UInt256) (rest : List UInt256) : State :=
  let v0 : UInt256 := x3 * x0
  let v1 : UInt256 := v0 + x1
  let v2 : UInt256 := x14 * v1
  let v3 : UInt256 := UInt256.shiftRight v2 (UInt256.ofNat 16)
  {s with pc := UInt256.ofNat 4080, memory := s.memory, stack := x2 :: v3 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: rest}

theorem sqCol1part1_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions sqCol1part1Program {s with pc := UInt256.ofNat 4071, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: rest} =
      some (sqCol1part1Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 rest) := by
  have hc (j : Nat) (hj : j ≤ 30) : rest.length + j < 1024 := by omega
  have hcr : rest.length < 1024 := by omega
  simp [hz, hzn, sqCol1part1Program, sqCol1part1Model, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, ofNat_sub_ofNat, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, hc, hcr]

def sqCol1part2Program : List Instr :=
  [.op (.Dup ⟨12, by decide⟩),
   .op (.Dup ⟨5, by decide⟩),
   .op (.Dup ⟨5, by decide⟩),
   .op .MULMOD,
   .op (.Dup ⟨0, by decide⟩),
   .op .ADD,
   .op .ADD,
   .op (.Dup ⟨12, by decide⟩)]

def sqCol1part2Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 : UInt256) (rest : List UInt256) : State :=
  let v0 : UInt256 := UInt256.mulMod x3 x4 x12
  let v1 : UInt256 := v0 + v0
  let v2 : UInt256 := v1 + x0
  {s with pc := UInt256.ofNat 4088, memory := s.memory, stack := x12 :: v2 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: rest}

theorem sqCol1part2_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions sqCol1part2Program {s with pc := UInt256.ofNat 4080, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: rest} =
      some (sqCol1part2Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 rest) := by
  have hc (j : Nat) (hj : j ≤ 31) : rest.length + j < 1024 := by omega
  have hcr : rest.length < 1024 := by omega
  simp [hz, hzn, sqCol1part2Program, sqCol1part2Model, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, ofNat_sub_ofNat, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, hc, hcr]

def sqCol1part3Program : List Instr :=
  [.op (.Dup ⟨9, by decide⟩),
   .op (.Dup ⟨4, by decide⟩),
   .op .MULMOD,
   .op .ADD,
   .op (.Dup ⟨12, by decide⟩),
   .push 1 160,
   .op .MLOAD,
   .op (.Dup ⟨3, by decide⟩)]

def sqCol1part3Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 : UInt256) (rest : List UInt256) : State :=
  let v0 : UInt256 := UInt256.mulMod x3 x9 x0
  let v1 : UInt256 := v0 + x1
  let v2 : UInt256 := MachineState.readWord s.memory 160
  {s with pc := UInt256.ofNat 4097, memory := s.memory, stack := x2 :: v2 :: x13 :: v1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: rest}

theorem sqCol1part3_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions sqCol1part3Program {s with pc := UInt256.ofNat 4088, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: rest} =
      some (sqCol1part3Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 rest) := by
  have hc (j : Nat) (hj : j ≤ 31) : rest.length + j < 1024 := by omega
  have hcr : rest.length < 1024 := by omega
  have ha160 : (160 : UInt256).toNat = 160 := rfl
  have hf160 := activeWords_fix s 160 32 (by decide) (by norm_num) hact
  simp [hz, hzn, sqCol1part3Program, sqCol1part3Model, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, ofNat_sub_ofNat, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, hc, hcr, ha160, hf160]

def sqCol1part4Program : List Instr :=
  [.op .MULMOD,
   .op .ADD,
   .op (.Dup ⟨12, by decide⟩),
   .op (.Swap ⟨0, by decide⟩),
   .push 2 2048,
   .op .MULMOD]

def sqCol1part4Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 : UInt256) (rest : List UInt256) : State :=
  let v0 : UInt256 := UInt256.mulMod x0 x1 x2
  let v1 : UInt256 := v0 + x3
  let v2 : UInt256 := UInt256.mulMod (UInt256.ofNat 2048) v1 x15
  {s with pc := UInt256.ofNat 4105, memory := s.memory, stack := v2 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: rest}

theorem sqCol1part4_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions sqCol1part4Program {s with pc := UInt256.ofNat 4097, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: rest} =
      some (sqCol1part4Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 rest) := by
  have hc (j : Nat) (hj : j ≤ 31) : rest.length + j < 1024 := by omega
  have hcr : rest.length < 1024 := by omega
  simp [hz, hzn, sqCol1part4Program, sqCol1part4Model, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, ofNat_sub_ofNat, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, hc, hcr]

def sqCol1Program : List Instr :=
  [.op (.Dup ⟨0, by decide⟩),
   .op (.Dup ⟨4, by decide⟩),
   .op (.Dup ⟨4, by decide⟩),
   .op .MUL,
   .op (.Dup ⟨0, by decide⟩),
   .op .ADD,
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
   .op (.Dup ⟨5, by decide⟩),
   .op (.Dup ⟨5, by decide⟩),
   .op .MULMOD,
   .op (.Dup ⟨0, by decide⟩),
   .op .ADD,
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

def sqCol1Model (s : State) (c q0 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cnt : UInt256) (rest : List UInt256) : State :=
  let v0 : UInt256 := x0 * x1
  let v1 : UInt256 := v0 + v0
  let v2 : UInt256 := v1 + c
  let v3 : UInt256 := q0 * n1
  let v4 : UInt256 := v3 + v2
  let v5 : UInt256 := inv * v4
  let v6 : UInt256 := UInt256.shiftRight v5 (UInt256.ofNat 16)
  let v7 : UInt256 := UInt256.mulMod x0 x1 P
  let v8 : UInt256 := v7 + v7
  let v9 : UInt256 := v8 + c
  let v10 : UInt256 := UInt256.mulMod q0 n1 P
  let v11 : UInt256 := v10 + v9
  let v12 : UInt256 := MachineState.readWord s.memory 160
  let v13 : UInt256 := UInt256.mulMod v6 v12 P
  let v14 : UInt256 := v13 + v11
  let v15 : UInt256 := UInt256.mulMod (UInt256.ofNat 2048) v14 P
  {s with pc := UInt256.ofNat 4105, memory := s.memory, stack := v15 :: v6 :: q0 :: x0 :: x1 :: x2 :: x3 :: x4 :: n1 :: n2 :: n3 :: n4 :: P :: inv :: cnt :: rest}

theorem sqCol1_run (s : State) (c q0 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cnt : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions sqCol1Program {s with pc := UInt256.ofNat 4063, stack := c :: q0 :: x0 :: x1 :: x2 :: x3 :: x4 :: n1 :: n2 :: n3 :: n4 :: P :: inv :: cnt :: rest} =
      some (sqCol1Model s c q0 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cnt rest) := by
  let v0 : UInt256 := x0 * x1
  let v1 : UInt256 := v0 + v0
  let v2 : UInt256 := v1 + c
  let v3 : UInt256 := q0 * n1
  let v4 : UInt256 := v3 + v2
  let v5 : UInt256 := inv * v4
  let v6 : UInt256 := UInt256.shiftRight v5 (UInt256.ofNat 16)
  let v7 : UInt256 := UInt256.mulMod x0 x1 P
  let v8 : UInt256 := v7 + v7
  let v9 : UInt256 := v8 + c
  let v10 : UInt256 := UInt256.mulMod q0 n1 P
  let v11 : UInt256 := v10 + v9
  let v12 : UInt256 := MachineState.readWord s.memory 160
  let v13 : UInt256 := UInt256.mulMod v6 v12 P
  let v14 : UInt256 := v13 + v11
  let v15 : UInt256 := UInt256.mulMod (UInt256.ofNat 2048) v14 P
  have h0 : runInstructions sqCol1part0Program {s with pc := UInt256.ofNat 4063, memory := s.memory, stack := c :: q0 :: x0 :: x1 :: x2 :: x3 :: x4 :: n1 :: n2 :: n3 :: n4 :: P :: inv :: cnt :: rest} = some {s with pc := UInt256.ofNat 4071, memory := s.memory, stack := n1 :: v2 :: c :: q0 :: x0 :: x1 :: x2 :: x3 :: x4 :: n1 :: n2 :: n3 :: n4 :: P :: inv :: cnt :: rest} := by
    simpa only [sqCol1part0Model, v0, v1, v2] using sqCol1part0_run (s) c q0 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cnt rest hcap hact
  have h1 : runInstructions sqCol1part1Program {s with pc := UInt256.ofNat 4071, memory := s.memory, stack := n1 :: v2 :: c :: q0 :: x0 :: x1 :: x2 :: x3 :: x4 :: n1 :: n2 :: n3 :: n4 :: P :: inv :: cnt :: rest} = some {s with pc := UInt256.ofNat 4080, memory := s.memory, stack := c :: v6 :: q0 :: x0 :: x1 :: x2 :: x3 :: x4 :: n1 :: n2 :: n3 :: n4 :: P :: inv :: cnt :: rest} := by
    simpa only [sqCol1part1Model, v3, v4, v5, v6] using sqCol1part1_run (s) n1 v2 c q0 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cnt rest hcap hact
  have h2 : runInstructions sqCol1part2Program {s with pc := UInt256.ofNat 4080, memory := s.memory, stack := c :: v6 :: q0 :: x0 :: x1 :: x2 :: x3 :: x4 :: n1 :: n2 :: n3 :: n4 :: P :: inv :: cnt :: rest} = some {s with pc := UInt256.ofNat 4088, memory := s.memory, stack := P :: v9 :: v6 :: q0 :: x0 :: x1 :: x2 :: x3 :: x4 :: n1 :: n2 :: n3 :: n4 :: P :: inv :: cnt :: rest} := by
    simpa only [sqCol1part2Model, v7, v8, v9] using sqCol1part2_run (s) c v6 q0 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cnt rest hcap hact
  have h3 : runInstructions sqCol1part3Program {s with pc := UInt256.ofNat 4088, memory := s.memory, stack := P :: v9 :: v6 :: q0 :: x0 :: x1 :: x2 :: x3 :: x4 :: n1 :: n2 :: n3 :: n4 :: P :: inv :: cnt :: rest} = some {s with pc := UInt256.ofNat 4097, memory := s.memory, stack := v6 :: v12 :: P :: v11 :: v6 :: q0 :: x0 :: x1 :: x2 :: x3 :: x4 :: n1 :: n2 :: n3 :: n4 :: P :: inv :: cnt :: rest} := by
    simpa only [sqCol1part3Model, v10, v11, v12] using sqCol1part3_run (s) P v9 v6 q0 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cnt rest hcap hact
  have h4 : runInstructions sqCol1part4Program {s with pc := UInt256.ofNat 4097, memory := s.memory, stack := v6 :: v12 :: P :: v11 :: v6 :: q0 :: x0 :: x1 :: x2 :: x3 :: x4 :: n1 :: n2 :: n3 :: n4 :: P :: inv :: cnt :: rest} = some {s with pc := UInt256.ofNat 4105, memory := s.memory, stack := v15 :: v6 :: q0 :: x0 :: x1 :: x2 :: x3 :: x4 :: n1 :: n2 :: n3 :: n4 :: P :: inv :: cnt :: rest} := by
    simpa only [sqCol1part4Model, v13, v14, v15] using sqCol1part4_run (s) v6 v12 P v11 v6 q0 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cnt rest hcap hact
  exact (runInstructions_append_some _ _ _ _ _ h0 (runInstructions_append_some _ _ _ _ _ h1 (runInstructions_append_some _ _ _ _ _ h2 (runInstructions_append_some _ _ _ _ _ h3 h4))))

def sqCol1_o0 (c q0 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cnt n0 : UInt256) : UInt256 :=
  (UInt256.mulMod (UInt256.ofNat 2048) ((UInt256.mulMod (UInt256.shiftRight (inv * ((q0 * n1) + (((x0 * x1) + (x0 * x1)) + c))) (UInt256.ofNat 16)) n0 P) + ((UInt256.mulMod q0 n1 P) + (((UInt256.mulMod x0 x1 P) + (UInt256.mulMod x0 x1 P)) + c))) P)

def sqCol1_o1 (c q0 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cnt n0 : UInt256) : UInt256 :=
  (UInt256.shiftRight (inv * ((q0 * n1) + (((x0 * x1) + (x0 * x1)) + c))) (UInt256.ofNat 16))

theorem sqCol1_eq (s : State) (c q0 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cnt n0 : UInt256) (rest : List UInt256)
    (h_n0 : MachineState.readWord s.memory 160 = n0) :
    sqCol1Model s c q0 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cnt rest =
      {s with pc := UInt256.ofNat 4105, stack := (sqCol1_o0 c q0 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cnt n0) :: (sqCol1_o1 c q0 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cnt n0) :: q0 :: x0 :: x1 :: x2 :: x3 :: x4 :: n1 :: n2 :: n3 :: n4 :: P :: inv :: cnt :: rest} := by
  simp only [sqCol1Model, sqCol1_o0, sqCol1_o1, h_n0]

/-! ## sqCol2: pc 4105..4165, 56 instructions -/

def sqCol2part0Program : List Instr :=
  [.op (.Dup ⟨0, by decide⟩),
   .op (.Dup ⟨6, by decide⟩),
   .op (.Dup ⟨5, by decide⟩),
   .op .MUL,
   .op (.Dup ⟨0, by decide⟩),
   .op .ADD,
   .op .ADD,
   .op (.Dup ⟨5, by decide⟩)]

def sqCol2part0Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 : UInt256) (rest : List UInt256) : State :=
  let v0 : UInt256 := x3 * x5
  let v1 : UInt256 := v0 + v0
  let v2 : UInt256 := v1 + x0
  {s with pc := UInt256.ofNat 4113, memory := s.memory, stack := x4 :: v2 :: x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: rest}

theorem sqCol2part0_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions sqCol2part0Program {s with pc := UInt256.ofNat 4105, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: rest} =
      some (sqCol2part0Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 rest) := by
  have hc (j : Nat) (hj : j ≤ 31) : rest.length + j < 1024 := by omega
  have hcr : rest.length < 1024 := by omega
  simp [hz, hzn, sqCol2part0Program, sqCol2part0Model, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, ofNat_sub_ofNat, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, hc, hcr]

def sqCol2part1Program : List Instr :=
  [.op (.Dup ⟨0, by decide⟩),
   .op .MUL,
   .op .ADD,
   .op (.Dup ⟨10, by decide⟩),
   .op (.Dup ⟨4, by decide⟩),
   .op .MUL,
   .op .ADD,
   .op (.Dup ⟨9, by decide⟩)]

def sqCol2part1Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 : UInt256) (rest : List UInt256) : State :=
  let v0 : UInt256 := x0 * x0
  let v1 : UInt256 := v0 + x1
  let v2 : UInt256 := x4 * x11
  let v3 : UInt256 := v2 + v1
  {s with pc := UInt256.ofNat 4121, memory := s.memory, stack := x10 :: v3 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: rest}

theorem sqCol2part1_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions sqCol2part1Program {s with pc := UInt256.ofNat 4113, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: rest} =
      some (sqCol2part1Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 rest) := by
  have hc (j : Nat) (hj : j ≤ 31) : rest.length + j < 1024 := by omega
  have hcr : rest.length < 1024 := by omega
  simp [hz, hzn, sqCol2part1Program, sqCol2part1Model, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, ofNat_sub_ofNat, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, hc, hcr]

def sqCol2part2Program : List Instr :=
  [.op (.Dup ⟨3, by decide⟩),
   .op .MUL,
   .op .ADD,
   .op (.Dup ⟨14, by decide⟩),
   .op .MUL,
   .push 1 16,
   .op .SHR,
   .op (.Swap ⟨0, by decide⟩)]

def sqCol2part2Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 : UInt256) (rest : List UInt256) : State :=
  let v0 : UInt256 := x3 * x0
  let v1 : UInt256 := v0 + x1
  let v2 : UInt256 := x15 * v1
  let v3 : UInt256 := UInt256.shiftRight v2 (UInt256.ofNat 16)
  {s with pc := UInt256.ofNat 4130, memory := s.memory, stack := x2 :: v3 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: rest}

theorem sqCol2part2_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions sqCol2part2Program {s with pc := UInt256.ofNat 4121, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: rest} =
      some (sqCol2part2Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 rest) := by
  have hc (j : Nat) (hj : j ≤ 31) : rest.length + j < 1024 := by omega
  have hcr : rest.length < 1024 := by omega
  simp [hz, hzn, sqCol2part2Program, sqCol2part2Model, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, ofNat_sub_ofNat, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, hc, hcr]

def sqCol2part3Program : List Instr :=
  [.op (.Dup ⟨13, by decide⟩),
   .op (.Dup ⟨7, by decide⟩),
   .op (.Dup ⟨6, by decide⟩),
   .op .MULMOD,
   .op (.Dup ⟨0, by decide⟩),
   .op .ADD,
   .op .ADD,
   .op (.Dup ⟨13, by decide⟩)]

def sqCol2part3Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 : UInt256) (rest : List UInt256) : State :=
  let v0 : UInt256 := UInt256.mulMod x4 x6 x13
  let v1 : UInt256 := v0 + v0
  let v2 : UInt256 := v1 + x0
  {s with pc := UInt256.ofNat 4138, memory := s.memory, stack := x13 :: v2 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: rest}

theorem sqCol2part3_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions sqCol2part3Program {s with pc := UInt256.ofNat 4130, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: rest} =
      some (sqCol2part3Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 rest) := by
  have hc (j : Nat) (hj : j ≤ 32) : rest.length + j < 1024 := by omega
  have hcr : rest.length < 1024 := by omega
  simp [hz, hzn, sqCol2part3Program, sqCol2part3Model, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, ofNat_sub_ofNat, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, hc, hcr]

def sqCol2part4Program : List Instr :=
  [.op (.Dup ⟨6, by decide⟩),
   .op (.Dup ⟨0, by decide⟩),
   .op .MULMOD,
   .op .ADD,
   .op (.Dup ⟨13, by decide⟩),
   .op (.Dup ⟨11, by decide⟩),
   .op (.Dup ⟨5, by decide⟩),
   .op .MULMOD]

def sqCol2part4Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 : UInt256) (rest : List UInt256) : State :=
  let v0 : UInt256 := UInt256.mulMod x6 x6 x0
  let v1 : UInt256 := v0 + x1
  let v2 : UInt256 := UInt256.mulMod x4 x11 x14
  {s with pc := UInt256.ofNat 4146, memory := s.memory, stack := v2 :: v1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: rest}

theorem sqCol2part4_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions sqCol2part4Program {s with pc := UInt256.ofNat 4138, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: rest} =
      some (sqCol2part4Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 rest) := by
  have hc (j : Nat) (hj : j ≤ 32) : rest.length + j < 1024 := by omega
  have hcr : rest.length < 1024 := by omega
  simp [hz, hzn, sqCol2part4Program, sqCol2part4Model, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, ofNat_sub_ofNat, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, hc, hcr]

def sqCol2part5Program : List Instr :=
  [.op .ADD,
   .op (.Dup ⟨13, by decide⟩),
   .op (.Dup ⟨10, by decide⟩),
   .op (.Dup ⟨4, by decide⟩),
   .op .MULMOD,
   .op .ADD,
   .op (.Dup ⟨13, by decide⟩)]

def sqCol2part5Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 : UInt256) (rest : List UInt256) : State :=
  let v0 : UInt256 := x0 + x1
  let v1 : UInt256 := UInt256.mulMod x3 x10 x14
  let v2 : UInt256 := v1 + v0
  {s with pc := UInt256.ofNat 4153, memory := s.memory, stack := x14 :: v2 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: rest}

theorem sqCol2part5_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions sqCol2part5Program {s with pc := UInt256.ofNat 4146, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: rest} =
      some (sqCol2part5Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 rest) := by
  have hc (j : Nat) (hj : j ≤ 32) : rest.length + j < 1024 := by omega
  have hcr : rest.length < 1024 := by omega
  simp [hz, hzn, sqCol2part5Program, sqCol2part5Model, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, ofNat_sub_ofNat, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, hc, hcr]

def sqCol2part6Program : List Instr :=
  [.push 1 160,
   .op .MLOAD,
   .op (.Dup ⟨3, by decide⟩),
   .op .MULMOD,
   .op .ADD,
   .op (.Dup ⟨13, by decide⟩),
   .op (.Swap ⟨0, by decide⟩)]

def sqCol2part6Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 : UInt256) (rest : List UInt256) : State :=
  let v0 : UInt256 := MachineState.readWord s.memory 160
  let v1 : UInt256 := UInt256.mulMod x2 v0 x0
  let v2 : UInt256 := v1 + x1
  {s with pc := UInt256.ofNat 4161, memory := s.memory, stack := v2 :: x14 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: rest}

theorem sqCol2part6_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions sqCol2part6Program {s with pc := UInt256.ofNat 4153, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: rest} =
      some (sqCol2part6Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 rest) := by
  have hc (j : Nat) (hj : j ≤ 32) : rest.length + j < 1024 := by omega
  have hcr : rest.length < 1024 := by omega
  have ha160 : (160 : UInt256).toNat = 160 := rfl
  have hf160 := activeWords_fix s 160 32 (by decide) (by norm_num) hact
  simp [hz, hzn, sqCol2part6Program, sqCol2part6Model, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, ofNat_sub_ofNat, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, hc, hcr, ha160, hf160]

def sqCol2part7Program : List Instr :=
  [.push 2 2048,
   .op .MULMOD]

def sqCol2part7Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 : UInt256) (rest : List UInt256) : State :=
  let v0 : UInt256 := UInt256.mulMod (UInt256.ofNat 2048) x0 x1
  {s with pc := UInt256.ofNat 4165, memory := s.memory, stack := v0 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: rest}

theorem sqCol2part7_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions sqCol2part7Program {s with pc := UInt256.ofNat 4161, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: rest} =
      some (sqCol2part7Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 rest) := by
  have hc (j : Nat) (hj : j ≤ 31) : rest.length + j < 1024 := by omega
  have hcr : rest.length < 1024 := by omega
  simp [hz, hzn, sqCol2part7Program, sqCol2part7Model, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, ofNat_sub_ofNat, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, hc, hcr]

def sqCol2Program : List Instr :=
  [.op (.Dup ⟨0, by decide⟩),
   .op (.Dup ⟨6, by decide⟩),
   .op (.Dup ⟨5, by decide⟩),
   .op .MUL,
   .op (.Dup ⟨0, by decide⟩),
   .op .ADD,
   .op .ADD,
   .op (.Dup ⟨5, by decide⟩),
   .op (.Dup ⟨0, by decide⟩),
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
   .op (.Dup ⟨7, by decide⟩),
   .op (.Dup ⟨6, by decide⟩),
   .op .MULMOD,
   .op (.Dup ⟨0, by decide⟩),
   .op .ADD,
   .op .ADD,
   .op (.Dup ⟨13, by decide⟩),
   .op (.Dup ⟨6, by decide⟩),
   .op (.Dup ⟨0, by decide⟩),
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

def sqCol2Model (s : State) (c q1 q0 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cnt : UInt256) (rest : List UInt256) : State :=
  let v0 : UInt256 := x0 * x2
  let v1 : UInt256 := v0 + v0
  let v2 : UInt256 := v1 + c
  let v3 : UInt256 := x1 * x1
  let v4 : UInt256 := v3 + v2
  let v5 : UInt256 := q0 * n2
  let v6 : UInt256 := v5 + v4
  let v7 : UInt256 := q1 * n1
  let v8 : UInt256 := v7 + v6
  let v9 : UInt256 := inv * v8
  let v10 : UInt256 := UInt256.shiftRight v9 (UInt256.ofNat 16)
  let v11 : UInt256 := UInt256.mulMod x0 x2 P
  let v12 : UInt256 := v11 + v11
  let v13 : UInt256 := v12 + c
  let v14 : UInt256 := UInt256.mulMod x1 x1 P
  let v15 : UInt256 := v14 + v13
  let v16 : UInt256 := UInt256.mulMod q0 n2 P
  let v17 : UInt256 := v16 + v15
  let v18 : UInt256 := UInt256.mulMod q1 n1 P
  let v19 : UInt256 := v18 + v17
  let v20 : UInt256 := MachineState.readWord s.memory 160
  let v21 : UInt256 := UInt256.mulMod v10 v20 P
  let v22 : UInt256 := v21 + v19
  let v23 : UInt256 := UInt256.mulMod (UInt256.ofNat 2048) v22 P
  {s with pc := UInt256.ofNat 4165, memory := s.memory, stack := v23 :: v10 :: q1 :: q0 :: x0 :: x1 :: x2 :: x3 :: x4 :: n1 :: n2 :: n3 :: n4 :: P :: inv :: cnt :: rest}

theorem sqCol2_run (s : State) (c q1 q0 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cnt : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions sqCol2Program {s with pc := UInt256.ofNat 4105, stack := c :: q1 :: q0 :: x0 :: x1 :: x2 :: x3 :: x4 :: n1 :: n2 :: n3 :: n4 :: P :: inv :: cnt :: rest} =
      some (sqCol2Model s c q1 q0 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cnt rest) := by
  let v0 : UInt256 := x0 * x2
  let v1 : UInt256 := v0 + v0
  let v2 : UInt256 := v1 + c
  let v3 : UInt256 := x1 * x1
  let v4 : UInt256 := v3 + v2
  let v5 : UInt256 := q0 * n2
  let v6 : UInt256 := v5 + v4
  let v7 : UInt256 := q1 * n1
  let v8 : UInt256 := v7 + v6
  let v9 : UInt256 := inv * v8
  let v10 : UInt256 := UInt256.shiftRight v9 (UInt256.ofNat 16)
  let v11 : UInt256 := UInt256.mulMod x0 x2 P
  let v12 : UInt256 := v11 + v11
  let v13 : UInt256 := v12 + c
  let v14 : UInt256 := UInt256.mulMod x1 x1 P
  let v15 : UInt256 := v14 + v13
  let v16 : UInt256 := UInt256.mulMod q0 n2 P
  let v17 : UInt256 := v16 + v15
  let v18 : UInt256 := UInt256.mulMod q1 n1 P
  let v19 : UInt256 := v18 + v17
  let v20 : UInt256 := MachineState.readWord s.memory 160
  let v21 : UInt256 := UInt256.mulMod v10 v20 P
  let v22 : UInt256 := v21 + v19
  let v23 : UInt256 := UInt256.mulMod (UInt256.ofNat 2048) v22 P
  have h0 : runInstructions sqCol2part0Program {s with pc := UInt256.ofNat 4105, memory := s.memory, stack := c :: q1 :: q0 :: x0 :: x1 :: x2 :: x3 :: x4 :: n1 :: n2 :: n3 :: n4 :: P :: inv :: cnt :: rest} = some {s with pc := UInt256.ofNat 4113, memory := s.memory, stack := x1 :: v2 :: c :: q1 :: q0 :: x0 :: x1 :: x2 :: x3 :: x4 :: n1 :: n2 :: n3 :: n4 :: P :: inv :: cnt :: rest} := by
    simpa only [sqCol2part0Model, v0, v1, v2] using sqCol2part0_run (s) c q1 q0 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cnt rest hcap hact
  have h1 : runInstructions sqCol2part1Program {s with pc := UInt256.ofNat 4113, memory := s.memory, stack := x1 :: v2 :: c :: q1 :: q0 :: x0 :: x1 :: x2 :: x3 :: x4 :: n1 :: n2 :: n3 :: n4 :: P :: inv :: cnt :: rest} = some {s with pc := UInt256.ofNat 4121, memory := s.memory, stack := n1 :: v6 :: c :: q1 :: q0 :: x0 :: x1 :: x2 :: x3 :: x4 :: n1 :: n2 :: n3 :: n4 :: P :: inv :: cnt :: rest} := by
    simpa only [sqCol2part1Model, v3, v4, v5, v6] using sqCol2part1_run (s) x1 v2 c q1 q0 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cnt rest hcap hact
  have h2 : runInstructions sqCol2part2Program {s with pc := UInt256.ofNat 4121, memory := s.memory, stack := n1 :: v6 :: c :: q1 :: q0 :: x0 :: x1 :: x2 :: x3 :: x4 :: n1 :: n2 :: n3 :: n4 :: P :: inv :: cnt :: rest} = some {s with pc := UInt256.ofNat 4130, memory := s.memory, stack := c :: v10 :: q1 :: q0 :: x0 :: x1 :: x2 :: x3 :: x4 :: n1 :: n2 :: n3 :: n4 :: P :: inv :: cnt :: rest} := by
    simpa only [sqCol2part2Model, v7, v8, v9, v10] using sqCol2part2_run (s) n1 v6 c q1 q0 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cnt rest hcap hact
  have h3 : runInstructions sqCol2part3Program {s with pc := UInt256.ofNat 4130, memory := s.memory, stack := c :: v10 :: q1 :: q0 :: x0 :: x1 :: x2 :: x3 :: x4 :: n1 :: n2 :: n3 :: n4 :: P :: inv :: cnt :: rest} = some {s with pc := UInt256.ofNat 4138, memory := s.memory, stack := P :: v13 :: v10 :: q1 :: q0 :: x0 :: x1 :: x2 :: x3 :: x4 :: n1 :: n2 :: n3 :: n4 :: P :: inv :: cnt :: rest} := by
    simpa only [sqCol2part3Model, v11, v12, v13] using sqCol2part3_run (s) c v10 q1 q0 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cnt rest hcap hact
  have h4 : runInstructions sqCol2part4Program {s with pc := UInt256.ofNat 4138, memory := s.memory, stack := P :: v13 :: v10 :: q1 :: q0 :: x0 :: x1 :: x2 :: x3 :: x4 :: n1 :: n2 :: n3 :: n4 :: P :: inv :: cnt :: rest} = some {s with pc := UInt256.ofNat 4146, memory := s.memory, stack := v16 :: v15 :: v10 :: q1 :: q0 :: x0 :: x1 :: x2 :: x3 :: x4 :: n1 :: n2 :: n3 :: n4 :: P :: inv :: cnt :: rest} := by
    simpa only [sqCol2part4Model, v14, v15, v16] using sqCol2part4_run (s) P v13 v10 q1 q0 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cnt rest hcap hact
  have h5 : runInstructions sqCol2part5Program {s with pc := UInt256.ofNat 4146, memory := s.memory, stack := v16 :: v15 :: v10 :: q1 :: q0 :: x0 :: x1 :: x2 :: x3 :: x4 :: n1 :: n2 :: n3 :: n4 :: P :: inv :: cnt :: rest} = some {s with pc := UInt256.ofNat 4153, memory := s.memory, stack := P :: v19 :: v10 :: q1 :: q0 :: x0 :: x1 :: x2 :: x3 :: x4 :: n1 :: n2 :: n3 :: n4 :: P :: inv :: cnt :: rest} := by
    simpa only [sqCol2part5Model, v17, v18, v19] using sqCol2part5_run (s) v16 v15 v10 q1 q0 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cnt rest hcap hact
  have h6 : runInstructions sqCol2part6Program {s with pc := UInt256.ofNat 4153, memory := s.memory, stack := P :: v19 :: v10 :: q1 :: q0 :: x0 :: x1 :: x2 :: x3 :: x4 :: n1 :: n2 :: n3 :: n4 :: P :: inv :: cnt :: rest} = some {s with pc := UInt256.ofNat 4161, memory := s.memory, stack := v22 :: P :: v10 :: q1 :: q0 :: x0 :: x1 :: x2 :: x3 :: x4 :: n1 :: n2 :: n3 :: n4 :: P :: inv :: cnt :: rest} := by
    simpa only [sqCol2part6Model, v20, v21, v22] using sqCol2part6_run (s) P v19 v10 q1 q0 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cnt rest hcap hact
  have h7 : runInstructions sqCol2part7Program {s with pc := UInt256.ofNat 4161, memory := s.memory, stack := v22 :: P :: v10 :: q1 :: q0 :: x0 :: x1 :: x2 :: x3 :: x4 :: n1 :: n2 :: n3 :: n4 :: P :: inv :: cnt :: rest} = some {s with pc := UInt256.ofNat 4165, memory := s.memory, stack := v23 :: v10 :: q1 :: q0 :: x0 :: x1 :: x2 :: x3 :: x4 :: n1 :: n2 :: n3 :: n4 :: P :: inv :: cnt :: rest} := by
    simpa only [sqCol2part7Model, v23] using sqCol2part7_run (s) v22 P v10 q1 q0 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cnt rest hcap hact
  exact (runInstructions_append_some _ _ _ _ _ h0 (runInstructions_append_some _ _ _ _ _ h1 (runInstructions_append_some _ _ _ _ _ h2 (runInstructions_append_some _ _ _ _ _ h3 (runInstructions_append_some _ _ _ _ _ h4 (runInstructions_append_some _ _ _ _ _ h5 (runInstructions_append_some _ _ _ _ _ h6 h7)))))))

def sqCol2_o0 (c q1 q0 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cnt n0 : UInt256) : UInt256 :=
  (UInt256.mulMod (UInt256.ofNat 2048) ((UInt256.mulMod (UInt256.shiftRight (inv * ((q1 * n1) + ((q0 * n2) + ((x1 * x1) + (((x0 * x2) + (x0 * x2)) + c))))) (UInt256.ofNat 16)) n0 P) + ((UInt256.mulMod q1 n1 P) + ((UInt256.mulMod q0 n2 P) + ((UInt256.mulMod x1 x1 P) + (((UInt256.mulMod x0 x2 P) + (UInt256.mulMod x0 x2 P)) + c))))) P)

def sqCol2_o1 (c q1 q0 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cnt n0 : UInt256) : UInt256 :=
  (UInt256.shiftRight (inv * ((q1 * n1) + ((q0 * n2) + ((x1 * x1) + (((x0 * x2) + (x0 * x2)) + c))))) (UInt256.ofNat 16))

theorem sqCol2_eq (s : State) (c q1 q0 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cnt n0 : UInt256) (rest : List UInt256)
    (h_n0 : MachineState.readWord s.memory 160 = n0) :
    sqCol2Model s c q1 q0 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cnt rest =
      {s with pc := UInt256.ofNat 4165, stack := (sqCol2_o0 c q1 q0 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cnt n0) :: (sqCol2_o1 c q1 q0 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cnt n0) :: q1 :: q0 :: x0 :: x1 :: x2 :: x3 :: x4 :: n1 :: n2 :: n3 :: n4 :: P :: inv :: cnt :: rest} := by
  simp only [sqCol2Model, sqCol2_o0, sqCol2_o1, h_n0]

/-! ## sqCol3: pc 4165..4234, 65 instructions -/

def sqCol3part0Program : List Instr :=
  [.op (.Dup ⟨0, by decide⟩),
   .op (.Dup ⟨8, by decide⟩),
   .op (.Dup ⟨6, by decide⟩),
   .op .MUL,
   .op (.Dup ⟨8, by decide⟩),
   .op (.Dup ⟨8, by decide⟩),
   .op .MUL,
   .op .ADD]

def sqCol3part0Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 : UInt256) (rest : List UInt256) : State :=
  let v0 : UInt256 := x4 * x7
  let v1 : UInt256 := x5 * x6
  let v2 : UInt256 := v1 + v0
  {s with pc := UInt256.ofNat 4173, memory := s.memory, stack := v2 :: x0 :: x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: rest}

theorem sqCol3part0_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions sqCol3part0Program {s with pc := UInt256.ofNat 4165, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: rest} =
      some (sqCol3part0Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 rest) := by
  have hc (j : Nat) (hj : j ≤ 33) : rest.length + j < 1024 := by omega
  have hcr : rest.length < 1024 := by omega
  simp [hz, hzn, sqCol3part0Program, sqCol3part0Model, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, ofNat_sub_ofNat, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, hc, hcr]

def sqCol3part1Program : List Instr :=
  [.op (.Dup ⟨0, by decide⟩),
   .op .ADD,
   .op .ADD,
   .op (.Dup ⟨12, by decide⟩),
   .op (.Dup ⟨5, by decide⟩),
   .op .MUL,
   .op .ADD,
   .op (.Dup ⟨11, by decide⟩)]

def sqCol3part1Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 : UInt256) (rest : List UInt256) : State :=
  let v0 : UInt256 := x0 + x0
  let v1 : UInt256 := v0 + x1
  let v2 : UInt256 := x5 * x13
  let v3 : UInt256 := v2 + v1
  {s with pc := UInt256.ofNat 4181, memory := s.memory, stack := x12 :: v3 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: rest}

theorem sqCol3part1_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions sqCol3part1Program {s with pc := UInt256.ofNat 4173, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: rest} =
      some (sqCol3part1Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 rest) := by
  have hc (j : Nat) (hj : j ≤ 32) : rest.length + j < 1024 := by omega
  have hcr : rest.length < 1024 := by omega
  simp [hz, hzn, sqCol3part1Program, sqCol3part1Model, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, ofNat_sub_ofNat, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, hc, hcr]

def sqCol3part2Program : List Instr :=
  [.op (.Dup ⟨4, by decide⟩),
   .op .MUL,
   .op .ADD,
   .op (.Dup ⟨10, by decide⟩),
   .op (.Dup ⟨3, by decide⟩),
   .op .MUL,
   .op .ADD,
   .op (.Dup ⟨15, by decide⟩)]

def sqCol3part2Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 : UInt256) (rest : List UInt256) : State :=
  let v0 : UInt256 := x4 * x0
  let v1 : UInt256 := v0 + x1
  let v2 : UInt256 := x3 * x11
  let v3 : UInt256 := v2 + v1
  {s with pc := UInt256.ofNat 4189, memory := s.memory, stack := x16 :: v3 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: rest}

theorem sqCol3part2_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions sqCol3part2Program {s with pc := UInt256.ofNat 4181, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: rest} =
      some (sqCol3part2Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 rest) := by
  have hc (j : Nat) (hj : j ≤ 32) : rest.length + j < 1024 := by omega
  have hcr : rest.length < 1024 := by omega
  simp [hz, hzn, sqCol3part2Program, sqCol3part2Model, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, ofNat_sub_ofNat, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, hc, hcr]

def sqCol3part3Program : List Instr :=
  [.op .MUL,
   .push 1 16,
   .op .SHR,
   .op (.Swap ⟨0, by decide⟩),
   .op (.Dup ⟨14, by decide⟩),
   .op (.Dup ⟨9, by decide⟩),
   .op (.Dup ⟨7, by decide⟩),
   .op .MULMOD]

def sqCol3part3Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 : UInt256) (rest : List UInt256) : State :=
  let v0 : UInt256 := x0 * x1
  let v1 : UInt256 := UInt256.shiftRight v0 (UInt256.ofNat 16)
  let v2 : UInt256 := UInt256.mulMod x6 x9 x15
  {s with pc := UInt256.ofNat 4198, memory := s.memory, stack := v2 :: x2 :: v1 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: rest}

theorem sqCol3part3_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions sqCol3part3Program {s with pc := UInt256.ofNat 4189, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: rest} =
      some (sqCol3part3Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 rest) := by
  have hc (j : Nat) (hj : j ≤ 33) : rest.length + j < 1024 := by omega
  have hcr : rest.length < 1024 := by omega
  simp [hz, hzn, sqCol3part3Program, sqCol3part3Model, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, ofNat_sub_ofNat, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, hc, hcr]

def sqCol3part4Program : List Instr :=
  [.op (.Dup ⟨15, by decide⟩),
   .op (.Dup ⟨9, by decide⟩),
   .op (.Dup ⟨9, by decide⟩),
   .op .MULMOD,
   .op .ADD,
   .op (.Dup ⟨0, by decide⟩),
   .op .ADD,
   .op .ADD]

def sqCol3part4Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 : UInt256) (rest : List UInt256) : State :=
  let v0 : UInt256 := UInt256.mulMod x7 x8 x15
  let v1 : UInt256 := v0 + x0
  let v2 : UInt256 := v1 + v1
  let v3 : UInt256 := v2 + x1
  {s with pc := UInt256.ofNat 4206, memory := s.memory, stack := v3 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: rest}

theorem sqCol3part4_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions sqCol3part4Program {s with pc := UInt256.ofNat 4198, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: rest} =
      some (sqCol3part4Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 rest) := by
  have hc (j : Nat) (hj : j ≤ 34) : rest.length + j < 1024 := by omega
  have hcr : rest.length < 1024 := by omega
  simp [hz, hzn, sqCol3part4Program, sqCol3part4Model, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, ofNat_sub_ofNat, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, hc, hcr]

def sqCol3part5Program : List Instr :=
  [.op (.Dup ⟨14, by decide⟩),
   .op (.Dup ⟨13, by decide⟩),
   .op (.Dup ⟨6, by decide⟩),
   .op .MULMOD,
   .op .ADD,
   .op (.Dup ⟨14, by decide⟩),
   .op (.Dup ⟨12, by decide⟩),
   .op (.Dup ⟨5, by decide⟩)]

def sqCol3part5Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 : UInt256) (rest : List UInt256) : State :=
  let v0 : UInt256 := UInt256.mulMod x4 x12 x14
  let v1 : UInt256 := v0 + x0
  {s with pc := UInt256.ofNat 4214, memory := s.memory, stack := x3 :: x11 :: x14 :: v1 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: rest}

theorem sqCol3part5_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions sqCol3part5Program {s with pc := UInt256.ofNat 4206, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: rest} =
      some (sqCol3part5Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 rest) := by
  have hc (j : Nat) (hj : j ≤ 33) : rest.length + j < 1024 := by omega
  have hcr : rest.length < 1024 := by omega
  simp [hz, hzn, sqCol3part5Program, sqCol3part5Model, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, ofNat_sub_ofNat, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, hc, hcr]

def sqCol3part6Program : List Instr :=
  [.op .MULMOD,
   .op .ADD,
   .op (.Dup ⟨14, by decide⟩),
   .op (.Dup ⟨11, by decide⟩),
   .op (.Dup ⟨4, by decide⟩),
   .op .MULMOD,
   .op .ADD,
   .op (.Dup ⟨14, by decide⟩)]

def sqCol3part6Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 : UInt256) (rest : List UInt256) : State :=
  let v0 : UInt256 := UInt256.mulMod x0 x1 x2
  let v1 : UInt256 := v0 + x3
  let v2 : UInt256 := UInt256.mulMod x5 x13 x17
  let v3 : UInt256 := v2 + v1
  {s with pc := UInt256.ofNat 4222, memory := s.memory, stack := x17 :: v3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: x18 :: x19 :: rest}

theorem sqCol3part6_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions sqCol3part6Program {s with pc := UInt256.ofNat 4214, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: x18 :: x19 :: rest} =
      some (sqCol3part6Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 rest) := by
  have hc (j : Nat) (hj : j ≤ 33) : rest.length + j < 1024 := by omega
  have hcr : rest.length < 1024 := by omega
  simp [hz, hzn, sqCol3part6Program, sqCol3part6Model, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, ofNat_sub_ofNat, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, hc, hcr]

def sqCol3part7Program : List Instr :=
  [.push 1 160,
   .op .MLOAD,
   .op (.Dup ⟨3, by decide⟩),
   .op .MULMOD,
   .op .ADD,
   .op (.Dup ⟨14, by decide⟩),
   .op (.Swap ⟨0, by decide⟩)]

def sqCol3part7Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 : UInt256) (rest : List UInt256) : State :=
  let v0 : UInt256 := MachineState.readWord s.memory 160
  let v1 : UInt256 := UInt256.mulMod x2 v0 x0
  let v2 : UInt256 := v1 + x1
  {s with pc := UInt256.ofNat 4230, memory := s.memory, stack := v2 :: x15 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: rest}

theorem sqCol3part7_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions sqCol3part7Program {s with pc := UInt256.ofNat 4222, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: rest} =
      some (sqCol3part7Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 rest) := by
  have hc (j : Nat) (hj : j ≤ 33) : rest.length + j < 1024 := by omega
  have hcr : rest.length < 1024 := by omega
  have ha160 : (160 : UInt256).toNat = 160 := rfl
  have hf160 := activeWords_fix s 160 32 (by decide) (by norm_num) hact
  simp [hz, hzn, sqCol3part7Program, sqCol3part7Model, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, ofNat_sub_ofNat, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, hc, hcr, ha160, hf160]

def sqCol3part8Program : List Instr :=
  [.push 2 2048,
   .op .MULMOD]

def sqCol3part8Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 : UInt256) (rest : List UInt256) : State :=
  let v0 : UInt256 := UInt256.mulMod (UInt256.ofNat 2048) x0 x1
  {s with pc := UInt256.ofNat 4234, memory := s.memory, stack := v0 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: rest}

theorem sqCol3part8_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions sqCol3part8Program {s with pc := UInt256.ofNat 4230, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: rest} =
      some (sqCol3part8Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 rest) := by
  have hc (j : Nat) (hj : j ≤ 32) : rest.length + j < 1024 := by omega
  have hcr : rest.length < 1024 := by omega
  simp [hz, hzn, sqCol3part8Program, sqCol3part8Model, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, ofNat_sub_ofNat, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, hc, hcr]

def sqCol3Program : List Instr :=
  [.op (.Dup ⟨0, by decide⟩),
   .op (.Dup ⟨8, by decide⟩),
   .op (.Dup ⟨6, by decide⟩),
   .op .MUL,
   .op (.Dup ⟨8, by decide⟩),
   .op (.Dup ⟨8, by decide⟩),
   .op .MUL,
   .op .ADD,
   .op (.Dup ⟨0, by decide⟩),
   .op .ADD,
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
   .op (.Dup ⟨9, by decide⟩),
   .op (.Dup ⟨7, by decide⟩),
   .op .MULMOD,
   .op (.Dup ⟨15, by decide⟩),
   .op (.Dup ⟨9, by decide⟩),
   .op (.Dup ⟨9, by decide⟩),
   .op .MULMOD,
   .op .ADD,
   .op (.Dup ⟨0, by decide⟩),
   .op .ADD,
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

def sqCol3Model (s : State) (c q2 q1 q0 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cnt : UInt256) (rest : List UInt256) : State :=
  let v0 : UInt256 := x0 * x3
  let v1 : UInt256 := x1 * x2
  let v2 : UInt256 := v1 + v0
  let v3 : UInt256 := v2 + v2
  let v4 : UInt256 := v3 + c
  let v5 : UInt256 := q0 * n3
  let v6 : UInt256 := v5 + v4
  let v7 : UInt256 := q1 * n2
  let v8 : UInt256 := v7 + v6
  let v9 : UInt256 := q2 * n1
  let v10 : UInt256 := v9 + v8
  let v11 : UInt256 := inv * v10
  let v12 : UInt256 := UInt256.shiftRight v11 (UInt256.ofNat 16)
  let v13 : UInt256 := UInt256.mulMod x0 x3 P
  let v14 : UInt256 := UInt256.mulMod x1 x2 P
  let v15 : UInt256 := v14 + v13
  let v16 : UInt256 := v15 + v15
  let v17 : UInt256 := v16 + c
  let v18 : UInt256 := UInt256.mulMod q0 n3 P
  let v19 : UInt256 := v18 + v17
  let v20 : UInt256 := UInt256.mulMod q1 n2 P
  let v21 : UInt256 := v20 + v19
  let v22 : UInt256 := UInt256.mulMod q2 n1 P
  let v23 : UInt256 := v22 + v21
  let v24 : UInt256 := MachineState.readWord s.memory 160
  let v25 : UInt256 := UInt256.mulMod v12 v24 P
  let v26 : UInt256 := v25 + v23
  let v27 : UInt256 := UInt256.mulMod (UInt256.ofNat 2048) v26 P
  {s with pc := UInt256.ofNat 4234, memory := s.memory, stack := v27 :: v12 :: q2 :: q1 :: q0 :: x0 :: x1 :: x2 :: x3 :: x4 :: n1 :: n2 :: n3 :: n4 :: P :: inv :: cnt :: rest}

theorem sqCol3_run (s : State) (c q2 q1 q0 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cnt : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions sqCol3Program {s with pc := UInt256.ofNat 4165, stack := c :: q2 :: q1 :: q0 :: x0 :: x1 :: x2 :: x3 :: x4 :: n1 :: n2 :: n3 :: n4 :: P :: inv :: cnt :: rest} =
      some (sqCol3Model s c q2 q1 q0 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cnt rest) := by
  let v0 : UInt256 := x0 * x3
  let v1 : UInt256 := x1 * x2
  let v2 : UInt256 := v1 + v0
  let v3 : UInt256 := v2 + v2
  let v4 : UInt256 := v3 + c
  let v5 : UInt256 := q0 * n3
  let v6 : UInt256 := v5 + v4
  let v7 : UInt256 := q1 * n2
  let v8 : UInt256 := v7 + v6
  let v9 : UInt256 := q2 * n1
  let v10 : UInt256 := v9 + v8
  let v11 : UInt256 := inv * v10
  let v12 : UInt256 := UInt256.shiftRight v11 (UInt256.ofNat 16)
  let v13 : UInt256 := UInt256.mulMod x0 x3 P
  let v14 : UInt256 := UInt256.mulMod x1 x2 P
  let v15 : UInt256 := v14 + v13
  let v16 : UInt256 := v15 + v15
  let v17 : UInt256 := v16 + c
  let v18 : UInt256 := UInt256.mulMod q0 n3 P
  let v19 : UInt256 := v18 + v17
  let v20 : UInt256 := UInt256.mulMod q1 n2 P
  let v21 : UInt256 := v20 + v19
  let v22 : UInt256 := UInt256.mulMod q2 n1 P
  let v23 : UInt256 := v22 + v21
  let v24 : UInt256 := MachineState.readWord s.memory 160
  let v25 : UInt256 := UInt256.mulMod v12 v24 P
  let v26 : UInt256 := v25 + v23
  let v27 : UInt256 := UInt256.mulMod (UInt256.ofNat 2048) v26 P
  have h0 : runInstructions sqCol3part0Program {s with pc := UInt256.ofNat 4165, memory := s.memory, stack := c :: q2 :: q1 :: q0 :: x0 :: x1 :: x2 :: x3 :: x4 :: n1 :: n2 :: n3 :: n4 :: P :: inv :: cnt :: rest} = some {s with pc := UInt256.ofNat 4173, memory := s.memory, stack := v2 :: c :: c :: q2 :: q1 :: q0 :: x0 :: x1 :: x2 :: x3 :: x4 :: n1 :: n2 :: n3 :: n4 :: P :: inv :: cnt :: rest} := by
    simpa only [sqCol3part0Model, v0, v1, v2] using sqCol3part0_run (s) c q2 q1 q0 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cnt rest hcap hact
  have h1 : runInstructions sqCol3part1Program {s with pc := UInt256.ofNat 4173, memory := s.memory, stack := v2 :: c :: c :: q2 :: q1 :: q0 :: x0 :: x1 :: x2 :: x3 :: x4 :: n1 :: n2 :: n3 :: n4 :: P :: inv :: cnt :: rest} = some {s with pc := UInt256.ofNat 4181, memory := s.memory, stack := n2 :: v6 :: c :: q2 :: q1 :: q0 :: x0 :: x1 :: x2 :: x3 :: x4 :: n1 :: n2 :: n3 :: n4 :: P :: inv :: cnt :: rest} := by
    simpa only [sqCol3part1Model, v3, v4, v5, v6] using sqCol3part1_run (s) v2 c c q2 q1 q0 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cnt rest hcap hact
  have h2 : runInstructions sqCol3part2Program {s with pc := UInt256.ofNat 4181, memory := s.memory, stack := n2 :: v6 :: c :: q2 :: q1 :: q0 :: x0 :: x1 :: x2 :: x3 :: x4 :: n1 :: n2 :: n3 :: n4 :: P :: inv :: cnt :: rest} = some {s with pc := UInt256.ofNat 4189, memory := s.memory, stack := inv :: v10 :: c :: q2 :: q1 :: q0 :: x0 :: x1 :: x2 :: x3 :: x4 :: n1 :: n2 :: n3 :: n4 :: P :: inv :: cnt :: rest} := by
    simpa only [sqCol3part2Model, v7, v8, v9, v10] using sqCol3part2_run (s) n2 v6 c q2 q1 q0 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cnt rest hcap hact
  have h3 : runInstructions sqCol3part3Program {s with pc := UInt256.ofNat 4189, memory := s.memory, stack := inv :: v10 :: c :: q2 :: q1 :: q0 :: x0 :: x1 :: x2 :: x3 :: x4 :: n1 :: n2 :: n3 :: n4 :: P :: inv :: cnt :: rest} = some {s with pc := UInt256.ofNat 4198, memory := s.memory, stack := v13 :: c :: v12 :: q2 :: q1 :: q0 :: x0 :: x1 :: x2 :: x3 :: x4 :: n1 :: n2 :: n3 :: n4 :: P :: inv :: cnt :: rest} := by
    simpa only [sqCol3part3Model, v11, v12, v13] using sqCol3part3_run (s) inv v10 c q2 q1 q0 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cnt rest hcap hact
  have h4 : runInstructions sqCol3part4Program {s with pc := UInt256.ofNat 4198, memory := s.memory, stack := v13 :: c :: v12 :: q2 :: q1 :: q0 :: x0 :: x1 :: x2 :: x3 :: x4 :: n1 :: n2 :: n3 :: n4 :: P :: inv :: cnt :: rest} = some {s with pc := UInt256.ofNat 4206, memory := s.memory, stack := v17 :: v12 :: q2 :: q1 :: q0 :: x0 :: x1 :: x2 :: x3 :: x4 :: n1 :: n2 :: n3 :: n4 :: P :: inv :: cnt :: rest} := by
    simpa only [sqCol3part4Model, v14, v15, v16, v17] using sqCol3part4_run (s) v13 c v12 q2 q1 q0 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cnt rest hcap hact
  have h5 : runInstructions sqCol3part5Program {s with pc := UInt256.ofNat 4206, memory := s.memory, stack := v17 :: v12 :: q2 :: q1 :: q0 :: x0 :: x1 :: x2 :: x3 :: x4 :: n1 :: n2 :: n3 :: n4 :: P :: inv :: cnt :: rest} = some {s with pc := UInt256.ofNat 4214, memory := s.memory, stack := q1 :: n2 :: P :: v19 :: v12 :: q2 :: q1 :: q0 :: x0 :: x1 :: x2 :: x3 :: x4 :: n1 :: n2 :: n3 :: n4 :: P :: inv :: cnt :: rest} := by
    simpa only [sqCol3part5Model, v18, v19] using sqCol3part5_run (s) v17 v12 q2 q1 q0 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cnt rest hcap hact
  have h6 : runInstructions sqCol3part6Program {s with pc := UInt256.ofNat 4214, memory := s.memory, stack := q1 :: n2 :: P :: v19 :: v12 :: q2 :: q1 :: q0 :: x0 :: x1 :: x2 :: x3 :: x4 :: n1 :: n2 :: n3 :: n4 :: P :: inv :: cnt :: rest} = some {s with pc := UInt256.ofNat 4222, memory := s.memory, stack := P :: v23 :: v12 :: q2 :: q1 :: q0 :: x0 :: x1 :: x2 :: x3 :: x4 :: n1 :: n2 :: n3 :: n4 :: P :: inv :: cnt :: rest} := by
    simpa only [sqCol3part6Model, v20, v21, v22, v23] using sqCol3part6_run (s) q1 n2 P v19 v12 q2 q1 q0 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cnt rest hcap hact
  have h7 : runInstructions sqCol3part7Program {s with pc := UInt256.ofNat 4222, memory := s.memory, stack := P :: v23 :: v12 :: q2 :: q1 :: q0 :: x0 :: x1 :: x2 :: x3 :: x4 :: n1 :: n2 :: n3 :: n4 :: P :: inv :: cnt :: rest} = some {s with pc := UInt256.ofNat 4230, memory := s.memory, stack := v26 :: P :: v12 :: q2 :: q1 :: q0 :: x0 :: x1 :: x2 :: x3 :: x4 :: n1 :: n2 :: n3 :: n4 :: P :: inv :: cnt :: rest} := by
    simpa only [sqCol3part7Model, v24, v25, v26] using sqCol3part7_run (s) P v23 v12 q2 q1 q0 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cnt rest hcap hact
  have h8 : runInstructions sqCol3part8Program {s with pc := UInt256.ofNat 4230, memory := s.memory, stack := v26 :: P :: v12 :: q2 :: q1 :: q0 :: x0 :: x1 :: x2 :: x3 :: x4 :: n1 :: n2 :: n3 :: n4 :: P :: inv :: cnt :: rest} = some {s with pc := UInt256.ofNat 4234, memory := s.memory, stack := v27 :: v12 :: q2 :: q1 :: q0 :: x0 :: x1 :: x2 :: x3 :: x4 :: n1 :: n2 :: n3 :: n4 :: P :: inv :: cnt :: rest} := by
    simpa only [sqCol3part8Model, v27] using sqCol3part8_run (s) v26 P v12 q2 q1 q0 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cnt rest hcap hact
  exact (runInstructions_append_some _ _ _ _ _ h0 (runInstructions_append_some _ _ _ _ _ h1 (runInstructions_append_some _ _ _ _ _ h2 (runInstructions_append_some _ _ _ _ _ h3 (runInstructions_append_some _ _ _ _ _ h4 (runInstructions_append_some _ _ _ _ _ h5 (runInstructions_append_some _ _ _ _ _ h6 (runInstructions_append_some _ _ _ _ _ h7 h8))))))))

def sqCol3_o0 (c q2 q1 q0 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cnt n0 : UInt256) : UInt256 :=
  (UInt256.mulMod (UInt256.ofNat 2048) ((UInt256.mulMod (UInt256.shiftRight (inv * ((q2 * n1) + ((q1 * n2) + ((q0 * n3) + ((((x1 * x2) + (x0 * x3)) + ((x1 * x2) + (x0 * x3))) + c))))) (UInt256.ofNat 16)) n0 P) + ((UInt256.mulMod q2 n1 P) + ((UInt256.mulMod q1 n2 P) + ((UInt256.mulMod q0 n3 P) + ((((UInt256.mulMod x1 x2 P) + (UInt256.mulMod x0 x3 P)) + ((UInt256.mulMod x1 x2 P) + (UInt256.mulMod x0 x3 P))) + c))))) P)

def sqCol3_o1 (c q2 q1 q0 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cnt n0 : UInt256) : UInt256 :=
  (UInt256.shiftRight (inv * ((q2 * n1) + ((q1 * n2) + ((q0 * n3) + ((((x1 * x2) + (x0 * x3)) + ((x1 * x2) + (x0 * x3))) + c))))) (UInt256.ofNat 16))

theorem sqCol3_eq (s : State) (c q2 q1 q0 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cnt n0 : UInt256) (rest : List UInt256)
    (h_n0 : MachineState.readWord s.memory 160 = n0) :
    sqCol3Model s c q2 q1 q0 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cnt rest =
      {s with pc := UInt256.ofNat 4234, stack := (sqCol3_o0 c q2 q1 q0 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cnt n0) :: (sqCol3_o1 c q2 q1 q0 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cnt n0) :: q2 :: q1 :: q0 :: x0 :: x1 :: x2 :: x3 :: x4 :: n1 :: n2 :: n3 :: n4 :: P :: inv :: cnt :: rest} := by
  simp only [sqCol3Model, sqCol3_o0, sqCol3_o1, h_n0]

/-! ## sqCol4: pc 4234..4329, 90 instructions -/

def sqCol4part0Program : List Instr :=
  [.op (.Dup ⟨0, by decide⟩),
   .op (.Dup ⟨15, by decide⟩),
   .op (.Dup ⟨0, by decide⟩),
   .op (.Dup ⟨12, by decide⟩),
   .op (.Dup ⟨9, by decide⟩),
   .op .MULMOD,
   .op (.Swap ⟨0, by decide⟩),
   .op (.Dup ⟨11, by decide⟩)]

def sqCol4part0Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 : UInt256) (rest : List UInt256) : State :=
  let v0 : UInt256 := UInt256.mulMod x5 x9 x14
  {s with pc := UInt256.ofNat 4242, memory := s.memory, stack := x8 :: x14 :: v0 :: x0 :: x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: rest}

theorem sqCol4part0_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions sqCol4part0Program {s with pc := UInt256.ofNat 4234, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: rest} =
      some (sqCol4part0Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 rest) := by
  have hc (j : Nat) (hj : j ≤ 40) : rest.length + j < 1024 := by omega
  have hcr : rest.length < 1024 := by omega
  simp [hz, hzn, sqCol4part0Program, sqCol4part0Model, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, ofNat_sub_ofNat, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, hc, hcr]

def sqCol4part1Program : List Instr :=
  [.op (.Dup ⟨10, by decide⟩),
   .op .MULMOD,
   .op .ADD,
   .op (.Dup ⟨0, by decide⟩),
   .op .ADD,
   .op .ADD,
   .op .JUMPDEST,
   .op (.Dup ⟨15, by decide⟩)]

def sqCol4part1Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 : UInt256) (rest : List UInt256) : State :=
  let v0 : UInt256 := UInt256.mulMod x10 x0 x1
  let v1 : UInt256 := v0 + x2
  let v2 : UInt256 := v1 + v1
  let v3 : UInt256 := v2 + x3
  {s with pc := UInt256.ofNat 4250, memory := s.memory, stack := x18 :: v3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: x18 :: x19 :: x20 :: rest}

theorem sqCol4part1_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions sqCol4part1Program {s with pc := UInt256.ofNat 4242, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: x18 :: x19 :: x20 :: rest} =
      some (sqCol4part1Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 rest) := by
  have hc (j : Nat) (hj : j ≤ 40) : rest.length + j < 1024 := by omega
  have hcr : rest.length < 1024 := by omega
  simp [hz, hzn, sqCol4part1Program, sqCol4part1Model, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, ofNat_sub_ofNat, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, hc, hcr]

def sqCol4part2Program : List Instr :=
  [.op (.Dup ⟨9, by decide⟩),
   .op (.Dup ⟨0, by decide⟩),
   .op .MULMOD,
   .op .ADD,
   .op (.Dup ⟨15, by decide⟩),
   .op (.Dup ⟨15, by decide⟩),
   .op (.Dup ⟨7, by decide⟩),
   .op .MULMOD]

def sqCol4part2Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 : UInt256) (rest : List UInt256) : State :=
  let v0 : UInt256 := UInt256.mulMod x9 x9 x0
  let v1 : UInt256 := v0 + x1
  let v2 : UInt256 := UInt256.mulMod x6 x15 x16
  {s with pc := UInt256.ofNat 4258, memory := s.memory, stack := v2 :: v1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: x18 :: rest}

theorem sqCol4part2_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions sqCol4part2Program {s with pc := UInt256.ofNat 4250, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: x18 :: rest} =
      some (sqCol4part2Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 rest) := by
  have hc (j : Nat) (hj : j ≤ 40) : rest.length + j < 1024 := by omega
  have hcr : rest.length < 1024 := by omega
  simp [hz, hzn, sqCol4part2Program, sqCol4part2Model, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, ofNat_sub_ofNat, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, hc, hcr]

def sqCol4part3Program : List Instr :=
  [.op .ADD,
   .op (.Dup ⟨15, by decide⟩),
   .op (.Dup ⟨14, by decide⟩),
   .op (.Dup ⟨6, by decide⟩),
   .op .MULMOD,
   .op .ADD,
   .op (.Dup ⟨15, by decide⟩),
   .op (.Dup ⟨13, by decide⟩)]

def sqCol4part3Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 : UInt256) (rest : List UInt256) : State :=
  let v0 : UInt256 := x0 + x1
  let v1 : UInt256 := UInt256.mulMod x5 x14 x16
  let v2 : UInt256 := v1 + v0
  {s with pc := UInt256.ofNat 4266, memory := s.memory, stack := x13 :: x16 :: v2 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: x18 :: rest}

theorem sqCol4part3_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions sqCol4part3Program {s with pc := UInt256.ofNat 4258, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: x18 :: rest} =
      some (sqCol4part3Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 rest) := by
  have hc (j : Nat) (hj : j ≤ 40) : rest.length + j < 1024 := by omega
  have hcr : rest.length < 1024 := by omega
  simp [hz, hzn, sqCol4part3Program, sqCol4part3Model, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, ofNat_sub_ofNat, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, hc, hcr]

def sqCol4part4Program : List Instr :=
  [.op (.Dup ⟨5, by decide⟩),
   .op .MULMOD,
   .op .ADD,
   .op (.Dup ⟨15, by decide⟩),
   .op (.Dup ⟨12, by decide⟩),
   .op (.Dup ⟨4, by decide⟩),
   .op .MULMOD,
   .op .ADD]

def sqCol4part4Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 : UInt256) (rest : List UInt256) : State :=
  let v0 : UInt256 := UInt256.mulMod x5 x0 x1
  let v1 : UInt256 := v0 + x2
  let v2 : UInt256 := UInt256.mulMod x4 x13 x17
  let v3 : UInt256 := v2 + v1
  {s with pc := UInt256.ofNat 4274, memory := s.memory, stack := v3 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: x18 :: x19 :: rest}

theorem sqCol4part4_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions sqCol4part4Program {s with pc := UInt256.ofNat 4266, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: x18 :: x19 :: rest} =
      some (sqCol4part4Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 rest) := by
  have hc (j : Nat) (hj : j ≤ 40) : rest.length + j < 1024 := by omega
  have hcr : rest.length < 1024 := by omega
  simp [hz, hzn, sqCol4part4Program, sqCol4part4Model, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, ofNat_sub_ofNat, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, hc, hcr]

def sqCol4part5Program : List Instr :=
  [.op (.Swap ⟨0, by decide⟩),
   .op (.Dup ⟨10, by decide⟩),
   .op (.Dup ⟨7, by decide⟩),
   .op .MUL,
   .op (.Dup ⟨10, by decide⟩),
   .op (.Dup ⟨9, by decide⟩),
   .op .MUL,
   .op .ADD]

def sqCol4part5Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 : UInt256) (rest : List UInt256) : State :=
  let v0 : UInt256 := x6 * x10
  let v1 : UInt256 := x7 * x9
  let v2 : UInt256 := v1 + v0
  {s with pc := UInt256.ofNat 4282, memory := s.memory, stack := v2 :: x1 :: x0 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: rest}

theorem sqCol4part5_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions sqCol4part5Program {s with pc := UInt256.ofNat 4274, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: rest} =
      some (sqCol4part5Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 rest) := by
  have hc (j : Nat) (hj : j ≤ 40) : rest.length + j < 1024 := by omega
  have hcr : rest.length < 1024 := by omega
  simp [hz, hzn, sqCol4part5Program, sqCol4part5Model, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, ofNat_sub_ofNat, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, hc, hcr]

def sqCol4part6Program : List Instr :=
  [.op (.Dup ⟨0, by decide⟩),
   .op .ADD,
   .op .ADD,
   .op .JUMPDEST,
   .op .JUMPDEST,
   .op (.Dup ⟨8, by decide⟩),
   .op (.Dup ⟨0, by decide⟩),
   .op .MUL]

def sqCol4part6Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 : UInt256) (rest : List UInt256) : State :=
  let v0 : UInt256 := x0 + x0
  let v1 : UInt256 := v0 + x1
  let v2 : UInt256 := x9 * x9
  {s with pc := UInt256.ofNat 4290, memory := s.memory, stack := v2 :: v1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: x18 :: rest}

theorem sqCol4part6_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions sqCol4part6Program {s with pc := UInt256.ofNat 4282, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: x18 :: rest} =
      some (sqCol4part6Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 rest) := by
  have hc (j : Nat) (hj : j ≤ 40) : rest.length + j < 1024 := by omega
  have hcr : rest.length < 1024 := by omega
  simp [hz, hzn, sqCol4part6Program, sqCol4part6Model, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, ofNat_sub_ofNat, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, hc, hcr]

def sqCol4part7Program : List Instr :=
  [.op .ADD,
   .op (.Dup ⟨14, by decide⟩),
   .op (.Dup ⟨6, by decide⟩),
   .op .MUL,
   .op .ADD,
   .op (.Dup ⟨13, by decide⟩),
   .op (.Dup ⟨5, by decide⟩),
   .op .MUL]

def sqCol4part7Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 : UInt256) (rest : List UInt256) : State :=
  let v0 : UInt256 := x0 + x1
  let v1 : UInt256 := x6 * x15
  let v2 : UInt256 := v1 + v0
  let v3 : UInt256 := x5 * x14
  {s with pc := UInt256.ofNat 4298, memory := s.memory, stack := v3 :: v2 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: x18 :: rest}

theorem sqCol4part7_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions sqCol4part7Program {s with pc := UInt256.ofNat 4290, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: x18 :: rest} =
      some (sqCol4part7Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 rest) := by
  have hc (j : Nat) (hj : j ≤ 40) : rest.length + j < 1024 := by omega
  have hcr : rest.length < 1024 := by omega
  simp [hz, hzn, sqCol4part7Program, sqCol4part7Model, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, ofNat_sub_ofNat, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, hc, hcr]

def sqCol4part8Program : List Instr :=
  [.op .ADD,
   .op (.Dup ⟨12, by decide⟩),
   .op (.Dup ⟨4, by decide⟩),
   .op .MUL,
   .op .ADD,
   .op (.Dup ⟨11, by decide⟩),
   .op (.Dup ⟨3, by decide⟩),
   .op .MUL]

def sqCol4part8Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 : UInt256) (rest : List UInt256) : State :=
  let v0 : UInt256 := x0 + x1
  let v1 : UInt256 := x4 * x13
  let v2 : UInt256 := v1 + v0
  let v3 : UInt256 := x3 * x12
  {s with pc := UInt256.ofNat 4306, memory := s.memory, stack := v3 :: v2 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: x18 :: rest}

theorem sqCol4part8_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions sqCol4part8Program {s with pc := UInt256.ofNat 4298, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: x18 :: rest} =
      some (sqCol4part8Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 rest) := by
  have hc (j : Nat) (hj : j ≤ 40) : rest.length + j < 1024 := by omega
  have hcr : rest.length < 1024 := by omega
  simp [hz, hzn, sqCol4part8Program, sqCol4part8Model, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, ofNat_sub_ofNat, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, hc, hcr]

def sqCol4part9Program : List Instr :=
  [.op .ADD,
   .push 1 192,
   .op .MLOAD,
   .op .MUL,
   .push 1 16,
   .op .SHR,
   .op (.Swap ⟨4, by decide⟩),
   .op .POP]

def sqCol4part9Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 : UInt256) (rest : List UInt256) : State :=
  let v0 : UInt256 := x0 + x1
  let v1 : UInt256 := MachineState.readWord s.memory 192
  let v2 : UInt256 := v1 * v0
  let v3 : UInt256 := UInt256.shiftRight v2 (UInt256.ofNat 16)
  {s with pc := UInt256.ofNat 4316, memory := s.memory, stack := x2 :: x3 :: x4 :: x5 :: v3 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: x18 :: rest}

theorem sqCol4part9_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions sqCol4part9Program {s with pc := UInt256.ofNat 4306, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: x18 :: rest} =
      some (sqCol4part9Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 rest) := by
  have hc (j : Nat) (hj : j ≤ 40) : rest.length + j < 1024 := by omega
  have hcr : rest.length < 1024 := by omega
  have ha192 : (192 : UInt256).toNat = 192 := rfl
  have hf192 := activeWords_fix s 192 32 (by decide) (by norm_num) hact
  simp [hz, hzn, sqCol4part9Program, sqCol4part9Model, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, ofNat_sub_ofNat, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, hc, hcr, ha192, hf192]

def sqCol4part10Program : List Instr :=
  [.op (.Dup ⟨14, by decide⟩),
   .push 1 160,
   .op .MLOAD,
   .op (.Dup ⟨6, by decide⟩),
   .op .MULMOD,
   .op .ADD,
   .op (.Dup ⟨14, by decide⟩),
   .op (.Swap ⟨0, by decide⟩)]

def sqCol4part10Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 : UInt256) (rest : List UInt256) : State :=
  let v0 : UInt256 := MachineState.readWord s.memory 160
  let v1 : UInt256 := UInt256.mulMod x4 v0 x14
  let v2 : UInt256 := v1 + x0
  {s with pc := UInt256.ofNat 4325, memory := s.memory, stack := v2 :: x14 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: rest}

theorem sqCol4part10_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions sqCol4part10Program {s with pc := UInt256.ofNat 4316, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: rest} =
      some (sqCol4part10Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 rest) := by
  have hc (j : Nat) (hj : j ≤ 40) : rest.length + j < 1024 := by omega
  have hcr : rest.length < 1024 := by omega
  have ha160 : (160 : UInt256).toNat = 160 := rfl
  have hf160 := activeWords_fix s 160 32 (by decide) (by norm_num) hact
  simp [hz, hzn, sqCol4part10Program, sqCol4part10Model, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, ofNat_sub_ofNat, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, hc, hcr, ha160, hf160]

def sqCol4part11Program : List Instr :=
  [.push 2 2048,
   .op .MULMOD]

def sqCol4part11Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 : UInt256) (rest : List UInt256) : State :=
  let v0 : UInt256 := UInt256.mulMod (UInt256.ofNat 2048) x0 x1
  {s with pc := UInt256.ofNat 4329, memory := s.memory, stack := v0 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: rest}

theorem sqCol4part11_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions sqCol4part11Program {s with pc := UInt256.ofNat 4325, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: rest} =
      some (sqCol4part11Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 rest) := by
  have hc (j : Nat) (hj : j ≤ 40) : rest.length + j < 1024 := by omega
  have hcr : rest.length < 1024 := by omega
  simp [hz, hzn, sqCol4part11Program, sqCol4part11Model, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, ofNat_sub_ofNat, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, hc, hcr]

def sqCol4Program : List Instr :=
  [.op (.Dup ⟨0, by decide⟩),
   .op (.Dup ⟨15, by decide⟩),
   .op (.Dup ⟨0, by decide⟩),
   .op (.Dup ⟨12, by decide⟩),
   .op (.Dup ⟨9, by decide⟩),
   .op .MULMOD,
   .op (.Swap ⟨0, by decide⟩),
   .op (.Dup ⟨11, by decide⟩),
   .op (.Dup ⟨10, by decide⟩),
   .op .MULMOD,
   .op .ADD,
   .op (.Dup ⟨0, by decide⟩),
   .op .ADD,
   .op .ADD,
   .op .JUMPDEST,
   .op (.Dup ⟨15, by decide⟩),
   .op (.Dup ⟨9, by decide⟩),
   .op (.Dup ⟨0, by decide⟩),
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
   .op (.Dup ⟨10, by decide⟩),
   .op (.Dup ⟨7, by decide⟩),
   .op .MUL,
   .op (.Dup ⟨10, by decide⟩),
   .op (.Dup ⟨9, by decide⟩),
   .op .MUL,
   .op .ADD,
   .op (.Dup ⟨0, by decide⟩),
   .op .ADD,
   .op .ADD,
   .op .JUMPDEST,
   .op .JUMPDEST,
   .op (.Dup ⟨8, by decide⟩),
   .op (.Dup ⟨0, by decide⟩),
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

def sqCol4Model (s : State) (c q3 q2 q1 q0 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cnt : UInt256) (rest : List UInt256) : State :=
  let v0 : UInt256 := UInt256.mulMod x0 x4 P
  let v1 : UInt256 := UInt256.mulMod x1 x3 P
  let v2 : UInt256 := v1 + v0
  let v3 : UInt256 := v2 + v2
  let v4 : UInt256 := v3 + c
  let v5 : UInt256 := UInt256.mulMod x2 x2 P
  let v6 : UInt256 := v5 + v4
  let v7 : UInt256 := UInt256.mulMod q0 n4 P
  let v8 : UInt256 := v7 + v6
  let v9 : UInt256 := UInt256.mulMod q1 n3 P
  let v10 : UInt256 := v9 + v8
  let v11 : UInt256 := UInt256.mulMod q2 n2 P
  let v12 : UInt256 := v11 + v10
  let v13 : UInt256 := UInt256.mulMod q3 n1 P
  let v14 : UInt256 := v13 + v12
  let v15 : UInt256 := x0 * x4
  let v16 : UInt256 := x1 * x3
  let v17 : UInt256 := v16 + v15
  let v18 : UInt256 := v17 + v17
  let v19 : UInt256 := v18 + c
  let v20 : UInt256 := x2 * x2
  let v21 : UInt256 := v20 + v19
  let v22 : UInt256 := q0 * n4
  let v23 : UInt256 := v22 + v21
  let v24 : UInt256 := q1 * n3
  let v25 : UInt256 := v24 + v23
  let v26 : UInt256 := q2 * n2
  let v27 : UInt256 := v26 + v25
  let v28 : UInt256 := q3 * n1
  let v29 : UInt256 := v28 + v27
  let v30 : UInt256 := MachineState.readWord s.memory 192
  let v31 : UInt256 := v30 * v29
  let v32 : UInt256 := UInt256.shiftRight v31 (UInt256.ofNat 16)
  let v33 : UInt256 := MachineState.readWord s.memory 160
  let v34 : UInt256 := UInt256.mulMod v32 v33 P
  let v35 : UInt256 := v34 + v14
  let v36 : UInt256 := UInt256.mulMod (UInt256.ofNat 2048) v35 P
  {s with pc := UInt256.ofNat 4329, memory := s.memory, stack := v36 :: q3 :: q2 :: q1 :: v32 :: x0 :: x1 :: x2 :: x3 :: x4 :: n1 :: n2 :: n3 :: n4 :: P :: inv :: cnt :: rest}

theorem sqCol4_run (s : State) (c q3 q2 q1 q0 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cnt : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions sqCol4Program {s with pc := UInt256.ofNat 4234, stack := c :: q3 :: q2 :: q1 :: q0 :: x0 :: x1 :: x2 :: x3 :: x4 :: n1 :: n2 :: n3 :: n4 :: P :: inv :: cnt :: rest} =
      some (sqCol4Model s c q3 q2 q1 q0 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cnt rest) := by
  let v0 : UInt256 := UInt256.mulMod x0 x4 P
  let v1 : UInt256 := UInt256.mulMod x1 x3 P
  let v2 : UInt256 := v1 + v0
  let v3 : UInt256 := v2 + v2
  let v4 : UInt256 := v3 + c
  let v5 : UInt256 := UInt256.mulMod x2 x2 P
  let v6 : UInt256 := v5 + v4
  let v7 : UInt256 := UInt256.mulMod q0 n4 P
  let v8 : UInt256 := v7 + v6
  let v9 : UInt256 := UInt256.mulMod q1 n3 P
  let v10 : UInt256 := v9 + v8
  let v11 : UInt256 := UInt256.mulMod q2 n2 P
  let v12 : UInt256 := v11 + v10
  let v13 : UInt256 := UInt256.mulMod q3 n1 P
  let v14 : UInt256 := v13 + v12
  let v15 : UInt256 := x0 * x4
  let v16 : UInt256 := x1 * x3
  let v17 : UInt256 := v16 + v15
  let v18 : UInt256 := v17 + v17
  let v19 : UInt256 := v18 + c
  let v20 : UInt256 := x2 * x2
  let v21 : UInt256 := v20 + v19
  let v22 : UInt256 := q0 * n4
  let v23 : UInt256 := v22 + v21
  let v24 : UInt256 := q1 * n3
  let v25 : UInt256 := v24 + v23
  let v26 : UInt256 := q2 * n2
  let v27 : UInt256 := v26 + v25
  let v28 : UInt256 := q3 * n1
  let v29 : UInt256 := v28 + v27
  let v30 : UInt256 := MachineState.readWord s.memory 192
  let v31 : UInt256 := v30 * v29
  let v32 : UInt256 := UInt256.shiftRight v31 (UInt256.ofNat 16)
  let v33 : UInt256 := MachineState.readWord s.memory 160
  let v34 : UInt256 := UInt256.mulMod v32 v33 P
  let v35 : UInt256 := v34 + v14
  let v36 : UInt256 := UInt256.mulMod (UInt256.ofNat 2048) v35 P
  have h0 : runInstructions sqCol4part0Program {s with pc := UInt256.ofNat 4234, memory := s.memory, stack := c :: q3 :: q2 :: q1 :: q0 :: x0 :: x1 :: x2 :: x3 :: x4 :: n1 :: n2 :: n3 :: n4 :: P :: inv :: cnt :: rest} = some {s with pc := UInt256.ofNat 4242, memory := s.memory, stack := x3 :: P :: v0 :: c :: c :: q3 :: q2 :: q1 :: q0 :: x0 :: x1 :: x2 :: x3 :: x4 :: n1 :: n2 :: n3 :: n4 :: P :: inv :: cnt :: rest} := by
    simpa only [sqCol4part0Model, v0] using sqCol4part0_run (s) c q3 q2 q1 q0 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cnt rest hcap hact
  have h1 : runInstructions sqCol4part1Program {s with pc := UInt256.ofNat 4242, memory := s.memory, stack := x3 :: P :: v0 :: c :: c :: q3 :: q2 :: q1 :: q0 :: x0 :: x1 :: x2 :: x3 :: x4 :: n1 :: n2 :: n3 :: n4 :: P :: inv :: cnt :: rest} = some {s with pc := UInt256.ofNat 4250, memory := s.memory, stack := P :: v4 :: c :: q3 :: q2 :: q1 :: q0 :: x0 :: x1 :: x2 :: x3 :: x4 :: n1 :: n2 :: n3 :: n4 :: P :: inv :: cnt :: rest} := by
    simpa only [sqCol4part1Model, v1, v2, v3, v4] using sqCol4part1_run (s) x3 P v0 c c q3 q2 q1 q0 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cnt rest hcap hact
  have h2 : runInstructions sqCol4part2Program {s with pc := UInt256.ofNat 4250, memory := s.memory, stack := P :: v4 :: c :: q3 :: q2 :: q1 :: q0 :: x0 :: x1 :: x2 :: x3 :: x4 :: n1 :: n2 :: n3 :: n4 :: P :: inv :: cnt :: rest} = some {s with pc := UInt256.ofNat 4258, memory := s.memory, stack := v7 :: v6 :: c :: q3 :: q2 :: q1 :: q0 :: x0 :: x1 :: x2 :: x3 :: x4 :: n1 :: n2 :: n3 :: n4 :: P :: inv :: cnt :: rest} := by
    simpa only [sqCol4part2Model, v5, v6, v7] using sqCol4part2_run (s) P v4 c q3 q2 q1 q0 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cnt rest hcap hact
  have h3 : runInstructions sqCol4part3Program {s with pc := UInt256.ofNat 4258, memory := s.memory, stack := v7 :: v6 :: c :: q3 :: q2 :: q1 :: q0 :: x0 :: x1 :: x2 :: x3 :: x4 :: n1 :: n2 :: n3 :: n4 :: P :: inv :: cnt :: rest} = some {s with pc := UInt256.ofNat 4266, memory := s.memory, stack := n2 :: P :: v10 :: c :: q3 :: q2 :: q1 :: q0 :: x0 :: x1 :: x2 :: x3 :: x4 :: n1 :: n2 :: n3 :: n4 :: P :: inv :: cnt :: rest} := by
    simpa only [sqCol4part3Model, v8, v9, v10] using sqCol4part3_run (s) v7 v6 c q3 q2 q1 q0 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cnt rest hcap hact
  have h4 : runInstructions sqCol4part4Program {s with pc := UInt256.ofNat 4266, memory := s.memory, stack := n2 :: P :: v10 :: c :: q3 :: q2 :: q1 :: q0 :: x0 :: x1 :: x2 :: x3 :: x4 :: n1 :: n2 :: n3 :: n4 :: P :: inv :: cnt :: rest} = some {s with pc := UInt256.ofNat 4274, memory := s.memory, stack := v14 :: c :: q3 :: q2 :: q1 :: q0 :: x0 :: x1 :: x2 :: x3 :: x4 :: n1 :: n2 :: n3 :: n4 :: P :: inv :: cnt :: rest} := by
    simpa only [sqCol4part4Model, v11, v12, v13, v14] using sqCol4part4_run (s) n2 P v10 c q3 q2 q1 q0 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cnt rest hcap hact
  have h5 : runInstructions sqCol4part5Program {s with pc := UInt256.ofNat 4274, memory := s.memory, stack := v14 :: c :: q3 :: q2 :: q1 :: q0 :: x0 :: x1 :: x2 :: x3 :: x4 :: n1 :: n2 :: n3 :: n4 :: P :: inv :: cnt :: rest} = some {s with pc := UInt256.ofNat 4282, memory := s.memory, stack := v17 :: c :: v14 :: q3 :: q2 :: q1 :: q0 :: x0 :: x1 :: x2 :: x3 :: x4 :: n1 :: n2 :: n3 :: n4 :: P :: inv :: cnt :: rest} := by
    simpa only [sqCol4part5Model, v15, v16, v17] using sqCol4part5_run (s) v14 c q3 q2 q1 q0 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cnt rest hcap hact
  have h6 : runInstructions sqCol4part6Program {s with pc := UInt256.ofNat 4282, memory := s.memory, stack := v17 :: c :: v14 :: q3 :: q2 :: q1 :: q0 :: x0 :: x1 :: x2 :: x3 :: x4 :: n1 :: n2 :: n3 :: n4 :: P :: inv :: cnt :: rest} = some {s with pc := UInt256.ofNat 4290, memory := s.memory, stack := v20 :: v19 :: v14 :: q3 :: q2 :: q1 :: q0 :: x0 :: x1 :: x2 :: x3 :: x4 :: n1 :: n2 :: n3 :: n4 :: P :: inv :: cnt :: rest} := by
    simpa only [sqCol4part6Model, v18, v19, v20] using sqCol4part6_run (s) v17 c v14 q3 q2 q1 q0 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cnt rest hcap hact
  have h7 : runInstructions sqCol4part7Program {s with pc := UInt256.ofNat 4290, memory := s.memory, stack := v20 :: v19 :: v14 :: q3 :: q2 :: q1 :: q0 :: x0 :: x1 :: x2 :: x3 :: x4 :: n1 :: n2 :: n3 :: n4 :: P :: inv :: cnt :: rest} = some {s with pc := UInt256.ofNat 4298, memory := s.memory, stack := v24 :: v23 :: v14 :: q3 :: q2 :: q1 :: q0 :: x0 :: x1 :: x2 :: x3 :: x4 :: n1 :: n2 :: n3 :: n4 :: P :: inv :: cnt :: rest} := by
    simpa only [sqCol4part7Model, v21, v22, v23, v24] using sqCol4part7_run (s) v20 v19 v14 q3 q2 q1 q0 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cnt rest hcap hact
  have h8 : runInstructions sqCol4part8Program {s with pc := UInt256.ofNat 4298, memory := s.memory, stack := v24 :: v23 :: v14 :: q3 :: q2 :: q1 :: q0 :: x0 :: x1 :: x2 :: x3 :: x4 :: n1 :: n2 :: n3 :: n4 :: P :: inv :: cnt :: rest} = some {s with pc := UInt256.ofNat 4306, memory := s.memory, stack := v28 :: v27 :: v14 :: q3 :: q2 :: q1 :: q0 :: x0 :: x1 :: x2 :: x3 :: x4 :: n1 :: n2 :: n3 :: n4 :: P :: inv :: cnt :: rest} := by
    simpa only [sqCol4part8Model, v25, v26, v27, v28] using sqCol4part8_run (s) v24 v23 v14 q3 q2 q1 q0 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cnt rest hcap hact
  have h9 : runInstructions sqCol4part9Program {s with pc := UInt256.ofNat 4306, memory := s.memory, stack := v28 :: v27 :: v14 :: q3 :: q2 :: q1 :: q0 :: x0 :: x1 :: x2 :: x3 :: x4 :: n1 :: n2 :: n3 :: n4 :: P :: inv :: cnt :: rest} = some {s with pc := UInt256.ofNat 4316, memory := s.memory, stack := v14 :: q3 :: q2 :: q1 :: v32 :: x0 :: x1 :: x2 :: x3 :: x4 :: n1 :: n2 :: n3 :: n4 :: P :: inv :: cnt :: rest} := by
    simpa only [sqCol4part9Model, v29, v30, v31, v32] using sqCol4part9_run (s) v28 v27 v14 q3 q2 q1 q0 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cnt rest hcap hact
  have h10 : runInstructions sqCol4part10Program {s with pc := UInt256.ofNat 4316, memory := s.memory, stack := v14 :: q3 :: q2 :: q1 :: v32 :: x0 :: x1 :: x2 :: x3 :: x4 :: n1 :: n2 :: n3 :: n4 :: P :: inv :: cnt :: rest} = some {s with pc := UInt256.ofNat 4325, memory := s.memory, stack := v35 :: P :: q3 :: q2 :: q1 :: v32 :: x0 :: x1 :: x2 :: x3 :: x4 :: n1 :: n2 :: n3 :: n4 :: P :: inv :: cnt :: rest} := by
    simpa only [sqCol4part10Model, v33, v34, v35] using sqCol4part10_run (s) v14 q3 q2 q1 v32 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cnt rest hcap hact
  have h11 : runInstructions sqCol4part11Program {s with pc := UInt256.ofNat 4325, memory := s.memory, stack := v35 :: P :: q3 :: q2 :: q1 :: v32 :: x0 :: x1 :: x2 :: x3 :: x4 :: n1 :: n2 :: n3 :: n4 :: P :: inv :: cnt :: rest} = some {s with pc := UInt256.ofNat 4329, memory := s.memory, stack := v36 :: q3 :: q2 :: q1 :: v32 :: x0 :: x1 :: x2 :: x3 :: x4 :: n1 :: n2 :: n3 :: n4 :: P :: inv :: cnt :: rest} := by
    simpa only [sqCol4part11Model, v36] using sqCol4part11_run (s) v35 P q3 q2 q1 v32 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cnt rest hcap hact
  exact (runInstructions_append_some _ _ _ _ _ h0 (runInstructions_append_some _ _ _ _ _ h1 (runInstructions_append_some _ _ _ _ _ h2 (runInstructions_append_some _ _ _ _ _ h3 (runInstructions_append_some _ _ _ _ _ h4 (runInstructions_append_some _ _ _ _ _ h5 (runInstructions_append_some _ _ _ _ _ h6 (runInstructions_append_some _ _ _ _ _ h7 (runInstructions_append_some _ _ _ _ _ h8 (runInstructions_append_some _ _ _ _ _ h9 (runInstructions_append_some _ _ _ _ _ h10 h11)))))))))))

def sqCol4_o0 (c q3 q2 q1 q0 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cnt n0 : UInt256) : UInt256 :=
  (UInt256.mulMod (UInt256.ofNat 2048) ((UInt256.mulMod (UInt256.shiftRight (inv * ((q3 * n1) + ((q2 * n2) + ((q1 * n3) + ((q0 * n4) + ((x2 * x2) + (((x1 * x3) + (x1 * x3)) + (((x0 * x4) + (x0 * x4)) + c)))))))) (UInt256.ofNat 16)) n0 P) + ((UInt256.mulMod q3 n1 P) + ((UInt256.mulMod q2 n2 P) + ((UInt256.mulMod q1 n3 P) + ((UInt256.mulMod q0 n4 P) + ((UInt256.mulMod x2 x2 P) + (((UInt256.mulMod x1 x3 P) + (UInt256.mulMod x1 x3 P)) + (((UInt256.mulMod x0 x4 P) + (UInt256.mulMod x0 x4 P)) + c)))))))) P)

def sqCol4_o4 (c q3 q2 q1 q0 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cnt n0 : UInt256) : UInt256 :=
  (UInt256.shiftRight (inv * ((q3 * n1) + ((q2 * n2) + ((q1 * n3) + ((q0 * n4) + ((x2 * x2) + (((x1 * x3) + (x1 * x3)) + (((x0 * x4) + (x0 * x4)) + c)))))))) (UInt256.ofNat 16))

theorem sqCol4_eq (s : State) (c q3 q2 q1 q0 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cnt n0 : UInt256) (rest : List UInt256)
    (h_n0 : MachineState.readWord s.memory 160 = n0)
    (h_inv : MachineState.readWord s.memory 192 = inv) :
    sqCol4Model s c q3 q2 q1 q0 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cnt rest =
      {s with pc := UInt256.ofNat 4329, stack := (sqCol4_o0 c q3 q2 q1 q0 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cnt n0) :: q3 :: q2 :: q1 :: (sqCol4_o4 c q3 q2 q1 q0 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cnt n0) :: x0 :: x1 :: x2 :: x3 :: x4 :: n1 :: n2 :: n3 :: n4 :: P :: inv :: cnt :: rest} := by
  simp only [sqCol4Model, sqCol4_o0, sqCol4_o4, h_n0, h_inv, fusePair]

/-! ## sqCol5: pc 4329..4444, 82 instructions -/

def sqCol5part0Program : List Instr :=
  [.op (.Dup ⟨0, by decide⟩),
   .op (.Dup ⟨10, by decide⟩),
   .op (.Dup ⟨8, by decide⟩),
   .op .MUL,
   .op (.Dup ⟨10, by decide⟩),
   .op (.Dup ⟨10, by decide⟩),
   .op .MUL,
   .op .ADD]

def sqCol5part0Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 : UInt256) (rest : List UInt256) : State :=
  let v0 : UInt256 := x6 * x9
  let v1 : UInt256 := x7 * x8
  let v2 : UInt256 := v1 + v0
  {s with pc := UInt256.ofNat 4337, memory := s.memory, stack := v2 :: x0 :: x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: rest}

theorem sqCol5part0_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions sqCol5part0Program {s with pc := UInt256.ofNat 4329, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: rest} =
      some (sqCol5part0Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 rest) := by
  have hc (j : Nat) (hj : j ≤ 40) : rest.length + j < 1024 := by omega
  have hcr : rest.length < 1024 := by omega
  simp [hz, hzn, sqCol5part0Program, sqCol5part0Model, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, ofNat_sub_ofNat, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, hc, hcr]

def sqCol5part1Program : List Instr :=
  [.op (.Dup ⟨0, by decide⟩),
   .op .ADD,
   .op .ADD,
   .op .JUMPDEST,
   .op .JUMPDEST,
   .op (.Dup ⟨14, by decide⟩),
   .op (.Dup ⟨5, by decide⟩),
   .op .MUL]

def sqCol5part1Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 : UInt256) (rest : List UInt256) : State :=
  let v0 : UInt256 := x0 + x0
  let v1 : UInt256 := v0 + x1
  let v2 : UInt256 := x5 * x15
  {s with pc := UInt256.ofNat 4345, memory := s.memory, stack := v2 :: v1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: x18 :: rest}

theorem sqCol5part1_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions sqCol5part1Program {s with pc := UInt256.ofNat 4337, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: x18 :: rest} =
      some (sqCol5part1Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 rest) := by
  have hc (j : Nat) (hj : j ≤ 40) : rest.length + j < 1024 := by omega
  have hcr : rest.length < 1024 := by omega
  simp [hz, hzn, sqCol5part1Program, sqCol5part1Model, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, ofNat_sub_ofNat, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, hc, hcr]

def sqCol5part2Program : List Instr :=
  [.op .ADD,
   .op (.Dup ⟨13, by decide⟩),
   .op (.Dup ⟨4, by decide⟩),
   .op .MUL,
   .op .ADD,
   .op (.Dup ⟨12, by decide⟩),
   .op (.Dup ⟨3, by decide⟩),
   .op .MUL]

def sqCol5part2Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 : UInt256) (rest : List UInt256) : State :=
  let v0 : UInt256 := x0 + x1
  let v1 : UInt256 := x4 * x14
  let v2 : UInt256 := v1 + v0
  let v3 : UInt256 := x3 * x13
  {s with pc := UInt256.ofNat 4353, memory := s.memory, stack := v3 :: v2 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: x18 :: rest}

theorem sqCol5part2_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions sqCol5part2Program {s with pc := UInt256.ofNat 4345, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: x18 :: rest} =
      some (sqCol5part2Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 rest) := by
  have hc (j : Nat) (hj : j ≤ 40) : rest.length + j < 1024 := by omega
  have hcr : rest.length < 1024 := by omega
  simp [hz, hzn, sqCol5part2Program, sqCol5part2Model, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, ofNat_sub_ofNat, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, hc, hcr]

def sqCol5part3Program : List Instr :=
  [.op .ADD,
   .op (.Dup ⟨11, by decide⟩),
   .op (.Dup ⟨6, by decide⟩),
   .op .MUL,
   .op .ADD,
   .op (.Swap ⟨0, by decide⟩),
   .op (.Dup ⟨15, by decide⟩),
   .op (.Dup ⟨0, by decide⟩)]

def sqCol5part3Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 : UInt256) (rest : List UInt256) : State :=
  let v0 : UInt256 := x0 + x1
  let v1 : UInt256 := x6 * x12
  let v2 : UInt256 := v1 + v0
  {s with pc := UInt256.ofNat 4361, memory := s.memory, stack := x16 :: x16 :: x2 :: v2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: x18 :: rest}

theorem sqCol5part3_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions sqCol5part3Program {s with pc := UInt256.ofNat 4353, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: x18 :: rest} =
      some (sqCol5part3Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 rest) := by
  have hc (j : Nat) (hj : j ≤ 40) : rest.length + j < 1024 := by omega
  have hcr : rest.length < 1024 := by omega
  simp [hz, hzn, sqCol5part3Program, sqCol5part3Model, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, ofNat_sub_ofNat, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, hc, hcr]

def sqCol5part4Program : List Instr :=
  [.op (.Dup ⟨12, by decide⟩),
   .op (.Dup ⟨10, by decide⟩),
   .op .MULMOD,
   .op (.Swap ⟨0, by decide⟩),
   .op (.Dup ⟨11, by decide⟩),
   .op (.Dup ⟨11, by decide⟩),
   .op .MULMOD,
   .op .ADD]

def sqCol5part4Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 : UInt256) (rest : List UInt256) : State :=
  let v0 : UInt256 := UInt256.mulMod x9 x12 x0
  let v1 : UInt256 := UInt256.mulMod x10 x11 x1
  let v2 : UInt256 := v1 + v0
  {s with pc := UInt256.ofNat 4369, memory := s.memory, stack := v2 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: x18 :: x19 :: rest}

theorem sqCol5part4_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions sqCol5part4Program {s with pc := UInt256.ofNat 4361, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: x18 :: x19 :: rest} =
      some (sqCol5part4Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 rest) := by
  have hc (j : Nat) (hj : j ≤ 40) : rest.length + j < 1024 := by omega
  have hcr : rest.length < 1024 := by omega
  simp [hz, hzn, sqCol5part4Program, sqCol5part4Model, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, ofNat_sub_ofNat, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, hc, hcr]

def sqCol5part5Program : List Instr :=
  [.op (.Dup ⟨0, by decide⟩),
   .op .ADD,
   .op .ADD,
   .op .JUMPDEST,
   .op (.Dup ⟨15, by decide⟩),
   .op (.Dup ⟨15, by decide⟩),
   .op (.Dup ⟨6, by decide⟩),
   .op .MULMOD]

def sqCol5part5Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 : UInt256) (rest : List UInt256) : State :=
  let v0 : UInt256 := x0 + x0
  let v1 : UInt256 := v0 + x1
  let v2 : UInt256 := UInt256.mulMod x5 x15 x16
  {s with pc := UInt256.ofNat 4377, memory := s.memory, stack := v2 :: v1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: x18 :: rest}

theorem sqCol5part5_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions sqCol5part5Program {s with pc := UInt256.ofNat 4369, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: x18 :: rest} =
      some (sqCol5part5Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 rest) := by
  have hc (j : Nat) (hj : j ≤ 40) : rest.length + j < 1024 := by omega
  have hcr : rest.length < 1024 := by omega
  simp [hz, hzn, sqCol5part5Program, sqCol5part5Model, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, ofNat_sub_ofNat, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, hc, hcr]

def sqCol5part6Program : List Instr :=
  [.op .ADD,
   .op (.Dup ⟨15, by decide⟩),
   .op (.Dup ⟨14, by decide⟩),
   .op (.Dup ⟨5, by decide⟩),
   .op .MULMOD,
   .op .ADD,
   .op (.Dup ⟨15, by decide⟩),
   .op (.Dup ⟨13, by decide⟩)]

def sqCol5part6Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 : UInt256) (rest : List UInt256) : State :=
  let v0 : UInt256 := x0 + x1
  let v1 : UInt256 := UInt256.mulMod x4 x14 x16
  let v2 : UInt256 := v1 + v0
  {s with pc := UInt256.ofNat 4385, memory := s.memory, stack := x13 :: x16 :: v2 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: x18 :: rest}

theorem sqCol5part6_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions sqCol5part6Program {s with pc := UInt256.ofNat 4377, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: x18 :: rest} =
      some (sqCol5part6Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 rest) := by
  have hc (j : Nat) (hj : j ≤ 40) : rest.length + j < 1024 := by omega
  have hcr : rest.length < 1024 := by omega
  simp [hz, hzn, sqCol5part6Program, sqCol5part6Model, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, ofNat_sub_ofNat, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, hc, hcr]

def sqCol5part7Program : List Instr :=
  [.op (.Dup ⟨4, by decide⟩),
   .op .MULMOD,
   .op .ADD,
   .op (.Dup ⟨15, by decide⟩),
   .op (.Dup ⟨12, by decide⟩),
   .op (.Dup ⟨7, by decide⟩),
   .op .MULMOD,
   .op .ADD]

def sqCol5part7Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 : UInt256) (rest : List UInt256) : State :=
  let v0 : UInt256 := UInt256.mulMod x4 x0 x1
  let v1 : UInt256 := v0 + x2
  let v2 : UInt256 := UInt256.mulMod x7 x13 x17
  let v3 : UInt256 := v2 + v1
  {s with pc := UInt256.ofNat 4393, memory := s.memory, stack := v3 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: x18 :: x19 :: rest}

theorem sqCol5part7_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions sqCol5part7Program {s with pc := UInt256.ofNat 4385, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: x18 :: x19 :: rest} =
      some (sqCol5part7Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 rest) := by
  have hc (j : Nat) (hj : j ≤ 40) : rest.length + j < 1024 := by omega
  have hcr : rest.length < 1024 := by omega
  simp [hz, hzn, sqCol5part7Program, sqCol5part7Model, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, ofNat_sub_ofNat, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, hc, hcr]

def sqCol5part8Program : List Instr :=
  [.op (.Dup ⟨15, by decide⟩),
   .op (.Swap ⟨0, by decide⟩),
   .op (.Dup ⟨2, by decide⟩),
   .op .NOT,
   .op .ADDMOD,
   .push 1 5,
   .op .SHR,
   .op (.Dup ⟨1, by decide⟩)]

def sqCol5part8Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 : UInt256) (rest : List UInt256) : State :=
  let v0 : UInt256 := UInt256.lnot x1
  let v1 : UInt256 := UInt256.addMod v0 x0 x15
  let v2 : UInt256 := UInt256.shiftRight v1 (UInt256.ofNat 5)
  {s with pc := UInt256.ofNat 4402, memory := s.memory, stack := x1 :: v2 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: rest}

theorem sqCol5part8_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions sqCol5part8Program {s with pc := UInt256.ofNat 4393, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: rest} =
      some (sqCol5part8Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 rest) := by
  have hc (j : Nat) (hj : j ≤ 40) : rest.length + j < 1024 := by omega
  have hcr : rest.length < 1024 := by omega
  simp [hz, hzn, sqCol5part8Program, sqCol5part8Model, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, ofNat_sub_ofNat, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, hc, hcr]

def sqCol5part9Program : List Instr :=
  [.push 30 1766847064778384329583297500742918515827483896875618958121606201292619775,
   .op .AND,
   .op (.Swap ⟨6, by decide⟩),
   .op .POP,
   .push 1 16,
   .op .SHL,
   .op (.Swap ⟨0, by decide⟩),
   .push 1 240]

def sqCol5part9Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 : UInt256) (rest : List UInt256) : State :=
  let v0 : UInt256 := UInt256.land (UInt256.ofNat 1766847064778384329583297500742918515827483896875618958121606201292619775) x0
  let v1 : UInt256 := UInt256.shiftLeft x1 (UInt256.ofNat 16)
  {s with pc := UInt256.ofNat 4442, memory := s.memory, stack := (UInt256.ofNat 240) :: x2 :: v1 :: x3 :: x4 :: x5 :: x6 :: v0 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: x18 :: rest}

theorem sqCol5part9_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions sqCol5part9Program {s with pc := UInt256.ofNat 4402, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: x18 :: rest} =
      some (sqCol5part9Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 rest) := by
  have hc (j : Nat) (hj : j ≤ 40) : rest.length + j < 1024 := by omega
  have hcr : rest.length < 1024 := by omega
  simp [hz, hzn, sqCol5part9Program, sqCol5part9Model, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, ofNat_sub_ofNat, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, hc, hcr]

def sqCol5part10Program : List Instr :=
  [.op .SHR,
   .op .ADD]

def sqCol5part10Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 : UInt256) (rest : List UInt256) : State :=
  let v0 : UInt256 := UInt256.shiftRight x0 (UInt256.ofNat 240)
  let v1 : UInt256 := v0 + x1
  {s with pc := UInt256.ofNat 4444, memory := s.memory, stack := v1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: rest}

theorem sqCol5part10_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions sqCol5part10Program {s with pc := UInt256.ofNat 4442, stack := (UInt256.ofNat 240) :: x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: rest} =
      some (sqCol5part10Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 rest) := by
  have hc (j : Nat) (hj : j ≤ 40) : rest.length + j < 1024 := by omega
  have hcr : rest.length < 1024 := by omega
  simp [hz, hzn, sqCol5part10Program, sqCol5part10Model, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, ofNat_sub_ofNat, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, hc, hcr]

def sqCol5Program : List Instr :=
  [.op (.Dup ⟨0, by decide⟩),
   .op (.Dup ⟨10, by decide⟩),
   .op (.Dup ⟨8, by decide⟩),
   .op .MUL,
   .op (.Dup ⟨10, by decide⟩),
   .op (.Dup ⟨10, by decide⟩),
   .op .MUL,
   .op .ADD,
   .op (.Dup ⟨0, by decide⟩),
   .op .ADD,
   .op .ADD,
   .op .JUMPDEST,
   .op .JUMPDEST,
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
   .op (.Dup ⟨0, by decide⟩),
   .op (.Dup ⟨12, by decide⟩),
   .op (.Dup ⟨10, by decide⟩),
   .op .MULMOD,
   .op (.Swap ⟨0, by decide⟩),
   .op (.Dup ⟨11, by decide⟩),
   .op (.Dup ⟨11, by decide⟩),
   .op .MULMOD,
   .op .ADD,
   .op (.Dup ⟨0, by decide⟩),
   .op .ADD,
   .op .ADD,
   .op .JUMPDEST,
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
   .push 30 1766847064778384329583297500742918515827483896875618958121606201292619775,
   .op .AND,
   .op (.Swap ⟨6, by decide⟩),
   .op .POP,
   .push 1 16,
   .op .SHL,
   .op (.Swap ⟨0, by decide⟩),
   .push 1 240,
   .op .SHR,
   .op .ADD]

def sqCol5Model (s : State) (c q3 q2 q1 q4 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cnt : UInt256) (rest : List UInt256) : State :=
  let v0 : UInt256 := x1 * x4
  let v1 : UInt256 := x2 * x3
  let v2 : UInt256 := v1 + v0
  let v3 : UInt256 := v2 + v2
  let v4 : UInt256 := v3 + c
  let v5 : UInt256 := q1 * n4
  let v6 : UInt256 := v5 + v4
  let v7 : UInt256 := q2 * n3
  let v8 : UInt256 := v7 + v6
  let v9 : UInt256 := q3 * n2
  let v10 : UInt256 := v9 + v8
  let v11 : UInt256 := q4 * n1
  let v12 : UInt256 := v11 + v10
  let v13 : UInt256 := UInt256.mulMod x1 x4 P
  let v14 : UInt256 := UInt256.mulMod x2 x3 P
  let v15 : UInt256 := v14 + v13
  let v16 : UInt256 := v15 + v15
  let v17 : UInt256 := v16 + c
  let v18 : UInt256 := UInt256.mulMod q1 n4 P
  let v19 : UInt256 := v18 + v17
  let v20 : UInt256 := UInt256.mulMod q2 n3 P
  let v21 : UInt256 := v20 + v19
  let v22 : UInt256 := UInt256.mulMod q3 n2 P
  let v23 : UInt256 := v22 + v21
  let v24 : UInt256 := UInt256.mulMod q4 n1 P
  let v25 : UInt256 := v24 + v23
  let v26 : UInt256 := UInt256.lnot v12
  let v27 : UInt256 := UInt256.addMod v26 v25 P
  let v28 : UInt256 := UInt256.shiftRight v27 (UInt256.ofNat 5)
  let v29 : UInt256 := UInt256.land (UInt256.ofNat 1766847064778384329583297500742918515827483896875618958121606201292619775) v12
  let v30 : UInt256 := UInt256.shiftLeft v28 (UInt256.ofNat 16)
  let v31 : UInt256 := UInt256.shiftRight v12 (UInt256.ofNat 240)
  let v32 : UInt256 := v31 + v30
  {s with pc := UInt256.ofNat 4444, memory := s.memory, stack := v32 :: q3 :: q2 :: q1 :: q4 :: v29 :: x1 :: x2 :: x3 :: x4 :: n1 :: n2 :: n3 :: n4 :: P :: inv :: cnt :: rest}

theorem sqCol5_run (s : State) (c q3 q2 q1 q4 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cnt : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions sqCol5Program {s with pc := UInt256.ofNat 4329, stack := c :: q3 :: q2 :: q1 :: q4 :: x0 :: x1 :: x2 :: x3 :: x4 :: n1 :: n2 :: n3 :: n4 :: P :: inv :: cnt :: rest} =
      some (sqCol5Model s c q3 q2 q1 q4 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cnt rest) := by
  let v0 : UInt256 := x1 * x4
  let v1 : UInt256 := x2 * x3
  let v2 : UInt256 := v1 + v0
  let v3 : UInt256 := v2 + v2
  let v4 : UInt256 := v3 + c
  let v5 : UInt256 := q1 * n4
  let v6 : UInt256 := v5 + v4
  let v7 : UInt256 := q2 * n3
  let v8 : UInt256 := v7 + v6
  let v9 : UInt256 := q3 * n2
  let v10 : UInt256 := v9 + v8
  let v11 : UInt256 := q4 * n1
  let v12 : UInt256 := v11 + v10
  let v13 : UInt256 := UInt256.mulMod x1 x4 P
  let v14 : UInt256 := UInt256.mulMod x2 x3 P
  let v15 : UInt256 := v14 + v13
  let v16 : UInt256 := v15 + v15
  let v17 : UInt256 := v16 + c
  let v18 : UInt256 := UInt256.mulMod q1 n4 P
  let v19 : UInt256 := v18 + v17
  let v20 : UInt256 := UInt256.mulMod q2 n3 P
  let v21 : UInt256 := v20 + v19
  let v22 : UInt256 := UInt256.mulMod q3 n2 P
  let v23 : UInt256 := v22 + v21
  let v24 : UInt256 := UInt256.mulMod q4 n1 P
  let v25 : UInt256 := v24 + v23
  let v26 : UInt256 := UInt256.lnot v12
  let v27 : UInt256 := UInt256.addMod v26 v25 P
  let v28 : UInt256 := UInt256.shiftRight v27 (UInt256.ofNat 5)
  let v29 : UInt256 := UInt256.land (UInt256.ofNat 1766847064778384329583297500742918515827483896875618958121606201292619775) v12
  let v30 : UInt256 := UInt256.shiftLeft v28 (UInt256.ofNat 16)
  let v31 : UInt256 := UInt256.shiftRight v12 (UInt256.ofNat 240)
  let v32 : UInt256 := v31 + v30
  have h0 : runInstructions sqCol5part0Program {s with pc := UInt256.ofNat 4329, memory := s.memory, stack := c :: q3 :: q2 :: q1 :: q4 :: x0 :: x1 :: x2 :: x3 :: x4 :: n1 :: n2 :: n3 :: n4 :: P :: inv :: cnt :: rest} = some {s with pc := UInt256.ofNat 4337, memory := s.memory, stack := v2 :: c :: c :: q3 :: q2 :: q1 :: q4 :: x0 :: x1 :: x2 :: x3 :: x4 :: n1 :: n2 :: n3 :: n4 :: P :: inv :: cnt :: rest} := by
    simpa only [sqCol5part0Model, v0, v1, v2] using sqCol5part0_run (s) c q3 q2 q1 q4 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cnt rest hcap hact
  have h1 : runInstructions sqCol5part1Program {s with pc := UInt256.ofNat 4337, memory := s.memory, stack := v2 :: c :: c :: q3 :: q2 :: q1 :: q4 :: x0 :: x1 :: x2 :: x3 :: x4 :: n1 :: n2 :: n3 :: n4 :: P :: inv :: cnt :: rest} = some {s with pc := UInt256.ofNat 4345, memory := s.memory, stack := v5 :: v4 :: c :: q3 :: q2 :: q1 :: q4 :: x0 :: x1 :: x2 :: x3 :: x4 :: n1 :: n2 :: n3 :: n4 :: P :: inv :: cnt :: rest} := by
    simpa only [sqCol5part1Model, v3, v4, v5] using sqCol5part1_run (s) v2 c c q3 q2 q1 q4 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cnt rest hcap hact
  have h2 : runInstructions sqCol5part2Program {s with pc := UInt256.ofNat 4345, memory := s.memory, stack := v5 :: v4 :: c :: q3 :: q2 :: q1 :: q4 :: x0 :: x1 :: x2 :: x3 :: x4 :: n1 :: n2 :: n3 :: n4 :: P :: inv :: cnt :: rest} = some {s with pc := UInt256.ofNat 4353, memory := s.memory, stack := v9 :: v8 :: c :: q3 :: q2 :: q1 :: q4 :: x0 :: x1 :: x2 :: x3 :: x4 :: n1 :: n2 :: n3 :: n4 :: P :: inv :: cnt :: rest} := by
    simpa only [sqCol5part2Model, v6, v7, v8, v9] using sqCol5part2_run (s) v5 v4 c q3 q2 q1 q4 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cnt rest hcap hact
  have h3 : runInstructions sqCol5part3Program {s with pc := UInt256.ofNat 4353, memory := s.memory, stack := v9 :: v8 :: c :: q3 :: q2 :: q1 :: q4 :: x0 :: x1 :: x2 :: x3 :: x4 :: n1 :: n2 :: n3 :: n4 :: P :: inv :: cnt :: rest} = some {s with pc := UInt256.ofNat 4361, memory := s.memory, stack := P :: P :: c :: v12 :: q3 :: q2 :: q1 :: q4 :: x0 :: x1 :: x2 :: x3 :: x4 :: n1 :: n2 :: n3 :: n4 :: P :: inv :: cnt :: rest} := by
    simpa only [sqCol5part3Model, v10, v11, v12] using sqCol5part3_run (s) v9 v8 c q3 q2 q1 q4 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cnt rest hcap hact
  have h4 : runInstructions sqCol5part4Program {s with pc := UInt256.ofNat 4361, memory := s.memory, stack := P :: P :: c :: v12 :: q3 :: q2 :: q1 :: q4 :: x0 :: x1 :: x2 :: x3 :: x4 :: n1 :: n2 :: n3 :: n4 :: P :: inv :: cnt :: rest} = some {s with pc := UInt256.ofNat 4369, memory := s.memory, stack := v15 :: c :: v12 :: q3 :: q2 :: q1 :: q4 :: x0 :: x1 :: x2 :: x3 :: x4 :: n1 :: n2 :: n3 :: n4 :: P :: inv :: cnt :: rest} := by
    simpa only [sqCol5part4Model, v13, v14, v15] using sqCol5part4_run (s) P P c v12 q3 q2 q1 q4 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cnt rest hcap hact
  have h5 : runInstructions sqCol5part5Program {s with pc := UInt256.ofNat 4369, memory := s.memory, stack := v15 :: c :: v12 :: q3 :: q2 :: q1 :: q4 :: x0 :: x1 :: x2 :: x3 :: x4 :: n1 :: n2 :: n3 :: n4 :: P :: inv :: cnt :: rest} = some {s with pc := UInt256.ofNat 4377, memory := s.memory, stack := v18 :: v17 :: v12 :: q3 :: q2 :: q1 :: q4 :: x0 :: x1 :: x2 :: x3 :: x4 :: n1 :: n2 :: n3 :: n4 :: P :: inv :: cnt :: rest} := by
    simpa only [sqCol5part5Model, v16, v17, v18] using sqCol5part5_run (s) v15 c v12 q3 q2 q1 q4 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cnt rest hcap hact
  have h6 : runInstructions sqCol5part6Program {s with pc := UInt256.ofNat 4377, memory := s.memory, stack := v18 :: v17 :: v12 :: q3 :: q2 :: q1 :: q4 :: x0 :: x1 :: x2 :: x3 :: x4 :: n1 :: n2 :: n3 :: n4 :: P :: inv :: cnt :: rest} = some {s with pc := UInt256.ofNat 4385, memory := s.memory, stack := n2 :: P :: v21 :: v12 :: q3 :: q2 :: q1 :: q4 :: x0 :: x1 :: x2 :: x3 :: x4 :: n1 :: n2 :: n3 :: n4 :: P :: inv :: cnt :: rest} := by
    simpa only [sqCol5part6Model, v19, v20, v21] using sqCol5part6_run (s) v18 v17 v12 q3 q2 q1 q4 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cnt rest hcap hact
  have h7 : runInstructions sqCol5part7Program {s with pc := UInt256.ofNat 4385, memory := s.memory, stack := n2 :: P :: v21 :: v12 :: q3 :: q2 :: q1 :: q4 :: x0 :: x1 :: x2 :: x3 :: x4 :: n1 :: n2 :: n3 :: n4 :: P :: inv :: cnt :: rest} = some {s with pc := UInt256.ofNat 4393, memory := s.memory, stack := v25 :: v12 :: q3 :: q2 :: q1 :: q4 :: x0 :: x1 :: x2 :: x3 :: x4 :: n1 :: n2 :: n3 :: n4 :: P :: inv :: cnt :: rest} := by
    simpa only [sqCol5part7Model, v22, v23, v24, v25] using sqCol5part7_run (s) n2 P v21 v12 q3 q2 q1 q4 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cnt rest hcap hact
  have h8 : runInstructions sqCol5part8Program {s with pc := UInt256.ofNat 4393, memory := s.memory, stack := v25 :: v12 :: q3 :: q2 :: q1 :: q4 :: x0 :: x1 :: x2 :: x3 :: x4 :: n1 :: n2 :: n3 :: n4 :: P :: inv :: cnt :: rest} = some {s with pc := UInt256.ofNat 4402, memory := s.memory, stack := v12 :: v28 :: v12 :: q3 :: q2 :: q1 :: q4 :: x0 :: x1 :: x2 :: x3 :: x4 :: n1 :: n2 :: n3 :: n4 :: P :: inv :: cnt :: rest} := by
    simpa only [sqCol5part8Model, v26, v27, v28] using sqCol5part8_run (s) v25 v12 q3 q2 q1 q4 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cnt rest hcap hact
  have h9 : runInstructions sqCol5part9Program {s with pc := UInt256.ofNat 4402, memory := s.memory, stack := v12 :: v28 :: v12 :: q3 :: q2 :: q1 :: q4 :: x0 :: x1 :: x2 :: x3 :: x4 :: n1 :: n2 :: n3 :: n4 :: P :: inv :: cnt :: rest} = some {s with pc := UInt256.ofNat 4442, memory := s.memory, stack := (UInt256.ofNat 240) :: v12 :: v30 :: q3 :: q2 :: q1 :: q4 :: v29 :: x1 :: x2 :: x3 :: x4 :: n1 :: n2 :: n3 :: n4 :: P :: inv :: cnt :: rest} := by
    simpa only [sqCol5part9Model, v29, v30] using sqCol5part9_run (s) v12 v28 v12 q3 q2 q1 q4 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cnt rest hcap hact
  have h10 : runInstructions sqCol5part10Program {s with pc := UInt256.ofNat 4442, memory := s.memory, stack := (UInt256.ofNat 240) :: v12 :: v30 :: q3 :: q2 :: q1 :: q4 :: v29 :: x1 :: x2 :: x3 :: x4 :: n1 :: n2 :: n3 :: n4 :: P :: inv :: cnt :: rest} = some {s with pc := UInt256.ofNat 4444, memory := s.memory, stack := v32 :: q3 :: q2 :: q1 :: q4 :: v29 :: x1 :: x2 :: x3 :: x4 :: n1 :: n2 :: n3 :: n4 :: P :: inv :: cnt :: rest} := by
    simpa only [sqCol5part10Model, v31, v32] using sqCol5part10_run (s) v12 v30 q3 q2 q1 q4 v29 x1 x2 x3 x4 n1 n2 n3 n4 P inv cnt rest hcap hact
  exact (runInstructions_append_some _ _ _ _ _ h0 (runInstructions_append_some _ _ _ _ _ h1 (runInstructions_append_some _ _ _ _ _ h2 (runInstructions_append_some _ _ _ _ _ h3 (runInstructions_append_some _ _ _ _ _ h4 (runInstructions_append_some _ _ _ _ _ h5 (runInstructions_append_some _ _ _ _ _ h6 (runInstructions_append_some _ _ _ _ _ h7 (runInstructions_append_some _ _ _ _ _ h8 (runInstructions_append_some _ _ _ _ _ h9 h10))))))))))

def sqCol5_o0 (c q3 q2 q1 q4 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cnt : UInt256) : UInt256 :=
  ((UInt256.shiftRight ((q4 * n1) + ((q3 * n2) + ((q2 * n3) + ((q1 * n4) + (((x2 * x3) + (x2 * x3)) + (((x1 * x4) + (x1 * x4)) + c)))))) (UInt256.ofNat 240)) + (UInt256.shiftLeft (UInt256.shiftRight (UInt256.addMod (UInt256.lnot ((q4 * n1) + ((q3 * n2) + ((q2 * n3) + ((q1 * n4) + (((x2 * x3) + (x2 * x3)) + (((x1 * x4) + (x1 * x4)) + c))))))) ((UInt256.mulMod q4 n1 P) + ((UInt256.mulMod q3 n2 P) + ((UInt256.mulMod q2 n3 P) + ((UInt256.mulMod q1 n4 P) + (((UInt256.mulMod x2 x3 P) + (UInt256.mulMod x2 x3 P)) + (((UInt256.mulMod x1 x4 P) + (UInt256.mulMod x1 x4 P)) + c)))))) P) (UInt256.ofNat 5)) (UInt256.ofNat 16)))

def sqCol5_o5 (c q3 q2 q1 q4 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cnt : UInt256) : UInt256 :=
  (UInt256.land (UInt256.ofNat 1766847064778384329583297500742918515827483896875618958121606201292619775) ((q4 * n1) + ((q3 * n2) + ((q2 * n3) + ((q1 * n4) + (((x2 * x3) + (x2 * x3)) + (((x1 * x4) + (x1 * x4)) + c)))))))

theorem sqCol5_eq (s : State) (c q3 q2 q1 q4 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cnt : UInt256) (rest : List UInt256) :
    sqCol5Model s c q3 q2 q1 q4 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cnt rest =
      {s with pc := UInt256.ofNat 4444, stack := (sqCol5_o0 c q3 q2 q1 q4 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cnt) :: q3 :: q2 :: q1 :: q4 :: (sqCol5_o5 c q3 q2 q1 q4 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cnt) :: x1 :: x2 :: x3 :: x4 :: n1 :: n2 :: n3 :: n4 :: P :: inv :: cnt :: rest} := by
  simp only [sqCol5Model, sqCol5_o0, sqCol5_o5, fusePair]

/-! ## sqCol6: pc 4444..4546, 69 instructions -/

def sqCol6part0Program : List Instr :=
  [.op (.Dup ⟨0, by decide⟩),
   .op (.Dup ⟨10, by decide⟩),
   .op (.Dup ⟨9, by decide⟩),
   .op .MUL,
   .op (.Dup ⟨0, by decide⟩),
   .op .ADD,
   .op .ADD,
   .op (.Dup ⟨9, by decide⟩)]

def sqCol6part0Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 : UInt256) (rest : List UInt256) : State :=
  let v0 : UInt256 := x7 * x9
  let v1 : UInt256 := v0 + v0
  let v2 : UInt256 := v1 + x0
  {s with pc := UInt256.ofNat 4452, memory := s.memory, stack := x8 :: v2 :: x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: rest}

theorem sqCol6part0_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions sqCol6part0Program {s with pc := UInt256.ofNat 4444, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: rest} =
      some (sqCol6part0Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 rest) := by
  have hc (j : Nat) (hj : j ≤ 33) : rest.length + j < 1024 := by omega
  have hcr : rest.length < 1024 := by omega
  simp [hz, hzn, sqCol6part0Program, sqCol6part0Model, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, ofNat_sub_ofNat, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, hc, hcr]

def sqCol6part1Program : List Instr :=
  [.op (.Dup ⟨0, by decide⟩),
   .op .MUL,
   .op .ADD,
   .op (.Dup ⟨14, by decide⟩),
   .op (.Dup ⟨4, by decide⟩),
   .op .MUL,
   .op .ADD,
   .op (.Dup ⟨13, by decide⟩)]

def sqCol6part1Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 : UInt256) (rest : List UInt256) : State :=
  let v0 : UInt256 := x0 * x0
  let v1 : UInt256 := v0 + x1
  let v2 : UInt256 := x4 * x15
  let v3 : UInt256 := v2 + v1
  {s with pc := UInt256.ofNat 4460, memory := s.memory, stack := x14 :: v3 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: x18 :: rest}

theorem sqCol6part1_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions sqCol6part1Program {s with pc := UInt256.ofNat 4452, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: x18 :: rest} =
      some (sqCol6part1Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 rest) := by
  have hc (j : Nat) (hj : j ≤ 33) : rest.length + j < 1024 := by omega
  have hcr : rest.length < 1024 := by omega
  simp [hz, hzn, sqCol6part1Program, sqCol6part1Model, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, ofNat_sub_ofNat, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, hc, hcr]

def sqCol6part2Program : List Instr :=
  [.op (.Dup ⟨3, by decide⟩),
   .op .MUL,
   .op .ADD,
   .op (.Dup ⟨12, by decide⟩),
   .op (.Dup ⟨6, by decide⟩),
   .op .MUL,
   .op .ADD,
   .op (.Swap ⟨0, by decide⟩)]

def sqCol6part2Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 : UInt256) (rest : List UInt256) : State :=
  let v0 : UInt256 := x3 * x0
  let v1 : UInt256 := v0 + x1
  let v2 : UInt256 := x6 * x13
  let v3 : UInt256 := v2 + v1
  {s with pc := UInt256.ofNat 4468, memory := s.memory, stack := x2 :: v3 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: x18 :: rest}

theorem sqCol6part2_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions sqCol6part2Program {s with pc := UInt256.ofNat 4460, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: x18 :: rest} =
      some (sqCol6part2Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 rest) := by
  have hc (j : Nat) (hj : j ≤ 33) : rest.length + j < 1024 := by omega
  have hcr : rest.length < 1024 := by omega
  simp [hz, hzn, sqCol6part2Program, sqCol6part2Model, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, ofNat_sub_ofNat, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, hc, hcr]

def sqCol6part3Program : List Instr :=
  [.op (.Dup ⟨15, by decide⟩),
   .op (.Dup ⟨11, by decide⟩),
   .op (.Dup ⟨10, by decide⟩),
   .op .MULMOD,
   .op (.Dup ⟨0, by decide⟩),
   .op .ADD,
   .op .ADD,
   .op (.Dup ⟨15, by decide⟩)]

def sqCol6part3Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 : UInt256) (rest : List UInt256) : State :=
  let v0 : UInt256 := UInt256.mulMod x8 x10 x15
  let v1 : UInt256 := v0 + v0
  let v2 : UInt256 := v1 + x0
  {s with pc := UInt256.ofNat 4476, memory := s.memory, stack := x15 :: v2 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: rest}

theorem sqCol6part3_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions sqCol6part3Program {s with pc := UInt256.ofNat 4468, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: rest} =
      some (sqCol6part3Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 rest) := by
  have hc (j : Nat) (hj : j ≤ 34) : rest.length + j < 1024 := by omega
  have hcr : rest.length < 1024 := by omega
  simp [hz, hzn, sqCol6part3Program, sqCol6part3Model, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, ofNat_sub_ofNat, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, hc, hcr]

def sqCol6part4Program : List Instr :=
  [.op (.Dup ⟨10, by decide⟩),
   .op (.Dup ⟨0, by decide⟩),
   .op .MULMOD,
   .op .ADD,
   .op (.Dup ⟨15, by decide⟩),
   .op (.Dup ⟨15, by decide⟩),
   .op (.Dup ⟨5, by decide⟩),
   .op .MULMOD]

def sqCol6part4Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 : UInt256) (rest : List UInt256) : State :=
  let v0 : UInt256 := UInt256.mulMod x10 x10 x0
  let v1 : UInt256 := v0 + x1
  let v2 : UInt256 := UInt256.mulMod x4 x15 x16
  {s with pc := UInt256.ofNat 4484, memory := s.memory, stack := v2 :: v1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: x18 :: rest}

theorem sqCol6part4_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions sqCol6part4Program {s with pc := UInt256.ofNat 4476, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: x18 :: rest} =
      some (sqCol6part4Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 rest) := by
  have hc (j : Nat) (hj : j ≤ 34) : rest.length + j < 1024 := by omega
  have hcr : rest.length < 1024 := by omega
  simp [hz, hzn, sqCol6part4Program, sqCol6part4Model, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, ofNat_sub_ofNat, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, hc, hcr]

def sqCol6part5Program : List Instr :=
  [.op .ADD,
   .op (.Dup ⟨15, by decide⟩),
   .op (.Dup ⟨14, by decide⟩),
   .op (.Dup ⟨4, by decide⟩),
   .op .MULMOD,
   .op .ADD,
   .op (.Dup ⟨15, by decide⟩),
   .op (.Dup ⟨13, by decide⟩)]

def sqCol6part5Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 : UInt256) (rest : List UInt256) : State :=
  let v0 : UInt256 := x0 + x1
  let v1 : UInt256 := UInt256.mulMod x3 x14 x16
  let v2 : UInt256 := v1 + v0
  {s with pc := UInt256.ofNat 4492, memory := s.memory, stack := x13 :: x16 :: v2 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: x18 :: rest}

theorem sqCol6part5_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions sqCol6part5Program {s with pc := UInt256.ofNat 4484, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: x18 :: rest} =
      some (sqCol6part5Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 rest) := by
  have hc (j : Nat) (hj : j ≤ 34) : rest.length + j < 1024 := by omega
  have hcr : rest.length < 1024 := by omega
  simp [hz, hzn, sqCol6part5Program, sqCol6part5Model, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, ofNat_sub_ofNat, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, hc, hcr]

def sqCol6part6Program : List Instr :=
  [.op (.Dup ⟨7, by decide⟩),
   .op .MULMOD,
   .op .ADD,
   .op (.Dup ⟨15, by decide⟩),
   .op (.Swap ⟨0, by decide⟩),
   .op (.Dup ⟨2, by decide⟩),
   .op .NOT,
   .op .ADDMOD]

def sqCol6part6Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 : UInt256) (rest : List UInt256) : State :=
  let v0 : UInt256 := UInt256.mulMod x7 x0 x1
  let v1 : UInt256 := v0 + x2
  let v2 : UInt256 := UInt256.lnot x3
  let v3 : UInt256 := UInt256.addMod v2 v1 x17
  {s with pc := UInt256.ofNat 4500, memory := s.memory, stack := v3 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: x18 :: x19 :: rest}

theorem sqCol6part6_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions sqCol6part6Program {s with pc := UInt256.ofNat 4492, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: x18 :: x19 :: rest} =
      some (sqCol6part6Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 rest) := by
  have hc (j : Nat) (hj : j ≤ 34) : rest.length + j < 1024 := by omega
  have hcr : rest.length < 1024 := by omega
  simp [hz, hzn, sqCol6part6Program, sqCol6part6Model, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, ofNat_sub_ofNat, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, hc, hcr]

def sqCol6part7Program : List Instr :=
  [.push 1 5,
   .op .SHR,
   .op (.Dup ⟨1, by decide⟩),
   .push 30 1766847064778384329583297500742918515827483896875618958121606201292619775,
   .op .AND,
   .op (.Swap ⟨7, by decide⟩),
   .op .POP]

def sqCol6part7Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 : UInt256) (rest : List UInt256) : State :=
  let v0 : UInt256 := UInt256.shiftRight x0 (UInt256.ofNat 5)
  let v1 : UInt256 := UInt256.land (UInt256.ofNat 1766847064778384329583297500742918515827483896875618958121606201292619775) x1
  {s with pc := UInt256.ofNat 4538, memory := s.memory, stack := v0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: v1 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: rest}

theorem sqCol6part7_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions sqCol6part7Program {s with pc := UInt256.ofNat 4500, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: rest} =
      some (sqCol6part7Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 rest) := by
  have hc (j : Nat) (hj : j ≤ 33) : rest.length + j < 1024 := by omega
  have hcr : rest.length < 1024 := by omega
  simp [hz, hzn, sqCol6part7Program, sqCol6part7Model, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, ofNat_sub_ofNat, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, hc, hcr]

def sqCol6part8Program : List Instr :=
  [.push 1 16,
   .op .SHL,
   .op (.Swap ⟨0, by decide⟩),
   .push 1 240,
   .op .SHR,
   .op .ADD]

def sqCol6part8Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 : UInt256) (rest : List UInt256) : State :=
  let v0 : UInt256 := UInt256.shiftLeft x0 (UInt256.ofNat 16)
  let v1 : UInt256 := UInt256.shiftRight x1 (UInt256.ofNat 240)
  let v2 : UInt256 := v1 + v0
  {s with pc := UInt256.ofNat 4546, memory := s.memory, stack := v2 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: rest}

theorem sqCol6part8_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions sqCol6part8Program {s with pc := UInt256.ofNat 4538, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: rest} =
      some (sqCol6part8Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 rest) := by
  have hc (j : Nat) (hj : j ≤ 32) : rest.length + j < 1024 := by omega
  have hcr : rest.length < 1024 := by omega
  simp [hz, hzn, sqCol6part8Program, sqCol6part8Model, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, ofNat_sub_ofNat, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, hc, hcr]

def sqCol6Program : List Instr :=
  [.op (.Dup ⟨0, by decide⟩),
   .op (.Dup ⟨10, by decide⟩),
   .op (.Dup ⟨9, by decide⟩),
   .op .MUL,
   .op (.Dup ⟨0, by decide⟩),
   .op .ADD,
   .op .ADD,
   .op (.Dup ⟨9, by decide⟩),
   .op (.Dup ⟨0, by decide⟩),
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
   .op (.Dup ⟨11, by decide⟩),
   .op (.Dup ⟨10, by decide⟩),
   .op .MULMOD,
   .op (.Dup ⟨0, by decide⟩),
   .op .ADD,
   .op .ADD,
   .op (.Dup ⟨15, by decide⟩),
   .op (.Dup ⟨10, by decide⟩),
   .op (.Dup ⟨0, by decide⟩),
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
   .push 30 1766847064778384329583297500742918515827483896875618958121606201292619775,
   .op .AND,
   .op (.Swap ⟨7, by decide⟩),
   .op .POP,
   .push 1 16,
   .op .SHL,
   .op (.Swap ⟨0, by decide⟩),
   .push 1 240,
   .op .SHR,
   .op .ADD]

def sqCol6Model (s : State) (c q3 q2 q1 q4 z0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cnt : UInt256) (rest : List UInt256) : State :=
  let v0 : UInt256 := x2 * x4
  let v1 : UInt256 := v0 + v0
  let v2 : UInt256 := v1 + c
  let v3 : UInt256 := x3 * x3
  let v4 : UInt256 := v3 + v2
  let v5 : UInt256 := q2 * n4
  let v6 : UInt256 := v5 + v4
  let v7 : UInt256 := q3 * n3
  let v8 : UInt256 := v7 + v6
  let v9 : UInt256 := q4 * n2
  let v10 : UInt256 := v9 + v8
  let v11 : UInt256 := UInt256.mulMod x2 x4 P
  let v12 : UInt256 := v11 + v11
  let v13 : UInt256 := v12 + c
  let v14 : UInt256 := UInt256.mulMod x3 x3 P
  let v15 : UInt256 := v14 + v13
  let v16 : UInt256 := UInt256.mulMod q2 n4 P
  let v17 : UInt256 := v16 + v15
  let v18 : UInt256 := UInt256.mulMod q3 n3 P
  let v19 : UInt256 := v18 + v17
  let v20 : UInt256 := UInt256.mulMod q4 n2 P
  let v21 : UInt256 := v20 + v19
  let v22 : UInt256 := UInt256.lnot v10
  let v23 : UInt256 := UInt256.addMod v22 v21 P
  let v24 : UInt256 := UInt256.shiftRight v23 (UInt256.ofNat 5)
  let v25 : UInt256 := UInt256.land (UInt256.ofNat 1766847064778384329583297500742918515827483896875618958121606201292619775) v10
  let v26 : UInt256 := UInt256.shiftLeft v24 (UInt256.ofNat 16)
  let v27 : UInt256 := UInt256.shiftRight v10 (UInt256.ofNat 240)
  let v28 : UInt256 := v27 + v26
  {s with pc := UInt256.ofNat 4546, memory := s.memory, stack := v28 :: q3 :: q2 :: q1 :: q4 :: z0 :: v25 :: x2 :: x3 :: x4 :: n1 :: n2 :: n3 :: n4 :: P :: inv :: cnt :: rest}

theorem sqCol6_run (s : State) (c q3 q2 q1 q4 z0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cnt : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions sqCol6Program {s with pc := UInt256.ofNat 4444, stack := c :: q3 :: q2 :: q1 :: q4 :: z0 :: x1 :: x2 :: x3 :: x4 :: n1 :: n2 :: n3 :: n4 :: P :: inv :: cnt :: rest} =
      some (sqCol6Model s c q3 q2 q1 q4 z0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cnt rest) := by
  let v0 : UInt256 := x2 * x4
  let v1 : UInt256 := v0 + v0
  let v2 : UInt256 := v1 + c
  let v3 : UInt256 := x3 * x3
  let v4 : UInt256 := v3 + v2
  let v5 : UInt256 := q2 * n4
  let v6 : UInt256 := v5 + v4
  let v7 : UInt256 := q3 * n3
  let v8 : UInt256 := v7 + v6
  let v9 : UInt256 := q4 * n2
  let v10 : UInt256 := v9 + v8
  let v11 : UInt256 := UInt256.mulMod x2 x4 P
  let v12 : UInt256 := v11 + v11
  let v13 : UInt256 := v12 + c
  let v14 : UInt256 := UInt256.mulMod x3 x3 P
  let v15 : UInt256 := v14 + v13
  let v16 : UInt256 := UInt256.mulMod q2 n4 P
  let v17 : UInt256 := v16 + v15
  let v18 : UInt256 := UInt256.mulMod q3 n3 P
  let v19 : UInt256 := v18 + v17
  let v20 : UInt256 := UInt256.mulMod q4 n2 P
  let v21 : UInt256 := v20 + v19
  let v22 : UInt256 := UInt256.lnot v10
  let v23 : UInt256 := UInt256.addMod v22 v21 P
  let v24 : UInt256 := UInt256.shiftRight v23 (UInt256.ofNat 5)
  let v25 : UInt256 := UInt256.land (UInt256.ofNat 1766847064778384329583297500742918515827483896875618958121606201292619775) v10
  let v26 : UInt256 := UInt256.shiftLeft v24 (UInt256.ofNat 16)
  let v27 : UInt256 := UInt256.shiftRight v10 (UInt256.ofNat 240)
  let v28 : UInt256 := v27 + v26
  have h0 : runInstructions sqCol6part0Program {s with pc := UInt256.ofNat 4444, memory := s.memory, stack := c :: q3 :: q2 :: q1 :: q4 :: z0 :: x1 :: x2 :: x3 :: x4 :: n1 :: n2 :: n3 :: n4 :: P :: inv :: cnt :: rest} = some {s with pc := UInt256.ofNat 4452, memory := s.memory, stack := x3 :: v2 :: c :: q3 :: q2 :: q1 :: q4 :: z0 :: x1 :: x2 :: x3 :: x4 :: n1 :: n2 :: n3 :: n4 :: P :: inv :: cnt :: rest} := by
    simpa only [sqCol6part0Model, v0, v1, v2] using sqCol6part0_run (s) c q3 q2 q1 q4 z0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cnt rest hcap hact
  have h1 : runInstructions sqCol6part1Program {s with pc := UInt256.ofNat 4452, memory := s.memory, stack := x3 :: v2 :: c :: q3 :: q2 :: q1 :: q4 :: z0 :: x1 :: x2 :: x3 :: x4 :: n1 :: n2 :: n3 :: n4 :: P :: inv :: cnt :: rest} = some {s with pc := UInt256.ofNat 4460, memory := s.memory, stack := n3 :: v6 :: c :: q3 :: q2 :: q1 :: q4 :: z0 :: x1 :: x2 :: x3 :: x4 :: n1 :: n2 :: n3 :: n4 :: P :: inv :: cnt :: rest} := by
    simpa only [sqCol6part1Model, v3, v4, v5, v6] using sqCol6part1_run (s) x3 v2 c q3 q2 q1 q4 z0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cnt rest hcap hact
  have h2 : runInstructions sqCol6part2Program {s with pc := UInt256.ofNat 4460, memory := s.memory, stack := n3 :: v6 :: c :: q3 :: q2 :: q1 :: q4 :: z0 :: x1 :: x2 :: x3 :: x4 :: n1 :: n2 :: n3 :: n4 :: P :: inv :: cnt :: rest} = some {s with pc := UInt256.ofNat 4468, memory := s.memory, stack := c :: v10 :: q3 :: q2 :: q1 :: q4 :: z0 :: x1 :: x2 :: x3 :: x4 :: n1 :: n2 :: n3 :: n4 :: P :: inv :: cnt :: rest} := by
    simpa only [sqCol6part2Model, v7, v8, v9, v10] using sqCol6part2_run (s) n3 v6 c q3 q2 q1 q4 z0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cnt rest hcap hact
  have h3 : runInstructions sqCol6part3Program {s with pc := UInt256.ofNat 4468, memory := s.memory, stack := c :: v10 :: q3 :: q2 :: q1 :: q4 :: z0 :: x1 :: x2 :: x3 :: x4 :: n1 :: n2 :: n3 :: n4 :: P :: inv :: cnt :: rest} = some {s with pc := UInt256.ofNat 4476, memory := s.memory, stack := P :: v13 :: v10 :: q3 :: q2 :: q1 :: q4 :: z0 :: x1 :: x2 :: x3 :: x4 :: n1 :: n2 :: n3 :: n4 :: P :: inv :: cnt :: rest} := by
    simpa only [sqCol6part3Model, v11, v12, v13] using sqCol6part3_run (s) c v10 q3 q2 q1 q4 z0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cnt rest hcap hact
  have h4 : runInstructions sqCol6part4Program {s with pc := UInt256.ofNat 4476, memory := s.memory, stack := P :: v13 :: v10 :: q3 :: q2 :: q1 :: q4 :: z0 :: x1 :: x2 :: x3 :: x4 :: n1 :: n2 :: n3 :: n4 :: P :: inv :: cnt :: rest} = some {s with pc := UInt256.ofNat 4484, memory := s.memory, stack := v16 :: v15 :: v10 :: q3 :: q2 :: q1 :: q4 :: z0 :: x1 :: x2 :: x3 :: x4 :: n1 :: n2 :: n3 :: n4 :: P :: inv :: cnt :: rest} := by
    simpa only [sqCol6part4Model, v14, v15, v16] using sqCol6part4_run (s) P v13 v10 q3 q2 q1 q4 z0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cnt rest hcap hact
  have h5 : runInstructions sqCol6part5Program {s with pc := UInt256.ofNat 4484, memory := s.memory, stack := v16 :: v15 :: v10 :: q3 :: q2 :: q1 :: q4 :: z0 :: x1 :: x2 :: x3 :: x4 :: n1 :: n2 :: n3 :: n4 :: P :: inv :: cnt :: rest} = some {s with pc := UInt256.ofNat 4492, memory := s.memory, stack := n2 :: P :: v19 :: v10 :: q3 :: q2 :: q1 :: q4 :: z0 :: x1 :: x2 :: x3 :: x4 :: n1 :: n2 :: n3 :: n4 :: P :: inv :: cnt :: rest} := by
    simpa only [sqCol6part5Model, v17, v18, v19] using sqCol6part5_run (s) v16 v15 v10 q3 q2 q1 q4 z0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cnt rest hcap hact
  have h6 : runInstructions sqCol6part6Program {s with pc := UInt256.ofNat 4492, memory := s.memory, stack := n2 :: P :: v19 :: v10 :: q3 :: q2 :: q1 :: q4 :: z0 :: x1 :: x2 :: x3 :: x4 :: n1 :: n2 :: n3 :: n4 :: P :: inv :: cnt :: rest} = some {s with pc := UInt256.ofNat 4500, memory := s.memory, stack := v23 :: v10 :: q3 :: q2 :: q1 :: q4 :: z0 :: x1 :: x2 :: x3 :: x4 :: n1 :: n2 :: n3 :: n4 :: P :: inv :: cnt :: rest} := by
    simpa only [sqCol6part6Model, v20, v21, v22, v23] using sqCol6part6_run (s) n2 P v19 v10 q3 q2 q1 q4 z0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cnt rest hcap hact
  have h7 : runInstructions sqCol6part7Program {s with pc := UInt256.ofNat 4500, memory := s.memory, stack := v23 :: v10 :: q3 :: q2 :: q1 :: q4 :: z0 :: x1 :: x2 :: x3 :: x4 :: n1 :: n2 :: n3 :: n4 :: P :: inv :: cnt :: rest} = some {s with pc := UInt256.ofNat 4538, memory := s.memory, stack := v24 :: v10 :: q3 :: q2 :: q1 :: q4 :: z0 :: v25 :: x2 :: x3 :: x4 :: n1 :: n2 :: n3 :: n4 :: P :: inv :: cnt :: rest} := by
    simpa only [sqCol6part7Model, v24, v25] using sqCol6part7_run (s) v23 v10 q3 q2 q1 q4 z0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cnt rest hcap hact
  have h8 : runInstructions sqCol6part8Program {s with pc := UInt256.ofNat 4538, memory := s.memory, stack := v24 :: v10 :: q3 :: q2 :: q1 :: q4 :: z0 :: v25 :: x2 :: x3 :: x4 :: n1 :: n2 :: n3 :: n4 :: P :: inv :: cnt :: rest} = some {s with pc := UInt256.ofNat 4546, memory := s.memory, stack := v28 :: q3 :: q2 :: q1 :: q4 :: z0 :: v25 :: x2 :: x3 :: x4 :: n1 :: n2 :: n3 :: n4 :: P :: inv :: cnt :: rest} := by
    simpa only [sqCol6part8Model, v26, v27, v28] using sqCol6part8_run (s) v24 v10 q3 q2 q1 q4 z0 v25 x2 x3 x4 n1 n2 n3 n4 P inv cnt rest hcap hact
  exact (runInstructions_append_some _ _ _ _ _ h0 (runInstructions_append_some _ _ _ _ _ h1 (runInstructions_append_some _ _ _ _ _ h2 (runInstructions_append_some _ _ _ _ _ h3 (runInstructions_append_some _ _ _ _ _ h4 (runInstructions_append_some _ _ _ _ _ h5 (runInstructions_append_some _ _ _ _ _ h6 (runInstructions_append_some _ _ _ _ _ h7 h8))))))))

def sqCol6_o0 (c q3 q2 q1 q4 z0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cnt : UInt256) : UInt256 :=
  ((UInt256.shiftRight ((q4 * n2) + ((q3 * n3) + ((q2 * n4) + ((x3 * x3) + (((x2 * x4) + (x2 * x4)) + c))))) (UInt256.ofNat 240)) + (UInt256.shiftLeft (UInt256.shiftRight (UInt256.addMod (UInt256.lnot ((q4 * n2) + ((q3 * n3) + ((q2 * n4) + ((x3 * x3) + (((x2 * x4) + (x2 * x4)) + c)))))) ((UInt256.mulMod q4 n2 P) + ((UInt256.mulMod q3 n3 P) + ((UInt256.mulMod q2 n4 P) + ((UInt256.mulMod x3 x3 P) + (((UInt256.mulMod x2 x4 P) + (UInt256.mulMod x2 x4 P)) + c))))) P) (UInt256.ofNat 5)) (UInt256.ofNat 16)))

def sqCol6_o6 (c q3 q2 q1 q4 z0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cnt : UInt256) : UInt256 :=
  (UInt256.land (UInt256.ofNat 1766847064778384329583297500742918515827483896875618958121606201292619775) ((q4 * n2) + ((q3 * n3) + ((q2 * n4) + ((x3 * x3) + (((x2 * x4) + (x2 * x4)) + c))))))

theorem sqCol6_eq (s : State) (c q3 q2 q1 q4 z0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cnt : UInt256) (rest : List UInt256) :
    sqCol6Model s c q3 q2 q1 q4 z0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cnt rest =
      {s with pc := UInt256.ofNat 4546, stack := (sqCol6_o0 c q3 q2 q1 q4 z0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cnt) :: q3 :: q2 :: q1 :: q4 :: z0 :: (sqCol6_o6 c q3 q2 q1 q4 z0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cnt) :: x2 :: x3 :: x4 :: n1 :: n2 :: n3 :: n4 :: P :: inv :: cnt :: rest} := by
  simp only [sqCol6Model, sqCol6_o0, sqCol6_o6]

/-! ## sqCol7: pc 4546..4630, 51 instructions -/

def sqCol7part0Program : List Instr :=
  [.op (.Dup ⟨0, by decide⟩),
   .op (.Dup ⟨10, by decide⟩),
   .op (.Dup ⟨10, by decide⟩),
   .op .MUL,
   .op (.Dup ⟨0, by decide⟩),
   .op .ADD,
   .op .ADD,
   .op (.Dup ⟨14, by decide⟩)]

def sqCol7part0Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 : UInt256) (rest : List UInt256) : State :=
  let v0 : UInt256 := x8 * x9
  let v1 : UInt256 := v0 + v0
  let v2 : UInt256 := v1 + x0
  {s with pc := UInt256.ofNat 4554, memory := s.memory, stack := x13 :: v2 :: x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: rest}

theorem sqCol7part0_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions sqCol7part0Program {s with pc := UInt256.ofNat 4546, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: rest} =
      some (sqCol7part0Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 rest) := by
  have hc (j : Nat) (hj : j ≤ 33) : rest.length + j < 1024 := by omega
  have hcr : rest.length < 1024 := by omega
  simp [hz, hzn, sqCol7part0Program, sqCol7part0Model, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, ofNat_sub_ofNat, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, hc, hcr]

def sqCol7part1Program : List Instr :=
  [.op (.Dup ⟨3, by decide⟩),
   .op .MUL,
   .op .ADD,
   .op (.Dup ⟨13, by decide⟩),
   .op (.Dup ⟨6, by decide⟩),
   .op .MUL,
   .op .ADD,
   .op (.Swap ⟨0, by decide⟩)]

def sqCol7part1Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 : UInt256) (rest : List UInt256) : State :=
  let v0 : UInt256 := x3 * x0
  let v1 : UInt256 := v0 + x1
  let v2 : UInt256 := x6 * x14
  let v3 : UInt256 := v2 + v1
  {s with pc := UInt256.ofNat 4562, memory := s.memory, stack := x2 :: v3 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: x18 :: rest}

theorem sqCol7part1_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions sqCol7part1Program {s with pc := UInt256.ofNat 4554, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: x18 :: rest} =
      some (sqCol7part1Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 rest) := by
  have hc (j : Nat) (hj : j ≤ 33) : rest.length + j < 1024 := by omega
  have hcr : rest.length < 1024 := by omega
  simp [hz, hzn, sqCol7part1Program, sqCol7part1Model, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, ofNat_sub_ofNat, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, hc, hcr]

def sqCol7part2Program : List Instr :=
  [.op (.Dup ⟨15, by decide⟩),
   .op (.Dup ⟨11, by decide⟩),
   .op (.Dup ⟨11, by decide⟩),
   .op .MULMOD,
   .op (.Dup ⟨0, by decide⟩),
   .op .ADD,
   .op .ADD,
   .op (.Dup ⟨15, by decide⟩)]

def sqCol7part2Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 : UInt256) (rest : List UInt256) : State :=
  let v0 : UInt256 := UInt256.mulMod x9 x10 x15
  let v1 : UInt256 := v0 + v0
  let v2 : UInt256 := v1 + x0
  {s with pc := UInt256.ofNat 4570, memory := s.memory, stack := x15 :: v2 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: rest}

theorem sqCol7part2_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions sqCol7part2Program {s with pc := UInt256.ofNat 4562, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: rest} =
      some (sqCol7part2Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 rest) := by
  have hc (j : Nat) (hj : j ≤ 34) : rest.length + j < 1024 := by omega
  have hcr : rest.length < 1024 := by omega
  simp [hz, hzn, sqCol7part2Program, sqCol7part2Model, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, ofNat_sub_ofNat, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, hc, hcr]

def sqCol7part3Program : List Instr :=
  [.op (.Dup ⟨15, by decide⟩),
   .op (.Dup ⟨4, by decide⟩),
   .op .MULMOD,
   .op .ADD,
   .op (.Dup ⟨15, by decide⟩),
   .op (.Dup ⟨14, by decide⟩),
   .op (.Dup ⟨7, by decide⟩),
   .op .MULMOD]

def sqCol7part3Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 : UInt256) (rest : List UInt256) : State :=
  let v0 : UInt256 := UInt256.mulMod x3 x15 x0
  let v1 : UInt256 := v0 + x1
  let v2 : UInt256 := UInt256.mulMod x6 x14 x16
  {s with pc := UInt256.ofNat 4578, memory := s.memory, stack := v2 :: v1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: x18 :: rest}

theorem sqCol7part3_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions sqCol7part3Program {s with pc := UInt256.ofNat 4570, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: x18 :: rest} =
      some (sqCol7part3Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 rest) := by
  have hc (j : Nat) (hj : j ≤ 34) : rest.length + j < 1024 := by omega
  have hcr : rest.length < 1024 := by omega
  simp [hz, hzn, sqCol7part3Program, sqCol7part3Model, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, ofNat_sub_ofNat, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, hc, hcr]

def sqCol7part4Program : List Instr :=
  [.op .ADD,
   .op (.Dup ⟨15, by decide⟩),
   .op (.Swap ⟨0, by decide⟩),
   .op (.Dup ⟨2, by decide⟩),
   .op .NOT,
   .op .ADDMOD,
   .push 1 5,
   .op .SHR]

def sqCol7part4Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 : UInt256) (rest : List UInt256) : State :=
  let v0 : UInt256 := x0 + x1
  let v1 : UInt256 := UInt256.lnot x2
  let v2 : UInt256 := UInt256.addMod v1 v0 x16
  let v3 : UInt256 := UInt256.shiftRight v2 (UInt256.ofNat 5)
  {s with pc := UInt256.ofNat 4587, memory := s.memory, stack := v3 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: x18 :: rest}

theorem sqCol7part4_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions sqCol7part4Program {s with pc := UInt256.ofNat 4578, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: x18 :: rest} =
      some (sqCol7part4Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 rest) := by
  have hc (j : Nat) (hj : j ≤ 33) : rest.length + j < 1024 := by omega
  have hcr : rest.length < 1024 := by omega
  simp [hz, hzn, sqCol7part4Program, sqCol7part4Model, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, ofNat_sub_ofNat, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, hc, hcr]

def sqCol7part5Program : List Instr :=
  [.op (.Dup ⟨1, by decide⟩),
   .push 30 1766847064778384329583297500742918515827483896875618958121606201292619775,
   .op .AND,
   .op (.Swap ⟨8, by decide⟩),
   .op .POP,
   .push 1 16,
   .op .SHL,
   .op (.Swap ⟨0, by decide⟩)]

def sqCol7part5Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 : UInt256) (rest : List UInt256) : State :=
  let v0 : UInt256 := UInt256.land (UInt256.ofNat 1766847064778384329583297500742918515827483896875618958121606201292619775) x1
  let v1 : UInt256 := UInt256.shiftLeft x0 (UInt256.ofNat 16)
  {s with pc := UInt256.ofNat 4626, memory := s.memory, stack := x1 :: v1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: v0 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: rest}

theorem sqCol7part5_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions sqCol7part5Program {s with pc := UInt256.ofNat 4587, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: rest} =
      some (sqCol7part5Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 rest) := by
  have hc (j : Nat) (hj : j ≤ 33) : rest.length + j < 1024 := by omega
  have hcr : rest.length < 1024 := by omega
  simp [hz, hzn, sqCol7part5Program, sqCol7part5Model, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, ofNat_sub_ofNat, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, hc, hcr]

def sqCol7part6Program : List Instr :=
  [.push 1 240,
   .op .SHR,
   .op .ADD]

def sqCol7part6Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 : UInt256) (rest : List UInt256) : State :=
  let v0 : UInt256 := UInt256.shiftRight x0 (UInt256.ofNat 240)
  let v1 : UInt256 := v0 + x1
  {s with pc := UInt256.ofNat 4630, memory := s.memory, stack := v1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: rest}

theorem sqCol7part6_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions sqCol7part6Program {s with pc := UInt256.ofNat 4626, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: rest} =
      some (sqCol7part6Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 rest) := by
  have hc (j : Nat) (hj : j ≤ 32) : rest.length + j < 1024 := by omega
  have hcr : rest.length < 1024 := by omega
  simp [hz, hzn, sqCol7part6Program, sqCol7part6Model, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, ofNat_sub_ofNat, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, hc, hcr]

def sqCol7Program : List Instr :=
  [.op (.Dup ⟨0, by decide⟩),
   .op (.Dup ⟨10, by decide⟩),
   .op (.Dup ⟨10, by decide⟩),
   .op .MUL,
   .op (.Dup ⟨0, by decide⟩),
   .op .ADD,
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
   .op (.Dup ⟨11, by decide⟩),
   .op (.Dup ⟨11, by decide⟩),
   .op .MULMOD,
   .op (.Dup ⟨0, by decide⟩),
   .op .ADD,
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
   .push 30 1766847064778384329583297500742918515827483896875618958121606201292619775,
   .op .AND,
   .op (.Swap ⟨8, by decide⟩),
   .op .POP,
   .push 1 16,
   .op .SHL,
   .op (.Swap ⟨0, by decide⟩),
   .push 1 240,
   .op .SHR,
   .op .ADD]

def sqCol7Model (s : State) (c q3 q2 q1 q4 z0 z1 x2 x3 x4 n1 n2 n3 n4 P inv cnt : UInt256) (rest : List UInt256) : State :=
  let v0 : UInt256 := x3 * x4
  let v1 : UInt256 := v0 + v0
  let v2 : UInt256 := v1 + c
  let v3 : UInt256 := q3 * n4
  let v4 : UInt256 := v3 + v2
  let v5 : UInt256 := q4 * n3
  let v6 : UInt256 := v5 + v4
  let v7 : UInt256 := UInt256.mulMod x3 x4 P
  let v8 : UInt256 := v7 + v7
  let v9 : UInt256 := v8 + c
  let v10 : UInt256 := UInt256.mulMod q3 n4 P
  let v11 : UInt256 := v10 + v9
  let v12 : UInt256 := UInt256.mulMod q4 n3 P
  let v13 : UInt256 := v12 + v11
  let v14 : UInt256 := UInt256.lnot v6
  let v15 : UInt256 := UInt256.addMod v14 v13 P
  let v16 : UInt256 := UInt256.shiftRight v15 (UInt256.ofNat 5)
  let v17 : UInt256 := UInt256.land (UInt256.ofNat 1766847064778384329583297500742918515827483896875618958121606201292619775) v6
  let v18 : UInt256 := UInt256.shiftLeft v16 (UInt256.ofNat 16)
  let v19 : UInt256 := UInt256.shiftRight v6 (UInt256.ofNat 240)
  let v20 : UInt256 := v19 + v18
  {s with pc := UInt256.ofNat 4630, memory := s.memory, stack := v20 :: q3 :: q2 :: q1 :: q4 :: z0 :: z1 :: v17 :: x3 :: x4 :: n1 :: n2 :: n3 :: n4 :: P :: inv :: cnt :: rest}

theorem sqCol7_run (s : State) (c q3 q2 q1 q4 z0 z1 x2 x3 x4 n1 n2 n3 n4 P inv cnt : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions sqCol7Program {s with pc := UInt256.ofNat 4546, stack := c :: q3 :: q2 :: q1 :: q4 :: z0 :: z1 :: x2 :: x3 :: x4 :: n1 :: n2 :: n3 :: n4 :: P :: inv :: cnt :: rest} =
      some (sqCol7Model s c q3 q2 q1 q4 z0 z1 x2 x3 x4 n1 n2 n3 n4 P inv cnt rest) := by
  let v0 : UInt256 := x3 * x4
  let v1 : UInt256 := v0 + v0
  let v2 : UInt256 := v1 + c
  let v3 : UInt256 := q3 * n4
  let v4 : UInt256 := v3 + v2
  let v5 : UInt256 := q4 * n3
  let v6 : UInt256 := v5 + v4
  let v7 : UInt256 := UInt256.mulMod x3 x4 P
  let v8 : UInt256 := v7 + v7
  let v9 : UInt256 := v8 + c
  let v10 : UInt256 := UInt256.mulMod q3 n4 P
  let v11 : UInt256 := v10 + v9
  let v12 : UInt256 := UInt256.mulMod q4 n3 P
  let v13 : UInt256 := v12 + v11
  let v14 : UInt256 := UInt256.lnot v6
  let v15 : UInt256 := UInt256.addMod v14 v13 P
  let v16 : UInt256 := UInt256.shiftRight v15 (UInt256.ofNat 5)
  let v17 : UInt256 := UInt256.land (UInt256.ofNat 1766847064778384329583297500742918515827483896875618958121606201292619775) v6
  let v18 : UInt256 := UInt256.shiftLeft v16 (UInt256.ofNat 16)
  let v19 : UInt256 := UInt256.shiftRight v6 (UInt256.ofNat 240)
  let v20 : UInt256 := v19 + v18
  have h0 : runInstructions sqCol7part0Program {s with pc := UInt256.ofNat 4546, memory := s.memory, stack := c :: q3 :: q2 :: q1 :: q4 :: z0 :: z1 :: x2 :: x3 :: x4 :: n1 :: n2 :: n3 :: n4 :: P :: inv :: cnt :: rest} = some {s with pc := UInt256.ofNat 4554, memory := s.memory, stack := n4 :: v2 :: c :: q3 :: q2 :: q1 :: q4 :: z0 :: z1 :: x2 :: x3 :: x4 :: n1 :: n2 :: n3 :: n4 :: P :: inv :: cnt :: rest} := by
    simpa only [sqCol7part0Model, v0, v1, v2] using sqCol7part0_run (s) c q3 q2 q1 q4 z0 z1 x2 x3 x4 n1 n2 n3 n4 P inv cnt rest hcap hact
  have h1 : runInstructions sqCol7part1Program {s with pc := UInt256.ofNat 4554, memory := s.memory, stack := n4 :: v2 :: c :: q3 :: q2 :: q1 :: q4 :: z0 :: z1 :: x2 :: x3 :: x4 :: n1 :: n2 :: n3 :: n4 :: P :: inv :: cnt :: rest} = some {s with pc := UInt256.ofNat 4562, memory := s.memory, stack := c :: v6 :: q3 :: q2 :: q1 :: q4 :: z0 :: z1 :: x2 :: x3 :: x4 :: n1 :: n2 :: n3 :: n4 :: P :: inv :: cnt :: rest} := by
    simpa only [sqCol7part1Model, v3, v4, v5, v6] using sqCol7part1_run (s) n4 v2 c q3 q2 q1 q4 z0 z1 x2 x3 x4 n1 n2 n3 n4 P inv cnt rest hcap hact
  have h2 : runInstructions sqCol7part2Program {s with pc := UInt256.ofNat 4562, memory := s.memory, stack := c :: v6 :: q3 :: q2 :: q1 :: q4 :: z0 :: z1 :: x2 :: x3 :: x4 :: n1 :: n2 :: n3 :: n4 :: P :: inv :: cnt :: rest} = some {s with pc := UInt256.ofNat 4570, memory := s.memory, stack := P :: v9 :: v6 :: q3 :: q2 :: q1 :: q4 :: z0 :: z1 :: x2 :: x3 :: x4 :: n1 :: n2 :: n3 :: n4 :: P :: inv :: cnt :: rest} := by
    simpa only [sqCol7part2Model, v7, v8, v9] using sqCol7part2_run (s) c v6 q3 q2 q1 q4 z0 z1 x2 x3 x4 n1 n2 n3 n4 P inv cnt rest hcap hact
  have h3 : runInstructions sqCol7part3Program {s with pc := UInt256.ofNat 4570, memory := s.memory, stack := P :: v9 :: v6 :: q3 :: q2 :: q1 :: q4 :: z0 :: z1 :: x2 :: x3 :: x4 :: n1 :: n2 :: n3 :: n4 :: P :: inv :: cnt :: rest} = some {s with pc := UInt256.ofNat 4578, memory := s.memory, stack := v12 :: v11 :: v6 :: q3 :: q2 :: q1 :: q4 :: z0 :: z1 :: x2 :: x3 :: x4 :: n1 :: n2 :: n3 :: n4 :: P :: inv :: cnt :: rest} := by
    simpa only [sqCol7part3Model, v10, v11, v12] using sqCol7part3_run (s) P v9 v6 q3 q2 q1 q4 z0 z1 x2 x3 x4 n1 n2 n3 n4 P inv cnt rest hcap hact
  have h4 : runInstructions sqCol7part4Program {s with pc := UInt256.ofNat 4578, memory := s.memory, stack := v12 :: v11 :: v6 :: q3 :: q2 :: q1 :: q4 :: z0 :: z1 :: x2 :: x3 :: x4 :: n1 :: n2 :: n3 :: n4 :: P :: inv :: cnt :: rest} = some {s with pc := UInt256.ofNat 4587, memory := s.memory, stack := v16 :: v6 :: q3 :: q2 :: q1 :: q4 :: z0 :: z1 :: x2 :: x3 :: x4 :: n1 :: n2 :: n3 :: n4 :: P :: inv :: cnt :: rest} := by
    simpa only [sqCol7part4Model, v13, v14, v15, v16] using sqCol7part4_run (s) v12 v11 v6 q3 q2 q1 q4 z0 z1 x2 x3 x4 n1 n2 n3 n4 P inv cnt rest hcap hact
  have h5 : runInstructions sqCol7part5Program {s with pc := UInt256.ofNat 4587, memory := s.memory, stack := v16 :: v6 :: q3 :: q2 :: q1 :: q4 :: z0 :: z1 :: x2 :: x3 :: x4 :: n1 :: n2 :: n3 :: n4 :: P :: inv :: cnt :: rest} = some {s with pc := UInt256.ofNat 4626, memory := s.memory, stack := v6 :: v18 :: q3 :: q2 :: q1 :: q4 :: z0 :: z1 :: v17 :: x3 :: x4 :: n1 :: n2 :: n3 :: n4 :: P :: inv :: cnt :: rest} := by
    simpa only [sqCol7part5Model, v17, v18] using sqCol7part5_run (s) v16 v6 q3 q2 q1 q4 z0 z1 x2 x3 x4 n1 n2 n3 n4 P inv cnt rest hcap hact
  have h6 : runInstructions sqCol7part6Program {s with pc := UInt256.ofNat 4626, memory := s.memory, stack := v6 :: v18 :: q3 :: q2 :: q1 :: q4 :: z0 :: z1 :: v17 :: x3 :: x4 :: n1 :: n2 :: n3 :: n4 :: P :: inv :: cnt :: rest} = some {s with pc := UInt256.ofNat 4630, memory := s.memory, stack := v20 :: q3 :: q2 :: q1 :: q4 :: z0 :: z1 :: v17 :: x3 :: x4 :: n1 :: n2 :: n3 :: n4 :: P :: inv :: cnt :: rest} := by
    simpa only [sqCol7part6Model, v19, v20] using sqCol7part6_run (s) v6 v18 q3 q2 q1 q4 z0 z1 v17 x3 x4 n1 n2 n3 n4 P inv cnt rest hcap hact
  exact (runInstructions_append_some _ _ _ _ _ h0 (runInstructions_append_some _ _ _ _ _ h1 (runInstructions_append_some _ _ _ _ _ h2 (runInstructions_append_some _ _ _ _ _ h3 (runInstructions_append_some _ _ _ _ _ h4 (runInstructions_append_some _ _ _ _ _ h5 h6))))))

def sqCol7_o0 (c q3 q2 q1 q4 z0 z1 x2 x3 x4 n1 n2 n3 n4 P inv cnt : UInt256) : UInt256 :=
  ((UInt256.shiftRight ((q4 * n3) + ((q3 * n4) + (((x3 * x4) + (x3 * x4)) + c))) (UInt256.ofNat 240)) + (UInt256.shiftLeft (UInt256.shiftRight (UInt256.addMod (UInt256.lnot ((q4 * n3) + ((q3 * n4) + (((x3 * x4) + (x3 * x4)) + c)))) ((UInt256.mulMod q4 n3 P) + ((UInt256.mulMod q3 n4 P) + (((UInt256.mulMod x3 x4 P) + (UInt256.mulMod x3 x4 P)) + c))) P) (UInt256.ofNat 5)) (UInt256.ofNat 16)))

def sqCol7_o7 (c q3 q2 q1 q4 z0 z1 x2 x3 x4 n1 n2 n3 n4 P inv cnt : UInt256) : UInt256 :=
  (UInt256.land (UInt256.ofNat 1766847064778384329583297500742918515827483896875618958121606201292619775) ((q4 * n3) + ((q3 * n4) + (((x3 * x4) + (x3 * x4)) + c))))

theorem sqCol7_eq (s : State) (c q3 q2 q1 q4 z0 z1 x2 x3 x4 n1 n2 n3 n4 P inv cnt : UInt256) (rest : List UInt256) :
    sqCol7Model s c q3 q2 q1 q4 z0 z1 x2 x3 x4 n1 n2 n3 n4 P inv cnt rest =
      {s with pc := UInt256.ofNat 4630, stack := (sqCol7_o0 c q3 q2 q1 q4 z0 z1 x2 x3 x4 n1 n2 n3 n4 P inv cnt) :: q3 :: q2 :: q1 :: q4 :: z0 :: z1 :: (sqCol7_o7 c q3 q2 q1 q4 z0 z1 x2 x3 x4 n1 n2 n3 n4 P inv cnt) :: x3 :: x4 :: n1 :: n2 :: n3 :: n4 :: P :: inv :: cnt :: rest} := by
  simp only [sqCol7Model, sqCol7_o0, sqCol7_o7]

/-! ## sqCol8: pc 4630..4701, 38 instructions -/

def sqCol8part0Program : List Instr :=
  [.op (.Dup ⟨0, by decide⟩),
   .op (.Dup ⟨10, by decide⟩),
   .op (.Dup ⟨0, by decide⟩),
   .op .MUL,
   .op .ADD,
   .op (.Dup ⟨14, by decide⟩),
   .op (.Dup ⟨6, by decide⟩),
   .op .MUL]

def sqCol8part0Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 : UInt256) (rest : List UInt256) : State :=
  let v0 : UInt256 := x9 * x9
  let v1 : UInt256 := v0 + x0
  let v2 : UInt256 := x4 * x13
  {s with pc := UInt256.ofNat 4638, memory := s.memory, stack := v2 :: v1 :: x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: rest}

theorem sqCol8part0_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions sqCol8part0Program {s with pc := UInt256.ofNat 4630, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: rest} =
      some (sqCol8part0Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 rest) := by
  have hc (j : Nat) (hj : j ≤ 33) : rest.length + j < 1024 := by omega
  have hcr : rest.length < 1024 := by omega
  simp [hz, hzn, sqCol8part0Program, sqCol8part0Model, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, ofNat_sub_ofNat, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, hc, hcr]

def sqCol8part1Program : List Instr :=
  [.op .ADD,
   .op (.Swap ⟨0, by decide⟩),
   .op (.Dup ⟨15, by decide⟩),
   .op (.Dup ⟨11, by decide⟩),
   .op (.Dup ⟨0, by decide⟩),
   .op .MULMOD,
   .op .ADD,
   .op (.Dup ⟨15, by decide⟩)]

def sqCol8part1Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 : UInt256) (rest : List UInt256) : State :=
  let v0 : UInt256 := x0 + x1
  let v1 : UInt256 := UInt256.mulMod x11 x11 x16
  let v2 : UInt256 := v1 + x2
  {s with pc := UInt256.ofNat 4646, memory := s.memory, stack := x16 :: v2 :: v0 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: x18 :: rest}

theorem sqCol8part1_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions sqCol8part1Program {s with pc := UInt256.ofNat 4638, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: x18 :: rest} =
      some (sqCol8part1Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 rest) := by
  have hc (j : Nat) (hj : j ≤ 34) : rest.length + j < 1024 := by omega
  have hcr : rest.length < 1024 := by omega
  simp [hz, hzn, sqCol8part1Program, sqCol8part1Model, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, ofNat_sub_ofNat, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, hc, hcr]

def sqCol8part2Program : List Instr :=
  [.op (.Dup ⟨15, by decide⟩),
   .op (.Dup ⟨7, by decide⟩),
   .op .MULMOD,
   .op .ADD,
   .op (.Dup ⟨15, by decide⟩),
   .op (.Swap ⟨0, by decide⟩),
   .op (.Dup ⟨2, by decide⟩),
   .op .NOT]

def sqCol8part2Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 : UInt256) (rest : List UInt256) : State :=
  let v0 : UInt256 := UInt256.mulMod x6 x15 x0
  let v1 : UInt256 := v0 + x1
  let v2 : UInt256 := UInt256.lnot x2
  {s with pc := UInt256.ofNat 4654, memory := s.memory, stack := v2 :: v1 :: x16 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: x18 :: rest}

theorem sqCol8part2_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions sqCol8part2Program {s with pc := UInt256.ofNat 4646, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: x18 :: rest} =
      some (sqCol8part2Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 rest) := by
  have hc (j : Nat) (hj : j ≤ 34) : rest.length + j < 1024 := by omega
  have hcr : rest.length < 1024 := by omega
  simp [hz, hzn, sqCol8part2Program, sqCol8part2Model, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, ofNat_sub_ofNat, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, hc, hcr]

def sqCol8part3Program : List Instr :=
  [.op .ADDMOD,
   .push 1 5,
   .op .SHR,
   .op (.Dup ⟨1, by decide⟩),
   .push 30 1766847064778384329583297500742918515827483896875618958121606201292619775,
   .op .AND,
   .op (.Swap ⟨9, by decide⟩),
   .op .POP]

def sqCol8part3Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 : UInt256) (rest : List UInt256) : State :=
  let v0 : UInt256 := UInt256.addMod x0 x1 x2
  let v1 : UInt256 := UInt256.shiftRight v0 (UInt256.ofNat 5)
  let v2 : UInt256 := UInt256.land (UInt256.ofNat 1766847064778384329583297500742918515827483896875618958121606201292619775) x3
  {s with pc := UInt256.ofNat 4693, memory := s.memory, stack := v1 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: v2 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: x18 :: x19 :: rest}

theorem sqCol8part3_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions sqCol8part3Program {s with pc := UInt256.ofNat 4654, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: x18 :: x19 :: rest} =
      some (sqCol8part3Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 rest) := by
  have hc (j : Nat) (hj : j ≤ 33) : rest.length + j < 1024 := by omega
  have hcr : rest.length < 1024 := by omega
  simp [hz, hzn, sqCol8part3Program, sqCol8part3Model, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, ofNat_sub_ofNat, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, hc, hcr]

def sqCol8part4Program : List Instr :=
  [.push 1 16,
   .op .SHL,
   .op (.Swap ⟨0, by decide⟩),
   .push 1 240,
   .op .SHR,
   .op .ADD]

def sqCol8part4Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 : UInt256) (rest : List UInt256) : State :=
  let v0 : UInt256 := UInt256.shiftLeft x0 (UInt256.ofNat 16)
  let v1 : UInt256 := UInt256.shiftRight x1 (UInt256.ofNat 240)
  let v2 : UInt256 := v1 + v0
  {s with pc := UInt256.ofNat 4701, memory := s.memory, stack := v2 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: rest}

theorem sqCol8part4_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions sqCol8part4Program {s with pc := UInt256.ofNat 4693, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: rest} =
      some (sqCol8part4Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 rest) := by
  have hc (j : Nat) (hj : j ≤ 32) : rest.length + j < 1024 := by omega
  have hcr : rest.length < 1024 := by omega
  simp [hz, hzn, sqCol8part4Program, sqCol8part4Model, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, ofNat_sub_ofNat, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, hc, hcr]

def sqCol8Program : List Instr :=
  [.op (.Dup ⟨0, by decide⟩),
   .op (.Dup ⟨10, by decide⟩),
   .op (.Dup ⟨0, by decide⟩),
   .op .MUL,
   .op .ADD,
   .op (.Dup ⟨14, by decide⟩),
   .op (.Dup ⟨6, by decide⟩),
   .op .MUL,
   .op .ADD,
   .op (.Swap ⟨0, by decide⟩),
   .op (.Dup ⟨15, by decide⟩),
   .op (.Dup ⟨11, by decide⟩),
   .op (.Dup ⟨0, by decide⟩),
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
   .push 30 1766847064778384329583297500742918515827483896875618958121606201292619775,
   .op .AND,
   .op (.Swap ⟨9, by decide⟩),
   .op .POP,
   .push 1 16,
   .op .SHL,
   .op (.Swap ⟨0, by decide⟩),
   .push 1 240,
   .op .SHR,
   .op .ADD]

def sqCol8Model (s : State) (c q3 q2 q1 q4 z0 z1 z2 x3 x4 n1 n2 n3 n4 P inv cnt : UInt256) (rest : List UInt256) : State :=
  let v0 : UInt256 := x4 * x4
  let v1 : UInt256 := v0 + c
  let v2 : UInt256 := q4 * n4
  let v3 : UInt256 := v2 + v1
  let v4 : UInt256 := UInt256.mulMod x4 x4 P
  let v5 : UInt256 := v4 + c
  let v6 : UInt256 := UInt256.mulMod q4 n4 P
  let v7 : UInt256 := v6 + v5
  let v8 : UInt256 := UInt256.lnot v3
  let v9 : UInt256 := UInt256.addMod v8 v7 P
  let v10 : UInt256 := UInt256.shiftRight v9 (UInt256.ofNat 5)
  let v11 : UInt256 := UInt256.land (UInt256.ofNat 1766847064778384329583297500742918515827483896875618958121606201292619775) v3
  let v12 : UInt256 := UInt256.shiftLeft v10 (UInt256.ofNat 16)
  let v13 : UInt256 := UInt256.shiftRight v3 (UInt256.ofNat 240)
  let v14 : UInt256 := v13 + v12
  {s with pc := UInt256.ofNat 4701, memory := s.memory, stack := v14 :: q3 :: q2 :: q1 :: q4 :: z0 :: z1 :: z2 :: v11 :: x4 :: n1 :: n2 :: n3 :: n4 :: P :: inv :: cnt :: rest}

theorem sqCol8_run (s : State) (c q3 q2 q1 q4 z0 z1 z2 x3 x4 n1 n2 n3 n4 P inv cnt : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions sqCol8Program {s with pc := UInt256.ofNat 4630, stack := c :: q3 :: q2 :: q1 :: q4 :: z0 :: z1 :: z2 :: x3 :: x4 :: n1 :: n2 :: n3 :: n4 :: P :: inv :: cnt :: rest} =
      some (sqCol8Model s c q3 q2 q1 q4 z0 z1 z2 x3 x4 n1 n2 n3 n4 P inv cnt rest) := by
  let v0 : UInt256 := x4 * x4
  let v1 : UInt256 := v0 + c
  let v2 : UInt256 := q4 * n4
  let v3 : UInt256 := v2 + v1
  let v4 : UInt256 := UInt256.mulMod x4 x4 P
  let v5 : UInt256 := v4 + c
  let v6 : UInt256 := UInt256.mulMod q4 n4 P
  let v7 : UInt256 := v6 + v5
  let v8 : UInt256 := UInt256.lnot v3
  let v9 : UInt256 := UInt256.addMod v8 v7 P
  let v10 : UInt256 := UInt256.shiftRight v9 (UInt256.ofNat 5)
  let v11 : UInt256 := UInt256.land (UInt256.ofNat 1766847064778384329583297500742918515827483896875618958121606201292619775) v3
  let v12 : UInt256 := UInt256.shiftLeft v10 (UInt256.ofNat 16)
  let v13 : UInt256 := UInt256.shiftRight v3 (UInt256.ofNat 240)
  let v14 : UInt256 := v13 + v12
  have h0 : runInstructions sqCol8part0Program {s with pc := UInt256.ofNat 4630, memory := s.memory, stack := c :: q3 :: q2 :: q1 :: q4 :: z0 :: z1 :: z2 :: x3 :: x4 :: n1 :: n2 :: n3 :: n4 :: P :: inv :: cnt :: rest} = some {s with pc := UInt256.ofNat 4638, memory := s.memory, stack := v2 :: v1 :: c :: q3 :: q2 :: q1 :: q4 :: z0 :: z1 :: z2 :: x3 :: x4 :: n1 :: n2 :: n3 :: n4 :: P :: inv :: cnt :: rest} := by
    simpa only [sqCol8part0Model, v0, v1, v2] using sqCol8part0_run (s) c q3 q2 q1 q4 z0 z1 z2 x3 x4 n1 n2 n3 n4 P inv cnt rest hcap hact
  have h1 : runInstructions sqCol8part1Program {s with pc := UInt256.ofNat 4638, memory := s.memory, stack := v2 :: v1 :: c :: q3 :: q2 :: q1 :: q4 :: z0 :: z1 :: z2 :: x3 :: x4 :: n1 :: n2 :: n3 :: n4 :: P :: inv :: cnt :: rest} = some {s with pc := UInt256.ofNat 4646, memory := s.memory, stack := P :: v5 :: v3 :: q3 :: q2 :: q1 :: q4 :: z0 :: z1 :: z2 :: x3 :: x4 :: n1 :: n2 :: n3 :: n4 :: P :: inv :: cnt :: rest} := by
    simpa only [sqCol8part1Model, v3, v4, v5] using sqCol8part1_run (s) v2 v1 c q3 q2 q1 q4 z0 z1 z2 x3 x4 n1 n2 n3 n4 P inv cnt rest hcap hact
  have h2 : runInstructions sqCol8part2Program {s with pc := UInt256.ofNat 4646, memory := s.memory, stack := P :: v5 :: v3 :: q3 :: q2 :: q1 :: q4 :: z0 :: z1 :: z2 :: x3 :: x4 :: n1 :: n2 :: n3 :: n4 :: P :: inv :: cnt :: rest} = some {s with pc := UInt256.ofNat 4654, memory := s.memory, stack := v8 :: v7 :: P :: v3 :: q3 :: q2 :: q1 :: q4 :: z0 :: z1 :: z2 :: x3 :: x4 :: n1 :: n2 :: n3 :: n4 :: P :: inv :: cnt :: rest} := by
    simpa only [sqCol8part2Model, v6, v7, v8] using sqCol8part2_run (s) P v5 v3 q3 q2 q1 q4 z0 z1 z2 x3 x4 n1 n2 n3 n4 P inv cnt rest hcap hact
  have h3 : runInstructions sqCol8part3Program {s with pc := UInt256.ofNat 4654, memory := s.memory, stack := v8 :: v7 :: P :: v3 :: q3 :: q2 :: q1 :: q4 :: z0 :: z1 :: z2 :: x3 :: x4 :: n1 :: n2 :: n3 :: n4 :: P :: inv :: cnt :: rest} = some {s with pc := UInt256.ofNat 4693, memory := s.memory, stack := v10 :: v3 :: q3 :: q2 :: q1 :: q4 :: z0 :: z1 :: z2 :: v11 :: x4 :: n1 :: n2 :: n3 :: n4 :: P :: inv :: cnt :: rest} := by
    simpa only [sqCol8part3Model, v9, v10, v11] using sqCol8part3_run (s) v8 v7 P v3 q3 q2 q1 q4 z0 z1 z2 x3 x4 n1 n2 n3 n4 P inv cnt rest hcap hact
  have h4 : runInstructions sqCol8part4Program {s with pc := UInt256.ofNat 4693, memory := s.memory, stack := v10 :: v3 :: q3 :: q2 :: q1 :: q4 :: z0 :: z1 :: z2 :: v11 :: x4 :: n1 :: n2 :: n3 :: n4 :: P :: inv :: cnt :: rest} = some {s with pc := UInt256.ofNat 4701, memory := s.memory, stack := v14 :: q3 :: q2 :: q1 :: q4 :: z0 :: z1 :: z2 :: v11 :: x4 :: n1 :: n2 :: n3 :: n4 :: P :: inv :: cnt :: rest} := by
    simpa only [sqCol8part4Model, v12, v13, v14] using sqCol8part4_run (s) v10 v3 q3 q2 q1 q4 z0 z1 z2 v11 x4 n1 n2 n3 n4 P inv cnt rest hcap hact
  exact (runInstructions_append_some _ _ _ _ _ h0 (runInstructions_append_some _ _ _ _ _ h1 (runInstructions_append_some _ _ _ _ _ h2 (runInstructions_append_some _ _ _ _ _ h3 h4))))

def sqCol8_o0 (c q3 q2 q1 q4 z0 z1 z2 x3 x4 n1 n2 n3 n4 P inv cnt : UInt256) : UInt256 :=
  ((UInt256.shiftRight ((q4 * n4) + ((x4 * x4) + c)) (UInt256.ofNat 240)) + (UInt256.shiftLeft (UInt256.shiftRight (UInt256.addMod (UInt256.lnot ((q4 * n4) + ((x4 * x4) + c))) ((UInt256.mulMod q4 n4 P) + ((UInt256.mulMod x4 x4 P) + c)) P) (UInt256.ofNat 5)) (UInt256.ofNat 16)))

def sqCol8_o8 (c q3 q2 q1 q4 z0 z1 z2 x3 x4 n1 n2 n3 n4 P inv cnt : UInt256) : UInt256 :=
  (UInt256.land (UInt256.ofNat 1766847064778384329583297500742918515827483896875618958121606201292619775) ((q4 * n4) + ((x4 * x4) + c)))

theorem sqCol8_eq (s : State) (c q3 q2 q1 q4 z0 z1 z2 x3 x4 n1 n2 n3 n4 P inv cnt : UInt256) (rest : List UInt256) :
    sqCol8Model s c q3 q2 q1 q4 z0 z1 z2 x3 x4 n1 n2 n3 n4 P inv cnt rest =
      {s with pc := UInt256.ofNat 4701, stack := (sqCol8_o0 c q3 q2 q1 q4 z0 z1 z2 x3 x4 n1 n2 n3 n4 P inv cnt) :: q3 :: q2 :: q1 :: q4 :: z0 :: z1 :: z2 :: (sqCol8_o8 c q3 q2 q1 q4 z0 z1 z2 x3 x4 n1 n2 n3 n4 P inv cnt) :: x4 :: n1 :: n2 :: n3 :: n4 :: P :: inv :: cnt :: rest} := by
  simp only [sqCol8Model, sqCol8_o0, sqCol8_o8]

/-! ## sqTail: pc 4701..4712, 10 instructions -/

def sqTailpart0Program : List Instr :=
  [.op (.Swap ⟨8, by decide⟩),
   .op .POP,
   .op .POP,
   .op .POP,
   .op .POP,
   .op .POP,
   .push 1 1,
   .op (.Dup ⟨12, by decide⟩)]

def sqTailpart0Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 : UInt256) (rest : List UInt256) : State :=
  {s with pc := UInt256.ofNat 4710, memory := s.memory, stack := x16 :: (UInt256.ofNat 1) :: x5 :: x6 :: x7 :: x8 :: x0 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: rest}

theorem sqTailpart0_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions sqTailpart0Program {s with pc := UInt256.ofNat 4701, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: rest} =
      some (sqTailpart0Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 rest) := by
  have hc (j : Nat) (hj : j ≤ 30) : rest.length + j < 1024 := by omega
  have hcr : rest.length < 1024 := by omega
  simp [hz, hzn, sqTailpart0Program, sqTailpart0Model, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, ofNat_sub_ofNat, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, hc, hcr]

def sqTailpart1Program : List Instr :=
  [.op .SUB,
   .op (.Swap ⟨11, by decide⟩)]

def sqTailpart1Model (s : State) (x0 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 : UInt256) (rest : List UInt256) : State :=
  let v0 : UInt256 := x0 - (UInt256.ofNat 1)
  {s with pc := UInt256.ofNat 4712, memory := s.memory, stack := x13 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: v0 :: rest}

theorem sqTailpart1_run (s : State) (x0 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions sqTailpart1Program {s with pc := UInt256.ofNat 4710, stack := x0 :: (UInt256.ofNat 1) :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: rest} =
      some (sqTailpart1Model s x0 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 rest) := by
  have hc (j : Nat) (hj : j ≤ 27) : rest.length + j < 1024 := by omega
  have hcr : rest.length < 1024 := by omega
  simp [hz, hzn, sqTailpart1Program, sqTailpart1Model, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, ofNat_sub_ofNat, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, hc, hcr]

def sqTailProgram : List Instr :=
  [.op (.Swap ⟨8, by decide⟩),
   .op .POP,
   .op .POP,
   .op .POP,
   .op .POP,
   .op .POP,
   .push 1 1,
   .op (.Dup ⟨12, by decide⟩),
   .op .SUB,
   .op (.Swap ⟨11, by decide⟩)]

def sqTailModel (s : State) (c q3 q2 q1 q4 z0 z1 z2 z3 x4 n1 n2 n3 n4 P inv cnt : UInt256) (rest : List UInt256) : State :=
  let v0 : UInt256 := cnt - (UInt256.ofNat 1)
  {s with pc := UInt256.ofNat 4712, memory := s.memory, stack := cnt :: z0 :: z1 :: z2 :: z3 :: c :: n1 :: n2 :: n3 :: n4 :: P :: inv :: v0 :: rest}

theorem sqTail_run (s : State) (c q3 q2 q1 q4 z0 z1 z2 z3 x4 n1 n2 n3 n4 P inv cnt : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions sqTailProgram {s with pc := UInt256.ofNat 4701, stack := c :: q3 :: q2 :: q1 :: q4 :: z0 :: z1 :: z2 :: z3 :: x4 :: n1 :: n2 :: n3 :: n4 :: P :: inv :: cnt :: rest} =
      some (sqTailModel s c q3 q2 q1 q4 z0 z1 z2 z3 x4 n1 n2 n3 n4 P inv cnt rest) := by
  let v0 : UInt256 := cnt - (UInt256.ofNat 1)
  have h0 : runInstructions sqTailpart0Program {s with pc := UInt256.ofNat 4701, memory := s.memory, stack := c :: q3 :: q2 :: q1 :: q4 :: z0 :: z1 :: z2 :: z3 :: x4 :: n1 :: n2 :: n3 :: n4 :: P :: inv :: cnt :: rest} = some {s with pc := UInt256.ofNat 4710, memory := s.memory, stack := cnt :: (UInt256.ofNat 1) :: z0 :: z1 :: z2 :: z3 :: c :: n1 :: n2 :: n3 :: n4 :: P :: inv :: cnt :: rest} := by
    simpa only [sqTailpart0Model] using sqTailpart0_run (s) c q3 q2 q1 q4 z0 z1 z2 z3 x4 n1 n2 n3 n4 P inv cnt rest hcap hact
  have h1 : runInstructions sqTailpart1Program {s with pc := UInt256.ofNat 4710, memory := s.memory, stack := cnt :: (UInt256.ofNat 1) :: z0 :: z1 :: z2 :: z3 :: c :: n1 :: n2 :: n3 :: n4 :: P :: inv :: cnt :: rest} = some {s with pc := UInt256.ofNat 4712, memory := s.memory, stack := cnt :: z0 :: z1 :: z2 :: z3 :: c :: n1 :: n2 :: n3 :: n4 :: P :: inv :: v0 :: rest} := by
    simpa only [sqTailpart1Model, v0] using sqTailpart1_run (s) cnt z0 z1 z2 z3 c n1 n2 n3 n4 P inv cnt rest hcap hact
  exact (runInstructions_append_some _ _ _ _ _ h0 h1)

def sqTail_o12 (c q3 q2 q1 q4 z0 z1 z2 z3 x4 n1 n2 n3 n4 P inv cnt : UInt256) : UInt256 :=
  (cnt - (UInt256.ofNat 1))

theorem sqTail_eq (s : State) (c q3 q2 q1 q4 z0 z1 z2 z3 x4 n1 n2 n3 n4 P inv cnt : UInt256) (rest : List UInt256) :
    sqTailModel s c q3 q2 q1 q4 z0 z1 z2 z3 x4 n1 n2 n3 n4 P inv cnt rest =
      {s with pc := UInt256.ofNat 4712, stack := cnt :: z0 :: z1 :: z2 :: z3 :: c :: n1 :: n2 :: n3 :: n4 :: P :: inv :: (sqTail_o12 c q3 q2 q1 q4 z0 z1 z2 z3 x4 n1 n2 n3 n4 P inv cnt) :: rest} := by
  simp only [sqTailModel, sqTail_o12]

end CycleSubmission.R5.ExecSquare
