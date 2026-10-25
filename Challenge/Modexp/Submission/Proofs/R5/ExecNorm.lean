import Challenge.Modexp.Submission.Proofs.Bytecode.WindowNibbleDefs
import Challenge.Modexp.Submission.Proofs.Fast.Exp

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

private theorem hz : ({val := 0} : UInt256) = UInt256.ofNat 0 := rfl
private theorem hzn : ({val := 0} : UInt256).toNat = 0 := rfl

/-! ## norm: pc 5184..5188, 4 instructions -/

def normpart0Program : List Instr :=
  [.op .JUMPDEST,
   .op (.Dup ⟨8, by decide⟩),
   .op (.Dup ⟨5, by decide⟩),
   .op .LT]

def normpart0Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 : UInt256) (rest : List UInt256) : State :=
  let v0 : UInt256 := UInt256.lt x4 x8
  {s with pc := UInt256.ofNat 5188, memory := s.memory, stack := v0 :: x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: rest}

theorem normpart0_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions normpart0Program {s with pc := UInt256.ofNat 5184, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: rest} =
      some (normpart0Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 rest) := by
  have hc (j : Nat) (hj : j ≤ 27) : rest.length + j < 1024 := by omega
  have hcr : rest.length < 1024 := by omega
  simp [hz, hzn, normpart0Program, normpart0Model, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, ofNat_sub_ofNat, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, hc, hcr]

def normProgram : List Instr :=
  [.op .JUMPDEST,
   .op (.Dup ⟨8, by decide⟩),
   .op (.Dup ⟨5, by decide⟩),
   .op .LT]

def normModel (s : State) (a0 a1 a2 a3 a4 n1 n2 n3 n4 P inv cntp : UInt256) (rest : List UInt256) : State :=
  let v0 : UInt256 := UInt256.lt a4 n4
  {s with pc := UInt256.ofNat 5188, memory := s.memory, stack := v0 :: a0 :: a1 :: a2 :: a3 :: a4 :: n1 :: n2 :: n3 :: n4 :: P :: inv :: cntp :: rest}

theorem norm_run (s : State) (a0 a1 a2 a3 a4 n1 n2 n3 n4 P inv cntp : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions normProgram {s with pc := UInt256.ofNat 5184, stack := a0 :: a1 :: a2 :: a3 :: a4 :: n1 :: n2 :: n3 :: n4 :: P :: inv :: cntp :: rest} =
      some (normModel s a0 a1 a2 a3 a4 n1 n2 n3 n4 P inv cntp rest) := by
  let v0 : UInt256 := UInt256.lt a4 n4
  have h0 : runInstructions normpart0Program {s with pc := UInt256.ofNat 5184, memory := s.memory, stack := a0 :: a1 :: a2 :: a3 :: a4 :: n1 :: n2 :: n3 :: n4 :: P :: inv :: cntp :: rest} = some {s with pc := UInt256.ofNat 5188, memory := s.memory, stack := v0 :: a0 :: a1 :: a2 :: a3 :: a4 :: n1 :: n2 :: n3 :: n4 :: P :: inv :: cntp :: rest} := by
    simpa only [normpart0Model, v0] using normpart0_run (s) a0 a1 a2 a3 a4 n1 n2 n3 n4 P inv cntp rest hcap hact
  exact h0

def norm_o0 (a0 a1 a2 a3 a4 n1 n2 n3 n4 P inv cntp : UInt256) : UInt256 :=
  (UInt256.lt a4 n4)

theorem norm_eq (s : State) (a0 a1 a2 a3 a4 n1 n2 n3 n4 P inv cntp : UInt256) (rest : List UInt256) :
    normModel s a0 a1 a2 a3 a4 n1 n2 n3 n4 P inv cntp rest =
      {s with pc := UInt256.ofNat 5188, stack := (norm_o0 a0 a1 a2 a3 a4 n1 n2 n3 n4 P inv cntp) :: a0 :: a1 :: a2 :: a3 :: a4 :: n1 :: n2 :: n3 :: n4 :: P :: inv :: cntp :: rest} := by
  simp only [normModel, norm_o0]

/-! ## blk5192: pc 5192..5261, 59 instructions -/

def blk5192part0Program : List Instr :=
  [.push 1 160,
   .op .MLOAD,
   .op (.Dup ⟨1, by decide⟩),
   .op .SUB,
   .op (.Dup ⟨0, by decide⟩),
   .push 1 255,
   .op .SHR,
   .op (.Swap ⟨0, by decide⟩)]

def blk5192part0Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 : UInt256) (rest : List UInt256) : State :=
  let v0 : UInt256 := MachineState.readWord s.memory 160
  let v1 : UInt256 := x0 - v0
  let v2 : UInt256 := UInt256.shiftRight v1 (UInt256.ofNat 255)
  {s with pc := UInt256.ofNat 5202, memory := s.memory, stack := v1 :: v2 :: x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: rest}

theorem blk5192part0_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions blk5192part0Program {s with pc := UInt256.ofNat 5192, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: rest} =
      some (blk5192part0Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 rest) := by
  have hc (j : Nat) (hj : j ≤ 28) : rest.length + j < 1024 := by omega
  have hcr : rest.length < 1024 := by omega
  have ha160 : (160 : UInt256).toNat = 160 := rfl
  have hf160 := activeWords_fix s 160 32 (by decide) (by norm_num) hact
  simp [hz, hzn, blk5192part0Program, blk5192part0Model, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, ofNat_sub_ofNat, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, hc, hcr, ha160, hf160]

def blk5192part1Program : List Instr :=
  [.push 1 224,
   .op .MLOAD,
   .op .AND,
   .op (.Swap ⟨0, by decide⟩),
   .op (.Dup ⟨3, by decide⟩),
   .op .SUB,
   .op (.Dup ⟨7, by decide⟩),
   .op (.Swap ⟨0, by decide⟩)]

def blk5192part1Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 : UInt256) (rest : List UInt256) : State :=
  let v0 : UInt256 := MachineState.readWord s.memory 224
  let v1 : UInt256 := UInt256.land v0 x0
  let v2 : UInt256 := x3 - x1
  {s with pc := UInt256.ofNat 5211, memory := s.memory, stack := v2 :: x7 :: v1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: rest}

theorem blk5192part1_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions blk5192part1Program {s with pc := UInt256.ofNat 5202, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: rest} =
      some (blk5192part1Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 rest) := by
  have hc (j : Nat) (hj : j ≤ 28) : rest.length + j < 1024 := by omega
  have hcr : rest.length < 1024 := by omega
  have ha224 : (224 : UInt256).toNat = 224 := rfl
  have hf224 := activeWords_fix s 224 32 (by decide) (by norm_num) hact
  simp [hz, hzn, blk5192part1Program, blk5192part1Model, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, ofNat_sub_ofNat, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, hc, hcr, ha224, hf224]

def blk5192part2Program : List Instr :=
  [.op .SUB,
   .op (.Dup ⟨0, by decide⟩),
   .push 1 255,
   .op .SHR,
   .op (.Swap ⟨0, by decide⟩),
   .push 1 224,
   .op .MLOAD,
   .op .AND]

def blk5192part2Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 : UInt256) (rest : List UInt256) : State :=
  let v0 : UInt256 := x0 - x1
  let v1 : UInt256 := UInt256.shiftRight v0 (UInt256.ofNat 255)
  let v2 : UInt256 := MachineState.readWord s.memory 224
  let v3 : UInt256 := UInt256.land v2 v0
  {s with pc := UInt256.ofNat 5221, memory := s.memory, stack := v3 :: v1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: rest}

theorem blk5192part2_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions blk5192part2Program {s with pc := UInt256.ofNat 5211, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: rest} =
      some (blk5192part2Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 rest) := by
  have hc (j : Nat) (hj : j ≤ 29) : rest.length + j < 1024 := by omega
  have hcr : rest.length < 1024 := by omega
  have ha224 : (224 : UInt256).toNat = 224 := rfl
  have hf224 := activeWords_fix s 224 32 (by decide) (by norm_num) hact
  simp [hz, hzn, blk5192part2Program, blk5192part2Model, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, ofNat_sub_ofNat, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, hc, hcr, ha224, hf224]

def blk5192part3Program : List Instr :=
  [.op (.Swap ⟨0, by decide⟩),
   .op (.Dup ⟨5, by decide⟩),
   .op .SUB,
   .op (.Dup ⟨9, by decide⟩),
   .op (.Swap ⟨0, by decide⟩),
   .op .SUB,
   .op (.Dup ⟨0, by decide⟩)]

def blk5192part3Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 : UInt256) (rest : List UInt256) : State :=
  let v0 : UInt256 := x5 - x1
  let v1 : UInt256 := v0 - x9
  {s with pc := UInt256.ofNat 5228, memory := s.memory, stack := v1 :: v1 :: x0 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: rest}

theorem blk5192part3_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions blk5192part3Program {s with pc := UInt256.ofNat 5221, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: rest} =
      some (blk5192part3Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 rest) := by
  have hc (j : Nat) (hj : j ≤ 29) : rest.length + j < 1024 := by omega
  have hcr : rest.length < 1024 := by omega
  simp [hz, hzn, blk5192part3Program, blk5192part3Model, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, ofNat_sub_ofNat, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, hc, hcr]

def blk5192part4Program : List Instr :=
  [.push 1 255,
   .op .SHR,
   .op (.Swap ⟨0, by decide⟩),
   .push 1 224,
   .op .MLOAD,
   .op .AND,
   .op (.Swap ⟨0, by decide⟩),
   .op (.Dup ⟨7, by decide⟩)]

def blk5192part4Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 : UInt256) (rest : List UInt256) : State :=
  let v0 : UInt256 := UInt256.shiftRight x0 (UInt256.ofNat 255)
  let v1 : UInt256 := MachineState.readWord s.memory 224
  let v2 : UInt256 := UInt256.land v1 x1
  {s with pc := UInt256.ofNat 5238, memory := s.memory, stack := x7 :: v0 :: v2 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: rest}

theorem blk5192part4_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions blk5192part4Program {s with pc := UInt256.ofNat 5228, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: rest} =
      some (blk5192part4Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 rest) := by
  have hc (j : Nat) (hj : j ≤ 30) : rest.length + j < 1024 := by omega
  have hcr : rest.length < 1024 := by omega
  have ha224 : (224 : UInt256).toNat = 224 := rfl
  have hf224 := activeWords_fix s 224 32 (by decide) (by norm_num) hact
  simp [hz, hzn, blk5192part4Program, blk5192part4Model, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, ofNat_sub_ofNat, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, hc, hcr, ha224, hf224]

def blk5192part5Program : List Instr :=
  [.op .SUB,
   .op (.Dup ⟨11, by decide⟩),
   .op (.Swap ⟨0, by decide⟩),
   .op .SUB,
   .op (.Dup ⟨0, by decide⟩),
   .push 1 255,
   .op .SHR,
   .op (.Swap ⟨0, by decide⟩)]

def blk5192part5Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 : UInt256) (rest : List UInt256) : State :=
  let v0 : UInt256 := x0 - x1
  let v1 : UInt256 := v0 - x12
  let v2 : UInt256 := UInt256.shiftRight v1 (UInt256.ofNat 255)
  {s with pc := UInt256.ofNat 5247, memory := s.memory, stack := v1 :: v2 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: rest}

theorem blk5192part5_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions blk5192part5Program {s with pc := UInt256.ofNat 5238, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: rest} =
      some (blk5192part5Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 rest) := by
  have hc (j : Nat) (hj : j ≤ 31) : rest.length + j < 1024 := by omega
  have hcr : rest.length < 1024 := by omega
  simp [hz, hzn, blk5192part5Program, blk5192part5Model, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, ofNat_sub_ofNat, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, hc, hcr]

def blk5192part6Program : List Instr :=
  [.push 1 224,
   .op .MLOAD,
   .op .AND,
   .op (.Swap ⟨0, by decide⟩),
   .op (.Dup ⟨9, by decide⟩),
   .op .SUB,
   .op (.Dup ⟨13, by decide⟩),
   .op (.Swap ⟨0, by decide⟩)]

def blk5192part6Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 : UInt256) (rest : List UInt256) : State :=
  let v0 : UInt256 := MachineState.readWord s.memory 224
  let v1 : UInt256 := UInt256.land v0 x0
  let v2 : UInt256 := x9 - x1
  {s with pc := UInt256.ofNat 5256, memory := s.memory, stack := v2 :: x13 :: v1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: rest}

theorem blk5192part6_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions blk5192part6Program {s with pc := UInt256.ofNat 5247, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: rest} =
      some (blk5192part6Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 rest) := by
  have hc (j : Nat) (hj : j ≤ 31) : rest.length + j < 1024 := by omega
  have hcr : rest.length < 1024 := by omega
  have ha224 : (224 : UInt256).toNat = 224 := rfl
  have hf224 := activeWords_fix s 224 32 (by decide) (by norm_num) hact
  simp [hz, hzn, blk5192part6Program, blk5192part6Model, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, ofNat_sub_ofNat, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, hc, hcr, ha224, hf224]

def blk5192part7Program : List Instr :=
  [.op .SUB,
   .op (.Dup ⟨0, by decide⟩),
   .push 1 255,
   .op .SHR]

def blk5192part7Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 : UInt256) (rest : List UInt256) : State :=
  let v0 : UInt256 := x0 - x1
  let v1 : UInt256 := UInt256.shiftRight v0 (UInt256.ofNat 255)
  {s with pc := UInt256.ofNat 5261, memory := s.memory, stack := v1 :: v0 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: rest}

theorem blk5192part7_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions blk5192part7Program {s with pc := UInt256.ofNat 5256, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: rest} =
      some (blk5192part7Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 rest) := by
  have hc (j : Nat) (hj : j ≤ 32) : rest.length + j < 1024 := by omega
  have hcr : rest.length < 1024 := by omega
  simp [hz, hzn, blk5192part7Program, blk5192part7Model, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, ofNat_sub_ofNat, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, hc, hcr]

def blk5192Program : List Instr :=
  [.push 1 160,
   .op .MLOAD,
   .op (.Dup ⟨1, by decide⟩),
   .op .SUB,
   .op (.Dup ⟨0, by decide⟩),
   .push 1 255,
   .op .SHR,
   .op (.Swap ⟨0, by decide⟩),
   .push 1 224,
   .op .MLOAD,
   .op .AND,
   .op (.Swap ⟨0, by decide⟩),
   .op (.Dup ⟨3, by decide⟩),
   .op .SUB,
   .op (.Dup ⟨7, by decide⟩),
   .op (.Swap ⟨0, by decide⟩),
   .op .SUB,
   .op (.Dup ⟨0, by decide⟩),
   .push 1 255,
   .op .SHR,
   .op (.Swap ⟨0, by decide⟩),
   .push 1 224,
   .op .MLOAD,
   .op .AND,
   .op (.Swap ⟨0, by decide⟩),
   .op (.Dup ⟨5, by decide⟩),
   .op .SUB,
   .op (.Dup ⟨9, by decide⟩),
   .op (.Swap ⟨0, by decide⟩),
   .op .SUB,
   .op (.Dup ⟨0, by decide⟩),
   .push 1 255,
   .op .SHR,
   .op (.Swap ⟨0, by decide⟩),
   .push 1 224,
   .op .MLOAD,
   .op .AND,
   .op (.Swap ⟨0, by decide⟩),
   .op (.Dup ⟨7, by decide⟩),
   .op .SUB,
   .op (.Dup ⟨11, by decide⟩),
   .op (.Swap ⟨0, by decide⟩),
   .op .SUB,
   .op (.Dup ⟨0, by decide⟩),
   .push 1 255,
   .op .SHR,
   .op (.Swap ⟨0, by decide⟩),
   .push 1 224,
   .op .MLOAD,
   .op .AND,
   .op (.Swap ⟨0, by decide⟩),
   .op (.Dup ⟨9, by decide⟩),
   .op .SUB,
   .op (.Dup ⟨13, by decide⟩),
   .op (.Swap ⟨0, by decide⟩),
   .op .SUB,
   .op (.Dup ⟨0, by decide⟩),
   .push 1 255,
   .op .SHR]

def blk5192Model (s : State) (a0 a1 a2 a3 a4 n1 n2 n3 n4 P inv cntp : UInt256) (rest : List UInt256) : State :=
  let v0 : UInt256 := MachineState.readWord s.memory 160
  let v1 : UInt256 := a0 - v0
  let v2 : UInt256 := UInt256.shiftRight v1 (UInt256.ofNat 255)
  let v3 : UInt256 := MachineState.readWord s.memory 224
  let v4 : UInt256 := UInt256.land v3 v1
  let v5 : UInt256 := a1 - v2
  let v6 : UInt256 := v5 - n1
  let v7 : UInt256 := UInt256.shiftRight v6 (UInt256.ofNat 255)
  let v8 : UInt256 := MachineState.readWord s.memory 224
  let v9 : UInt256 := UInt256.land v8 v6
  let v10 : UInt256 := a2 - v7
  let v11 : UInt256 := v10 - n2
  let v12 : UInt256 := UInt256.shiftRight v11 (UInt256.ofNat 255)
  let v13 : UInt256 := MachineState.readWord s.memory 224
  let v14 : UInt256 := UInt256.land v13 v11
  let v15 : UInt256 := a3 - v12
  let v16 : UInt256 := v15 - n3
  let v17 : UInt256 := UInt256.shiftRight v16 (UInt256.ofNat 255)
  let v18 : UInt256 := MachineState.readWord s.memory 224
  let v19 : UInt256 := UInt256.land v18 v16
  let v20 : UInt256 := a4 - v17
  let v21 : UInt256 := v20 - n4
  let v22 : UInt256 := UInt256.shiftRight v21 (UInt256.ofNat 255)
  {s with pc := UInt256.ofNat 5261, memory := s.memory, stack := v22 :: v21 :: v19 :: v14 :: v9 :: v4 :: a0 :: a1 :: a2 :: a3 :: a4 :: n1 :: n2 :: n3 :: n4 :: P :: inv :: cntp :: rest}

theorem blk5192_run (s : State) (a0 a1 a2 a3 a4 n1 n2 n3 n4 P inv cntp : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions blk5192Program {s with pc := UInt256.ofNat 5192, stack := a0 :: a1 :: a2 :: a3 :: a4 :: n1 :: n2 :: n3 :: n4 :: P :: inv :: cntp :: rest} =
      some (blk5192Model s a0 a1 a2 a3 a4 n1 n2 n3 n4 P inv cntp rest) := by
  let v0 : UInt256 := MachineState.readWord s.memory 160
  let v1 : UInt256 := a0 - v0
  let v2 : UInt256 := UInt256.shiftRight v1 (UInt256.ofNat 255)
  let v3 : UInt256 := MachineState.readWord s.memory 224
  let v4 : UInt256 := UInt256.land v3 v1
  let v5 : UInt256 := a1 - v2
  let v6 : UInt256 := v5 - n1
  let v7 : UInt256 := UInt256.shiftRight v6 (UInt256.ofNat 255)
  let v8 : UInt256 := MachineState.readWord s.memory 224
  let v9 : UInt256 := UInt256.land v8 v6
  let v10 : UInt256 := a2 - v7
  let v11 : UInt256 := v10 - n2
  let v12 : UInt256 := UInt256.shiftRight v11 (UInt256.ofNat 255)
  let v13 : UInt256 := MachineState.readWord s.memory 224
  let v14 : UInt256 := UInt256.land v13 v11
  let v15 : UInt256 := a3 - v12
  let v16 : UInt256 := v15 - n3
  let v17 : UInt256 := UInt256.shiftRight v16 (UInt256.ofNat 255)
  let v18 : UInt256 := MachineState.readWord s.memory 224
  let v19 : UInt256 := UInt256.land v18 v16
  let v20 : UInt256 := a4 - v17
  let v21 : UInt256 := v20 - n4
  let v22 : UInt256 := UInt256.shiftRight v21 (UInt256.ofNat 255)
  have h0 : runInstructions blk5192part0Program {s with pc := UInt256.ofNat 5192, memory := s.memory, stack := a0 :: a1 :: a2 :: a3 :: a4 :: n1 :: n2 :: n3 :: n4 :: P :: inv :: cntp :: rest} = some {s with pc := UInt256.ofNat 5202, memory := s.memory, stack := v1 :: v2 :: a0 :: a1 :: a2 :: a3 :: a4 :: n1 :: n2 :: n3 :: n4 :: P :: inv :: cntp :: rest} := by
    simpa only [blk5192part0Model, v0, v1, v2] using blk5192part0_run (s) a0 a1 a2 a3 a4 n1 n2 n3 n4 P inv cntp rest hcap hact
  have h1 : runInstructions blk5192part1Program {s with pc := UInt256.ofNat 5202, memory := s.memory, stack := v1 :: v2 :: a0 :: a1 :: a2 :: a3 :: a4 :: n1 :: n2 :: n3 :: n4 :: P :: inv :: cntp :: rest} = some {s with pc := UInt256.ofNat 5211, memory := s.memory, stack := v5 :: n1 :: v4 :: a0 :: a1 :: a2 :: a3 :: a4 :: n1 :: n2 :: n3 :: n4 :: P :: inv :: cntp :: rest} := by
    simpa only [blk5192part1Model, v3, v4, v5] using blk5192part1_run (s) v1 v2 a0 a1 a2 a3 a4 n1 n2 n3 n4 P inv cntp rest hcap hact
  have h2 : runInstructions blk5192part2Program {s with pc := UInt256.ofNat 5211, memory := s.memory, stack := v5 :: n1 :: v4 :: a0 :: a1 :: a2 :: a3 :: a4 :: n1 :: n2 :: n3 :: n4 :: P :: inv :: cntp :: rest} = some {s with pc := UInt256.ofNat 5221, memory := s.memory, stack := v9 :: v7 :: v4 :: a0 :: a1 :: a2 :: a3 :: a4 :: n1 :: n2 :: n3 :: n4 :: P :: inv :: cntp :: rest} := by
    simpa only [blk5192part2Model, v6, v7, v8, v9] using blk5192part2_run (s) v5 n1 v4 a0 a1 a2 a3 a4 n1 n2 n3 n4 P inv cntp rest hcap hact
  have h3 : runInstructions blk5192part3Program {s with pc := UInt256.ofNat 5221, memory := s.memory, stack := v9 :: v7 :: v4 :: a0 :: a1 :: a2 :: a3 :: a4 :: n1 :: n2 :: n3 :: n4 :: P :: inv :: cntp :: rest} = some {s with pc := UInt256.ofNat 5228, memory := s.memory, stack := v11 :: v11 :: v9 :: v4 :: a0 :: a1 :: a2 :: a3 :: a4 :: n1 :: n2 :: n3 :: n4 :: P :: inv :: cntp :: rest} := by
    simpa only [blk5192part3Model, v10, v11] using blk5192part3_run (s) v9 v7 v4 a0 a1 a2 a3 a4 n1 n2 n3 n4 P inv cntp rest hcap hact
  have h4 : runInstructions blk5192part4Program {s with pc := UInt256.ofNat 5228, memory := s.memory, stack := v11 :: v11 :: v9 :: v4 :: a0 :: a1 :: a2 :: a3 :: a4 :: n1 :: n2 :: n3 :: n4 :: P :: inv :: cntp :: rest} = some {s with pc := UInt256.ofNat 5238, memory := s.memory, stack := a3 :: v12 :: v14 :: v9 :: v4 :: a0 :: a1 :: a2 :: a3 :: a4 :: n1 :: n2 :: n3 :: n4 :: P :: inv :: cntp :: rest} := by
    simpa only [blk5192part4Model, v12, v13, v14] using blk5192part4_run (s) v11 v11 v9 v4 a0 a1 a2 a3 a4 n1 n2 n3 n4 P inv cntp rest hcap hact
  have h5 : runInstructions blk5192part5Program {s with pc := UInt256.ofNat 5238, memory := s.memory, stack := a3 :: v12 :: v14 :: v9 :: v4 :: a0 :: a1 :: a2 :: a3 :: a4 :: n1 :: n2 :: n3 :: n4 :: P :: inv :: cntp :: rest} = some {s with pc := UInt256.ofNat 5247, memory := s.memory, stack := v16 :: v17 :: v14 :: v9 :: v4 :: a0 :: a1 :: a2 :: a3 :: a4 :: n1 :: n2 :: n3 :: n4 :: P :: inv :: cntp :: rest} := by
    simpa only [blk5192part5Model, v15, v16, v17] using blk5192part5_run (s) a3 v12 v14 v9 v4 a0 a1 a2 a3 a4 n1 n2 n3 n4 P inv cntp rest hcap hact
  have h6 : runInstructions blk5192part6Program {s with pc := UInt256.ofNat 5247, memory := s.memory, stack := v16 :: v17 :: v14 :: v9 :: v4 :: a0 :: a1 :: a2 :: a3 :: a4 :: n1 :: n2 :: n3 :: n4 :: P :: inv :: cntp :: rest} = some {s with pc := UInt256.ofNat 5256, memory := s.memory, stack := v20 :: n4 :: v19 :: v14 :: v9 :: v4 :: a0 :: a1 :: a2 :: a3 :: a4 :: n1 :: n2 :: n3 :: n4 :: P :: inv :: cntp :: rest} := by
    simpa only [blk5192part6Model, v18, v19, v20] using blk5192part6_run (s) v16 v17 v14 v9 v4 a0 a1 a2 a3 a4 n1 n2 n3 n4 P inv cntp rest hcap hact
  have h7 : runInstructions blk5192part7Program {s with pc := UInt256.ofNat 5256, memory := s.memory, stack := v20 :: n4 :: v19 :: v14 :: v9 :: v4 :: a0 :: a1 :: a2 :: a3 :: a4 :: n1 :: n2 :: n3 :: n4 :: P :: inv :: cntp :: rest} = some {s with pc := UInt256.ofNat 5261, memory := s.memory, stack := v22 :: v21 :: v19 :: v14 :: v9 :: v4 :: a0 :: a1 :: a2 :: a3 :: a4 :: n1 :: n2 :: n3 :: n4 :: P :: inv :: cntp :: rest} := by
    simpa only [blk5192part7Model, v21, v22] using blk5192part7_run (s) v20 n4 v19 v14 v9 v4 a0 a1 a2 a3 a4 n1 n2 n3 n4 P inv cntp rest hcap hact
  exact (runInstructions_append_some _ _ _ _ _ h0 (runInstructions_append_some _ _ _ _ _ h1 (runInstructions_append_some _ _ _ _ _ h2 (runInstructions_append_some _ _ _ _ _ h3 (runInstructions_append_some _ _ _ _ _ h4 (runInstructions_append_some _ _ _ _ _ h5 (runInstructions_append_some _ _ _ _ _ h6 h7)))))))

def blk5192_o0 (a0 a1 a2 a3 a4 n1 n2 n3 n4 P inv cntp n0 M : UInt256) : UInt256 :=
  (UInt256.shiftRight ((a4 - (UInt256.shiftRight ((a3 - (UInt256.shiftRight ((a2 - (UInt256.shiftRight ((a1 - (UInt256.shiftRight (a0 - n0) (UInt256.ofNat 255))) - n1) (UInt256.ofNat 255))) - n2) (UInt256.ofNat 255))) - n3) (UInt256.ofNat 255))) - n4) (UInt256.ofNat 255))

def blk5192_o1 (a0 a1 a2 a3 a4 n1 n2 n3 n4 P inv cntp n0 M : UInt256) : UInt256 :=
  ((a4 - (UInt256.shiftRight ((a3 - (UInt256.shiftRight ((a2 - (UInt256.shiftRight ((a1 - (UInt256.shiftRight (a0 - n0) (UInt256.ofNat 255))) - n1) (UInt256.ofNat 255))) - n2) (UInt256.ofNat 255))) - n3) (UInt256.ofNat 255))) - n4)

def blk5192_o2 (a0 a1 a2 a3 a4 n1 n2 n3 n4 P inv cntp n0 M : UInt256) : UInt256 :=
  (UInt256.land M ((a3 - (UInt256.shiftRight ((a2 - (UInt256.shiftRight ((a1 - (UInt256.shiftRight (a0 - n0) (UInt256.ofNat 255))) - n1) (UInt256.ofNat 255))) - n2) (UInt256.ofNat 255))) - n3))

def blk5192_o3 (a0 a1 a2 a3 a4 n1 n2 n3 n4 P inv cntp n0 M : UInt256) : UInt256 :=
  (UInt256.land M ((a2 - (UInt256.shiftRight ((a1 - (UInt256.shiftRight (a0 - n0) (UInt256.ofNat 255))) - n1) (UInt256.ofNat 255))) - n2))

def blk5192_o4 (a0 a1 a2 a3 a4 n1 n2 n3 n4 P inv cntp n0 M : UInt256) : UInt256 :=
  (UInt256.land M ((a1 - (UInt256.shiftRight (a0 - n0) (UInt256.ofNat 255))) - n1))

def blk5192_o5 (a0 a1 a2 a3 a4 n1 n2 n3 n4 P inv cntp n0 M : UInt256) : UInt256 :=
  (UInt256.land M (a0 - n0))

theorem blk5192_eq (s : State) (a0 a1 a2 a3 a4 n1 n2 n3 n4 P inv cntp n0 M : UInt256) (rest : List UInt256)
    (h_n0 : MachineState.readWord s.memory 160 = n0)
    (h_M : MachineState.readWord s.memory 224 = M) :
    blk5192Model s a0 a1 a2 a3 a4 n1 n2 n3 n4 P inv cntp rest =
      {s with pc := UInt256.ofNat 5261, stack := (blk5192_o0 a0 a1 a2 a3 a4 n1 n2 n3 n4 P inv cntp n0 M) :: (blk5192_o1 a0 a1 a2 a3 a4 n1 n2 n3 n4 P inv cntp n0 M) :: (blk5192_o2 a0 a1 a2 a3 a4 n1 n2 n3 n4 P inv cntp n0 M) :: (blk5192_o3 a0 a1 a2 a3 a4 n1 n2 n3 n4 P inv cntp n0 M) :: (blk5192_o4 a0 a1 a2 a3 a4 n1 n2 n3 n4 P inv cntp n0 M) :: (blk5192_o5 a0 a1 a2 a3 a4 n1 n2 n3 n4 P inv cntp n0 M) :: a0 :: a1 :: a2 :: a3 :: a4 :: n1 :: n2 :: n3 :: n4 :: P :: inv :: cntp :: rest} := by
  simp only [blk5192Model, blk5192_o0, blk5192_o1, blk5192_o2, blk5192_o3, blk5192_o4, blk5192_o5, h_n0, h_M]

/-! ## blk5265: pc 5265..5275, 10 instructions -/

def blk5265part0Program : List Instr :=
  [.op (.Swap ⟨8, by decide⟩),
   .op .POP,
   .op (.Swap ⟨6, by decide⟩),
   .op .POP,
   .op (.Swap ⟨4, by decide⟩),
   .op .POP,
   .op (.Swap ⟨2, by decide⟩),
   .op .POP]

def blk5265part0Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 : UInt256) (rest : List UInt256) : State :=
  {s with pc := UInt256.ofNat 5273, memory := s.memory, stack := x4 :: x5 :: x3 :: x2 :: x1 :: x0 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: rest}

theorem blk5265part0_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions blk5265part0Program {s with pc := UInt256.ofNat 5265, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: rest} =
      some (blk5265part0Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 rest) := by
  have hc (j : Nat) (hj : j ≤ 30) : rest.length + j < 1024 := by omega
  have hcr : rest.length < 1024 := by omega
  simp [hz, hzn, blk5265part0Program, blk5265part0Model, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, ofNat_sub_ofNat, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, hc, hcr]

def blk5265part1Program : List Instr :=
  [.op (.Swap ⟨0, by decide⟩),
   .op .POP]

def blk5265part1Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 : UInt256) (rest : List UInt256) : State :=
  {s with pc := UInt256.ofNat 5275, memory := s.memory, stack := x0 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: rest}

theorem blk5265part1_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions blk5265part1Program {s with pc := UInt256.ofNat 5273, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: rest} =
      some (blk5265part1Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 rest) := by
  have hc (j : Nat) (hj : j ≤ 26) : rest.length + j < 1024 := by omega
  have hcr : rest.length < 1024 := by omega
  simp [hz, hzn, blk5265part1Program, blk5265part1Model, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, ofNat_sub_ofNat, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, hc, hcr]

def blk5265Program : List Instr :=
  [.op (.Swap ⟨8, by decide⟩),
   .op .POP,
   .op (.Swap ⟨6, by decide⟩),
   .op .POP,
   .op (.Swap ⟨4, by decide⟩),
   .op .POP,
   .op (.Swap ⟨2, by decide⟩),
   .op .POP,
   .op (.Swap ⟨0, by decide⟩),
   .op .POP]

def blk5265Model (s : State) (d4 d3 d2 d1 d0 a0 a1 a2 a3 a4 n1 n2 n3 n4 P inv cntp : UInt256) (rest : List UInt256) : State :=
  {s with pc := UInt256.ofNat 5275, memory := s.memory, stack := d0 :: d1 :: d2 :: d3 :: d4 :: n1 :: n2 :: n3 :: n4 :: P :: inv :: cntp :: rest}

theorem blk5265_run (s : State) (d4 d3 d2 d1 d0 a0 a1 a2 a3 a4 n1 n2 n3 n4 P inv cntp : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions blk5265Program {s with pc := UInt256.ofNat 5265, stack := d4 :: d3 :: d2 :: d1 :: d0 :: a0 :: a1 :: a2 :: a3 :: a4 :: n1 :: n2 :: n3 :: n4 :: P :: inv :: cntp :: rest} =
      some (blk5265Model s d4 d3 d2 d1 d0 a0 a1 a2 a3 a4 n1 n2 n3 n4 P inv cntp rest) := by
  have h0 : runInstructions blk5265part0Program {s with pc := UInt256.ofNat 5265, memory := s.memory, stack := d4 :: d3 :: d2 :: d1 :: d0 :: a0 :: a1 :: a2 :: a3 :: a4 :: n1 :: n2 :: n3 :: n4 :: P :: inv :: cntp :: rest} = some {s with pc := UInt256.ofNat 5273, memory := s.memory, stack := d0 :: a0 :: d1 :: d2 :: d3 :: d4 :: n1 :: n2 :: n3 :: n4 :: P :: inv :: cntp :: rest} := by
    simpa only [blk5265part0Model] using blk5265part0_run (s) d4 d3 d2 d1 d0 a0 a1 a2 a3 a4 n1 n2 n3 n4 P inv cntp rest hcap hact
  have h1 : runInstructions blk5265part1Program {s with pc := UInt256.ofNat 5273, memory := s.memory, stack := d0 :: a0 :: d1 :: d2 :: d3 :: d4 :: n1 :: n2 :: n3 :: n4 :: P :: inv :: cntp :: rest} = some {s with pc := UInt256.ofNat 5275, memory := s.memory, stack := d0 :: d1 :: d2 :: d3 :: d4 :: n1 :: n2 :: n3 :: n4 :: P :: inv :: cntp :: rest} := by
    simpa only [blk5265part1Model] using blk5265part1_run (s) d0 a0 d1 d2 d3 d4 n1 n2 n3 n4 P inv cntp rest hcap hact
  exact (runInstructions_append_some _ _ _ _ _ h0 h1)

theorem blk5265_eq (s : State) (d4 d3 d2 d1 d0 a0 a1 a2 a3 a4 n1 n2 n3 n4 P inv cntp : UInt256) (rest : List UInt256) :
    blk5265Model s d4 d3 d2 d1 d0 a0 a1 a2 a3 a4 n1 n2 n3 n4 P inv cntp rest =
      {s with pc := UInt256.ofNat 5275, stack := d0 :: d1 :: d2 :: d3 :: d4 :: n1 :: n2 :: n3 :: n4 :: P :: inv :: cntp :: rest} := by
  simp only [blk5265Model]

/-! ## neg: pc 5279..5285, 6 instructions -/

def negpart0Program : List Instr :=
  [.op .JUMPDEST,
   .op .POP,
   .op .POP,
   .op .POP,
   .op .POP,
   .op .POP]

def negpart0Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 : UInt256) (rest : List UInt256) : State :=
  {s with pc := UInt256.ofNat 5285, memory := s.memory, stack := x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: rest}

theorem negpart0_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions negpart0Program {s with pc := UInt256.ofNat 5279, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: rest} =
      some (negpart0Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 rest) := by
  have hc (j : Nat) (hj : j ≤ 30) : rest.length + j < 1024 := by omega
  have hcr : rest.length < 1024 := by omega
  simp [hz, hzn, negpart0Program, negpart0Model, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, ofNat_sub_ofNat, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, hc, hcr]

def negProgram : List Instr :=
  [.op .JUMPDEST,
   .op .POP,
   .op .POP,
   .op .POP,
   .op .POP,
   .op .POP]

def negModel (s : State) (d4 d3 d2 d1 d0 a0 a1 a2 a3 a4 n1 n2 n3 n4 P inv cntp : UInt256) (rest : List UInt256) : State :=
  {s with pc := UInt256.ofNat 5285, memory := s.memory, stack := a0 :: a1 :: a2 :: a3 :: a4 :: n1 :: n2 :: n3 :: n4 :: P :: inv :: cntp :: rest}

theorem neg_run (s : State) (d4 d3 d2 d1 d0 a0 a1 a2 a3 a4 n1 n2 n3 n4 P inv cntp : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions negProgram {s with pc := UInt256.ofNat 5279, stack := d4 :: d3 :: d2 :: d1 :: d0 :: a0 :: a1 :: a2 :: a3 :: a4 :: n1 :: n2 :: n3 :: n4 :: P :: inv :: cntp :: rest} =
      some (negModel s d4 d3 d2 d1 d0 a0 a1 a2 a3 a4 n1 n2 n3 n4 P inv cntp rest) := by
  have h0 : runInstructions negpart0Program {s with pc := UInt256.ofNat 5279, memory := s.memory, stack := d4 :: d3 :: d2 :: d1 :: d0 :: a0 :: a1 :: a2 :: a3 :: a4 :: n1 :: n2 :: n3 :: n4 :: P :: inv :: cntp :: rest} = some {s with pc := UInt256.ofNat 5285, memory := s.memory, stack := a0 :: a1 :: a2 :: a3 :: a4 :: n1 :: n2 :: n3 :: n4 :: P :: inv :: cntp :: rest} := by
    simpa only [negpart0Model] using negpart0_run (s) d4 d3 d2 d1 d0 a0 a1 a2 a3 a4 n1 n2 n3 n4 P inv cntp rest hcap hact
  exact h0

theorem neg_eq (s : State) (d4 d3 d2 d1 d0 a0 a1 a2 a3 a4 n1 n2 n3 n4 P inv cntp : UInt256) (rest : List UInt256) :
    negModel s d4 d3 d2 d1 d0 a0 a1 a2 a3 a4 n1 n2 n3 n4 P inv cntp rest =
      {s with pc := UInt256.ofNat 5285, stack := a0 :: a1 :: a2 :: a3 :: a4 :: n1 :: n2 :: n3 :: n4 :: P :: inv :: cntp :: rest} := by
  simp only [negModel]

/-! ## done: pc 5285..5330, 35 instructions -/

def donepart0Program : List Instr :=
  [.op .JUMPDEST,
   .op (.Dup ⟨1, by decide⟩),
   .push 1 240,
   .op .SHL,
   .op (.Dup ⟨1, by decide⟩),
   .op .OR,
   .push 1 96,
   .op .MSTORE]

def donepart0Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 : UInt256) (rest : List UInt256) : State :=
  let v0 : UInt256 := UInt256.shiftLeft x1 (UInt256.ofNat 240)
  let v1 : UInt256 := UInt256.lor x0 v0
  let v2 : ByteArray := MachineState.writeBytes s.memory (Data.Bytes.natToBytesPadded v1.toNat 32) 96
  {s with pc := UInt256.ofNat 5295, memory := v2, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: rest}

theorem donepart0_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions donepart0Program {s with pc := UInt256.ofNat 5285, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: rest} =
      some (donepart0Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 rest) := by
  have hc (j : Nat) (hj : j ≤ 27) : rest.length + j < 1024 := by omega
  have hcr : rest.length < 1024 := by omega
  have ha96 : (96 : UInt256).toNat = 96 := rfl
  have hf96 := activeWords_fix s 96 32 (by decide) (by norm_num) hact
  simp [hz, hzn, donepart0Program, donepart0Model, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, ofNat_sub_ofNat, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, hc, hcr, ha96, hf96]

def donepart1Program : List Instr :=
  [.op (.Dup ⟨2, by decide⟩),
   .push 1 224,
   .op .SHL,
   .op (.Dup ⟨2, by decide⟩),
   .push 1 16,
   .op .SHR,
   .op .OR]

def donepart1Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 : UInt256) (rest : List UInt256) : State :=
  let v0 : UInt256 := UInt256.shiftLeft x2 (UInt256.ofNat 224)
  let v1 : UInt256 := UInt256.shiftRight x1 (UInt256.ofNat 16)
  let v2 : UInt256 := UInt256.lor v1 v0
  {s with pc := UInt256.ofNat 5304, memory := s.memory, stack := v2 :: x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: rest}

theorem donepart1_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions donepart1Program {s with pc := UInt256.ofNat 5295, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: rest} =
      some (donepart1Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 rest) := by
  have hc (j : Nat) (hj : j ≤ 28) : rest.length + j < 1024 := by omega
  have hcr : rest.length < 1024 := by omega
  simp [hz, hzn, donepart1Program, donepart1Model, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, ofNat_sub_ofNat, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, hc, hcr]

def donepart2Program : List Instr :=
  [.push 1 64,
   .op .MSTORE,
   .op (.Dup ⟨3, by decide⟩),
   .push 1 208,
   .op .SHL,
   .op (.Dup ⟨3, by decide⟩),
   .push 1 32,
   .op .SHR]

def donepart2Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 : UInt256) (rest : List UInt256) : State :=
  let v0 : ByteArray := MachineState.writeBytes s.memory (Data.Bytes.natToBytesPadded x0.toNat 32) 64
  let v1 : UInt256 := UInt256.shiftLeft x4 (UInt256.ofNat 208)
  let v2 : UInt256 := UInt256.shiftRight x3 (UInt256.ofNat 32)
  {s with pc := UInt256.ofNat 5315, memory := v0, stack := v2 :: v1 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: rest}

theorem donepart2_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions donepart2Program {s with pc := UInt256.ofNat 5304, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: rest} =
      some (donepart2Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 rest) := by
  have hc (j : Nat) (hj : j ≤ 28) : rest.length + j < 1024 := by omega
  have hcr : rest.length < 1024 := by omega
  have ha64 : (64 : UInt256).toNat = 64 := rfl
  have hf64 := activeWords_fix s 64 32 (by decide) (by norm_num) hact
  simp [hz, hzn, donepart2Program, donepart2Model, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, ofNat_sub_ofNat, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, hc, hcr, ha64, hf64]

def donepart3Program : List Instr :=
  [.op .OR,
   .push 1 32,
   .op .MSTORE,
   .op (.Dup ⟨4, by decide⟩),
   .push 1 192,
   .op .SHL,
   .op (.Dup ⟨4, by decide⟩)]

def donepart3Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 : UInt256) (rest : List UInt256) : State :=
  let v0 : UInt256 := UInt256.lor x0 x1
  let v1 : ByteArray := MachineState.writeBytes s.memory (Data.Bytes.natToBytesPadded v0.toNat 32) 32
  let v2 : UInt256 := UInt256.shiftLeft x6 (UInt256.ofNat 192)
  {s with pc := UInt256.ofNat 5324, memory := v1, stack := x5 :: v2 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: rest}

theorem donepart3_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions donepart3Program {s with pc := UInt256.ofNat 5315, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: rest} =
      some (donepart3Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 rest) := by
  have hc (j : Nat) (hj : j ≤ 27) : rest.length + j < 1024 := by omega
  have hcr : rest.length < 1024 := by omega
  have ha32 : (32 : UInt256).toNat = 32 := rfl
  have hf32 := activeWords_fix s 32 32 (by decide) (by norm_num) hact
  simp [hz, hzn, donepart3Program, donepart3Model, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, ofNat_sub_ofNat, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, hc, hcr, ha32, hf32]

def donepart4Program : List Instr :=
  [.push 1 48,
   .op .SHR,
   .op .OR,
   .push 0 0,
   .op .MSTORE]

def donepart4Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 : UInt256) (rest : List UInt256) : State :=
  let v0 : UInt256 := UInt256.shiftRight x0 (UInt256.ofNat 48)
  let v1 : UInt256 := UInt256.lor v0 x1
  let v2 : ByteArray := MachineState.writeBytes s.memory (Data.Bytes.natToBytesPadded v1.toNat 32) 0
  {s with pc := UInt256.ofNat 5330, memory := v2, stack := x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: rest}

theorem donepart4_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions donepart4Program {s with pc := UInt256.ofNat 5324, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: rest} =
      some (donepart4Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 rest) := by
  have hc (j : Nat) (hj : j ≤ 28) : rest.length + j < 1024 := by omega
  have hcr : rest.length < 1024 := by omega
  have ha0 : (0 : UInt256).toNat = 0 := rfl
  have hf0 := activeWords_fix s 0 32 (by decide) (by norm_num) hact
  simp [hz, hzn, donepart4Program, donepart4Model, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, ofNat_sub_ofNat, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, hc, hcr, ha0, hf0]

def doneProgram : List Instr :=
  [.op .JUMPDEST,
   .op (.Dup ⟨1, by decide⟩),
   .push 1 240,
   .op .SHL,
   .op (.Dup ⟨1, by decide⟩),
   .op .OR,
   .push 1 96,
   .op .MSTORE,
   .op (.Dup ⟨2, by decide⟩),
   .push 1 224,
   .op .SHL,
   .op (.Dup ⟨2, by decide⟩),
   .push 1 16,
   .op .SHR,
   .op .OR,
   .push 1 64,
   .op .MSTORE,
   .op (.Dup ⟨3, by decide⟩),
   .push 1 208,
   .op .SHL,
   .op (.Dup ⟨3, by decide⟩),
   .push 1 32,
   .op .SHR,
   .op .OR,
   .push 1 32,
   .op .MSTORE,
   .op (.Dup ⟨4, by decide⟩),
   .push 1 192,
   .op .SHL,
   .op (.Dup ⟨4, by decide⟩),
   .push 1 48,
   .op .SHR,
   .op .OR,
   .push 0 0,
   .op .MSTORE]

def doneModel (s : State) (a0 a1 a2 a3 a4 n1 n2 n3 n4 P inv cntp : UInt256) (rest : List UInt256) : State :=
  let v0 : UInt256 := UInt256.shiftLeft a1 (UInt256.ofNat 240)
  let v1 : UInt256 := UInt256.lor a0 v0
  let v2 : ByteArray := MachineState.writeBytes s.memory (Data.Bytes.natToBytesPadded v1.toNat 32) 96
  let v3 : UInt256 := UInt256.shiftLeft a2 (UInt256.ofNat 224)
  let v4 : UInt256 := UInt256.shiftRight a1 (UInt256.ofNat 16)
  let v5 : UInt256 := UInt256.lor v4 v3
  let v6 : ByteArray := MachineState.writeBytes v2 (Data.Bytes.natToBytesPadded v5.toNat 32) 64
  let v7 : UInt256 := UInt256.shiftLeft a3 (UInt256.ofNat 208)
  let v8 : UInt256 := UInt256.shiftRight a2 (UInt256.ofNat 32)
  let v9 : UInt256 := UInt256.lor v8 v7
  let v10 : ByteArray := MachineState.writeBytes v6 (Data.Bytes.natToBytesPadded v9.toNat 32) 32
  let v11 : UInt256 := UInt256.shiftLeft a4 (UInt256.ofNat 192)
  let v12 : UInt256 := UInt256.shiftRight a3 (UInt256.ofNat 48)
  let v13 : UInt256 := UInt256.lor v12 v11
  let v14 : ByteArray := MachineState.writeBytes v10 (Data.Bytes.natToBytesPadded v13.toNat 32) 0
  {s with pc := UInt256.ofNat 5330, memory := v14, stack := a0 :: a1 :: a2 :: a3 :: a4 :: n1 :: n2 :: n3 :: n4 :: P :: inv :: cntp :: rest}

theorem done_run (s : State) (a0 a1 a2 a3 a4 n1 n2 n3 n4 P inv cntp : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions doneProgram {s with pc := UInt256.ofNat 5285, stack := a0 :: a1 :: a2 :: a3 :: a4 :: n1 :: n2 :: n3 :: n4 :: P :: inv :: cntp :: rest} =
      some (doneModel s a0 a1 a2 a3 a4 n1 n2 n3 n4 P inv cntp rest) := by
  let v0 : UInt256 := UInt256.shiftLeft a1 (UInt256.ofNat 240)
  let v1 : UInt256 := UInt256.lor a0 v0
  let v2 : ByteArray := MachineState.writeBytes s.memory (Data.Bytes.natToBytesPadded v1.toNat 32) 96
  let v3 : UInt256 := UInt256.shiftLeft a2 (UInt256.ofNat 224)
  let v4 : UInt256 := UInt256.shiftRight a1 (UInt256.ofNat 16)
  let v5 : UInt256 := UInt256.lor v4 v3
  let v6 : ByteArray := MachineState.writeBytes v2 (Data.Bytes.natToBytesPadded v5.toNat 32) 64
  let v7 : UInt256 := UInt256.shiftLeft a3 (UInt256.ofNat 208)
  let v8 : UInt256 := UInt256.shiftRight a2 (UInt256.ofNat 32)
  let v9 : UInt256 := UInt256.lor v8 v7
  let v10 : ByteArray := MachineState.writeBytes v6 (Data.Bytes.natToBytesPadded v9.toNat 32) 32
  let v11 : UInt256 := UInt256.shiftLeft a4 (UInt256.ofNat 192)
  let v12 : UInt256 := UInt256.shiftRight a3 (UInt256.ofNat 48)
  let v13 : UInt256 := UInt256.lor v12 v11
  let v14 : ByteArray := MachineState.writeBytes v10 (Data.Bytes.natToBytesPadded v13.toNat 32) 0
  have h0 : runInstructions donepart0Program {s with pc := UInt256.ofNat 5285, memory := s.memory, stack := a0 :: a1 :: a2 :: a3 :: a4 :: n1 :: n2 :: n3 :: n4 :: P :: inv :: cntp :: rest} = some {s with pc := UInt256.ofNat 5295, memory := v2, stack := a0 :: a1 :: a2 :: a3 :: a4 :: n1 :: n2 :: n3 :: n4 :: P :: inv :: cntp :: rest} := by
    simpa only [donepart0Model, v0, v1, v2] using donepart0_run (s) a0 a1 a2 a3 a4 n1 n2 n3 n4 P inv cntp rest hcap hact
  have h1 : runInstructions donepart1Program {s with pc := UInt256.ofNat 5295, memory := v2, stack := a0 :: a1 :: a2 :: a3 :: a4 :: n1 :: n2 :: n3 :: n4 :: P :: inv :: cntp :: rest} = some {s with pc := UInt256.ofNat 5304, memory := v2, stack := v5 :: a0 :: a1 :: a2 :: a3 :: a4 :: n1 :: n2 :: n3 :: n4 :: P :: inv :: cntp :: rest} := by
    simpa only [donepart1Model, v3, v4, v5] using donepart1_run ({s with memory := v2}) a0 a1 a2 a3 a4 n1 n2 n3 n4 P inv cntp rest hcap hact
  have h2 : runInstructions donepart2Program {s with pc := UInt256.ofNat 5304, memory := v2, stack := v5 :: a0 :: a1 :: a2 :: a3 :: a4 :: n1 :: n2 :: n3 :: n4 :: P :: inv :: cntp :: rest} = some {s with pc := UInt256.ofNat 5315, memory := v6, stack := v8 :: v7 :: a0 :: a1 :: a2 :: a3 :: a4 :: n1 :: n2 :: n3 :: n4 :: P :: inv :: cntp :: rest} := by
    simpa only [donepart2Model, v6, v7, v8] using donepart2_run ({s with memory := v2}) v5 a0 a1 a2 a3 a4 n1 n2 n3 n4 P inv cntp rest hcap hact
  have h3 : runInstructions donepart3Program {s with pc := UInt256.ofNat 5315, memory := v6, stack := v8 :: v7 :: a0 :: a1 :: a2 :: a3 :: a4 :: n1 :: n2 :: n3 :: n4 :: P :: inv :: cntp :: rest} = some {s with pc := UInt256.ofNat 5324, memory := v10, stack := a3 :: v11 :: a0 :: a1 :: a2 :: a3 :: a4 :: n1 :: n2 :: n3 :: n4 :: P :: inv :: cntp :: rest} := by
    simpa only [donepart3Model, v9, v10, v11] using donepart3_run ({s with memory := v6}) v8 v7 a0 a1 a2 a3 a4 n1 n2 n3 n4 P inv cntp rest hcap hact
  have h4 : runInstructions donepart4Program {s with pc := UInt256.ofNat 5324, memory := v10, stack := a3 :: v11 :: a0 :: a1 :: a2 :: a3 :: a4 :: n1 :: n2 :: n3 :: n4 :: P :: inv :: cntp :: rest} = some {s with pc := UInt256.ofNat 5330, memory := v14, stack := a0 :: a1 :: a2 :: a3 :: a4 :: n1 :: n2 :: n3 :: n4 :: P :: inv :: cntp :: rest} := by
    simpa only [donepart4Model, v12, v13, v14] using donepart4_run ({s with memory := v10}) a3 v11 a0 a1 a2 a3 a4 n1 n2 n3 n4 P inv cntp rest hcap hact
  exact (runInstructions_append_some _ _ _ _ _ h0 (runInstructions_append_some _ _ _ _ _ h1 (runInstructions_append_some _ _ _ _ _ h2 (runInstructions_append_some _ _ _ _ _ h3 h4))))

def done_mem (mem : ByteArray) (a0 a1 a2 a3 a4 n1 n2 n3 n4 P inv cntp : UInt256) : ByteArray :=
  (MachineState.writeBytes (MachineState.writeBytes (MachineState.writeBytes (MachineState.writeBytes mem (Data.Bytes.natToBytesPadded (UInt256.lor a0 (UInt256.shiftLeft a1 (UInt256.ofNat 240))).toNat 32) 96) (Data.Bytes.natToBytesPadded (UInt256.lor (UInt256.shiftRight a1 (UInt256.ofNat 16)) (UInt256.shiftLeft a2 (UInt256.ofNat 224))).toNat 32) 64) (Data.Bytes.natToBytesPadded (UInt256.lor (UInt256.shiftRight a2 (UInt256.ofNat 32)) (UInt256.shiftLeft a3 (UInt256.ofNat 208))).toNat 32) 32) (Data.Bytes.natToBytesPadded (UInt256.lor (UInt256.shiftRight a3 (UInt256.ofNat 48)) (UInt256.shiftLeft a4 (UInt256.ofNat 192))).toNat 32) 0)

theorem done_eq (s : State) (a0 a1 a2 a3 a4 n1 n2 n3 n4 P inv cntp : UInt256) (rest : List UInt256) :
    doneModel s a0 a1 a2 a3 a4 n1 n2 n3 n4 P inv cntp rest =
      {s with pc := UInt256.ofNat 5330, memory := done_mem s.memory a0 a1 a2 a3 a4 n1 n2 n3 n4 P inv cntp, stack := a0 :: a1 :: a2 :: a3 :: a4 :: n1 :: n2 :: n3 :: n4 :: P :: inv :: cntp :: rest} := by
  simp only [doneModel, done_mem]

end CycleSubmission.R5.ExecNorm
