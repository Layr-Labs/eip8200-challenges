import Challenge.EvmProof.Stepper
import Challenge.Modexp.Submission.Proofs.Bytecode.WindowNibbleDefs
import Challenge.Modexp.Submission.Proofs.Fast.Monpro
import Challenge.Modexp.Submission.Proofs.Cycle.DoubleInput

set_option warningAsError true
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000

/-! Exact fused square columns 0+1 for the doubled a0*a2 input pair.
The high sums at PC 5840 are deliberately NOT identified. Their reductions
at PC 5859 agree, including the intervening memory write to address 192.
No bound on any other input digit is required. -/
namespace CycleSubmission.DoubleInput01
open EvmSemantics EvmSemantics.EVM YulEvmCompiler
open Challenge.EvmProof.Word Challenge.EvmProof.Stepper
open Challenge.Modexp.Submission.Proofs.Bytecode.WindowNibbleKernel
open Challenge.Modexp.Submission.Proofs.Fast
local notation "W" => UInt256
local notation "N" => UInt256.ofNat



def b0Program : List Instr :=
  [.push 2 768,
   .op .MLOAD,
   .op (.Dup ⟨8, by decide⟩),
   .op (.Dup ⟨1, by decide⟩),
   .op (.Dup ⟨0, by decide⟩),
   .op (.Dup ⟨0, by decide⟩),
   .op .MUL]

def b0Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 : W) (rest : List W) : State :=
  let v0 : W := MachineState.readWord (s.memory) 768
  let v1 : W := v0 * v0
  {s with pc := N 5721, memory := s.memory, stack := v1 :: v0 :: x7 :: v0 :: x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: rest}

theorem b0_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions b0Program {s with pc := N 5712, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: rest} =
      some (b0Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 rest) := by
  have capacity (j : Nat) (hj : j ≤ 32) : rest.length+j < 1024 := by omega
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have ha768 : (768 : W).toNat = 768 := rfl
  have hf768 := Monpro.activeWords_fix s 768 32 (by decide) (by norm_num) hact
  simp [hz, hzn, capacity,b0Program, b0Model, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, Challenge.EvmProof.Word.literal_eq_ofNat, ha768, hf768]

def b1Program : List Instr :=
  [.push 2 2720,
   .op .MLOAD,
   .op .MUL,
   .op (.Dup ⟨14, by decide⟩),
   .op .AND,
   .op (.Swap ⟨11, by decide⟩),
   .op .POP,
   .op (.Dup ⟨10, by decide⟩)]

def b1Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 : W) (rest : List W) : State :=
  let v0 : W := MachineState.readWord (s.memory) 2720
  let v1 : W := v0 * x0
  let v2 : W := UInt256.land x14 v1
  {s with pc := N 5731, memory := s.memory, stack := x11 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: v2 :: x13 :: x14 :: x15 :: x16 :: x17 :: rest}

theorem b1_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions b1Program {s with pc := N 5721, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: rest} =
      some (b1Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 rest) := by
  have capacity (j : Nat) (hj : j ≤ 32) : rest.length+j < 1024 := by omega
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have ha2720 : (2720 : W).toNat = 2720 := rfl
  have hf2720 := Monpro.activeWords_fix s 2720 32 (by decide) (by norm_num) hact
  simp [hz, hzn, capacity,b1Program, b1Model, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, Challenge.EvmProof.Word.literal_eq_ofNat, ha2720, hf2720]

def b2Program : List Instr :=
  [.op (.Swap ⟨2, by decide⟩),
   .op .MULMOD,
   .op (.Dup ⟨1, by decide⟩),
   .op (.Dup ⟨11, by decide⟩),
   .op (.Dup ⟨15, by decide⟩),
   .op .MULMOD,
   .op .ADD,
   .push 3 2048]

def b2Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 : W) (rest : List W) : State :=
  let v0 : W := UInt256.mulMod x3 x1 x2
  let v1 : W := UInt256.mulMod x15 x12 x0
  let v2 : W := v1 + v0
  {s with pc := N 5742, memory := s.memory, stack := (N 2048) :: v2 :: x0 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: rest}

theorem b2_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions b2Program {s with pc := N 5731, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: rest} =
      some (b2Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 rest) := by
  have capacity (j : Nat) (hj : j ≤ 32) : rest.length+j < 1024 := by omega
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  simp [hz, hzn, capacity,b2Program, b2Model, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, Challenge.EvmProof.Word.literal_eq_ofNat, ]

def b3Program : List Instr :=
  [.op .MULMOD,
   .push 2 768,
   .op .MLOAD,
   .op (.Dup ⟨0, by decide⟩),
   .op .ADD,
   .op (.Dup ⟨9, by decide⟩),
   .op (.Dup ⟨1, by decide⟩),
   .op (.Dup ⟨7, by decide⟩)]

def b3Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 : W) (rest : List W) : State :=
  let v0 : W := UInt256.mulMod x0 x1 x2
  let v1 : W := MachineState.readWord (s.memory) 768
  let v2 : W := v1 + v1
  {s with pc := N 5752, memory := s.memory, stack := x6 :: v2 :: x10 :: v2 :: v0 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: rest}

theorem b3_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions b3Program {s with pc := N 5742, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: rest} =
      some (b3Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 rest) := by
  have capacity (j : Nat) (hj : j ≤ 32) : rest.length+j < 1024 := by omega
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have ha768 : (768 : W).toNat = 768 := rfl
  have hf768 := Monpro.activeWords_fix s 768 32 (by decide) (by norm_num) hact
  simp [hz, hzn, capacity,b3Program, b3Model, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, Challenge.EvmProof.Word.literal_eq_ofNat, ha768, hf768]

def b4Program : List Instr :=
  [.op .MULMOD,
   .op (.Swap ⟨0, by decide⟩),
   .op (.Dup ⟨6, by decide⟩),
   .op .MUL,
   .op (.Dup ⟨2, by decide⟩),
   .op .ADD,
   .op (.Dup ⟨11, by decide⟩),
   .op (.Dup ⟨13, by decide⟩)]

def b4Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 : W) (rest : List W) : State :=
  let v0 : W := UInt256.mulMod x0 x1 x2
  let v1 : W := x8 * x3
  let v2 : W := x4 + v1
  {s with pc := N 5760, memory := s.memory, stack := x14 :: x13 :: v2 :: v0 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: x18 :: rest}

theorem b4_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions b4Program {s with pc := N 5752, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: x18 :: rest} =
      some (b4Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 rest) := by
  have capacity (j : Nat) (hj : j ≤ 32) : rest.length+j < 1024 := by omega
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  simp [hz, hzn, capacity,b4Program, b4Model, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, Challenge.EvmProof.Word.literal_eq_ofNat, ]

def b5Program : List Instr :=
  [.op .MUL,
   .op .ADD,
   .op (.Swap ⟨1, by decide⟩),
   .op .ADD,
   .op (.Dup ⟨9, by decide⟩),
   .op (.Dup ⟨12, by decide⟩),
   .op (.Dup ⟨12, by decide⟩),
   .op .MULMOD]

def b5Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 : W) (rest : List W) : State :=
  let v0 : W := x0 * x1
  let v1 : W := v0 + x2
  let v2 : W := x4 + x3
  let v3 : W := UInt256.mulMod x13 x14 x12
  {s with pc := N 5768, memory := s.memory, stack := v3 :: v2 :: v1 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: x18 :: rest}

theorem b5_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions b5Program {s with pc := N 5760, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: x18 :: rest} =
      some (b5Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 rest) := by
  have capacity (j : Nat) (hj : j ≤ 32) : rest.length+j < 1024 := by omega
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  simp [hz, hzn, capacity,b5Program, b5Model, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, Challenge.EvmProof.Word.literal_eq_ofNat, ]

def b6Program : List Instr :=
  [.op .ADD,
   .op (.Dup ⟨9, by decide⟩),
   .op (.Dup ⟨14, by decide⟩),
   .push 4 2720,
   .op .MLOAD,
   .op (.Dup ⟨2, by decide⟩),
   .op (.Swap ⟨4, by decide⟩),
   .op .MUL]

def b6Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 : W) (rest : List W) : State :=
  let v0 : W := x0 + x1
  let v1 : W := MachineState.readWord (s.memory) 2720
  let v2 : W := x2 * v1
  {s with pc := N 5780, memory := s.memory, stack := v2 :: x14 :: x10 :: v0 :: x10 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: rest}

theorem b6_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions b6Program {s with pc := N 5768, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: rest} =
      some (b6Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 rest) := by
  have capacity (j : Nat) (hj : j ≤ 32) : rest.length+j < 1024 := by omega
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have ha2720 : (2720 : W).toNat = 2720 := rfl
  have hf2720 := Monpro.activeWords_fix s 2720 32 (by decide) (by norm_num) hact
  simp [hz, hzn, capacity,b6Program, b6Model, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, Challenge.EvmProof.Word.literal_eq_ofNat, ha2720, hf2720]

def b7Program : List Instr :=
  [.op (.Dup ⟨15, by decide⟩),
   .op .AND,
   .op (.Dup ⟨0, by decide⟩),
   .op (.Swap ⟨11, by decide⟩),
   .op .POP,
   .op .MULMOD,
   .op .ADD,
   .push 2 2048]

def b7Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 : W) (rest : List W) : State :=
  let v0 : W := UInt256.land x15 x0
  let v1 : W := UInt256.mulMod v0 x1 x2
  let v2 : W := v1 + x3
  {s with pc := N 5790, memory := s.memory, stack := (N 2048) :: v2 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: v0 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: x18 :: rest}

theorem b7_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions b7Program {s with pc := N 5780, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: x18 :: rest} =
      some (b7Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 rest) := by
  have capacity (j : Nat) (hj : j ≤ 32) : rest.length+j < 1024 := by omega
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  simp [hz, hzn, capacity,b7Program, b7Model, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, Challenge.EvmProof.Word.literal_eq_ofNat, ]

def b8Program : List Instr :=
  [.op .MULMOD,
   .push 5 768,
   .op .MLOAD,
   .op (.Dup ⟨0, by decide⟩),
   .op .ADD,
   .op (.Dup ⟨2, by decide⟩),
   .op (.Dup ⟨11, by decide⟩),
   .op .MUL]

def b8Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 : W) (rest : List W) : State :=
  let v0 : W := UInt256.mulMod x0 x1 x2
  let v1 : W := MachineState.readWord (s.memory) 768
  let v2 : W := v1 + v1
  let v3 : W := x11 * x3
  {s with pc := N 5803, memory := s.memory, stack := v3 :: v2 :: v0 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: rest}

theorem b8_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions b8Program {s with pc := N 5790, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: rest} =
      some (b8Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 rest) := by
  have capacity (j : Nat) (hj : j ≤ 32) : rest.length+j < 1024 := by omega
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have ha768 : (768 : W).toNat = 768 := rfl
  have hf768 := Monpro.activeWords_fix s 768 32 (by decide) (by norm_num) hact
  simp [hz, hzn, capacity,b8Program, b8Model, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, Challenge.EvmProof.Word.literal_eq_ofNat, ha768, hf768]

def b9Program : List Instr :=
  [.op (.Dup ⟨6, by decide⟩),
   .op (.Dup ⟨0, by decide⟩),
   .op .MUL,
   .op (.Dup ⟨11, by decide⟩),
   .op (.Dup ⟨3, by decide⟩),
   .op (.Dup ⟨10, by decide⟩),
   .op .MULMOD,
   .op (.Swap ⟨2, by decide⟩)]

def b9Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 : W) (rest : List W) : State :=
  let v0 : W := x6 * x6
  let v1 : W := UInt256.mulMod x7 x1 x10
  {s with pc := N 5811, memory := s.memory, stack := x1 :: v0 :: x0 :: v1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: rest}

theorem b9_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions b9Program {s with pc := N 5803, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: rest} =
      some (b9Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 rest) := by
  have capacity (j : Nat) (hj : j ≤ 32) : rest.length+j < 1024 := by omega
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  simp [hz, hzn, capacity,b9Program, b9Model, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, Challenge.EvmProof.Word.literal_eq_ofNat, ]

def b10Program : List Instr :=
  [.op (.Dup ⟨9, by decide⟩),
   .op .MUL,
   .op (.Dup ⟨4, by decide⟩),
   .op .ADD,
   .op .ADD,
   .op .ADD,
   .op (.Dup ⟨9, by decide⟩),
   .op (.Dup ⟨13, by decide⟩)]

def b10Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 : W) (rest : List W) : State :=
  let v0 : W := x9 * x0
  let v1 : W := x4 + v0
  let v2 : W := v1 + x1
  let v3 : W := v2 + x2
  {s with pc := N 5819, memory := s.memory, stack := x14 :: x11 :: v3 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: x18 :: rest}

theorem b10_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions b10Program {s with pc := N 5811, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: x18 :: rest} =
      some (b10Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 rest) := by
  have capacity (j : Nat) (hj : j ≤ 32) : rest.length+j < 1024 := by omega
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  simp [hz, hzn, capacity,b10Program, b10Model, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, Challenge.EvmProof.Word.literal_eq_ofNat, ]

def b11Program : List Instr :=
  [.op .MUL,
   .op .ADD,
   .op (.Swap ⟨1, by decide⟩),
   .op .ADD,
   .op (.Dup ⟨9, by decide⟩),
   .op (.Dup ⟨6, by decide⟩),
   .op (.Dup ⟨0, by decide⟩),
   .op .MULMOD]

def b11Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 : W) (rest : List W) : State :=
  let v0 : W := x0 * x1
  let v1 : W := v0 + x2
  let v2 : W := x4 + x3
  let v3 : W := UInt256.mulMod x8 x8 x12
  {s with pc := N 5827, memory := s.memory, stack := v3 :: v2 :: v1 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: x18 :: rest}

theorem b11_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions b11Program {s with pc := N 5819, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: x18 :: rest} =
      some (b11Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 rest) := by
  have capacity (j : Nat) (hj : j ≤ 32) : rest.length+j < 1024 := by omega
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  simp [hz, hzn, capacity,b11Program, b11Model, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, Challenge.EvmProof.Word.literal_eq_ofNat, ]

def b12Program : List Instr :=
  [.op .ADD,
   .op (.Dup ⟨9, by decide⟩),
   .op (.Dup ⟨3, by decide⟩),
   .op (.Dup ⟨12, by decide⟩),
   .op .MULMOD,
   .op .ADD,
   .op (.Dup ⟨9, by decide⟩),
   .op (.Dup ⟨12, by decide⟩)]

def b12Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 : W) (rest : List W) : State :=
  let v0 : W := x0 + x1
  let v1 : W := UInt256.mulMod x11 x3 x10
  let v2 : W := v1 + v0
  {s with pc := N 5835, memory := s.memory, stack := x12 :: x10 :: v2 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: rest}

theorem b12_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions b12Program {s with pc := N 5827, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: rest} =
      some (b12Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 rest) := by
  have capacity (j : Nat) (hj : j ≤ 32) : rest.length+j < 1024 := by omega
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  simp [hz, hzn, capacity,b12Program, b12Model, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, Challenge.EvmProof.Word.literal_eq_ofNat, ]

def b13Program : List Instr :=
  [.op (.Dup ⟨10, by decide⟩),
   .op .MULMOD,
   .op .ADD,
   .op (.Dup ⟨9, by decide⟩),
   .op (.Dup ⟨14, by decide⟩)]

def b13Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 : W) (rest : List W) : State :=
  let v0 : W := UInt256.mulMod x10 x0 x1
  let v1 : W := v0 + x2
  {s with pc := N 5840, memory := s.memory, stack := x15 :: x11 :: v1 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: rest}

theorem b13_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions b13Program {s with pc := N 5835, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: rest} =
      some (b13Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 rest) := by
  have capacity (j : Nat) (hj : j ≤ 32) : rest.length+j < 1024 := by omega
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  simp [hz, hzn, capacity,b13Program, b13Model, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, Challenge.EvmProof.Word.literal_eq_ofNat, ]

def program0 : List Instr := b0Program ++ (b1Program ++ (b2Program ++ (b3Program ++ (b4Program ++ (b5Program ++ (b6Program ++ (b7Program ++ (b8Program ++ (b9Program ++ (b10Program ++ (b11Program ++ (b12Program ++ (b13Program)))))))))))))

def b14Program : List Instr :=
  [.push 2 2720,
   .op .MLOAD,
   .op (.Dup ⟨2, by decide⟩),
   .op (.Swap ⟨4, by decide⟩),
   .op .MUL,
   .op (.Dup ⟨15, by decide⟩),
   .op .AND,
   .op (.Dup ⟨0, by decide⟩)]

def b14Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 : W) (rest : List W) : State :=
  let v0 : W := MachineState.readWord (s.memory) 2720
  let v1 : W := x3 * v0
  let v2 : W := UInt256.land x14 v1
  {s with pc := N 5850, memory := s.memory, stack := v2 :: v2 :: x0 :: x1 :: x2 :: x1 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: rest}

theorem b14_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions b14Program {s with pc := N 5840, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: rest} =
      some (b14Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 rest) := by
  have capacity (j : Nat) (hj : j ≤ 32) : rest.length+j < 1024 := by omega
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have ha2720 : (2720 : W).toNat = 2720 := rfl
  have hf2720 := Monpro.activeWords_fix s 2720 32 (by decide) (by norm_num) hact
  simp [hz, hzn, capacity,b14Program, b14Model, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, Challenge.EvmProof.Word.literal_eq_ofNat, ha2720, hf2720]

def b15Program : List Instr :=
  [.push 1 192,
   .op .MSTORE,
   .op .MULMOD,
   .op .ADD,
   .push 2 2048,
   .op .MULMOD]

def b15Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 : W) (rest : List W) : State :=
  let v0 : ByteArray := MachineState.writeBytes s.memory (Data.Bytes.natToBytesPadded x0.toNat 32) 192
  let v1 : W := UInt256.mulMod x1 x2 x3
  let v2 : W := v1 + x4
  let v3 : W := UInt256.mulMod (N 2048) v2 x5
  {s with pc := N 5859, memory := v0, stack := v3 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: x18 :: x19 :: rest}

theorem b15_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions b15Program {s with pc := N 5850, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: x18 :: x19 :: rest} =
      some (b15Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 rest) := by
  have capacity (j : Nat) (hj : j ≤ 32) : rest.length+j < 1024 := by omega
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have ha192 : (192 : W).toNat = 192 := rfl
  have hf192 := Monpro.activeWords_fix s 192 32 (by decide) (by norm_num) hact
  simp [hz, hzn, capacity,b15Program, b15Model, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, Challenge.EvmProof.Word.literal_eq_ofNat, ha192, hf192]

def prefix1 : List Instr := b14Program ++ (b15Program)

def candidateBoundaryModel (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 : W) (rest : List W) : State :=
  let v0 : W := MachineState.readWord (s.memory) 768
  let v1 : W := v0 * v0
  let v2 : W := MachineState.readWord (s.memory) 2720
  let v3 : W := v2 * v1
  let v4 : W := UInt256.land w10 v3
  let v5 : W := UInt256.mulMod v0 v0 w7
  let v6 : W := UInt256.mulMod w11 v4 w7
  let v7 : W := v6 + v5
  let v8 : W := UInt256.mulMod (N 2048) v7 w7
  let v9 : W := MachineState.readWord (s.memory) 768
  let v10 : W := v9 + v9
  let v11 : W := UInt256.mulMod w3 v10 w7
  let v12 : W := w3 * v10
  let v13 : W := v8 + v12
  let v14 : W := w9 * v4
  let v15 : W := v14 + v13
  let v16 : W := v8 + v11
  let v17 : W := UInt256.mulMod v4 w9 w7
  let v18 : W := v17 + v16
  let v19 : W := MachineState.readWord (s.memory) 2720
  let v20 : W := v15 * v19
  let v21 : W := UInt256.land w10 v20
  let v22 : W := UInt256.mulMod v21 w11 w7
  let v23 : W := v22 + v18
  let v24 : W := UInt256.mulMod (N 2048) v23 w7
  let v25 : W := MachineState.readWord (s.memory) 768
  let v26 : W := v25 + v25
  let v27 : W := v4 * w0
  let v28 : W := w3 * w3
  let v29 : W := UInt256.mulMod w4 v26 w7
  let v30 : W := w4 * v26
  let v31 : W := v24 + v30
  let v32 : W := v31 + v28
  let v33 : W := v32 + v27
  let v34 : W := w9 * v21
  let v35 : W := v34 + v33
  let v36 : W := v24 + v29
  let v37 : W := UInt256.mulMod w3 w3 w7
  let v38 : W := v37 + v36
  let v39 : W := UInt256.mulMod v4 w0 w7
  let v40 : W := v39 + v38
  let v41 : W := UInt256.mulMod v21 w9 w7
  let v42 : W := v41 + v40
  let v43 : W := MachineState.readWord (s.memory) 2720
  let v44 : W := v35 * v43
  let v45 : W := UInt256.land w10 v44
  let v46 : ByteArray := MachineState.writeBytes s.memory (Data.Bytes.natToBytesPadded v45.toNat 32) 192
  let v47 : W := UInt256.mulMod v45 w11 w7
  let v48 : W := v47 + v42
  let v49 : W := UInt256.mulMod (N 2048) v48 w7
  {s with pc := N 5859, memory := v46, stack := v49 :: w0 :: w1 :: w2 :: w3 :: w4 :: w5 :: v21 :: w7 :: v4 :: w9 :: w10 :: w11 :: w12 :: w13 :: rest}

theorem b_run (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions (program0 ++ prefix1) {s with pc := N 5712, stack := w0 :: w1 :: w2 :: w3 :: w4 :: w5 :: w6 :: w7 :: w8 :: w9 :: w10 :: w11 :: w12 :: w13 :: rest} =
      some (candidateBoundaryModel s w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 rest) := by
  let v0 : W := MachineState.readWord (s.memory) 768
  let v1 : W := v0 * v0
  let v2 : W := MachineState.readWord (s.memory) 2720
  let v3 : W := v2 * v1
  let v4 : W := UInt256.land w10 v3
  let v5 : W := UInt256.mulMod v0 v0 w7
  let v6 : W := UInt256.mulMod w11 v4 w7
  let v7 : W := v6 + v5
  let v8 : W := UInt256.mulMod (N 2048) v7 w7
  let v9 : W := MachineState.readWord (s.memory) 768
  let v10 : W := v9 + v9
  let v11 : W := UInt256.mulMod w3 v10 w7
  let v12 : W := w3 * v10
  let v13 : W := v8 + v12
  let v14 : W := w9 * v4
  let v15 : W := v14 + v13
  let v16 : W := v8 + v11
  let v17 : W := UInt256.mulMod v4 w9 w7
  let v18 : W := v17 + v16
  let v19 : W := MachineState.readWord (s.memory) 2720
  let v20 : W := v15 * v19
  let v21 : W := UInt256.land w10 v20
  let v22 : W := UInt256.mulMod v21 w11 w7
  let v23 : W := v22 + v18
  let v24 : W := UInt256.mulMod (N 2048) v23 w7
  let v25 : W := MachineState.readWord (s.memory) 768
  let v26 : W := v25 + v25
  let v27 : W := v4 * w0
  let v28 : W := w3 * w3
  let v29 : W := UInt256.mulMod w4 v26 w7
  let v30 : W := w4 * v26
  let v31 : W := v24 + v30
  let v32 : W := v31 + v28
  let v33 : W := v32 + v27
  let v34 : W := w9 * v21
  let v35 : W := v34 + v33
  let v36 : W := v24 + v29
  let v37 : W := UInt256.mulMod w3 w3 w7
  let v38 : W := v37 + v36
  let v39 : W := UInt256.mulMod v4 w0 w7
  let v40 : W := v39 + v38
  let v41 : W := UInt256.mulMod v21 w9 w7
  let v42 : W := v41 + v40
  let v43 : W := MachineState.readWord (s.memory) 2720
  let v44 : W := v35 * v43
  let v45 : W := UInt256.land w10 v44
  let v46 : ByteArray := MachineState.writeBytes s.memory (Data.Bytes.natToBytesPadded v45.toNat 32) 192
  let v47 : W := UInt256.mulMod v45 w11 w7
  let v48 : W := v47 + v42
  let v49 : W := UInt256.mulMod (N 2048) v48 w7
  have h0 : runInstructions b0Program {s with pc := N 5712, memory := s.memory, stack := w0 :: w1 :: w2 :: w3 :: w4 :: w5 :: w6 :: w7 :: w8 :: w9 :: w10 :: w11 :: w12 :: w13 :: rest} = some {s with pc := N 5721, memory := s.memory, stack := v1 :: v0 :: w7 :: v0 :: w0 :: w1 :: w2 :: w3 :: w4 :: w5 :: w6 :: w7 :: w8 :: w9 :: w10 :: w11 :: w12 :: w13 :: rest} := by
    simpa only [b0Model, v0, v1] using
      b0_run ({s with memory := s.memory}) (w0) (w1) (w2) (w3) (w4) (w5) (w6) (w7) (w8) (w9) (w10) (w11) (w12) (w13) rest hcap hact
  have h1 : runInstructions b1Program {s with pc := N 5721, memory := s.memory, stack := v1 :: v0 :: w7 :: v0 :: w0 :: w1 :: w2 :: w3 :: w4 :: w5 :: w6 :: w7 :: w8 :: w9 :: w10 :: w11 :: w12 :: w13 :: rest} = some {s with pc := N 5731, memory := s.memory, stack := w7 :: v0 :: w7 :: v0 :: w0 :: w1 :: w2 :: w3 :: w4 :: w5 :: w6 :: w7 :: v4 :: w9 :: w10 :: w11 :: w12 :: w13 :: rest} := by
    simpa only [b1Model, v2, v3, v4] using
      b1_run ({s with memory := s.memory}) (v1) (v0) (w7) (v0) (w0) (w1) (w2) (w3) (w4) (w5) (w6) (w7) (w8) (w9) (w10) (w11) (w12) (w13) rest hcap hact
  have h2 : runInstructions b2Program {s with pc := N 5731, memory := s.memory, stack := w7 :: v0 :: w7 :: v0 :: w0 :: w1 :: w2 :: w3 :: w4 :: w5 :: w6 :: w7 :: v4 :: w9 :: w10 :: w11 :: w12 :: w13 :: rest} = some {s with pc := N 5742, memory := s.memory, stack := N 2048 :: v7 :: w7 :: w0 :: w1 :: w2 :: w3 :: w4 :: w5 :: w6 :: w7 :: v4 :: w9 :: w10 :: w11 :: w12 :: w13 :: rest} := by
    simpa only [b2Model, v5, v6, v7] using
      b2_run ({s with memory := s.memory}) (w7) (v0) (w7) (v0) (w0) (w1) (w2) (w3) (w4) (w5) (w6) (w7) (v4) (w9) (w10) (w11) (w12) (w13) rest hcap hact
  have h3 : runInstructions b3Program {s with pc := N 5742, memory := s.memory, stack := N 2048 :: v7 :: w7 :: w0 :: w1 :: w2 :: w3 :: w4 :: w5 :: w6 :: w7 :: v4 :: w9 :: w10 :: w11 :: w12 :: w13 :: rest} = some {s with pc := N 5752, memory := s.memory, stack := w3 :: v10 :: w7 :: v10 :: v8 :: w0 :: w1 :: w2 :: w3 :: w4 :: w5 :: w6 :: w7 :: v4 :: w9 :: w10 :: w11 :: w12 :: w13 :: rest} := by
    simpa only [b3Model, v8, v9, v10] using
      b3_run ({s with memory := s.memory}) (N 2048) (v7) (w7) (w0) (w1) (w2) (w3) (w4) (w5) (w6) (w7) (v4) (w9) (w10) (w11) (w12) (w13) rest hcap hact
  have h4 : runInstructions b4Program {s with pc := N 5752, memory := s.memory, stack := w3 :: v10 :: w7 :: v10 :: v8 :: w0 :: w1 :: w2 :: w3 :: w4 :: w5 :: w6 :: w7 :: v4 :: w9 :: w10 :: w11 :: w12 :: w13 :: rest} = some {s with pc := N 5760, memory := s.memory, stack := w9 :: v4 :: v13 :: v11 :: v8 :: w0 :: w1 :: w2 :: w3 :: w4 :: w5 :: w6 :: w7 :: v4 :: w9 :: w10 :: w11 :: w12 :: w13 :: rest} := by
    simpa only [b4Model, v11, v12, v13] using
      b4_run ({s with memory := s.memory}) (w3) (v10) (w7) (v10) (v8) (w0) (w1) (w2) (w3) (w4) (w5) (w6) (w7) (v4) (w9) (w10) (w11) (w12) (w13) rest hcap hact
  have h5 : runInstructions b5Program {s with pc := N 5760, memory := s.memory, stack := w9 :: v4 :: v13 :: v11 :: v8 :: w0 :: w1 :: w2 :: w3 :: w4 :: w5 :: w6 :: w7 :: v4 :: w9 :: w10 :: w11 :: w12 :: w13 :: rest} = some {s with pc := N 5768, memory := s.memory, stack := v17 :: v16 :: v15 :: w0 :: w1 :: w2 :: w3 :: w4 :: w5 :: w6 :: w7 :: v4 :: w9 :: w10 :: w11 :: w12 :: w13 :: rest} := by
    simpa only [b5Model, v14, v15, v16, v17] using
      b5_run ({s with memory := s.memory}) (w9) (v4) (v13) (v11) (v8) (w0) (w1) (w2) (w3) (w4) (w5) (w6) (w7) (v4) (w9) (w10) (w11) (w12) (w13) rest hcap hact
  have h6 : runInstructions b6Program {s with pc := N 5768, memory := s.memory, stack := v17 :: v16 :: v15 :: w0 :: w1 :: w2 :: w3 :: w4 :: w5 :: w6 :: w7 :: v4 :: w9 :: w10 :: w11 :: w12 :: w13 :: rest} = some {s with pc := N 5780, memory := s.memory, stack := v20 :: w11 :: w7 :: v18 :: w7 :: w0 :: w1 :: w2 :: w3 :: w4 :: w5 :: w6 :: w7 :: v4 :: w9 :: w10 :: w11 :: w12 :: w13 :: rest} := by
    simpa only [b6Model, v18, v19, v20] using
      b6_run ({s with memory := s.memory}) (v17) (v16) (v15) (w0) (w1) (w2) (w3) (w4) (w5) (w6) (w7) (v4) (w9) (w10) (w11) (w12) (w13) rest hcap hact
  have h7 : runInstructions b7Program {s with pc := N 5780, memory := s.memory, stack := v20 :: w11 :: w7 :: v18 :: w7 :: w0 :: w1 :: w2 :: w3 :: w4 :: w5 :: w6 :: w7 :: v4 :: w9 :: w10 :: w11 :: w12 :: w13 :: rest} = some {s with pc := N 5790, memory := s.memory, stack := N 2048 :: v23 :: w7 :: w0 :: w1 :: w2 :: w3 :: w4 :: w5 :: v21 :: w7 :: v4 :: w9 :: w10 :: w11 :: w12 :: w13 :: rest} := by
    simpa only [b7Model, v21, v22, v23] using
      b7_run ({s with memory := s.memory}) (v20) (w11) (w7) (v18) (w7) (w0) (w1) (w2) (w3) (w4) (w5) (w6) (w7) (v4) (w9) (w10) (w11) (w12) (w13) rest hcap hact
  have h8 : runInstructions b8Program {s with pc := N 5790, memory := s.memory, stack := N 2048 :: v23 :: w7 :: w0 :: w1 :: w2 :: w3 :: w4 :: w5 :: v21 :: w7 :: v4 :: w9 :: w10 :: w11 :: w12 :: w13 :: rest} = some {s with pc := N 5803, memory := s.memory, stack := v27 :: v26 :: v24 :: w0 :: w1 :: w2 :: w3 :: w4 :: w5 :: v21 :: w7 :: v4 :: w9 :: w10 :: w11 :: w12 :: w13 :: rest} := by
    simpa only [b8Model, v24, v25, v26, v27] using
      b8_run ({s with memory := s.memory}) (N 2048) (v23) (w7) (w0) (w1) (w2) (w3) (w4) (w5) (v21) (w7) (v4) (w9) (w10) (w11) (w12) (w13) rest hcap hact
  have h9 : runInstructions b9Program {s with pc := N 5803, memory := s.memory, stack := v27 :: v26 :: v24 :: w0 :: w1 :: w2 :: w3 :: w4 :: w5 :: v21 :: w7 :: v4 :: w9 :: w10 :: w11 :: w12 :: w13 :: rest} = some {s with pc := N 5811, memory := s.memory, stack := v26 :: v28 :: v27 :: v29 :: v24 :: w0 :: w1 :: w2 :: w3 :: w4 :: w5 :: v21 :: w7 :: v4 :: w9 :: w10 :: w11 :: w12 :: w13 :: rest} := by
    simpa only [b9Model, v28, v29] using
      b9_run ({s with memory := s.memory}) (v27) (v26) (v24) (w0) (w1) (w2) (w3) (w4) (w5) (v21) (w7) (v4) (w9) (w10) (w11) (w12) (w13) rest hcap hact
  have h10 : runInstructions b10Program {s with pc := N 5811, memory := s.memory, stack := v26 :: v28 :: v27 :: v29 :: v24 :: w0 :: w1 :: w2 :: w3 :: w4 :: w5 :: v21 :: w7 :: v4 :: w9 :: w10 :: w11 :: w12 :: w13 :: rest} = some {s with pc := N 5819, memory := s.memory, stack := w9 :: v21 :: v33 :: v29 :: v24 :: w0 :: w1 :: w2 :: w3 :: w4 :: w5 :: v21 :: w7 :: v4 :: w9 :: w10 :: w11 :: w12 :: w13 :: rest} := by
    simpa only [b10Model, v30, v31, v32, v33] using
      b10_run ({s with memory := s.memory}) (v26) (v28) (v27) (v29) (v24) (w0) (w1) (w2) (w3) (w4) (w5) (v21) (w7) (v4) (w9) (w10) (w11) (w12) (w13) rest hcap hact
  have h11 : runInstructions b11Program {s with pc := N 5819, memory := s.memory, stack := w9 :: v21 :: v33 :: v29 :: v24 :: w0 :: w1 :: w2 :: w3 :: w4 :: w5 :: v21 :: w7 :: v4 :: w9 :: w10 :: w11 :: w12 :: w13 :: rest} = some {s with pc := N 5827, memory := s.memory, stack := v37 :: v36 :: v35 :: w0 :: w1 :: w2 :: w3 :: w4 :: w5 :: v21 :: w7 :: v4 :: w9 :: w10 :: w11 :: w12 :: w13 :: rest} := by
    simpa only [b11Model, v34, v35, v36, v37] using
      b11_run ({s with memory := s.memory}) (w9) (v21) (v33) (v29) (v24) (w0) (w1) (w2) (w3) (w4) (w5) (v21) (w7) (v4) (w9) (w10) (w11) (w12) (w13) rest hcap hact
  have h12 : runInstructions b12Program {s with pc := N 5827, memory := s.memory, stack := v37 :: v36 :: v35 :: w0 :: w1 :: w2 :: w3 :: w4 :: w5 :: v21 :: w7 :: v4 :: w9 :: w10 :: w11 :: w12 :: w13 :: rest} = some {s with pc := N 5835, memory := s.memory, stack := w9 :: w7 :: v40 :: v35 :: w0 :: w1 :: w2 :: w3 :: w4 :: w5 :: v21 :: w7 :: v4 :: w9 :: w10 :: w11 :: w12 :: w13 :: rest} := by
    simpa only [b12Model, v38, v39, v40] using
      b12_run ({s with memory := s.memory}) (v37) (v36) (v35) (w0) (w1) (w2) (w3) (w4) (w5) (v21) (w7) (v4) (w9) (w10) (w11) (w12) (w13) rest hcap hact
  have h13 : runInstructions b13Program {s with pc := N 5835, memory := s.memory, stack := w9 :: w7 :: v40 :: v35 :: w0 :: w1 :: w2 :: w3 :: w4 :: w5 :: v21 :: w7 :: v4 :: w9 :: w10 :: w11 :: w12 :: w13 :: rest} = some {s with pc := N 5840, memory := s.memory, stack := w11 :: w7 :: v42 :: v35 :: w0 :: w1 :: w2 :: w3 :: w4 :: w5 :: v21 :: w7 :: v4 :: w9 :: w10 :: w11 :: w12 :: w13 :: rest} := by
    simpa only [b13Model, v41, v42] using
      b13_run ({s with memory := s.memory}) (w9) (w7) (v40) (v35) (w0) (w1) (w2) (w3) (w4) (w5) (v21) (w7) (v4) (w9) (w10) (w11) (w12) (w13) rest hcap hact
  have h14 : runInstructions b14Program {s with pc := N 5840, memory := s.memory, stack := w11 :: w7 :: v42 :: v35 :: w0 :: w1 :: w2 :: w3 :: w4 :: w5 :: v21 :: w7 :: v4 :: w9 :: w10 :: w11 :: w12 :: w13 :: rest} = some {s with pc := N 5850, memory := s.memory, stack := v45 :: v45 :: w11 :: w7 :: v42 :: w7 :: w0 :: w1 :: w2 :: w3 :: w4 :: w5 :: v21 :: w7 :: v4 :: w9 :: w10 :: w11 :: w12 :: w13 :: rest} := by
    simpa only [b14Model, v43, v44, v45] using
      b14_run ({s with memory := s.memory}) (w11) (w7) (v42) (v35) (w0) (w1) (w2) (w3) (w4) (w5) (v21) (w7) (v4) (w9) (w10) (w11) (w12) (w13) rest hcap hact
  have h15 : runInstructions b15Program {s with pc := N 5850, memory := s.memory, stack := v45 :: v45 :: w11 :: w7 :: v42 :: w7 :: w0 :: w1 :: w2 :: w3 :: w4 :: w5 :: v21 :: w7 :: v4 :: w9 :: w10 :: w11 :: w12 :: w13 :: rest} = some {s with pc := N 5859, memory := v46, stack := v49 :: w0 :: w1 :: w2 :: w3 :: w4 :: w5 :: v21 :: w7 :: v4 :: w9 :: w10 :: w11 :: w12 :: w13 :: rest} := by
    simpa only [b15Model, v46, v47, v48, v49] using
      b15_run ({s with memory := s.memory}) (v45) (v45) (w11) (w7) (v42) (w7) (w0) (w1) (w2) (w3) (w4) (w5) (v21) (w7) (v4) (w9) (w10) (w11) (w12) (w13) rest hcap hact
  simpa only [candidateBoundaryModel, program0, prefix1, List.append_assoc] using (runInstructions_append_some _ _ _ _ _ h0 (runInstructions_append_some _ _ _ _ _ h1 (runInstructions_append_some _ _ _ _ _ h2 (runInstructions_append_some _ _ _ _ _ h3 (runInstructions_append_some _ _ _ _ _ h4 (runInstructions_append_some _ _ _ _ _ h5 (runInstructions_append_some _ _ _ _ _ h6 (runInstructions_append_some _ _ _ _ _ h7 (runInstructions_append_some _ _ _ _ _ h8 (runInstructions_append_some _ _ _ _ _ h9 (runInstructions_append_some _ _ _ _ _ h10 (runInstructions_append_some _ _ _ _ _ h11 (runInstructions_append_some _ _ _ _ _ h12 (runInstructions_append_some _ _ _ _ _ h13 (runInstructions_append_some _ _ _ _ _ h14 h15)))))))))))))))

def parentBoundaryModel (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 : W) (rest : List W) : State :=
  let v0 : W := MachineState.readWord (s.memory) 768
  let v1 : W := v0 * v0
  let v2 : W := MachineState.readWord (s.memory) 2720
  let v3 : W := v2 * v1
  let v4 : W := UInt256.land w10 v3
  let v5 : W := UInt256.mulMod v0 v0 w7
  let v6 : W := UInt256.mulMod w11 v4 w7
  let v7 : W := v6 + v5
  let v8 : W := UInt256.mulMod (N 2048) v7 w7
  let v9 : W := MachineState.readWord (s.memory) 768
  let v10 : W := v9 + v9
  let v11 : W := UInt256.mulMod w3 v10 w7
  let v12 : W := w3 * v10
  let v13 : W := v8 + v12
  let v14 : W := w9 * v4
  let v15 : W := v14 + v13
  let v16 : W := v8 + v11
  let v17 : W := UInt256.mulMod v4 w9 w7
  let v18 : W := v17 + v16
  let v19 : W := MachineState.readWord (s.memory) 2720
  let v20 : W := v15 * v19
  let v21 : W := UInt256.land w10 v20
  let v22 : W := UInt256.mulMod v21 w11 w7
  let v23 : W := v22 + v18
  let v24 : W := UInt256.mulMod (N 2048) v23 w7
  let v25 : W := MachineState.readWord (s.memory) 768
  let v26 : W := v4 * w0
  let v27 : W := w3 * w3
  let v28 : W := UInt256.mulMod w4 v25 w7
  let v29 : W := v28 + v28
  let v30 : W := w4 * v25
  let v31 : W := v30 + v30
  let v32 : W := v24 + v31
  let v33 : W := v32 + v27
  let v34 : W := v33 + v26
  let v35 : W := w9 * v21
  let v36 : W := v35 + v34
  let v37 : W := v24 + v29
  let v38 : W := UInt256.mulMod w3 w3 w7
  let v39 : W := v38 + v37
  let v40 : W := UInt256.mulMod v4 w0 w7
  let v41 : W := v40 + v39
  let v42 : W := UInt256.mulMod v21 w9 w7
  let v43 : W := v42 + v41
  let v44 : W := MachineState.readWord (s.memory) 2720
  let v45 : W := v36 * v44
  let v46 : W := UInt256.land w10 v45
  let v47 : ByteArray := MachineState.writeBytes s.memory (Data.Bytes.natToBytesPadded v46.toNat 32) 192
  let v48 : W := UInt256.mulMod v46 w11 w7
  let v49 : W := v48 + v43
  let v50 : W := UInt256.mulMod (N 2048) v49 w7
  {s with pc := N 5859, memory := v47, stack := v50 :: w0 :: w1 :: w2 :: w3 :: w4 :: w5 :: v21 :: w7 :: v4 :: w9 :: w10 :: w11 :: w12 :: w13 :: rest}

def t0Program : List Instr :=
  [.push 1 32,
   .op .MLOAD,
   .op (.Dup ⟨9, by decide⟩),
   .push 2 768,
   .op .MLOAD,
   .op (.Dup ⟨0, by decide⟩),
   .op (.Dup ⟨3, by decide⟩),
   .op .MUL]

def t0Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 : W) (rest : List W) : State :=
  let v0 : W := MachineState.readWord (s.memory) 32
  let v1 : W := MachineState.readWord (s.memory) 768
  let v2 : W := v0 * v1
  {s with pc := N 5870, memory := s.memory, stack := v2 :: v1 :: x8 :: v0 :: x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: rest}

theorem t0_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions t0Program {s with pc := N 5859, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: rest} =
      some (t0Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 rest) := by
  have capacity (j : Nat) (hj : j ≤ 32) : rest.length+j < 1024 := by omega
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have ha32 : (32 : W).toNat = 32 := rfl
  have hf32 := Monpro.activeWords_fix s 32 32 (by decide) (by norm_num) hact
  have ha768 : (768 : W).toNat = 768 := rfl
  have hf768 := Monpro.activeWords_fix s 768 32 (by decide) (by norm_num) hact
  simp [hz, hzn, capacity,t0Program, t0Model, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, Challenge.EvmProof.Word.literal_eq_ofNat, ha32, ha768, hf32, hf768]

def t1Program : List Instr :=
  [.op (.Dup ⟨9, by decide⟩),
   .op (.Dup ⟨9, by decide⟩),
   .op .MUL,
   .op .ADD,
   .op (.Dup ⟨0, by decide⟩),
   .op .ADD,
   .op (.Swap ⟨2, by decide⟩),
   .op .MULMOD]

def t1Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 : W) (rest : List W) : State :=
  let v0 : W := x8 * x9
  let v1 : W := v0 + x0
  let v2 : W := v1 + v1
  let v3 : W := UInt256.mulMod x3 x1 x2
  {s with pc := N 5878, memory := s.memory, stack := v3 :: v2 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: x18 :: rest}

theorem t1_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions t1Program {s with pc := N 5870, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: x18 :: rest} =
      some (t1Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 rest) := by
  have capacity (j : Nat) (hj : j ≤ 32) : rest.length+j < 1024 := by omega
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  simp [hz, hzn, capacity,t1Program, t1Model, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, Challenge.EvmProof.Word.literal_eq_ofNat, ]

def t2Program : List Instr :=
  [.op (.Dup ⟨10, by decide⟩),
   .op (.Dup ⟨8, by decide⟩),
   .op (.Dup ⟨8, by decide⟩),
   .op .MULMOD,
   .op .ADD,
   .op (.Dup ⟨0, by decide⟩),
   .op .ADD,
   .op (.Dup ⟨2, by decide⟩)]

def t2Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 : W) (rest : List W) : State :=
  let v0 : W := UInt256.mulMod x6 x7 x10
  let v1 : W := v0 + x0
  let v2 : W := v1 + v1
  {s with pc := N 5886, memory := s.memory, stack := x2 :: v2 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: rest}

theorem t2_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions t2Program {s with pc := N 5878, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: rest} =
      some (t2Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 rest) := by
  have capacity (j : Nat) (hj : j ≤ 32) : rest.length+j < 1024 := by omega
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  simp [hz, hzn, capacity,t2Program, t2Model, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, Challenge.EvmProof.Word.literal_eq_ofNat, ]

def t3Program : List Instr :=
  [.op .ADD,
   .op (.Swap ⟨1, by decide⟩),
   .op .ADD,
   .op (.Dup ⟨14, by decide⟩),
   .op (.Dup ⟨11, by decide⟩),
   .op .MUL,
   .op .ADD,
   .op (.Dup ⟨2, by decide⟩)]

def t3Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 : W) (rest : List W) : State :=
  let v0 : W := x0 + x1
  let v1 : W := x3 + x2
  let v2 : W := x12 * x16
  let v3 : W := v2 + v1
  {s with pc := N 5894, memory := s.memory, stack := x4 :: v3 :: v0 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: rest}

theorem t3_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions t3Program {s with pc := N 5886, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: rest} =
      some (t3Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 rest) := by
  have capacity (j : Nat) (hj : j ≤ 32) : rest.length+j < 1024 := by omega
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  simp [hz, hzn, capacity,t3Program, t3Model, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, Challenge.EvmProof.Word.literal_eq_ofNat, ]

def t4Program : List Instr :=
  [.op (.Dup ⟨9, by decide⟩),
   .op .MUL,
   .op .ADD,
   .op (.Dup ⟨11, by decide⟩),
   .push 1 192,
   .op .MLOAD,
   .op .MUL,
   .op .ADD]

def t4Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 : W) (rest : List W) : State :=
  let v0 : W := x9 * x0
  let v1 : W := v0 + x1
  let v2 : W := MachineState.readWord (s.memory) 192
  let v3 : W := v2 * x12
  let v4 : W := v3 + v1
  {s with pc := N 5903, memory := s.memory, stack := v4 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: rest}

theorem t4_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions t4Program {s with pc := N 5894, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: rest} =
      some (t4Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 rest) := by
  have capacity (j : Nat) (hj : j ≤ 32) : rest.length+j < 1024 := by omega
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have ha192 : (192 : W).toNat = 192 := rfl
  have hf192 := Monpro.activeWords_fix s 192 32 (by decide) (by norm_num) hact
  simp [hz, hzn, capacity,t4Program, t4Model, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, Challenge.EvmProof.Word.literal_eq_ofNat, ha192, hf192]

def t5Program : List Instr :=
  [.op (.Swap ⟨0, by decide⟩),
   .op (.Dup ⟨9, by decide⟩),
   .op (.Dup ⟨15, by decide⟩),
   .op (.Dup ⟨12, by decide⟩),
   .op .MULMOD,
   .op .ADD,
   .op (.Dup ⟨9, by decide⟩),
   .op (.Dup ⟨3, by decide⟩)]

def t5Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 : W) (rest : List W) : State :=
  let v0 : W := UInt256.mulMod x10 x14 x9
  let v1 : W := v0 + x1
  {s with pc := N 5911, memory := s.memory, stack := x2 :: x9 :: v1 :: x0 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: rest}

theorem t5_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions t5Program {s with pc := N 5903, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: rest} =
      some (t5Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 rest) := by
  have capacity (j : Nat) (hj : j ≤ 32) : rest.length+j < 1024 := by omega
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  simp [hz, hzn, capacity,t5Program, t5Model, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, Challenge.EvmProof.Word.literal_eq_ofNat, ]

def t6Program : List Instr :=
  [.op (.Dup ⟨10, by decide⟩),
   .op .MULMOD,
   .op .ADD,
   .op (.Dup ⟨9, by decide⟩),
   .op (.Dup ⟨12, by decide⟩),
   .push 1 192,
   .op .MLOAD,
   .op .MULMOD]

def t6Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 : W) (rest : List W) : State :=
  let v0 : W := UInt256.mulMod x10 x0 x1
  let v1 : W := v0 + x2
  let v2 : W := MachineState.readWord (s.memory) 192
  let v3 : W := UInt256.mulMod v2 x13 x11
  {s with pc := N 5920, memory := s.memory, stack := v3 :: v1 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: rest}

theorem t6_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions t6Program {s with pc := N 5911, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: rest} =
      some (t6Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 rest) := by
  have capacity (j : Nat) (hj : j ≤ 32) : rest.length+j < 1024 := by omega
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have ha192 : (192 : W).toNat = 192 := rfl
  have hf192 := Monpro.activeWords_fix s 192 32 (by decide) (by norm_num) hact
  simp [hz, hzn, capacity,t6Program, t6Model, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, Challenge.EvmProof.Word.literal_eq_ofNat, ha192, hf192]

def t7Program : List Instr :=
  [.op .ADD,
   .op (.Dup ⟨9, by decide⟩),
   .op (.Dup ⟨14, by decide⟩),
   .push 2 2720,
   .op .MLOAD,
   .op (.Dup ⟨2, by decide⟩),
   .op (.Swap ⟨4, by decide⟩),
   .op .MUL]

def t7Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 : W) (rest : List W) : State :=
  let v0 : W := x0 + x1
  let v1 : W := MachineState.readWord (s.memory) 2720
  let v2 : W := x2 * v1
  {s with pc := N 5930, memory := s.memory, stack := v2 :: x14 :: x10 :: v0 :: x10 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: rest}

theorem t7_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions t7Program {s with pc := N 5920, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: rest} =
      some (t7Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 rest) := by
  have capacity (j : Nat) (hj : j ≤ 32) : rest.length+j < 1024 := by omega
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have ha2720 : (2720 : W).toNat = 2720 := rfl
  have hf2720 := Monpro.activeWords_fix s 2720 32 (by decide) (by norm_num) hact
  simp [hz, hzn, capacity,t7Program, t7Model, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, Challenge.EvmProof.Word.literal_eq_ofNat, ha2720, hf2720]

def t8Program : List Instr :=
  [.op (.Dup ⟨15, by decide⟩),
   .op .AND,
   .op (.Dup ⟨0, by decide⟩),
   .push 0 0,
   .op .MSTORE,
   .op .MULMOD,
   .op .ADD,
   .push 2 2048]

def t8Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 : W) (rest : List W) : State :=
  let v0 : W := UInt256.land x15 x0
  let v1 : ByteArray := MachineState.writeBytes s.memory (Data.Bytes.natToBytesPadded v0.toNat 32) 0
  let v2 : W := UInt256.mulMod v0 x1 x2
  let v3 : W := v2 + x3
  {s with pc := N 5940, memory := v1, stack := (N 2048) :: v3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: x18 :: rest}

theorem t8_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions t8Program {s with pc := N 5930, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: x18 :: rest} =
      some (t8Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 rest) := by
  have capacity (j : Nat) (hj : j ≤ 32) : rest.length+j < 1024 := by omega
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have ha0 : (0 : W).toNat = 0 := rfl
  have hf0 := Monpro.activeWords_fix s 0 32 (by decide) (by norm_num) hact
  simp [hz, hzn, capacity,t8Program, t8Model, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, Challenge.EvmProof.Word.literal_eq_ofNat, hz, hzn, ha0, hf0]

def t9Program : List Instr :=
  [.op .MULMOD,
   .push 1 64,
   .op .MLOAD,
   .op (.Dup ⟨9, by decide⟩),
   .push 2 768,
   .op .MLOAD,
   .op (.Dup ⟨0, by decide⟩),
   .op (.Dup ⟨3, by decide⟩)]

def t9Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 : W) (rest : List W) : State :=
  let v0 : W := UInt256.mulMod x0 x1 x2
  let v1 : W := MachineState.readWord (s.memory) 64
  let v2 : W := MachineState.readWord (s.memory) 768
  {s with pc := N 5951, memory := s.memory, stack := v1 :: v2 :: v2 :: x10 :: v1 :: v0 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: rest}

theorem t9_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions t9Program {s with pc := N 5940, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: rest} =
      some (t9Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 rest) := by
  have capacity (j : Nat) (hj : j ≤ 32) : rest.length+j < 1024 := by omega
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have ha64 : (64 : W).toNat = 64 := rfl
  have hf64 := Monpro.activeWords_fix s 64 32 (by decide) (by norm_num) hact
  have ha768 : (768 : W).toNat = 768 := rfl
  have hf768 := Monpro.activeWords_fix s 768 32 (by decide) (by norm_num) hact
  simp [hz, hzn, capacity,t9Program, t9Model, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, Challenge.EvmProof.Word.literal_eq_ofNat, ha64, ha768, hf64, hf768]

def t10Program : List Instr :=
  [.op .MUL,
   .push 1 32,
   .op .MLOAD,
   .op (.Dup ⟨9, by decide⟩),
   .op .MUL,
   .op .ADD,
   .op (.Dup ⟨0, by decide⟩),
   .op .ADD]

def t10Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 : W) (rest : List W) : State :=
  let v0 : W := x0 * x1
  let v1 : W := MachineState.readWord (s.memory) 32
  let v2 : W := x9 * v1
  let v3 : W := v2 + v0
  let v4 : W := v3 + v3
  {s with pc := N 5960, memory := s.memory, stack := v4 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: x18 :: x19 :: rest}

theorem t10_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions t10Program {s with pc := N 5951, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: x18 :: x19 :: rest} =
      some (t10Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 rest) := by
  have capacity (j : Nat) (hj : j ≤ 32) : rest.length+j < 1024 := by omega
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have ha32 : (32 : W).toNat = 32 := rfl
  have hf32 := Monpro.activeWords_fix s 32 32 (by decide) (by norm_num) hact
  simp [hz, hzn, capacity,t10Program, t10Model, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, Challenge.EvmProof.Word.literal_eq_ofNat, ha32, hf32]

def t11Program : List Instr :=
  [.op (.Swap ⟨2, by decide⟩),
   .op .MULMOD,
   .op (.Dup ⟨10, by decide⟩),
   .push 1 32,
   .op .MLOAD,
   .op (.Dup ⟨8, by decide⟩),
   .op .MULMOD]

def t11Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 : W) (rest : List W) : State :=
  let v0 : W := UInt256.mulMod x3 x1 x2
  let v1 : W := MachineState.readWord (s.memory) 32
  let v2 : W := UInt256.mulMod x8 v1 x12
  {s with pc := N 5968, memory := s.memory, stack := v2 :: v0 :: x0 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: x18 :: rest}

theorem t11_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions t11Program {s with pc := N 5960, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: x18 :: rest} =
      some (t11Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 rest) := by
  have capacity (j : Nat) (hj : j ≤ 32) : rest.length+j < 1024 := by omega
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have ha32 : (32 : W).toNat = 32 := rfl
  have hf32 := Monpro.activeWords_fix s 32 32 (by decide) (by norm_num) hact
  simp [hz, hzn, capacity,t11Program, t11Model, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, Challenge.EvmProof.Word.literal_eq_ofNat, ha32, hf32]

def tail1 : List Instr := t0Program ++ (t1Program ++ (t2Program ++ (t3Program ++ (t4Program ++ (t5Program ++ (t6Program ++ (t7Program ++ (t8Program ++ (t9Program ++ (t10Program ++ (t11Program)))))))))))

def tailModel (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 : W) (rest : List W) : State :=
  let v0 : W := MachineState.readWord (s.memory) 32
  let v1 : W := MachineState.readWord (s.memory) 768
  let v2 : W := v0 * v1
  let v3 : W := x4 * x5
  let v4 : W := v3 + v2
  let v5 : W := v4 + v4
  let v6 : W := UInt256.mulMod v0 v1 x8
  let v7 : W := UInt256.mulMod x4 x5 x8
  let v8 : W := v7 + v6
  let v9 : W := v8 + v8
  let v10 : W := x0 + v9
  let v11 : W := x0 + v5
  let v12 : W := x9 * x13
  let v13 : W := v12 + v11
  let v14 : W := x7 * x1
  let v15 : W := v14 + v13
  let v16 : W := MachineState.readWord (s.memory) 192
  let v17 : W := v16 * x10
  let v18 : W := v17 + v15
  let v19 : W := UInt256.mulMod x9 x13 x8
  let v20 : W := v19 + v10
  let v21 : W := UInt256.mulMod x7 x1 x8
  let v22 : W := v21 + v20
  let v23 : W := MachineState.readWord (s.memory) 192
  let v24 : W := UInt256.mulMod v23 x10 x8
  let v25 : W := v24 + v22
  let v26 : W := MachineState.readWord (s.memory) 2720
  let v27 : W := v18 * v26
  let v28 : W := UInt256.land x11 v27
  let v29 : ByteArray := MachineState.writeBytes s.memory (Data.Bytes.natToBytesPadded v28.toNat 32) 0
  let v30 : W := UInt256.mulMod v28 x12 x8
  let v31 : W := v30 + v25
  let v32 : W := UInt256.mulMod (N 2048) v31 x8
  let v33 : W := MachineState.readWord (v29) 64
  let v34 : W := MachineState.readWord (v29) 768
  let v35 : W := v33 * v34
  let v36 : W := MachineState.readWord (v29) 32
  let v37 : W := x4 * v36
  let v38 : W := v37 + v35
  let v39 : W := v38 + v38
  let v40 : W := UInt256.mulMod v33 v34 x8
  let v41 : W := MachineState.readWord (v29) 32
  let v42 : W := UInt256.mulMod x4 v41 x8
  {s with pc := N 5968, memory := v29, stack := v42 :: v40 :: v39 :: v32 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: rest}

theorem t_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions (tail1) {s with pc := N 5859, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: rest} =
      some (tailModel s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 rest) := by
  let v0 : W := MachineState.readWord (s.memory) 32
  let v1 : W := MachineState.readWord (s.memory) 768
  let v2 : W := v0 * v1
  let v3 : W := x4 * x5
  let v4 : W := v3 + v2
  let v5 : W := v4 + v4
  let v6 : W := UInt256.mulMod v0 v1 x8
  let v7 : W := UInt256.mulMod x4 x5 x8
  let v8 : W := v7 + v6
  let v9 : W := v8 + v8
  let v10 : W := x0 + v9
  let v11 : W := x0 + v5
  let v12 : W := x9 * x13
  let v13 : W := v12 + v11
  let v14 : W := x7 * x1
  let v15 : W := v14 + v13
  let v16 : W := MachineState.readWord (s.memory) 192
  let v17 : W := v16 * x10
  let v18 : W := v17 + v15
  let v19 : W := UInt256.mulMod x9 x13 x8
  let v20 : W := v19 + v10
  let v21 : W := UInt256.mulMod x7 x1 x8
  let v22 : W := v21 + v20
  let v23 : W := MachineState.readWord (s.memory) 192
  let v24 : W := UInt256.mulMod v23 x10 x8
  let v25 : W := v24 + v22
  let v26 : W := MachineState.readWord (s.memory) 2720
  let v27 : W := v18 * v26
  let v28 : W := UInt256.land x11 v27
  let v29 : ByteArray := MachineState.writeBytes s.memory (Data.Bytes.natToBytesPadded v28.toNat 32) 0
  let v30 : W := UInt256.mulMod v28 x12 x8
  let v31 : W := v30 + v25
  let v32 : W := UInt256.mulMod (N 2048) v31 x8
  let v33 : W := MachineState.readWord (v29) 64
  let v34 : W := MachineState.readWord (v29) 768
  let v35 : W := v33 * v34
  let v36 : W := MachineState.readWord (v29) 32
  let v37 : W := x4 * v36
  let v38 : W := v37 + v35
  let v39 : W := v38 + v38
  let v40 : W := UInt256.mulMod v33 v34 x8
  let v41 : W := MachineState.readWord (v29) 32
  let v42 : W := UInt256.mulMod x4 v41 x8
  have h0 : runInstructions t0Program {s with pc := N 5859, memory := s.memory, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: rest} = some {s with pc := N 5870, memory := s.memory, stack := v2 :: v1 :: x8 :: v0 :: x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: rest} := by
    simpa only [t0Model, v0, v1, v2] using
      t0_run ({s with memory := s.memory}) (x0) (x1) (x2) (x3) (x4) (x5) (x6) (x7) (x8) (x9) (x10) (x11) (x12) (x13) (x14) rest hcap hact
  have h1 : runInstructions t1Program {s with pc := N 5870, memory := s.memory, stack := v2 :: v1 :: x8 :: v0 :: x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: rest} = some {s with pc := N 5878, memory := s.memory, stack := v6 :: v5 :: x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: rest} := by
    simpa only [t1Model, v3, v4, v5, v6] using
      t1_run ({s with memory := s.memory}) (v2) (v1) (x8) (v0) (x0) (x1) (x2) (x3) (x4) (x5) (x6) (x7) (x8) (x9) (x10) (x11) (x12) (x13) (x14) rest hcap hact
  have h2 : runInstructions t2Program {s with pc := N 5878, memory := s.memory, stack := v6 :: v5 :: x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: rest} = some {s with pc := N 5886, memory := s.memory, stack := x0 :: v9 :: v5 :: x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: rest} := by
    simpa only [t2Model, v7, v8, v9] using
      t2_run ({s with memory := s.memory}) (v6) (v5) (x0) (x1) (x2) (x3) (x4) (x5) (x6) (x7) (x8) (x9) (x10) (x11) (x12) (x13) (x14) rest hcap hact
  have h3 : runInstructions t3Program {s with pc := N 5886, memory := s.memory, stack := x0 :: v9 :: v5 :: x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: rest} = some {s with pc := N 5894, memory := s.memory, stack := x1 :: v13 :: v10 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: rest} := by
    simpa only [t3Model, v10, v11, v12, v13] using
      t3_run ({s with memory := s.memory}) (x0) (v9) (v5) (x0) (x1) (x2) (x3) (x4) (x5) (x6) (x7) (x8) (x9) (x10) (x11) (x12) (x13) (x14) rest hcap hact
  have h4 : runInstructions t4Program {s with pc := N 5894, memory := s.memory, stack := x1 :: v13 :: v10 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: rest} = some {s with pc := N 5903, memory := s.memory, stack := v18 :: v10 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: rest} := by
    simpa only [t4Model, v14, v15, v16, v17, v18] using
      t4_run ({s with memory := s.memory}) (x1) (v13) (v10) (x1) (x2) (x3) (x4) (x5) (x6) (x7) (x8) (x9) (x10) (x11) (x12) (x13) (x14) rest hcap hact
  have h5 : runInstructions t5Program {s with pc := N 5903, memory := s.memory, stack := v18 :: v10 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: rest} = some {s with pc := N 5911, memory := s.memory, stack := x1 :: x8 :: v20 :: v18 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: rest} := by
    simpa only [t5Model, v19, v20] using
      t5_run ({s with memory := s.memory}) (v18) (v10) (x1) (x2) (x3) (x4) (x5) (x6) (x7) (x8) (x9) (x10) (x11) (x12) (x13) (x14) rest hcap hact
  have h6 : runInstructions t6Program {s with pc := N 5911, memory := s.memory, stack := x1 :: x8 :: v20 :: v18 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: rest} = some {s with pc := N 5920, memory := s.memory, stack := v24 :: v22 :: v18 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: rest} := by
    simpa only [t6Model, v21, v22, v23, v24] using
      t6_run ({s with memory := s.memory}) (x1) (x8) (v20) (v18) (x1) (x2) (x3) (x4) (x5) (x6) (x7) (x8) (x9) (x10) (x11) (x12) (x13) (x14) rest hcap hact
  have h7 : runInstructions t7Program {s with pc := N 5920, memory := s.memory, stack := v24 :: v22 :: v18 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: rest} = some {s with pc := N 5930, memory := s.memory, stack := v27 :: x12 :: x8 :: v25 :: x8 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: rest} := by
    simpa only [t7Model, v25, v26, v27] using
      t7_run ({s with memory := s.memory}) (v24) (v22) (v18) (x1) (x2) (x3) (x4) (x5) (x6) (x7) (x8) (x9) (x10) (x11) (x12) (x13) (x14) rest hcap hact
  have h8 : runInstructions t8Program {s with pc := N 5930, memory := s.memory, stack := v27 :: x12 :: x8 :: v25 :: x8 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: rest} = some {s with pc := N 5940, memory := v29, stack := N 2048 :: v31 :: x8 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: rest} := by
    simpa only [t8Model, v28, v29, v30, v31] using
      t8_run ({s with memory := s.memory}) (v27) (x12) (x8) (v25) (x8) (x1) (x2) (x3) (x4) (x5) (x6) (x7) (x8) (x9) (x10) (x11) (x12) (x13) (x14) rest hcap hact
  have h9 : runInstructions t9Program {s with pc := N 5940, memory := v29, stack := N 2048 :: v31 :: x8 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: rest} = some {s with pc := N 5951, memory := v29, stack := v33 :: v34 :: v34 :: x8 :: v33 :: v32 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: rest} := by
    simpa only [t9Model, v32, v33, v34] using
      t9_run ({s with memory := v29}) (N 2048) (v31) (x8) (x1) (x2) (x3) (x4) (x5) (x6) (x7) (x8) (x9) (x10) (x11) (x12) (x13) (x14) rest hcap hact
  have h10 : runInstructions t10Program {s with pc := N 5951, memory := v29, stack := v33 :: v34 :: v34 :: x8 :: v33 :: v32 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: rest} = some {s with pc := N 5960, memory := v29, stack := v39 :: v34 :: x8 :: v33 :: v32 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: rest} := by
    simpa only [t10Model, v35, v36, v37, v38, v39] using
      t10_run ({s with memory := v29}) (v33) (v34) (v34) (x8) (v33) (v32) (x1) (x2) (x3) (x4) (x5) (x6) (x7) (x8) (x9) (x10) (x11) (x12) (x13) (x14) rest hcap hact
  have h11 : runInstructions t11Program {s with pc := N 5960, memory := v29, stack := v39 :: v34 :: x8 :: v33 :: v32 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: rest} = some {s with pc := N 5968, memory := v29, stack := v42 :: v40 :: v39 :: v32 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: rest} := by
    simpa only [t11Model, v40, v41, v42] using
      t11_run ({s with memory := v29}) (v39) (v34) (x8) (v33) (v32) (x1) (x2) (x3) (x4) (x5) (x6) (x7) (x8) (x9) (x10) (x11) (x12) (x13) (x14) rest hcap hact
  simpa only [tailModel, tail1, List.append_assoc] using (runInstructions_append_some _ _ _ _ _ h0 (runInstructions_append_some _ _ _ _ _ h1 (runInstructions_append_some _ _ _ _ _ h2 (runInstructions_append_some _ _ _ _ _ h3 (runInstructions_append_some _ _ _ _ _ h4 (runInstructions_append_some _ _ _ _ _ h5 (runInstructions_append_some _ _ _ _ _ h6 (runInstructions_append_some _ _ _ _ _ h7 (runInstructions_append_some _ _ _ _ _ h8 (runInstructions_append_some _ _ _ _ _ h9 (runInstructions_append_some _ _ _ _ _ h10 h11)))))))))))

/-- Exact candidate slice 5840..5968. -/
def program1 : List Instr := prefix1 ++ tail1

/-- Exact candidate slice 5712..5968. -/
def mergedProgram : List Instr := program0 ++ program1

/-- Promoted-parent two-column model, generated with the same memory-aware
executor as the candidate; all reads after writes use the updated memory. -/
def mergedModel (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 : W) (rest : List W) : State :=
  let v0 : W := MachineState.readWord (s.memory) 768
  let v1 : W := v0 * v0
  let v2 : W := MachineState.readWord (s.memory) 2720
  let v3 : W := v2 * v1
  let v4 : W := UInt256.land w10 v3
  let v5 : W := UInt256.mulMod v0 v0 w7
  let v6 : W := UInt256.mulMod w11 v4 w7
  let v7 : W := v6 + v5
  let v8 : W := UInt256.mulMod (N 2048) v7 w7
  let v9 : W := MachineState.readWord (s.memory) 768
  let v10 : W := v9 + v9
  let v11 : W := UInt256.mulMod w3 v10 w7
  let v12 : W := w3 * v10
  let v13 : W := v8 + v12
  let v14 : W := w9 * v4
  let v15 : W := v14 + v13
  let v16 : W := v8 + v11
  let v17 : W := UInt256.mulMod v4 w9 w7
  let v18 : W := v17 + v16
  let v19 : W := MachineState.readWord (s.memory) 2720
  let v20 : W := v15 * v19
  let v21 : W := UInt256.land w10 v20
  let v22 : W := UInt256.mulMod v21 w11 w7
  let v23 : W := v22 + v18
  let v24 : W := UInt256.mulMod (N 2048) v23 w7
  let v25 : W := MachineState.readWord (s.memory) 768
  let v26 : W := v4 * w0
  let v27 : W := w3 * w3
  let v28 : W := UInt256.mulMod w4 v25 w7
  let v29 : W := v28 + v28
  let v30 : W := w4 * v25
  let v31 : W := v30 + v30
  let v32 : W := v24 + v31
  let v33 : W := v32 + v27
  let v34 : W := v33 + v26
  let v35 : W := w9 * v21
  let v36 : W := v35 + v34
  let v37 : W := v24 + v29
  let v38 : W := UInt256.mulMod w3 w3 w7
  let v39 : W := v38 + v37
  let v40 : W := UInt256.mulMod v4 w0 w7
  let v41 : W := v40 + v39
  let v42 : W := UInt256.mulMod v21 w9 w7
  let v43 : W := v42 + v41
  let v44 : W := MachineState.readWord (s.memory) 2720
  let v45 : W := v36 * v44
  let v46 : W := UInt256.land w10 v45
  let v47 : ByteArray := MachineState.writeBytes s.memory (Data.Bytes.natToBytesPadded v46.toNat 32) 192
  let v48 : W := UInt256.mulMod v46 w11 w7
  let v49 : W := v48 + v43
  let v50 : W := UInt256.mulMod (N 2048) v49 w7
  let v51 : W := MachineState.readWord (v47) 32
  let v52 : W := MachineState.readWord (v47) 768
  let v53 : W := v51 * v52
  let v54 : W := w3 * w4
  let v55 : W := v54 + v53
  let v56 : W := v55 + v55
  let v57 : W := UInt256.mulMod v51 v52 w7
  let v58 : W := UInt256.mulMod w3 w4 w7
  let v59 : W := v58 + v57
  let v60 : W := v59 + v59
  let v61 : W := v50 + v60
  let v62 : W := v50 + v56
  let v63 : W := v4 * w12
  let v64 : W := v63 + v62
  let v65 : W := v21 * w0
  let v66 : W := v65 + v64
  let v67 : W := MachineState.readWord (v47) 192
  let v68 : W := v67 * w9
  let v69 : W := v68 + v66
  let v70 : W := UInt256.mulMod v4 w12 w7
  let v71 : W := v70 + v61
  let v72 : W := UInt256.mulMod v21 w0 w7
  let v73 : W := v72 + v71
  let v74 : W := MachineState.readWord (v47) 192
  let v75 : W := UInt256.mulMod v74 w9 w7
  let v76 : W := v75 + v73
  let v77 : W := MachineState.readWord (v47) 2720
  let v78 : W := v69 * v77
  let v79 : W := UInt256.land w10 v78
  let v80 : ByteArray := MachineState.writeBytes v47 (Data.Bytes.natToBytesPadded v79.toNat 32) 0
  let v81 : W := UInt256.mulMod v79 w11 w7
  let v82 : W := v81 + v76
  let v83 : W := UInt256.mulMod (N 2048) v82 w7
  let v84 : W := MachineState.readWord (v80) 64
  let v85 : W := MachineState.readWord (v80) 768
  let v86 : W := v84 * v85
  let v87 : W := MachineState.readWord (v80) 32
  let v88 : W := w3 * v87
  let v89 : W := v88 + v86
  let v90 : W := v89 + v89
  let v91 : W := UInt256.mulMod v84 v85 w7
  let v92 : W := MachineState.readWord (v80) 32
  let v93 : W := UInt256.mulMod w3 v92 w7
  {s with pc := N 5968, memory := v80, stack := v93 :: v91 :: v90 :: v83 :: w0 :: w1 :: w2 :: w3 :: w4 :: w5 :: v21 :: w7 :: v4 :: w9 :: w10 :: w11 :: w12 :: w13 :: rest}

/-- Five incoming residues occur before the fused column's final reduction.
Their total, plus the doubled product residue, fits below 2^256 for this P. -/
theorem high_double_radix240 (a b c r t u v factor : W)
    (ha : a.toNat < 2^240)
    (hc : c.toNat < (N (2^251-1)).toNat)
    (hr : r.toNat < (N (2^251-1)).toNat)
    (ht : t.toNat < (N (2^251-1)).toNat)
    (hu : u.toNat < (N (2^251-1)).toNat)
    (hv : v.toNat < (N (2^251-1)).toNat) :
    UInt256.mulMod factor
      (v + (u + (t + (r + (c + UInt256.mulMod b (a+a) (N (2^251-1))))))) (N (2^251-1)) =
    UInt256.mulMod factor
      (v + (u + (t + (r + (c + (UInt256.mulMod b a (N (2^251-1)) +
        UInt256.mulMod b a (N (2^251-1)))))))) (N (2^251-1)) := by
  let p := N (2^251-1)
  have hpval : p.toNat = 2^251-1 := by norm_num [p, word_toNat_ofNat]
  have hp : 0 < p.toNat := by rw [hpval]; norm_num
  have hroom : 7*p.toNat ≤ 2^256 := by rw [hpval]; norm_num
  have add_le (x y : W) : (x+y).toNat ≤ x.toNat+y.toNat := by
    rw [word_toNat_add]; exact Nat.mod_le _ _
  have h0 := add_le r c
  have h1 := add_le t (r+c)
  have h2 := add_le u (t+(r+c))
  have h3 := add_le v (u+(t+(r+c)))
  have hbound : 2*p.toNat+(v+(u+(t+(r+c)))).toNat ≤ 2^256 := by
    change c.toNat < p.toNat at hc
    change r.toNat < p.toNat at hr
    change t.toNat < p.toNat at ht
    change u.toNat < p.toNat at hu
    change v.toNat < p.toNat at hv
    omega
  have hh := DoubleInput.high_double a b p (v+(u+(t+(r+c)))) factor hp (by omega) hbound
  simpa only [DoubleInput.addA, word_add_comm, DoubleInput.addL] using hh

private theorem residue_lt (x y : W) :
    (UInt256.mulMod x y (N (2^251-1))).toNat < (N (2^251-1)).toNat := by
  have hp : 0 < (N (2^251-1)).toNat := by norm_num [word_toNat_ofNat]
  rw [DoubleInput.mulMod_nat _ _ _ hp]
  exact Nat.mod_lt _ hp


theorem boundary_eq (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 : W) (rest : List W)
    (hp : w7 = N (2^251-1))
    (ha : (MachineState.readWord s.memory 768).toNat < 2^240) :
    candidateBoundaryModel s w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 rest =
      parentBoundaryModel s w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 rest := by
  subst w7
  let v0 : W := MachineState.readWord (s.memory) 768
  let v1 : W := v0 * v0
  let v2 : W := MachineState.readWord (s.memory) 2720
  let v3 : W := v2 * v1
  let v4 : W := UInt256.land w10 v3
  let v5 : W := UInt256.mulMod v0 v0 (N (2^251-1))
  let v6 : W := UInt256.mulMod w11 v4 (N (2^251-1))
  let v7 : W := v6 + v5
  let v8 : W := UInt256.mulMod (N 2048) v7 (N (2^251-1))
  let v9 : W := MachineState.readWord (s.memory) 768
  let v10 : W := v9 + v9
  let v11 : W := UInt256.mulMod w3 v10 (N (2^251-1))
  let v12 : W := w3 * v10
  let v13 : W := v8 + v12
  let v14 : W := w9 * v4
  let v15 : W := v14 + v13
  let v16 : W := v8 + v11
  let v17 : W := UInt256.mulMod v4 w9 (N (2^251-1))
  let v18 : W := v17 + v16
  let v19 : W := MachineState.readWord (s.memory) 2720
  let v20 : W := v15 * v19
  let v21 : W := UInt256.land w10 v20
  let v22 : W := UInt256.mulMod v21 w11 (N (2^251-1))
  let v23 : W := v22 + v18
  let v24 : W := UInt256.mulMod (N 2048) v23 (N (2^251-1))
  let v25 : W := MachineState.readWord (s.memory) 768
  let v26 : W := v4 * w0
  let v27 : W := w3 * w3
  let v28 : W := UInt256.mulMod w4 v25 (N (2^251-1))
  let v29 : W := v28 + v28
  let v30 : W := w4 * v25
  let v31 : W := v30 + v30
  let v32 : W := v24 + v31
  let v33 : W := v32 + v27
  let v34 : W := v33 + v26
  let v35 : W := w9 * v21
  let v36 : W := v35 + v34
  let v37 : W := v24 + v29
  let v38 : W := UInt256.mulMod w3 w3 (N (2^251-1))
  let v39 : W := v38 + v37
  let v40 : W := UInt256.mulMod v4 w0 (N (2^251-1))
  let v41 : W := v40 + v39
  let v42 : W := UInt256.mulMod v21 w9 (N (2^251-1))
  let v43 : W := v42 + v41
  let v44 : W := MachineState.readWord (s.memory) 2720
  let v45 : W := v36 * v44
  let v46 : W := UInt256.land w10 v45
  let v47 : ByteArray := MachineState.writeBytes s.memory (Data.Bytes.natToBytesPadded v46.toNat 32) 192
  let v48 : W := UInt256.mulMod v46 w11 (N (2^251-1))
  let v49 : W := v48 + v43
  let v50 : W := UInt256.mulMod (N 2048) v49 (N (2^251-1))
  have hh := high_double_radix240 v25 w4 v24 v38 v40 v42 v48 (N 2048) ha
    (residue_lt _ _) (residue_lt _ _) (residue_lt _ _) (residue_lt _ _) (residue_lt _ _)
  have hl : w4*(v25+v25) = w4*v25+w4*v25 := DoubleInput.low_double v25 w4
  unfold candidateBoundaryModel parentBoundaryModel
  dsimp only
  rw [hl]
  exact congrArg (fun x : W => {s with pc := N 5859, memory := v47, stack :=
    x :: w0 :: w1 :: w2 :: w3 :: w4 :: w5 :: v21 :: (N (2^251-1)) :: v4 :: w9 :: w10 :: w11 :: w12 :: w13 :: rest}) hh

/-- Exact fused execution. Besides capacity and active memory, the only
arithmetic invariant is the real a0 digit bound and the exact residue modulus.
The mask and every other stack/memory word remain arbitrary. -/
theorem merged_run (s : State) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat)
    (hp : w7 = N (2^251-1))
    (ha : (MachineState.readWord s.memory 768).toNat < 2^240) :
    runInstructions mergedProgram
      {s with pc := N 5712, stack := w0 :: w1 :: w2 :: w3 :: w4 :: w5 :: w6 :: w7 :: w8 :: w9 :: w10 :: w11 :: w12 :: w13 :: rest} =
        some (mergedModel s w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 rest) := by
  have hb := b_run s w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 rest hcap hact
  rw [boundary_eq s w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 rest hp ha] at hb
  let v0 : W := MachineState.readWord (s.memory) 768
  let v1 : W := v0 * v0
  let v2 : W := MachineState.readWord (s.memory) 2720
  let v3 : W := v2 * v1
  let v4 : W := UInt256.land w10 v3
  let v5 : W := UInt256.mulMod v0 v0 w7
  let v6 : W := UInt256.mulMod w11 v4 w7
  let v7 : W := v6 + v5
  let v8 : W := UInt256.mulMod (N 2048) v7 w7
  let v9 : W := MachineState.readWord (s.memory) 768
  let v10 : W := v9 + v9
  let v11 : W := UInt256.mulMod w3 v10 w7
  let v12 : W := w3 * v10
  let v13 : W := v8 + v12
  let v14 : W := w9 * v4
  let v15 : W := v14 + v13
  let v16 : W := v8 + v11
  let v17 : W := UInt256.mulMod v4 w9 w7
  let v18 : W := v17 + v16
  let v19 : W := MachineState.readWord (s.memory) 2720
  let v20 : W := v15 * v19
  let v21 : W := UInt256.land w10 v20
  let v22 : W := UInt256.mulMod v21 w11 w7
  let v23 : W := v22 + v18
  let v24 : W := UInt256.mulMod (N 2048) v23 w7
  let v25 : W := MachineState.readWord (s.memory) 768
  let v26 : W := v4 * w0
  let v27 : W := w3 * w3
  let v28 : W := UInt256.mulMod w4 v25 w7
  let v29 : W := v28 + v28
  let v30 : W := w4 * v25
  let v31 : W := v30 + v30
  let v32 : W := v24 + v31
  let v33 : W := v32 + v27
  let v34 : W := v33 + v26
  let v35 : W := w9 * v21
  let v36 : W := v35 + v34
  let v37 : W := v24 + v29
  let v38 : W := UInt256.mulMod w3 w3 w7
  let v39 : W := v38 + v37
  let v40 : W := UInt256.mulMod v4 w0 w7
  let v41 : W := v40 + v39
  let v42 : W := UInt256.mulMod v21 w9 w7
  let v43 : W := v42 + v41
  let v44 : W := MachineState.readWord (s.memory) 2720
  let v45 : W := v36 * v44
  let v46 : W := UInt256.land w10 v45
  let v47 : ByteArray := MachineState.writeBytes s.memory (Data.Bytes.natToBytesPadded v46.toNat 32) 192
  let v48 : W := UInt256.mulMod v46 w11 w7
  let v49 : W := v48 + v43
  let v50 : W := UInt256.mulMod (N 2048) v49 w7
  have ht := t_run ({s with memory := v47}) (v50) (w0) (w1) (w2) (w3) (w4) (w5) (v21) (w7) (v4) (w9) (w10) (w11) (w12) (w13) rest hcap hact
  have ht' : runInstructions tail1 (parentBoundaryModel s w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 rest) =
      some (mergedModel s w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 rest) := by
    exact ht
  have h := runInstructions_append_some _ _ _ _ _ hb ht'
  simpa only [mergedProgram, program1, List.append_assoc] using h

#print axioms merged_run
end CycleSubmission.DoubleInput01
