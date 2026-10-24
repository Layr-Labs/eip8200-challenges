import Challenge.Modexp.Submission.Proofs.Fast.Monpro
import Challenge.Modexp.Submission.Proofs.Bytecode.WindowNibbleDefs
set_option warningAsError true
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option maxRecDepth 40000
set_option maxHeartbeats 8000000
namespace CycleSubmission.Execution
open EvmSemantics EvmSemantics.EVM YulEvmCompiler
open Challenge.Modexp.Submission.Proofs.Bytecode.WindowNibbleKernel
open Challenge.Modexp.Submission.Proofs.Fast

def squareColumn0part0Program : List Instr :=
  [.push 2 768,
   .op .MLOAD,
   .op (.Dup ⟨8, by decide⟩),
   .op (.Dup ⟨1, by decide⟩),
   .op (.Dup ⟨0, by decide⟩),
   .op (.Dup ⟨0, by decide⟩),
   .op .MUL,
   .push 2 2720,
   .op .MLOAD]

def squareColumn0part0Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 : UInt256) (rest : List UInt256) : State :=
  let v0 : UInt256 := MachineState.readWord s.memory 768
  let v1 : UInt256 := v0 * v0
  let v2 : UInt256 := MachineState.readWord s.memory 2720
  {s with pc := UInt256.ofNat 6166, memory := s.memory, stack := v2 :: v1 :: v0 :: x7 :: v0 :: x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: rest}

theorem squareColumn0part0_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions squareColumn0part0Program {s with pc := UInt256.ofNat 6153, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: rest} =
      some (squareColumn0part0Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 rest) := by
  have hz : ({val := 0} : UInt256) = UInt256.ofNat 0 := rfl
  have hzn : ({val := 0} : UInt256).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 19) : rest.length + j < 1024 := by omega
  have ha768 : (768 : UInt256).toNat = 768 := rfl
  have hf768 := Monpro.activeWords_fix s 768 32 (by decide) (by norm_num) hact
  have ha2720 : (2720 : UInt256).toNat = 2720 := rfl
  have hf2720 := Monpro.activeWords_fix s 2720 32 (by decide) (by norm_num) hact
  simp [hz, hzn, squareColumn0part0Program, squareColumn0part0Model, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, Challenge.EvmProof.Word.literal_eq_ofNat, capacity, Nat.add_assoc, ha768, hf768, ha2720, hf2720]


def squareColumn0part1Program : List Instr :=
  [.op .MUL,
   .op (.Dup ⟨14, by decide⟩),
   .op .AND,
   .op (.Swap ⟨11, by decide⟩),
   .op .POP,
   .op (.Dup ⟨10, by decide⟩),
   .op (.Swap ⟨2, by decide⟩),
   .op .MULMOD]

def squareColumn0part1Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 : UInt256) (rest : List UInt256) : State :=
  let v0 : UInt256 := x0 * x1
  let v1 : UInt256 := UInt256.land x15 v0
  let v2 : UInt256 := UInt256.mulMod x4 x2 x3
  {s with pc := UInt256.ofNat 6174, memory := s.memory, stack := v2 :: x12 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: v1 :: x14 :: x15 :: x16 :: x17 :: x18 :: rest}

theorem squareColumn0part1_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions squareColumn0part1Program {s with pc := UInt256.ofNat 6166, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: x18 :: rest} =
      some (squareColumn0part1Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 rest) := by
  have hz : ({val := 0} : UInt256) = UInt256.ofNat 0 := rfl
  have hzn : ({val := 0} : UInt256).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 19) : rest.length + j < 1024 := by omega
  simp [hz, hzn, squareColumn0part1Program, squareColumn0part1Model, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, Challenge.EvmProof.Word.literal_eq_ofNat, capacity, Nat.add_assoc]


def squareColumn0part2Program : List Instr :=
  [.op (.Dup ⟨1, by decide⟩),
   .op (.Dup ⟨11, by decide⟩),
   .op (.Dup ⟨15, by decide⟩),
   .op .MULMOD,
   .op .ADD,
   .push 2 2048,
   .op .MULMOD,
   .op (.Dup ⟨4, by decide⟩)]

def squareColumn0part2Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 : UInt256) (rest : List UInt256) : State :=
  let v0 : UInt256 := UInt256.mulMod x13 x10 x1
  let v1 : UInt256 := v0 + x0
  let v2 : UInt256 := UInt256.mulMod (UInt256.ofNat 2048) v1 x1
  {s with pc := UInt256.ofNat 6184, memory := s.memory, stack := x5 :: v2 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: rest}

theorem squareColumn0part2_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions squareColumn0part2Program {s with pc := UInt256.ofNat 6174, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: rest} =
      some (squareColumn0part2Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 rest) := by
  have hz : ({val := 0} : UInt256) = UInt256.ofNat 0 := rfl
  have hzn : ({val := 0} : UInt256).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 19) : rest.length + j < 1024 := by omega
  simp [hz, hzn, squareColumn0part2Program, squareColumn0part2Model, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, Challenge.EvmProof.Word.literal_eq_ofNat, capacity, Nat.add_assoc]


def squareColumn0part3Program : List Instr :=
  [.op (.Dup ⟨9, by decide⟩),
   .push 2 768,
   .op .MLOAD,
   .op (.Dup ⟨0, by decide⟩),
   .op (.Dup ⟨3, by decide⟩),
   .op .MUL,
   .op (.Dup ⟨0, by decide⟩),
   .op .ADD]

def squareColumn0part3Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 : UInt256) (rest : List UInt256) : State :=
  let v0 : UInt256 := MachineState.readWord s.memory 768
  let v1 : UInt256 := x0 * v0
  let v2 : UInt256 := v1 + v1
  {s with pc := UInt256.ofNat 6194, memory := s.memory, stack := v2 :: v0 :: x9 :: x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: rest}

theorem squareColumn0part3_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions squareColumn0part3Program {s with pc := UInt256.ofNat 6184, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: rest} =
      some (squareColumn0part3Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 rest) := by
  have hz : ({val := 0} : UInt256) = UInt256.ofNat 0 := rfl
  have hzn : ({val := 0} : UInt256).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 20) : rest.length + j < 1024 := by omega
  have ha768 : (768 : UInt256).toNat = 768 := rfl
  have hf768 := Monpro.activeWords_fix s 768 32 (by decide) (by norm_num) hact
  simp [hz, hzn, squareColumn0part3Program, squareColumn0part3Model, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, Challenge.EvmProof.Word.literal_eq_ofNat, capacity, Nat.add_assoc, ha768, hf768]


def squareColumn0part4Program : List Instr :=
  [.op (.Swap ⟨2, by decide⟩),
   .op .MULMOD,
   .op (.Dup ⟨0, by decide⟩),
   .op .ADD,
   .op (.Dup ⟨2, by decide⟩),
   .op .ADD,
   .op (.Swap ⟨1, by decide⟩),
   .op .ADD]

def squareColumn0part4Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 : UInt256) (rest : List UInt256) : State :=
  let v0 : UInt256 := UInt256.mulMod x3 x1 x2
  let v1 : UInt256 := v0 + v0
  let v2 : UInt256 := x4 + v1
  let v3 : UInt256 := x4 + x0
  {s with pc := UInt256.ofNat 6202, memory := s.memory, stack := v3 :: v2 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: x18 :: rest}

theorem squareColumn0part4_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions squareColumn0part4Program {s with pc := UInt256.ofNat 6194, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: x18 :: rest} =
      some (squareColumn0part4Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 rest) := by
  have hz : ({val := 0} : UInt256) = UInt256.ofNat 0 := rfl
  have hzn : ({val := 0} : UInt256).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 19) : rest.length + j < 1024 := by omega
  simp [hz, hzn, squareColumn0part4Program, squareColumn0part4Model, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, Challenge.EvmProof.Word.literal_eq_ofNat, capacity, Nat.add_assoc]


def squareColumn0part5Program : List Instr :=
  [.op (.Dup ⟨11, by decide⟩),
   .op (.Dup ⟨11, by decide⟩),
   .op .MUL,
   .op .ADD,
   .op (.Swap ⟨0, by decide⟩),
   .op (.Dup ⟨9, by decide⟩),
   .op (.Dup ⟨12, by decide⟩),
   .op (.Dup ⟨12, by decide⟩)]

def squareColumn0part5Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 : UInt256) (rest : List UInt256) : State :=
  let v0 : UInt256 := x10 * x11
  let v1 : UInt256 := v0 + x0
  {s with pc := UInt256.ofNat 6210, memory := s.memory, stack := x10 :: x11 :: x9 :: x1 :: v1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: rest}

theorem squareColumn0part5_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions squareColumn0part5Program {s with pc := UInt256.ofNat 6202, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: rest} =
      some (squareColumn0part5Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 rest) := by
  have hz : ({val := 0} : UInt256) = UInt256.ofNat 0 := rfl
  have hzn : ({val := 0} : UInt256).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 19) : rest.length + j < 1024 := by omega
  simp [hz, hzn, squareColumn0part5Program, squareColumn0part5Model, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, Challenge.EvmProof.Word.literal_eq_ofNat, capacity, Nat.add_assoc]


def squareColumn0part6Program : List Instr :=
  [.op .MULMOD,
   .op .ADD,
   .op (.Dup ⟨9, by decide⟩),
   .op (.Dup ⟨14, by decide⟩),
   .push 2 2720,
   .op .MLOAD,
   .op (.Dup ⟨2, by decide⟩),
   .op (.Swap ⟨4, by decide⟩)]

def squareColumn0part6Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 : UInt256) (rest : List UInt256) : State :=
  let v0 : UInt256 := UInt256.mulMod x0 x1 x2
  let v1 : UInt256 := v0 + x3
  let v2 : UInt256 := MachineState.readWord s.memory 2720
  {s with pc := UInt256.ofNat 6220, memory := s.memory, stack := x4 :: v2 :: x16 :: x12 :: v1 :: x12 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: x18 :: rest}

theorem squareColumn0part6_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions squareColumn0part6Program {s with pc := UInt256.ofNat 6210, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: x18 :: rest} =
      some (squareColumn0part6Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 rest) := by
  have hz : ({val := 0} : UInt256) = UInt256.ofNat 0 := rfl
  have hzn : ({val := 0} : UInt256).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 20) : rest.length + j < 1024 := by omega
  have ha2720 : (2720 : UInt256).toNat = 2720 := rfl
  have hf2720 := Monpro.activeWords_fix s 2720 32 (by decide) (by norm_num) hact
  simp [hz, hzn, squareColumn0part6Program, squareColumn0part6Model, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, Challenge.EvmProof.Word.literal_eq_ofNat, capacity, Nat.add_assoc, ha2720, hf2720]


def squareColumn0part7Program : List Instr :=
  [.op .MUL,
   .op (.Dup ⟨15, by decide⟩),
   .op .AND,
   .op (.Dup ⟨0, by decide⟩),
   .op (.Swap ⟨11, by decide⟩),
   .op .POP,
   .op .MULMOD,
   .op .ADD]

def squareColumn0part7Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 : UInt256) (rest : List UInt256) : State :=
  let v0 : UInt256 := x0 * x1
  let v1 : UInt256 := UInt256.land x16 v0
  let v2 : UInt256 := UInt256.mulMod v1 x2 x3
  let v3 : UInt256 := v2 + x4
  {s with pc := UInt256.ofNat 6228, memory := s.memory, stack := v3 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: v1 :: x13 :: x14 :: x15 :: x16 :: x17 :: x18 :: x19 :: rest}

theorem squareColumn0part7_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions squareColumn0part7Program {s with pc := UInt256.ofNat 6220, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: x18 :: x19 :: rest} =
      some (squareColumn0part7Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 rest) := by
  have hz : ({val := 0} : UInt256) = UInt256.ofNat 0 := rfl
  have hzn : ({val := 0} : UInt256).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 20) : rest.length + j < 1024 := by omega
  simp [hz, hzn, squareColumn0part7Program, squareColumn0part7Model, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, Challenge.EvmProof.Word.literal_eq_ofNat, capacity, Nat.add_assoc]


def squareColumn0part8Program : List Instr :=
  [.push 2 2048,
   .op .MULMOD,
   .op (.Dup ⟨5, by decide⟩),
   .op (.Dup ⟨9, by decide⟩),
   .push 2 768,
   .op .MLOAD,
   .op (.Dup ⟨0, by decide⟩),
   .op (.Dup ⟨3, by decide⟩)]

def squareColumn0part8Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 : UInt256) (rest : List UInt256) : State :=
  let v0 : UInt256 := UInt256.mulMod (UInt256.ofNat 2048) x0 x1
  let v1 : UInt256 := MachineState.readWord s.memory 768
  {s with pc := UInt256.ofNat 6240, memory := s.memory, stack := x6 :: v1 :: v1 :: x9 :: x6 :: v0 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: rest}

theorem squareColumn0part8_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions squareColumn0part8Program {s with pc := UInt256.ofNat 6228, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: rest} =
      some (squareColumn0part8Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 rest) := by
  have hz : ({val := 0} : UInt256) = UInt256.ofNat 0 := rfl
  have hzn : ({val := 0} : UInt256).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 20) : rest.length + j < 1024 := by omega
  have ha768 : (768 : UInt256).toNat = 768 := rfl
  have hf768 := Monpro.activeWords_fix s 768 32 (by decide) (by norm_num) hact
  simp [hz, hzn, squareColumn0part8Program, squareColumn0part8Model, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, Challenge.EvmProof.Word.literal_eq_ofNat, capacity, Nat.add_assoc, ha768, hf768]


def squareColumn0part9Program : List Instr :=
  [.op .MUL,
   .op (.Dup ⟨0, by decide⟩),
   .op .ADD,
   .op (.Swap ⟨2, by decide⟩),
   .op .MULMOD,
   .op (.Dup ⟨0, by decide⟩),
   .op .ADD,
   .op (.Dup ⟨2, by decide⟩)]

def squareColumn0part9Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 : UInt256) (rest : List UInt256) : State :=
  let v0 : UInt256 := x0 * x1
  let v1 : UInt256 := v0 + v0
  let v2 : UInt256 := UInt256.mulMod x4 x2 x3
  let v3 : UInt256 := v2 + v2
  {s with pc := UInt256.ofNat 6248, memory := s.memory, stack := x5 :: v3 :: v1 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: x18 :: x19 :: rest}

theorem squareColumn0part9_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions squareColumn0part9Program {s with pc := UInt256.ofNat 6240, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: x18 :: x19 :: rest} =
      some (squareColumn0part9Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 rest) := by
  have hz : ({val := 0} : UInt256) = UInt256.ofNat 0 := rfl
  have hzn : ({val := 0} : UInt256).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 20) : rest.length + j < 1024 := by omega
  simp [hz, hzn, squareColumn0part9Program, squareColumn0part9Model, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, Challenge.EvmProof.Word.literal_eq_ofNat, capacity, Nat.add_assoc]


def squareColumn0part10Program : List Instr :=
  [.op .ADD,
   .op (.Swap ⟨1, by decide⟩),
   .op .ADD,
   .op (.Dup ⟨5, by decide⟩),
   .op (.Dup ⟨0, by decide⟩),
   .op .MUL,
   .op .ADD,
   .op (.Dup ⟨2, by decide⟩)]

def squareColumn0part10Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 : UInt256) (rest : List UInt256) : State :=
  let v0 : UInt256 := x0 + x1
  let v1 : UInt256 := x3 + x2
  let v2 : UInt256 := x7 * x7
  let v3 : UInt256 := v2 + v1
  {s with pc := UInt256.ofNat 6256, memory := s.memory, stack := x4 :: v3 :: v0 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: rest}

theorem squareColumn0part10_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions squareColumn0part10Program {s with pc := UInt256.ofNat 6248, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: rest} =
      some (squareColumn0part10Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 rest) := by
  have hz : ({val := 0} : UInt256) = UInt256.ofNat 0 := rfl
  have hzn : ({val := 0} : UInt256).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 18) : rest.length + j < 1024 := by omega
  simp [hz, hzn, squareColumn0part10Program, squareColumn0part10Model, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, Challenge.EvmProof.Word.literal_eq_ofNat, capacity, Nat.add_assoc]


def squareColumn0part11Program : List Instr :=
  [.op (.Dup ⟨11, by decide⟩),
   .op .MUL,
   .op .ADD,
   .op (.Dup ⟨11, by decide⟩),
   .op (.Dup ⟨9, by decide⟩),
   .op .MUL,
   .op .ADD,
   .op (.Swap ⟨0, by decide⟩)]

def squareColumn0part11Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 : UInt256) (rest : List UInt256) : State :=
  let v0 : UInt256 := x11 * x0
  let v1 : UInt256 := v0 + x1
  let v2 : UInt256 := x9 * x12
  let v3 : UInt256 := v2 + v1
  {s with pc := UInt256.ofNat 6264, memory := s.memory, stack := x2 :: v3 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: rest}

theorem squareColumn0part11_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions squareColumn0part11Program {s with pc := UInt256.ofNat 6256, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: rest} =
      some (squareColumn0part11Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 rest) := by
  have hz : ({val := 0} : UInt256) = UInt256.ofNat 0 := rfl
  have hzn : ({val := 0} : UInt256).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 18) : rest.length + j < 1024 := by omega
  simp [hz, hzn, squareColumn0part11Program, squareColumn0part11Model, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, Challenge.EvmProof.Word.literal_eq_ofNat, capacity, Nat.add_assoc]


def squareColumn0part12Program : List Instr :=
  [.op (.Dup ⟨9, by decide⟩),
   .op (.Dup ⟨6, by decide⟩),
   .op (.Dup ⟨0, by decide⟩),
   .op .MULMOD,
   .op .ADD,
   .op (.Dup ⟨9, by decide⟩),
   .op (.Dup ⟨3, by decide⟩),
   .op (.Dup ⟨12, by decide⟩)]

def squareColumn0part12Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 : UInt256) (rest : List UInt256) : State :=
  let v0 : UInt256 := UInt256.mulMod x5 x5 x9
  let v1 : UInt256 := v0 + x0
  {s with pc := UInt256.ofNat 6272, memory := s.memory, stack := x10 :: x2 :: x9 :: v1 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: rest}

theorem squareColumn0part12_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions squareColumn0part12Program {s with pc := UInt256.ofNat 6264, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: rest} =
      some (squareColumn0part12Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 rest) := by
  have hz : ({val := 0} : UInt256) = UInt256.ofNat 0 := rfl
  have hzn : ({val := 0} : UInt256).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 19) : rest.length + j < 1024 := by omega
  simp [hz, hzn, squareColumn0part12Program, squareColumn0part12Model, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, Challenge.EvmProof.Word.literal_eq_ofNat, capacity, Nat.add_assoc]


def squareColumn0part13Program : List Instr :=
  [.op .MULMOD,
   .op .ADD,
   .op (.Dup ⟨9, by decide⟩),
   .op (.Dup ⟨12, by decide⟩),
   .op (.Dup ⟨10, by decide⟩),
   .op .MULMOD,
   .op .ADD,
   .op (.Dup ⟨9, by decide⟩)]

def squareColumn0part13Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 : UInt256) (rest : List UInt256) : State :=
  let v0 : UInt256 := UInt256.mulMod x0 x1 x2
  let v1 : UInt256 := v0 + x3
  let v2 : UInt256 := UInt256.mulMod x11 x14 x12
  let v3 : UInt256 := v2 + v1
  {s with pc := UInt256.ofNat 6280, memory := s.memory, stack := x12 :: v3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: x18 :: rest}

theorem squareColumn0part13_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions squareColumn0part13Program {s with pc := UInt256.ofNat 6272, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: x18 :: rest} =
      some (squareColumn0part13Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 rest) := by
  have hz : ({val := 0} : UInt256) = UInt256.ofNat 0 := rfl
  have hzn : ({val := 0} : UInt256).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 19) : rest.length + j < 1024 := by omega
  simp [hz, hzn, squareColumn0part13Program, squareColumn0part13Model, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, Challenge.EvmProof.Word.literal_eq_ofNat, capacity, Nat.add_assoc]


def squareColumn0part14Program : List Instr :=
  [.op (.Dup ⟨14, by decide⟩)]

def squareColumn0part14Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 : UInt256) (rest : List UInt256) : State :=
  {s with pc := UInt256.ofNat 6281, memory := s.memory, stack := x14 :: x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: rest}

theorem squareColumn0part14_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions squareColumn0part14Program {s with pc := UInt256.ofNat 6280, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: rest} =
      some (squareColumn0part14Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 rest) := by
  have hz : ({val := 0} : UInt256) = UInt256.ofNat 0 := rfl
  have hzn : ({val := 0} : UInt256).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 18) : rest.length + j < 1024 := by omega
  simp [hz, hzn, squareColumn0part14Program, squareColumn0part14Model, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, Challenge.EvmProof.Word.literal_eq_ofNat, capacity, Nat.add_assoc]


def squareColumn0Program : List Instr :=
  [.push 2 768,
   .op .MLOAD,
   .op (.Dup ⟨8, by decide⟩),
   .op (.Dup ⟨1, by decide⟩),
   .op (.Dup ⟨0, by decide⟩),
   .op (.Dup ⟨0, by decide⟩),
   .op .MUL,
   .push 2 2720,
   .op .MLOAD,
   .op .MUL,
   .op (.Dup ⟨14, by decide⟩),
   .op .AND,
   .op (.Swap ⟨11, by decide⟩),
   .op .POP,
   .op (.Dup ⟨10, by decide⟩),
   .op (.Swap ⟨2, by decide⟩),
   .op .MULMOD,
   .op (.Dup ⟨1, by decide⟩),
   .op (.Dup ⟨11, by decide⟩),
   .op (.Dup ⟨15, by decide⟩),
   .op .MULMOD,
   .op .ADD,
   .push 2 2048,
   .op .MULMOD,
   .op (.Dup ⟨4, by decide⟩),
   .op (.Dup ⟨9, by decide⟩),
   .push 2 768,
   .op .MLOAD,
   .op (.Dup ⟨0, by decide⟩),
   .op (.Dup ⟨3, by decide⟩),
   .op .MUL,
   .op (.Dup ⟨0, by decide⟩),
   .op .ADD,
   .op (.Swap ⟨2, by decide⟩),
   .op .MULMOD,
   .op (.Dup ⟨0, by decide⟩),
   .op .ADD,
   .op (.Dup ⟨2, by decide⟩),
   .op .ADD,
   .op (.Swap ⟨1, by decide⟩),
   .op .ADD,
   .op (.Dup ⟨11, by decide⟩),
   .op (.Dup ⟨11, by decide⟩),
   .op .MUL,
   .op .ADD,
   .op (.Swap ⟨0, by decide⟩),
   .op (.Dup ⟨9, by decide⟩),
   .op (.Dup ⟨12, by decide⟩),
   .op (.Dup ⟨12, by decide⟩),
   .op .MULMOD,
   .op .ADD,
   .op (.Dup ⟨9, by decide⟩),
   .op (.Dup ⟨14, by decide⟩),
   .push 2 2720,
   .op .MLOAD,
   .op (.Dup ⟨2, by decide⟩),
   .op (.Swap ⟨4, by decide⟩),
   .op .MUL,
   .op (.Dup ⟨15, by decide⟩),
   .op .AND,
   .op (.Dup ⟨0, by decide⟩),
   .op (.Swap ⟨11, by decide⟩),
   .op .POP,
   .op .MULMOD,
   .op .ADD,
   .push 2 2048,
   .op .MULMOD,
   .op (.Dup ⟨5, by decide⟩),
   .op (.Dup ⟨9, by decide⟩),
   .push 2 768,
   .op .MLOAD,
   .op (.Dup ⟨0, by decide⟩),
   .op (.Dup ⟨3, by decide⟩),
   .op .MUL,
   .op (.Dup ⟨0, by decide⟩),
   .op .ADD,
   .op (.Swap ⟨2, by decide⟩),
   .op .MULMOD,
   .op (.Dup ⟨0, by decide⟩),
   .op .ADD,
   .op (.Dup ⟨2, by decide⟩),
   .op .ADD,
   .op (.Swap ⟨1, by decide⟩),
   .op .ADD,
   .op (.Dup ⟨5, by decide⟩),
   .op (.Dup ⟨0, by decide⟩),
   .op .MUL,
   .op .ADD,
   .op (.Dup ⟨2, by decide⟩),
   .op (.Dup ⟨11, by decide⟩),
   .op .MUL,
   .op .ADD,
   .op (.Dup ⟨11, by decide⟩),
   .op (.Dup ⟨9, by decide⟩),
   .op .MUL,
   .op .ADD,
   .op (.Swap ⟨0, by decide⟩),
   .op (.Dup ⟨9, by decide⟩),
   .op (.Dup ⟨6, by decide⟩),
   .op (.Dup ⟨0, by decide⟩),
   .op .MULMOD,
   .op .ADD,
   .op (.Dup ⟨9, by decide⟩),
   .op (.Dup ⟨3, by decide⟩),
   .op (.Dup ⟨12, by decide⟩),
   .op .MULMOD,
   .op .ADD,
   .op (.Dup ⟨9, by decide⟩),
   .op (.Dup ⟨12, by decide⟩),
   .op (.Dup ⟨10, by decide⟩),
   .op .MULMOD,
   .op .ADD,
   .op (.Dup ⟨9, by decide⟩),
   .op (.Dup ⟨14, by decide⟩)]

def squareColumn0Model (s : State) (word0 word1 word2 word3 word4 word5 word6 word7 word8 word9 word10 word11 word12 word13 : UInt256) (rest : List UInt256) : State :=
  let v0 : UInt256 := MachineState.readWord s.memory 768
  let v1 : UInt256 := v0 * v0
  let v2 : UInt256 := MachineState.readWord s.memory 2720
  let v3 : UInt256 := v2 * v1
  let v4 : UInt256 := UInt256.land word10 v3
  let v5 : UInt256 := UInt256.mulMod v0 v0 word7
  let v6 : UInt256 := UInt256.mulMod word11 v4 word7
  let v7 : UInt256 := v6 + v5
  let v8 : UInt256 := UInt256.mulMod (UInt256.ofNat 2048) v7 word7
  let v9 : UInt256 := MachineState.readWord s.memory 768
  let v10 : UInt256 := word3 * v9
  let v11 : UInt256 := v10 + v10
  let v12 : UInt256 := UInt256.mulMod word3 v9 word7
  let v13 : UInt256 := v12 + v12
  let v14 : UInt256 := v8 + v13
  let v15 : UInt256 := v8 + v11
  let v16 : UInt256 := v4 * word9
  let v17 : UInt256 := v16 + v15
  let v18 : UInt256 := UInt256.mulMod v4 word9 word7
  let v19 : UInt256 := v18 + v14
  let v20 : UInt256 := MachineState.readWord s.memory 2720
  let v21 : UInt256 := v17 * v20
  let v22 : UInt256 := UInt256.land word10 v21
  let v23 : UInt256 := UInt256.mulMod v22 word11 word7
  let v24 : UInt256 := v23 + v19
  let v25 : UInt256 := UInt256.mulMod (UInt256.ofNat 2048) v24 word7
  let v26 : UInt256 := MachineState.readWord s.memory 768
  let v27 : UInt256 := word4 * v26
  let v28 : UInt256 := v27 + v27
  let v29 : UInt256 := UInt256.mulMod word4 v26 word7
  let v30 : UInt256 := v29 + v29
  let v31 : UInt256 := v25 + v30
  let v32 : UInt256 := v25 + v28
  let v33 : UInt256 := word3 * word3
  let v34 : UInt256 := v33 + v32
  let v35 : UInt256 := v4 * word0
  let v36 : UInt256 := v35 + v34
  let v37 : UInt256 := v22 * word9
  let v38 : UInt256 := v37 + v36
  let v39 : UInt256 := UInt256.mulMod word3 word3 word7
  let v40 : UInt256 := v39 + v31
  let v41 : UInt256 := UInt256.mulMod v4 word0 word7
  let v42 : UInt256 := v41 + v40
  let v43 : UInt256 := UInt256.mulMod v22 word9 word7
  let v44 : UInt256 := v43 + v42
  {s with pc := UInt256.ofNat 6281, memory := s.memory, stack := word11 :: word7 :: v44 :: v38 :: word0 :: word1 :: word2 :: word3 :: word4 :: word5 :: v22 :: word7 :: v4 :: word9 :: word10 :: word11 :: word12 :: word13 :: rest}

theorem squareColumn0_run (s : State) (word0 word1 word2 word3 word4 word5 word6 word7 word8 word9 word10 word11 word12 word13 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions squareColumn0Program {s with pc := UInt256.ofNat 6153, stack := word0 :: word1 :: word2 :: word3 :: word4 :: word5 :: word6 :: word7 :: word8 :: word9 :: word10 :: word11 :: word12 :: word13 :: rest} =
      some (squareColumn0Model s word0 word1 word2 word3 word4 word5 word6 word7 word8 word9 word10 word11 word12 word13 rest) := by
  let v0 : UInt256 := MachineState.readWord s.memory 768
  let v1 : UInt256 := v0 * v0
  let v2 : UInt256 := MachineState.readWord s.memory 2720
  let v3 : UInt256 := v2 * v1
  let v4 : UInt256 := UInt256.land word10 v3
  let v5 : UInt256 := UInt256.mulMod v0 v0 word7
  let v6 : UInt256 := UInt256.mulMod word11 v4 word7
  let v7 : UInt256 := v6 + v5
  let v8 : UInt256 := UInt256.mulMod (UInt256.ofNat 2048) v7 word7
  let v9 : UInt256 := MachineState.readWord s.memory 768
  let v10 : UInt256 := word3 * v9
  let v11 : UInt256 := v10 + v10
  let v12 : UInt256 := UInt256.mulMod word3 v9 word7
  let v13 : UInt256 := v12 + v12
  let v14 : UInt256 := v8 + v13
  let v15 : UInt256 := v8 + v11
  let v16 : UInt256 := v4 * word9
  let v17 : UInt256 := v16 + v15
  let v18 : UInt256 := UInt256.mulMod v4 word9 word7
  let v19 : UInt256 := v18 + v14
  let v20 : UInt256 := MachineState.readWord s.memory 2720
  let v21 : UInt256 := v17 * v20
  let v22 : UInt256 := UInt256.land word10 v21
  let v23 : UInt256 := UInt256.mulMod v22 word11 word7
  let v24 : UInt256 := v23 + v19
  let v25 : UInt256 := UInt256.mulMod (UInt256.ofNat 2048) v24 word7
  let v26 : UInt256 := MachineState.readWord s.memory 768
  let v27 : UInt256 := word4 * v26
  let v28 : UInt256 := v27 + v27
  let v29 : UInt256 := UInt256.mulMod word4 v26 word7
  let v30 : UInt256 := v29 + v29
  let v31 : UInt256 := v25 + v30
  let v32 : UInt256 := v25 + v28
  let v33 : UInt256 := word3 * word3
  let v34 : UInt256 := v33 + v32
  let v35 : UInt256 := v4 * word0
  let v36 : UInt256 := v35 + v34
  let v37 : UInt256 := v22 * word9
  let v38 : UInt256 := v37 + v36
  let v39 : UInt256 := UInt256.mulMod word3 word3 word7
  let v40 : UInt256 := v39 + v31
  let v41 : UInt256 := UInt256.mulMod v4 word0 word7
  let v42 : UInt256 := v41 + v40
  let v43 : UInt256 := UInt256.mulMod v22 word9 word7
  let v44 : UInt256 := v43 + v42
  have h0 : runInstructions squareColumn0part0Program {s with pc := UInt256.ofNat 6153, memory := s.memory, stack := word0 :: word1 :: word2 :: word3 :: word4 :: word5 :: word6 :: word7 :: word8 :: word9 :: word10 :: word11 :: word12 :: word13 :: rest} = some {s with pc := UInt256.ofNat 6166, memory := s.memory, stack := v2 :: v1 :: v0 :: word7 :: v0 :: word0 :: word1 :: word2 :: word3 :: word4 :: word5 :: word6 :: word7 :: word8 :: word9 :: word10 :: word11 :: word12 :: word13 :: rest} := by
    simpa only [squareColumn0part0Model, v0, v1, v2] using squareColumn0part0_run (s) (word0) (word1) (word2) (word3) (word4) (word5) (word6) (word7) (word8) (word9) (word10) (word11) (word12) (word13) rest hcap hact
  have h1 : runInstructions squareColumn0part1Program {s with pc := UInt256.ofNat 6166, memory := s.memory, stack := v2 :: v1 :: v0 :: word7 :: v0 :: word0 :: word1 :: word2 :: word3 :: word4 :: word5 :: word6 :: word7 :: word8 :: word9 :: word10 :: word11 :: word12 :: word13 :: rest} = some {s with pc := UInt256.ofNat 6174, memory := s.memory, stack := v5 :: word7 :: word0 :: word1 :: word2 :: word3 :: word4 :: word5 :: word6 :: word7 :: v4 :: word9 :: word10 :: word11 :: word12 :: word13 :: rest} := by
    simpa only [squareColumn0part1Model, v3, v4, v5] using squareColumn0part1_run (s) (v2) (v1) (v0) (word7) (v0) (word0) (word1) (word2) (word3) (word4) (word5) (word6) (word7) (word8) (word9) (word10) (word11) (word12) (word13) rest hcap hact
  have h2 : runInstructions squareColumn0part2Program {s with pc := UInt256.ofNat 6174, memory := s.memory, stack := v5 :: word7 :: word0 :: word1 :: word2 :: word3 :: word4 :: word5 :: word6 :: word7 :: v4 :: word9 :: word10 :: word11 :: word12 :: word13 :: rest} = some {s with pc := UInt256.ofNat 6184, memory := s.memory, stack := word3 :: v8 :: word0 :: word1 :: word2 :: word3 :: word4 :: word5 :: word6 :: word7 :: v4 :: word9 :: word10 :: word11 :: word12 :: word13 :: rest} := by
    simpa only [squareColumn0part2Model, v6, v7, v8] using squareColumn0part2_run (s) (v5) (word7) (word0) (word1) (word2) (word3) (word4) (word5) (word6) (word7) (v4) (word9) (word10) (word11) (word12) (word13) rest hcap hact
  have h3 : runInstructions squareColumn0part3Program {s with pc := UInt256.ofNat 6184, memory := s.memory, stack := word3 :: v8 :: word0 :: word1 :: word2 :: word3 :: word4 :: word5 :: word6 :: word7 :: v4 :: word9 :: word10 :: word11 :: word12 :: word13 :: rest} = some {s with pc := UInt256.ofNat 6194, memory := s.memory, stack := v11 :: v9 :: word7 :: word3 :: v8 :: word0 :: word1 :: word2 :: word3 :: word4 :: word5 :: word6 :: word7 :: v4 :: word9 :: word10 :: word11 :: word12 :: word13 :: rest} := by
    simpa only [squareColumn0part3Model, v9, v10, v11] using squareColumn0part3_run (s) (word3) (v8) (word0) (word1) (word2) (word3) (word4) (word5) (word6) (word7) (v4) (word9) (word10) (word11) (word12) (word13) rest hcap hact
  have h4 : runInstructions squareColumn0part4Program {s with pc := UInt256.ofNat 6194, memory := s.memory, stack := v11 :: v9 :: word7 :: word3 :: v8 :: word0 :: word1 :: word2 :: word3 :: word4 :: word5 :: word6 :: word7 :: v4 :: word9 :: word10 :: word11 :: word12 :: word13 :: rest} = some {s with pc := UInt256.ofNat 6202, memory := s.memory, stack := v15 :: v14 :: word0 :: word1 :: word2 :: word3 :: word4 :: word5 :: word6 :: word7 :: v4 :: word9 :: word10 :: word11 :: word12 :: word13 :: rest} := by
    simpa only [squareColumn0part4Model, v12, v13, v14, v15] using squareColumn0part4_run (s) (v11) (v9) (word7) (word3) (v8) (word0) (word1) (word2) (word3) (word4) (word5) (word6) (word7) (v4) (word9) (word10) (word11) (word12) (word13) rest hcap hact
  have h5 : runInstructions squareColumn0part5Program {s with pc := UInt256.ofNat 6202, memory := s.memory, stack := v15 :: v14 :: word0 :: word1 :: word2 :: word3 :: word4 :: word5 :: word6 :: word7 :: v4 :: word9 :: word10 :: word11 :: word12 :: word13 :: rest} = some {s with pc := UInt256.ofNat 6210, memory := s.memory, stack := v4 :: word9 :: word7 :: v14 :: v17 :: word0 :: word1 :: word2 :: word3 :: word4 :: word5 :: word6 :: word7 :: v4 :: word9 :: word10 :: word11 :: word12 :: word13 :: rest} := by
    simpa only [squareColumn0part5Model, v16, v17] using squareColumn0part5_run (s) (v15) (v14) (word0) (word1) (word2) (word3) (word4) (word5) (word6) (word7) (v4) (word9) (word10) (word11) (word12) (word13) rest hcap hact
  have h6 : runInstructions squareColumn0part6Program {s with pc := UInt256.ofNat 6210, memory := s.memory, stack := v4 :: word9 :: word7 :: v14 :: v17 :: word0 :: word1 :: word2 :: word3 :: word4 :: word5 :: word6 :: word7 :: v4 :: word9 :: word10 :: word11 :: word12 :: word13 :: rest} = some {s with pc := UInt256.ofNat 6220, memory := s.memory, stack := v17 :: v20 :: word11 :: word7 :: v19 :: word7 :: word0 :: word1 :: word2 :: word3 :: word4 :: word5 :: word6 :: word7 :: v4 :: word9 :: word10 :: word11 :: word12 :: word13 :: rest} := by
    simpa only [squareColumn0part6Model, v18, v19, v20] using squareColumn0part6_run (s) (v4) (word9) (word7) (v14) (v17) (word0) (word1) (word2) (word3) (word4) (word5) (word6) (word7) (v4) (word9) (word10) (word11) (word12) (word13) rest hcap hact
  have h7 : runInstructions squareColumn0part7Program {s with pc := UInt256.ofNat 6220, memory := s.memory, stack := v17 :: v20 :: word11 :: word7 :: v19 :: word7 :: word0 :: word1 :: word2 :: word3 :: word4 :: word5 :: word6 :: word7 :: v4 :: word9 :: word10 :: word11 :: word12 :: word13 :: rest} = some {s with pc := UInt256.ofNat 6228, memory := s.memory, stack := v24 :: word7 :: word0 :: word1 :: word2 :: word3 :: word4 :: word5 :: v22 :: word7 :: v4 :: word9 :: word10 :: word11 :: word12 :: word13 :: rest} := by
    simpa only [squareColumn0part7Model, v21, v22, v23, v24] using squareColumn0part7_run (s) (v17) (v20) (word11) (word7) (v19) (word7) (word0) (word1) (word2) (word3) (word4) (word5) (word6) (word7) (v4) (word9) (word10) (word11) (word12) (word13) rest hcap hact
  have h8 : runInstructions squareColumn0part8Program {s with pc := UInt256.ofNat 6228, memory := s.memory, stack := v24 :: word7 :: word0 :: word1 :: word2 :: word3 :: word4 :: word5 :: v22 :: word7 :: v4 :: word9 :: word10 :: word11 :: word12 :: word13 :: rest} = some {s with pc := UInt256.ofNat 6240, memory := s.memory, stack := word4 :: v26 :: v26 :: word7 :: word4 :: v25 :: word0 :: word1 :: word2 :: word3 :: word4 :: word5 :: v22 :: word7 :: v4 :: word9 :: word10 :: word11 :: word12 :: word13 :: rest} := by
    simpa only [squareColumn0part8Model, v25, v26] using squareColumn0part8_run (s) (v24) (word7) (word0) (word1) (word2) (word3) (word4) (word5) (v22) (word7) (v4) (word9) (word10) (word11) (word12) (word13) rest hcap hact
  have h9 : runInstructions squareColumn0part9Program {s with pc := UInt256.ofNat 6240, memory := s.memory, stack := word4 :: v26 :: v26 :: word7 :: word4 :: v25 :: word0 :: word1 :: word2 :: word3 :: word4 :: word5 :: v22 :: word7 :: v4 :: word9 :: word10 :: word11 :: word12 :: word13 :: rest} = some {s with pc := UInt256.ofNat 6248, memory := s.memory, stack := v25 :: v30 :: v28 :: v25 :: word0 :: word1 :: word2 :: word3 :: word4 :: word5 :: v22 :: word7 :: v4 :: word9 :: word10 :: word11 :: word12 :: word13 :: rest} := by
    simpa only [squareColumn0part9Model, v27, v28, v29, v30] using squareColumn0part9_run (s) (word4) (v26) (v26) (word7) (word4) (v25) (word0) (word1) (word2) (word3) (word4) (word5) (v22) (word7) (v4) (word9) (word10) (word11) (word12) (word13) rest hcap hact
  have h10 : runInstructions squareColumn0part10Program {s with pc := UInt256.ofNat 6248, memory := s.memory, stack := v25 :: v30 :: v28 :: v25 :: word0 :: word1 :: word2 :: word3 :: word4 :: word5 :: v22 :: word7 :: v4 :: word9 :: word10 :: word11 :: word12 :: word13 :: rest} = some {s with pc := UInt256.ofNat 6256, memory := s.memory, stack := word0 :: v34 :: v31 :: word0 :: word1 :: word2 :: word3 :: word4 :: word5 :: v22 :: word7 :: v4 :: word9 :: word10 :: word11 :: word12 :: word13 :: rest} := by
    simpa only [squareColumn0part10Model, v31, v32, v33, v34] using squareColumn0part10_run (s) (v25) (v30) (v28) (v25) (word0) (word1) (word2) (word3) (word4) (word5) (v22) (word7) (v4) (word9) (word10) (word11) (word12) (word13) rest hcap hact
  have h11 : runInstructions squareColumn0part11Program {s with pc := UInt256.ofNat 6256, memory := s.memory, stack := word0 :: v34 :: v31 :: word0 :: word1 :: word2 :: word3 :: word4 :: word5 :: v22 :: word7 :: v4 :: word9 :: word10 :: word11 :: word12 :: word13 :: rest} = some {s with pc := UInt256.ofNat 6264, memory := s.memory, stack := v31 :: v38 :: word0 :: word1 :: word2 :: word3 :: word4 :: word5 :: v22 :: word7 :: v4 :: word9 :: word10 :: word11 :: word12 :: word13 :: rest} := by
    simpa only [squareColumn0part11Model, v35, v36, v37, v38] using squareColumn0part11_run (s) (word0) (v34) (v31) (word0) (word1) (word2) (word3) (word4) (word5) (v22) (word7) (v4) (word9) (word10) (word11) (word12) (word13) rest hcap hact
  have h12 : runInstructions squareColumn0part12Program {s with pc := UInt256.ofNat 6264, memory := s.memory, stack := v31 :: v38 :: word0 :: word1 :: word2 :: word3 :: word4 :: word5 :: v22 :: word7 :: v4 :: word9 :: word10 :: word11 :: word12 :: word13 :: rest} = some {s with pc := UInt256.ofNat 6272, memory := s.memory, stack := v4 :: word0 :: word7 :: v40 :: v38 :: word0 :: word1 :: word2 :: word3 :: word4 :: word5 :: v22 :: word7 :: v4 :: word9 :: word10 :: word11 :: word12 :: word13 :: rest} := by
    simpa only [squareColumn0part12Model, v39, v40] using squareColumn0part12_run (s) (v31) (v38) (word0) (word1) (word2) (word3) (word4) (word5) (v22) (word7) (v4) (word9) (word10) (word11) (word12) (word13) rest hcap hact
  have h13 : runInstructions squareColumn0part13Program {s with pc := UInt256.ofNat 6272, memory := s.memory, stack := v4 :: word0 :: word7 :: v40 :: v38 :: word0 :: word1 :: word2 :: word3 :: word4 :: word5 :: v22 :: word7 :: v4 :: word9 :: word10 :: word11 :: word12 :: word13 :: rest} = some {s with pc := UInt256.ofNat 6280, memory := s.memory, stack := word7 :: v44 :: v38 :: word0 :: word1 :: word2 :: word3 :: word4 :: word5 :: v22 :: word7 :: v4 :: word9 :: word10 :: word11 :: word12 :: word13 :: rest} := by
    simpa only [squareColumn0part13Model, v41, v42, v43, v44] using squareColumn0part13_run (s) (v4) (word0) (word7) (v40) (v38) (word0) (word1) (word2) (word3) (word4) (word5) (v22) (word7) (v4) (word9) (word10) (word11) (word12) (word13) rest hcap hact
  have h14 : runInstructions squareColumn0part14Program {s with pc := UInt256.ofNat 6280, memory := s.memory, stack := word7 :: v44 :: v38 :: word0 :: word1 :: word2 :: word3 :: word4 :: word5 :: v22 :: word7 :: v4 :: word9 :: word10 :: word11 :: word12 :: word13 :: rest} = some {s with pc := UInt256.ofNat 6281, memory := s.memory, stack := word11 :: word7 :: v44 :: v38 :: word0 :: word1 :: word2 :: word3 :: word4 :: word5 :: v22 :: word7 :: v4 :: word9 :: word10 :: word11 :: word12 :: word13 :: rest} := by
    simpa only [squareColumn0part14Model] using squareColumn0part14_run (s) (word7) (v44) (v38) (word0) (word1) (word2) (word3) (word4) (word5) (v22) (word7) (v4) (word9) (word10) (word11) (word12) (word13) rest hcap hact
  exact (runInstructions_append_some _ _ _ _ _ h0 (runInstructions_append_some _ _ _ _ _ h1 (runInstructions_append_some _ _ _ _ _ h2 (runInstructions_append_some _ _ _ _ _ h3 (runInstructions_append_some _ _ _ _ _ h4 (runInstructions_append_some _ _ _ _ _ h5 (runInstructions_append_some _ _ _ _ _ h6 (runInstructions_append_some _ _ _ _ _ h7 (runInstructions_append_some _ _ _ _ _ h8 (runInstructions_append_some _ _ _ _ _ h9 (runInstructions_append_some _ _ _ _ _ h10 (runInstructions_append_some _ _ _ _ _ h11 (runInstructions_append_some _ _ _ _ _ h12 (runInstructions_append_some _ _ _ _ _ h13 h14))))))))))))))


end CycleSubmission.Execution
